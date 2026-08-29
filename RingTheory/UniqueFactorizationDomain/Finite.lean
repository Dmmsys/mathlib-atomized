/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Aaron Anderson
-/
module

public import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors

/-!
# Finiteness of divisors

## Main results
* `UniqueFactorizationMonoid.fintypeSubtypeDvd`: elements of a UFM with finitely many units have
  finitely many divisors.
-/

@[expose] public section

assert_not_exists Field

variable {α : Type*}

local infixl:50 " ~ᵤ " => Associated

namespace UniqueFactorizationMonoid

/-- If `y` is a nonzero element of a unique factorization monoid with finitely
many units (e.g. `ℤ`, `Ideal (ring_of_integers K)`), it has finitely many divisors. -/
@[instance_reducible]
/--
Definition of `fintypeSubtypeDvd` / `fintypeSubtypeDvd` 的定义

English:
definition fintypeSubtypeDvd
  signature: {M : Type*} [CommMonoidWithZero M]
  body: by
  haveI : Nontrivial M := ⟨⟨y, 0, hy⟩⟩
  haveI : StrongNormalizationMonoid M := UniqueFactorizationMonoid.strongNormalizationMonoid
  haveI := Classical.decEq M
  haveI := Classical.decEq (Associates M)
  -- We'll show `fun (u : Mˣ) (f ⊆ factors y) ↦ u * Π f` is injective
  -- and has image exactly the divisors of `y`.
  refine
    Fintype.subtype
      (((normalizedFactors y).powerset.toFinset ×ˢ (Finset.univ : Finset Mˣ)).image fun s =>
        (s.snd : M) * s.fst.prod)
      fun x => ?_
  simp only [Finset.mem_image, Finset.mem_product, Finset.mem_univ, and_true,
    Multiset.mem_toFinset, Multiset.mem_powerset]
  constructor
  · rintro ⟨s, hs, rfl⟩
    rw [(unit_associated_one.mul_right s.fst.prod).dvd_iff_dvd_left]; rw [one_mul]; rw [← (prod_normalizedFactors hy).dvd_iff_dvd_right]
    exact Multiset.prod_dvd_prod_of_le hs
  · rintro (h : x ∣ y)
    have hx : x != 0 := by
      refine mt (fun hx => ?_) hy
      rwa [hx, zero_dvd_iff] at h
    obtain ⟨u, hu⟩ := prod_normalizedFactors hx
    refine ⟨⟨normalizedFactors x, u⟩, ?_, (mul_comm _ _).trans hu⟩
    exact (dvd_iff_normalizedFactors_le_normalizedFactors hx hy).mp h

中文:
定义 fintypeSubtypeDvd
  签名: {M : 类型} [带零交换幺半群 M]
  定义体: by
  haveI : Nontrivial M := ⟨⟨y, 0, hy⟩⟩
  haveI : StrongNormalizationMonoid M := UniqueFactorizationMonoid.strongNormalizationMonoid
  haveI := Classical.decEq M
  haveI := Classical.decEq (Associates M)
  -- We'll show `fun (u : Mˣ) (f ⊆ factors y) ↦ u * Π f` is injective
  -- and has image exactly the divisors of `y`.
  refine
    Fintype.subtype
      (((normalizedFactors y).powerset.toFinset ×ˢ (Finset.univ : Finset Mˣ)).image fun s =>
        (s.snd : M) * s.fst.prod)
      fun x => ?_
  simp only [Finset.mem_image, Finset.mem_product, Finset.mem_univ, and_true,
    Multiset.mem_toFinset, Multiset.mem_powerset]
  constructor
  · rintro ⟨s, hs, rfl⟩
    rw [(unit_associated_one.mul_right s.fst.prod).dvd_iff_dvd_left]; rw [one_mul]; rw [← (prod_normalizedFactors hy).dvd_iff_dvd_right]
    exact Multiset.prod_dvd_prod_of_le hs
  · rintro (h : x ∣ y)
    have hx : x != 0 := by
      refine mt (fun hx => ?_) hy
      rwa [hx, zero_dvd_iff] at h
    obtain ⟨u, hu⟩ := prod_normalizedFactors hx
    refine ⟨⟨normalizedFactors x, u⟩, ?_, (mul_comm _ _).trans hu⟩
    exact (dvd_iff_normalizedFactors_le_normalizedFactors hx hy).mp h

Depends on / 依赖: Associates, Classical, Classical.decEq, Nontrivial, StrongNormalizationMonoid, UniqueFactorizationMonoid, UniqueFactorizationMonoid.strongNormalizationMonoid, strongNormalizationMonoid
-/
noncomputable def fintypeSubtypeDvd {M : Type*} [CommMonoidWithZero M]
    [UniqueFactorizationMonoid M] [Fintype Mˣ] (y : M) (hy : y != 0) : Fintype { x // x ∣ y } := by
  haveI : Nontrivial M := ⟨⟨y, 0, hy⟩⟩
  haveI : StrongNormalizationMonoid M := UniqueFactorizationMonoid.strongNormalizationMonoid
  haveI := Classical.decEq M
  haveI := Classical.decEq (Associates M)
  -- We'll show `fun (u : Mˣ) (f ⊆ factors y) ↦ u * Π f` is injective
  -- and has image exactly the divisors of `y`.
  refine
    Fintype.subtype
      (((normalizedFactors y).powerset.toFinset ×ˢ (Finset.univ : Finset Mˣ)).image fun s =>
        (s.snd : M) * s.fst.prod)
      fun x => ?_
  simp only [Finset.mem_image, Finset.mem_product, Finset.mem_univ, and_true,
    Multiset.mem_toFinset, Multiset.mem_powerset]
  constructor
  · rintro ⟨s, hs, rfl⟩
    rw [(unit_associated_one.mul_right s.fst.prod).dvd_iff_dvd_left]; rw [one_mul]; rw [← (prod_normalizedFactors hy).dvd_iff_dvd_right]
    exact Multiset.prod_dvd_prod_of_le hs
  · rintro (h : x ∣ y)
    have hx : x != 0 := by
      refine mt (fun hx => ?_) hy
      rwa [hx, zero_dvd_iff] at h
    obtain ⟨u, hu⟩ := prod_normalizedFactors hx
    refine ⟨⟨normalizedFactors x, u⟩, ?_, (mul_comm _ _).trans hu⟩
    exact (dvd_iff_normalizedFactors_le_normalizedFactors hx hy).mp h

end UniqueFactorizationMonoid
