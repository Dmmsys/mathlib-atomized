/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Deepro Choudhury
-/
module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Algebra.Module.Equiv.Basic

/-!

# Additional results about finite spanning sets in linear algebra

-/

public section

open Set Function
open Submodule (span)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `LinearEquiv.isOfFinOrder_of_finite_of_span_eq_top_of_mapsTo` / 引理 `LinearEquiv.isOfFinOrder_of_finite_of_span_eq_top_of_mapsTo`

English:
lemma LinearEquiv.isOfFinOrder_of_finite_of_span_eq_top_of_mapsTo
  proof: by
  replace he : BijOn e Φ Φ := (hΦ₁.injOn_iff_bijOn_of_mapsTo he).mp e.injective.injOn
  let e' := he.equiv
  have : Finite Φ := finite_coe_iff.mpr hΦ₁
  obtain ⟨k, hk₀, hk⟩ := isOfFinOrder_of_finite e'
  refine ⟨k, hk₀, ?_⟩
  ext m
  have hm : m in span R Φ := hΦ₂ ▸ Submodule.mem_top
  simp only 

中文:
引理 LinearEquiv.isOfFinOrder_of_finite_of_span_eq_top_of_mapsTo
  证明: by
  replace he : BijOn e Φ Φ := (hΦ₁.injOn_iff_bijOn_of_mapsTo he).mp e.injective.injOn
  let e' := he.equiv
  have : Finite Φ := finite_coe_iff.mpr hΦ₁
  obtain ⟨k, hk₀, hk⟩ := isOfFinOrder_of_finite e'
  refine ⟨k, hk₀, ?_⟩
  ext m
  have hm : m in span R Φ := hΦ₂ ▸ Submodule.mem_top
  simp only 

Depends on / 依赖: Finite, LinearEquiv, LinearEquiv.coe_one, LinearEquiv.po, Submodule, Submodule.mem_top, Submodule.span_induction, coe_one, e.injective.injOn, finite_coe_iff, finite_coe_iff.mpr, he.equiv, id_eq, injOn_iff_bijOn_of_mapsTo, injective, isOfFinOrder_of_finite, map_add, mem_top, mul_left_iterate, mul_one
-/
lemma LinearEquiv.isOfFinOrder_of_finite_of_span_eq_top_of_mapsTo
    {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {Φ : Set M} (hΦ₁ : Φ.Finite) (hΦ₂ : span R Φ = ⊤) {e : M ≃ₗ[R] M} (he : MapsTo e Φ Φ) :
    IsOfFinOrder e := by
  replace he : BijOn e Φ Φ := (hΦ₁.injOn_iff_bijOn_of_mapsTo he).mp e.injective.injOn
  let e' := he.equiv
  have : Finite Φ := finite_coe_iff.mpr hΦ₁
  obtain ⟨k, hk₀, hk⟩ := isOfFinOrder_of_finite e'
  refine ⟨k, hk₀, ?_⟩
  ext m
  have hm : m in span R Φ := hΦ₂ ▸ Submodule.mem_top
  simp only [mul_left_iterate, mul_one, LinearEquiv.coe_one, id_eq]
  refine Submodule.span_induction (fun x hx => ?_) (by simp)
    (fun x y _ _ hx hy => by simp [map_add, hx, hy]) (fun t x _ hx => by simp [hx]) hm
  rw [LinearEquiv.pow_apply]; rw [← he.1.coe_iterate_restrict ⟨x]; rw [hx⟩ k]
  replace hk : (e') ^ k = 1 := by simpa [IsPeriodicPt, IsFixedPt] using hk
  replace hk := Equiv.congr_fun hk ⟨x, hx⟩
  rwa [Equiv.Perm.coe_one, id_eq, Subtype.ext_iff, Equiv.Perm.coe_pow] at hk
