/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Quotients of powers of principal ideals

This file deals with taking quotients of powers of principal ideals.

## Main definitions and results

* `Ideal.quotEquivPowQuotPowSucc`: for a principal ideal `I`, `R ⧸ I ≃ₗ[R] I ^ n ⧸ I ^ (n + 1)`

## Implementation details

At site of usage, calling `LinearEquiv.toEquiv` can cause timeouts in the search for a complex
synthesis like `Module 𝒪[K] 𝓀[k]`, so the plain equiv versions are provided.

These equivs are defined here as opposed to in the quotients file since they cannot be
formed as ring equivs.

-/

@[expose] public section


namespace Ideal

section IsPrincipal

variable {R : Type*} [CommRing R] [IsDomain R] {I : Ideal R}

/-- For a principal ideal `I`, `R ⧸ I ≃ₗ[R] I ^ n ⧸ I ^ (n + 1)`. To convert into a form
that uses the ideal of `R ⧸ I ^ (n + 1)`, compose with
`Ideal.powQuotPowSuccLinearEquivMapMkPowSuccPow`. -/
noncomputable
/--
Definition of `quotEquivPowQuotPowSucc` / `quotEquivPowQuotPowSucc` 的定义

English:
definition quotEquivPowQuotPowSucc
  signature: (h : I.IsPrincipal) (h' : I != ⊥) (n : Nat)
  body: by
  let f : (I ^ n : Ideal R) ->ₗ[R] (I ^ n : Ideal R) ⧸ (I • ⊤ : Submodule R (I ^ n : Ideal R)) :=
    Submodule.mkQ _
  let ϖ := h.principal.choose
  have hI : I = Ideal.span {ϖ} := h.principal.choose_spec
  have hϖ : ϖ ^ n in I ^ n := hI ▸ (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) n)
  let g : R ->ₗ[R] (I ^ n : Ideal R) := (LinearMap.mulRight R ϖ ^ n).codRestrict _ fun x => by
    simp only [LinearMap.pow_mulRight, LinearMap.mulRight_apply]
    -- TODO: change argument of Ideal.pow_mem_of_mem
    exact Ideal.mul_mem_left _ _ hϖ
  have : I = LinearMap.ker (f.comp g) := by
    ext x
    simp only [LinearMap.codRestrict, LinearMap.pow_mulRight, LinearMap.mulRight_apply,
      LinearMap.mem_ker, LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_top_iff, smul_eq_mul,
      f, g]
    constructor <;> intro hx
    · exact Submodule.mul_mem_mul hx hϖ
    · rw [← pow_succ', hI, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
      obtain ⟨y, hy⟩ := hx
      rw [mul_comm]; rw [pow_succ]; rw [mul_assoc]; rw [mul_right_inj' (pow_ne_zero _ _)] at hy
      · rw [hI, Ideal.mem_span_singleton]
        exact ⟨y, hy⟩
      · contrapose h'
        rw [hI]; rw [h']; rw [Ideal.span_singleton_eq_bot]
  let e : (R ⧸ I) ≃ₗ[R] R ⧸ (LinearMap.ker (f.comp g)) :=
    Submodule.quotEquivOfEq I (LinearMap.ker (f ∘ₗ g)) this
  refine e.trans ((f.comp g).quotKerEquivOfSurjective ?_)
  refine (Submodule.mkQ_surjective _).comp ?_
  rintro ⟨x, hx⟩
  rw [hI]; rw [Ideal.span_singleton_pow]; rw [Ideal.mem_span_singleton] at hx
  refine hx.imp ?_
  simp [g, LinearMap.codRestrict, eq_comm, mul_comm]

中文:
定义 quotEquivPowQuotPowSucc
  签名: (h : I.是Principal) (h' : I != ⊥) (n : 自然数)
  定义体: by
  let f : (I ^ n : Ideal R) ->ₗ[R] (I ^ n : Ideal R) ⧸ (I • ⊤ : Submodule R (I ^ n : Ideal R)) :=
    Submodule.mkQ _
  let ϖ := h.principal.choose
  have hI : I = Ideal.span {ϖ} := h.principal.choose_spec
  have hϖ : ϖ ^ n in I ^ n := hI ▸ (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) n)
  let g : R ->ₗ[R] (I ^ n : Ideal R) := (LinearMap.mulRight R ϖ ^ n).codRestrict _ fun x => by
    simp only [LinearMap.pow_mulRight, LinearMap.mulRight_apply]
    -- TODO: change argument of Ideal.pow_mem_of_mem
    exact Ideal.mul_mem_left _ _ hϖ
  have : I = LinearMap.ker (f.comp g) := by
    ext x
    simp only [LinearMap.codRestrict, LinearMap.pow_mulRight, LinearMap.mulRight_apply,
      LinearMap.mem_ker, LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_top_iff, smul_eq_mul,
      f, g]
    constructor <;> intro hx
    · exact Submodule.mul_mem_mul hx hϖ
    · rw [← pow_succ', hI, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
      obtain ⟨y, hy⟩ := hx
      rw [mul_comm]; rw [pow_succ]; rw [mul_assoc]; rw [mul_right_inj' (pow_ne_zero _ _)] at hy
      · rw [hI, Ideal.mem_span_singleton]
        exact ⟨y, hy⟩
      · contrapose h'
        rw [hI]; rw [h']; rw [Ideal.span_singleton_eq_bot]
  let e : (R ⧸ I) ≃ₗ[R] R ⧸ (LinearMap.ker (f.comp g)) :=
    Submodule.quotEquivOfEq I (LinearMap.ker (f ∘ₗ g)) this
  refine e.trans ((f.comp g).quotKerEquivOfSurjective ?_)
  refine (Submodule.mkQ_surjective _).comp ?_
  rintro ⟨x, hx⟩
  rw [hI]; rw [Ideal.span_singleton_pow]; rw [Ideal.mem_span_singleton] at hx
  refine hx.imp ?_
  simp [g, LinearMap.codRestrict, eq_comm, mul_comm]

Depends on / 依赖: Ideal.mem_span_singleton_self, Ideal.pow_mem_pow, Ideal.span, LinearMap, LinearMap.mulRight, LinearMap.mulRight_apply, LinearMap.pow_mulRight, Submodule, Submodule.mkQ, choose_spec, codRestrict, h.principal.choose, h.principal.choose_spec, mem_span_singleton_self, mulRight, mulRight_apply, pow_mem_pow, pow_mulRight, principal
-/
def quotEquivPowQuotPowSucc (h : I.IsPrincipal) (h' : I != ⊥) (n : Nat) :
    (R ⧸ I) ≃ₗ[R] (I ^ n : Ideal R) ⧸ (I • ⊤ : Submodule R (I ^ n : Ideal R)) := by
  let f : (I ^ n : Ideal R) ->ₗ[R] (I ^ n : Ideal R) ⧸ (I • ⊤ : Submodule R (I ^ n : Ideal R)) :=
    Submodule.mkQ _
  let ϖ := h.principal.choose
  have hI : I = Ideal.span {ϖ} := h.principal.choose_spec
  have hϖ : ϖ ^ n in I ^ n := hI ▸ (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) n)
  let g : R ->ₗ[R] (I ^ n : Ideal R) := (LinearMap.mulRight R ϖ ^ n).codRestrict _ fun x => by
    simp only [LinearMap.pow_mulRight, LinearMap.mulRight_apply]
    -- TODO: change argument of Ideal.pow_mem_of_mem
    exact Ideal.mul_mem_left _ _ hϖ
  have : I = LinearMap.ker (f.comp g) := by
    ext x
    simp only [LinearMap.codRestrict, LinearMap.pow_mulRight, LinearMap.mulRight_apply,
      LinearMap.mem_ker, LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_top_iff, smul_eq_mul,
      f, g]
    constructor <;> intro hx
    · exact Submodule.mul_mem_mul hx hϖ
    · rw [← pow_succ', hI, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
      obtain ⟨y, hy⟩ := hx
      rw [mul_comm]; rw [pow_succ]; rw [mul_assoc]; rw [mul_right_inj' (pow_ne_zero _ _)] at hy
      · rw [hI, Ideal.mem_span_singleton]
        exact ⟨y, hy⟩
      · contrapose h'
        rw [hI]; rw [h']; rw [Ideal.span_singleton_eq_bot]
  let e : (R ⧸ I) ≃ₗ[R] R ⧸ (LinearMap.ker (f.comp g)) :=
    Submodule.quotEquivOfEq I (LinearMap.ker (f ∘ₗ g)) this
  refine e.trans ((f.comp g).quotKerEquivOfSurjective ?_)
  refine (Submodule.mkQ_surjective _).comp ?_
  rintro ⟨x, hx⟩
  rw [hI]; rw [Ideal.span_singleton_pow]; rw [Ideal.mem_span_singleton] at hx
  refine hx.imp ?_
  simp [g, LinearMap.codRestrict, eq_comm, mul_comm]

/-- For a principal ideal `I`, `R ⧸ I ≃ I ^ n ⧸ I ^ (n + 1)`. Supplied as a plain equiv to bypass
typeclass synthesis issues on complex `Module` goals. To convert into a form
that uses the ideal of `R ⧸ I ^ (n + 1)`, compose with
`Ideal.powQuotPowSuccEquivMapMkPowSuccPow`. -/
noncomputable
/--
Definition of `quotEquivPowQuotPowSuccEquiv` / `quotEquivPowQuotPowSuccEquiv` 的定义

English:
definition quotEquivPowQuotPowSuccEquiv
  signature: (h : I.IsPrincipal) (h' : I != ⊥) (n : Nat)
  body: quotEquivPowQuotPowSucc h h' n

中文:
定义 quotEquivPowQuotPowSuccEquiv
  签名: (h : I.是Principal) (h' : I != ⊥) (n : 自然数)
  定义体: quotEquivPowQuotPowSucc h h' n

Depends on / 依赖: quotEquivPowQuotPowSucc
-/
def quotEquivPowQuotPowSuccEquiv (h : I.IsPrincipal) (h' : I != ⊥) (n : Nat) :
    (R ⧸ I) ≃ (I ^ n : Ideal R) ⧸ (I • ⊤ : Submodule R (I ^ n : Ideal R)) :=
  quotEquivPowQuotPowSucc h h' n

end IsPrincipal

end Ideal
