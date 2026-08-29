/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Principal Ideals

This file deals with the set of principal ideals of a `CommRing R`.

## Main definitions and results

* `Ideal.isPrincipalSubmonoid`: the submonoid of `Ideal R` formed by the principal ideals of `R`.

* `Ideal.isPrincipalNonZeroDivisorsSubmonoid`: the submonoid of `(Ideal R)⁰` formed by the
  non-zero-divisors principal ideals of `R`.

* `Ideal.associatesMulEquivIsPrincipal`: the `MulEquiv` between the monoid of `Associates R` and
  the submonoid of principal ideals of `R`.

* `Ideal.associatesNonZeroDivisorsMulEquivIsPrincipal`: the `MulEquiv` between the monoid of
  `Associates R⁰` and the submonoid of non-zero-divisors principal ideals of `R`.
-/

@[expose] public section

variable {R : Type*} [CommRing R]

namespace Ideal

open Submodule Associates

open scoped nonZeroDivisors

variable (R) in
/--
Definition of `isPrincipalSubmonoid` / `isPrincipalSubmonoid` 的定义

English:
definition isPrincipalSubmonoid
  signature: : Submonoid (Ideal R) where
  body: {I | IsPrincipal I}
  mul_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x * y, span_singleton_mul_span_singleton x y⟩
  one_mem' := ⟨1, one_eq_span⟩

中文:
定义 isPrincipalSubmonoid
  签名: : Submonoid (Ideal R) where
  定义体: {I | IsPrincipal I}
  mul_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x * y, span_singleton_mul_span_singleton x y⟩
  one_mem' := ⟨1, one_eq_span⟩

Depends on / 依赖: IsPrincipal
-/
def isPrincipalSubmonoid : Submonoid (Ideal R) where
  carrier := {I | IsPrincipal I}
  mul_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x * y, span_singleton_mul_span_singleton x y⟩
  one_mem' := ⟨1, one_eq_span⟩

/--
theorem `mem_isPrincipalSubmonoid_iff` / 定理 `mem_isPrincipalSubmonoid_iff`

English:
theorem mem_isPrincipalSubmonoid_iff
  given: {I : Ideal R}
  proof: Iff.rfl

中文:
定理 mem_isPrincipalSubmonoid_iff
  条件: {I : Ideal R}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_isPrincipalSubmonoid_iff {I : Ideal R} :
    I in isPrincipalSubmonoid R ↔ IsPrincipal I := Iff.rfl

/--
theorem `span_singleton_mem_isPrincipalSubmonoid` / 定理 `span_singleton_mem_isPrincipalSubmonoid`

English:
theorem span_singleton_mem_isPrincipalSubmonoid
  given: (a : R)
  proof: mem_isPrincipalSubmonoid_iff.mpr ⟨a, rfl⟩

中文:
定理 span_singleton_mem_isPrincipalSubmonoid
  条件: (a : R)
  证明: mem_isPrincipalSubmonoid_iff.mpr ⟨a, rfl⟩

Depends on / 依赖: mem_isPrincipalSubmonoid_iff, mem_isPrincipalSubmonoid_iff.mpr
-/
theorem span_singleton_mem_isPrincipalSubmonoid (a : R) :
    span {a} in isPrincipalSubmonoid R := mem_isPrincipalSubmonoid_iff.mpr ⟨a, rfl⟩

variable (R) in
/--
Definition of `isPrincipalNonZeroDivisorsSubmonoid` / `isPrincipalNonZeroDivisorsSubmonoid` 的定义

English:
definition isPrincipalNonZeroDivisorsSubmonoid
  signature: : Submonoid (Ideal R)⁰ where
  body: {I | IsPrincipal I.val}
  mul_mem' := by
    rintro ⟨_, _⟩ ⟨_, _⟩ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x * y, by
      simp_rw [Submonoid.mk_mul_mk, submodule_span_eq, span_singleton_mul_span_singleton]⟩
  one_mem' := ⟨1, by simp⟩

中文:
定义 isPrincipalNonZeroDivisorsSubmonoid
  签名: : Submonoid (Ideal R)⁰ where
  定义体: {I | IsPrincipal I.val}
  mul_mem' := by
    rintro ⟨_, _⟩ ⟨_, _⟩ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x * y, by
      simp_rw [Submonoid.mk_mul_mk, submodule_span_eq, span_singleton_mul_span_singleton]⟩
  one_mem' := ⟨1, by simp⟩

Depends on / 依赖: I.val, IsPrincipal
-/
def isPrincipalNonZeroDivisorsSubmonoid : Submonoid (Ideal R)⁰ where
  carrier := {I | IsPrincipal I.val}
  mul_mem' := by
    rintro ⟨_, _⟩ ⟨_, _⟩ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x * y, by
      simp_rw [Submonoid.mk_mul_mk, submodule_span_eq, span_singleton_mul_span_singleton]⟩
  one_mem' := ⟨1, by simp⟩

variable [IsDomain R]

variable (R) in
/--
Definition of `associatesEquivIsPrincipal` / `associatesEquivIsPrincipal` 的定义

English:
definition associatesEquivIsPrincipal
  signature: :
  body: _root_.Quotient.lift (fun x => ⟨span {x}, x, rfl⟩)
    (fun _ _ _ => by simpa [span_singleton_eq_span_singleton])
  invFun I := .mk I.2.generator
  left_inv := Quotient.ind fun _ => by simpa [Quotient.eq] using!
    Ideal.span_singleton_eq_span_singleton.mp (@Ideal.span_singleton_generator _ _ _ ⟨_,

中文:
定义 associatesEquivIsPrincipal
  签名: :
  定义体: _root_.Quotient.lift (fun x => ⟨span {x}, x, rfl⟩)
    (fun _ _ _ => by simpa [span_singleton_eq_span_singleton])
  invFun I := .mk I.2.generator
  left_inv := Quotient.ind fun _ => by simpa [Quotient.eq] using!
    Ideal.span_singleton_eq_span_singleton.mp (@Ideal.span_singleton_generator _ _ _ ⟨_,

Depends on / 依赖: Quotient, _root_, _root_.Quotient.lift
-/
noncomputable def associatesEquivIsPrincipal :
    Associates R ≃ {I : Ideal R // IsPrincipal I} where
  toFun := _root_.Quotient.lift (fun x => ⟨span {x}, x, rfl⟩)
    (fun _ _ _ => by simpa [span_singleton_eq_span_singleton])
  invFun I := .mk I.2.generator
  left_inv := Quotient.ind fun _ => by simpa [Quotient.eq] using!
    Ideal.span_singleton_eq_span_singleton.mp (@Ideal.span_singleton_generator _ _ _ ⟨_, rfl⟩)
  right_inv I := by simp only [_root_.Quotient.lift_mk, span_singleton_generator, Subtype.coe_eta]

@[simp]
/--
theorem `associatesEquivIsPrincipal_apply` / 定理 `associatesEquivIsPrincipal_apply`

English:
theorem associatesEquivIsPrincipal_apply
  given: (x : R)
  proof: rfl

@[simp]

中文:
定理 associatesEquivIsPrincipal_apply
  条件: (x : R)
  证明: rfl

@[simp]
-/
theorem associatesEquivIsPrincipal_apply (x : R) :
    associatesEquivIsPrincipal R (.mk x) = span {x} := rfl

@[simp]
/--
theorem `associatesEquivIsPrincipal_symm_apply` / 定理 `associatesEquivIsPrincipal_symm_apply`

English:
theorem associatesEquivIsPrincipal_symm_apply
  given: {I : Ideal R} (hI : IsPrincipal I)
  proof: rfl

中文:
定理 associatesEquivIsPrincipal_symm_apply
  条件: {I : Ideal R} (hI : IsPrincipal I)
  证明: rfl
-/
theorem associatesEquivIsPrincipal_symm_apply {I : Ideal R} (hI : IsPrincipal I) :
    (associatesEquivIsPrincipal R).symm ⟨I, hI⟩ = .mk hI.generator := rfl

/--
theorem `associatesEquivIsPrincipal_mul` / 定理 `associatesEquivIsPrincipal_mul`

English:
theorem associatesEquivIsPrincipal_mul
  given: (x y : Associates R)
  proof: by
  rw [← quot_out x]; rw [← quot_out y]
  simp_rw [mk_mul_mk, associatesEquivIsPrincipal_apply, span_singleton_mul_span_singleton]

@[simp]

中文:
定理 associatesEquivIsPrincipal_mul
  条件: (x y : Associates R)
  证明: by
  rw [← quot_out x]; rw [← quot_out y]
  simp_rw [mk_mul_mk, associatesEquivIsPrincipal_apply, span_singleton_mul_span_singleton]

@[simp]

Depends on / 依赖: associatesEquivIsPrincipal_apply, mk_mul_mk, quot_out, simp_rw, span_singleton_mul_span_singleton
-/
theorem associatesEquivIsPrincipal_mul (x y : Associates R) :
    (associatesEquivIsPrincipal R (x * y) : Ideal R) =
      (associatesEquivIsPrincipal R x) * (associatesEquivIsPrincipal R y) := by
  rw [← quot_out x]; rw [← quot_out y]
  simp_rw [mk_mul_mk, associatesEquivIsPrincipal_apply, span_singleton_mul_span_singleton]

@[simp]
/--
theorem `associatesEquivIsPrincipal_map_zero` / 定理 `associatesEquivIsPrincipal_map_zero`

English:
theorem associatesEquivIsPrincipal_map_zero
  proof: by
  rw [← mk_zero]; rw [associatesEquivIsPrincipal_apply]; rw [Submodule.zero_eq_bot]; rw [span_singleton_eq_bot]

@[simp]

中文:
定理 associatesEquivIsPrincipal_map_zero
  证明: by
  rw [← mk_zero]; rw [associatesEquivIsPrincipal_apply]; rw [Submodule.zero_eq_bot]; rw [span_singleton_eq_bot]

@[simp]

Depends on / 依赖: Submodule, Submodule.zero_eq_bot, associatesEquivIsPrincipal_apply, mk_zero, span_singleton_eq_bot, zero_eq_bot
-/
theorem associatesEquivIsPrincipal_map_zero :
    (associatesEquivIsPrincipal R 0 : Ideal R) = 0 := by
  rw [← mk_zero]; rw [associatesEquivIsPrincipal_apply]; rw [Submodule.zero_eq_bot]; rw [span_singleton_eq_bot]

@[simp]
/--
theorem `associatesEquivIsPrincipal_map_one` / 定理 `associatesEquivIsPrincipal_map_one`

English:
theorem associatesEquivIsPrincipal_map_one
  proof: by
  rw [one_eq_mk_one]; rw [associatesEquivIsPrincipal_apply]; rw [span_singleton_one]; rw [one_eq_top]

中文:
定理 associatesEquivIsPrincipal_map_one
  证明: by
  rw [one_eq_mk_one]; rw [associatesEquivIsPrincipal_apply]; rw [span_singleton_one]; rw [one_eq_top]

Depends on / 依赖: associatesEquivIsPrincipal_apply, one_eq_mk_one, one_eq_top, span_singleton_one
-/
theorem associatesEquivIsPrincipal_map_one :
    (associatesEquivIsPrincipal R 1 : Ideal R) = 1 := by
  rw [one_eq_mk_one]; rw [associatesEquivIsPrincipal_apply]; rw [span_singleton_one]; rw [one_eq_top]

set_option backward.isDefEq.respectTransparency false in
variable (R) in
/--
Definition of `associatesMulEquivIsPrincipal` / `associatesMulEquivIsPrincipal` 的定义

English:
definition associatesMulEquivIsPrincipal
  signature: :
  body: associatesEquivIsPrincipal R
  map_mul' _ _ := by
    rw [Subtype.ext_iff]
    -- This `erw` is needed to see through `{I // IsPrincipal I} = ↑(isPrincipalSubmonoid R)`:
    -- we can redefine `associatesEquivIsPrincipal` to get rid of this `erw` but then we'd need
    -- to add one in `associatesNo

中文:
定义 associatesMulEquivIsPrincipal
  签名: :
  定义体: associatesEquivIsPrincipal R
  map_mul' _ _ := by
    rw [Subtype.ext_iff]
    -- This `erw` is needed to see through `{I // IsPrincipal I} = ↑(isPrincipalSubmonoid R)`:
    -- we can redefine `associatesEquivIsPrincipal` to get rid of this `erw` but then we'd need
    -- to add one in `associatesNo

Depends on / 依赖: associatesEquivIsPrincipal
-/
noncomputable def associatesMulEquivIsPrincipal :
    Associates R ≃* isPrincipalSubmonoid R where
  __ := associatesEquivIsPrincipal R
  map_mul' _ _ := by
    rw [Subtype.ext_iff]
    -- This `erw` is needed to see through `{I // IsPrincipal I} = ↑(isPrincipalSubmonoid R)`:
    -- we can redefine `associatesEquivIsPrincipal` to get rid of this `erw` but then we'd need
    -- to add one in `associatesNonZeroDivisorsEquivIsPrincipal`.
    erw [associatesEquivIsPrincipal_mul]
    rfl

variable (R) in
/--
Definition of `associatesNonZeroDivisorsEquivIsPrincipal` / `associatesNonZeroDivisorsEquivIsPrincipal` 的定义

English:
definition associatesNonZeroDivisorsEquivIsPrincipal
  signature: :
  body: calc Associates R⁰ ≃ (Associates R)⁰ := associatesNonZeroDivisorsEquiv.toEquiv.symm
    _ ≃ {I : {I : Ideal R // IsPrincipal I} // I.1 in (Ideal R)⁰} :=
      Equiv.subtypeEquiv (associatesEquivIsPrincipal R)
        (fun x => by rw [← quot_out x, mk_mem_nonZeroDivisors_associates,
          associa

中文:
定义 associatesNonZeroDivisorsEquivIsPrincipal
  签名: :
  定义体: calc Associates R⁰ ≃ (Associates R)⁰ := associatesNonZeroDivisorsEquiv.toEquiv.symm
    _ ≃ {I : {I : Ideal R // IsPrincipal I} // I.1 in (Ideal R)⁰} :=
      Equiv.subtypeEquiv (associatesEquivIsPrincipal R)
        (fun x => by rw [← quot_out x, mk_mem_nonZeroDivisors_associates,
          associa

Depends on / 依赖: Associates, Equiv.subtypeEquiv, Equiv.subtypeSubtypeEquivSubtypeInter, IsPrincipal, associatesEquivIsPrincipal, associatesEquivIsPrincipal_apply, associatesNonZeroDivisorsEquiv, associatesNonZeroDivisorsEquiv.toEquiv.symm, mk_mem_nonZeroDivisors_associates, quot_out, span_singleton_nonZeroDivisors, subtypeEquiv, subtypeSubtypeEquivSubtypeInter, toEquiv
-/
noncomputable def associatesNonZeroDivisorsEquivIsPrincipal :
    Associates R⁰ ≃ {I : (Ideal R)⁰ // IsPrincipal (I : Ideal R)} :=
  calc Associates R⁰ ≃ (Associates R)⁰ := associatesNonZeroDivisorsEquiv.toEquiv.symm
    _ ≃ {I : {I : Ideal R // IsPrincipal I} // I.1 in (Ideal R)⁰} :=
      Equiv.subtypeEquiv (associatesEquivIsPrincipal R)
        (fun x => by rw [← quot_out x, mk_mem_nonZeroDivisors_associates,
          associatesEquivIsPrincipal_apply, span_singleton_nonZeroDivisors])
    _ ≃ {I : Ideal R // IsPrincipal I ∧ I in (Ideal R)⁰} :=
      Equiv.subtypeSubtypeEquivSubtypeInter (fun I => IsPrincipal I) (fun I => I in (Ideal R)⁰)
    _ ≃ {I : Ideal R // I in (Ideal R)⁰ ∧ IsPrincipal I} :=
.subtypeEquivProp by simp_rw [and_comm]
    _ ≃ {I : (Ideal R)⁰ // IsPrincipal I.1} := (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm

@[simp]
/--
theorem `associatesNonZeroDivisorsEquivIsPrincipal_apply` / 定理 `associatesNonZeroDivisorsEquivIsPrincipal_apply`

English:
theorem associatesNonZeroDivisorsEquivIsPrincipal_apply
  given: (x : R⁰)
  proof: rfl

中文:
定理 associatesNonZeroDivisorsEquivIsPrincipal_apply
  条件: (x : R⁰)
  证明: rfl
-/
theorem associatesNonZeroDivisorsEquivIsPrincipal_apply (x : R⁰) :
    associatesNonZeroDivisorsEquivIsPrincipal R (.mk x) = Ideal.span {(x : R)} := rfl

/--
theorem `associatesNonZeroDivisorsEquivIsPrincipal_coe` / 定理 `associatesNonZeroDivisorsEquivIsPrincipal_coe`

English:
theorem associatesNonZeroDivisorsEquivIsPrincipal_coe
  given: (x : Associates R⁰)
  proof: rfl

中文:
定理 associatesNonZeroDivisorsEquivIsPrincipal_coe
  条件: (x : Associates R⁰)
  证明: rfl
-/
theorem associatesNonZeroDivisorsEquivIsPrincipal_coe (x : Associates R⁰) :
    (associatesNonZeroDivisorsEquivIsPrincipal R x : Ideal R) =
      (associatesEquivIsPrincipal R (associatesNonZeroDivisorsEquiv.symm x)) := rfl

/--
theorem `associatesNonZeroDivisorsEquivIsPrincipal_mul` / 定理 `associatesNonZeroDivisorsEquivIsPrincipal_mul`

English:
theorem associatesNonZeroDivisorsEquivIsPrincipal_mul
  given: (x y : Associates R⁰)
  proof: by
  simp_rw [associatesNonZeroDivisorsEquivIsPrincipal_coe, map_mul, Submonoid.coe_mul,
    associatesEquivIsPrincipal_mul]

@[simp]

中文:
定理 associatesNonZeroDivisorsEquivIsPrincipal_mul
  条件: (x y : Associates R⁰)
  证明: by
  simp_rw [associatesNonZeroDivisorsEquivIsPrincipal_coe, map_mul, Submonoid.coe_mul,
    associatesEquivIsPrincipal_mul]

@[simp]

Depends on / 依赖: Submonoid, Submonoid.coe_mul, associatesEquivIsPrincipal_mul, associatesNonZeroDivisorsEquivIsPrincipal_coe, coe_mul, map_mul, simp_rw
-/
theorem associatesNonZeroDivisorsEquivIsPrincipal_mul (x y : Associates R⁰) :
    (associatesNonZeroDivisorsEquivIsPrincipal R (x * y) : Ideal R) =
      (associatesNonZeroDivisorsEquivIsPrincipal R x) *
        (associatesNonZeroDivisorsEquivIsPrincipal R y) := by
  simp_rw [associatesNonZeroDivisorsEquivIsPrincipal_coe, map_mul, Submonoid.coe_mul,
    associatesEquivIsPrincipal_mul]

@[simp]
/--
theorem `associatesNonZeroDivisorsEquivIsPrincipal_map_one` / 定理 `associatesNonZeroDivisorsEquivIsPrincipal_map_one`

English:
theorem associatesNonZeroDivisorsEquivIsPrincipal_map_one
  proof: by
  rw [associatesNonZeroDivisorsEquivIsPrincipal_coe]; rw [map_one]; rw [OneMemClass.coe_one]; rw [associatesEquivIsPrincipal_map_one]

中文:
定理 associatesNonZeroDivisorsEquivIsPrincipal_map_one
  证明: by
  rw [associatesNonZeroDivisorsEquivIsPrincipal_coe]; rw [map_one]; rw [OneMemClass.coe_one]; rw [associatesEquivIsPrincipal_map_one]

Depends on / 依赖: OneMemClass, OneMemClass.coe_one, associatesEquivIsPrincipal_map_one, associatesNonZeroDivisorsEquivIsPrincipal_coe, coe_one, map_one
-/
theorem associatesNonZeroDivisorsEquivIsPrincipal_map_one :
    (associatesNonZeroDivisorsEquivIsPrincipal R 1 : Ideal R) = 1 := by
  rw [associatesNonZeroDivisorsEquivIsPrincipal_coe]; rw [map_one]; rw [OneMemClass.coe_one]; rw [associatesEquivIsPrincipal_map_one]

set_option backward.isDefEq.respectTransparency false in
variable (R) in
/--
Definition of `associatesNonZeroDivisorsMulEquivIsPrincipal` / `associatesNonZeroDivisorsMulEquivIsPrincipal` 的定义

English:
definition associatesNonZeroDivisorsMulEquivIsPrincipal
  signature: :
  body: associatesNonZeroDivisorsEquivIsPrincipal R
  map_mul' _ _ := by
    rw [Subtype.ext_iff]; rw [Subtype.ext_iff]; rw [Equiv.toFun_as_coe]; rw [associatesNonZeroDivisorsEquivIsPrincipal_mul]
    rfl

中文:
定义 associatesNonZeroDivisorsMulEquivIsPrincipal
  签名: :
  定义体: associatesNonZeroDivisorsEquivIsPrincipal R
  map_mul' _ _ := by
    rw [Subtype.ext_iff]; rw [Subtype.ext_iff]; rw [Equiv.toFun_as_coe]; rw [associatesNonZeroDivisorsEquivIsPrincipal_mul]
    rfl

Depends on / 依赖: associatesNonZeroDivisorsEquivIsPrincipal
-/
noncomputable def associatesNonZeroDivisorsMulEquivIsPrincipal :
    Associates R⁰ ≃* (isPrincipalNonZeroDivisorsSubmonoid R) where
  __ := associatesNonZeroDivisorsEquivIsPrincipal R
  map_mul' _ _ := by
    rw [Subtype.ext_iff]; rw [Subtype.ext_iff]; rw [Equiv.toFun_as_coe]; rw [associatesNonZeroDivisorsEquivIsPrincipal_mul]
    rfl

/--
Definition of `isoBaseOfIsPrincipal` / `isoBaseOfIsPrincipal` 的定义

English:
definition isoBaseOfIsPrincipal
  signature: {I : Ideal R}
  body: letI x := IsPrincipal.generator I
  have hx : x != 0 := by rwa [Ne, ← IsPrincipal.eq_bot_iff_generator_eq_zero]
  (LinearEquiv.toSpanNonzeroSingleton R R x hx).trans
    (LinearEquiv.ofEq (Submodule.span R {x}) I (IsPrincipal.span_singleton_generator I))

@[simp]

中文:
定义 isoBaseOfIsPrincipal
  签名: {I : Ideal R}
  定义体: letI x := IsPrincipal.generator I
  have hx : x != 0 := by rwa [Ne, ← IsPrincipal.eq_bot_iff_generator_eq_zero]
  (LinearEquiv.toSpanNonzeroSingleton R R x hx).trans
    (LinearEquiv.ofEq (Submodule.span R {x}) I (IsPrincipal.span_singleton_generator I))

@[simp]

Depends on / 依赖: IsPrincipal, IsPrincipal.eq_bot_iff_generator_eq_zero, IsPrincipal.generator, IsPrincipal.span_singleton_generator, LinearEquiv, LinearEquiv.ofEq, LinearEquiv.toSpanNonzeroSingleton, Submodule, Submodule.span, eq_bot_iff_generator_eq_zero, generator, span_singleton_generator, toSpanNonzeroSingleton
-/
noncomputable def isoBaseOfIsPrincipal {I : Ideal R}
    [hprinc : I.IsPrincipal] (hI : I != ⊥) : R ≃ₗ[R] I :=
  letI x := IsPrincipal.generator I
  have hx : x != 0 := by rwa [Ne, ← IsPrincipal.eq_bot_iff_generator_eq_zero]
  (LinearEquiv.toSpanNonzeroSingleton R R x hx).trans
    (LinearEquiv.ofEq (Submodule.span R {x}) I (IsPrincipal.span_singleton_generator I))

@[simp]
/--
theorem `isoBaseOfIsPrincipal_apply` / 定理 `isoBaseOfIsPrincipal_apply`

English:
theorem isoBaseOfIsPrincipal_apply
  given: {I : Ideal R} [hprinc : I.IsPrincipal] (hI : I != ⊥) (x : R)
  proof: rfl

中文:
定理 isoBaseOfIsPrincipal_apply
  条件: {I : Ideal R} [hprinc : I.IsPrincipal] (hI : I != ⊥) (x : R)
  证明: rfl
-/
theorem isoBaseOfIsPrincipal_apply {I : Ideal R} [hprinc : I.IsPrincipal] (hI : I != ⊥) (x : R) :
    (Ideal.isoBaseOfIsPrincipal hI) x = x * IsPrincipal.generator I :=
  rfl

/--
theorem `subtype_isoBaseOfIsPrincipal_eq_mul` / 定理 `subtype_isoBaseOfIsPrincipal_eq_mul`

English:
theorem subtype_isoBaseOfIsPrincipal_eq_mul
  statement: {I : Ideal R}
  proof: by
  ext
  simp

中文:
定理 subtype_isoBaseOfIsPrincipal_eq_mul
  结论: {I : Ideal R}
  证明: by
  ext
  simp
-/
theorem subtype_isoBaseOfIsPrincipal_eq_mul {I : Ideal R}
    [hprinc : I.IsPrincipal] (h : I != ⊥) :
    Submodule.subtype I ∘ₗ ↑(Ideal.isoBaseOfIsPrincipal h) =
    LinearMap.mul R R (IsPrincipal.generator I) := by
  ext
  simp

end Ideal
