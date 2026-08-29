/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Johan Commelin, Patrick Massot
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Valuation.Basic

/-!
# The valuation on a quotient ring

The support of a valuation `v : Valuation R Γ₀` is `supp v`. If `J` is an ideal of `R`
with `h : J ⊆ supp v` then the induced valuation
on `R / J` = `Ideal.Quotient J` is `onQuot v h`.

-/

@[expose] public section


namespace Valuation

variable {R Γ₀ : Type*} [CommRing R] [LinearOrderedCommMonoidWithZero Γ₀]
variable (v : Valuation R Γ₀)

/--
Definition of `onQuotVal` / `onQuotVal` 的定义

English:
definition onQuotVal
  signature: {J : Ideal R} (hJ : J <= supp v)
  body: fun q =>
  Quotient.liftOn' q v fun a b h =>
    calc
      v a = v (b + -(-a + b)) := by simp
      _ = v b :=
v.map_add_supp b (Ideal.neg_mem_iff _).2 hJ QuotientAddGroup.leftRel_apply.mp h

中文:
定义 onQuotVal
  签名: {J : Ideal R} (hJ : J <= supp v)
  定义体: fun q =>
  Quotient.liftOn' q v fun a b h =>
    calc
      v a = v (b + -(-a + b)) := by simp
      _ = v b :=
v.map_add_supp b (Ideal.neg_mem_iff _).2 hJ QuotientAddGroup.leftRel_apply.mp h
-/
def onQuotVal {J : Ideal R} (hJ : J <= supp v) : R ⧸ J -> Γ₀ := fun q =>
  Quotient.liftOn' q v fun a b h =>
    calc
      v a = v (b + -(-a + b)) := by simp
      _ = v b :=
v.map_add_supp b (Ideal.neg_mem_iff _).2 hJ QuotientAddGroup.leftRel_apply.mp h

/--
Definition of `onQuot` / `onQuot` 的定义

English:
definition onQuot
  signature: {J : Ideal R} (hJ : J <= supp v)
  body: v.onQuotVal hJ
  map_zero' := v.map_zero
  map_one' := v.map_one
  map_mul' xbar ybar := Quotient.ind₂' v.map_mul xbar ybar
  map_add_le_max' xbar ybar := Quotient.ind₂' v.map_add xbar ybar

@[simp]

中文:
定义 onQuot
  签名: {J : Ideal R} (hJ : J <= supp v)
  定义体: v.onQuotVal hJ
  map_zero' := v.map_zero
  map_one' := v.map_one
  map_mul' xbar ybar := Quotient.ind₂' v.map_mul xbar ybar
  map_add_le_max' xbar ybar := Quotient.ind₂' v.map_add xbar ybar

@[simp]

Depends on / 依赖: onQuotVal, v.onQuotVal
-/
def onQuot {J : Ideal R} (hJ : J <= supp v) : Valuation (R ⧸ J) Γ₀ where
  toFun := v.onQuotVal hJ
  map_zero' := v.map_zero
  map_one' := v.map_one
  map_mul' xbar ybar := Quotient.ind₂' v.map_mul xbar ybar
  map_add_le_max' xbar ybar := Quotient.ind₂' v.map_add xbar ybar

@[simp]
/--
theorem `onQuot_comap_eq` / 定理 `onQuot_comap_eq`

English:
theorem onQuot_comap_eq
  given: {J : Ideal R} (hJ : J <= supp v)
  proof: ext fun _ => rfl

中文:
定理 onQuot_comap_eq
  条件: {J : Ideal R} (hJ : J <= supp v)
  证明: ext fun _ => rfl
-/
theorem onQuot_comap_eq {J : Ideal R} (hJ : J <= supp v) :
    (v.onQuot hJ).comap (Ideal.Quotient.mk J) = v :=
  ext fun _ => rfl

/--
theorem `self_le_supp_comap` / 定理 `self_le_supp_comap`

English:
theorem self_le_supp_comap
  given: (J : Ideal R) (v : Valuation (R ⧸ J) Γ₀)
  proof: by
  rw [comap_supp]; rw [← Ideal.map_le_iff_le_comap]
  simp

@[simp]

中文:
定理 self_le_supp_comap
  条件: (J : Ideal R) (v : Valuation (R ⧸ J) Γ₀)
  证明: by
  rw [comap_supp]; rw [← Ideal.map_le_iff_le_comap]
  simp

@[simp]

Depends on / 依赖: Ideal.map_le_iff_le_comap, comap_supp, map_le_iff_le_comap
-/
theorem self_le_supp_comap (J : Ideal R) (v : Valuation (R ⧸ J) Γ₀) :
    J <= (v.comap (Ideal.Quotient.mk J)).supp := by
  rw [comap_supp]; rw [← Ideal.map_le_iff_le_comap]
  simp

@[simp]
/--
theorem `comap_onQuot_eq` / 定理 `comap_onQuot_eq`

English:
theorem comap_onQuot_eq
  given: (J : Ideal R) (v : Valuation (R ⧸ J) Γ₀)
  proof: ext by
    rintro ⟨x⟩
    rfl

中文:
定理 comap_onQuot_eq
  条件: (J : Ideal R) (v : Valuation (R ⧸ J) Γ₀)
  证明: ext by
    rintro ⟨x⟩
    rfl
-/
theorem comap_onQuot_eq (J : Ideal R) (v : Valuation (R ⧸ J) Γ₀) :
    (v.comap (Ideal.Quotient.mk J)).onQuot (v.self_le_supp_comap J) = v :=
ext by
    rintro ⟨x⟩
    rfl

/--
theorem `supp_quot` / 定理 `supp_quot`

English:
theorem supp_quot
  given: {J : Ideal R} (hJ : J <= supp v)
  proof: by
  apply le_antisymm
  · rintro ⟨x⟩ hx
    apply Ideal.subset_span
    exact ⟨x, hx, rfl⟩
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact hx

中文:
定理 supp_quot
  条件: {J : Ideal R} (hJ : J <= supp v)
  证明: by
  apply le_antisymm
  · rintro ⟨x⟩ hx
    apply Ideal.subset_span
    exact ⟨x, hx, rfl⟩
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact hx

Depends on / 依赖: Ideal.map_le_iff_le_comap, Ideal.subset_span, le_antisymm, map_le_iff_le_comap, subset_span
-/
theorem supp_quot {J : Ideal R} (hJ : J <= supp v) :
    supp (v.onQuot hJ) = (supp v).map (Ideal.Quotient.mk J) := by
  apply le_antisymm
  · rintro ⟨x⟩ hx
    apply Ideal.subset_span
    exact ⟨x, hx, rfl⟩
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact hx

/--
theorem `supp_quot_supp` / 定理 `supp_quot_supp`

English:
theorem supp_quot_supp
  statement: supp (v.onQuot le_rfl) = 0
  proof: by
  rw [supp_quot]
  exact Ideal.map_quotient_self _

中文:
定理 supp_quot_supp
  结论: supp (v.onQuot le_rfl) = 0
  证明: by
  rw [supp_quot]
  exact Ideal.map_quotient_self _

Depends on / 依赖: Ideal.map_quotient_self, map_quotient_self, supp_quot
-/
theorem supp_quot_supp : supp (v.onQuot le_rfl) = 0 := by
  rw [supp_quot]
  exact Ideal.map_quotient_self _

end Valuation

namespace AddValuation

variable {R Γ₀ : Type*}
variable [CommRing R] [LinearOrderedAddCommMonoidWithTop Γ₀]
variable (v : AddValuation R Γ₀)

/--
Definition of `onQuotVal` / `onQuotVal` 的定义

English:
definition onQuotVal
  signature: {J : Ideal R} (hJ : J <= supp v)
  body: Valuation.onQuotVal v hJ

中文:
定义 onQuotVal
  签名: {J : Ideal R} (hJ : J <= supp v)
  定义体: Valuation.onQuotVal v hJ

Depends on / 依赖: Valuation, Valuation.onQuotVal, onQuotVal
-/
def onQuotVal {J : Ideal R} (hJ : J <= supp v) : R ⧸ J -> Γ₀ :=
  Valuation.onQuotVal v hJ

/--
Definition of `onQuot` / `onQuot` 的定义

English:
definition onQuot
  signature: {J : Ideal R} (hJ : J <= supp v)
  body: Valuation.onQuot v hJ

@[simp]

中文:
定义 onQuot
  签名: {J : Ideal R} (hJ : J <= supp v)
  定义体: Valuation.onQuot v hJ

@[simp]

Depends on / 依赖: Valuation, Valuation.onQuot, onQuot
-/
def onQuot {J : Ideal R} (hJ : J <= supp v) : AddValuation (R ⧸ J) Γ₀ :=
  Valuation.onQuot v hJ

@[simp]
/--
theorem `onQuot_comap_eq` / 定理 `onQuot_comap_eq`

English:
theorem onQuot_comap_eq
  given: {J : Ideal R} (hJ : J <= supp v)
  proof: Valuation.onQuot_comap_eq v hJ

中文:
定理 onQuot_comap_eq
  条件: {J : Ideal R} (hJ : J <= supp v)
  证明: Valuation.onQuot_comap_eq v hJ

Depends on / 依赖: Valuation, Valuation.onQuot_comap_eq, onQuot_comap_eq
-/
theorem onQuot_comap_eq {J : Ideal R} (hJ : J <= supp v) :
    (v.onQuot hJ).comap (Ideal.Quotient.mk J) = v :=
  Valuation.onQuot_comap_eq v hJ

/--
theorem `comap_supp` / 定理 `comap_supp`

English:
theorem comap_supp
  given: {S : Type*} [CommRing S] (f : S ->+* R)
  proof: Valuation.comap_supp v f

中文:
定理 comap_supp
  条件: {S : 类型} [CommRing S] (f : S ->+* R)
  证明: Valuation.comap_supp v f

Depends on / 依赖: Valuation, Valuation.comap_supp, comap_supp
-/
theorem comap_supp {S : Type*} [CommRing S] (f : S ->+* R) :
    supp (v.comap f) = Ideal.comap f v.supp :=
  Valuation.comap_supp v f

/--
theorem `self_le_supp_comap` / 定理 `self_le_supp_comap`

English:
theorem self_le_supp_comap
  given: (J : Ideal R) (v : AddValuation (R ⧸ J) Γ₀)
  proof: Valuation.self_le_supp_comap J v

@[simp]

中文:
定理 self_le_supp_comap
  条件: (J : Ideal R) (v : AddValuation (R ⧸ J) Γ₀)
  证明: Valuation.self_le_supp_comap J v

@[simp]

Depends on / 依赖: Valuation, Valuation.self_le_supp_comap, self_le_supp_comap
-/
theorem self_le_supp_comap (J : Ideal R) (v : AddValuation (R ⧸ J) Γ₀) :
    J <= (v.comap (Ideal.Quotient.mk J)).supp :=
  Valuation.self_le_supp_comap J v

@[simp]
/--
theorem `comap_onQuot_eq` / 定理 `comap_onQuot_eq`

English:
theorem comap_onQuot_eq
  given: (J : Ideal R) (v : AddValuation (R ⧸ J) Γ₀)
  proof: Valuation.comap_onQuot_eq J v

中文:
定理 comap_onQuot_eq
  条件: (J : Ideal R) (v : AddValuation (R ⧸ J) Γ₀)
  证明: Valuation.comap_onQuot_eq J v

Depends on / 依赖: Valuation, Valuation.comap_onQuot_eq, comap_onQuot_eq
-/
theorem comap_onQuot_eq (J : Ideal R) (v : AddValuation (R ⧸ J) Γ₀) :
    (v.comap (Ideal.Quotient.mk J)).onQuot (v.self_le_supp_comap J) = v :=
  Valuation.comap_onQuot_eq J v

/--
theorem `supp_quot` / 定理 `supp_quot`

English:
theorem supp_quot
  given: {J : Ideal R} (hJ : J <= supp v)
  proof: Valuation.supp_quot v hJ

中文:
定理 supp_quot
  条件: {J : Ideal R} (hJ : J <= supp v)
  证明: Valuation.supp_quot v hJ

Depends on / 依赖: Valuation, Valuation.supp_quot, supp_quot
-/
theorem supp_quot {J : Ideal R} (hJ : J <= supp v) :
    supp (v.onQuot hJ) = (supp v).map (Ideal.Quotient.mk J) :=
  Valuation.supp_quot v hJ

/--
theorem `supp_quot_supp` / 定理 `supp_quot_supp`

English:
theorem supp_quot_supp
  statement: supp ((Valuation.onQuot v) le_rfl) = 0
  proof: Valuation.supp_quot_supp v

中文:
定理 supp_quot_supp
  结论: supp ((Valuation.onQuot v) le_rfl) = 0
  证明: Valuation.supp_quot_supp v

Depends on / 依赖: Valuation, Valuation.supp_quot_supp, supp_quot_supp
-/
theorem supp_quot_supp : supp ((Valuation.onQuot v) le_rfl) = 0 :=
  Valuation.supp_quot_supp v

end AddValuation
