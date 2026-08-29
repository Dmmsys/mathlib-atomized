/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.RingTheory.HahnSeries.Multiplication
public import Mathlib.RingTheory.Valuation.Basic

/-!
# Valuations on Hahn Series rings

If `Γ` is a linearly ordered cancellative monoid and `R` is a domain, then the domain `R⟦Γ⟧`
admits an additive valuation given by `orderTop`.

## Main Definitions
* `HahnSeries.addVal Γ R` defines an `AddValuation` on `R⟦Γ⟧` when `Γ` is linearly
  ordered.

## TODO
* Multiplicative valuations
* Add any API for Laurent series valuations that do not depend on `Γ = ℤ`.

## References
- [J. van der Hoeven, *Operators on Generalized Power Series*][van_der_hoeven]
-/

@[expose] public section


noncomputable section

variable {Γ R : Type*}

namespace HahnSeries

section Valuation
variable [AddCancelCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ] [Ring R] [IsDomain R]

variable (Γ R) in
/--
Definition of `addVal` / `addVal` 的定义

English:
definition addVal
  signature: : AddValuation R⟦Γ⟧ (WithTop Γ)
  body: AddValuation.of orderTop orderTop_zero (orderTop_one) (fun _ _ => min_orderTop_le_orderTop_add)
  fun x y => by
    by_cases hx : x = 0; · simp [hx]
    by_cases hy : y = 0; · simp [hy]
    rw [← order_eq_orderTop_of_ne_zero hx]; rw [← order_eq_orderTop_of_ne_zero hy]; rw [← order_eq_orderTop_of_ne_

中文:
定义 addVal
  签名: : AddValuation R⟦Γ⟧ (WithTop Γ)
  定义体: AddValuation.of orderTop orderTop_zero (orderTop_one) (fun _ _ => min_orderTop_le_orderTop_add)
  fun x y => by
    by_cases hx : x = 0; · simp [hx]
    by_cases hy : y = 0; · simp [hy]
    rw [← order_eq_orderTop_of_ne_zero hx]; rw [← order_eq_orderTop_of_ne_zero hy]; rw [← order_eq_orderTop_of_ne_

Depends on / 依赖: AddValuation, AddValuation.of, WithTop, WithTop.coe_add, WithTop.coe_eq_coe, coe_add, coe_eq_coe, min_orderTop_le_orderTop_add, mul_ne_zero, orderTop, orderTop_one, orderTop_zero, order_eq_orderTop_of_ne_zero, order_mul
-/
def addVal : AddValuation R⟦Γ⟧ (WithTop Γ) :=
  AddValuation.of orderTop orderTop_zero (orderTop_one) (fun _ _ => min_orderTop_le_orderTop_add)
  fun x y => by
    by_cases hx : x = 0; · simp [hx]
    by_cases hy : y = 0; · simp [hy]
    rw [← order_eq_orderTop_of_ne_zero hx]; rw [← order_eq_orderTop_of_ne_zero hy]; rw [← order_eq_orderTop_of_ne_zero (mul_ne_zero hx hy)]; rw [← WithTop.coe_add]; rw [WithTop.coe_eq_coe]; rw [order_mul hx hy]

/--
theorem `addVal_apply` / 定理 `addVal_apply`

English:
theorem addVal_apply
  given: {x : R⟦Γ⟧}
  statement: addVal Γ R x = x.orderTop
  proof: AddValuation.of_apply _

@[simp]

中文:
定理 addVal_apply
  条件: {x : R⟦Γ⟧}
  结论: addVal Γ R x = x.orderTop
  证明: AddValuation.of_apply _

@[simp]

Depends on / 依赖: AddValuation, AddValuation.of_apply, of_apply
-/
theorem addVal_apply {x : R⟦Γ⟧} : addVal Γ R x = x.orderTop :=
  AddValuation.of_apply _

@[simp]
/--
theorem `addVal_apply_of_ne` / 定理 `addVal_apply_of_ne`

English:
theorem addVal_apply_of_ne
  given: {x : R⟦Γ⟧} (hx : x != 0)
  statement: addVal Γ R x = x.order
  proof: addVal_apply.trans (order_eq_orderTop_of_ne_zero hx).symm

中文:
定理 addVal_apply_of_ne
  条件: {x : R⟦Γ⟧} (hx : x != 0)
  结论: addVal Γ R x = x.order
  证明: addVal_apply.trans (order_eq_orderTop_of_ne_zero hx).symm

Depends on / 依赖: addVal_apply, addVal_apply.trans, order_eq_orderTop_of_ne_zero
-/
theorem addVal_apply_of_ne {x : R⟦Γ⟧} (hx : x != 0) : addVal Γ R x = x.order :=
  addVal_apply.trans (order_eq_orderTop_of_ne_zero hx).symm

/--
theorem `addVal_le_of_coeff_ne_zero` / 定理 `addVal_le_of_coeff_ne_zero`

English:
theorem addVal_le_of_coeff_ne_zero
  given: {x : R⟦Γ⟧} {g : Γ} (h : x.coeff g != 0)
  statement: addVal Γ R x <= g
  proof: orderTop_le_of_coeff_ne_zero h

中文:
定理 addVal_le_of_coeff_ne_zero
  条件: {x : R⟦Γ⟧} {g : Γ} (h : x.coeff g != 0)
  结论: addVal Γ R x <= g
  证明: orderTop_le_of_coeff_ne_zero h

Depends on / 依赖: orderTop_le_of_coeff_ne_zero
-/
theorem addVal_le_of_coeff_ne_zero {x : R⟦Γ⟧} {g : Γ} (h : x.coeff g != 0) : addVal Γ R x <= g :=
  orderTop_le_of_coeff_ne_zero h

end Valuation

end HahnSeries
