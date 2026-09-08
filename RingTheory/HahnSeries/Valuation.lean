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
/-- The additive valuation on `R⟦Γ⟧` returning the smallest index at which
  a Hahn Series has a nonzero coefficient, or `⊤` for the 0 series. -/
/-
**HahnSeries.addVal** 是 Mathlib 中的一个定义，位于命名空间 `HahnSeries`。
形式化陈述：addVal : AddValuation R⟦Γ⟧ (WithTop Γ)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The additive valuation on `R⟦Γ⟧` returning the smallest index at which
  a Hahn Series has a nonzero coefficient, or `⊤` for the 0 series.
-/
def addVal : AddValuation R⟦Γ⟧ (WithTop Γ) :=
  AddValuation.of orderTop orderTop_zero (orderTop_one) (fun _ _ => min_orderTop_le_orderTop_add)
  fun x y => by
    by_cases hx : x = 0; · simp [hx]
    by_cases hy : y = 0; · simp [hy]
    rw [← order_eq_orderTop_of_ne_zero hx, ← order_eq_orderTop_of_ne_zero hy,
      ← order_eq_orderTop_of_ne_zero (mul_ne_zero hx hy), ← WithTop.coe_add, WithTop.coe_eq_coe,
      order_mul hx hy]
/-
**HahnSeries.addVal_apply** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：addVal_apply {x : R⟦Γ⟧} : addVal Γ R x = x.orderTop
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddValuation.of_apply`：of_apply : (of f h0 h1 hadd hmul) r = f r
-/
theorem addVal_apply {x : R⟦Γ⟧} : addVal Γ R x = x.orderTop :=
  AddValuation.of_apply _

@[simp]
/-
**HahnSeries.addVal_apply_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：addVal_apply_of_ne {x : R⟦Γ⟧} (hx : x != 0) : addVal Γ R x = x.order
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `HahnSeries.addVal_apply`：addVal_apply {x : R⟦Γ⟧} : addVal Γ R x = x.orde
rTop
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HahnSeries.order_eq_orderTop_of_ne_zero`：order_eq_orderTop_of_ne_zero (h
x : x != 0) : order x = orderTop x
-/
theorem addVal_apply_of_ne {x : R⟦Γ⟧} (hx : x ≠ 0) : addVal Γ R x = x.order :=
  addVal_apply.trans (order_eq_orderTop_of_ne_zero hx).symm
/-
**HahnSeries.addVal_le_of_coeff_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：addVal_le_of_coeff_ne_zero {x : R⟦Γ⟧} {g : Γ} (h : x.coeff g != 0) : addVa
l Γ R x <= g
参数：h : x.coeff g != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.orderTop_le_of_coeff_ne_zero`：orderTop_le_of_coeff_ne_zero {Γ
} [LinearOrder Γ] {x : R⟦Γ⟧} {g : Γ} (h : x.coeff g != 0) : x.orderTop <= g
-/
theorem addVal_le_of_coeff_ne_zero {x : R⟦Γ⟧} {g : Γ} (h : x.coeff g ≠ 0) : addVal Γ R x ≤ g :=
  orderTop_le_of_coeff_ne_zero h

end Valuation

end HahnSeries

