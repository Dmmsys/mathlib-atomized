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

/-- If `hJ : J ⊆ supp v` then `onQuotVal hJ` is the induced function on `R / J` as a function.
Note: it's just the function; the valuation is `onQuot hJ`. -/
/-
**Valuation.onQuotVal** 是 Mathlib 中的一个定义，位于命名空间 `Valuation`。
形式化陈述：onQuotVal {J : Ideal R} (hJ : J <= supp v) : R ⧸ J -> Γ₀
参数：hJ : J <= supp v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `hJ : J ⊆ supp v` then `onQuotVal hJ` is the induced function on `R / J` as a
 function.
Note: it's just the function; the valuation is `onQuot hJ`.
-/
def onQuotVal {J : Ideal R} (hJ : J ≤ supp v) : R ⧸ J → Γ₀ := fun q =>
  Quotient.liftOn' q v fun a b h =>
    calc
      v a = v (b + -(-a + b)) := by simp
      _ = v b :=
        v.map_add_supp b <| (Ideal.neg_mem_iff _).2 <| hJ <| QuotientAddGroup.leftRel_apply.mp h

/-- The extension of valuation `v` on `R` to valuation on `R / J` if `J ⊆ supp v`. -/
/-
**Valuation.onQuot** 是 Mathlib 中的一个定义，位于命名空间 `Valuation`。
形式化陈述：onQuot {J : Ideal R} (hJ : J <= supp v) : Valuation (R ⧸ J) Γ₀ where toFun
参数：hJ : J <= supp v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The extension of valuation `v` on `R` to valuation on `R / J` if `J ⊆ supp v`.
-/
def onQuot {J : Ideal R} (hJ : J ≤ supp v) : Valuation (R ⧸ J) Γ₀ where
  toFun := v.onQuotVal hJ
  map_zero' := v.map_zero
  map_one' := v.map_one
  map_mul' xbar ybar := Quotient.ind₂' v.map_mul xbar ybar
  map_add_le_max' xbar ybar := Quotient.ind₂' v.map_add xbar ybar

@[simp]
/-
**Valuation.onQuot_comap_eq** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：onQuot_comap_eq {J : Ideal R} (hJ : J <= supp v) : (v.onQuot hJ).comap (Id
eal.Quotient.mk J) = v
参数：hJ : J <= supp v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.ext`：ext {v₁ v₂ : Valuation R Γ₀} (h : forall r, v₁ r = v₂ r) 
: v₁ = v₂
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
theorem onQuot_comap_eq {J : Ideal R} (hJ : J ≤ supp v) :
    (v.onQuot hJ).comap (Ideal.Quotient.mk J) = v :=
  ext fun _ => rfl
/-
**Valuation.self_le_supp_comap** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：self_le_supp_comap (J : Ideal R) (v : Valuation (R ⧸ J) Γ₀) : J <= (v.coma
p (Ideal.Quotient.mk J)).supp
参数：J : Ideal R；v : Valuation (R ⧸ J) Γ₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Valuation.comap_supp`：comap_supp {S : Type*} [CommRing S] (f : S ->+* R)
 : supp (v.comap f) = Ideal.comap f v.supp
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.map_le_iff_le_comap`：map_le_iff_le_comap [RingHomClass F R S] : ma
p f I <= K ↔ I <= comap f K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ideal.map_quotient_self`：map_quotient_self (I : Ideal R) [I.IsTwoSided] 
: map (Quotient.mk I) I = ⊥
-/
theorem self_le_supp_comap (J : Ideal R) (v : Valuation (R ⧸ J) Γ₀) :
    J ≤ (v.comap (Ideal.Quotient.mk J)).supp := by
  rw [comap_supp, ← Ideal.map_le_iff_le_comap]
  simp

@[simp]
/-
**Valuation.comap_onQuot_eq** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：comap_onQuot_eq (J : Ideal R) (v : Valuation (R ⧸ J) Γ₀) : (v.comap (Ideal
.Quotient.mk J)).onQuot (v.self_le_supp_comap J) = v
参数：J : Ideal R；v : Valuation (R ⧸ J) Γ₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.ext`：ext {v₁ v₂ : Valuation R Γ₀} (h : forall r, v₁ r = v₂ r) 
: v₁ = v₂
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Valuation.self_le_supp_comap`：self_le_supp_comap (J : Ideal R) (v : Valu
ation (R ⧸ J) Γ₀) : J <= (v.comap (Ideal.Quotient.mk J)).supp
-/
theorem comap_onQuot_eq (J : Ideal R) (v : Valuation (R ⧸ J) Γ₀) :
    (v.comap (Ideal.Quotient.mk J)).onQuot (v.self_le_supp_comap J) = v :=
  ext <| by
    rintro ⟨x⟩
    rfl

/-- The quotient valuation on `R / J` has support `(supp v) / J` if `J ⊆ supp v`. -/
/-
**Valuation.supp_quot** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：supp_quot {J : Ideal R} (hJ : J <= supp v) : supp (v.onQuot hJ) = (supp v)
.map (Ideal.Quotient.mk J)
参数：hJ : J <= supp v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.subset_span`：subset_span {s : Set α} : s subseteq span s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.map_le_iff_le_comap`：map_le_iff_le_comap [RingHomClass F R S] : ma
p f I <= K ↔ I <= comap f K

--- 原说明 ---
The quotient valuation on `R / J` has support `(supp v) / J` if `J ⊆ supp v`.
-/
theorem supp_quot {J : Ideal R} (hJ : J ≤ supp v) :
    supp (v.onQuot hJ) = (supp v).map (Ideal.Quotient.mk J) := by
  apply le_antisymm
  · rintro ⟨x⟩ hx
    apply Ideal.subset_span
    exact ⟨x, hx, rfl⟩
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact hx
/-
**Valuation.supp_quot_supp** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：supp_quot_supp : supp (v.onQuot le_rfl) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Valuation.supp_quot`：supp_quot {J : Ideal R} (hJ : J <= supp v) : supp (
v.onQuot hJ) = (supp v).map (Ideal.Quotient.mk J)
· 使用定理 `Ideal.map_quotient_self`：map_quotient_self (I : Ideal R) [I.IsTwoSided] 
: map (Quotient.mk I) I = ⊥
-/
theorem supp_quot_supp : supp (v.onQuot le_rfl) = 0 := by
  rw [supp_quot]
  exact Ideal.map_quotient_self _

end Valuation

namespace AddValuation

variable {R Γ₀ : Type*}
variable [CommRing R] [LinearOrderedAddCommMonoidWithTop Γ₀]
variable (v : AddValuation R Γ₀)

/-- If `hJ : J ⊆ supp v` then `onQuotVal hJ` is the induced function on `R / J` as a function.
Note: it's just the function; the valuation is `onQuot hJ`. -/
/-
**AddValuation.onQuotVal** 是 Mathlib 中的一个定义，位于命名空间 `AddValuation`。
形式化陈述：onQuotVal {J : Ideal R} (hJ : J <= supp v) : R ⧸ J -> Γ₀
参数：hJ : J <= supp v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `hJ : J ⊆ supp v` then `onQuotVal hJ` is the induced function on `R / J` as a
 function.
Note: it's just the function; the valuation is `onQuot hJ`.
-/
def onQuotVal {J : Ideal R} (hJ : J ≤ supp v) : R ⧸ J → Γ₀ :=
  Valuation.onQuotVal v hJ

/-- The extension of valuation `v` on `R` to valuation on `R / J` if `J ⊆ supp v`. -/
/-
**AddValuation.onQuot** 是 Mathlib 中的一个定义，位于命名空间 `AddValuation`。
形式化陈述：onQuot {J : Ideal R} (hJ : J <= supp v) : AddValuation (R ⧸ J) Γ₀
参数：hJ : J <= supp v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The extension of valuation `v` on `R` to valuation on `R / J` if `J ⊆ supp v`.
-/
def onQuot {J : Ideal R} (hJ : J ≤ supp v) : AddValuation (R ⧸ J) Γ₀ :=
  Valuation.onQuot v hJ

@[simp]
/-
**AddValuation.onQuot_comap_eq** 是 Mathlib 中的一个定理，位于命名空间 `AddValuation`。
形式化陈述：onQuot_comap_eq {J : Ideal R} (hJ : J <= supp v) : (v.onQuot hJ).comap (Id
eal.Quotient.mk J) = v
参数：hJ : J <= supp v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.onQuot_comap_eq`：onQuot_comap_eq {J : Ideal R} (hJ : J <= supp
 v) : (v.onQuot hJ).comap (Ideal.Quotient.mk J) = v
-/
theorem onQuot_comap_eq {J : Ideal R} (hJ : J ≤ supp v) :
    (v.onQuot hJ).comap (Ideal.Quotient.mk J) = v :=
  Valuation.onQuot_comap_eq v hJ
/-
**AddValuation.comap_supp** 是 Mathlib 中的一个定理，位于命名空间 `AddValuation`。
形式化陈述：comap_supp {S : Type*} [CommRing S] (f : S ->+* R) : supp (v.comap f) = Id
eal.comap f v.supp
参数：f : S ->+* R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.comap_supp`：comap_supp {S : Type*} [CommRing S] (f : S ->+* R)
 : supp (v.comap f) = Ideal.comap f v.supp
-/
theorem comap_supp {S : Type*} [CommRing S] (f : S →+* R) :
    supp (v.comap f) = Ideal.comap f v.supp :=
  Valuation.comap_supp v f
/-
**AddValuation.self_le_supp_comap** 是 Mathlib 中的一个定理，位于命名空间 `AddValuation`。
形式化陈述：self_le_supp_comap (J : Ideal R) (v : AddValuation (R ⧸ J) Γ₀) : J <= (v.c
omap (Ideal.Quotient.mk J)).supp
参数：J : Ideal R；v : AddValuation (R ⧸ J) Γ₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.self_le_supp_comap`：self_le_supp_comap (J : Ideal R) (v : Valu
ation (R ⧸ J) Γ₀) : J <= (v.comap (Ideal.Quotient.mk J)).supp
-/
theorem self_le_supp_comap (J : Ideal R) (v : AddValuation (R ⧸ J) Γ₀) :
    J ≤ (v.comap (Ideal.Quotient.mk J)).supp :=
  Valuation.self_le_supp_comap J v

@[simp]
/-
**AddValuation.comap_onQuot_eq** 是 Mathlib 中的一个定理，位于命名空间 `AddValuation`。
形式化陈述：comap_onQuot_eq (J : Ideal R) (v : AddValuation (R ⧸ J) Γ₀) : (v.comap (Id
eal.Quotient.mk J)).onQuot (v.self_le_supp_comap J) = v
参数：J : Ideal R；v : AddValuation (R ⧸ J) Γ₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.comap_onQuot_eq`：comap_onQuot_eq (J : Ideal R) (v : Valuation 
(R ⧸ J) Γ₀) : (v.comap (Ideal.Quotient.mk J)).onQuot (v.self_le_supp_comap J) = 
v
-/
theorem comap_onQuot_eq (J : Ideal R) (v : AddValuation (R ⧸ J) Γ₀) :
    (v.comap (Ideal.Quotient.mk J)).onQuot (v.self_le_supp_comap J) = v :=
  Valuation.comap_onQuot_eq J v

/-- The quotient valuation on `R / J` has support `(supp v) / J` if `J ⊆ supp v`. -/
/-
**AddValuation.supp_quot** 是 Mathlib 中的一个定理，位于命名空间 `AddValuation`。
形式化陈述：supp_quot {J : Ideal R} (hJ : J <= supp v) : supp (v.onQuot hJ) = (supp v)
.map (Ideal.Quotient.mk J)
参数：hJ : J <= supp v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.supp_quot`：supp_quot {J : Ideal R} (hJ : J <= supp v) : supp (
v.onQuot hJ) = (supp v).map (Ideal.Quotient.mk J)

--- 原说明 ---
The quotient valuation on `R / J` has support `(supp v) / J` if `J ⊆ supp v`.
-/
theorem supp_quot {J : Ideal R} (hJ : J ≤ supp v) :
    supp (v.onQuot hJ) = (supp v).map (Ideal.Quotient.mk J) :=
  Valuation.supp_quot v hJ
/-
**AddValuation.supp_quot_supp** 是 Mathlib 中的一个定理，位于命名空间 `AddValuation`。
形式化陈述：supp_quot_supp : supp ((Valuation.onQuot v) le_rfl) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.supp_quot_supp`：supp_quot_supp : supp (v.onQuot le_rfl) = 0
-/
theorem supp_quot_supp : supp ((Valuation.onQuot v) le_rfl) = 0 :=
  Valuation.supp_quot_supp v

end AddValuation

