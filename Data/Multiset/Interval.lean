/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Data.DFinsupp.Interval
public import Mathlib.Data.DFinsupp.Multiset
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Algebra.Order.Group.Nat

/-!
# Finite intervals of multisets

This file provides the `LocallyFiniteOrder` instance for `Multiset α` and calculates the
cardinality of its finite intervals.

## Implementation notes

We implement the intervals via the intervals on `DFinsupp`, rather than via filtering
`Multiset.Powerset`; this is because `(Multiset.replicate n x).Powerset` has `2^n` entries not `n+1`
entries as it contains duplicates. We do not go via `Finsupp` as this would be noncomputable, and
multisets are typically used computationally.

-/

public section


open Finset DFinsupp Function

open scoped Pointwise

variable {α : Type*}

namespace Multiset

variable [DecidableEq α] (s t : Multiset α)

/-
**Multiset.instLocallyFiniteOrder** 是 Mathlib 中的一个实例，位于命名空间 `Multiset`。
形式化陈述：instLocallyFiniteOrder : LocallyFiniteOrder (Multiset α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
instance instLocallyFiniteOrder : LocallyFiniteOrder (Multiset α) :=
  LocallyFiniteOrder.ofIcc (Multiset α)
    (fun s t => (Finset.Icc (toDFinsupp s) (toDFinsupp t)).map
      Multiset.equivDFinsupp.toEquiv.symm.toEmbedding)
    fun s t x => by simp
/-
**Multiset.Icc_eq** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：Icc_eq : Finset.Icc s t = (Finset.Icc (toDFinsupp s) (toDFinsupp t)).map M
ultiset.equivDFinsupp.toEquiv.symm.toEmbedding
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Icc_eq :
    Finset.Icc s t = (Finset.Icc (toDFinsupp s) (toDFinsupp t)).map
      Multiset.equivDFinsupp.toEquiv.symm.toEmbedding :=
  rfl
/-
**Multiset.uIcc_eq** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：uIcc_eq : uIcc s t = (uIcc (toDFinsupp s) (toDFinsupp t)).map Multiset.equ
ivDFinsupp.toEquiv.symm.toEmbedding
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Multiset.Icc_eq`：Icc_eq : Finset.Icc s t = (Finset.Icc (toDFinsupp s) (t
oDFinsupp t)).map Multiset.equivDFinsupp.toEquiv.symm.toEmbedding
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Multiset.toDFinsupp_inter`：toDFinsupp_inter (s t : Multiset α) : toDFins
upp (s inter t) = toDFinsupp s ⊓ toDFinsupp t
· 使用定理 `Multiset.toDFinsupp_union`：toDFinsupp_union (s t : Multiset α) : toDFins
upp (s union t) = toDFinsupp s ⊔ toDFinsupp t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem uIcc_eq :
    uIcc s t =
      (uIcc (toDFinsupp s) (toDFinsupp t)).map Multiset.equivDFinsupp.toEquiv.symm.toEmbedding :=
  (Icc_eq _ _).trans <| by simp [uIcc]
/-
**Multiset.card_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：card_Icc : #(Finset.Icc s t) = ∏ i in s.toFinset union t.toFinset, (t.coun
t i + 1 - s.count i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用引理 `DFinsupp.card_Icc`：card_Icc : #(Icc f g) = ∏ i in f.support union g.supp
ort, #(Icc (f i) (g i))
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Nat.card_Icc`：∀ (a b : ℕ), (Finset.Icc a b).card = b + 1 - a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Multiset.toDFinsupp_support`：toDFinsupp_support (s : Multiset α) : s.toD
Finsupp.support = s.toFinset
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_Icc :
    #(Finset.Icc s t) = ∏ i ∈ s.toFinset ∪ t.toFinset, (t.count i + 1 - s.count i) := by
  simp_rw [Icc_eq, Finset.card_map, DFinsupp.card_Icc, Nat.card_Icc, Multiset.toDFinsupp_apply,
    toDFinsupp_support]
/-
**Multiset.card_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：card_Ico : #(Finset.Ico s t) = ∏ i in s.toFinset union t.toFinset, (t.coun
t i + 1 - s.count i) - 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_Ico_eq_card_Icc_sub_one`：card_Ico_eq_card_Icc_sub_one (a b :
 α) : #(Ico a b) = #(Icc a b) - 1
· 使用定理 `Multiset.card_Icc`：card_Icc : #(Finset.Icc s t) = ∏ i in s.toFinset unio
n t.toFinset, (t.count i + 1 - s.count i)
-/
theorem card_Ico :
    #(Finset.Ico s t) = ∏ i ∈ s.toFinset ∪ t.toFinset, (t.count i + 1 - s.count i) - 1 := by
  rw [Finset.card_Ico_eq_card_Icc_sub_one, card_Icc]
/-
**Multiset.card_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：card_Ioc : #(Finset.Ioc s t) = ∏ i in s.toFinset union t.toFinset, (t.coun
t i + 1 - s.count i) - 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_Ioc_eq_card_Icc_sub_one`：card_Ioc_eq_card_Icc_sub_one (a b :
 α) : #(Ioc a b) = #(Icc a b) - 1
· 使用定理 `Multiset.card_Icc`：card_Icc : #(Finset.Icc s t) = ∏ i in s.toFinset unio
n t.toFinset, (t.count i + 1 - s.count i)
-/
theorem card_Ioc :
    #(Finset.Ioc s t) = ∏ i ∈ s.toFinset ∪ t.toFinset, (t.count i + 1 - s.count i) - 1 := by
  rw [Finset.card_Ioc_eq_card_Icc_sub_one, card_Icc]
/-
**Multiset.card_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：card_Ioo : #(Finset.Ioo s t) = ∏ i in s.toFinset union t.toFinset, (t.coun
t i + 1 - s.count i) - 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_Ioo_eq_card_Icc_sub_two`：card_Ioo_eq_card_Icc_sub_two (a b :
 α) : #(Ioo a b) = #(Icc a b) - 2
· 使用定理 `Multiset.card_Icc`：card_Icc : #(Finset.Icc s t) = ∏ i in s.toFinset unio
n t.toFinset, (t.count i + 1 - s.count i)
-/
theorem card_Ioo :
    #(Finset.Ioo s t) = ∏ i ∈ s.toFinset ∪ t.toFinset, (t.count i + 1 - s.count i) - 2 := by
  rw [Finset.card_Ioo_eq_card_Icc_sub_two, card_Icc]
/-
**Multiset.card_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：card_uIcc : (uIcc s t).card = ∏ i in s.toFinset union t.toFinset, ((t.coun
t i - s.count i : Int).natAbs + 1)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.uIcc_eq`：uIcc_eq : uIcc s t = (uIcc (toDFinsupp s) (toDFinsupp 
t)).map Multiset.equivDFinsupp.toEquiv.symm.toEmbedding
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用引理 `DFinsupp.card_uIcc`：card_uIcc : #(uIcc f g) = ∏ i in f.support union g.s
upport, #(uIcc (f i) (g i))
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Nat.card_uIcc`：card_uIcc : #(uIcc a b) = (b - a : Int).natAbs + 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Multiset.toDFinsupp_support`：toDFinsupp_support (s : Multiset α) : s.toD
Finsupp.support = s.toFinset
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_uIcc :
    (uIcc s t).card = ∏ i ∈ s.toFinset ∪ t.toFinset, ((t.count i - s.count i : ℤ).natAbs + 1) := by
  simp_rw [uIcc_eq, Finset.card_map, DFinsupp.card_uIcc, Nat.card_uIcc, Multiset.toDFinsupp_apply,
    toDFinsupp_support]
/-
**Multiset.card_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：card_Iic : (Finset.Iic s).card = ∏ i in s.toFinset, (s.count i + 1)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.card_Icc`：card_Icc : #(Finset.Icc s t) = ∏ i in s.toFinset unio
n t.toFinset, (t.count i + 1 - s.count i)
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.empty_union`：empty_union (s : Finset α) : ∅ union s = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_Iic : (Finset.Iic s).card = ∏ i ∈ s.toFinset, (s.count i + 1) := by
  simp_rw [Iic_eq_Icc, card_Icc, bot_eq_zero, toFinset_zero, empty_union, count_zero, tsub_zero]

end Multiset

