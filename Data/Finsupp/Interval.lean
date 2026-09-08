/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Finset.Finsupp
public import Mathlib.Data.Finsupp.Order
public import Mathlib.Order.Interval.Finset.Basic

/-!
# Finite intervals of finitely supported functions

This file provides the `LocallyFiniteOrder` instance for `ι →₀ α` when `α` itself is locally
finite and calculates the cardinality of its finite intervals.

## Main declarations

* `Finsupp.rangeSingleton`: Postcomposition with `Singleton.singleton` on `Finset` as a
  `Finsupp`.
* `Finsupp.rangeIcc`: Postcomposition with `Finset.Icc` as a `Finsupp`.

Both these definitions use the fact that `0 = {0}` to ensure that the resulting function is finitely
supported.
-/

@[expose] public section

noncomputable section

open Finset Finsupp Function Pointwise

variable {ι α : Type*}

namespace Finsupp

section RangeSingleton

variable [Zero α] {f : ι →₀ α} {i : ι} {a : α}

/-- Pointwise `Singleton.singleton` bundled as a `Finsupp`. -/
@[simps]
/-
**Finsupp.rangeSingleton** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：rangeSingleton (f : ι ->₀ α) : ι ->₀ Finset α where toFun i
参数：f : ι ->₀ α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pointwise `Singleton.singleton` bundled as a `Finsupp`.
-/
def rangeSingleton (f : ι →₀ α) : ι →₀ Finset α where
  toFun i := {f i}
  support := f.support
  mem_support_toFun i := by
    rw [← not_iff_not, notMem_support_iff, not_ne_iff]
    exact singleton_injective.eq_iff.symm
/-
**Finsupp.mem_rangeSingleton_apply_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：mem_rangeSingleton_apply_iff : a in f.rangeSingleton i ↔ a = f i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Finset α) ↔ 
b = a
-/
theorem mem_rangeSingleton_apply_iff : a ∈ f.rangeSingleton i ↔ a = f i :=
  mem_singleton

end RangeSingleton

section RangeIcc

variable [Zero α] [PartialOrder α] [LocallyFiniteOrder α] [DecidableEq ι]
variable {f g : ι →₀ α} {i : ι} {a : α}

/-- Pointwise `Finset.Icc` bundled as a `Finsupp`. -/
@[simps apply]
/-
**Finsupp.rangeIcc** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：rangeIcc (f g : ι ->₀ α) : ι ->₀ Finset α where toFun i
参数：f g : ι ->₀ α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pointwise `Finset.Icc` bundled as a `Finsupp`.
-/
def rangeIcc (f g : ι →₀ α) : ι →₀ Finset α where
  toFun i := Icc (f i) (g i)
  support := f.support ∪ g.support
  mem_support_toFun i := by
    rw [mem_union, ← not_iff_not, not_or, notMem_support_iff, notMem_support_iff, not_ne_iff]
    exact Icc_eq_singleton_iff.symm
/-
**Finsupp.coe_rangeIcc** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：coe_rangeIcc (f g : ι ->₀ α) : rangeIcc f g i = Icc (f i) (g i)
参数：f g : ι ->₀ α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_rangeIcc (f g : ι →₀ α) : rangeIcc f g i = Icc (f i) (g i) := rfl

@[simp]
/-
**Finsupp.rangeIcc_support** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：rangeIcc_support (f g : ι ->₀ α) : (rangeIcc f g).support = f.support unio
n g.support
参数：f g : ι ->₀ α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rangeIcc_support (f g : ι →₀ α) :
    (rangeIcc f g).support = f.support ∪ g.support := rfl
/-
**Finsupp.mem_rangeIcc_apply_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：mem_rangeIcc_apply_iff : a in f.rangeIcc g i ↔ f i <= a ∧ a <= g i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_Icc`：mem_Icc : x in Icc a b ↔ a <= x ∧ x <= b
-/
theorem mem_rangeIcc_apply_iff : a ∈ f.rangeIcc g i ↔ f i ≤ a ∧ a ≤ g i := mem_Icc

end RangeIcc

section PartialOrder

variable [PartialOrder α] [Zero α] [LocallyFiniteOrder α] [DecidableEq ι] [DecidableEq α]
variable (f g : ι →₀ α)

/-
**Finsupp.instLocallyFiniteOrder** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：instLocallyFiniteOrder : LocallyFiniteOrder (ι ->₀ α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instLocallyFiniteOrder : LocallyFiniteOrder (ι →₀ α) :=
  LocallyFiniteOrder.ofIcc (ι →₀ α) (fun f g => (f.support ∪ g.support).finsupp <| f.rangeIcc g)
    fun f g x => by
      refine
        (mem_finsupp_iff_of_support_subset <| Finset.subset_of_eq <| rangeIcc_support _ _).trans ?_
      simp_rw [mem_rangeIcc_apply_iff]
      exact forall_and
/-
**Finsupp.Icc_eq** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：Icc_eq : Icc f g = (f.support union g.support).finsupp (f.rangeIcc g)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Icc_eq : Icc f g = (f.support ∪ g.support).finsupp (f.rangeIcc g) := rfl
/-
**Finsupp.card_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：card_Icc : #(Icc f g) = ∏ i in f.support union g.support, #(Icc (f i) (g i
))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_finsupp`：card_finsupp (s : Finset ι) (t : ι -> Finset α) : #
(s.finsupp t) = ∏ i in s, #(t i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_Icc : #(Icc f g) = ∏ i ∈ f.support ∪ g.support, #(Icc (f i) (g i)) := by
  simp_rw [Icc_eq, card_finsupp, coe_rangeIcc]
/-
**Finsupp.card_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：card_Ico : #(Ico f g) = ∏ i in f.support union g.support, #(Icc (f i) (g i
)) - 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_Ico_eq_card_Icc_sub_one`：card_Ico_eq_card_Icc_sub_one (a b :
 α) : #(Ico a b) = #(Icc a b) - 1
· 使用定理 `Finsupp.card_Icc`：card_Icc : #(Icc f g) = ∏ i in f.support union g.suppo
rt, #(Icc (f i) (g i))
-/
theorem card_Ico : #(Ico f g) = ∏ i ∈ f.support ∪ g.support, #(Icc (f i) (g i)) - 1 := by
  rw [card_Ico_eq_card_Icc_sub_one, card_Icc]
/-
**Finsupp.card_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：card_Ioc : #(Ioc f g) = ∏ i in f.support union g.support, #(Icc (f i) (g i
)) - 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_Ioc_eq_card_Icc_sub_one`：card_Ioc_eq_card_Icc_sub_one (a b :
 α) : #(Ioc a b) = #(Icc a b) - 1
· 使用定理 `Finsupp.card_Icc`：card_Icc : #(Icc f g) = ∏ i in f.support union g.suppo
rt, #(Icc (f i) (g i))
-/
theorem card_Ioc : #(Ioc f g) = ∏ i ∈ f.support ∪ g.support, #(Icc (f i) (g i)) - 1 := by
  rw [card_Ioc_eq_card_Icc_sub_one, card_Icc]
/-
**Finsupp.card_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：card_Ioo : #(Ioo f g) = ∏ i in f.support union g.support, #(Icc (f i) (g i
)) - 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_Ioo_eq_card_Icc_sub_two`：card_Ioo_eq_card_Icc_sub_two (a b :
 α) : #(Ioo a b) = #(Icc a b) - 2
· 使用定理 `Finsupp.card_Icc`：card_Icc : #(Icc f g) = ∏ i in f.support union g.suppo
rt, #(Icc (f i) (g i))
-/
theorem card_Ioo : #(Ioo f g) = ∏ i ∈ f.support ∪ g.support, #(Icc (f i) (g i)) - 2 := by
  rw [card_Ioo_eq_card_Icc_sub_two, card_Icc]

end PartialOrder

section Lattice
variable [Lattice α] [Zero α] [LocallyFiniteOrder α] (f g : ι →₀ α)

open scoped Classical in
/-
**Finsupp.card_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：card_uIcc : #(uIcc f g) = ∏ i in f.support union g.support, #(uIcc (f i) (
g i))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finsupp.support_inf_union_support_sup`：support_inf_union_support_sup : (
f ⊓ g).support union (f ⊔ g).support = f.support union g.support
· 使用定理 `Finsupp.card_Icc`：card_Icc : #(Icc f g) = ∏ i in f.support union g.suppo
rt, #(Icc (f i) (g i))
-/
theorem card_uIcc :
    #(uIcc f g) = ∏ i ∈ f.support ∪ g.support, #(uIcc (f i) (g i)) := by
  rw [← support_inf_union_support_sup]; exact card_Icc (_ : ι →₀ α) _

end Lattice

section IsBotZeroClass

variable [AddCommMonoid α] [PartialOrder α] [IsBotZeroClass α]
  [OrderBot α] [LocallyFiniteOrder α]
variable [DecidableEq ι] [DecidableEq α] (f : ι →₀ α)

/-
**Finsupp.card_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：card_Iic : #(Iic f) = ∏ i in f.support, #(Iic (f i))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `bot_eq_zero`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero α] 
[IsBotZeroClass α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `Finsupp.instIsBotZeroClass`：∀ {ι : Type u_1} {α : Type u_3} [inst : AddC
ommMonoid α] [inst_1 : PartialOrder α] [IsBotZeroClass α],   IsBotZeroClass (ι →
₀ α)
· 使用定理 `Finsupp.card_Icc`：card_Icc : #(Icc f g) = ∏ i in f.support union g.suppo
rt, #(Icc (f i) (g i))
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.empty_union`：empty_union (s : Finset α) : ∅ union s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_Iic : #(Iic f) = ∏ i ∈ f.support, #(Iic (f i)) := by
  simp [Iic_eq_Icc, card_Icc, bot_eq_zero]
/-
**Finsupp.card_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：card_Iio : #(Iio f) = ∏ i in f.support, #(Iic (f i)) - 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_Iio_eq_card_Iic_sub_one`：card_Iio_eq_card_Iic_sub_one (a : α
) : #(Iio a) = #(Iic a) - 1
· 使用定理 `Finsupp.card_Iic`：card_Iic : #(Iic f) = ∏ i in f.support, #(Iic (f i))
-/
theorem card_Iio : #(Iio f) = ∏ i ∈ f.support, #(Iic (f i)) - 1 := by
  rw [card_Iio_eq_card_Iic_sub_one, card_Iic]

end IsBotZeroClass

end Finsupp

