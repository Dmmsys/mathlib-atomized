/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Interval.Finset.Basic
public import Mathlib.Data.Fintype.BigOperators

/-!
# Intervals in a pi type

This file shows that (dependent) functions to locally finite orders equipped with the pointwise
order are locally finite and calculates the cardinality of their intervals.
-/

public section


open Finset Fintype

variable {ι : Type*} {α : ι → Type*} [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (α i)]

namespace Pi
section PartialOrder
variable [∀ i, PartialOrder (α i)]

section LocallyFiniteOrder
variable [∀ i, LocallyFiniteOrder (α i)]

/-
**Pi.instLocallyFiniteOrder** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：instLocallyFiniteOrder : LocallyFiniteOrder (forall i, α i)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instLocallyFiniteOrder : LocallyFiniteOrder (∀ i, α i) :=
  LocallyFiniteOrder.ofIcc _ (fun a b => piFinset fun i => Icc (a i) (b i)) fun a b x => by
    simp_rw [mem_piFinset, mem_Icc, le_def, forall_and]

variable (a b : ∀ i, α i)
/-
**Pi.Icc_eq** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：Icc_eq : Icc a b = piFinset fun i => Icc (a i) (b i)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Icc_eq : Icc a b = piFinset fun i => Icc (a i) (b i) :=
  rfl
/-
**Pi.card_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：card_Icc : #(Icc a b) = ∏ i, #(Icc (a i) (b i))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.card_piFinset`：∀ {ι : Type u_4} {α : ι → Type u_6} [inst : Decid
ableEq ι] [inst_1 : Fintype ι] (s : (i : ι) → Finset (α i)),   (Fintype.piFinset
 s).card = …
-/
theorem card_Icc : #(Icc a b) = ∏ i, #(Icc (a i) (b i)) :=
  card_piFinset _
/-
**Pi.card_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：card_Ico : #(Ico a b) = ∏ i, #(Icc (a i) (b i)) - 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_Ico_eq_card_Icc_sub_one`：card_Ico_eq_card_Icc_sub_one (a b :
 α) : #(Ico a b) = #(Icc a b) - 1
· 使用定理 `Pi.card_Icc`：card_Icc : #(Icc a b) = ∏ i, #(Icc (a i) (b i))
-/
theorem card_Ico : #(Ico a b) = ∏ i, #(Icc (a i) (b i)) - 1 := by
  rw [card_Ico_eq_card_Icc_sub_one, card_Icc]
/-
**Pi.card_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：card_Ioc : #(Ioc a b) = ∏ i, #(Icc (a i) (b i)) - 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_Ioc_eq_card_Icc_sub_one`：card_Ioc_eq_card_Icc_sub_one (a b :
 α) : #(Ioc a b) = #(Icc a b) - 1
· 使用定理 `Pi.card_Icc`：card_Icc : #(Icc a b) = ∏ i, #(Icc (a i) (b i))
-/
theorem card_Ioc : #(Ioc a b) = ∏ i, #(Icc (a i) (b i)) - 1 := by
  rw [card_Ioc_eq_card_Icc_sub_one, card_Icc]
/-
**Pi.card_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：card_Ioo : #(Ioo a b) = ∏ i, #(Icc (a i) (b i)) - 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_Ioo_eq_card_Icc_sub_two`：card_Ioo_eq_card_Icc_sub_two (a b :
 α) : #(Ioo a b) = #(Icc a b) - 2
· 使用定理 `Pi.card_Icc`：card_Icc : #(Icc a b) = ∏ i, #(Icc (a i) (b i))
-/
theorem card_Ioo : #(Ioo a b) = ∏ i, #(Icc (a i) (b i)) - 2 := by
  rw [card_Ioo_eq_card_Icc_sub_two, card_Icc]

end LocallyFiniteOrder

section LocallyFiniteOrderBot
variable [∀ i, LocallyFiniteOrderBot (α i)] (b : ∀ i, α i)

/-
**Pi.instLocallyFiniteOrderBot** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：instLocallyFiniteOrderBot : LocallyFiniteOrderBot (forall i, α i)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instLocallyFiniteOrderBot : LocallyFiniteOrderBot (∀ i, α i) :=
  .ofIic _ (fun b => piFinset fun i => Iic (b i)) fun b x => by
    simp_rw [mem_piFinset, mem_Iic, le_def]
/-
**Pi.card_Iic** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：card_Iic : #(Iic b) = ∏ i, #(Iic (b i))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.card_piFinset`：∀ {ι : Type u_4} {α : ι → Type u_6} [inst : Decid
ableEq ι] [inst_1 : Fintype ι] (s : (i : ι) → Finset (α i)),   (Fintype.piFinset
 s).card = …
-/
lemma card_Iic : #(Iic b) = ∏ i, #(Iic (b i)) := card_piFinset _
/-
**Pi.card_Iio** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：card_Iio : #(Iio b) = ∏ i, #(Iic (b i)) - 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_Iio_eq_card_Iic_sub_one`：card_Iio_eq_card_Iic_sub_one (a : α
) : #(Iio a) = #(Iic a) - 1
· 使用引理 `Pi.card_Iic`：card_Iic : #(Iic b) = ∏ i, #(Iic (b i))
-/
lemma card_Iio : #(Iio b) = ∏ i, #(Iic (b i)) - 1 := by rw [card_Iio_eq_card_Iic_sub_one, card_Iic]

end LocallyFiniteOrderBot

section LocallyFiniteOrderTop
variable [∀ i, LocallyFiniteOrderTop (α i)] (a : ∀ i, α i)

/-
**Pi.instLocallyFiniteOrderTop** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：instLocallyFiniteOrderTop : LocallyFiniteOrderTop (forall i, α i)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instLocallyFiniteOrderTop : LocallyFiniteOrderTop (∀ i, α i) :=
  LocallyFiniteOrderTop.ofIci _ (fun a => piFinset fun i => Ici (a i)) fun a x => by
    simp_rw [mem_piFinset, mem_Ici, le_def]
/-
**Pi.card_Ici** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：card_Ici : #(Ici a) = ∏ i, #(Ici (a i))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.card_piFinset`：∀ {ι : Type u_4} {α : ι → Type u_6} [inst : Decid
ableEq ι] [inst_1 : Fintype ι] (s : (i : ι) → Finset (α i)),   (Fintype.piFinset
 s).card = …
-/
lemma card_Ici : #(Ici a) = ∏ i, #(Ici (a i)) := card_piFinset _
/-
**Pi.card_Ioi** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：card_Ioi : #(Ioi a) = ∏ i, #(Ici (a i)) - 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_Ioi_eq_card_Ici_sub_one`：card_Ioi_eq_card_Ici_sub_one (a : α
) : #(Ioi a) = #(Ici a) - 1
· 使用引理 `Pi.card_Ici`：card_Ici : #(Ici a) = ∏ i, #(Ici (a i))
-/
lemma card_Ioi : #(Ioi a) = ∏ i, #(Ici (a i)) - 1 := by rw [card_Ioi_eq_card_Ici_sub_one, card_Ici]

end LocallyFiniteOrderTop
end PartialOrder

section Lattice
variable [∀ i, Lattice (α i)] [∀ i, LocallyFiniteOrder (α i)] (a b : ∀ i, α i)

/-
**Pi.uIcc_eq** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：uIcc_eq : uIcc a b = piFinset fun i => uIcc (a i) (b i)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem uIcc_eq : uIcc a b = piFinset fun i => uIcc (a i) (b i) := rfl
/-
**Pi.card_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：card_uIcc : #(uIcc a b) = ∏ i, #(uIcc (a i) (b i))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.card_Icc`：card_Icc : #(Icc a b) = ∏ i, #(Icc (a i) (b i))
-/
theorem card_uIcc : #(uIcc a b) = ∏ i, #(uIcc (a i) (b i)) := card_Icc _ _

end Lattice
end Pi

