/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Sigma.Order
public import Mathlib.Order.Interval.Finset.Defs

/-!
# Finite intervals in a sigma type

This file provides the `LocallyFiniteOrder` instance for the disjoint sum of orders `Σ i, α i` and
calculates the cardinality of its finite intervals.

## TODO

Do the same for the lexicographical order
-/

public section


open Finset Function

namespace Sigma

variable {ι : Type*} {α : ι → Type*}

/-! ### Disjoint sum of orders -/


section Disjoint

section LocallyFiniteOrder
variable [DecidableEq ι] [∀ i, Preorder (α i)] [∀ i, LocallyFiniteOrder (α i)]

/-
**Sigma.instLocallyFiniteOrder** 是 Mathlib 中的一个实例，位于命名空间 `Sigma`。
形式化陈述：instLocallyFiniteOrder : LocallyFiniteOrder (Σ i, α i) where finsetIcc
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instLocallyFiniteOrder : LocallyFiniteOrder (Σ i, α i) where
  finsetIcc := sigmaLift fun _ => Icc
  finsetIco := sigmaLift fun _ => Ico
  finsetIoc := sigmaLift fun _ => Ioc
  finsetIoo := sigmaLift fun _ => Ioo
  finset_mem_Icc := fun ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩ => by
    simp_rw [mem_sigmaLift, le_def, mem_Icc, exists_and_left, ← exists_and_right, ← exists_prop]
    exact exists₂_congr fun _ _ => by constructor <;> rintro ⟨⟨⟩, ht⟩ <;> exact ⟨rfl, ht⟩
  finset_mem_Ico := fun ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩ => by
    simp_rw [mem_sigmaLift, le_def, lt_def, mem_Ico, exists_and_left, ← exists_and_right, ←
      exists_prop]
    exact exists₂_congr fun _ _ => by constructor <;> rintro ⟨⟨⟩, ht⟩ <;> exact ⟨rfl, ht⟩
  finset_mem_Ioc := fun ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩ => by
    simp_rw [mem_sigmaLift, le_def, lt_def, mem_Ioc, exists_and_left, ← exists_and_right, ←
      exists_prop]
    exact exists₂_congr fun _ _ => by constructor <;> rintro ⟨⟨⟩, ht⟩ <;> exact ⟨rfl, ht⟩
  finset_mem_Ioo := fun ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩ => by
    simp_rw [mem_sigmaLift, lt_def, mem_Ioo, exists_and_left, ← exists_and_right, ← exists_prop]
    exact exists₂_congr fun _ _ => by constructor <;> rintro ⟨⟨⟩, ht⟩ <;> exact ⟨rfl, ht⟩

section

variable (a b : Σ i, α i)

/-
**Sigma.card_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Sigma`。
形式化陈述：card_Icc : #(Icc a b) = if h : a.1 = b.1 then #(Icc (h.rec a.2) b.2) else 
0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_sigmaLift`：card_sigmaLift : (sigmaLift f a b).card = dite (a
.1 = b.1) (fun h => (f (h ▸ a.2) b.2).card) fun _ => 0
-/
theorem card_Icc : #(Icc a b) = if h : a.1 = b.1 then #(Icc (h.rec a.2) b.2) else 0 :=
  card_sigmaLift (fun _ => Icc) _ _
/-
**Sigma.card_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Sigma`。
形式化陈述：card_Ico : #(Ico a b) = if h : a.1 = b.1 then #(Ico (h.rec a.2) b.2) else 
0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_sigmaLift`：card_sigmaLift : (sigmaLift f a b).card = dite (a
.1 = b.1) (fun h => (f (h ▸ a.2) b.2).card) fun _ => 0
-/
theorem card_Ico : #(Ico a b) = if h : a.1 = b.1 then #(Ico (h.rec a.2) b.2) else 0 :=
  card_sigmaLift (fun _ => Ico) _ _
/-
**Sigma.card_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Sigma`。
形式化陈述：card_Ioc : #(Ioc a b) = if h : a.1 = b.1 then #(Ioc (h.rec a.2) b.2) else 
0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_sigmaLift`：card_sigmaLift : (sigmaLift f a b).card = dite (a
.1 = b.1) (fun h => (f (h ▸ a.2) b.2).card) fun _ => 0
-/
theorem card_Ioc : #(Ioc a b) = if h : a.1 = b.1 then #(Ioc (h.rec a.2) b.2) else 0 :=
  card_sigmaLift (fun _ => Ioc) _ _
/-
**Sigma.card_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Sigma`。
形式化陈述：card_Ioo : #(Ioo a b) = if h : a.1 = b.1 then #(Ioo (h.rec a.2) b.2) else 
0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_sigmaLift`：card_sigmaLift : (sigmaLift f a b).card = dite (a
.1 = b.1) (fun h => (f (h ▸ a.2) b.2).card) fun _ => 0
-/
theorem card_Ioo : #(Ioo a b) = if h : a.1 = b.1 then #(Ioo (h.rec a.2) b.2) else 0 :=
  card_sigmaLift (fun _ => Ioo) _ _

end

variable (i : ι) (a b : α i)

@[simp]
/-
**Sigma.Icc_mk_mk** 是 Mathlib 中的一个定理，位于命名空间 `Sigma`。
形式化陈述：Icc_mk_mk : Icc (⟨i, a⟩ : Sigma α) ⟨i, b⟩ = (Icc a b).map (Embedding.sigma
Mk i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem Icc_mk_mk : Icc (⟨i, a⟩ : Sigma α) ⟨i, b⟩ = (Icc a b).map (Embedding.sigmaMk i) :=
  dif_pos rfl

@[simp]
/-
**Sigma.Ico_mk_mk** 是 Mathlib 中的一个定理，位于命名空间 `Sigma`。
形式化陈述：Ico_mk_mk : Ico (⟨i, a⟩ : Sigma α) ⟨i, b⟩ = (Ico a b).map (Embedding.sigma
Mk i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem Ico_mk_mk : Ico (⟨i, a⟩ : Sigma α) ⟨i, b⟩ = (Ico a b).map (Embedding.sigmaMk i) :=
  dif_pos rfl

@[simp]
/-
**Sigma.Ioc_mk_mk** 是 Mathlib 中的一个定理，位于命名空间 `Sigma`。
形式化陈述：Ioc_mk_mk : Ioc (⟨i, a⟩ : Sigma α) ⟨i, b⟩ = (Ioc a b).map (Embedding.sigma
Mk i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem Ioc_mk_mk : Ioc (⟨i, a⟩ : Sigma α) ⟨i, b⟩ = (Ioc a b).map (Embedding.sigmaMk i) :=
  dif_pos rfl

@[simp]
/-
**Sigma.Ioo_mk_mk** 是 Mathlib 中的一个定理，位于命名空间 `Sigma`。
形式化陈述：Ioo_mk_mk : Ioo (⟨i, a⟩ : Sigma α) ⟨i, b⟩ = (Ioo a b).map (Embedding.sigma
Mk i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem Ioo_mk_mk : Ioo (⟨i, a⟩ : Sigma α) ⟨i, b⟩ = (Ioo a b).map (Embedding.sigmaMk i) :=
  dif_pos rfl

end LocallyFiniteOrder

section LocallyFiniteOrderBot
variable [∀ i, Preorder (α i)] [∀ i, LocallyFiniteOrderBot (α i)]

/-
**Sigma.instLocallyFiniteOrderBot** 是 Mathlib 中的一个实例，位于命名空间 `Sigma`。
形式化陈述：instLocallyFiniteOrderBot : LocallyFiniteOrderBot (Σ i, α i) where finsetI
ic | ⟨i, a⟩ => (Iic a).map (Embedding.sigmaMk i) finsetIio | ⟨i, a⟩ => (Iio a).m
ap (Embedding.sigmaMk i) finset_mem_Iic
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instLocallyFiniteOrderBot : LocallyFiniteOrderBot (Σ i, α i) where
  finsetIic | ⟨i, a⟩ => (Iic a).map (Embedding.sigmaMk i)
  finsetIio | ⟨i, a⟩ => (Iio a).map (Embedding.sigmaMk i)
  finset_mem_Iic := fun ⟨i, a⟩ ⟨j, b⟩ => by
    obtain rfl | hij := eq_or_ne i j
    · simp
    · simp [hij, le_def, hij.symm]
  finset_mem_Iio := fun ⟨i, a⟩ ⟨j, b⟩ => by
    obtain rfl | hij := eq_or_ne i j
    · simp
    · simp [hij, lt_def, hij.symm]

variable (i : ι) (a : α i)
/-
**Sigma.Iic_mk** 是 Mathlib 中的一个定理，位于命名空间 `Sigma`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : (i : ι) → Preorder (α i)] [ins
t_1 : (i : ι) → LocallyFiniteOrderBot (α i)]   (i : ι) (a : α i), Finset.Iic ⟨i,
 a⟩ = Finset.map (Function.Embedding.sigmaMk i) (Finset.Iic a)
参数：i : ι；α i；i : ι；α i；i : ι；a : α i；Function.Embedding.sigmaMk i；Finset.Iic a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem Iic_mk : Iic (⟨i, a⟩ : Sigma α) = (Iic a).map (Embedding.sigmaMk i) := rfl
/-
**Sigma.Iio_mk** 是 Mathlib 中的一个定理，位于命名空间 `Sigma`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : (i : ι) → Preorder (α i)] [ins
t_1 : (i : ι) → LocallyFiniteOrderBot (α i)]   (i : ι) (a : α i), Finset.Iio ⟨i,
 a⟩ = Finset.map (Function.Embedding.sigmaMk i) (Finset.Iio a)
参数：i : ι；α i；i : ι；α i；i : ι；a : α i；Function.Embedding.sigmaMk i；Finset.Iio a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem Iio_mk : Iio (⟨i, a⟩ : Sigma α) = (Iio a).map (Embedding.sigmaMk i) := rfl

end LocallyFiniteOrderBot

section LocallyFiniteOrderTop
variable [∀ i, Preorder (α i)] [∀ i, LocallyFiniteOrderTop (α i)]

/-
**Sigma.instLocallyFiniteOrderTop** 是 Mathlib 中的一个实例，位于命名空间 `Sigma`。
形式化陈述：instLocallyFiniteOrderTop : LocallyFiniteOrderTop (Σ i, α i) where finsetI
ci | ⟨i, a⟩ => (Ici a).map (Embedding.sigmaMk i) finsetIoi | ⟨i, a⟩ => (Ioi a).m
ap (Embedding.sigmaMk i) finset_mem_Ici
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instLocallyFiniteOrderTop : LocallyFiniteOrderTop (Σ i, α i) where
  finsetIci | ⟨i, a⟩ => (Ici a).map (Embedding.sigmaMk i)
  finsetIoi | ⟨i, a⟩ => (Ioi a).map (Embedding.sigmaMk i)
  finset_mem_Ici := fun ⟨i, a⟩ ⟨j, b⟩ => by
    obtain rfl | hij := eq_or_ne i j
    · simp
    · simp [hij, le_def]
  finset_mem_Ioi := fun ⟨i, a⟩ ⟨j, b⟩ => by
    obtain rfl | hij := eq_or_ne i j
    · simp
    · simp [hij, lt_def]

variable (i : ι) (a : α i)
/-
**Sigma.Ici_mk** 是 Mathlib 中的一个定理，位于命名空间 `Sigma`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : (i : ι) → Preorder (α i)] [ins
t_1 : (i : ι) → LocallyFiniteOrderTop (α i)]   (i : ι) (a : α i), Finset.Ici ⟨i,
 a⟩ = Finset.map (Function.Embedding.sigmaMk i) (Finset.Ici a)
参数：i : ι；α i；i : ι；α i；i : ι；a : α i；Function.Embedding.sigmaMk i；Finset.Ici a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem Ici_mk : Ici (⟨i, a⟩ : Sigma α) = (Ici a).map (Embedding.sigmaMk i) := rfl
/-
**Sigma.Ioi_mk** 是 Mathlib 中的一个定理，位于命名空间 `Sigma`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : (i : ι) → Preorder (α i)] [ins
t_1 : (i : ι) → LocallyFiniteOrderTop (α i)]   (i : ι) (a : α i), Finset.Ioi ⟨i,
 a⟩ = Finset.map (Function.Embedding.sigmaMk i) (Finset.Ioi a)
参数：i : ι；α i；i : ι；α i；i : ι；a : α i；Function.Embedding.sigmaMk i；Finset.Ioi a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem Ioi_mk : Ioi (⟨i, a⟩ : Sigma α) = (Ioi a).map (Embedding.sigmaMk i) := rfl

end LocallyFiniteOrderTop

end Disjoint

end Sigma

