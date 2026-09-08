/-
Copyright (c) 2026 Yael Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yael Dillies
-/
module

public import Mathlib.Data.Set.Card

import Mathlib.Order.Interval.Finset.Nat

/-!
# Finite intervals of naturals

This file calculates the cardinality of intervals of natural numbers as sets.
-/

public section

namespace Set

/-
**Set.ncard_Icc_nat** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ (a b : ℕ), (Set.Icc a b).ncard = b + 1 - a
参数：a b : ℕ；Set.Icc a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_Icc`：coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b
· 使用定理 `Nat.card_Icc`：∀ (a b : ℕ), (Finset.Icc a b).card = b + 1 - a
-/
@[simp] lemma ncard_Icc_nat (a b : ℕ) : (Icc a b).ncard = b + 1 - a := by
  simpa [← Set.ncard_coe_finset] using Nat.card_Icc a b
/-
**Set.ncard_Ico_nat** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ (a b : ℕ), (Set.Ico a b).ncard = b - a
参数：a b : ℕ；Set.Ico a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用定理 `Nat.card_Ico`：∀ (a b : ℕ), (Finset.Ico a b).card = b - a
-/
@[simp] lemma ncard_Ico_nat (a b : ℕ) : (Ico a b).ncard = b - a := by
  simpa [← Set.ncard_coe_finset] using Nat.card_Ico a b
/-
**Set.ncard_Ioc_nat** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ (a b : ℕ), (Set.Ioc a b).ncard = b - a
参数：a b : ℕ；Set.Ioc a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_Ioc`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrder α] (b a : α), ↑(Finset.Ioc b a) = Set.Ioc b a
· 使用定理 `Nat.card_Ioc`：∀ (a b : ℕ), (Finset.Ioc a b).card = b - a
-/
@[simp] lemma ncard_Ioc_nat (a b : ℕ) : (Ioc a b).ncard = b - a := by
  simpa [← Set.ncard_coe_finset] using Nat.card_Ioc a b
/-
**Set.ncard_Ioo_nat** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ (a b : ℕ), (Set.Ioo a b).ncard = b - a - 1
参数：a b : ℕ；Set.Ioo a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_Ioo`：coe_Ioo (a b : α) : (Ioo a b : Set α) = Set.Ioo a b
· 使用定理 `Nat.card_Ioo`：∀ (a b : ℕ), (Finset.Ioo a b).card = b - a - 1
-/
@[simp] lemma ncard_Ioo_nat (a b : ℕ) : (Ioo a b).ncard = b - a - 1 := by
  simpa [← Set.ncard_coe_finset] using Nat.card_Ioo a b
/-
**Set.ncard_uIcc_nat** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ (a b : ℕ), (Set.uIcc a b).ncard = (↑b - ↑a).natAbs + 1
参数：a b : ℕ；Set.uIcc a b；↑b - ↑a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_uIcc`：coe_uIcc (a b : α) : (Finset.uIcc a b : Set α) = Set.uI
cc a b
· 使用定理 `Nat.card_uIcc`：card_uIcc : #(uIcc a b) = (b - a : Int).natAbs + 1
-/
@[simp] lemma ncard_uIcc_nat (a b : ℕ) : (uIcc a b).ncard = (b - a : ℤ).natAbs + 1 := by
  simpa [← Set.ncard_coe_finset] using Nat.card_uIcc a b
/-
**Set.ncard_Iic_nat** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ (b : ℕ), (Set.Iic b).ncard = b + 1
参数：b : ℕ；Set.Iic b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iic a) = Set.Iic a
· 使用引理 `Nat.card_Iic`：card_Iic : #(Iic b) = b + 1
-/
@[simp] lemma ncard_Iic_nat (b : ℕ) : (Iic b).ncard = b + 1 := by
  simpa [← Set.ncard_coe_finset] using Nat.card_Iic b
/-
**Set.ncard_Iio_nat** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ (b : ℕ), (Set.Iio b).ncard = b
参数：b : ℕ；Set.Iio b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_Iio`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iio a) = Set.Iio a
· 使用定理 `Nat.card_Iio`：card_Iio : #(Iio b) = b
-/
@[simp] lemma ncard_Iio_nat (b : ℕ) : (Iio b).ncard = b := by
  simpa [← Set.ncard_coe_finset] using Nat.card_Iio b

end Set

