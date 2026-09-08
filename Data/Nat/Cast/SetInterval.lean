/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Order.Interval.Set.OrdConnected
public import Mathlib.Order.Nat
public import Mathlib.Order.UpperLower.Basic

/-!
# Images of intervals under `Nat.cast : ℕ → ℤ`

In this file we prove that the image of each `Set.Ixx` interval under `Nat.cast : ℕ → ℤ`
is the corresponding interval in `ℤ`.
-/

public section

open Set

namespace Nat

@[simp]
/-
**Nat.range_cast_int** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：range_cast_int : range ((↑) : Nat -> Int) = Ici 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `Int.natCast_nonneg`：∀ (n : ℕ), 0 ≤ ↑n
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `instCanLiftIntNatCastLeOfNat`：CanLift ℤ ℕ (fun n => ↑n) fun x => 0 ≤ x
-/
theorem range_cast_int : range ((↑) : ℕ → ℤ) = Ici 0 :=
  Subset.antisymm (range_subset_iff.2 Int.natCast_nonneg) CanLift.prf
/-
**Nat.image_cast_int_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：image_cast_int_Icc (a b : Nat) : (↑) '' Icc a b = Icc (a : Int) b
参数：a b : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.image_Icc`：image_Icc (e : α ↪o β) (he : OrdConnected (ran
ge e)) (x y : α) : e '' Icc x y = Icc (e x) (e y)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.castOrderEmbedding_apply`：∀ {α : Type u_1} [inst : AddMonoidWithOne 
α] [inst_1 : PartialOrder α] [inst_2 : AddLeftMono α]   [inst_3 : ZeroLEOneClass
 α] [inst_4 : Char…
· 使用定理 `Nat.range_cast_int`：range_cast_int : range ((↑) : Nat -> Int) = Ici 0
-/
theorem image_cast_int_Icc (a b : ℕ) : (↑) '' Icc a b = Icc (a : ℤ) b :=
  (castOrderEmbedding (α := ℤ)).image_Icc (by simp [ordConnected_Ici]) a b
/-
**Nat.image_cast_int_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：image_cast_int_Ico (a b : Nat) : (↑) '' Ico a b = Ico (a : Int) b
参数：a b : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.image_Ico`：image_Ico (e : α ↪o β) (he : OrdConnected (ran
ge e)) (x y : α) : e '' Ico x y = Ico (e x) (e y)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.castOrderEmbedding_apply`：∀ {α : Type u_1} [inst : AddMonoidWithOne 
α] [inst_1 : PartialOrder α] [inst_2 : AddLeftMono α]   [inst_3 : ZeroLEOneClass
 α] [inst_4 : Char…
· 使用定理 `Nat.range_cast_int`：range_cast_int : range ((↑) : Nat -> Int) = Ici 0
-/
theorem image_cast_int_Ico (a b : ℕ) : (↑) '' Ico a b = Ico (a : ℤ) b :=
  (castOrderEmbedding (α := ℤ)).image_Ico (by simp [ordConnected_Ici]) a b
/-
**Nat.image_cast_int_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：image_cast_int_Ioc (a b : Nat) : (↑) '' Ioc a b = Ioc (a : Int) b
参数：a b : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.image_Ioc`：image_Ioc (e : α ↪o β) (he : OrdConnected (ran
ge e)) (x y : α) : e '' Ioc x y = Ioc (e x) (e y)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.castOrderEmbedding_apply`：∀ {α : Type u_1} [inst : AddMonoidWithOne 
α] [inst_1 : PartialOrder α] [inst_2 : AddLeftMono α]   [inst_3 : ZeroLEOneClass
 α] [inst_4 : Char…
· 使用定理 `Nat.range_cast_int`：range_cast_int : range ((↑) : Nat -> Int) = Ici 0
-/
theorem image_cast_int_Ioc (a b : ℕ) : (↑) '' Ioc a b = Ioc (a : ℤ) b :=
  (castOrderEmbedding (α := ℤ)).image_Ioc (by simp [ordConnected_Ici]) a b
/-
**Nat.image_cast_int_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：image_cast_int_Ioo (a b : Nat) : (↑) '' Ioo a b = Ioo (a : Int) b
参数：a b : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.image_Ioo`：image_Ioo (e : α ↪o β) (he : OrdConnected (ran
ge e)) (x y : α) : e '' Ioo x y = Ioo (e x) (e y)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.castOrderEmbedding_apply`：∀ {α : Type u_1} [inst : AddMonoidWithOne 
α] [inst_1 : PartialOrder α] [inst_2 : AddLeftMono α]   [inst_3 : ZeroLEOneClass
 α] [inst_4 : Char…
· 使用定理 `Nat.range_cast_int`：range_cast_int : range ((↑) : Nat -> Int) = Ici 0
-/
theorem image_cast_int_Ioo (a b : ℕ) : (↑) '' Ioo a b = Ioo (a : ℤ) b :=
  (castOrderEmbedding (α := ℤ)).image_Ioo (by simp [ordConnected_Ici]) a b
/-
**Nat.image_cast_int_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：image_cast_int_Iic (a : Nat) : (↑) '' Iic a = Icc (0 : Int) a
参数：a : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Icc_bot`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : OrderBot α] 
{a : α}, Set.Icc ⊥ a = Set.Iic a
· 使用定理 `Nat.image_cast_int_Icc`：image_cast_int_Icc (a b : Nat) : (↑) '' Icc a b 
= Icc (a : Int) b
-/
theorem image_cast_int_Iic (a : ℕ) : (↑) '' Iic a = Icc (0 : ℤ) a := by
  rw [← Icc_bot, image_cast_int_Icc]; rfl
/-
**Nat.image_cast_int_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：image_cast_int_Iio (a : Nat) : (↑) '' Iio a = Ico (0 : Int) a
参数：a : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Ico_bot`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : OrderBot α] 
{a : α}, Set.Ico ⊥ a = Set.Iio a
· 使用定理 `Nat.image_cast_int_Ico`：image_cast_int_Ico (a b : Nat) : (↑) '' Ico a b 
= Ico (a : Int) b
-/
theorem image_cast_int_Iio (a : ℕ) : (↑) '' Iio a = Ico (0 : ℤ) a := by
  rw [← Ico_bot, image_cast_int_Ico]; rfl
/-
**Nat.image_cast_int_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：image_cast_int_Ici (a : Nat) : (↑) '' Ici a = Ici (a : Int)
参数：a : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.image_Ici`：OrderEmbedding.image_Ici (e : α ↪o β) (he : Is
UpperSet (range e)) (a : α) : e '' Ici a = Ici (e a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.castOrderEmbedding_apply`：∀ {α : Type u_1} [inst : AddMonoidWithOne 
α] [inst_1 : PartialOrder α] [inst_2 : AddLeftMono α]   [inst_3 : ZeroLEOneClass
 α] [inst_4 : Char…
· 使用定理 `Nat.range_cast_int`：range_cast_int : range ((↑) : Nat -> Int) = Ici 0
-/
theorem image_cast_int_Ici (a : ℕ) : (↑) '' Ici a = Ici (a : ℤ) :=
  (castOrderEmbedding (α := ℤ)).image_Ici (by simp [isUpperSet_Ici]) a
/-
**Nat.image_cast_int_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：image_cast_int_Ioi (a : Nat) : (↑) '' Ioi a = Ioi (a : Int)
参数：a : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.image_Ioi`：OrderEmbedding.image_Ioi (e : α ↪o β) (he : Is
UpperSet (range e)) (a : α) : e '' Ioi a = Ioi (e a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.castOrderEmbedding_apply`：∀ {α : Type u_1} [inst : AddMonoidWithOne 
α] [inst_1 : PartialOrder α] [inst_2 : AddLeftMono α]   [inst_3 : ZeroLEOneClass
 α] [inst_4 : Char…
· 使用定理 `Nat.range_cast_int`：range_cast_int : range ((↑) : Nat -> Int) = Ici 0
-/
theorem image_cast_int_Ioi (a : ℕ) : (↑) '' Ioi a = Ioi (a : ℤ) :=
  (castOrderEmbedding (α := ℤ)).image_Ioi (by simp [isUpperSet_Ici]) a

end Nat

