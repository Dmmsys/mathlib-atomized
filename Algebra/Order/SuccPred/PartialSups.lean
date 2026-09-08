/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Oliver Butterley, Lua Viana Reis
-/
module

public import Mathlib.Algebra.Order.SuccPred
public import Mathlib.Order.PartialSups
public import Mathlib.Order.SuccPred.LinearLocallyFinite

/-!
# `PartialSups` in a `SuccAddOrder`

Basic results concerning `PartialSups` which follow with minimal assumptions beyond the fact that
the `PartialSup` is defined over a `SuccAddOrder`.
-/

public section

open Finset

variable {α ι : Type*} [SemilatticeSup α] [LinearOrder ι]

@[simp]
/-
**partialSups_add_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：partialSups_add_one [Add ι] [One ι] [LocallyFiniteOrderBot ι] [SuccAddOrde
r ι] (f : ι -> α) (i : ι) : partialSups f (i + 1) = partialSups f i ⊔ f (i + 1)
参数：f : ι -> α；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `partialSups_succ`：partialSups_succ [LinearOrder ι] [LocallyFiniteOrderBo
t ι] [SuccOrder ι] (f : ι -> α) (i : ι) : partialSups f (Order.succ i) = partial
Sups f…
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
-/
lemma partialSups_add_one [Add ι] [One ι] [LocallyFiniteOrderBot ι] [SuccAddOrder ι]
    (f : ι → α) (i : ι) : partialSups f (i + 1) = partialSups f i ⊔ f (i + 1) :=
  Order.succ_eq_add_one i ▸ partialSups_succ f i

/-- See `partialSups_succ` for another decomposition of `(partialSups f) (Order.succ i)`. -/
/-
**partialSups_succ'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：partialSups_succ' {α : Type*} [SemilatticeSup α] [LocallyFiniteOrder ι] [S
uccOrder ι] [OrderBot ι] (f : ι -> α) (i : ι) : (partialSups f) (Order.succ i) =
 f ⊥ ⊔ (partialSups (f ∘ Order.succ)) i
参数：f : ι -> α；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Succ.rec`：Succ.rec {m : α} {P : forall n, m <= n -> Prop} (rfl : P m le_
rfl) (succ : forall n (hmn : m <= n), P n hmn -> P (succ n) (hmn.trans <| le_s…
· 使用定理 `LinearLocallyFiniteOrder.instIsSuccArchimedeanOfLocallyFiniteOrder`：∀ {ι
 : Type u_1} [inst : LinearOrder ι] [LocallyFiniteOrder ι] [inst_2 : SuccOrder ι
], IsSuccArchimedean ι
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `partialSups_succ`：partialSups_succ [LinearOrder ι] [LocallyFiniteOrderBo
t ι] [SuccOrder ι] (f : ι -> α) (i : ι) : partialSups f (Order.succ i) = partial
Sups f…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `partialSups_bot`：partialSups_bot [PartialOrder ι] [LocallyFiniteOrder ι]
 [OrderBot ι] (f : ι -> α) : partialSups f ⊥ = f ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `sup_assoc`：sup_assoc (a b c : α) : a ⊔ b ⊔ c = a ⊔ (b ⊔ c)
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a

--- 原说明 ---
See `partialSups_succ` for another decomposition of `(partialSups f) (Order.succ
 i)`.
-/
lemma partialSups_succ' {α : Type*} [SemilatticeSup α] [LocallyFiniteOrder ι]
    [SuccOrder ι] [OrderBot ι] (f : ι → α) (i : ι) :
    (partialSups f) (Order.succ i) = f ⊥ ⊔ (partialSups (f ∘ Order.succ)) i := by
  refine Succ.rec (by simp) (fun j _ h ↦ ?_) (bot_le (a := i))
  have : (partialSups (f ∘ Order.succ)) (Order.succ j) =
      ((partialSups (f ∘ Order.succ)) j ⊔ (f ∘ Order.succ) (Order.succ j)) := by simp
  simp [this, h, sup_assoc]

/-- See `partialSups_add_one` for another decomposition of `partialSups f (i + 1)`. -/
/-
**partialSups_add_one'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：partialSups_add_one' [Add ι] [One ι] [OrderBot ι] [LocallyFiniteOrder ι] [
SuccAddOrder ι] (f : ι -> α) (i : ι) : partialSups f (i + 1) = f ⊥ ⊔ partialSups
 (f ∘ (fun k => k + 1)) i
参数：f : ι -> α；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `partialSups_succ`：partialSups_succ [LinearOrder ι] [LocallyFiniteOrderBo
t ι] [SuccOrder ι] (f : ι -> α) (i : ι) : partialSups f (Order.succ i) = partial
Sups f…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `partialSups_succ'`：partialSups_succ' {α : Type*} [SemilatticeSup α] [Loc
allyFiniteOrder ι] [SuccOrder ι] [OrderBot ι] (f : ι -> α) (i : ι) : (partialSup
s f) (O…

--- 原说明 ---
See `partialSups_add_one` for another decomposition of `partialSups f (i + 1)`.
-/
lemma partialSups_add_one' [Add ι] [One ι] [OrderBot ι] [LocallyFiniteOrder ι]
    [SuccAddOrder ι] (f : ι → α) (i : ι) :
    partialSups f (i + 1) = f ⊥ ⊔ partialSups (f ∘ (fun k ↦ k + 1)) i := by
  simpa [← Order.succ_eq_add_one] using partialSups_succ' f i
