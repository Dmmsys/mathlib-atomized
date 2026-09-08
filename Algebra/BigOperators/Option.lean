/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Data.Finset.Option
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Lemmas about products and sums over finite sets in `Option α`

In this file we prove formulas for products and sums over `Finset.insertNone s` and
`Finset.eraseNone s`.
-/

public section

open Function

namespace Finset

variable {α M : Type*} [CommMonoid M]

@[to_additive (attr := simp)]
/-
**Finset.prod_insertNone** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_insertNone (f : Option α -> M) (s : Finset α) : ∏ x in insertNone s, 
f x = f none * ∏ x in s, f (some x)
参数：f : Option α -> M；s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_cons`：prod_cons (h : a ∉ s) : ∏ x in cons a s h, f x = f a *
 ∏ x in s, f x
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Function.Embedding.some_apply`：∀ {α : Type u_1}, ⇑Function.Embedding.som
e = some
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_insertNone (f : Option α → M) (s : Finset α) :
    ∏ x ∈ insertNone s, f x = f none * ∏ x ∈ s, f (some x) := by simp [insertNone]

@[to_additive]
/-
**Finset.mul_prod_eq_prod_insertNone** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mul_prod_eq_prod_insertNone (f : α -> M) (x : M) (s : Finset α) : x * ∏ i 
in s, f i = ∏ i in insertNone s, i.elim x f
参数：f : α -> M；x : M；s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_insertNone`：prod_insertNone (f : Option α -> M) (s : Finset 
α) : ∏ x in insertNone s, f x = f none * ∏ x in s, f (some x)
-/
theorem mul_prod_eq_prod_insertNone (f : α → M) (x : M) (s : Finset α) :
    x * ∏ i ∈ s, f i = ∏ i ∈ insertNone s, i.elim x f :=
  (prod_insertNone (fun i => i.elim x f) _).symm

@[to_additive]
/-
**Finset.prod_eraseNone** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_eraseNone (f : α -> M) (s : Finset (Option α)) : ∏ x in eraseNone s, 
f x = ∏ x in s, Option.elim' 1 f x
参数：f : α -> M；s : Finset (Option α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Option.elim'`：elim'_update {α : Type*} {β : Type*} [DecidableEq α] (f : 
β) (g : α -> β) (a : α) (x : β) : Option.elim' f (update g a x) = update (Option
.e…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.map_some_eraseNone`：map_some_eraseNone [DecidableEq (Option α)] (
s : Finset (Option α)) : (eraseNone s).map Embedding.some = s.erase none
· 使用定理 `Finset.prod_erase`：prod_erase [DecidableEq ι] (s : Finset ι) {f : ι -> M
} {a : ι} (h : f a = 1) : ∏ x in s.erase a, f x = ∏ x in s, f x
-/
theorem prod_eraseNone (f : α → M) (s : Finset (Option α)) :
    ∏ x ∈ eraseNone s, f x = ∏ x ∈ s, Option.elim' 1 f x := by
  classical calc
      ∏ x ∈ eraseNone s, f x = ∏ x ∈ (eraseNone s).map Embedding.some, Option.elim' 1 f x :=
        (prod_map (eraseNone s) Embedding.some <| Option.elim' 1 f).symm
      _ = ∏ x ∈ s.erase none, Option.elim' 1 f x := by rw [map_some_eraseNone]
      _ = ∏ x ∈ s, Option.elim' 1 f x := prod_erase _ rfl

end Finset

