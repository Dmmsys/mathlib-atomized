/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Data.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Product and sums indexed by finite sets in sigma types.

-/

public section

variable {ι κ α β γ : Type*}

open Fin Function

variable {s s₁ s₂ : Finset α} {a : α} {f g : α → β}

namespace Finset

section CommMonoid

variable [CommMonoid β]

/-- The product over a sigma type equals the product of the fiberwise products.
For rewriting in the reverse direction, use `Finset.prod_sigma'`.

See also `Fintype.prod_sigma` for the product over the whole type. -/
@[to_additive /-- The sum over a sigma type equals the sum of the fiberwise sums. For rewriting
in the reverse direction, use `Finset.sum_sigma'`.

See also `Fintype.sum_sigma` for the sum over the whole type. -/]
/-
**Finset.prod_sigma** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_sigma {σ : α -> Type*} (s : Finset α) (t : forall a, Finset (σ a)) (f
 : Sigma σ -> β) : ∏ x in s.sigma t, f x = ∏ a in s, ∏ s in t a, f ⟨a, s⟩
参数：s : Finset α；t : forall a, Finset (σ a)；f : Sigma σ -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.pairwiseDisjoint_map_sigmaMk`：pairwiseDisjoint_map_sigmaMk : (s :
 Set ι).PairwiseDisjoint fun i => (t i).map (Embedding.sigmaMk i)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_disjiUnion`：prod_disjiUnion (s : Finset κ) (t : κ -> Finset 
ι) (h) : ∏ x in s.disjiUnion t h, f x = ∏ i in s, ∏ x in t i, f x
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Function.Embedding.sigmaMk_apply`：∀ {α : Type u_1} {β : α → Type u_3} (a
 : α) (snd : β a), (Function.Embedding.sigmaMk a) snd = ⟨a, snd⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_sigma {σ : α → Type*} (s : Finset α) (t : ∀ a, Finset (σ a)) (f : Sigma σ → β) :
    ∏ x ∈ s.sigma t, f x = ∏ a ∈ s, ∏ s ∈ t a, f ⟨a, s⟩ := by
  simp_rw [← disjiUnion_map_sigma_mk, prod_disjiUnion, prod_map, Function.Embedding.sigmaMk_apply]

/-- The product over a sigma type equals the product of the fiberwise products. For rewriting
in the reverse direction, use `Finset.prod_sigma`. -/
@[to_additive /-- The sum over a sigma type equals the sum of the fiberwise sums. For rewriting
in the reverse direction, use `Finset.sum_sigma` -/]
/-
**Finset.prod_sigma'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_sigma' {σ : α -> Type*} (s : Finset α) (t : forall a, Finset (σ a)) (
f : forall a, σ a -> β) : (∏ a in s, ∏ s in t a, f a s) = ∏ x in s.sigma t, f x.
1 x.2
参数：s : Finset α；t : forall a, Finset (σ a)；f : forall a, σ a -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_sigma`：prod_sigma {σ : α -> Type*} (s : Finset α) (t : foral
l a, Finset (σ a)) (f : Sigma σ -> β) : ∏ x in s.sigma t, f x = ∏ a in s, ∏ s in
 t a, f…
-/
theorem prod_sigma' {σ : α → Type*} (s : Finset α) (t : ∀ a, Finset (σ a)) (f : ∀ a, σ a → β) :
    (∏ a ∈ s, ∏ s ∈ t a, f a s) = ∏ x ∈ s.sigma t, f x.1 x.2 :=
  Eq.symm <| prod_sigma s t fun x => f x.1 x.2

@[to_additive]
/-
**Finset.prod_finset_product** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_finset_product (r : Finset (γ × α)) (s : Finset γ) (t : γ -> Finset α
) (h : forall p : γ × α, p in r ↔ p.1 in s ∧ p.2 in t p.1) {f : γ × α -> β} : ∏ 
p in r, f p = ∏ c in s, ∏ a in t c, f (c, a)
参数：r : Finset (γ × α)；s : Finset γ；t : γ -> Finset α；h : forall p : γ × α, p in 
r ↔ p.1 in s ∧ p.2 in t p.1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Finset.prod_equiv`：prod_equiv (e : ι ≃ κ) (hst : forall i, i in s ↔ e i 
in t) (hfg : forall i in s, f i = g (e i)) : ∏ i in s, f i = ∏ i in t, g i
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.sigmaEquivProd_symm_apply`：∀ (α : Type u_1) (β : Type u_2) (a : α 
× β), (Equiv.sigmaEquivProd α β).symm a = ⟨a.1, a.2⟩
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Prod.mk.eta`：∀ {α : Type u_1} {β : Type u_2} {p : α × β}, (p.1, p.2) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.prod_sigma`：prod_sigma {σ : α -> Type*} (s : Finset α) (t : foral
l a, Finset (σ a)) (f : Sigma σ -> β) : ∏ x in s.sigma t, f x = ∏ a in s, ∏ s in
 t a, f…
-/
theorem prod_finset_product (r : Finset (γ × α)) (s : Finset γ) (t : γ → Finset α)
    (h : ∀ p : γ × α, p ∈ r ↔ p.1 ∈ s ∧ p.2 ∈ t p.1) {f : γ × α → β} :
    ∏ p ∈ r, f p = ∏ c ∈ s, ∏ a ∈ t c, f (c, a) := by
  refine Eq.trans ?_ (prod_sigma s t fun p => f (p.1, p.2))
  apply prod_equiv (Equiv.sigmaEquivProd _ _).symm <;> simp [h]

@[to_additive]
/-
**Finset.prod_finset_product'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_finset_product' (r : Finset (γ × α)) (s : Finset γ) (t : γ -> Finset 
α) (h : forall p : γ × α, p in r ↔ p.1 in s ∧ p.2 in t p.1) {f : γ -> α -> β} : 
∏ p in r, f p.1 p.2 = ∏ c in s, ∏ a in t c, f c a
参数：r : Finset (γ × α)；s : Finset γ；t : γ -> Finset α；h : forall p : γ × α, p in 
r ↔ p.1 in s ∧ p.2 in t p.1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_finset_product`：prod_finset_product (r : Finset (γ × α)) (s 
: Finset γ) (t : γ -> Finset α) (h : forall p : γ × α, p in r ↔ p.1 in s ∧ p.2 i
n t p.1) {f : γ …
-/
theorem prod_finset_product' (r : Finset (γ × α)) (s : Finset γ) (t : γ → Finset α)
    (h : ∀ p : γ × α, p ∈ r ↔ p.1 ∈ s ∧ p.2 ∈ t p.1) {f : γ → α → β} :
    ∏ p ∈ r, f p.1 p.2 = ∏ c ∈ s, ∏ a ∈ t c, f c a :=
  prod_finset_product r s t h

@[to_additive]
/-
**Finset.prod_finset_product_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_finset_product_right (r : Finset (α × γ)) (s : Finset γ) (t : γ -> Fi
nset α) (h : forall p : α × γ, p in r ↔ p.2 in s ∧ p.1 in t p.2) {f : α × γ -> β
} : ∏ p in r, f p = ∏ c in s, ∏ a in t c, f (a, c)
参数：r : Finset (α × γ)；s : Finset γ；t : γ -> Finset α；h : forall p : α × γ, p in 
r ↔ p.2 in s ∧ p.1 in t p.2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Finset.prod_equiv`：prod_equiv (e : ι ≃ κ) (hst : forall i, i in s ↔ e i 
in t) (hfg : forall i in s, f i = g (e i)) : ∏ i in s, f i = ∏ i in t, g i
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.sigmaEquivProd_symm_apply`：∀ (α : Type u_1) (β : Type u_2) (a : α 
× β), (Equiv.sigmaEquivProd α β).symm a = ⟨a.1, a.2⟩
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Prod.mk.eta`：∀ {α : Type u_1} {β : Type u_2} {p : α × β}, (p.1, p.2) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.prod_sigma`：prod_sigma {σ : α -> Type*} (s : Finset α) (t : foral
l a, Finset (σ a)) (f : Sigma σ -> β) : ∏ x in s.sigma t, f x = ∏ a in s, ∏ s in
 t a, f…
-/
theorem prod_finset_product_right (r : Finset (α × γ)) (s : Finset γ) (t : γ → Finset α)
    (h : ∀ p : α × γ, p ∈ r ↔ p.2 ∈ s ∧ p.1 ∈ t p.2) {f : α × γ → β} :
    ∏ p ∈ r, f p = ∏ c ∈ s, ∏ a ∈ t c, f (a, c) := by
  refine Eq.trans ?_ (prod_sigma s t fun p => f (p.2, p.1))
  apply prod_equiv ((Equiv.prodComm _ _).trans (Equiv.sigmaEquivProd _ _).symm) <;> simp [h]

@[to_additive]
/-
**Finset.prod_finset_product_right'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_finset_product_right' (r : Finset (α × γ)) (s : Finset γ) (t : γ -> F
inset α) (h : forall p : α × γ, p in r ↔ p.2 in s ∧ p.1 in t p.2) {f : α -> γ ->
 β} : ∏ p in r, f p.1 p.2 = ∏ c in s, ∏ a in t c, f a c
参数：r : Finset (α × γ)；s : Finset γ；t : γ -> Finset α；h : forall p : α × γ, p in 
r ↔ p.2 in s ∧ p.1 in t p.2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_finset_product_right`：prod_finset_product_right (r : Finset 
(α × γ)) (s : Finset γ) (t : γ -> Finset α) (h : forall p : α × γ, p in r ↔ p.2 
in s ∧ p.1 in t p.2) {…
-/
theorem prod_finset_product_right' (r : Finset (α × γ)) (s : Finset γ) (t : γ → Finset α)
    (h : ∀ p : α × γ, p ∈ r ↔ p.2 ∈ s ∧ p.1 ∈ t p.2) {f : α → γ → β} :
    ∏ p ∈ r, f p.1 p.2 = ∏ c ∈ s, ∏ a ∈ t c, f a c :=
  prod_finset_product_right r s t h

/-- The product over a product set equals the product of the fiberwise products. For rewriting
in the reverse direction, use `Finset.prod_product'`. -/
@[to_additive /-- The sum over a product set equals the sum of the fiberwise sums. For rewriting
in the reverse direction, use `Finset.sum_product'` -/]
/-
**Finset.prod_product** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_product (s : Finset γ) (t : Finset α) (f : γ × α -> β) : ∏ x in s ×ˢ 
t, f x = ∏ x in s, ∏ y in t, f (x, y)
参数：s : Finset γ；t : Finset α；f : γ × α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_finset_product`：prod_finset_product (r : Finset (γ × α)) (s 
: Finset γ) (t : γ -> Finset α) (h : forall p : γ × α, p in r ↔ p.1 in s ∧ p.2 i
n t p.1) {f : γ …
· 使用定理 `Finset.mem_product`：mem_product {p : α × β} : p in s ×ˢ t ↔ p.1 in s ∧ p
.2 in t
-/
theorem prod_product (s : Finset γ) (t : Finset α) (f : γ × α → β) :
    ∏ x ∈ s ×ˢ t, f x = ∏ x ∈ s, ∏ y ∈ t, f (x, y) :=
  prod_finset_product (s ×ˢ t) s (fun _a => t) fun _p => mem_product

/-- The product over a product set equals the product of the fiberwise products. For rewriting
in the reverse direction, use `Finset.prod_product`. -/
@[to_additive /-- The sum over a product set equals the sum of the fiberwise sums. For rewriting
in the reverse direction, use `Finset.sum_product` -/]
/-
**Finset.prod_product'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_product' (s : Finset γ) (t : Finset α) (f : γ -> α -> β) : ∏ x in s ×
ˢ t, f x.1 x.2 = ∏ x in s, ∏ y in t, f x y
参数：s : Finset γ；t : Finset α；f : γ -> α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_product`：prod_product (s : Finset γ) (t : Finset α) (f : γ ×
 α -> β) : ∏ x in s ×ˢ t, f x = ∏ x in s, ∏ y in t, f (x, y)
-/
theorem prod_product' (s : Finset γ) (t : Finset α) (f : γ → α → β) :
    ∏ x ∈ s ×ˢ t, f x.1 x.2 = ∏ x ∈ s, ∏ y ∈ t, f x y :=
  prod_product ..

@[to_additive]
/-
**Finset.prod_product_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_product_right (s : Finset γ) (t : Finset α) (f : γ × α -> β) : ∏ x in
 s ×ˢ t, f x = ∏ y in t, ∏ x in s, f (x, y)
参数：s : Finset γ；t : Finset α；f : γ × α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_finset_product_right`：prod_finset_product_right (r : Finset 
(α × γ)) (s : Finset γ) (t : γ -> Finset α) (h : forall p : α × γ, p in r ↔ p.2 
in s ∧ p.1 in t p.2) {…
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Finset.mem_product`：mem_product {p : α × β} : p in s ×ˢ t ↔ p.1 in s ∧ p
.2 in t
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
-/
theorem prod_product_right (s : Finset γ) (t : Finset α) (f : γ × α → β) :
    ∏ x ∈ s ×ˢ t, f x = ∏ y ∈ t, ∏ x ∈ s, f (x, y) :=
  prod_finset_product_right (s ×ˢ t) t (fun _a => s) fun _p => mem_product.trans and_comm

/-- An uncurried version of `Finset.prod_product_right`. -/
@[to_additive /-- An uncurried version of `Finset.sum_product_right` -/]
/-
**Finset.prod_product_right'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_product_right' (s : Finset γ) (t : Finset α) (f : γ -> α -> β) : ∏ x 
in s ×ˢ t, f x.1 x.2 = ∏ y in t, ∏ x in s, f x y
参数：s : Finset γ；t : Finset α；f : γ -> α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_product_right`：prod_product_right (s : Finset γ) (t : Finset
 α) (f : γ × α -> β) : ∏ x in s ×ˢ t, f x = ∏ y in t, ∏ x in s, f (x, y)

--- 原说明 ---
An uncurried version of `Finset.prod_product_right`.
-/
theorem prod_product_right' (s : Finset γ) (t : Finset α) (f : γ → α → β) :
    ∏ x ∈ s ×ˢ t, f x.1 x.2 = ∏ y ∈ t, ∏ x ∈ s, f x y :=
  prod_product_right ..

/-- Generalization of `Finset.prod_comm` to the case when the inner `Finset`s depend on the outer
variable. -/
@[to_additive /-- Generalization of `Finset.sum_comm` to the case when the inner `Finset`s depend on
the outer variable. -/]
/-
**Finset.prod_comm'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_comm' {s : Finset γ} {t : γ -> Finset α} {t' : Finset α} {s' : α -> F
inset γ} (h : forall x y, x in s ∧ y in t x ↔ x in s' y ∧ y in t') {f : γ -> α -
> β} : (∏ x in s, ∏ y in t x, f x y) = ∏ y in t', ∏ x in s' y, f x y
参数：h : forall x y, x in s ∧ y in t x ↔ x in s' y ∧ y in t'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.Embedding.sectR_apply`：∀ {α : Type u_1} (a : α) (β : Type u_2) 
(b : β), (Function.Embedding.sectR a β) b = (a, b)
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_finset_product'`：prod_finset_product' (r : Finset (γ × α)) (
s : Finset γ) (t : γ -> Finset α) (h : forall p : γ × α, p in r ↔ p.1 in s ∧ p.2
 in t p.1) {f : γ…
· 使用定理 `Finset.prod_finset_product_right'`：prod_finset_product_right' (r : Finse
t (α × γ)) (s : Finset γ) (t : γ -> Finset α) (h : forall p : α × γ, p in r ↔ p.
2 in s ∧ p.1 in t p.2) …
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
-/
theorem prod_comm' {s : Finset γ} {t : γ → Finset α} {t' : Finset α} {s' : α → Finset γ}
    (h : ∀ x y, x ∈ s ∧ y ∈ t x ↔ x ∈ s' y ∧ y ∈ t') {f : γ → α → β} :
    (∏ x ∈ s, ∏ y ∈ t x, f x y) = ∏ y ∈ t', ∏ x ∈ s' y, f x y := by
  classical
    have : ∀ z : γ × α, (z ∈ s.biUnion fun x => (t x).map <| Function.Embedding.sectR x _) ↔
      z.1 ∈ s ∧ z.2 ∈ t z.1 := by
      rintro ⟨x, y⟩
      simp only [mem_biUnion, mem_map, Function.Embedding.sectR_apply, Prod.mk.injEq,
        exists_eq_right, ← and_assoc]
    exact
      (prod_finset_product' _ _ _ this).symm.trans
        ((prod_finset_product_right' _ _ _) fun ⟨x, y⟩ => (this _).trans ((h x y).trans and_comm))

@[to_additive]
/-
**Finset.prod_comm** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_comm {s : Finset γ} {t : Finset α} {f : γ -> α -> β} : (∏ x in s, ∏ y
 in t, f x y) = ∏ y in t, ∏ x in s, f x y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_comm'`：prod_comm' {s : Finset γ} {t : γ -> Finset α} {t' : F
inset α} {s' : α -> Finset γ} (h : forall x y, x in s ∧ y in t x ↔ x in s' y ∧ y
 in t')…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem prod_comm {s : Finset γ} {t : Finset α} {f : γ → α → β} :
    (∏ x ∈ s, ∏ y ∈ t, f x y) = ∏ y ∈ t, ∏ x ∈ s, f x y :=
  prod_comm' fun _ _ => Iff.rfl

/-- Cyclically permute 3 nested instances of `Finset.prod`. -/
@[to_additive]
/-
**Finset.prod_comm_cycle** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_comm_cycle {s : Finset γ} {t : Finset α} {u : Finset κ} {f : γ -> α -
> κ -> β} : (∏ x in s, ∏ y in t, ∏ z in u, f x y z) = ∏ z in u, ∏ x in s, ∏ y in
 t, f x y z
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_comm`：prod_comm {s : Finset γ} {t : Finset α} {f : γ -> α ->
 β} : (∏ x in s, ∏ y in t, f x y) = ∏ y in t, ∏ x in s, f x y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Cyclically permute 3 nested instances of `Finset.prod`.
-/
theorem prod_comm_cycle {s : Finset γ} {t : Finset α} {u : Finset κ} {f : γ → α → κ → β} :
    (∏ x ∈ s, ∏ y ∈ t, ∏ z ∈ u, f x y z) = ∏ z ∈ u, ∏ x ∈ s, ∏ y ∈ t, f x y z := by
  simp_rw [prod_comm (s := t), prod_comm (s := s)]

end CommMonoid

@[simp]
/-
**Finset.card_sigma** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_sigma {σ : α -> Type*} (s : Finset α) (t : forall a, Finset (σ a)) : 
#(s.sigma t) = ∑ a in s, #(t a)
参数：s : Finset α；t : forall a, Finset (σ a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.card_sigma`：card_sigma : card (s.sigma t) = sum (map (fun a => 
card (t a)) s)
-/
theorem card_sigma {σ : α → Type*} (s : Finset α) (t : ∀ a, Finset (σ a)) :
    #(s.sigma t) = ∑ a ∈ s, #(t a) :=
  Multiset.card_sigma _ _

end Finset

