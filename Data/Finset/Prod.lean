/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Oliver Nash
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.List.OffDiag
public import Mathlib.Data.Nat.Choose.Basic

/-!
# Finsets in product types

This file defines finset constructions on the product type `α × β`. Beware not to confuse with the
`Finset.prod` operation which computes the multiplicative product.

## Main declarations

* `Finset.product`: Turns `s : Finset α`, `t : Finset β` into their product in `Finset (α × β)`.
* `Finset.diag`: For `s : Finset α`, `s.diag` is the `Finset (α × α)` of pairs `(a, a)` with
  `a ∈ s`.
* `Finset.offDiag`: For `s : Finset α`, `s.offDiag` is the `Finset (α × α)` of pairs `(a, b)` with
  `a, b ∈ s` and `a ≠ b`.
-/

@[expose] public section

assert_not_exists MonoidWithZero

open Multiset

variable {α β γ : Type*}

namespace Finset

/-! ### prod -/


section Prod

variable {s s' : Finset α} {t t' : Finset β} {a : α} {b : β}

/-- `product s t` is the set of pairs `(a, b)` such that `a ∈ s` and `b ∈ t`. -/
/-
**Finset.product** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → Finset α → Finset β → Finset (α × β)
参数：α × β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`product s t` is the set of pairs `(a, b)` such that `a ∈ s` and `b ∈ t`.
-/
protected def product (s : Finset α) (t : Finset β) : Finset (α × β) :=
  ⟨_, s.nodup.product t.nodup⟩
/-
**Finset.instSProd** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
形式化陈述：instSProd : SProd (Finset α) (Finset β) (Finset (α × β)) where sprod
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSProd : SProd (Finset α) (Finset β) (Finset (α × β)) where
  sprod := Finset.product

@[simp]
/-
**Finset.product_eq_sprod** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：product_eq_sprod : Finset.product s t = s ×ˢ t
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem product_eq_sprod : Finset.product s t = s ×ˢ t :=
  rfl

@[simp]
/-
**Finset.product_val** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：product_val : (s ×ˢ t).1 = s.1 ×ˢ t.1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem product_val : (s ×ˢ t).1 = s.1 ×ˢ t.1 :=
  rfl

@[simp, grind =]
/-
**Finset.mem_product** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_product {p : α × β} : p in s ×ˢ t ↔ p.1 in s ∧ p.2 in t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.mem_product`：∀ {α : Type u_1} {β : Type v} {s : Multiset α} {t 
: Multiset β} {p : α × β}, p ∈ s ×ˢ t ↔ p.1 ∈ s ∧ p.2 ∈ t
-/
theorem mem_product {p : α × β} : p ∈ s ×ˢ t ↔ p.1 ∈ s ∧ p.2 ∈ t :=
  Multiset.mem_product
/-
**Finset.mk_mem_product** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mk_mem_product (ha : a in s) (hb : b in t) : (a, b) in s ×ˢ t
参数：ha : a in s；hb : b in t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_product`：mem_product {p : α × β} : p in s ×ˢ t ↔ p.1 in s ∧ p
.2 in t
-/
theorem mk_mem_product (ha : a ∈ s) (hb : b ∈ t) : (a, b) ∈ s ×ˢ t :=
  mem_product.2 ⟨ha, hb⟩

@[simp, norm_cast]
/-
**Finset.coe_product** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_product (s : Finset α) (t : Finset β) : (↑(s ×ˢ t) : Set (α × β)) = (s
 : Set α) ×ˢ t
参数：s : Finset α；t : Finset β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Finset.mem_product`：mem_product {p : α × β} : p in s ×ˢ t ↔ p.1 in s ∧ p
.2 in t
-/
theorem coe_product (s : Finset α) (t : Finset β) :
    (↑(s ×ˢ t) : Set (α × β)) = (s : Set α) ×ˢ t :=
  Set.ext fun _ => Finset.mem_product

/-- The product `s ×ˢ t` of two finsets, viewed as a subtype, is equivalent to the product of the
subtypes `s × t`. The `Finset` analogue of `Equiv.Set.prod`. -/
/-
**Finset._root_.Equiv.Finset.prod** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product `s ×ˢ t` of two finsets, viewed as a subtype, is equivalent to the p
roduct of the
subtypes `s × t`. The `Finset` analogue of `Equiv.Set.prod`.
-/
def _root_.Equiv.Finset.prod (s : Finset α) (t : Finset β) : ↥(s ×ˢ t) ≃ s × t where
  toFun x := ⟨⟨x.1.1, (mem_product.mp x.2).1⟩, ⟨x.1.2, (mem_product.mp x.2).2⟩⟩
  invFun x := ⟨⟨x.1.1, x.2.1⟩, mem_product.mpr ⟨x.1.2, x.2.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
/-
**Finset.subset_product_image_fst** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：subset_product_image_fst [DecidableEq α] : (s ×ˢ t).image Prod.fst subsete
q s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem subset_product_image_fst [DecidableEq α] : (s ×ˢ t).image Prod.fst ⊆ s := fun i => by
  simp +contextual [mem_image]
/-
**Finset.subset_product_image_snd** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：subset_product_image_snd [DecidableEq β] : (s ×ˢ t).image Prod.snd subsete
q t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem subset_product_image_snd [DecidableEq β] : (s ×ˢ t).image Prod.snd ⊆ t := fun i => by
  simp +contextual [mem_image]
/-
**Finset.product_image_fst** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：product_image_fst [DecidableEq α] (ht : t.Nonempty) : (s ×ˢ t).image Prod.
fst = s
参数：ht : t.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Finset.Nonempty.exists_mem`：∀ {α : Type u_1} {s : Finset α}, s.Nonempty 
→ ∃ x, x ∈ s
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem product_image_fst [DecidableEq α] (ht : t.Nonempty) : (s ×ˢ t).image Prod.fst = s := by
  ext i
  simp [mem_image, ht.exists_mem]
/-
**Finset.product_image_snd** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：product_image_snd [DecidableEq β] (ht : s.Nonempty) : (s ×ˢ t).image Prod.
snd = t
参数：ht : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Finset.Nonempty.exists_mem`：∀ {α : Type u_1} {s : Finset α}, s.Nonempty 
→ ∃ x, x ∈ s
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem product_image_snd [DecidableEq β] (ht : s.Nonempty) : (s ×ˢ t).image Prod.snd = t := by
  ext i
  simp [mem_image, ht.exists_mem]
/-
**Finset.subset_product** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：subset_product [DecidableEq α] [DecidableEq β] {s : Finset (α × β)} : s su
bseteq s.image Prod.fst ×ˢ s.image Prod.snd
参数：α × β。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subset_product [DecidableEq α] [DecidableEq β] {s : Finset (α × β)} :
    s ⊆ s.image Prod.fst ×ˢ s.image Prod.snd := by grind

@[gcongr]
/-
**Finset.product_subset_product** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：product_subset_product (hs : s subseteq s') (ht : t subseteq t') : s ×ˢ t 
subseteq s' ×ˢ t'
参数：hs : s subseteq s'；ht : t subseteq t'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_product`：mem_product {p : α × β} : p in s ×ˢ t ↔ p.1 in s ∧ p
.2 in t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem product_subset_product (hs : s ⊆ s') (ht : t ⊆ t') : s ×ˢ t ⊆ s' ×ˢ t' := fun ⟨_, _⟩ h =>
  mem_product.2 ⟨hs (mem_product.1 h).1, ht (mem_product.1 h).2⟩
/-
**Finset.product_subset_product_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：product_subset_product_left (hs : s subseteq s') : s ×ˢ t subseteq s' ×ˢ t
参数：hs : s subseteq s'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.product_subset_product`：product_subset_product (hs : s subseteq s
') (ht : t subseteq t') : s ×ˢ t subseteq s' ×ˢ t'
· 使用定理 `Finset.Subset.refl`：∀ {α : Type u_1} (s : Finset α), s ⊆ s
-/
theorem product_subset_product_left (hs : s ⊆ s') : s ×ˢ t ⊆ s' ×ˢ t :=
  product_subset_product hs (Subset.refl _)
/-
**Finset.product_subset_product_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：product_subset_product_right (ht : t subseteq t') : s ×ˢ t subseteq s ×ˢ t
'
参数：ht : t subseteq t'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.product_subset_product`：product_subset_product (hs : s subseteq s
') (ht : t subseteq t') : s ×ˢ t subseteq s' ×ˢ t'
· 使用定理 `Finset.Subset.refl`：∀ {α : Type u_1} (s : Finset α), s ⊆ s
-/
theorem product_subset_product_right (ht : t ⊆ t') : s ×ˢ t ⊆ s ×ˢ t' :=
  product_subset_product (Subset.refl _) ht
/-
**Finset.prodMap_image_product** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prodMap_image_product {δ : Type*} [DecidableEq β] [DecidableEq δ] (f : α -
> β) (g : γ -> δ) (s : Finset α) (t : Finset γ) : (s ×ˢ t).image (Prod.map f g) 
= s.image f ×ˢ t.image g
参数：f : α -> β；g : γ -> δ；s : Finset α；t : Finset γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.prodMap_image_prod`：prodMap_image_prod (f : α -> β) (g : γ -> δ) (s 
: Set α) (t : Set γ) : (Prod.map f g) '' (s ×ˢ t) = (f '' s) ×ˢ (g '' t)
-/
theorem prodMap_image_product {δ : Type*} [DecidableEq β] [DecidableEq δ]
    (f : α → β) (g : γ → δ) (s : Finset α) (t : Finset γ) :
    (s ×ˢ t).image (Prod.map f g) = s.image f ×ˢ t.image g :=
  mod_cast Set.prodMap_image_prod f g s t
/-
**Finset.prodMap_map_product** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prodMap_map_product {δ : Type*} (f : α ↪ β) (g : γ ↪ δ) (s : Finset α) (t 
: Finset γ) : (s ×ˢ t).map (f.prodMap g) = s.map f ×ˢ t.map g
参数：f : α ↪ β；g : γ ↪ δ；s : Finset α；t : Finset γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Finset.coe_product`：coe_product (s : Finset α) (t : Finset β) : (↑(s ×ˢ 
t) : Set (α × β)) = (s : Set α) ×ˢ t
· 使用定理 `Set.prodMap_image_prod`：prodMap_image_prod (f : α -> β) (g : γ -> δ) (s 
: Set α) (t : Set γ) : (Prod.map f g) '' (s ×ˢ t) = (f '' s) ×ˢ (g '' t)
-/
theorem prodMap_map_product {δ : Type*} (f : α ↪ β) (g : γ ↪ δ) (s : Finset α) (t : Finset γ) :
    (s ×ˢ t).map (f.prodMap g) = s.map f ×ˢ t.map g := by
  simpa [← coe_inj] using Set.prodMap_image_prod f g s t
/-
**Finset.map_swap_product** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：map_swap_product (s : Finset α) (t : Finset β) : (t ×ˢ s).map ⟨Prod.swap, 
Prod.swap_injective⟩ = s ×ˢ t
参数：s : Finset α；t : Finset β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `Prod.swap_injective`：swap_injective : Function.Injective (@swap α β)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Finset.coe_product`：coe_product (s : Finset α) (t : Finset β) : (↑(s ×ˢ 
t) : Set (α × β)) = (s : Set α) ×ˢ t
· 使用定理 `Set.image_swap_prod`：image_swap_prod (s : Set α) (t : Set β) : Prod.swap
 '' s ×ˢ t = t ×ˢ s
-/
theorem map_swap_product (s : Finset α) (t : Finset β) :
    (t ×ˢ s).map ⟨Prod.swap, Prod.swap_injective⟩ = s ×ˢ t :=
  coe_injective <| by
    push_cast
    exact Set.image_swap_prod _ _

@[simp]
/-
**Finset.image_swap_product** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_swap_product [DecidableEq (α × β)] (s : Finset α) (t : Finset β) : (
t ×ˢ s).image Prod.swap = s ×ˢ t
参数：α × β；s : Finset α；t : Finset β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_product`：coe_product (s : Finset α) (t : Finset β) : (↑(s ×ˢ 
t) : Set (α × β)) = (s : Set α) ×ˢ t
· 使用定理 `Set.image_swap_prod`：image_swap_prod (s : Set α) (t : Set β) : Prod.swap
 '' s ×ˢ t = t ×ˢ s
-/
theorem image_swap_product [DecidableEq (α × β)] (s : Finset α) (t : Finset β) :
    (t ×ˢ s).image Prod.swap = s ×ˢ t :=
  coe_injective <| by
    push_cast
    exact Set.image_swap_prod _ _
/-
**Finset.product_eq_biUnion** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：product_eq_biUnion [DecidableEq (α × β)] (s : Finset α) (t : Finset β) : s
 ×ˢ t = s.biUnion fun a => t.image fun b => (a, b)
参数：α × β；s : Finset α；t : Finset β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem product_eq_biUnion [DecidableEq (α × β)] (s : Finset α) (t : Finset β) :
    s ×ˢ t = s.biUnion fun a => t.image fun b => (a, b) := by grind
/-
**Finset.product_eq_biUnion_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：product_eq_biUnion_right [DecidableEq (α × β)] (s : Finset α) (t : Finset 
β) : s ×ˢ t = t.biUnion fun b => s.image fun a => (a, b)
参数：α × β；s : Finset α；t : Finset β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem product_eq_biUnion_right [DecidableEq (α × β)] (s : Finset α) (t : Finset β) :
    s ×ˢ t = t.biUnion fun b => s.image fun a => (a, b) := by grind

/-- See also `Finset.sup_product_left`. -/
@[simp]
/-
**Finset.product_biUnion** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：product_biUnion [DecidableEq γ] (s : Finset α) (t : Finset β) (f : α × β -
> Finset γ) : (s ×ˢ t).biUnion f = s.biUnion fun a => t.biUnion fun b => f (a, b
)
参数：s : Finset α；t : Finset β；f : α × β -> Finset γ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See also `Finset.sup_product_left`.
-/
theorem product_biUnion [DecidableEq γ] (s : Finset α) (t : Finset β) (f : α × β → Finset γ) :
    (s ×ˢ t).biUnion f = s.biUnion fun a => t.biUnion fun b => f (a, b) := by grind

@[simp]
/-
**Finset.card_product** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_product (s : Finset α) (t : Finset β) : card (s ×ˢ t) = card s * card
 t
参数：s : Finset α；t : Finset β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.card_product`：card_product : card (s ×ˢ t) = card s * card t
-/
theorem card_product (s : Finset α) (t : Finset β) : card (s ×ˢ t) = card s * card t :=
  Multiset.card_product _ _

/-- The product of two Finsets is nontrivial iff both are nonempty
  at least one of them is nontrivial. -/
/-
**Finset.nontrivial_prod_iff** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：nontrivial_prod_iff : (s ×ˢ t).Nontrivial ↔ s.Nonempty ∧ t.Nonempty ∧ (s.N
ontrivial ∨ t.Nontrivial)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.card_product`：card_product (s : Finset α) (t : Finset β) : card (
s ×ˢ t) = card s * card t
· 使用定理 `Nat.one_lt_mul_iff`：∀ {m n : ℕ}, 1 < m * n ↔ 0 < m ∧ 0 < n ∧ (1 < m ∨ 1 
< n)

--- 原说明 ---
The product of two Finsets is nontrivial iff both are nonempty
  at least one of them is nontrivial.
-/
lemma nontrivial_prod_iff : (s ×ˢ t).Nontrivial ↔
    s.Nonempty ∧ t.Nonempty ∧ (s.Nontrivial ∨ t.Nontrivial) := by
  simp_rw [← card_pos, ← one_lt_card_iff_nontrivial, card_product]; apply Nat.one_lt_mul_iff
/-
**Finset.filter_product** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：filter_product (p : α -> Prop) (q : β -> Prop) [DecidablePred p] [Decidabl
ePred q] : ((s ×ˢ t).filter fun x : α × β => p x.1 ∧ q x.2) = s.filter p ×ˢ t.fi
lter q
参数：p : α -> Prop；q : β -> Prop。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem filter_product (p : α → Prop) (q : β → Prop) [DecidablePred p] [DecidablePred q] :
    ((s ×ˢ t).filter fun x : α × β => p x.1 ∧ q x.2) = s.filter p ×ˢ t.filter q := by grind
/-
**Finset.filter_product_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：filter_product_left (p : α -> Prop) [DecidablePred p] : ((s ×ˢ t).filter f
un x : α × β => p x.1) = s.filter p ×ˢ t
参数：p : α -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Finset.filter_true`：∀ {α : Type u_1} {h : DecidablePred fun x => True} (
s : Finset α), {x ∈ s | True} = s
· 使用定理 `Finset.filter_product`：filter_product (p : α -> Prop) (q : β -> Prop) [D
ecidablePred p] [DecidablePred q] : ((s ×ˢ t).filter fun x : α × β => p x.1 ∧ q 
x.2) = s.fi…
-/
theorem filter_product_left (p : α → Prop) [DecidablePred p] :
    ((s ×ˢ t).filter fun x : α × β => p x.1) = s.filter p ×ˢ t := by
  simpa using filter_product p fun _ => true
/-
**Finset.filter_product_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：filter_product_right (q : β -> Prop) [DecidablePred q] : ((s ×ˢ t).filter 
fun x : α × β => q x.2) = s ×ˢ t.filter q
参数：q : β -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Finset.filter_true`：∀ {α : Type u_1} {h : DecidablePred fun x => True} (
s : Finset α), {x ∈ s | True} = s
· 使用定理 `Finset.filter_product`：filter_product (p : α -> Prop) (q : β -> Prop) [D
ecidablePred p] [DecidablePred q] : ((s ×ˢ t).filter fun x : α × β => p x.1 ∧ q 
x.2) = s.fi…
-/
theorem filter_product_right (q : β → Prop) [DecidablePred q] :
    ((s ×ˢ t).filter fun x : α × β => q x.2) = s ×ˢ t.filter q := by
  simpa using filter_product (fun _ : α => true) q
/-
**Finset.filter_product_card** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：filter_product_card (s : Finset α) (t : Finset β) (p : α -> Prop) (q : β -
> Prop) [DecidablePred p] [DecidablePred q] : ((s ×ˢ t).filter fun x : α × β => 
(p x.1) = (q x.2)).card = (s.filter p).card * (t.filter q).card + (s.filter (¬ p
 ·)).card * (t.filter (¬ q ·)).card
参数：s : Finset α；t : Finset β；p : α -> Prop；q : β -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_product`：card_product (s : Finset α) (t : Finset β) : card (
s ×ˢ t) = card s * card t
· 使用定理 `Finset.filter_product`：filter_product (p : α -> Prop) (q : β -> Prop) [D
ecidablePred p] [DecidablePred q] : ((s ×ˢ t).filter fun x : α × β => p x.1 ∧ q 
x.2) = s.fi…
· 使用定理 `Finset.card_union_of_disjoint`：∀ {α : Type u_1} {s t : Finset α} [inst :
 DecidableEq α], Disjoint s t → (s ∪ t).card = s.card + t.card
· 使用定理 `Finset.disjoint_filter_filter'`：disjoint_filter_filter' (s t : Finset α)
 {p q : α -> Prop} [DecidablePred p] [DecidablePred q] (h : Disjoint p q) : Disj
oint (s.filter p) (t…
· 使用定理 `Disjoint.inf_right`：Disjoint.inf_right (h : Disjoint a b) : Disjoint a (
b ⊓ c)
· 使用定理 `Disjoint.inf_left`：Disjoint.inf_left (h : Disjoint a b) : Disjoint (a ⊓ 
c) b
· 使用定理 `disjoint_compl_right`：disjoint_compl_right : Disjoint a aᶜ
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem filter_product_card (s : Finset α) (t : Finset β) (p : α → Prop) (q : β → Prop)
    [DecidablePred p] [DecidablePred q] :
    ((s ×ˢ t).filter fun x : α × β => (p x.1) = (q x.2)).card =
      (s.filter p).card * (t.filter q).card +
        (s.filter (¬ p ·)).card * (t.filter (¬ q ·)).card := by
  classical
  rw [← card_product, ← card_product, ← filter_product, ← filter_product, ← card_union_of_disjoint]
  · apply congr_arg
    grind
  · apply Finset.disjoint_filter_filter'
    exact (disjoint_compl_right.inf_left _).inf_right _

@[simp]
/-
**Finset.empty_product** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：empty_product (t : Finset β) : (∅ : Finset α) ×ˢ t = ∅
参数：t : Finset β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem empty_product (t : Finset β) : (∅ : Finset α) ×ˢ t = ∅ :=
  rfl

@[simp]
/-
**Finset.product_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：product_empty (s : Finset α) : s ×ˢ (∅ : Finset β) = ∅
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_empty_of_forall_notMem`：eq_empty_of_forall_notMem {s : Finset 
α} (H : forall x, x ∉ s) : s = ∅
· 使用定理 `Finset.notMem_empty`：notMem_empty (a : α) : a ∉ (∅ : Finset α)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_product`：mem_product {p : α × β} : p in s ×ˢ t ↔ p.1 in s ∧ p
.2 in t
-/
theorem product_empty (s : Finset α) : s ×ˢ (∅ : Finset β) = ∅ :=
  eq_empty_of_forall_notMem fun _ h => notMem_empty _ (Finset.mem_product.1 h).2

@[aesop safe apply (rule_sets := [finsetNonempty])]
/-
**Finset.Nonempty.product** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nonempty`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Finset α} {t : Finset β}, s.Nonempty 
→ t.Nonempty → (s ×ˢ t).Nonempty
参数：s ×ˢ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_product`：mem_product {p : α × β} : p in s ×ˢ t ↔ p.1 in s ∧ p
.2 in t
-/
theorem Nonempty.product (hs : s.Nonempty) (ht : t.Nonempty) : (s ×ˢ t).Nonempty :=
  let ⟨x, hx⟩ := hs
  let ⟨y, hy⟩ := ht
  ⟨(x, y), mem_product.2 ⟨hx, hy⟩⟩
/-
**Finset.Nonempty.fst** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nonempty`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Finset α} {t : Finset β}, (s ×ˢ t).No
nempty → s.Nonempty
参数：s ×ˢ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_product`：mem_product {p : α × β} : p in s ×ˢ t ↔ p.1 in s ∧ p
.2 in t
-/
theorem Nonempty.fst (h : (s ×ˢ t).Nonempty) : s.Nonempty :=
  let ⟨xy, hxy⟩ := h
  ⟨xy.1, (mem_product.1 hxy).1⟩
/-
**Finset.Nonempty.snd** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nonempty`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Finset α} {t : Finset β}, (s ×ˢ t).No
nempty → t.Nonempty
参数：s ×ˢ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_product`：mem_product {p : α × β} : p in s ×ˢ t ↔ p.1 in s ∧ p
.2 in t
-/
theorem Nonempty.snd (h : (s ×ˢ t).Nonempty) : t.Nonempty :=
  let ⟨xy, hxy⟩ := h
  ⟨xy.2, (mem_product.1 hxy).2⟩

@[simp]
/-
**Finset.nonempty_product** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：nonempty_product : (s ×ˢ t).Nonempty ↔ s.Nonempty ∧ t.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nonempty.fst`：∀ {α : Type u_1} {β : Type u_2} {s : Finset α} {t :
 Finset β}, (s ×ˢ t).Nonempty → s.Nonempty
· 使用定理 `Finset.Nonempty.snd`：∀ {α : Type u_1} {β : Type u_2} {s : Finset α} {t :
 Finset β}, (s ×ˢ t).Nonempty → t.Nonempty
· 使用定理 `Finset.Nonempty.product`：∀ {α : Type u_1} {β : Type u_2} {s : Finset α} 
{t : Finset β}, s.Nonempty → t.Nonempty → (s ×ˢ t).Nonempty
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem nonempty_product : (s ×ˢ t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  ⟨fun h => ⟨h.fst, h.snd⟩, fun h => h.1.product h.2⟩

@[simp]
/-
**Finset.product_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：product_eq_empty {s : Finset α} {t : Finset β} : s ×ˢ t = ∅ ↔ s = ∅ ∨ t = 
∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₁`：contrapose_iff₁ {p q : Prop} 
: (¬ p ↔ ¬ q) -> (p ↔ q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.nonempty_product`：nonempty_product : (s ×ˢ t).Nonempty ↔ s.Nonemp
ty ∧ t.Nonempty
-/
theorem product_eq_empty {s : Finset α} {t : Finset β} : s ×ˢ t = ∅ ↔ s = ∅ ∨ t = ∅ := by
  contrapose!; exact nonempty_product

@[simp]
/-
**Finset.singleton_product** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：singleton_product {a : α} : ({a} : Finset α) ×ˢ t = t.map ⟨Prod.mk a, Prod
.mk_right_injective _⟩
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Prod.mk_right_injective`：mk_right_injective {α β : Type*} (a : α) : (mk 
a : β -> α × β).Injective
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem singleton_product {a : α} :
    ({a} : Finset α) ×ˢ t = t.map ⟨Prod.mk a, Prod.mk_right_injective _⟩ := by
  ext ⟨x, y⟩
  simp [and_left_comm, eq_comm]

@[simp]
/-
**Finset.product_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：product_singleton : s ×ˢ {b} = s.map ⟨fun i => (i, b), Prod.mk_left_inject
ive _⟩
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Prod.mk_left_injective`：mk_left_injective {α β : Type*} (b : β) : (fun a
 => mk a b : α -> α × β).Injective
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma product_singleton : s ×ˢ {b} = s.map ⟨fun i => (i, b), Prod.mk_left_injective _⟩ := by
  ext ⟨x, y⟩
  simp [and_left_comm, eq_comm]
/-
**Finset.singleton_product_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：singleton_product_singleton {a : α} {b : β} : ({a} ×ˢ {b} : Finset _) = {(
a, b)}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prod.mk_left_injective`：mk_left_injective {α β : Type*} (b : β) : (fun a
 => mk a b : α -> α × β).Injective
· 使用引理 `Finset.product_singleton`：product_singleton : s ×ˢ {b} = s.map ⟨fun i =>
 (i, b), Prod.mk_left_injective _⟩
· 使用定理 `Finset.map_singleton`：map_singleton (f : α ↪ β) (a : α) : map f {a} = {f
 a}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem singleton_product_singleton {a : α} {b : β} :
    ({a} ×ˢ {b} : Finset _) = {(a, b)} := by
  simp only [product_singleton, Function.Embedding.coeFn_mk, map_singleton]

@[simp]
/-
**Finset.union_product** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：union_product [DecidableEq α] [DecidableEq β] : (s union s') ×ˢ t = s ×ˢ t
 union s' ×ˢ t
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem union_product [DecidableEq α] [DecidableEq β] : (s ∪ s') ×ˢ t = s ×ˢ t ∪ s' ×ˢ t := by grind

@[simp]
/-
**Finset.product_union** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：product_union [DecidableEq α] [DecidableEq β] : s ×ˢ (t union t') = s ×ˢ t
 union s ×ˢ t'
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem product_union [DecidableEq α] [DecidableEq β] : s ×ˢ (t ∪ t') = s ×ˢ t ∪ s ×ˢ t' := by grind
/-
**Finset.inter_product** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inter_product [DecidableEq α] [DecidableEq β] : (s inter s') ×ˢ t = s ×ˢ t
 inter s' ×ˢ t
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inter_product [DecidableEq α] [DecidableEq β] : (s ∩ s') ×ˢ t = s ×ˢ t ∩ s' ×ˢ t := by grind
/-
**Finset.product_inter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：product_inter [DecidableEq α] [DecidableEq β] : s ×ˢ (t inter t') = s ×ˢ t
 inter s ×ˢ t'
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem product_inter [DecidableEq α] [DecidableEq β] : s ×ˢ (t ∩ t') = s ×ˢ t ∩ s ×ˢ t' := by grind
/-
**Finset.product_inter_product** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：product_inter_product [DecidableEq α] [DecidableEq β] : s ×ˢ t inter s' ×ˢ
 t' = (s inter s') ×ˢ (t inter t')
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem product_inter_product [DecidableEq α] [DecidableEq β] :
    s ×ˢ t ∩ s' ×ˢ t' = (s ∩ s') ×ˢ (t ∩ t') := by grind
/-
**Finset.disjoint_product** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：disjoint_product : Disjoint (s ×ˢ t) (s' ×ˢ t') ↔ Disjoint s s' ∨ Disjoint
 t t'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_product`：coe_product (s : Finset α) (t : Finset β) : (↑(s ×ˢ 
t) : Set (α × β)) = (s : Set α) ×ˢ t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem disjoint_product : Disjoint (s ×ˢ t) (s' ×ˢ t') ↔ Disjoint s s' ∨ Disjoint t t' := by
  simp_rw [← disjoint_coe, coe_product, Set.disjoint_prod]

@[simp]
/-
**Finset.disjUnion_product** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：disjUnion_product (hs : Disjoint s s') : s.disjUnion s' hs ×ˢ t = (s ×ˢ t)
.disjUnion (s' ×ˢ t) (disjoint_product.mpr <| Or.inl hs)
参数：hs : Disjoint s s'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_of_veq`：∀ {α : Type u_1} {s t : Finset α}, s.val = t.val → s =
 t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.disjoint_product`：disjoint_product : Disjoint (s ×ˢ t) (s' ×ˢ t')
 ↔ Disjoint s s' ∨ Disjoint t t'
· 使用定理 `Multiset.add_product`：add_product (s t : Multiset α) (u : Multiset β) : 
(s + t) ×ˢ u = s ×ˢ u + t ×ˢ u
-/
theorem disjUnion_product (hs : Disjoint s s') :
    s.disjUnion s' hs ×ˢ t = (s ×ˢ t).disjUnion (s' ×ˢ t) (disjoint_product.mpr <| Or.inl hs) :=
  eq_of_veq <| Multiset.add_product _ _ _

@[simp]
/-
**Finset.product_disjUnion** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：product_disjUnion (ht : Disjoint t t') : s ×ˢ t.disjUnion t' ht = (s ×ˢ t)
.disjUnion (s ×ˢ t') (disjoint_product.mpr <| Or.inr ht)
参数：ht : Disjoint t t'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_of_veq`：∀ {α : Type u_1} {s t : Finset α}, s.val = t.val → s =
 t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.disjoint_product`：disjoint_product : Disjoint (s ×ˢ t) (s' ×ˢ t')
 ↔ Disjoint s s' ∨ Disjoint t t'
· 使用定理 `Multiset.product_add`：product_add (s : Multiset α) : forall t u : Multis
et β, s ×ˢ (t + u) = s ×ˢ t + s ×ˢ u
-/
theorem product_disjUnion (ht : Disjoint t t') :
    s ×ˢ t.disjUnion t' ht = (s ×ˢ t).disjUnion (s ×ˢ t') (disjoint_product.mpr <| Or.inr ht) :=
  eq_of_veq <| Multiset.product_add _ _ _

end Prod

section Diag

variable (s t : Finset α)

/-- Given a finite set `s`, the diagonal, `s.diag` is the set of pairs of the form `(a, a)` for
`a ∈ s`. -/
/-
**Finset.diag** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：diag : Finset (α × α)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Function.diag_injective`：diag_injective : Injective (α

--- 原说明 ---
Given a finite set `s`, the diagonal, `s.diag` is the set of pairs of the form `
(a, a)` for
`a ∈ s`.
-/
def diag : Finset (α × α) := s.map ⟨Function.diag, Function.diag_injective⟩

-- TODO: define `Multiset.offDiag`, provide basic API, use it here
/-- Given a finite set `s`, the off-diagonal, `s.offDiag` is the set of pairs `(a, b)` with `a ≠ b`
for `a, b ∈ s`. -/
/-
**Finset.offDiag** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：offDiag : Finset (α × α)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `List.Perm.offDiag`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → l₁.of
fDiag.Perm l₂.offDiag

--- 原说明 ---
Given a finite set `s`, the off-diagonal, `s.offDiag` is the set of pairs `(a, b
)` with `a ≠ b`
for `a, b ∈ s`.
-/
def offDiag : Finset (α × α) :=
  .mk (Quotient.map List.offDiag (fun _ _ ↦ List.Perm.offDiag) s.1) <| by
    rcases s with ⟨⟨s⟩, hs⟩
    exact hs.offDiag

variable {s} {x : α × α}

@[simp, grind =]
/-
**Finset.mem_diag** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_diag : x in s.diag ↔ x.1 in s ∧ x.1 = x.2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.diag_injective`：diag_injective : Injective (α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
theorem mem_diag : x ∈ s.diag ↔ x.1 ∈ s ∧ x.1 = x.2 := by
  aesop (add simp diag)

@[simp, grind =]
/-
**Finset.mem_offDiag** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_offDiag : x in s.offDiag ↔ x.1 in s ∧ x.2 in s ∧ x.1 != x.2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Nodup.mem_offDiag`：∀ {α : Type u_1} {l : List α}, l.Nodup → ∀ {x : 
α × α}, x ∈ l.offDiag ↔ x.1 ∈ l ∧ x.2 ∈ l ∧ x.1 ≠ x.2
-/
theorem mem_offDiag : x ∈ s.offDiag ↔ x.1 ∈ s ∧ x.2 ∈ s ∧ x.1 ≠ x.2 := by
  rcases s with ⟨⟨s⟩, hs⟩
  exact hs.mem_offDiag

@[simp, grind =]
/-
**Finset.diag_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：diag_nonempty : s.diag.Nonempty ↔ s.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.diag_injective`：diag_injective : Injective (α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem diag_nonempty : s.diag.Nonempty ↔ s.Nonempty := by
  simp [diag]

@[simp, grind =]
/-
**Finset.diag_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：diag_eq_empty : s.diag = ∅ ↔ s = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.diag_injective`：diag_injective : Injective (α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem diag_eq_empty : s.diag = ∅ ↔ s = ∅ := by
  simp [diag]
/-
**Finset.diag_eq_filter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：diag_eq_filter [DecidableEq α] : s.diag = (s ×ˢ s).filter fun a : α × α =>
 a.fst = a.snd
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem diag_eq_filter [DecidableEq α] :
    s.diag = (s ×ˢ s).filter fun a : α × α => a.fst = a.snd := by
  ext; simp +contextual

variable (s)

@[simp]
/-
**Finset.image_diag** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_diag [DecidableEq β] (f : α × α -> β) (s : Finset α) : s.diag.image 
f = s.image fun x => f (x, x)
参数：f : α × α -> β；s : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image_diag [DecidableEq β] (f : α × α → β) (s : Finset α) :
    s.diag.image f = s.image fun x ↦ f (x, x) := by
  grind

@[simp, norm_cast]
/-
**Finset.coe_offDiag** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_offDiag : (s.offDiag : Set (α × α)) = (s : Set α).offDiag
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Finset.mem_offDiag`：mem_offDiag : x in s.offDiag ↔ x.1 in s ∧ x.2 in s ∧
 x.1 != x.2
-/
theorem coe_offDiag : (s.offDiag : Set (α × α)) = (s : Set α).offDiag :=
  Set.ext fun _ => mem_offDiag

@[simp]
/-
**Finset.diag_card** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：diag_card : (diag s).card = s.card
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `Function.diag_injective`：diag_injective : Injective (α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem diag_card : (diag s).card = s.card := by
  simp [diag]

@[simp]
/-
**Finset.offDiag_card** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：offDiag_card : (offDiag s).card = s.card * s.card - s.card
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `List.length_offDiag`：length_offDiag (l : List α) : length l.offDiag = le
ngth l ^ 2 - length l
-/
theorem offDiag_card : (offDiag s).card = s.card * s.card - s.card := by
  rw [← sq]
  rcases s with ⟨⟨s⟩, hs⟩
  apply List.length_offDiag

@[gcongr, mono]
/-
**Finset.diag_mono** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：diag_mono : Monotone (diag : Finset α -> Finset (α × α))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Function.diag_injective`：diag_injective : Injective (α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem diag_mono : Monotone (diag : Finset α → Finset (α × α)) := fun _ _ ↦ by simp [diag]

@[gcongr, mono]
/-
**Finset.offDiag_mono** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：offDiag_mono : Monotone (offDiag : Finset α -> Finset (α × α))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_offDiag`：mem_offDiag : x in s.offDiag ↔ x.1 in s ∧ x.2 in s ∧
 x.1 != x.2
· 使用定理 `And.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∧ b → c ∧ d
· 使用定理 `And.imp_left`：∀ {a b c : Prop}, (a → b) → a ∧ c → b ∧ c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem offDiag_mono : Monotone (offDiag : Finset α → Finset (α × α)) := fun _ _ h _ hx =>
  mem_offDiag.2 <| And.imp (@h _) (And.imp_left <| @h _) <| mem_offDiag.1 hx

@[simp]
/-
**Finset.diag_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：diag_empty : (∅ : Finset α).diag = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem diag_empty : (∅ : Finset α).diag = ∅ :=
  rfl

@[simp]
/-
**Finset.offDiag_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：offDiag_empty : (∅ : Finset α).offDiag = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem offDiag_empty : (∅ : Finset α).offDiag = ∅ :=
  rfl

@[simp]
/-
**Finset.diag_union_offDiag** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：diag_union_offDiag [DecidableEq α] : s.diag union s.offDiag = s ×ˢ s
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem diag_union_offDiag [DecidableEq α] : s.diag ∪ s.offDiag = s ×ˢ s := by
  grind

@[simp]
/-
**Finset.disjoint_diag_offDiag** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：disjoint_diag_offDiag : Disjoint s.diag s.offDiag
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem disjoint_diag_offDiag : Disjoint s.diag s.offDiag := by simp [disjoint_left]
/-
**Finset.product_sdiff_diag** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：product_sdiff_diag [DecidableEq α] : s ×ˢ s \ s.diag = s.offDiag
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem product_sdiff_diag [DecidableEq α] : s ×ˢ s \ s.diag = s.offDiag := by grind
/-
**Finset.product_sdiff_offDiag** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：product_sdiff_offDiag [DecidableEq α] : s ×ˢ s \ s.offDiag = s.diag
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem product_sdiff_offDiag [DecidableEq α] : s ×ˢ s \ s.offDiag = s.diag := by grind
/-
**Finset.diag_inter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：diag_inter [DecidableEq α] : (s inter t).diag = s.diag inter t.diag
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem diag_inter [DecidableEq α] : (s ∩ t).diag = s.diag ∩ t.diag := by
  grind
/-
**Finset.offDiag_inter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：offDiag_inter [DecidableEq α] : (s inter t).offDiag = s.offDiag inter t.of
fDiag
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_offDiag`：coe_offDiag : (s.offDiag : Set (α × α)) = (s : Set α
).offDiag
· 使用定理 `Finset.coe_inter`：coe_inter (s₁ s₂ : Finset α) : ↑(s₁ inter s₂) = (s₁ in
ter s₂ : Set α)
· 使用定理 `Set.offDiag_inter`：offDiag_inter : (s inter t).offDiag = s.offDiag inter
 t.offDiag
-/
theorem offDiag_inter [DecidableEq α] : (s ∩ t).offDiag = s.offDiag ∩ t.offDiag :=
  coe_injective <| by
    push_cast
    exact Set.offDiag_inter _ _
/-
**Finset.diag_union** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：diag_union [DecidableEq α] : (s union t).diag = s.diag union t.diag
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem diag_union [DecidableEq α] : (s ∪ t).diag = s.diag ∪ t.diag := by
  grind

variable {s t}
/-
**Finset.offDiag_union** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：offDiag_union [DecidableEq α] (h : Disjoint s t) : (s union t).offDiag = s
.offDiag union t.offDiag union s ×ˢ t union t ×ˢ s
参数：h : Disjoint s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_offDiag`：coe_offDiag : (s.offDiag : Set (α × α)) = (s : Set α
).offDiag
· 使用定理 `Finset.coe_union`：coe_union (s₁ s₂ : Finset α) : ↑(s₁ union s₂) = (s₁ un
ion s₂ : Set α)
· 使用定理 `Finset.coe_product`：coe_product (s : Finset α) (t : Finset β) : (↑(s ×ˢ 
t) : Set (α × β)) = (s : Set α) ×ˢ t
· 使用定理 `Set.offDiag_union`：offDiag_union (h : Disjoint s t) : (s union t).offDia
g = s.offDiag union t.offDiag union s ×ˢ t union t ×ˢ s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.disjoint_coe`：disjoint_coe : Disjoint (s : Set α) t ↔ Disjoint s 
t
-/
theorem offDiag_union [DecidableEq α] (h : Disjoint s t) :
    (s ∪ t).offDiag = s.offDiag ∪ t.offDiag ∪ s ×ˢ t ∪ t ×ˢ s :=
  coe_injective <| by
    push_cast
    exact Set.offDiag_union (disjoint_coe.2 h)

@[simp]
/-
**Finset.offDiag_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：offDiag_singleton (a : α) : ({a} : Finset α).offDiag = ∅
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.offDiag_card`：offDiag_card : (offDiag s).card = s.card * s.card -
 s.card
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Nat.sub_self`：∀ (n : ℕ), n - n = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem offDiag_singleton (a : α) : ({a} : Finset α).offDiag = ∅ := by simp [← Finset.card_eq_zero]
/-
**Finset.diag_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：diag_singleton (a : α) : ({a} : Finset α).diag = {(a, a)}
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem diag_singleton (a : α) : ({a} : Finset α).diag = {(a, a)} := by grind
/-
**Finset.diag_insert** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：diag_insert [DecidableEq α] (a : α) : (insert a s).diag = insert (a, a) s.
diag
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem diag_insert [DecidableEq α] (a : α) :
    (insert a s).diag = insert (a, a) s.diag := by grind
/-
**Finset.offDiag_insert** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：offDiag_insert [DecidableEq α] {a : α} (has : a ∉ s) : (insert a s).offDia
g = s.offDiag union {a} ×ˢ s union s ×ˢ {a}
参数：has : a ∉ s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem offDiag_insert [DecidableEq α] {a : α} (has : a ∉ s) :
    (insert a s).offDiag = s.offDiag ∪ {a} ×ˢ s ∪ s ×ˢ {a} := by
  grind
/-
**Finset.offDiag_filter_lt_eq_filter_le** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：offDiag_filter_lt_eq_filter_le {ι} [PartialOrder ι] [DecidableLE ι] [Decid
ableLT ι] (s : Finset ι) : s.offDiag.filter (fun i => i.1 < i.2) = s.offDiag.fil
ter (fun i => i.1 <= i.2)
参数：s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Ne.le_iff_lt`：Ne.le_iff_lt (h : a != b) : a <= b ↔ a < b
-/
theorem offDiag_filter_lt_eq_filter_le {ι} [PartialOrder ι] [DecidableLE ι] [DecidableLT ι]
    (s : Finset ι) :
    s.offDiag.filter (fun i => i.1 < i.2) = s.offDiag.filter (fun i => i.1 ≤ i.2) := by
  ext
  simpa using fun _ _ a ↦ (Ne.le_iff_lt a).symm

/-- The number of strictly ordered pairs `(a, b)` with `a, b ∈ s` is `(#s).choose 2`. -/
/-
**Finset.card_product_filter_lt** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：card_product_filter_lt [LinearOrder α] : #{x in s ×ˢ s | x.1 < x.2} = (#s)
.choose 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.card_equiv`：card_equiv (e : α ≃ β) (hst : forall i, i in s ↔ e i 
in t) : #s = #t

--- 原说明 ---
The number of strictly ordered pairs `(a, b)` with `a, b ∈ s` is `(#s).choose 2`
.
-/
lemma card_product_filter_lt [LinearOrder α] :
    #{x ∈ s ×ˢ s | x.1 < x.2} = (#s).choose 2 := by
  set u : Finset (α × α) := {x ∈ s ×ˢ s | x.1 < x.2}
  set v : Finset (α × α) := {x ∈ s ×ˢ s | x.2 < x.1}
  have disj : Disjoint u v := by grind [disjoint_left]
  have union : u.disjUnion v disj = s.offDiag := by grind
  have swap : #u = #v := Finset.card_equiv (Equiv.prodComm α α) (by grind)
  grind [Nat.mul_sub_one, offDiag_card, Nat.choose_two_right]

end Diag

end Finset

