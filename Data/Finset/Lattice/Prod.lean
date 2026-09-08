/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Prod

/-!
# Lattice operations on finsets of products

This file is concerned with folding binary lattice operations over finsets.
-/

public section

assert_not_exists IsOrderedMonoid MonoidWithZero

open Function Multiset OrderDual

variable {F α β γ ι κ : Type*}

namespace Finset


section Sup

-- TODO: define with just `[Bot α]` where some lemmas hold without requiring `[OrderBot α]`
variable [SemilatticeSup α] [OrderBot α]

/-- See also `Finset.product_biUnion`. -/
@[to_dual inf_product_left]
/-
**Finset.sup_product_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sup_product_left (s : Finset β) (t : Finset γ) (f : β × γ -> α) : (s ×ˢ t)
.sup f = s.sup fun i => t.sup fun i' => f ⟨i, i'⟩
参数：s : Finset β；t : Finset γ；f : β × γ -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
See also `Finset.product_biUnion`.
-/
theorem sup_product_left (s : Finset β) (t : Finset γ) (f : β × γ → α) :
    (s ×ˢ t).sup f = s.sup fun i => t.sup fun i' => f ⟨i, i'⟩ :=
  eq_of_forall_ge_iff fun a => by simp [@forall_comm _ γ]

@[to_dual inf_product_right]
/-
**Finset.sup_product_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sup_product_right (s : Finset β) (t : Finset γ) (f : β × γ -> α) : (s ×ˢ t
).sup f = t.sup fun i' => s.sup fun i => f ⟨i, i'⟩
参数：s : Finset β；t : Finset γ；f : β × γ -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_product_left`：sup_product_left (s : Finset β) (t : Finset γ) 
(f : β × γ -> α) : (s ×ˢ t).sup f = s.sup fun i => t.sup fun i' => f ⟨i, i'⟩
· 使用定理 `Finset.sup_comm`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [inst : 
SemilatticeSup α] [inst_1 : OrderBot α] (s : Finset β)   (t : Finset γ) (f : β →
 γ → …
-/
theorem sup_product_right (s : Finset β) (t : Finset γ) (f : β × γ → α) :
    (s ×ˢ t).sup f = t.sup fun i' => s.sup fun i => f ⟨i, i'⟩ := by
  rw [sup_product_left, Finset.sup_comm]

section Prod
variable {ι κ α β : Type*} [SemilatticeSup α] [SemilatticeSup β] [OrderBot α] [OrderBot β]
  {s : Finset ι} {t : Finset κ}

@[to_dual (attr := simp)]
/-
**Finset.sup_prodMap** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：sup_prodMap (hs : s.Nonempty) (ht : t.Nonempty) (f : ι -> α) (g : κ -> β) 
: sup (s ×ˢ t) (Prod.map f g) = (sup s f, sup t g)
参数：hs : s.Nonempty；ht : t.Nonempty；f : ι -> α；g : κ -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma sup_prodMap (hs : s.Nonempty) (ht : t.Nonempty) (f : ι → α) (g : κ → β) :
    sup (s ×ˢ t) (Prod.map f g) = (sup s f, sup t g) :=
  eq_of_forall_ge_iff fun i ↦ by
    obtain ⟨a, ha⟩ := hs
    obtain ⟨b, hb⟩ := ht
    simp only [Prod.map, Finset.sup_le_iff, mem_product, and_imp, Prod.forall, Prod.le_def]
    exact ⟨fun h ↦ ⟨fun i hi ↦ (h _ _ hi hb).1, fun j hj ↦ (h _ _ ha hj).2⟩, by simp_all⟩

end Prod

end Sup

section DistribLattice

variable [DistribLattice α]

variable [OrderBot α] {s : Finset ι} {t : Finset κ} {f : ι → α} {g : κ → α} {a : α}

@[to_dual]
/-
**Finset.sup_inf_sup** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sup_inf_sup (s : Finset ι) (t : Finset κ) (f : ι -> α) (g : κ -> α) : s.su
p f ⊓ t.sup g = (s ×ˢ t).sup fun i => f i.1 ⊓ g i.2
参数：s : Finset ι；t : Finset κ；f : ι -> α；g : κ -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_inf_distrib_right`：sup_inf_distrib_right (s : Finset ι) (f : 
ι -> α) (a : α) : s.sup f ⊓ a = s.sup fun i => f i ⊓ a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sup_inf_distrib_left`：sup_inf_distrib_left (s : Finset ι) (f : ι 
-> α) (a : α) : a ⊓ s.sup f = s.sup fun i => a ⊓ f i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sup_product_left`：sup_product_left (s : Finset β) (t : Finset γ) 
(f : β × γ -> α) : (s ×ˢ t).sup f = s.sup fun i => t.sup fun i' => f ⟨i, i'⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sup_inf_sup (s : Finset ι) (t : Finset κ) (f : ι → α) (g : κ → α) :
    s.sup f ⊓ t.sup g = (s ×ˢ t).sup fun i => f i.1 ⊓ g i.2 := by
  simp_rw [Finset.sup_inf_distrib_right, Finset.sup_inf_distrib_left, sup_product_left]

end DistribLattice

section Sup'

variable [SemilatticeSup α]

variable {s : Finset β} (H : s.Nonempty) (f : β → α)

@[to_dual inf'_product_left]
/-
**Finset.sup'_product_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [inst : SemilatticeSup α] {
s : Finset β} {t : Finset γ}   (h : (s ×ˢ t).Nonempty) (f : β × γ → α), (s ×ˢ t)
.sup' h f = s.sup' ⋯ fun i => t.sup' ⋯ fun i' => f (i, i')
参数：h : (s ×ˢ t).Nonempty；f : β × γ → α；s ×ˢ t；i, i'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.Nonempty.fst`：∀ {α : Type u_1} {β : Type u_2} {s : Finset α} {t :
 Finset β}, (s ×ˢ t).Nonempty → s.Nonempty
· 使用定理 `Finset.Nonempty.snd`：∀ {α : Type u_1} {β : Type u_2} {s : Finset α} {t :
 Finset β}, (s ×ˢ t).Nonempty → t.Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sup'_product_left {t : Finset γ} (h : (s ×ˢ t).Nonempty) (f : β × γ → α) :
    (s ×ˢ t).sup' h f = s.sup' h.fst fun i => t.sup' h.snd fun i' => f ⟨i, i'⟩ :=
  eq_of_forall_ge_iff fun a => by simp [@forall_comm _ γ]

@[to_dual inf'_product_right]
/-
**Finset.sup'_product_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [inst : SemilatticeSup α] {
s : Finset β} {t : Finset γ}   (h : (s ×ˢ t).Nonempty) (f : β × γ → α), (s ×ˢ t)
.sup' h f = t.sup' ⋯ fun i' => s.sup' ⋯ fun i => f (i, i')
参数：h : (s ×ˢ t).Nonempty；f : β × γ → α；s ×ˢ t；i, i'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.Nonempty.snd`：∀ {α : Type u_1} {β : Type u_2} {s : Finset α} {t :
 Finset β}, (s ×ˢ t).Nonempty → t.Nonempty
· 使用定理 `Finset.Nonempty.fst`：∀ {α : Type u_1} {β : Type u_2} {s : Finset α} {t :
 Finset β}, (s ×ˢ t).Nonempty → s.Nonempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup'_product_left`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4}
 [inst : SemilatticeSup α] {s : Finset β} {t : Finset γ}   (h : (s ×ˢ t).Nonempt
y) (f : β × γ …
· 使用定理 `Finset.sup'_comm`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [inst :
 SemilatticeSup α] {s : Finset β} {t : Finset γ} (hs : s.Nonempty)   (ht : t.Non
empty)…
-/
theorem sup'_product_right {t : Finset γ} (h : (s ×ˢ t).Nonempty) (f : β × γ → α) :
    (s ×ˢ t).sup' h f = t.sup' h.snd fun i' => s.sup' h.fst fun i => f ⟨i, i'⟩ := by
  rw [sup'_product_left, Finset.sup'_comm]

section Prod
variable {ι κ α β : Type*} [SemilatticeSup α] [SemilatticeSup β] {s : Finset ι} {t : Finset κ}

set_option backward.isDefEq.respectTransparency false in
/-- See also `Finset.sup'_prodMap`. -/
@[to_dual /-- See also `Finset.inf'_prodMap`. -/]
/-
**Finset.prodMk_sup'_sup'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {ι : Type u_7} {κ : Type u_8} {α : Type u_9} {β : Type u_10} [inst : Sem
ilatticeSup α] [inst_1 : SemilatticeSup β]   {s : Finset ι} {t : Finset κ} (hs :
 s.Nonempty) (ht : t.Nonempty) (f : ι → α) (g : κ → β),   (s.sup' hs f, t.sup' h
t g) = (s ×ˢ t).sup' ⋯ (Prod.map f g)
参数：hs : s.Nonempty；ht : t.Nonempty；f : ι → α；g : κ → β；s.sup' hs f, t.sup' ht g；
s ×ˢ t；Prod.map f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.Nonempty.product`：∀ {α : Type u_1} {β : Type u_2} {s : Finset α} 
{t : Finset β}, s.Nonempty → t.Nonempty → (s ×ˢ t).Nonempty
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sup'_congr`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSu
p α] {s : Finset β} (H : s.Nonempty) {t : Finset β} {f g : β → α}   (h₁ : s = t)
, (∀ x …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
See also `Finset.sup'_prodMap`.
-/
lemma prodMk_sup'_sup' (hs : s.Nonempty) (ht : t.Nonempty) (f : ι → α) (g : κ → β) :
    (sup' s hs f, sup' t ht g) = sup' (s ×ˢ t) (hs.product ht) (Prod.map f g) :=
  eq_of_forall_ge_iff fun i ↦ by
    obtain ⟨a, ha⟩ := hs
    obtain ⟨b, hb⟩ := ht
    simp only [Prod.map, sup'_le_iff, mem_product, and_imp, Prod.forall, Prod.le_def]
    exact ⟨by simp_all, fun h ↦ ⟨fun i hi ↦ (h _ _ hi hb).1, fun j hj ↦ (h _ _ ha hj).2⟩⟩

/-- See also `Finset.prodMk_sup'_sup'`. -/
@[to_dual -- (attr := simp) -- TODO: Why does `Prod.map_apply` simplify the LHS?
/-- See also `Finset.prodMk_inf'_inf'`. -/]
/-
**Finset.sup'_prodMap** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {ι : Type u_7} {κ : Type u_8} {α : Type u_9} {β : Type u_10} [inst : Sem
ilatticeSup α] [inst_1 : SemilatticeSup β]   {s : Finset ι} {t : Finset κ} (hst 
: (s ×ˢ t).Nonempty) (f : ι → α) (g : κ → β),   (s ×ˢ t).sup' hst (Prod.map f g)
 = (s.sup' ⋯ f, t.sup' ⋯ g)
参数：hst : (s ×ˢ t).Nonempty；f : ι → α；g : κ → β；s ×ˢ t；Prod.map f g；s.sup' ⋯ f, t
.sup' ⋯ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.Nonempty.fst`：∀ {α : Type u_1} {β : Type u_2} {s : Finset α} {t :
 Finset β}, (s ×ˢ t).Nonempty → s.Nonempty
· 使用定理 `Finset.Nonempty.snd`：∀ {α : Type u_1} {β : Type u_2} {s : Finset α} {t :
 Finset β}, (s ×ˢ t).Nonempty → t.Nonempty
· 使用定理 `Finset.Nonempty.product`：∀ {α : Type u_1} {β : Type u_2} {s : Finset α} 
{t : Finset β}, s.Nonempty → t.Nonempty → (s ×ˢ t).Nonempty
· 使用定理 `Finset.prodMk_sup'_sup'`：∀ {ι : Type u_7} {κ : Type u_8} {α : Type u_9} 
{β : Type u_10} [inst : SemilatticeSup α] [inst_1 : SemilatticeSup β]   {s : Fin
set ι} {t : F…
-/
lemma sup'_prodMap (hst : (s ×ˢ t).Nonempty) (f : ι → α) (g : κ → β) :
    sup' (s ×ˢ t) hst (Prod.map f g) = (sup' s hst.fst f, sup' t hst.snd g) :=
  (prodMk_sup'_sup' _ _ _ _).symm

end Prod

end Sup'

section DistribLattice
variable [DistribLattice α] {s : Finset ι} {t : Finset κ} (hs : s.Nonempty) (ht : t.Nonempty)
  {f : ι → α} {g : κ → α} {a : α}

@[to_dual]
/-
**Finset.sup'_inf_sup'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {ι : Type u_5} {κ : Type u_6} [inst : DistribLattice α] {
s : Finset ι} {t : Finset κ} (hs : s.Nonempty)   (ht : t.Nonempty) (f : ι → α) (
g : κ → α), s.sup' hs f ⊓ t.sup' ht g = (s ×ˢ t).sup' ⋯ fun i => f i.1 ⊓ g i.2
参数：hs : s.Nonempty；ht : t.Nonempty；f : ι → α；g : κ → α；s ×ˢ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.Nonempty.product`：∀ {α : Type u_1} {β : Type u_2} {s : Finset α} 
{t : Finset β}, s.Nonempty → t.Nonempty → (s ×ˢ t).Nonempty
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup'_inf_distrib_right`：∀ {α : Type u_2} {ι : Type u_5} [inst : D
istribLattice α] {s : Finset ι} (hs : s.Nonempty) (f : ι → α) (a : α),   s.sup' 
hs f ⊓ a = s.sup' h…
· 使用定理 `Finset.sup'_congr`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSu
p α] {s : Finset β} (H : s.Nonempty) {t : Finset β} {f g : β → α}   (h₁ : s = t)
, (∀ x …
· 使用定理 `Finset.sup'_inf_distrib_left`：∀ {α : Type u_2} {ι : Type u_5} [inst : Di
stribLattice α] {s : Finset ι} (hs : s.Nonempty) (f : ι → α) (a : α),   a ⊓ s.su
p' hs f = s.sup' h…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.Nonempty.fst`：∀ {α : Type u_1} {β : Type u_2} {s : Finset α} {t :
 Finset β}, (s ×ˢ t).Nonempty → s.Nonempty
· 使用定理 `Finset.Nonempty.snd`：∀ {α : Type u_1} {β : Type u_2} {s : Finset α} {t :
 Finset β}, (s ×ˢ t).Nonempty → t.Nonempty
· 使用定理 `Finset.sup'_product_left`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4}
 [inst : SemilatticeSup α] {s : Finset β} {t : Finset γ}   (h : (s ×ˢ t).Nonempt
y) (f : β × γ …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sup'_inf_sup' (f : ι → α) (g : κ → α) :
    s.sup' hs f ⊓ t.sup' ht g = (s ×ˢ t).sup' (hs.product ht) fun i => f i.1 ⊓ g i.2 := by
  simp_rw [Finset.sup'_inf_distrib_right, Finset.sup'_inf_distrib_left, sup'_product_left]

end DistribLattice

end Finset

