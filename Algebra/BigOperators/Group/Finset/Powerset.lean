/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Powerset

/-!
# Big operators

In this file we prove theorems about products and sums over a `Finset.powerset`.

-/

public section

variable {α β γ : Type*}

variable {s : Finset α} {a : α}

namespace Finset

variable [CommMonoid β]

/-- A product over all subsets of `s ∪ {x}` is obtained by multiplying the product over all subsets
of `s`, and over all subsets of `s` to which one adds `x`. -/
@[to_additive /-- A sum over all subsets of `s ∪ {x}` is obtained by summing the sum over all
subsets of `s`, and over all subsets of `s` to which one adds `x`. -/]
/-
**Finset.prod_powerset_insert** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_powerset_insert [DecidableEq α] (ha : a ∉ s) (f : Finset α -> β) : ∏ 
t in (insert a s).powerset, f t = (∏ t in s.powerset, f t) * ∏ t in s.powerset, 
f (insert a t)
参数：ha : a ∉ s；f : Finset α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.powerset_insert`：powerset_insert [DecidableEq α] (s : Finset α) (
a : α) : powerset (insert a s) = s.powerset union s.powerset.image (insert a)
· 使用定理 `Finset.prod_union`：prod_union [DecidableEq ι] (h : Disjoint s₁ s₂) : ∏ x
 in s₁ union s₂, f x = (∏ x in s₁, f x) * ∏ x in s₂, f x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Finset.prod_image`：prod_image [DecidableEq ι] {s : Finset κ} {g : κ -> ι
} : Set.InjOn g s -> ∏ x in s.image g, f x = ∏ x in s, f (g x)
· 使用定理 `Set.InjOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f : α →
 β}, s₁ ⊆ s₂ → Set.InjOn f s₂ → Set.InjOn f s₁
· 使用定理 `Finset.notMem_mono`：notMem_mono {s t : Finset α} (h : s subseteq t) {a :
 α} : a ∉ t -> a ∉ s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_powerset`：mem_powerset {s t : Finset α} : s in powerset t ↔ s
 subseteq t
· 使用定理 `Set.LeftInvOn.injOn`：injOn (h : LeftInvOn f₁' f s) : InjOn f s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `Finset.insert_erase_invOn`：insert_erase_invOn : Set.InvOn (insert a) (fu
n s => s.erase a) {s : Finset α | a in s} {s : Finset α | a ∉ s}
-/
lemma prod_powerset_insert [DecidableEq α] (ha : a ∉ s) (f : Finset α → β) :
    ∏ t ∈ (insert a s).powerset, f t =
      (∏ t ∈ s.powerset, f t) * ∏ t ∈ s.powerset, f (insert a t) := by
  rw [powerset_insert, prod_union, prod_image]
  · exact insert_erase_invOn.2.injOn.mono fun t ht ↦ notMem_mono (mem_powerset.1 ht) ha
  · aesop (add simp [disjoint_left, insert_subset_iff])

/-- A product over all subsets of `s ∪ {x}` is obtained by multiplying the product over all subsets
of `s`, and over all subsets of `s` to which one adds `x`. -/
@[to_additive /-- A sum over all subsets of `s ∪ {x}` is obtained by summing the sum over all
subsets of `s`, and over all subsets of `s` to which one adds `x`. -/]
/-
**Finset.prod_powerset_cons** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_powerset_cons (ha : a ∉ s) (f : Finset α -> β) : ∏ t in (s.cons a ha)
.powerset, f t = (∏ t in s.powerset, f t) * ∏ t in s.powerset.attach, f (cons a 
t <| notMem_mono (mem_powerset.1 t.2) ha)
参数：ha : a ∉ s；f : Finset α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.notMem_mono`：notMem_mono {s t : Finset α} (h : s subseteq t) {a :
 α} : a ∉ t -> a ∉ s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_powerset`：mem_powerset {s t : Finset α} : s in powerset t ↔ s
 subseteq t
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.cons_eq_insert`：cons_eq_insert (a s h) : @cons α a s h = insert a
 s
· 使用引理 `Finset.prod_powerset_insert`：prod_powerset_insert [DecidableEq α] (ha : 
a ∉ s) (f : Finset α -> β) : ∏ t in (insert a s).powerset, f t = (∏ t in s.power
set, f t) * ∏ t i…
· 使用引理 `Finset.prod_attach`：prod_attach (s : Finset ι) (f : ι -> M) : ∏ x in s.a
ttach, f x = ∏ x in s, f x
-/
lemma prod_powerset_cons (ha : a ∉ s) (f : Finset α → β) :
    ∏ t ∈ (s.cons a ha).powerset, f t = (∏ t ∈ s.powerset, f t) *
      ∏ t ∈ s.powerset.attach, f (cons a t <| notMem_mono (mem_powerset.1 t.2) ha) := by
  classical
  simp_rw [cons_eq_insert]
  rw [prod_powerset_insert ha, prod_attach _ fun t ↦ f (insert a t)]

set_option backward.isDefEq.respectTransparency false in
/-- A product over `powerset s` is equal to the double product over sets of subsets of `s` with
`#s = k`, for `k = 0, ..., #s`. -/
@[to_additive /-- A sum over `powerset s` is equal to the double sum over sets of subsets of `s`
with `#s = k`, for `k = 0, ..., #s` -/]
/-
**Finset.prod_powerset** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_powerset (s : Finset α) (f : Finset α -> β) : ∏ t in powerset s, f t 
= ∏ j in range (#s + 1), ∏ t in powersetCard j s, f t
参数：s : Finset α；f : Finset α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pairwise.set_pairwise`：Pairwise.set_pairwise (hl : Pairwise R l) [Std.Sy
mm R] : { x | x in l }.Pairwise R
· 使用定理 `Finset.pairwise_disjoint_powersetCard`：pairwise_disjoint_powersetCard (s
 : Finset α) : Pairwise fun i j => Disjoint (s.powersetCard i) (s.powersetCard j
)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.powerset_card_disjiUnion`：powerset_card_disjiUnion (s : Finset α)
 : Finset.powerset s = (range (s.card + 1)).disjiUnion (fun i => powersetCard i 
s) (s.pairwise_disjoi…
· 使用定理 `Finset.prod_disjiUnion`：prod_disjiUnion (s : Finset κ) (t : κ -> Finset 
ι) (h) : ∏ x in s.disjiUnion t h, f x = ∏ i in s, ∏ x in t i, f x
-/
lemma prod_powerset (s : Finset α) (f : Finset α → β) :
    ∏ t ∈ powerset s, f t = ∏ j ∈ range (#s + 1), ∏ t ∈ powersetCard j s, f t := by
  rw [powerset_card_disjiUnion, prod_disjiUnion]

/-- A product over `Finset.powersetCard` which only depends on the size of the sets is constant. -/
@[to_additive
/-- A sum over `Finset.powersetCard` which only depends on the size of the sets is constant. -/]
/-
**Finset.prod_powersetCard** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_powersetCard (n : Nat) (s : Finset α) (f : Nat -> β) : ∏ t in powerse
tCard n s, f #t = f n ^ (#s).choose n
参数：n : Nat；s : Finset α；f : Nat -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_eq_pow_card`：prod_eq_pow_card {b : M} (hf : forall a in s, f
 a = b) : ∏ a in s, f a = b ^ #s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_powersetCard`：∀ {α : Type u_1} {n : ℕ} {s t : Finset α}, s ∈ 
Finset.powersetCard n t ↔ s ⊆ t ∧ s.card = n
· 使用定理 `Finset.card_powersetCard`：card_powersetCard (n : Nat) (s : Finset α) : c
ard (powersetCard n s) = Nat.choose (card s) n
-/
lemma prod_powersetCard (n : ℕ) (s : Finset α) (f : ℕ → β) :
    ∏ t ∈ powersetCard n s, f #t = f n ^ (#s).choose n := by
  rw [prod_eq_pow_card, card_powersetCard]; rintro a ha; rw [(mem_powersetCard.1 ha).2]

end Finset

