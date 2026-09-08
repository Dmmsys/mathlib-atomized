/-
Copyright (c) 2022 Yaël Dillies, Ella Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Ella Yu
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-!
# Additive energy

This file defines the additive energy of two finsets of a group. This is a central quantity in
additive combinatorics.

## Main declarations

* `Finset.addEnergy`: The additive energy of two finsets in an additive group.
* `Finset.mulEnergy`: The multiplicative energy of two finsets in a group.

## Notation

The following notations are defined in the `Combinatorics.Additive` scope:
* `E[s, t]` for `Finset.addEnergy s t`.
* `Eₘ[s, t]` for `Finset.mulEnergy s t`.
* `E[s]` for `E[s, s]`.
* `Eₘ[s]` for `Eₘ[s, s]`.

## TODO

It's possibly interesting to have
`(s ×ˢ s) ×ˢ t ×ˢ t).filter (fun x : (α × α) × α × α ↦ x.1.1 * x.2.1 = x.1.2 * x.2.2)`
(whose `card` is `mulEnergy s t`) as a standalone definition.
-/

@[expose] public section

open scoped Pointwise

variable {α : Type*} [DecidableEq α]

namespace Finset
section Mul
variable [Mul α] {s s₁ s₂ t t₁ t₂ : Finset α}

/-- The multiplicative energy `Eₘ[s, t]` of two finsets `s` and `t` in a group is the number of
quadruples `(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ * b₁ = a₂ * b₂`.

The notation `Eₘ[s, t]` is available in scope `Combinatorics.Additive`. -/
@[to_additive
/-- The additive energy `E[s, t]` of two finsets `s` and `t` in a group is the number of quadruples
`(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ + b₁ = a₂ + b₂`.

The notation `E[s, t]` is available in scope `Combinatorics.Additive`. -/]
/-
**Finset.mulEnergy** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：mulEnergy (s t : Finset α) : Nat
参数：s t : Finset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mulEnergy (s t : Finset α) : ℕ :=
  #{x ∈ ((s ×ˢ s) ×ˢ t ×ˢ t) | x.1.1 * x.2.1 = x.1.2 * x.2.2}

/-- The multiplicative energy of two finsets `s` and `t` in a group is the number of quadruples
`(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ * b₁ = a₂ * b₂`. -/
scoped[Combinatorics.Additive] notation3:max "Eₘ[" s ", " t "]" => Finset.mulEnergy s t

/-- The additive energy of two finsets `s` and `t` in a group is the number of quadruples
`(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ + b₁ = a₂ + b₂`. -/
scoped[Combinatorics.Additive] notation3:max "E[" s ", " t "]" => Finset.addEnergy s t

/-- The multiplicative energy of a finset `s` in a group is the number of quadruples
`(a₁, a₂, b₁, b₂) ∈ s × s × s × s` such that `a₁ * b₁ = a₂ * b₂`. -/
scoped[Combinatorics.Additive] notation3:max "Eₘ[" s "]" => Finset.mulEnergy s s

/-- The additive energy of a finset `s` in a group is the number of quadruples
`(a₁, a₂, b₁, b₂) ∈ s × s × s × s` such that `a₁ + b₁ = a₂ + b₂`. -/
scoped[Combinatorics.Additive] notation3:max "E[" s "]" => Finset.addEnergy s s

open scoped Combinatorics.Additive

@[to_additive (attr := gcongr)]
/-
**Finset.mulEnergy_mono** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：mulEnergy_mono (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂) : Eₘ[s₁, t₁] <=
 Eₘ[s₂, t₂]
参数：hs : s₁ subseteq s₂；ht : t₁ subseteq t₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `Finset.filter_subset_filter`：∀ {α : Type u_1} (p : α → Prop) [inst : Dec
idablePred p] {s t : Finset α}, s ⊆ t → Finset.filter p s ⊆ Finset.filter p t
· 使用定理 `Finset.product_subset_product`：product_subset_product (hs : s subseteq s
') (ht : t subseteq t') : s ×ˢ t subseteq s' ×ˢ t'
-/
lemma mulEnergy_mono (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) : Eₘ[s₁, t₁] ≤ Eₘ[s₂, t₂] := by
  unfold mulEnergy; gcongr
/-
**Finset.mulEnergy_mono_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : Mul α] {s₁ s₂ t : Finset
 α}, s₁ ⊆ s₂ → s₁.mulEnergy t ≤ s₂.mulEnergy t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.mulEnergy_mono`：mulEnergy_mono (hs : s₁ subseteq s₂) (ht : t₁ sub
seteq t₂) : Eₘ[s₁, t₁] <= Eₘ[s₂, t₂]
· 使用定理 `Finset.Subset.rfl`：∀ {α : Type u_1} {s : Finset α}, s ⊆ s
-/
@[to_additive] lemma mulEnergy_mono_left (hs : s₁ ⊆ s₂) : Eₘ[s₁, t] ≤ Eₘ[s₂, t] :=
  mulEnergy_mono hs Subset.rfl
/-
**Finset.mulEnergy_mono_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : Mul α] {s t₁ t₂ : Finset
 α}, t₁ ⊆ t₂ → s.mulEnergy t₁ ≤ s.mulEnergy t₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.mulEnergy_mono`：mulEnergy_mono (hs : s₁ subseteq s₂) (ht : t₁ sub
seteq t₂) : Eₘ[s₁, t₁] <= Eₘ[s₂, t₂]
· 使用定理 `Finset.Subset.rfl`：∀ {α : Type u_1} {s : Finset α}, s ⊆ s
-/
@[to_additive] lemma mulEnergy_mono_right (ht : t₁ ⊆ t₂) : Eₘ[s, t₁] ≤ Eₘ[s, t₂] :=
  mulEnergy_mono Subset.rfl ht
/-
**Finset.le_mulEnergy** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : Mul α] {s t : Finset α},
 s.card * t.card ≤ s.mulEnergy t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_product`：card_product (s : Finset α) (t : Finset β) : card (
s ×ˢ t) = card s * card t
· 使用引理 `Finset.card_le_card_of_injOn`：card_le_card_of_injOn (f : α -> β) (hf : S
et.MapsTo f s t) (f_inj : (s : Set α).InjOn f) : #s <= #t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_product`：coe_product (s : Finset α) (t : Finset β) : (↑(s ×ˢ 
t) : Set (α × β)) = (s : Set α) ×ˢ t
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.coe_filter`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePred
 p] (s : Finset α), ↑(Finset.filter p s) = {x | x ∈ s ∧ p x}
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[to_additive] lemma le_mulEnergy : #s * #t ≤ Eₘ[s, t] := by
  rw [← card_product]
  exact card_le_card_of_injOn (fun x => ((x.1, x.1), x.2, x.2)) (by simp [Set.MapsTo]) (by simp)
/-
**Finset.le_mulEnergy_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : Mul α] {s : Finset α}, s
.card ^ 2 ≤ s.mulEnergy s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.le_mulEnergy`：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : M
ul α] {s t : Finset α}, s.card * t.card ≤ s.mulEnergy t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
-/
@[to_additive] lemma le_mulEnergy_self : #s ^ 2 ≤ Eₘ[s] := sq #s ▸ le_mulEnergy
/-
**Finset.mulEnergy_pos** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : Mul α] {s t : Finset α},
 s.Nonempty → t.Nonempty → 0 < s.mulEnergy t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `Finset.Nonempty.card_pos`：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → 
0 < s.card
· 使用定理 `Finset.le_mulEnergy`：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : M
ul α] {s t : Finset α}, s.card * t.card ≤ s.mulEnergy t
-/
@[to_additive] lemma mulEnergy_pos (hs : s.Nonempty) (ht : t.Nonempty) : 0 < Eₘ[s, t] :=
  (mul_pos hs.card_pos ht.card_pos).trans_le le_mulEnergy
/-
**Finset.mulEnergy_self_pos** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : Mul α] {s : Finset α}, s
.Nonempty → 0 < s.mulEnergy s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mulEnergy_pos`：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : 
Mul α] {s t : Finset α}, s.Nonempty → t.Nonempty → 0 < s.mulEnergy t
-/
@[to_additive] lemma mulEnergy_self_pos (hs : s.Nonempty) : 0 < Eₘ[s] :=
  mulEnergy_pos hs hs

variable (s t)
/-
**Finset.mulEnergy_empty_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : Mul α] (t : Finset α), ∅
.mulEnergy t = 0
参数：t : Finset α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.filter.congr_simp`：∀ {α : Type u_1} (p p_1 : α → Prop),   p = p_1
 →     ∀ {inst : DecidablePred p} [inst_1 : DecidablePred p_1] (s s_1 : Finset α
),       s = s…
· 使用定理 `Finset.product_empty`：product_empty (s : Finset α) : s ×ˢ (∅ : Finset β)
 = ∅
· 使用定理 `Finset.filter_empty`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePr
ed p], Finset.filter p ∅ = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[to_additive (attr := simp)] lemma mulEnergy_empty_left : Eₘ[∅, t] = 0 := by simp [mulEnergy]
/-
**Finset.mulEnergy_empty_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : Mul α] (s : Finset α), s
.mulEnergy ∅ = 0
参数：s : Finset α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.filter.congr_simp`：∀ {α : Type u_1} (p p_1 : α → Prop),   p = p_1
 →     ∀ {inst : DecidablePred p} [inst_1 : DecidablePred p_1] (s s_1 : Finset α
),       s = s…
· 使用定理 `Finset.product_empty`：product_empty (s : Finset α) : s ×ˢ (∅ : Finset β)
 = ∅
· 使用定理 `Finset.filter_empty`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePr
ed p], Finset.filter p ∅ = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[to_additive (attr := simp)] lemma mulEnergy_empty_right : Eₘ[s, ∅] = 0 := by simp [mulEnergy]

variable {s t}
/-
**Finset.mulEnergy_pos_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : Mul α] {s t : Finset α},
 0 < s.mulEnergy t ↔ s.Nonempty ∧ t.Nonempty
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_and_or_eq`：not_and_or_eq : (¬ (p ∧ q)) = (¬ p ∨ 
¬ q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mulEnergy_empty_left`：∀ {α : Type u_1} [inst : DecidableEq α] [in
st_1 : Mul α] (t : Finset α), ∅.mulEnergy t = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.mulEnergy_empty_right`：∀ {α : Type u_1} [inst : DecidableEq α] [i
nst_1 : Mul α] (s : Finset α), s.mulEnergy ∅ = 0
· 使用定理 `Finset.mulEnergy_pos`：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : 
Mul α] {s t : Finset α}, s.Nonempty → t.Nonempty → 0 < s.mulEnergy t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
@[to_additive (attr := simp)] lemma mulEnergy_pos_iff : 0 < Eₘ[s, t] ↔ s.Nonempty ∧ t.Nonempty where
  mp h := by by_contra! +distrib rfl | rfl <;> simp at h
  mpr h := mulEnergy_pos h.1 h.2
/-
**Finset.mulEnergy_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : Mul α] {s t : Finset α},
 s.mulEnergy t = 0 ↔ s = ∅ ∨ t = ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.not_lt_iff_eq'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}
, b ≤ a → (¬b < a ↔ a = b)
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[to_additive (attr := simp)] lemma mulEnergy_eq_zero_iff : Eₘ[s, t] = 0 ↔ s = ∅ ∨ t = ∅ := by
  simp [← (Nat.zero_le _).not_lt_iff_eq', imp_iff_or_not, or_comm]
/-
**Finset.mulEnergy_self_pos_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : Mul α] {s : Finset α}, 0
 < s.mulEnergy s ↔ s.Nonempty
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mulEnergy_pos_iff`：∀ {α : Type u_1} [inst : DecidableEq α] [inst_
1 : Mul α] {s t : Finset α}, 0 < s.mulEnergy t ↔ s.Nonempty ∧ t.Nonempty
· 使用定理 `and_self_iff`：∀ {a : Prop}, a ∧ a ↔ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[to_additive] lemma mulEnergy_self_pos_iff : 0 < Eₘ[s] ↔ s.Nonempty := by
  rw [mulEnergy_pos_iff, and_self_iff]
/-
**Finset.mulEnergy_self_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : Mul α] {s : Finset α}, s
.mulEnergy s = 0 ↔ s = ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mulEnergy_eq_zero_iff`：∀ {α : Type u_1} [inst : DecidableEq α] [i
nst_1 : Mul α] {s t : Finset α}, s.mulEnergy t = 0 ↔ s = ∅ ∨ t = ∅
· 使用定理 `or_self_iff`：∀ {a : Prop}, a ∨ a ↔ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[to_additive] lemma mulEnergy_self_eq_zero_iff : Eₘ[s] = 0 ↔ s = ∅ := by
  rw [mulEnergy_eq_zero_iff, or_self_iff]
/-
**Finset.mulEnergy_eq_card_filter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : Mul α] (s t : Finset α),
   s.mulEnergy t = {x ∈ (s ×ˢ t) ×ˢ s ×ˢ t | x.1.1 * x.1.2 = x.2.1 * x.2.2}.card
参数：s t : Finset α；s ×ˢ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.card_equiv`：card_equiv (e : α ≃ β) (hst : forall i, i in s ↔ e i 
in t) : #s = #t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.prodProdProdComm_apply`：∀ (α : Type u_9) (β : Type u_10) (γ : Type
 u_11) (δ : Type u_12) (abcd : (α × β) × γ × δ),   (Equiv.prodProdProdComm α β γ
 δ) abcd = ((abcd.…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[to_additive] lemma mulEnergy_eq_card_filter (s t : Finset α) :
    Eₘ[s, t] = #{x ∈ ((s ×ˢ t) ×ˢ s ×ˢ t) | x.1.1 * x.1.2 = x.2.1 * x.2.2} :=
  card_equiv (.prodProdProdComm _ _ _ _) (by simp [and_and_and_comm])

set_option backward.isDefEq.respectTransparency false in
/-
**Finset.mulEnergy_eq_sum_sq'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : Mul α] (s t : Finset α),
   s.mulEnergy t = ∑ a ∈ s * t, {xy ∈ s ×ˢ t | xy.1 * xy.2 = a}.card ^ 2
参数：s t : Finset α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mulEnergy_eq_card_filter`：∀ {α : Type u_1} [inst : DecidableEq α]
 [inst_1 : Mul α] (s t : Finset α),   s.mulEnergy t = {x ∈ (s ×ˢ t) ×ˢ s ×ˢ t | 
x.1.1 * x.1.2 = x.2.1…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.coe_mul`：coe_mul (s t : Finset α) : (↑(s * t) : Set α) = ↑s * ↑t
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_disjiUnion`：card_disjiUnion (s : Finset ι) (t : ι -> Finset 
M) (h) : #(s.disjiUnion t h) = ∑ a in s, #(t a)
· 使用引理 `Finset.disjiUnion_eq_biUnion`：disjiUnion_eq_biUnion (s : Finset α) (f : 
α -> Finset β) (hf) : s.disjiUnion f hf = s.biUnion f
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Finset.mul_mem_mul`：mul_mem_mul : a in s -> b in t -> a * b in s * t
-/
@[to_additive] lemma mulEnergy_eq_sum_sq' (s t : Finset α) :
    Eₘ[s, t] = ∑ a ∈ s * t, #{xy ∈ s ×ˢ t | xy.1 * xy.2 = a} ^ 2 := by
  simp_rw [mulEnergy_eq_card_filter, sq, ← card_product]
  rw [← card_disjiUnion]
  swap
  · aesop (add simp [Set.PairwiseDisjoint, Set.Pairwise, disjoint_left])
  · congr
    aesop (add unsafe mul_mem_mul)
/-
**Finset.mulEnergy_eq_sum_sq** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : Mul α] [inst_2 : Fintype
 α] (s t : Finset α),   s.mulEnergy t = ∑ a, {xy ∈ s ×ˢ t | xy.1 * xy.2 = a}.car
d ^ 2
参数：s t : Finset α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mulEnergy_eq_sum_sq'`：∀ {α : Type u_1} [inst : DecidableEq α] [in
st_1 : Mul α] (s t : Finset α),   s.mulEnergy t = ∑ a ∈ s * t, {xy ∈ s ×ˢ t | xy
.1 * xy.2 = a}.ca…
· 使用定理 `Fintype.sum_subset`：∀ {M : Type u_4} {ι : Type u_7} [inst : Fintype ι] [
inst_1 : AddCommMonoid M] {s : Finset ι} {f : ι → M},   (∀ (i : ι), f i ≠ 0 → i 
∈ s) → ∑…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
@[to_additive] lemma mulEnergy_eq_sum_sq [Fintype α] (s t : Finset α) :
    Eₘ[s, t] = ∑ a, #{xy ∈ s ×ˢ t | xy.1 * xy.2 = a} ^ 2 := by
  rw [mulEnergy_eq_sum_sq']
  exact Fintype.sum_subset <| by aesop (add simp [filter_eq_empty_iff, mul_mem_mul])

@[to_additive card_sq_le_card_mul_addEnergy]
/-
**Finset.card_sq_le_card_mul_mulEnergy** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：card_sq_le_card_mul_mulEnergy (s t u : Finset α) : #{xy in s ×ˢ t | xy.1 *
 xy.2 in u} ^ 2 <= #u * Eₘ[s, t]
参数：s t u : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.sum_card_fiberwise_eq_card_filter`：sum_card_fiberwise_eq_card_fil
ter {κ : Type*} [DecidableEq κ] (s : Finset ι) (t : Finset κ) (g : ι -> κ) : ∑ j
 in t, #{i in s | g i = j} = #…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `Finset.sum_mul_sq_le_sq_mul_sq`：sum_mul_sq_le_sq_mul_sq [CommSemiring R]
 [LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R] (s : Finset ι) (f g :
 ι -> R) : (∑ i in s…
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `mul_le_mul_right`：mul_le_mul_right [MulLeftMono α] {b c : α} (bc : b <= 
c) (a : α) : a * b <= a * c
· 使用定理 `Finset.sum_le_sum_of_ne_zero`：∀ {ι : Type u_1} {M : Type u_4} [inst : Ad
dCommMonoid M] [inst_1 : Preorder M] [CanonicallyOrderedAdd M] {f : ι → M}   {s 
t : Finset ι}, (∀ …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.mul_mem_mul`：mul_mem_mul : a in s -> b in t -> a * b in s * t
· 使用定理 `Finset.mulEnergy_eq_sum_sq'`：∀ {α : Type u_1} [inst : DecidableEq α] [in
st_1 : Mul α] (s t : Finset α),   s.mulEnergy t = ∑ a ∈ s * t, {xy ∈ s ×ˢ t | xy
.1 * xy.2 = a}.ca…
-/
lemma card_sq_le_card_mul_mulEnergy (s t u : Finset α) :
    #{xy ∈ s ×ˢ t | xy.1 * xy.2 ∈ u} ^ 2 ≤ #u * Eₘ[s, t] := by
  calc
    _ = (∑ c ∈ u, #{xy ∈ s ×ˢ t | xy.1 * xy.2 = c}) ^ 2 := by
        rw [← sum_card_fiberwise_eq_card_filter]
    _ ≤ #u * ∑ c ∈ u, #{xy ∈ s ×ˢ t | xy.1 * xy.2 = c} ^ 2 := by
        simpa using sum_mul_sq_le_sq_mul_sq (R := ℕ) _ 1 _
    _ ≤ #u * ∑ c ∈ s * t, #{xy ∈ s ×ˢ t | xy.1 * xy.2 = c} ^ 2 := by
        refine mul_le_mul_right (sum_le_sum_of_ne_zero ?_) _
        aesop (add simp [filter_eq_empty_iff]) (add unsafe mul_mem_mul)
    _ = #u * Eₘ[s, t] := by rw [mulEnergy_eq_sum_sq']
/-
**Finset.le_card_mul_mul_mulEnergy** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : Mul α] (s t : Finset α),
   s.card ^ 2 * t.card ^ 2 ≤ (s * t).card * s.mulEnergy t
参数：s t : Finset α；s * t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.filter_eq_self`：∀ {α : Type u_1} {p : α → Prop} [inst : Decidable
Pred p] {s : Finset α}, Finset.filter p s = s ↔ ∀ x ∈ s, p x
· 使用定理 `Finset.mul_mem_mul`：mul_mem_mul : a in s -> b in t -> a * b in s * t
· 使用定理 `Finset.card_product`：card_product (s : Finset α) (t : Finset β) : card (
s ×ˢ t) = card s * card t
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用引理 `Finset.card_sq_le_card_mul_mulEnergy`：card_sq_le_card_mul_mulEnergy (s t
 u : Finset α) : #{xy in s ×ˢ t | xy.1 * xy.2 in u} ^ 2 <= #u * Eₘ[s, t]
-/
@[to_additive le_card_add_mul_addEnergy] lemma le_card_mul_mul_mulEnergy (s t : Finset α) :
    #s ^ 2 * #t ^ 2 ≤ #(s * t) * Eₘ[s, t] :=
  calc
    _ = #{xy ∈ s ×ˢ t | xy.1 * xy.2 ∈ s * t} ^ 2 := by
      rw [filter_eq_self.2, card_product, mul_pow]; aesop (add unsafe mul_mem_mul)
    _ ≤ #(s * t) * Eₘ[s, t] := card_sq_le_card_mul_mulEnergy _ _ _

end Mul

open scoped Combinatorics.Additive

section CommMonoid

variable [CommMonoid α]

/-
**Finset.mulEnergy_comm** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : CommMonoid α] (s t : Fin
set α), s.mulEnergy t = t.mulEnergy s
参数：s t : Finset α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mulEnergy.eq_1`：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 :
 Mul α] (s t : Finset α),   s.mulEnergy t = {x ∈ (s ×ˢ s) ×ˢ t ×ˢ t | x.1.1 * x.
2.1 = x.1.2…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Finset.map_filter`：map_filter {f : α ≃ β} {p : α -> Prop} [DecidablePred
 p] : (s.filter p).map f.toEmbedding = (s.map f.toEmbedding).filter (p ∘ f.symm)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.filter.congr_simp`：∀ {α : Type u_1} (p p_1 : α → Prop),   p = p_1
 →     ∀ {inst : DecidablePred p} [inst_1 : DecidablePred p_1] (s s_1 : Finset α
),       s = s…
· 使用定理 `Finset.map_eq_image`：map_eq_image (f : α ↪ β) (s : Finset α) : s.map f =
 s.image f
· 使用定理 `Finset.image_swap_product`：image_swap_product [DecidableEq (α × β)] (s :
 Finset α) (t : Finset β) : (t ×ˢ s).image Prod.swap = s ×ˢ t
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[to_additive] lemma mulEnergy_comm (s t : Finset α) : Eₘ[s, t] = Eₘ[t, s] := by
  rw [mulEnergy, ← Finset.card_map (Equiv.prodComm _ _).toEmbedding, map_filter]
  simp [mulEnergy, mul_comm, map_eq_image]

end CommMonoid

section CommGroup

variable [CommGroup α] [Fintype α] (s t : Finset α)

@[to_additive (attr := simp)]
/-
**Finset.mulEnergy_univ_left** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：mulEnergy_univ_left : Eₘ[univ, t] = Fintype.card α * t.card ^ 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_right_cancel`：mul_right_cancel : a * b = c * b -> a = c
· 使用定理 `RightCancelSemigroup.toIsRightCancelMul`：∀ {G : Type u} [self : RightCan
celSemigroup G], IsRightCancelMul G
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_image_of_injOn`：card_image_of_injOn [DecidableEq β] (H : Set
.InjOn f s) : #(s.image f) = #s
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Prod.mk.eta`：∀ {α : Type u_1} {β : Type u_2} {p : α × β}, (p.1, p.2) = p
· 使用定理 `mul_right_comm`：mul_right_comm (a b c : G) : a * b * c = a * c * b
· 使用定理 `mul_inv_cancel_right`：mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
lemma mulEnergy_univ_left : Eₘ[univ, t] = Fintype.card α * t.card ^ 2 := by
  simp only [mulEnergy, univ_product_univ, Fintype.card, sq, ← card_product]
  let f : α × α × α → (α × α) × α × α := fun x => ((x.1 * x.2.2, x.1 * x.2.1), x.2)
  have : (↑((univ : Finset α) ×ˢ t ×ˢ t) : Set (α × α × α)).InjOn f := by
    rintro ⟨a₁, b₁, c₁⟩ _ ⟨a₂, b₂, c₂⟩ h₂ h
    simp_rw [f, Prod.ext_iff] at h
    obtain ⟨h, rfl, rfl⟩ := h
    rw [mul_right_cancel h.1]
  rw [← card_image_of_injOn this]
  congr with a
  simp only [mem_filter, mem_product, mem_univ, true_and, mem_image,
    Prod.exists]
  refine ⟨fun h => ⟨a.1.1 * a.2.2⁻¹, _, _, h.1, by simp [f, mul_right_comm, h.2]⟩, ?_⟩
  rintro ⟨b, c, d, hcd, rfl⟩
  simpa [f, mul_right_comm]

@[to_additive (attr := simp)]
/-
**Finset.mulEnergy_univ_right** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：mulEnergy_univ_right : Eₘ[s, univ] = Fintype.card α * s.card ^ 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mulEnergy_comm`：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 :
 CommMonoid α] (s t : Finset α), s.mulEnergy t = t.mulEnergy s
· 使用引理 `Finset.mulEnergy_univ_left`：mulEnergy_univ_left : Eₘ[univ, t] = Fintype.
card α * t.card ^ 2
-/
lemma mulEnergy_univ_right : Eₘ[s, univ] = Fintype.card α * s.card ^ 2 := by
  rw [mulEnergy_comm, mulEnergy_univ_left]

end CommGroup

end Finset

