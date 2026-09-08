/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Union

/-!
# Relating `Finset.biUnion` with lattice operations

This file shows `Finset.biUnion` could alternatively be defined in terms of `Finset.sup`.

## TODO

Remove `Finset.biUnion` in favour of `Finset.sup`.
-/

public section

open Function Multiset OrderDual

variable {F α β γ ι κ : Type*}
variable {s s₁ s₂ : Finset β} {f g : β → α} {a : α}

namespace Finset

section Sup

variable [SemilatticeSup α] [OrderBot α]

@[simp, grind =]
/-
**Finset.sup_biUnion** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sup_biUnion [DecidableEq β] (s : Finset γ) (t : γ -> Finset β) : (s.biUnio
n t).sup f = s.sup fun x => (t x).sup f
参数：s : Finset γ；t : γ -> Finset β。
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
-/
theorem sup_biUnion [DecidableEq β] (s : Finset γ) (t : γ → Finset β) :
    (s.biUnion t).sup f = s.sup fun x => (t x).sup f :=
  eq_of_forall_ge_iff fun c => by simp [@forall_comm _ β]

end Sup

section Inf

variable [SemilatticeInf α] [OrderTop α]

/-
**Finset.inf_biUnion** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} {f : β → α} [inst : Semilat
ticeInf α] [inst_1 : OrderTop α]   [inst_2 : DecidableEq β] (s : Finset γ) (t : 
γ → Finset β), (s.biUnion t).inf f = s.inf fun x => (t x).inf f
参数：s : Finset γ；t : γ → Finset β；s.biUnion t；t x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sup_biUnion`：sup_biUnion [DecidableEq β] (s : Finset γ) (t : γ ->
 Finset β) : (s.biUnion t).sup f = s.sup fun x => (t x).sup f
-/
@[simp, grind =] theorem inf_biUnion [DecidableEq β] (s : Finset γ) (t : γ → Finset β) :
    (s.biUnion t).inf f = s.inf fun x => (t x).inf f :=
  @sup_biUnion αᵒᵈ _ _ _ _ _ _ _ _

end Inf

section Sup'

variable [SemilatticeSup α]

variable {s : Finset β} (H : s.Nonempty) (f : β → α)

/-
**Finset.sup'_biUnion** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [inst : SemilatticeSup α] (
f : β → α) [inst_1 : DecidableEq β]   {s : Finset γ} (Hs : s.Nonempty) {t : γ → 
Finset β} (Ht : ∀ (b : γ), (t b).Nonempty),   (s.biUnion t).sup' ⋯ f = s.sup' Hs
 fun b => (t b).sup' ⋯ f
参数：f : β → α；Hs : s.Nonempty；Ht : ∀ (b : γ), (t b).Nonempty；s.biUnion t；t b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.Nonempty.biUnion`：∀ {α : Type u_1} {β : Type u_2} {s : Finset α} 
{t : α → Finset β} [inst : DecidableEq β],   s.Nonempty → (∀ x ∈ s, (t x).Nonemp
ty) → (s.biUn…
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
theorem sup'_biUnion [DecidableEq β] {s : Finset γ} (Hs : s.Nonempty) {t : γ → Finset β}
    (Ht : ∀ b, (t b).Nonempty) :
    (s.biUnion t).sup' (Hs.biUnion fun b _ => Ht b) f = s.sup' Hs (fun b => (t b).sup' (Ht b) f) :=
  eq_of_forall_ge_iff fun c => by simp [@forall_comm _ β]

end Sup'

section Inf'

variable [SemilatticeInf α]

variable {s : Finset β} (H : s.Nonempty) (f : β → α)

/-
**Finset.inf'_biUnion** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [inst : SemilatticeInf α] (
f : β → α) [inst_1 : DecidableEq β]   {s : Finset γ} (Hs : s.Nonempty) {t : γ → 
Finset β} (Ht : ∀ (b : γ), (t b).Nonempty),   (s.biUnion t).inf' ⋯ f = s.inf' Hs
 fun b => (t b).inf' ⋯ f
参数：f : β → α；Hs : s.Nonempty；Ht : ∀ (b : γ), (t b).Nonempty；s.biUnion t；t b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sup'_biUnion`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [ins
t : SemilatticeSup α] (f : β → α) [inst_1 : DecidableEq β]   {s : Finset γ} (Hs 
: s.Nonem…
-/
theorem inf'_biUnion [DecidableEq β] {s : Finset γ} (Hs : s.Nonempty) {t : γ → Finset β}
    (Ht : ∀ b, (t b).Nonempty) :
    (s.biUnion t).inf' (Hs.biUnion fun b _ => Ht b) f = s.inf' Hs (fun b => (t b).inf' (Ht b) f) :=
  sup'_biUnion (α := αᵒᵈ) _ Hs Ht

end Inf'

variable [DecidableEq α] {s : Finset ι} {f : ι → Finset α} {a : α}

/-
**Finset.sup_eq_biUnion** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sup_eq_biUnion {α β} [DecidableEq β] (s : Finset α) (t : α -> Finset β) : 
s.sup t = s.biUnion t
参数：s : Finset α；t : α -> Finset β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_sup`：∀ {α : Type u_2} {ι : Type u_5} [inst : DecidableEq α] {
s : Finset ι} {f : ι → Finset α} {a : α},   a ∈ s.sup f ↔ ∃ i ∈ s, a ∈ f i
· 使用定理 `Finset.mem_biUnion`：∀ {α : Type u_1} {β : Type u_2} {s : Finset α} {t : 
α → Finset β} [inst : DecidableEq β] {b : β},   b ∈ s.biUnion t ↔ ∃ a ∈ s, b ∈ t
 a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sup_eq_biUnion {α β} [DecidableEq β] (s : Finset α) (t : α → Finset β) :
    s.sup t = s.biUnion t := by
  ext
  rw [mem_sup, mem_biUnion]

end Finset

