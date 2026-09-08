/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Lattice.Prod
public import Mathlib.Data.Finset.Pi

/-!
# Lattice operations on finsets of functions

This file is concerned with folding binary lattice operations over finsets.
-/

public section

assert_not_exists IsOrderedMonoid MonoidWithZero

variable {α ι : Type*}

namespace Finset

variable [DistribLattice α] [BoundedOrder α] [DecidableEq ι]

--TODO: Extract out the obvious isomorphism `(insert i s).pi t ≃ t i ×ˢ s.pi t` from this proof
/-
**Finset.inf_sup** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inf_sup {κ : ι -> Type*} (s : Finset ι) (t : forall i, Finset (κ i)) (f : 
forall i, κ i -> α) : (s.inf fun i => (t i).sup (f i)) = (s.pi t).sup fun g => s
.attach.inf fun i => f _ g _ i.2
参数：s : Finset ι；t : forall i, Finset (κ i)；f : forall i, κ i -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.inf_empty`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeInf
 α] [inst_1 : OrderTop α] {f : β → α}, ∅.inf f = ⊤
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.inf_eq_top_of_isEmpty`：∀ {α : Type u_2} {β : Type u_3} [inst : Se
milatticeInf α] [inst_1 : OrderTop α] [IsEmpty β] (f : β → α) (S : Finset β),   
S.inf f = ⊤
· 使用定理 `Finset.sup_singleton`：sup_singleton {b : β} : ({b} : Finset β).sup f = f
 b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.inf_insert`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeIn
f α] [inst_1 : OrderTop α] {s : Finset β} {f : β → α}   [inst_2 : DecidableEq β]
 {b : β…
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
· 使用定理 `Finset.attach_insert`：attach_insert [DecidableEq α] (s : Finset α) (a : 
α) : attach (insert a s) = insert (⟨a, mem_insert_self a s⟩ : { x // x in insert
 a s }) ((…
· 使用定理 `Finset.sup_inf_sup`：sup_inf_sup (s : Finset ι) (t : Finset κ) (f : ι -> 
α) (g : κ -> α) : s.sup f ⊓ t.sup g = (s ×ˢ t).sup fun i => f i.1 ⊓ g i.2
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.inf_image`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [inst :
 SemilatticeInf α] [inst_1 : OrderTop α] [inst_2 : DecidableEq β]   (s : Finset 
γ) (f …
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.mem_of_mem_insert_of_ne`：mem_of_mem_insert_of_ne (h : b in insert
 a s) : b != a -> b in s
· 使用定理 `Finset.mem_insert`：mem_insert : a in insert b s ↔ a = b ∨ a in s
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
（共 34 条，此处仅展示前 30 条）
-/
theorem inf_sup {κ : ι → Type*} (s : Finset ι) (t : ∀ i, Finset (κ i)) (f : ∀ i, κ i → α) :
    (s.inf fun i => (t i).sup (f i)) =
      (s.pi t).sup fun g => s.attach.inf fun i => f _ <| g _ i.2 := by
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih => ?_
  rw [inf_insert, ih, attach_insert, sup_inf_sup]
  refine eq_of_forall_ge_iff fun c => ?_
  simp only [Finset.sup_le_iff, mem_product, mem_pi, and_imp, Prod.forall,
    inf_insert, inf_image]
  refine
    ⟨fun h g hg =>
      h (g i <| mem_insert_self _ _) (fun j hj => g j <| mem_insert_of_mem hj)
        (hg _ <| mem_insert_self _ _) fun j hj => hg _ <| mem_insert_of_mem hj,
      fun h a g ha hg => ?_⟩
  -- TODO: This `have` must be named to prevent it being shadowed by the internal `this` in `simpa`
  have aux : ∀ j : { x // x ∈ s }, ↑j ≠ i := fun j : s => ne_of_mem_of_not_mem j.2 hi
  -- `simpa` doesn't support placeholders in proof terms
  have := h (fun j hj => if hji : j = i then cast (congr_arg κ hji.symm) a
      else g _ <| mem_of_mem_insert_of_ne hj hji) (fun j hj => ?_)
  · simpa only [cast_eq, dif_pos, Function.comp_def, Subtype.coe_mk, dif_neg, aux] using! this
  rw [mem_insert] at hj
  obtain (rfl | hj) := hj
  · simpa
  · simpa [ne_of_mem_of_not_mem hj hi] using! hg _ _
/-
**Finset.sup_inf** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sup_inf {κ : ι -> Type*} (s : Finset ι) (t : forall i, Finset (κ i)) (f : 
forall i, κ i -> α) : (s.sup fun i => (t i).inf (f i)) = (s.pi t).inf fun g => s
.attach.sup fun i => f _ g _ i.2
参数：s : Finset ι；t : forall i, Finset (κ i)；f : forall i, κ i -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.inf_sup`：inf_sup {κ : ι -> Type*} (s : Finset ι) (t : forall i, F
inset (κ i)) (f : forall i, κ i -> α) : (s.inf fun i => (t i).sup (f i)) = (s.pi
 t).…
-/
theorem sup_inf {κ : ι → Type*} (s : Finset ι) (t : ∀ i, Finset (κ i)) (f : ∀ i, κ i → α) :
    (s.sup fun i => (t i).inf (f i)) = (s.pi t).inf fun g => s.attach.sup fun i => f _ <| g _ i.2 :=
  @inf_sup αᵒᵈ _ _ _ _ _ _ _ _

end Finset

