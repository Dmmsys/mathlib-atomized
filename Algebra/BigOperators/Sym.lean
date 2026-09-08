/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Data.Finset.Sym
public import Mathlib.Data.Sym.Sym2.Order
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Lemmas on `Finset.sum` and `Finset.prod` involving `Finset.sym2` or `Finset.sym`.
-/

public section

namespace Finset

open Multiset

/-
**Finset.sum_sym2_filter_not_isDiag** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sum_sym2_filter_not_isDiag {ι M} [LinearOrder ι] [AddCommMonoid M] (s : Fi
nset ι) (p : Sym2 ι -> M) : ∑ i in s.sym2 with ¬ i.IsDiag, p i = ∑ i in s.offDia
g with i.1 < i.2, p s(i.1, i.2)
参数：s : Finset ι；p : Sym2 ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.offDiag_filter_lt_eq_filter_le`：offDiag_filter_lt_eq_filter_le {ι
} [PartialOrder ι] [DecidableLE ι] [DecidableLT ι] (s : Finset ι) : s.offDiag.fi
lter (fun i => i.1 < i.2) =…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_subtype_eq_sum_filter`：∀ {ι : Type u_1} {M : Type u_4} {s : F
inset ι} [inst : AddCommMonoid M] (f : ι → M) {p : ι → Prop}   [inst_1 : Decidab
lePred p], ∑ x ∈ Finse…
· 使用定理 `Finset.sum_equiv`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst :
 AddCommMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M}   {g : κ → M} (e : ι
 ≃ κ),…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Sym2.sortEquiv_symm_apply`：∀ {α : Type u_1} [inst : LinearOrder α] (p : 
{ p // p.1 ≤ p.2 }), Sym2.sortEquiv.symm p = s((↑p).1, (↑p).2)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sum_sym2_filter_not_isDiag {ι M} [LinearOrder ι] [AddCommMonoid M]
    (s : Finset ι) (p : Sym2 ι → M) :
    ∑ i ∈ s.sym2 with ¬ i.IsDiag, p i = ∑ i ∈ s.offDiag with i.1 < i.2, p s(i.1, i.2) := by
  rw [Finset.offDiag_filter_lt_eq_filter_le]
  conv_rhs => rw [← Finset.sum_subtype_eq_sum_filter]
  refine (Finset.sum_equiv Sym2.sortEquiv.symm ?_ ?_).symm
  all_goals aesop
/-
**Finset.sum_count_of_mem_sym** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sum_count_of_mem_sym {α} [DecidableEq α] {m : Nat} {k : Sym α m} {s : Fins
et α} (hk : k in s.sym m) : (∑ i in s, count i k) = m
参数：hk : k in s.sym m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.sum_count_eq_card`：∀ {ι : Type u_1} [inst : DecidableEq ι] {s :
 Finset ι} {m : Multiset ι},   (∀ a ∈ m, a ∈ s) → ∑ a ∈ s, Multiset.count a m = 
m.card
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Sym.card_coe`：card_coe : Multiset.card (s : Multiset α) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sum_count_of_mem_sym {α} [DecidableEq α] {m : ℕ} {k : Sym α m} {s : Finset α}
    (hk : k ∈ s.sym m) : (∑ i ∈ s, count i k) = m := by
  simp_all

end Finset

