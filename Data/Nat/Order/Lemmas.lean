/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Data.Nat.Find
public import Mathlib.Data.Set.Basic
public import Mathlib.Tactic.ByContra

/-!
# Further lemmas about the natural numbers

The distinction between this file and `Mathlib/Algebra/Order/Ring/Nat.lean` is not particularly
clear. They were separated for now to minimize the porting requirements for tactics
during the transition to mathlib4. Please feel free to reorganize these two files.
-/

public section

assert_not_exists RelIso

namespace Nat

/-! ### Sets -/


/-
**Nat.Subtype.orderBot** 是 Mathlib 中的一个定义，位于命名空间 `Nat.Subtype`。
形式化陈述：(s : Set ℕ) → [DecidablePred fun x => x ∈ s] → [h : Nonempty ↑s] → OrderBo
t ↑s
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Sets
-/
instance Subtype.orderBot (s : Set ℕ) [DecidablePred (· ∈ s)] [h : Nonempty s] : OrderBot s where
  bot := ⟨Nat.find (nonempty_subtype.1 h), Nat.find_spec (nonempty_subtype.1 h)⟩
  bot_le x := Nat.find_min' _ x.2
/-
**Nat.Subtype.semilatticeSup** 是 Mathlib 中的一个定义，位于命名空间 `Nat.Subtype`。
形式化陈述：(p : ℕ → Prop) → SemilatticeSup (Subtype p)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Subtype.semilatticeSup (p : ℕ → Prop) : SemilatticeSup (Subtype p) :=
  { Subtype.instLinearOrder p, LinearOrder.toLattice with }
/-
**Nat.Subtype.coe_bot** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Subtype`。
形式化陈述：∀ {s : Set ℕ} [inst : DecidablePred fun x => x ∈ s] [h : Nonempty ↑s], ↑⊥ 
= Nat.find ⋯
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Subtype.coe_bot {s : Set ℕ} [DecidablePred (· ∈ s)] [h : Nonempty s] :
    ((⊥ : s) : ℕ) = Nat.find (nonempty_subtype.1 h) :=
  rfl
/-
**Nat.set_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：set_eq_univ {S : Set Nat} : S = Set.univ ↔ 0 in S ∧ forall k : Nat, k in S
 -> k + 1 in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.eq_univ_of_forall`：eq_univ_of_forall {s : Set α} : (forall x, x in s
) -> s = univ
· 使用引理 `Nat.set_induction`：set_induction {S : Set Nat} (hb : 0 in S) (h_ind : fo
rall k : Nat, k in S -> k + 1 in S) (n : Nat) : n in S
-/
theorem set_eq_univ {S : Set ℕ} : S = Set.univ ↔ 0 ∈ S ∧ ∀ k : ℕ, k ∈ S → k + 1 ∈ S :=
  ⟨by rintro rfl; simp, fun ⟨h0, hs⟩ => Set.eq_univ_of_forall (set_induction h0 hs)⟩
/-
**Nat.exists_not_and_succ_of_not_zero_of_exists** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：exists_not_and_succ_of_not_zero_of_exists {p : Nat -> Prop} (H' : ¬ p 0) (
H : exists n, p n) : exists n, ¬ p n ∧ p (n + 1)
参数：H' : ¬ p 0；H : exists n, p n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.le_zero_eq`：∀ (a : ℕ), (a ≤ 0) = (a = 0)
· 使用定理 `Nat.find_min`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n) {
m : ℕ}, m < Nat.find H → ¬p m
· 使用定理 `Nat.pred_lt`：∀ {n : ℕ}, n ≠ 0 → n.pred < n
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
-/
lemma exists_not_and_succ_of_not_zero_of_exists {p : ℕ → Prop} (H' : ¬ p 0) (H : ∃ n, p n) :
    ∃ n, ¬ p n ∧ p (n + 1) := by
  classical
  let k := Nat.find H
  have hk : p k := Nat.find_spec H
  suffices 0 < k from
    ⟨k - 1, Nat.find_min H <| Nat.pred_lt this.ne', by rwa [Nat.sub_add_cancel this]⟩
  by_contra! contra
  rw [le_zero_eq] at contra
  exact H' (contra ▸ hk)

end Nat

