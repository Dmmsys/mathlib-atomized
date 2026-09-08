/-
Copyright (c) 2021 Vladimir Goryachev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Goryachev
-/
module

public import Mathlib.Data.Nat.Count
public import Mathlib.Data.Set.Card

/-!
# Counting on ℕ

This file provides lemmas about the relation of `Nat.count` with cardinality functions.
-/

public section


namespace Nat
open Nat Count

variable {p : ℕ → Prop} [DecidablePred p] (n : ℕ)

/-
**Nat.count_le_cardinal** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：count_le_cardinal : (count p n : Cardinal) <= Cardinal.mk { k | p k }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.count_eq_card_fintype`：count_eq_card_fintype (n : Nat) : count p n =
 Fintype.card { k : Nat // k < n ∧ p k }
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `Cardinal.mk_subtype_mono`：mk_subtype_mono {p q : α -> Prop} (h : forall 
x, p x -> q x) : #{ x // p x } <= #{ x // q x }
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem count_le_cardinal : (count p n : Cardinal) ≤ Cardinal.mk { k | p k } := by
  rw [count_eq_card_fintype, ← Cardinal.mk_fintype]
  exact Cardinal.mk_subtype_mono fun x hx ↦ hx.2
/-
**Nat.count_le_setENCard** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：count_le_setENCard : count p n <= Set.encard { k | p k }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.count_le_cardinal`：count_le_cardinal : (count p n : Cardinal) <= Car
dinal.mk { k | p k }
-/
theorem count_le_setENCard : count p n ≤ Set.encard { k | p k } := by
  simp only [Set.encard, ENat.card, Set.coe_ofPred, Cardinal.natCast_le_toENat]
  exact Nat.count_le_cardinal n
/-
**Nat.count_le_setNCard** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：count_le_setNCard (h : { k | p k }.Finite) : count p n <= Set.ncard { k | 
p k }
参数：h : { k | p k }.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ncard_def`：ncard_def (s : Set α) : s.ncard = ENat.toNat s.encard
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ENat.natCast_le_natCast`：natCast_le_natCast {n m : Nat} : (n : Nat∞) <= 
(m : Nat∞) ↔ n <= m
· 使用定理 `ENat.natCast_toNat`：∀ {n : ℕ∞}, n ≠ ⊤ → ↑n.toNat = n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.count_le_setENCard`：count_le_setENCard : count p n <= Set.encard { k
 | p k }
-/
theorem count_le_setNCard (h : { k | p k }.Finite) : count p n ≤ Set.ncard { k | p k } := by
  rw [Set.ncard_def, ← ENat.natCast_le_natCast, ENat.natCast_toNat (by simpa)]
  exact count_le_setENCard n

end Nat

