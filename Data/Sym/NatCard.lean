/-
Copyright (c) 2026 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.Data.Sym.Basic
public import Mathlib.Data.Sym.Sym2

import Mathlib.Data.Sym.Card

/-!
# `Nat.card` versions of `Fintype.card` lemmas on `Sym`

Each of the lemmas assuming `[Fintype α]` and `Fintype.card` can be restated using `Nat.card` alone.
-/

public section

open Nat

variable (α : Type*)

namespace Sym

/-
**Sym.** 是 Mathlib 中的一个实例，位于命名空间 `Sym`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {k : ℕ} [Infinite α] [NeZero k] : Infinite (Sym α k) :=
  .of_injective (Sym.replicate k) <| Sym.replicate_right_injective (NeZero.ne _)

/-- A version of `card_sym_eq_multichoose` that does not need finiteness. -/
/-
**Sym.natCard_sym_eq_multichoose** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：natCard_sym_eq_multichoose (k : Nat) : Nat.card (Sym α k) = multichoose (N
at.card α) k
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finite_or_infinite`：finite_or_infinite (α : Sort*) : Finite α ∨ Infinite
 α
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Sym.card_sym_eq_multichoose`：card_sym_eq_multichoose (α : Type*) (k : Na
t) [Fintype α] [Fintype (Sym α k)] : card (Sym α k) = multichoose (card α) k
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Fintype.card_unique`：card_unique [Unique α] [h : Fintype α] : Fintype.ca
rd α = 1
· 使用定理 `Nat.card_eq_zero_of_infinite`：∀ {α : Type u_1} [Infinite α], Nat.card α 
= 0
· 使用定理 `Nat.multichoose_zero_right`：multichoose_zero_right (n : Nat) : multichoo
se n 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Sym.instInfiniteOfNeZeroNat`：∀ (α : Type u_1) {k : ℕ} [Infinite α] [NeZe
ro k], Infinite (Sym α k)
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.multichoose_zero_succ`：multichoose_zero_succ (k : Nat) : multichoose
 0 (k + 1) = 0

--- 原说明 ---
A version of `card_sym_eq_multichoose` that does not need finiteness.
-/
theorem natCard_sym_eq_multichoose (k : ℕ) :
    Nat.card (Sym α k) = multichoose (Nat.card α) k := by
  cases finite_or_infinite α
  · obtain ⟨_⟩ := nonempty_fintype α; let := Classical.decEq α
    simp_rw [Nat.card_eq_fintype_card]
    exact card_sym_eq_multichoose _ _
  cases k <;> simp

/-- A version of `card_sym_eq_choose` that does not need finiteness. -/
/-
**Sym.natCard_sym_eq_choose** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：natCard_sym_eq_choose (k : Nat) : Nat.card (Sym α k) = (Nat.card α + k - 1
).choose k
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Sym.natCard_sym_eq_multichoose`：natCard_sym_eq_multichoose (k : Nat) : N
at.card (Sym α k) = multichoose (Nat.card α) k
· 使用定理 `Nat.multichoose_eq`：multichoose_eq : forall n k : Nat, multichoose n k =
 (n + k - 1).choose k | _, 0 => by simp | 0, k + 1 => by simp | n + 1, k + 1 => 
by have …

--- 原说明 ---
A version of `card_sym_eq_choose` that does not need finiteness.
-/
theorem natCard_sym_eq_choose (k : ℕ) :
    Nat.card (Sym α k) = (Nat.card α + k - 1).choose k := by
  rw [natCard_sym_eq_multichoose, Nat.multichoose_eq]

end Sym

namespace Sym2

/-
**Sym2.** 是 Mathlib 中的一个实例，位于命名空间 `Sym2`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Infinite α] : Infinite (Sym2 α) :=
  .of_injective Sym2.diag <| Sym2.diag_injective
/-
**Sym2.** 是 Mathlib 中的一个实例，位于命名空间 `Sym2`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Infinite α] : Infinite {a : Sym2 α // a.IsDiag} :=
  .of_injective (fun a : α => ⟨.diag a, rfl⟩) fun _ _ h => Sym2.diag_injective congr($h)
/-
**Sym2.** 是 Mathlib 中的一个实例，位于命名空间 `Sym2`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Infinite α] : Infinite {a : Sym2 α // ¬a.IsDiag} :=
  let e := Infinite.natEmbedding α
  .of_injective (fun n => ⟨s(e 0, e (n + 1)), by simp⟩) fun _ _ => by simp
/-
**Sym2.natCard_subtype_diag** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：natCard_subtype_diag : Nat.card { a : Sym2 α // a.IsDiag } = Nat.card α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
-/
theorem natCard_subtype_diag : Nat.card { a : Sym2 α // a.IsDiag } = Nat.card α :=
  Nat.card_congr diagElemEquiv
/-
**Sym2.natCard_subtype_not_diag** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：natCard_subtype_not_diag : Nat.card { a : Sym2 α // ¬a.IsDiag } = (Nat.car
d α).choose 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finite_or_infinite`：finite_or_infinite (α : Sort*) : Finite α ∨ Infinite
 α
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Sym2.card_subtype_not_diag`：card_subtype_not_diag [Fintype α] : card { a
 : Sym2 α // ¬a.IsDiag } = (card α).choose 2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.card_eq_zero_of_infinite`：∀ {α : Type u_1} [Infinite α], Nat.card α 
= 0
· 使用定理 `Sym2.instInfiniteSubtypeNotIsDiag`：∀ (α : Type u_1) [Infinite α], Infini
te { a // ¬a.IsDiag }
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem natCard_subtype_not_diag :
    Nat.card { a : Sym2 α // ¬a.IsDiag } = (Nat.card α).choose 2 := by
  cases finite_or_infinite α
  · obtain ⟨_⟩ := nonempty_fintype α; let := Classical.decEq α
    simp_rw [Nat.card_eq_fintype_card]
    exact card_subtype_not_diag
  · simp
/-
**Sym2.ncard_diagSet** 是 Mathlib 中的一个引理，位于命名空间 `Sym2`。
形式化陈述：ncard_diagSet : (diagSet : Set (Sym2 α)).ncard = Nat.card α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.natCard_subtype_diag`：natCard_subtype_diag : Nat.card { a : Sym2 α 
// a.IsDiag } = Nat.card α
-/
lemma ncard_diagSet : (diagSet : Set (Sym2 α)).ncard = Nat.card α :=
  natCard_subtype_diag _
/-
**Sym2.ncard_diagSet_compl** 是 Mathlib 中的一个引理，位于命名空间 `Sym2`。
形式化陈述：ncard_diagSet_compl : (diagSetᶜ : Set (Sym2 α)).ncard = (Nat.card α).choos
e 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.natCard_subtype_not_diag`：natCard_subtype_not_diag : Nat.card { a :
 Sym2 α // ¬a.IsDiag } = (Nat.card α).choose 2
-/
lemma ncard_diagSet_compl : (diagSetᶜ : Set (Sym2 α)).ncard = (Nat.card α).choose 2 :=
  natCard_subtype_not_diag _

/-- Type **stars and bars** for the case `n = 2`. -/
/-
**Sym2.natCard** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：∀ (α : Type u_1), Nat.card (Sym2 α) = (Nat.card α + 1).choose 2
参数：α : Type u_1；Sym2 α；Nat.card α + 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finite_or_infinite`：finite_or_infinite (α : Sort*) : Finite α ∨ Infinite
 α
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Sym2.card`：∀ {α : Type u_2} [inst : Fintype α], Fintype.card (Sym2 α) = 
(Fintype.card α + 1).choose 2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.card_eq_zero_of_infinite`：∀ {α : Type u_1} [Infinite α], Nat.card α 
= 0
· 使用定理 `Sym2.instInfinite`：∀ (α : Type u_1) [Infinite α], Infinite (Sym2 α)
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.choose_succ_self`：choose_succ_self (n : Nat) : choose n (succ n) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Type **stars and bars** for the case `n = 2`.
-/
protected theorem natCard : Nat.card (Sym2 α) = Nat.choose (Nat.card α + 1) 2 := by
  cases finite_or_infinite α
  · obtain ⟨_⟩ := nonempty_fintype α; let := Classical.decEq α
    simp_rw [Nat.card_eq_fintype_card]
    exact Sym2.card
  · simp

end Sym2

