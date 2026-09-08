/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Data.Countable.Defs
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Logic.Equiv.Nat

/-!
# Countable types

In this file we provide basic instances of the `Countable` typeclass defined elsewhere.
-/

public section

assert_not_exists Monoid

universe u v w

open Function

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Countable ℤ :=
  Countable.of_equiv ℕ Equiv.intEquivNat.symm

/-!
### Definition in terms of `Function.Embedding`
-/

section Embedding

variable {α : Sort u} {β : Sort v}

/-
**countable_iff_nonempty_embedding** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：countable_iff_nonempty_embedding : Countable α ↔ Nonempty (α ↪ Nat)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Embedding.inj'`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ↪ β),
 Function.Injective self.toFun
-/
theorem countable_iff_nonempty_embedding : Countable α ↔ Nonempty (α ↪ ℕ) :=
  ⟨fun ⟨⟨f, hf⟩⟩ => ⟨⟨f, hf⟩⟩, fun ⟨f⟩ => ⟨⟨f, f.2⟩⟩⟩
/-
**uncountable_iff_isEmpty_embedding** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uncountable_iff_isEmpty_embedding : Uncountable α ↔ IsEmpty (α ↪ Nat)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `not_countable_iff`：not_countable_iff : ¬Countable α ↔ Uncountable α
· 使用定理 `countable_iff_nonempty_embedding`：countable_iff_nonempty_embedding : Cou
ntable α ↔ Nonempty (α ↪ Nat)
· 使用定理 `not_nonempty_iff`：not_nonempty_iff : ¬Nonempty α ↔ IsEmpty α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem uncountable_iff_isEmpty_embedding : Uncountable α ↔ IsEmpty (α ↪ ℕ) := by
  rw [← not_countable_iff, countable_iff_nonempty_embedding, not_nonempty_iff]
/-
**nonempty_embedding_nat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nonempty_embedding_nat (α) [Countable α] : Nonempty (α ↪ Nat)
参数：α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `countable_iff_nonempty_embedding`：countable_iff_nonempty_embedding : Cou
ntable α ↔ Nonempty (α ↪ Nat)
-/
theorem nonempty_embedding_nat (α) [Countable α] : Nonempty (α ↪ ℕ) :=
  countable_iff_nonempty_embedding.1 ‹_›
/-
**Function.Embedding.countable** 是 Mathlib 中的一个定理，位于命名空间 `Function.Embedding`。
形式化陈述：∀ {α : Sort u} {β : Sort v} [Countable β] (f : α ↪ β), Countable α
参数：f : α ↪ β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.countable`：∀ {α : Sort u} {β : Sort v} [Countable β] 
{f : α → β}, Function.Injective f → Countable α
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
-/
protected theorem Function.Embedding.countable [Countable β] (f : α ↪ β) : Countable α :=
  f.injective.countable
/-
**Function.Embedding.uncountable** 是 Mathlib 中的一个定理，位于命名空间 `Function.Embedding`。
形式化陈述：∀ {α : Sort u} {β : Sort v} [Uncountable α] (f : α ↪ β), Uncountable β
参数：f : α ↪ β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.uncountable`：∀ {α : Sort u} {β : Sort v} [Uncountable
 α] {f : α → β}, Function.Injective f → Uncountable β
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
-/
protected lemma Function.Embedding.uncountable [Uncountable α] (f : α ↪ β) : Uncountable β :=
  f.injective.uncountable

end Embedding

/-!
### Operations on `Type*`s
-/

section type

variable {α : Type u} {β : Type v} {π : α → Type w}

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Countable α] [Countable β] : Countable (α ⊕ β) := by
  rcases exists_injective_nat α with ⟨f, hf⟩
  rcases exists_injective_nat β with ⟨g, hg⟩
  exact (Equiv.natSumNatEquivNat.injective.comp <| hf.sumMap hg).countable
/-
**Sum.uncountable_inl** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Sum.uncountable_inl [Uncountable α] : Uncountable (α oplus β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.uncountable`：∀ {α : Sort u} {β : Sort v} [Uncountable
 α] {f : α → β}, Function.Injective f → Uncountable β
· 使用定理 `Sum.inl_injective`：inl_injective : Function.Injective (inl : α -> α oplu
s β)
-/
instance Sum.uncountable_inl [Uncountable α] : Uncountable (α ⊕ β) :=
  inl_injective.uncountable
/-
**Sum.uncountable_inr** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Sum.uncountable_inr [Uncountable β] : Uncountable (α oplus β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.uncountable`：∀ {α : Sort u} {β : Sort v} [Uncountable
 α] {f : α → β}, Function.Injective f → Uncountable β
· 使用定理 `Sum.inr_injective`：inr_injective : Function.Injective (inr : β -> α oplu
s β)
-/
instance Sum.uncountable_inr [Uncountable β] : Uncountable (α ⊕ β) :=
  inr_injective.uncountable
/-
**Option.instCountable** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Option.instCountable [Countable α] : Countable (Option α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Countable.of_equiv`：Countable.of_equiv (α : Sort*) [Countable α] (e : α 
≃ β) : Countable β
· 使用定理 `instCountableSum`：∀ {α : Type u} {β : Type v} [Countable α] [Countable β
], Countable (α ⊕ β)
· 使用定理 `instCountablePUnit`：Countable PUnit.{u}
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
instance Option.instCountable [Countable α] : Countable (Option α) :=
  Countable.of_equiv _ (Equiv.optionEquivSumPUnit.{0, _} α).symm
/-
**WithTop.instCountable** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：WithTop.instCountable [Countable α] : Countable (WithTop α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance WithTop.instCountable [Countable α] : Countable (WithTop α) := Option.instCountable
/-
**WithBot.instCountable** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：WithBot.instCountable [Countable α] : Countable (WithBot α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance WithBot.instCountable [Countable α] : Countable (WithBot α) := Option.instCountable
/-
**ENat.instCountable** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ENat.instCountable : Countable Nat∞
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `instCountableNat`：Countable ℕ
-/
instance ENat.instCountable : Countable ℕ∞ := Option.instCountable
/-
**Option.instUncountable** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Option.instUncountable [Uncountable α] : Uncountable (Option α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.uncountable`：∀ {α : Sort u} {β : Sort v} [Uncountable
 α] {f : α → β}, Function.Injective f → Uncountable β
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Option.some_inj`：∀ {α : Type u_1} {a b : α}, some a = some b ↔ a = b
-/
instance Option.instUncountable [Uncountable α] : Uncountable (Option α) :=
  Injective.uncountable fun _ _ ↦ Option.some_inj.1
/-
**WithTop.instUncountable** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：WithTop.instUncountable [Uncountable α] : Uncountable (WithTop α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance WithTop.instUncountable [Uncountable α] : Uncountable (WithTop α) := Option.instUncountable
/-
**WithBot.instUncountable** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：WithBot.instUncountable [Uncountable α] : Uncountable (WithBot α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance WithBot.instUncountable [Uncountable α] : Uncountable (WithBot α) := Option.instUncountable
/-
**untopD_coe_enat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (d n : ℕ), WithTop.untopD d ↑n = n
参数：d n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma untopD_coe_enat (d n : ℕ) : WithTop.untopD d (n : ℕ∞) = n := rfl
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Countable α] [Countable β] : Countable (α × β) := by
  rcases exists_injective_nat α with ⟨f, hf⟩
  rcases exists_injective_nat β with ⟨g, hg⟩
  exact (Nat.pairEquiv.injective.comp <| hf.prodMap hg).countable
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Uncountable α] [Nonempty β] : Uncountable (α × β) := by
  inhabit β
  exact (Prod.mk_left_injective default).uncountable
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nonempty α] [Uncountable β] : Uncountable (α × β) := by
  inhabit α
  exact (Prod.mk_right_injective default).uncountable
/-
**countable_left_of_prod_of_nonempty** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：countable_left_of_prod_of_nonempty [Nonempty β] (h : Countable (α × β)) : 
Countable α
参数：h : Countable (α × β)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instUncountableProdOfNonempty`：∀ {α : Type u} {β : Type v} [Uncountable 
α] [Nonempty β], Uncountable (α × β)
-/
lemma countable_left_of_prod_of_nonempty [Nonempty β] (h : Countable (α × β)) : Countable α := by
  contrapose! h
  infer_instance
/-
**countable_right_of_prod_of_nonempty** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：countable_right_of_prod_of_nonempty [Nonempty α] (h : Countable (α × β)) :
 Countable β
参数：h : Countable (α × β)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instUncountableProdOfNonempty_1`：∀ {α : Type u} {β : Type v} [Nonempty α
] [Uncountable β], Uncountable (α × β)
-/
lemma countable_right_of_prod_of_nonempty [Nonempty α] (h : Countable (α × β)) : Countable β := by
  contrapose! h
  infer_instance
/-
**countable_prod_swap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：countable_prod_swap [Countable (α × β)] : Countable (β × α)
参数：α × β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Countable.of_equiv`：Countable.of_equiv (α : Sort*) [Countable α] (e : α 
≃ β) : Countable β
-/
lemma countable_prod_swap [Countable (α × β)] : Countable (β × α) :=
  Countable.of_equiv _ (Equiv.prodComm α β)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Countable α] [∀ a, Countable (π a)] : Countable (Sigma π) := by
  rcases exists_injective_nat α with ⟨f, hf⟩
  choose g hg using fun a => exists_injective_nat (π a)
  exact ((Equiv.sigmaEquivProd ℕ ℕ).injective.comp <| hf.sigma_map hg).countable
/-
**Sigma.uncountable** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Sigma.uncountable (a : α) [Uncountable (π a)] : Uncountable (Sigma π)
参数：a : α；π a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.uncountable`：∀ {α : Sort u} {β : Sort v} [Uncountable
 α] {f : α → β}, Function.Injective f → Uncountable β
· 使用定理 `sigma_mk_injective`：∀ {α : Type u_1} {β : α → Type u_4} {i : α}, Functio
n.Injective (Sigma.mk i)
-/
lemma Sigma.uncountable (a : α) [Uncountable (π a)] : Uncountable (Sigma π) :=
  (sigma_mk_injective (i := a)).uncountable
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nonempty α] [∀ a, Uncountable (π a)] : Uncountable (Sigma π) := by
  inhabit α; exact Sigma.uncountable default
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 500) SetCoe.countable [Countable α] (s : Set α) : Countable s :=
  Subtype.countable

end type

section sort

variable {α : Sort u} {β : Sort v} {π : α → Sort w}

/-!
### Operations on `Sort*`s
-/

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Operations on `Sort*`s
-/
instance [Countable α] [Countable β] : Countable (α ⊕' β) :=
  Countable.of_equiv (PLift α ⊕ PLift β) (Equiv.plift.sumPSum Equiv.plift)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Countable α] [Countable β] : Countable (PProd α β) :=
  Countable.of_equiv (PLift α × PLift β) (Equiv.plift.prodPProd Equiv.plift)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Countable α] [∀ a, Countable (π a)] : Countable (PSigma π) :=
  Countable.of_equiv (Σ a : PLift α, PLift (π a.down)) (Equiv.psigmaEquivSigmaPLift π).symm
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Finite α] [∀ a, Countable (π a)] : Countable (∀ a, π a) := by
  have (n : ℕ) : Countable (Fin n → ℕ) := by
    induction n with
    | zero => infer_instance
    | succ n ihn => exact Countable.of_equiv (ℕ × (Fin n → ℕ)) (Fin.consEquiv fun _ ↦ ℕ)
  rcases Finite.exists_equiv_fin α with ⟨n, ⟨e⟩⟩
  have f := fun a => (nonempty_embedding_nat (π a)).some
  exact ((Embedding.piCongrRight f).trans (Equiv.piCongrLeft' _ e).toEmbedding).countable

end sort

