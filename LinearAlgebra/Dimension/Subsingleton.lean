/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kim Morrison, Eric Wieser, Junyan Xu, Andrew Yang
-/
module

public import Mathlib.LinearAlgebra.Dimension.Basic

/-!
# Dimension of trivial modules
-/

public section

variable (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M]

section

variable [Nontrivial R]

/-- See `rank_subsingleton` that assumes `Subsingleton R` instead. -/
/-
**rank_subsingleton'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (R : Type u_1) (M : Type u_2) [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M]   [Nontrivial R] [Subsingleton M], Module.rank
 R M = 0
参数：R : Type u_1；M : Type u_2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.rank_def`：∀ (R : Type u_1) (M : Type u_2) [inst : Semiring R] [in
st_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   Module.rank R M = ⨆ ι, C
ardin…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `bot_eq_zero`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero α] 
[IsBotZeroClass α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `ciSup_le`：ciSup_le [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, f x 
<= c) : iSup f <= c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.mk_eq_zero`：mk_eq_zero (α : Type u) [IsEmpty α] : #α = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `linearIndependent_subsingleton_iff`：linearIndependent_subsingleton_iff [
Nontrivial R] [Subsingleton M] (f : ι -> M) : LinearIndependent R f ↔ IsEmpty ι
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0

--- 原说明 ---
See `rank_subsingleton` that assumes `Subsingleton R` instead.
-/
@[simp, nontriviality] theorem rank_subsingleton' [Subsingleton M] : Module.rank R M = 0 := by
  rw [Module.rank, ← bot_eq_zero, eq_bot_iff]
  exact ciSup_le fun s ↦ by simp [(linearIndependent_subsingleton_iff _).mp s.2]
/-
**rank_punit** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_punit : Module.rank R PUnit = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `rank_subsingleton'`：∀ (R : Type u_1) (M : Type u_2) [inst : Semiring R] 
[inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Nontrivial R] [Subsin
gleton M…
· 使用定理 `instSubsingletonPUnit`：Subsingleton PUnit.{u_1}
-/
theorem rank_punit : Module.rank R PUnit = 0 := rank_subsingleton' _ _
/-
**rank_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_bot : Module.rank R (⊥ : Submodule R M) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `rank_subsingleton'`：∀ (R : Type u_1) (M : Type u_2) [inst : Semiring R] 
[inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Nontrivial R] [Subsin
gleton M…
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem rank_bot : Module.rank R (⊥ : Submodule R M) = 0 := rank_subsingleton' _ _

end

