/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Lattice

/-!
# Bounded lattices

This file contains miscellaneous lemmas about lattices with top or bottom elements.

## Common lattices

* Distributive lattices with a bottom element. Notated by `[DistribLattice α] [OrderBot α]`.
  It captures the properties of `Disjoint` that are common to `GeneralizedBooleanAlgebra` and
  `DistribLattice` when `OrderBot`.
* Bounded and distributive lattice. Notated by `[DistribLattice α] [BoundedOrder α]`.
  Typical examples include `Prop` and `Set α`.
-/

public section

open Function OrderDual

variable {α β : Type*}

/-! ### Top, bottom element -/

section SemilatticeSupTop

variable [SemilatticeSup α] [OrderTop α]

/-
**top_sup_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderTop α] (a : α), 
⊤ ⊔ a = ⊤
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `le_top`：le_top : a <= ⊤
-/
@[to_dual] theorem top_sup_eq (a : α) : ⊤ ⊔ a = ⊤ := sup_of_le_left le_top
/-
**sup_top_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderTop α] (a : α), 
a ⊔ ⊤ = ⊤
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `le_top`：le_top : a <= ⊤
-/
@[to_dual] theorem sup_top_eq (a : α) : a ⊔ ⊤ = ⊤ := sup_of_le_right le_top

end SemilatticeSupTop

section SemilatticeSupBot

variable [SemilatticeSup α] [OrderBot α] {a b : α}

/-
**bot_sup_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderBot α] (a : α), 
⊥ ⊔ a = a
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
@[to_dual] theorem bot_sup_eq (a : α) : ⊥ ⊔ a = a := sup_of_le_right bot_le
/-
**sup_bot_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderBot α] (a : α), 
a ⊔ ⊥ = a
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
@[to_dual] theorem sup_bot_eq (a : α) : a ⊔ ⊥ = a := sup_of_le_left bot_le

@[to_dual (attr := simp, grind =)]
/-
**sup_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_eq_bot_iff : a ⊔ b = ⊥ ↔ a = ⊥ ∧ b = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `sup_le_iff`：sup_le_iff : a ⊔ b <= c ↔ a <= c ∧ b <= c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sup_eq_bot_iff : a ⊔ b = ⊥ ↔ a = ⊥ ∧ b = ⊥ := by rw [eq_bot_iff, sup_le_iff]; simp

end SemilatticeSupBot

section LinearOrder

variable [LinearOrder α] [OrderBot α]

-- `simp` can prove these, so they shouldn't be simp-lemmas.

/-
**min_bot_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1 : OrderBot α] (a : α), min
 ⊥ a = ⊥
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_inf_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderBo
t α] (a : α), ⊥ ⊓ a = ⊥
-/
@[to_dual] theorem min_bot_left (a : α) : min ⊥ a = ⊥ := bot_inf_eq _
/-
**min_bot_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1 : OrderBot α] (a : α), min
 a ⊥ = ⊥
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_bot_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderBo
t α] (a : α), a ⊓ ⊥ = ⊥
-/
@[to_dual] theorem min_bot_right (a : α) : min a ⊥ = ⊥ := inf_bot_eq _
/-
**max_bot_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1 : OrderBot α] (a : α), max
 ⊥ a = a
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_sup_eq`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderBo
t α] (a : α), ⊥ ⊔ a = a
-/
@[to_dual] theorem max_bot_left (a : α) : max ⊥ a = a := bot_sup_eq _
/-
**max_bot_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1 : OrderBot α] (a : α), max
 a ⊥ = a
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_bot_eq`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderBo
t α] (a : α), a ⊔ ⊥ = a
-/
@[to_dual] theorem max_bot_right (a : α) : max a ⊥ = a := sup_bot_eq _
/-
**max_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1 : OrderBot α] {a b : α}, m
ax a b = ⊥ ↔ a = ⊥ ∧ b = ⊥
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_eq_bot_iff`：sup_eq_bot_iff : a ⊔ b = ⊥ ↔ a = ⊥ ∧ b = ⊥
-/
@[to_dual] theorem max_eq_bot {a b : α} : max a b = ⊥ ↔ a = ⊥ ∧ b = ⊥ := sup_eq_bot_iff

@[to_dual (attr := simp)]
/-
**min_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：min_eq_bot {a b : α} : min a b = ⊥ ↔ a = ⊥ ∨ b = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem min_eq_bot {a b : α} : min a b = ⊥ ↔ a = ⊥ ∨ b = ⊥ := by
  simp_rw [← le_bot_iff, inf_le_iff]

@[to_dual (attr := aesop (rule_sets := [finiteness]) safe apply)]
/-
**min_ne_bot** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：min_ne_bot {a b : α} (ha : a != ⊥) (hb : b != ⊥) : min a b != ⊥
参数：ha : a != ⊥；hb : b != ⊥。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma min_ne_bot {a b : α} (ha : a ≠ ⊥) (hb : b ≠ ⊥) : min a b ≠ ⊥ := by
  grind

end LinearOrder

/-! ### Induction on `WellFoundedGT` and `WellFoundedLT` -/

section WellFounded

@[to_dual (attr := elab_as_elim)]
/-
**WellFoundedGT.induction_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WellFoundedGT.induction_top [Preorder α] [WellFoundedGT α] [OrderTop α] {P
 : α -> Prop} (hexists : exists M, P M) (hind : forall N != ⊤, P N -> exists M >
 N, P M) : P ⊤
参数：hexists : exists M, P M；hind : forall N != ⊤, P N -> exists M > N, P M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `WellFoundedGT.induction`：∀ {α : Type u} [inst : LT α] [WellFoundedGT α] 
{motive : α → Prop} (a : α),   (∀ (x : α), (∀ (y : α), x < y → motive y) → motiv
e x) → motive…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem WellFoundedGT.induction_top [Preorder α] [WellFoundedGT α] [OrderTop α]
    {P : α → Prop} (hexists : ∃ M, P M) (hind : ∀ N ≠ ⊤, P N → ∃ M > N, P M) : P ⊤ := by
  contrapose! hexists
  intro M
  induction M using WellFoundedGT.induction with
  | ind x IH =>
    by_cases hx : x = ⊤
    · exact hx ▸ hexists
    · intro hx'
      obtain ⟨M, hM, hM'⟩ := hind x hx hx'
      exact IH _ hM hM'

end WellFounded

