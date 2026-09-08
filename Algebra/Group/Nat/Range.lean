/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.Embedding
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Data.Finset.Image

/-!
# `Finset.range` and addition of natural numbers
-/

public section
assert_not_exists MonoidWithZero MulAction IsOrderedMonoid

variable {α β γ : Type*}

namespace Finset

/-
**Finset.disjoint_range_addLeftEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：disjoint_range_addLeftEmbedding (a : Nat) (s : Finset Nat) : Disjoint (ran
ge a) (map (addLeftEmbedding a) s)
参数：a : Nat；s : Finset Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `addLeftEmbedding_apply`：∀ {G : Type u_1} [inst : Add G] [inst_1 : IsLeft
CancelAdd G] (g h : G), (addLeftEmbedding g) h = g + h
-/
theorem disjoint_range_addLeftEmbedding (a : ℕ) (s : Finset ℕ) :
    Disjoint (range a) (map (addLeftEmbedding a) s) := by
  simp_rw [disjoint_left, mem_map, mem_range, addLeftEmbedding_apply]
  rintro _ h ⟨l, -, rfl⟩
  lia
/-
**Finset.disjoint_range_addRightEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：disjoint_range_addRightEmbedding (a : Nat) (s : Finset Nat) : Disjoint (ra
nge a) (map (addRightEmbedding a) s)
参数：a : Nat；s : Finset Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `IsCancelAdd.toIsLeftCancelAdd`：∀ {G : Type u} {inst : Add G} [self : IsC
ancelAdd G], IsLeftCancelAdd G
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsCancelAdd.toIsRightCancelAdd`：∀ {G : Type u} {inst : Add G} [self : Is
CancelAdd G], IsRightCancelAdd G
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `addLeftEmbedding_eq_addRightEmbedding`：∀ {G : Type u_1} [inst : AddCommM
agma G] [inst_1 : IsCancelAdd G] (g : G), addLeftEmbedding g = addRightEmbedding
 g
· 使用定理 `Finset.disjoint_range_addLeftEmbedding`：disjoint_range_addLeftEmbedding 
(a : Nat) (s : Finset Nat) : Disjoint (range a) (map (addLeftEmbedding a) s)
-/
theorem disjoint_range_addRightEmbedding (a : ℕ) (s : Finset ℕ) :
    Disjoint (range a) (map (addRightEmbedding a) s) := by
  rw [← addLeftEmbedding_eq_addRightEmbedding]
  apply disjoint_range_addLeftEmbedding
/-
**Finset.range_add** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：range_add (a b : Nat) : range (a + b) = range a union (range b).map (addLe
ftEmbedding a)
参数：a b : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.val_inj`：val_inj {s t : Finset α} : s.1 = t.1 ↔ s = t
· 使用定理 `Finset.union_val`：union_val (s t : Finset α) : (s union t).1 = s.1 union
 t.1
· 使用定理 `Multiset.range_add_eq_union`：range_add_eq_union (a b : Nat) : range (a +
 b) = range a union (range b).map (a + ·)
-/
theorem range_add (a b : ℕ) : range (a + b) = range a ∪ (range b).map (addLeftEmbedding a) := by
  rw [← val_inj, union_val]
  exact Multiset.range_add_eq_union a b

end Finset

