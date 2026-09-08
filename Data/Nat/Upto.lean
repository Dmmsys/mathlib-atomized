/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
module

public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Sub.Basic

/-!
# `Nat.Upto`

`Nat.Upto p`, with `p` a predicate on `ℕ`, is a subtype of elements `n : ℕ` such that no value
(strictly) below `n` satisfies `p`.

This type has the property that `>` is well-founded when `∃ i, p i`, which allows us to implement
searches on `ℕ`, starting at `0` and with an unknown upper-bound.

It is similar to the well-founded relation constructed to define `Nat.find` with
the difference that, in `Nat.Upto p`, `p` does not need to be decidable. In fact,
`Nat.find` could be slightly altered to factor decidability out of its
well-founded relation and would then fulfill the same purpose as this file.
-/

@[expose] public section


namespace Nat

/-- The subtype of natural numbers `i` which have the property that
no `j` less than `i` satisfies `p`. This is an initial segment of the
natural numbers, up to and including the first value satisfying `p`.

We will be particularly interested in the case where there exists a value
satisfying `p`, because in this case the `>` relation is well-founded. -/
/-
**Nat.Upto** 是 Mathlib 中的一个缩写定义，位于命名空间 `Nat`。
形式化陈述：Upto (p : Nat -> Prop) : Type
参数：p : Nat -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subtype of natural numbers `i` which have the property that
no `j` less than `i` satisfies `p`. This is an initial segment of the
natural numbers, up to and including the first value satisfying `p`.

We will be particularly interested in the case where there exists a value
satisfying `p`, because in this case the `>` relation is well-founded.
-/
abbrev Upto (p : ℕ → Prop) : Type :=
  { i : ℕ // ∀ j < i, ¬p j }

namespace Upto

variable {p : ℕ → Prop}

/-- Lift the "greater than" relation on natural numbers to `Nat.Upto`. -/
/-
**Nat.Upto.GT** 是 Mathlib 中的一个定义，位于命名空间 `Nat.Upto`。
形式化陈述：(p : ℕ → Prop) → Nat.Upto p → Nat.Upto p → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift the "greater than" relation on natural numbers to `Nat.Upto`.
-/
protected def GT (p) (x y : Upto p) : Prop :=
  x.1 > y.1
/-
**Nat.Upto.** 是 Mathlib 中的一个实例，位于命名空间 `Nat.Upto`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LT (Upto p) :=
  ⟨fun x y => x.1 < y.1⟩

/-- The "greater than" relation on `Upto p` is well founded if (and only if) there exists a value
satisfying `p`. -/
/-
**Nat.Upto.wf** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Upto`。
形式化陈述：∀ {p : ℕ → Prop}, (∃ x, p x) → WellFounded (Nat.Upto.GT p)
参数：∃ x, p x；Nat.Upto.GT p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tsub_lt_tsub_iff_left_of_le`：tsub_lt_tsub_iff_left_of_le (h : b <= a) : 
a - b < a - c ↔ c < b
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `WellFoundedRelation.wf`：∀ {α : Sort u} [self : WellFoundedRelation α], W
ellFounded WellFoundedRelation.rel

--- 原说明 ---
The "greater than" relation on `Upto p` is well founded if (and only if) there e
xists a value
satisfying `p`.
-/
protected theorem wf : (∃ x, p x) → WellFounded (Upto.GT p)
  | ⟨x, h⟩ => by
    suffices Upto.GT p = InvImage (· < ·) fun y : Nat.Upto p => x - y.val by
      rw [this]
      exact (measure _).wf
    ext ⟨a, ha⟩ ⟨b, _⟩
    dsimp [InvImage, Upto.GT]
    rw [tsub_lt_tsub_iff_left_of_le (le_of_not_gt fun h' => ha _ h' h)]

/-- Zero is always a member of `Nat.Upto p` because it has no predecessors. -/
/-
**Nat.Upto.zero** 是 Mathlib 中的一个定义，位于命名空间 `Nat.Upto`。
形式化陈述：zero : Nat.Upto p
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Zero is always a member of `Nat.Upto p` because it has no predecessors.
-/
def zero : Nat.Upto p :=
  ⟨0, fun _ h => False.elim (Nat.not_lt_zero _ h)⟩

/-- The successor of `n` is in `Nat.Upto p` provided that `n` doesn't satisfy `p`. -/
/-
**Nat.Upto.succ** 是 Mathlib 中的一个定义，位于命名空间 `Nat.Upto`。
形式化陈述：succ (x : Nat.Upto p) (h : ¬p x.val) : Nat.Upto p
参数：x : Nat.Upto p；h : ¬p x.val。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The successor of `n` is in `Nat.Upto p` provided that `n` doesn't satisfy `p`.
-/
def succ (x : Nat.Upto p) (h : ¬p x.val) : Nat.Upto p :=
  ⟨x.val.succ, fun j h' => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 h' with (h' | rfl) <;> [exact x.2 _ h'; exact h]⟩

end Upto

end Nat

