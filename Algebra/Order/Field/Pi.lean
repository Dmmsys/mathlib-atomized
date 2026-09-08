/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Basic

/-!
# Lemmas about (finite domain) functions into fields.

We split this from `Algebra.Order.Field.Basic` to avoid importing the finiteness hierarchy there.
-/

public section

variable {α ι : Type*} [AddCommMonoid α] [LinearOrder α] [IsOrderedCancelAddMonoid α]
  [Nontrivial α] [DenselyOrdered α]

/-
**Pi.exists_forall_pos_add_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Pi.exists_forall_pos_add_lt [ExistsAddOfLE α] [Finite ι] {x y : ι -> α} (h
 : forall i, x i < y i) : exists ε, 0 < ε ∧ forall i, x i + ε < y i
参数：h : forall i, x i < y i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `exists_pos_add_of_lt'`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : 
Preorder α] [ExistsAddOfLE α] {a b : α} [AddLeftReflectLT α],   a < b → ∃ c, 0 <
 c ∧ a + c …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用引理 `Finset.inf'`：inf'_one [SemilatticeInf β] (f : α -> β) : inf' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.univ_nonempty`：univ_nonempty [Nonempty α] : (univ : Finset α).Non
empty
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.lt_inf'_iff`：∀ {α : Type u_2} {ι : Type u_5} [inst : LinearOrder 
α] {s : Finset ι} (H : s.Nonempty) {f : ι → α} {a : α},   a < s.inf' H f ↔ ∀ i ∈
 s, a < …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用定理 `add_lt_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [AddLe
ftStrictMono α] {b c : α}, b < c → ∀ (a : α), a + b < a + c
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Finset.inf'_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeInf α
] {s : Finset β} (f : β → α) {b : β} (h : b ∈ s),   s.inf' ⋯ f ≤ f b
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem Pi.exists_forall_pos_add_lt [ExistsAddOfLE α] [Finite ι] {x y : ι → α}
    (h : ∀ i, x i < y i) : ∃ ε, 0 < ε ∧ ∀ i, x i + ε < y i := by
  cases nonempty_fintype ι
  cases isEmpty_or_nonempty ι
  · obtain ⟨a, ha⟩ := exists_ne (0 : α)
    obtain ha | ha := ha.lt_or_gt <;> obtain ⟨b, hb, -⟩ := exists_pos_add_of_lt' ha <;>
      exact ⟨b, hb, isEmptyElim⟩
  choose ε hε hxε using fun i => exists_pos_add_of_lt' (h i)
  obtain rfl : x + ε = y := funext hxε
  have hε : 0 < Finset.univ.inf' Finset.univ_nonempty ε := (Finset.lt_inf'_iff _).2 fun i _ => hε _
  obtain ⟨δ, hδ, hδε⟩ := exists_between hε
  exact ⟨δ, hδ, fun i ↦ add_lt_add_right (hδε.trans_le <| Finset.inf'_le _ <| Finset.mem_univ _) _⟩
