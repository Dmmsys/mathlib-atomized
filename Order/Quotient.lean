/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Order.Interval.Set.OrdConnected

/-!
### Order instances on quotients

We define a `Preorder` instance on a general `Quotient`, as the transitive closure of the
`x ≤ y ∨ x ≈ y` relation. This is the quotient object in the category of preorders.

We show that in the case of a linear order with `Set.OrdConnected` equivalence classes, this
relation is automatically transitive (we don't need to take the transitive closure), and gives a
`LinearOrder` structure on the quotient. In that case, the resulting order is sometimes called a
**condensation**.
-/

@[expose] public section

open Set

variable {α : Type*} {s : Setoid α}

namespace Quotient

section LE
variable [LE α]

/-
**Quotient.** 是 Mathlib 中的一个实例，位于命名空间 `Quotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LE (Quotient s) where
  le := Quotient.lift₂ (Relation.TransGen fun x y ↦ x ≤ y ∨ x ≈ y) <| by
    refine fun x₁ x₂ y₁ y₂ hx hy ↦ propext ⟨?_, ?_⟩ <;> intro h
    · exact .trans (.single <| .inr (symm hx)) <| .trans h (.single <| .inr hy)
    · exact .trans (.single <| .inr hx) <| .trans h (.single <| .inr (symm hy))
/-
**Quotient.le_def** 是 Mathlib 中的一个定理，位于命名空间 `Quotient`。
形式化陈述：le_def {x y : α} : Quotient.mk s x <= Quotient.mk s y ↔ Relation.TransGen 
(fun x y => x <= y ∨ x ≈ y) x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_def {x y : α} :
    Quotient.mk s x ≤ Quotient.mk s y ↔ Relation.TransGen (fun x y ↦ x ≤ y ∨ x ≈ y) x y := .rfl
/-
**Quotient.** 是 Mathlib 中的一个实例，位于命名空间 `Quotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : @Std.Refl (Quotient s) (· ≤ ·) where
  refl x := by
    induction x using Quotient.inductionOn with | h x
    exact .single <| .inr (refl x)
/-
**Quotient.** 是 Mathlib 中的一个实例，位于命名空间 `Quotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsTrans (Quotient s) (· ≤ ·) where
  trans x y z h₁ h₂ := by
    induction x using Quotient.inductionOn with | h x
    induction y using Quotient.inductionOn with | h y
    induction z using Quotient.inductionOn with | h z
    exact Relation.TransGen.trans h₁ h₂
/-
**Quotient.** 是 Mathlib 中的一个实例，位于命名空间 `Quotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [@Std.Total α (· ≤ ·)] : @Std.Total (Quotient s) (· ≤ ·) where
  total x y := by
    induction x using Quotient.inductionOn with | h x
    induction y using Quotient.inductionOn with | h y
    obtain h | h := total_of (· ≤ ·) x y
    · exact .inl <| .single <| .inl h
    · exact .inr <| .single <| .inl h
/-
**Quotient.** 是 Mathlib 中的一个实例，位于命名空间 `Quotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Preorder (Quotient s) where
  le_refl := refl
  le_trans _ _ _ := _root_.trans

end LE

section Preorder
variable [Preorder α]

/-
**Quotient.mk_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Quotient`。
形式化陈述：mk_monotone : Monotone (Quotient.mk s)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_monotone : Monotone (Quotient.mk s) :=
  fun _ _ h ↦ .single (.inl h)
/-
**Quotient.lift_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Quotient`。
形式化陈述：lift_monotone {α β : Type*} [Preorder α] {s : Setoid α} [Preorder β] (f : 
α -> β) (hf : Monotone f) (H : forall x₁ x₂, x₁ ≈ x₂ -> f x₁ = f x₂) : Monotone 
(Quotient.lift f H)
参数：f : α -> β；hf : Monotone f；H : forall x₁ x₂, x₁ ≈ x₂ -> f x₁ = f x₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem lift_monotone {α β : Type*} [Preorder α] {s : Setoid α} [Preorder β]
    (f : α → β) (hf : Monotone f) (H : ∀ x₁ x₂, x₁ ≈ x₂ → f x₁ = f x₂) :
    Monotone (Quotient.lift f H) := by
  intro x y h
  induction x using Quotient.inductionOn with | h x
  induction y using Quotient.inductionOn with | h y
  induction h
  on_goal 2 => rename_i IH; apply IH.trans
  all_goals
    rename_i h
    cases h with
    | inl h => exact hf h
    | inr h => exact (H _ _ h).le

end Preorder

section LinearOrder
variable [LinearOrder α] [H : ∀ x, OrdConnected (Quotient.mk s ⁻¹' {x})]

/-
**Quotient.mk_le_mk** 是 Mathlib 中的一个定理，位于命名空间 `Quotient`。
形式化陈述：mk_le_mk {x y : α} : Quotient.mk s x <= Quotient.mk s y ↔ x <= y ∨ x ≈ y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `propext_iff`：∀ {a b : Prop}, a = b ↔ (a ↔ b)
· 使用定理 `congrFun₂`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → Sort
 u_3} {f g : (a : α) → (b : β a) → γ a b},   f = g → ∀ (a : α) (b : β a), f a b…
· 使用定理 `Relation.transGen_eq_self`：transGen_eq_self [IsTrans α r] : TransGen r =
 r
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Quotient.eq_iff_equiv`：Quotient.eq_iff_equiv {r : Setoid α} {x y : α} : 
Quotient.mk r x = ⟦y⟧ ↔ x ≈ y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.OrdConnected.out`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, 
s.OrdConnected → ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
· 使用定理 `Quotient.instIsEquivEquiv`：∀ {α : Type u_4} [inst : Setoid α], IsEquiv α
 fun x1 x2 => x1 ≈ x2
-/
theorem mk_le_mk {x y : α} : Quotient.mk s x ≤ Quotient.mk s y ↔ x ≤ y ∨ x ≈ y := by
  rw [← propext_iff]
  revert x y
  apply congrFun₂ <| @Relation.transGen_eq_self α _ ⟨fun x y z h₁ h₂ ↦ ?_⟩
  cases h₁ <;> cases h₂ <;> rename_i h₁ h₂
  · exact .inl <| h₁.trans h₂
  · rw [or_iff_not_imp_left, not_le]
    rw [← Quotient.eq_iff_equiv] at *
    exact fun h ↦ ((H _).out h₂.symm rfl ⟨h.le, h₁⟩).trans h₂
  · rw [or_iff_not_imp_left, not_le]
    rw [← Quotient.eq_iff_equiv] at *
    exact fun h ↦ ((H _).out h₁.symm rfl ⟨h₂, h.le⟩).symm
  · exact .inr (_root_.trans h₁ h₂)
/-
**Quotient.instLinearOrder** 是 Mathlib 中的一个实例，位于命名空间 `Quotient`。
形式化陈述：instLinearOrder [DecidableRel (· ≈ · : α -> α -> Prop)] : LinearOrder (Quo
tient s) where le_antisymm x y h₁ h₂
参数：· ≈ · : α -> α -> Prop。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk_le_mk`：mk_le_mk {x y : α} : Quotient.mk s x <= Quotient.mk s
 y ↔ x <= y ∨ x ≈ y
-/
instance instLinearOrder [DecidableRel (· ≈ · : α → α → Prop)] : LinearOrder (Quotient s) where
  le_antisymm x y h₁ h₂ := by
    induction x using Quotient.inductionOn with | h x
    induction y using Quotient.inductionOn with | h y
    rw [mk_le_mk] at h₁ h₂
    cases h₁ with
    | inr h => exact Quotient.sound h
    | inl h₁ =>
      cases h₂ with
      | inr h => exact (Quotient.sound h).symm
      | inl h₂ => exact congrArg _ (h₁.antisymm h₂)
  le_total := total_of _
  toDecidableLE x y := Quotient.recOnSubsingleton₂ x y fun x y ↦ decidable_of_iff' _ mk_le_mk
/-
**Quotient.mk_lt_mk** 是 Mathlib 中的一个定理，位于命名空间 `Quotient`。
形式化陈述：mk_lt_mk {x y : α} : Quotient.mk s x < Quotient.mk s y ↔ x < y ∧ ¬ x ≈ y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₁`：contrapose_iff₁ {p q : Prop} 
: (¬ p ↔ ¬ q) -> (p ↔ q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_and_or_eq`：not_and_or_eq : (¬ (p ∧ q)) = (¬ p ∨ 
¬ q)
· 使用定理 `Quotient.mk_le_mk`：mk_le_mk {x y : α} : Quotient.mk s x <= Quotient.mk s
 y ↔ x <= y ∨ x ≈ y
· 使用定理 `comm_of`：comm_of (r : α -> α -> Prop) [Std.Symm r] {a b : α} : r a b ↔ r
 b a
· 使用定理 `IsEquiv.toSymm`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEquiv α r]
, Std.Symm r
· 使用定理 `Quotient.instIsEquivEquiv`：∀ {α : Type u_4} [inst : Setoid α], IsEquiv α
 fun x1 x2 => x1 ≈ x2
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk_lt_mk {x y : α} : Quotient.mk s x < Quotient.mk s y ↔ x < y ∧ ¬ x ≈ y := by
  classical
  contrapose! +distrib
  rw [mk_le_mk, comm_of (· ≈ ·)]
/-
**Quotient.lt_of_mk_lt_mk** 是 Mathlib 中的一个定理，位于命名空间 `Quotient`。
形式化陈述：lt_of_mk_lt_mk {x y : α} (h : Quotient.mk s x < Quotient.mk s y) : x < y
参数：h : Quotient.mk s x < Quotient.mk s y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Quotient.mk_lt_mk`：mk_lt_mk {x y : α} : Quotient.mk s x < Quotient.mk s 
y ↔ x < y ∧ ¬ x ≈ y
-/
theorem lt_of_mk_lt_mk {x y : α} (h : Quotient.mk s x < Quotient.mk s y) : x < y :=
  (mk_lt_mk.1 h).1

end LinearOrder
end Quotient

