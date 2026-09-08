/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Data.Sym.Sym2
public import Mathlib.Order.Lattice

/-!
# Sorting the elements of `Sym2`

This file provides `Sym2.sortEquiv`, the forward direction of which is somewhat analogous to
`Multiset.sort`.
-/

@[expose] public section

namespace Sym2

variable {α}

/-- The supremum of the two elements. -/
/-
**Sym2.sup** 是 Mathlib 中的一个定义，位于命名空间 `Sym2`。
形式化陈述：sup [SemilatticeSup α] (x : Sym2 α) : α
参数：x : Sym2 α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a

--- 原说明 ---
The supremum of the two elements.
-/
def sup [SemilatticeSup α] (x : Sym2 α) : α := Sym2.lift ⟨(· ⊔ ·), sup_comm⟩ x
/-
**Sym2.sup_mk** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：∀ {α : Type u_1} [inst : SemilatticeSup α] (a b : α), s(a, b).sup = a ⊔ b
参数：a b : α；a, b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem sup_mk [SemilatticeSup α] (a b : α) : s(a, b).sup = a ⊔ b := rfl

/-- The infimum of the two elements. -/
/-
**Sym2.inf** 是 Mathlib 中的一个定义，位于命名空间 `Sym2`。
形式化陈述：inf [SemilatticeInf α] (x : Sym2 α) : α
参数：x : Sym2 α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a

--- 原说明 ---
The infimum of the two elements.
-/
def inf [SemilatticeInf α] (x : Sym2 α) : α := Sym2.lift ⟨(· ⊓ ·), inf_comm⟩ x
/-
**Sym2.inf_mk** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：∀ {α : Type u_1} [inst : SemilatticeInf α] (a b : α), s(a, b).inf = a ⊓ b
参数：a b : α；a, b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem inf_mk [SemilatticeInf α] (a b : α) : s(a, b).inf = a ⊓ b := rfl
/-
**Sym2.inf_le_sup** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：∀ {α : Type u_1} [inst : Lattice α] (s : Sym2 α), s.inf ≤ s.sup
参数：s : Sym2 α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
protected theorem inf_le_sup [Lattice α] (s : Sym2 α) : s.inf ≤ s.sup := by
  cases s using Sym2.ind; simp

/-- In a linear order, symmetric squares are canonically identified with ordered pairs. -/
@[simps!]
/-
**Sym2.sortEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Sym2`。
形式化陈述：sortEquiv [LinearOrder α] : Sym2 α ≃ { p : α × α // p.1 <= p.2 } where toF
un s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a linear order, symmetric squares are canonically identified with ordered pai
rs.
-/
def sortEquiv [LinearOrder α] : Sym2 α ≃ { p : α × α // p.1 ≤ p.2 } where
  toFun s := ⟨(s.inf, s.sup), Sym2.inf_le_sup _⟩
  invFun p := s(p.1.1, p.1.2)
  left_inv := Sym2.ind fun a b => eq_iff.mpr <| by
    cases le_total a b with
    | inl h => simp [h]
    | inr h => simp [h]
  right_inv := Subtype.rec <| Prod.rec fun x y hxy =>
    Subtype.ext <| Prod.ext (by simp [hxy]) (by simp [hxy])

/-- In a linear order, two symmetric squares are equal if and only if
they have the same infimum and supremum. -/
/-
**Sym2.inf_eq_inf_and_sup_eq_sup** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：inf_eq_inf_and_sup_eq_sup [LinearOrder α] {s t : Sym2 α} : s.inf = t.inf ∧
 s.sup = t.sup ↔ s = t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True

--- 原说明 ---
In a linear order, two symmetric squares are equal if and only if
they have the same infimum and supremum.
-/
theorem inf_eq_inf_and_sup_eq_sup [LinearOrder α] {s t : Sym2 α} :
    s.inf = t.inf ∧ s.sup = t.sup ↔ s = t := by
  induction s with | _ a b
  induction t with | _ c d
  obtain hab | hba := le_total a b <;> obtain hcd | hdc := le_total c d <;>
    aesop (add unsafe le_antisymm)

end Sym2

