/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Logic.Relation
public import Mathlib.Order.Hom.Basic
public import Mathlib.Tactic.Tauto

/-!
# Turning a preorder into a partial order

This file allows to make a preorder into a partial order by quotienting out the elements `a`, `b`
such that `a ≤ b` and `b ≤ a`.

`Antisymmetrization` is a functor from `Preorder` to `PartialOrder`. See `Preorder_to_PartialOrder`.

## Main declarations

* `AntisymmRel`: The antisymmetrization relation. `AntisymmRel r a b` means that `a` and `b` are
  related both ways by `r`.
* `Antisymmetrization α r`: The quotient of `α` by `AntisymmRel r`. Even when `r` is just a
  preorder, `Antisymmetrization α` is a partial order.
-/

@[expose] public section

open Function OrderDual

variable {α β : Type*} {a b c d : α}

section Relation

variable (r : α → α → Prop)

/-- The antisymmetrization relation `AntisymmRel r` is defined so that
`AntisymmRel r a b ↔ r a b ∧ r b a`. -/
/-
**AntisymmRel** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AntisymmRel (a b : α) : Prop
参数：a b : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The antisymmetrization relation `AntisymmRel r` is defined so that
`AntisymmRel r a b ↔ r a b ∧ r b a`.
-/
def AntisymmRel (a b : α) : Prop :=
  r a b ∧ r b a
/-
**antisymmRel_swap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：antisymmRel_swap : AntisymmRel (swap r) = AntisymmRel r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext₂`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → Sort u
_3} {f g : (a : α) → (b : β a) → γ a b},   (∀ (a : α) (b : β a), f a b = g a …
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
-/
theorem antisymmRel_swap : AntisymmRel (swap r) = AntisymmRel r :=
  funext₂ fun _ _ ↦ propext and_comm
/-
**antisymmRel_swap_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：antisymmRel_swap_apply : AntisymmRel (swap r) a b ↔ AntisymmRel r a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
-/
theorem antisymmRel_swap_apply : AntisymmRel (swap r) a b ↔ AntisymmRel r a b :=
  and_comm

@[simp, refl]
/-
**AntisymmRel.refl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntisymmRel.refl [Std.Refl r] (a : α) : AntisymmRel r a a
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
-/
theorem AntisymmRel.refl [Std.Refl r] (a : α) : AntisymmRel r a a :=
  ⟨_root_.refl _, _root_.refl _⟩

variable {r} in
/-
**AntisymmRel.rfl** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AntisymmRel.rfl [Std.Refl r] {a : α} : AntisymmRel r a a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntisymmRel.refl`：AntisymmRel.refl [Std.Refl r] (a : α) : AntisymmRel r 
a a
-/
lemma AntisymmRel.rfl [Std.Refl r] {a : α} : AntisymmRel r a a := .refl ..
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Std.Refl r] : Std.Refl (AntisymmRel r) where
  refl := .refl r

variable {r}
/-
**AntisymmRel.of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntisymmRel.of_eq [Std.Refl r] {a b : α} (h : a = b) : AntisymmRel r a b
参数：h : a = b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AntisymmRel.rfl`：AntisymmRel.rfl [Std.Refl r] {a : α} : AntisymmRel r a 
a
-/
theorem AntisymmRel.of_eq [Std.Refl r] {a b : α} (h : a = b) : AntisymmRel r a b := h ▸ .rfl
alias Eq.antisymmRel := AntisymmRel.of_eq

@[symm]
/-
**AntisymmRel.symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntisymmRel.symm : AntisymmRel r a b -> AntisymmRel r b a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.symm`：∀ {a b : Prop}, a ∧ b → b ∧ a
-/
theorem AntisymmRel.symm : AntisymmRel r a b → AntisymmRel r b a :=
  And.symm
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Std.Symm (AntisymmRel r) where
  symm _ _ := AntisymmRel.symm
/-
**antisymmRel_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：antisymmRel_comm : AntisymmRel r a b ↔ AntisymmRel r b a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
-/
theorem antisymmRel_comm : AntisymmRel r a b ↔ AntisymmRel r b a :=
  And.comm

@[trans]
/-
**AntisymmRel.trans** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntisymmRel.trans [IsTrans α r] (hab : AntisymmRel r a b) (hbc : AntisymmR
el r b c) : AntisymmRel r a c
参数：hab : AntisymmRel r a b；hbc : AntisymmRel r b c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem AntisymmRel.trans [IsTrans α r] (hab : AntisymmRel r a b) (hbc : AntisymmRel r b c) :
    AntisymmRel r a c :=
  ⟨_root_.trans hab.1 hbc.1, _root_.trans hbc.2 hab.2⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsTrans α r] : IsTrans α (AntisymmRel r) where
  trans _ _ _ := .trans
/-
**AntisymmRel.decidableRel** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：AntisymmRel.decidableRel [DecidableRel r] : DecidableRel (AntisymmRel r)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance AntisymmRel.decidableRel [DecidableRel r] : DecidableRel (AntisymmRel r) :=
  fun _ _ ↦ instDecidableAnd

@[simp]
/-
**antisymmRel_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：antisymmRel_iff_eq [Std.Refl r] [Std.Antisymm r] : AntisymmRel r a b ↔ a =
 b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `antisymm_iff`：antisymm_iff [Std.Refl r] [Std.Antisymm r] {a b : α} : r a
 b ∧ r b a ↔ a = b
-/
theorem antisymmRel_iff_eq [Std.Refl r] [Std.Antisymm r] : AntisymmRel r a b ↔ a = b :=
  antisymm_iff

alias ⟨AntisymmRel.eq, _⟩ := antisymmRel_iff_eq

namespace Mathlib.Tactic.GCongr

variable {α : Type*} {a b : α} {r : α → α → Prop}

/-
**Mathlib.Tactic.GCongr.AntisymmRel.left** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tact
ic.GCongr.AntisymmRel`。
形式化陈述：∀ {α : Type u_3} {a b : α} {r : α → α → Prop}, AntisymmRel r a b → r a b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma AntisymmRel.left (h : AntisymmRel r a b) : r a b := h.1

/-- See if the term is `AntisymmRel r a b` and the goal is `r a b`. -/
@[gcongr_forward] meta def exactAntisymmRelLeft : ForwardExt where
  eval h goal := do goal.assignIfDefEq (← Lean.Meta.mkAppM ``AntisymmRel.left #[h])

end Mathlib.Tactic.GCongr

end Relation

section LE

variable [LE α]

/-
**AntisymmRel.le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntisymmRel.le (h : AntisymmRel (· <= ·) a b) : a <= b
参数：h : AntisymmRel (· <= ·) a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem AntisymmRel.le (h : AntisymmRel (· ≤ ·) a b) : a ≤ b := h.1
/-
**AntisymmRel.ge** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntisymmRel.ge (h : AntisymmRel (· <= ·) a b) : b <= a
参数：h : AntisymmRel (· <= ·) a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem AntisymmRel.ge (h : AntisymmRel (· ≤ ·) a b) : b ≤ a := h.2

end LE

section IsPreorder

variable (α) (r : α → α → Prop) [IsPreorder α r]

/-- The antisymmetrization relation as an equivalence relation. -/
@[simps, instance_reducible]
/-
**AntisymmRel.setoid** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AntisymmRel.setoid : Setoid α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The antisymmetrization relation as an equivalence relation.
-/
def AntisymmRel.setoid : Setoid α :=
  ⟨AntisymmRel r, .refl r, .symm, .trans⟩

/-- The partial order derived from a preorder by making pairwise comparable elements equal. This is
the quotient by `fun a b => a ≤ b ∧ b ≤ a`. -/
/-
**Antisymmetrization** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Antisymmetrization : Type _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The partial order derived from a preorder by making pairwise comparable elements
 equal. This is
the quotient by `fun a b => a ≤ b ∧ b ≤ a`.
-/
def Antisymmetrization : Type _ :=
  Quotient <| AntisymmRel.setoid α r

variable {α}

/-- Turn an element into its antisymmetrization. -/
/-
**toAntisymmetrization** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：toAntisymmetrization : α -> Antisymmetrization α r
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn an element into its antisymmetrization.
-/
def toAntisymmetrization : α → Antisymmetrization α r :=
  Quotient.mk _

/-- Get a representative from the antisymmetrization. -/
/-
**ofAntisymmetrization** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ofAntisymmetrization : Antisymmetrization α r -> α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Get a representative from the antisymmetrization.
-/
noncomputable def ofAntisymmetrization : Antisymmetrization α r → α :=
  Quotient.out
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited α] : Inhabited (Antisymmetrization α r) :=
  inferInstanceAs <| Inhabited (Quotient _)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Subsingleton α] : Subsingleton (Antisymmetrization α r) :=
  inferInstanceAs <| Subsingleton (Quotient _)

@[elab_as_elim]
/-
**Antisymmetrization.ind** 是 Mathlib 中的一个定理，位于命名空间 `Antisymmetrization`。
形式化陈述：∀ {α : Type u_1} (r : α → α → Prop) [inst : IsPreorder α r] {p : Antisymme
trization α r → Prop},   (∀ (a : α), p (toAntisymmetrization r a)) → ∀ (q : Anti
symmetrization α r), p q
参数：r : α → α → Prop；∀ (a : α), p (toAntisymmetrization r a)；q : Antisymmetrizati
on α r。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem Antisymmetrization.ind {p : Antisymmetrization α r → Prop} :
    (∀ a, p <| toAntisymmetrization r a) → ∀ q, p q :=
  Quot.ind

@[elab_as_elim]
/-
**Antisymmetrization.induction_on** 是 Mathlib 中的一个定理，位于命名空间 `Antisymmetrization`
。
形式化陈述：∀ {α : Type u_1} (r : α → α → Prop) [inst : IsPreorder α r] {p : Antisymme
trization α r → Prop}   (a : Antisymmetrization α r), (∀ (a : α), p (toAntisymme
trization r a)) → p a
参数：r : α → α → Prop；a : Antisymmetrization α r；∀ (a : α), p (toAntisymmetrizatio
n r a)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
-/
protected theorem Antisymmetrization.induction_on {p : Antisymmetrization α r → Prop}
    (a : Antisymmetrization α r) (h : ∀ a, p <| toAntisymmetrization r a) : p a :=
  Quotient.inductionOn' a h

@[simp]
/-
**toAntisymmetrization_ofAntisymmetrization** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toAntisymmetrization_ofAntisymmetrization (a : Antisymmetrization α r) : t
oAntisymmetrization r (ofAntisymmetrization r a) = a
参数：a : Antisymmetrization α r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.out_eq'`：out_eq' (q : Quotient s₁) : Quotient.mk'' q.out = q
-/
theorem toAntisymmetrization_ofAntisymmetrization (a : Antisymmetrization α r) :
    toAntisymmetrization r (ofAntisymmetrization r a) = a :=
  Quotient.out_eq' _

end IsPreorder

section Preorder

variable [Preorder α] [Preorder β]

/-
**le_iff_lt_or_antisymmRel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_iff_lt_or_antisymmRel : a <= b ↔ a < b ∨ AntisymmRel (· <= ·) a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `lt_iff_le_not_ge`：lt_iff_le_not_ge : a < b ↔ a <= b ∧ ¬b <= a
· 使用定理 `AntisymmRel.eq_1`：∀ {α : Type u_1} (r : α → α → Prop) (a b : α), Antisym
mRel r a b = (r a b ∧ r b a)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Decidable.not_and_iff_not_or_not'`：∀ {b a : Prop} [Decidable b], ¬(a ∧ b
) ↔ ¬a ∨ ¬b
· 使用定理 `Decidable.of_not_not`：∀ {p : Prop} [Decidable p], ¬¬p → p
-/
theorem le_iff_lt_or_antisymmRel : a ≤ b ↔ a < b ∨ AntisymmRel (· ≤ ·) a b := by
  rw [lt_iff_le_not_ge, AntisymmRel]
  tauto

alias ⟨LE.le.lt_or_antisymmRel, _⟩ := le_iff_lt_or_antisymmRel
/-
**le_of_le_of_antisymmRel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_of_le_of_antisymmRel (h₁ : a <= b) (h₂ : AntisymmRel (· <= ·) b c) : a 
<= c
参数：h₁ : a <= b；h₂ : AntisymmRel (· <= ·) b c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `AntisymmRel.le`：AntisymmRel.le (h : AntisymmRel (· <= ·) a b) : a <= b
-/
theorem le_of_le_of_antisymmRel (h₁ : a ≤ b) (h₂ : AntisymmRel (· ≤ ·) b c) : a ≤ c :=
  h₁.trans h₂.le
/-
**le_of_antisymmRel_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_of_antisymmRel_of_le (h₁ : AntisymmRel (· <= ·) a b) (h₂ : b <= c) : a 
<= c
参数：h₁ : AntisymmRel (· <= ·) a b；h₂ : b <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `AntisymmRel.le`：AntisymmRel.le (h : AntisymmRel (· <= ·) a b) : a <= b
-/
theorem le_of_antisymmRel_of_le (h₁ : AntisymmRel (· ≤ ·) a b) (h₂ : b ≤ c) : a ≤ c :=
  h₁.le.trans h₂

alias LE.le.trans_antisymmRel := le_of_le_of_antisymmRel
alias AntisymmRel.trans_le := le_of_antisymmRel_of_le
/-
**lt_of_lt_of_antisymmRel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_of_lt_of_antisymmRel (h₁ : a < b) (h₂ : AntisymmRel (· <= ·) b c) : a <
 c
参数：h₁ : a < b；h₂ : AntisymmRel (· <= ·) b c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `AntisymmRel.le`：AntisymmRel.le (h : AntisymmRel (· <= ·) a b) : a <= b
-/
theorem lt_of_lt_of_antisymmRel (h₁ : a < b) (h₂ : AntisymmRel (· ≤ ·) b c) : a < c :=
  h₁.trans_le h₂.le
/-
**lt_of_antisymmRel_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_of_antisymmRel_of_lt (h₁ : AntisymmRel (· <= ·) a b) (h₂ : b < c) : a <
 c
参数：h₁ : AntisymmRel (· <= ·) a b；h₂ : b < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `AntisymmRel.le`：AntisymmRel.le (h : AntisymmRel (· <= ·) a b) : a <= b
-/
theorem lt_of_antisymmRel_of_lt (h₁ : AntisymmRel (· ≤ ·) a b) (h₂ : b < c) : a < c :=
  h₁.le.trans_lt h₂

alias LT.lt.trans_antisymmRel := lt_of_lt_of_antisymmRel
alias AntisymmRel.trans_lt := lt_of_antisymmRel_of_lt
/-
**not_lt_of_antisymmRel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_lt_of_antisymmRel (h : AntisymmRel (· <= ·) a b) : ¬ a < b
参数：h : AntisymmRel (· <= ·) a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `AntisymmRel.ge`：AntisymmRel.ge (h : AntisymmRel (· <= ·) a b) : b <= a
-/
theorem not_lt_of_antisymmRel (h : AntisymmRel (· ≤ ·) a b) : ¬ a < b :=
  h.ge.not_gt
/-
**not_gt_of_antisymmRel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_gt_of_antisymmRel (h : AntisymmRel (· <= ·) a b) : ¬ b < a
参数：h : AntisymmRel (· <= ·) a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `AntisymmRel.le`：AntisymmRel.le (h : AntisymmRel (· <= ·) a b) : a <= b
-/
theorem not_gt_of_antisymmRel (h : AntisymmRel (· ≤ ·) a b) : ¬ b < a :=
  h.le.not_gt

alias AntisymmRel.not_lt := not_lt_of_antisymmRel
alias AntisymmRel.not_gt := not_gt_of_antisymmRel
/-
**not_antisymmRel_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_antisymmRel_of_lt : a < b -> ¬ AntisymmRel (· <= ·) a b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `imp_not_comm`：∀ {a b : Prop}, a → ¬b ↔ b → ¬a
· 使用定理 `not_lt_of_antisymmRel`：not_lt_of_antisymmRel (h : AntisymmRel (· <= ·) a
 b) : ¬ a < b
-/
theorem not_antisymmRel_of_lt : a < b → ¬ AntisymmRel (· ≤ ·) a b :=
  imp_not_comm.1 not_lt_of_antisymmRel
/-
**not_antisymmRel_of_gt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_antisymmRel_of_gt : b < a -> ¬ AntisymmRel (· <= ·) a b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `imp_not_comm`：∀ {a b : Prop}, a → ¬b ↔ b → ¬a
· 使用定理 `not_gt_of_antisymmRel`：not_gt_of_antisymmRel (h : AntisymmRel (· <= ·) a
 b) : ¬ b < a
-/
theorem not_antisymmRel_of_gt : b < a → ¬ AntisymmRel (· ≤ ·) a b :=
  imp_not_comm.1 not_gt_of_antisymmRel

alias LT.lt.not_antisymmRel := not_antisymmRel_of_lt
alias LT.lt.not_antisymmRel_symm := not_antisymmRel_of_gt
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : @Trans α α α (· ≤ ·) (AntisymmRel (· ≤ ·)) (· ≤ ·) where
  trans := le_of_le_of_antisymmRel
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : @Trans α α α (AntisymmRel (· ≤ ·)) (· ≤ ·) (· ≤ ·) where
  trans := le_of_antisymmRel_of_le
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : @Trans α α α (· < ·) (AntisymmRel (· ≤ ·)) (· < ·) where
  trans := lt_of_lt_of_antisymmRel
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : @Trans α α α (AntisymmRel (· ≤ ·)) (· < ·) (· < ·) where
  trans := lt_of_antisymmRel_of_lt
/-
**AntisymmRel.le_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntisymmRel.le_congr (h₁ : AntisymmRel (· <= ·) a b) (h₂ : AntisymmRel (· 
<= ·) c d) : a <= c ↔ b <= d where mp h
参数：h₁ : AntisymmRel (· <= ·) a b；h₂ : AntisymmRel (· <= ·) c d。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_antisymmRel`：∀ {α : Type u_1} {a b c : α} [inst : Preorder α
], a ≤ b → AntisymmRel (fun x1 x2 => x1 ≤ x2) b c → a ≤ c
· 使用定理 `AntisymmRel.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : Preorder α], 
AntisymmRel (fun x1 x2 => x1 ≤ x2) a b → b ≤ c → a ≤ c
· 使用定理 `AntisymmRel.symm`：AntisymmRel.symm : AntisymmRel r a b -> AntisymmRel r 
b a
-/
theorem AntisymmRel.le_congr (h₁ : AntisymmRel (· ≤ ·) a b) (h₂ : AntisymmRel (· ≤ ·) c d) :
    a ≤ c ↔ b ≤ d where
  mp h := (h₁.symm.trans_le h).trans_antisymmRel h₂
  mpr h := (h₁.trans_le h).trans_antisymmRel h₂.symm
/-
**AntisymmRel.le_congr_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntisymmRel.le_congr_left (h : AntisymmRel (· <= ·) a b) : a <= c ↔ b <= c
参数：h : AntisymmRel (· <= ·) a b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntisymmRel.le_congr`：AntisymmRel.le_congr (h₁ : AntisymmRel (· <= ·) a 
b) (h₂ : AntisymmRel (· <= ·) c d) : a <= c ↔ b <= d where mp h
· 使用引理 `AntisymmRel.rfl`：AntisymmRel.rfl [Std.Refl r] {a : α} : AntisymmRel r a 
a
-/
theorem AntisymmRel.le_congr_left (h : AntisymmRel (· ≤ ·) a b) : a ≤ c ↔ b ≤ c :=
  h.le_congr .rfl
/-
**AntisymmRel.le_congr_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntisymmRel.le_congr_right (h : AntisymmRel (· <= ·) b c) : a <= b ↔ a <= 
c
参数：h : AntisymmRel (· <= ·) b c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntisymmRel.le_congr`：AntisymmRel.le_congr (h₁ : AntisymmRel (· <= ·) a 
b) (h₂ : AntisymmRel (· <= ·) c d) : a <= c ↔ b <= d where mp h
· 使用引理 `AntisymmRel.rfl`：AntisymmRel.rfl [Std.Refl r] {a : α} : AntisymmRel r a 
a
-/
theorem AntisymmRel.le_congr_right (h : AntisymmRel (· ≤ ·) b c) : a ≤ b ↔ a ≤ c :=
  AntisymmRel.rfl.le_congr h
/-
**AntisymmRel.lt_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntisymmRel.lt_congr (h₁ : AntisymmRel (· <= ·) a b) (h₂ : AntisymmRel (· 
<= ·) c d) : a < c ↔ b < d where mp h
参数：h₁ : AntisymmRel (· <= ·) a b；h₂ : AntisymmRel (· <= ·) c d。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_antisymmRel`：∀ {α : Type u_1} {a b c : α} [inst : Preorder α
], a < b → AntisymmRel (fun x1 x2 => x1 ≤ x2) b c → a < c
· 使用定理 `AntisymmRel.trans_lt`：∀ {α : Type u_1} {a b c : α} [inst : Preorder α], 
AntisymmRel (fun x1 x2 => x1 ≤ x2) a b → b < c → a < c
· 使用定理 `AntisymmRel.symm`：AntisymmRel.symm : AntisymmRel r a b -> AntisymmRel r 
b a
-/
theorem AntisymmRel.lt_congr (h₁ : AntisymmRel (· ≤ ·) a b) (h₂ : AntisymmRel (· ≤ ·) c d) :
    a < c ↔ b < d where
  mp h := (h₁.symm.trans_lt h).trans_antisymmRel h₂
  mpr h := (h₁.trans_lt h).trans_antisymmRel h₂.symm
/-
**AntisymmRel.lt_congr_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntisymmRel.lt_congr_left (h : AntisymmRel (· <= ·) a b) : a < c ↔ b < c
参数：h : AntisymmRel (· <= ·) a b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntisymmRel.lt_congr`：AntisymmRel.lt_congr (h₁ : AntisymmRel (· <= ·) a 
b) (h₂ : AntisymmRel (· <= ·) c d) : a < c ↔ b < d where mp h
· 使用引理 `AntisymmRel.rfl`：AntisymmRel.rfl [Std.Refl r] {a : α} : AntisymmRel r a 
a
-/
theorem AntisymmRel.lt_congr_left (h : AntisymmRel (· ≤ ·) a b) : a < c ↔ b < c :=
  h.lt_congr .rfl
/-
**AntisymmRel.lt_congr_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntisymmRel.lt_congr_right (h : AntisymmRel (· <= ·) b c) : a < b ↔ a < c
参数：h : AntisymmRel (· <= ·) b c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntisymmRel.lt_congr`：AntisymmRel.lt_congr (h₁ : AntisymmRel (· <= ·) a 
b) (h₂ : AntisymmRel (· <= ·) c d) : a < c ↔ b < d where mp h
· 使用引理 `AntisymmRel.rfl`：AntisymmRel.rfl [Std.Refl r] {a : α} : AntisymmRel r a 
a
-/
theorem AntisymmRel.lt_congr_right (h : AntisymmRel (· ≤ ·) b c) : a < b ↔ a < c :=
  AntisymmRel.rfl.lt_congr h
/-
**AntisymmRel.antisymmRel_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntisymmRel.antisymmRel_congr (h₁ : AntisymmRel (· <= ·) a b) (h₂ : Antisy
mmRel (· <= ·) c d) : AntisymmRel (· <= ·) a c ↔ AntisymmRel (· <= ·) b d
参数：h₁ : AntisymmRel (· <= ·) a b；h₂ : AntisymmRel (· <= ·) c d。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `rel_congr`：rel_congr [Std.Symm r] [IsTrans α r] {a b c d : α} (h₁ : r a 
b) (h₂ : r c d) : r a c ↔ r b d
· 使用定理 `instSymmAntisymmRel`：∀ {α : Type u_1} {r : α → α → Prop}, Std.Symm (Anti
symmRel r)
· 使用定理 `instIsTransAntisymmRel`：∀ {α : Type u_1} {r : α → α → Prop} [IsTrans α r
], IsTrans α (AntisymmRel r)
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
-/
theorem AntisymmRel.antisymmRel_congr
    (h₁ : AntisymmRel (· ≤ ·) a b) (h₂ : AntisymmRel (· ≤ ·) c d) :
    AntisymmRel (· ≤ ·) a c ↔ AntisymmRel (· ≤ ·) b d :=
  rel_congr h₁ h₂
/-
**AntisymmRel.antisymmRel_congr_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntisymmRel.antisymmRel_congr_left (h : AntisymmRel (· <= ·) a b) : Antisy
mmRel (· <= ·) a c ↔ AntisymmRel (· <= ·) b c
参数：h : AntisymmRel (· <= ·) a b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `rel_congr_left`：rel_congr_left [Std.Symm r] [IsTrans α r] {a b c : α} (h
 : r a b) : r a c ↔ r b c
· 使用定理 `instSymmAntisymmRel`：∀ {α : Type u_1} {r : α → α → Prop}, Std.Symm (Anti
symmRel r)
· 使用定理 `instIsTransAntisymmRel`：∀ {α : Type u_1} {r : α → α → Prop} [IsTrans α r
], IsTrans α (AntisymmRel r)
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
-/
theorem AntisymmRel.antisymmRel_congr_left (h : AntisymmRel (· ≤ ·) a b) :
    AntisymmRel (· ≤ ·) a c ↔ AntisymmRel (· ≤ ·) b c :=
  rel_congr_left h
/-
**AntisymmRel.antisymmRel_congr_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntisymmRel.antisymmRel_congr_right (h : AntisymmRel (· <= ·) b c) : Antis
ymmRel (· <= ·) a b ↔ AntisymmRel (· <= ·) a c
参数：h : AntisymmRel (· <= ·) b c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `rel_congr_right`：rel_congr_right [Std.Symm r] [IsTrans α r] {a b c : α} 
(h : r b c) : r a b ↔ r a c
· 使用定理 `instSymmAntisymmRel`：∀ {α : Type u_1} {r : α → α → Prop}, Std.Symm (Anti
symmRel r)
· 使用定理 `instIsTransAntisymmRel`：∀ {α : Type u_1} {r : α → α → Prop} [IsTrans α r
], IsTrans α (AntisymmRel r)
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
-/
theorem AntisymmRel.antisymmRel_congr_right (h : AntisymmRel (· ≤ ·) b c) :
    AntisymmRel (· ≤ ·) a b ↔ AntisymmRel (· ≤ ·) a c :=
  rel_congr_right h
/-
**AntisymmRel.image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntisymmRel.image (h : AntisymmRel (· <= ·) a b) {f : α -> β} (hf : Monoto
ne f) : AntisymmRel (· <= ·) (f a) (f b)
参数：h : AntisymmRel (· <= ·) a b；hf : Monotone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem AntisymmRel.image (h : AntisymmRel (· ≤ ·) a b) {f : α → β} (hf : Monotone f) :
    AntisymmRel (· ≤ ·) (f a) (f b) :=
  ⟨hf h.1, hf h.2⟩
/-
**instPartialOrderAntisymmetrization** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instPartialOrderAntisymmetrization : PartialOrder (Antisymmetrization α (·
 <= ·)) where le
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsPreorderLe`：∀ {α : Type u} [inst : Preorder α], IsPreorder α fun x
1 x2 => x1 ≤ x2
-/
instance instPartialOrderAntisymmetrization : PartialOrder (Antisymmetrization α (· ≤ ·)) where
  le :=
    Quotient.lift₂ (· ≤ ·) fun (_ _ _ _ : α) h₁ h₂ =>
      propext ⟨fun h => h₁.2.trans <| h.trans h₂.1, fun h => h₁.1.trans <| h.trans h₂.2⟩
  lt :=
    Quotient.lift₂ (· < ·) fun (_ _ _ _ : α) h₁ h₂ =>
      propext ⟨fun h => h₁.2.trans_lt <| h.trans_le h₂.1, fun h =>
                h₁.1.trans_lt <| h.trans_le h₂.2⟩
  le_refl a := Quotient.inductionOn' a le_refl
  le_trans a b c := Quotient.inductionOn₃' a b c fun _ _ _ => le_trans
  lt_iff_le_not_ge a b := Quotient.inductionOn₂' a b fun _ _ => lt_iff_le_not_ge
  le_antisymm a b := Quotient.inductionOn₂' a b fun _ _ hab hba => Quotient.sound' ⟨hab, hba⟩
/-
**antisymmetrization_fibration** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：antisymmetrization_fibration : Relation.Fibration (· < ·) (· < ·) (toAntis
ymmetrization (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsPreorderLe`：∀ {α : Type u} [inst : Preorder α], IsPreorder α fun x
1 x2 => x1 ≤ x2
-/
theorem antisymmetrization_fibration :
    Relation.Fibration (· < ·) (· < ·) (toAntisymmetrization (α := α) (· ≤ ·)) := by
  rintro a ⟨b⟩ h
  exact ⟨b, h, rfl⟩
/-
**acc_antisymmetrization_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：acc_antisymmetrization_iff : Acc (· < ·) (toAntisymmetrization (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `acc_lift₂_iff`：acc_lift₂_iff {_ : Setoid α} {r : α -> α -> Prop} {H : fo
rall (a₁ b₁ a₂ b₂ : α), a₁ ≈ a₂ -> b₁ ≈ b₂ -> r a₁ b₁ = r a₂ b₂} {a} : Acc (Quot
ien…
· 使用定理 `instIsPreorderLe`：∀ {α : Type u} [inst : Preorder α], IsPreorder α fun x
1 x2 => x1 ≤ x2
-/
theorem acc_antisymmetrization_iff : Acc (· < ·)
    (toAntisymmetrization (α := α) (· ≤ ·) a) ↔ Acc (· < ·) a :=
  acc_lift₂_iff
/-
**wellFounded_antisymmetrization_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wellFounded_antisymmetrization_iff : WellFounded (@LT.lt (Antisymmetrizati
on α (· <= ·)) _) ↔ WellFounded (@LT.lt α _)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `wellFounded_lift₂_iff`：wellFounded_lift₂_iff {_ : Setoid α} {r : α -> α 
-> Prop} {H : forall (a₁ b₁ a₂ b₂ : α), a₁ ≈ a₂ -> b₁ ≈ b₂ -> r a₁ b₁ = r a₂ b₂}
 : WellFoun…
· 使用定理 `instIsPreorderLe`：∀ {α : Type u} [inst : Preorder α], IsPreorder α fun x
1 x2 => x1 ≤ x2
-/
theorem wellFounded_antisymmetrization_iff :
    WellFounded (@LT.lt (Antisymmetrization α (· ≤ ·)) _) ↔ WellFounded (@LT.lt α _) :=
  wellFounded_lift₂_iff
/-
**wellFoundedLT_antisymmetrization_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wellFoundedLT_antisymmetrization_iff : WellFoundedLT (Antisymmetrization α
 (· <= ·)) ↔ WellFoundedLT α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsPreorderLe`：∀ {α : Type u} [inst : Preorder α], IsPreorder α fun x
1 x2 => x1 ≤ x2
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
theorem wellFoundedLT_antisymmetrization_iff :
    WellFoundedLT (Antisymmetrization α (· ≤ ·)) ↔ WellFoundedLT α := by
  simp_rw [isWellFounded_iff, wellFounded_antisymmetrization_iff]

set_option backward.isDefEq.respectTransparency false in
/-
**wellFoundedGT_antisymmetrization_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wellFoundedGT_antisymmetrization_iff : WellFoundedGT (Antisymmetrization α
 (· <= ·)) ↔ WellFoundedGT α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsPreorderLe`：∀ {α : Type u} [inst : Preorder α], IsPreorder α fun x
1 x2 => x1 ≤ x2
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `wellFounded_liftOn₂'_iff`：∀ {α : Type u_1} {s : Setoid α} {r : α → α → P
rop} {H : ∀ (a₁ a₂ b₁ b₂ : α), s a₁ b₁ → s a₂ b₂ → r a₁ a₂ = r b₁ b₂},   (WellFo
unded fun x y …
-/
theorem wellFoundedGT_antisymmetrization_iff :
    WellFoundedGT (Antisymmetrization α (· ≤ ·)) ↔ WellFoundedGT α := by
  simp_rw [isWellFounded_iff]
  convert! wellFounded_liftOn₂'_iff with ⟨_⟩ ⟨_⟩
  exact fun _ _ _ _ h₁ h₂ ↦ propext
    ⟨fun h ↦ (h₂.2.trans_lt h).trans_le h₁.1, fun h ↦ (h₂.1.trans_lt h).trans_le h₁.2⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [WellFoundedLT α] : WellFoundedLT (Antisymmetrization α (· ≤ ·)) :=
  wellFoundedLT_antisymmetrization_iff.mpr ‹_›
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [WellFoundedGT α] : WellFoundedGT (Antisymmetrization α (· ≤ ·)) :=
  wellFoundedGT_antisymmetrization_iff.mpr ‹_›

set_option backward.isDefEq.respectTransparency false in
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableLE α] [DecidableLT α] [@Std.Total α (· ≤ ·)] :
    LinearOrder (Antisymmetrization α (· ≤ ·)) :=
  { instPartialOrderAntisymmetrization with
    le_total := fun a b => Quotient.inductionOn₂' a b <| total_of (· ≤ ·),
    toDecidableLE := fun _ _ => show Decidable (Quotient.liftOn₂' _ _ _ _) from inferInstance,
    toDecidableLT := fun _ _ => show Decidable (Quotient.liftOn₂' _ _ _ _) from inferInstance }

@[simp]
/-
**toAntisymmetrization_le_toAntisymmetrization_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toAntisymmetrization_le_toAntisymmetrization_iff : toAntisymmetrization (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `instIsPreorderLe`：∀ {α : Type u} [inst : Preorder α], IsPreorder α fun x
1 x2 => x1 ≤ x2
-/
theorem toAntisymmetrization_le_toAntisymmetrization_iff :
    toAntisymmetrization (α := α) (· ≤ ·) a ≤ toAntisymmetrization (α := α) (· ≤ ·) b ↔ a ≤ b :=
  Iff.rfl

@[simp]
/-
**toAntisymmetrization_lt_toAntisymmetrization_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toAntisymmetrization_lt_toAntisymmetrization_iff : toAntisymmetrization (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `instIsPreorderLe`：∀ {α : Type u} [inst : Preorder α], IsPreorder α fun x
1 x2 => x1 ≤ x2
-/
theorem toAntisymmetrization_lt_toAntisymmetrization_iff :
    toAntisymmetrization (α := α) (· ≤ ·) a < toAntisymmetrization (α := α) (· ≤ ·) b ↔ a < b :=
  Iff.rfl

@[simp]
/-
**ofAntisymmetrization_le_ofAntisymmetrization_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofAntisymmetrization_le_ofAntisymmetrization_iff {a b : Antisymmetrization
 α (· <= ·)} : ofAntisymmetrization (· <= ·) a <= ofAntisymmetrization (· <= ·) 
b ↔ a <= b
参数：· <= ·。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsPreorderLe`：∀ {α : Type u} [inst : Preorder α], IsPreorder α fun x
1 x2 => x1 ≤ x2
· 使用定理 `RelEmbedding.map_rel_iff`：map_rel_iff (f : r ↪r s) {a b} : s (f a) (f b)
 ↔ r a b
-/
theorem ofAntisymmetrization_le_ofAntisymmetrization_iff {a b : Antisymmetrization α (· ≤ ·)} :
    ofAntisymmetrization (· ≤ ·) a ≤ ofAntisymmetrization (· ≤ ·) b ↔ a ≤ b :=
  (Quotient.outRelEmbedding _).map_rel_iff

@[simp]
/-
**ofAntisymmetrization_lt_ofAntisymmetrization_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofAntisymmetrization_lt_ofAntisymmetrization_iff {a b : Antisymmetrization
 α (· <= ·)} : ofAntisymmetrization (· <= ·) a < ofAntisymmetrization (· <= ·) b
 ↔ a < b
参数：· <= ·。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsPreorderLe`：∀ {α : Type u} [inst : Preorder α], IsPreorder α fun x
1 x2 => x1 ≤ x2
· 使用定理 `RelEmbedding.map_rel_iff`：map_rel_iff (f : r ↪r s) {a b} : s (f a) (f b)
 ↔ r a b
-/
theorem ofAntisymmetrization_lt_ofAntisymmetrization_iff {a b : Antisymmetrization α (· ≤ ·)} :
    ofAntisymmetrization (· ≤ ·) a < ofAntisymmetrization (· ≤ ·) b ↔ a < b :=
  (Quotient.outRelEmbedding _).map_rel_iff

@[gcongr, mono]
/-
**toAntisymmetrization_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toAntisymmetrization_mono : Monotone (toAntisymmetrization (α
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAntisymmetrization_mono : Monotone (toAntisymmetrization (α := α) (· ≤ ·)) :=
  fun _ _ => id

open scoped Relator in
/-
**liftFun_antisymmRel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：liftFun_antisymmRel (f : α ->o β) : ((AntisymmRel.setoid α (· <= ·)).r ⇒ (
AntisymmRel.setoid β (· <= ·)).r) f f
参数：f : α ->o β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsPreorderLe`：∀ {α : Type u} [inst : Preorder α], IsPreorder α fun x
1 x2 => x1 ≤ x2
· 使用定理 `OrderHom.mono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst
_1 : Preorder β] (f : α →o β), Monotone ⇑f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem liftFun_antisymmRel (f : α →o β) :
    ((AntisymmRel.setoid α (· ≤ ·)).r ⇒ (AntisymmRel.setoid β (· ≤ ·)).r) f f := fun _ _ h =>
  ⟨f.mono h.1, f.mono h.2⟩

/-- Turns an order homomorphism from `α` to `β` into one from `Antisymmetrization α` to
`Antisymmetrization β`. `Antisymmetrization` is actually a functor. See `Preorder_to_PartialOrder`.
-/
/-
**OrderHom.antisymmetrization** 是 Mathlib 中的一个定义，位于命名空间 `OrderHom`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     [inst : Preorder α] →       [inst_
1 : Preorder β] →         (α →o β) → (Antisymmetrization α fun x1 x2 => x1 ≤ x2)
 →o Antisymmetrization β fun x1 x2 => x1 ≤ x2
参数：α →o β；Antisymmetrization α fun x1 x2 => x1 ≤ x2。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instIsPreorderLe`：∀ {α : Type u} [inst : Preorder α], IsPreorder α fun x
1 x2 => x1 ≤ x2
· 使用定理 `Quotient.map'`：map'_mk'' (f : α -> β) (h) (x : α) : (Quotient.mk'' x : Q
uotient s₁).map' f h = (Quotient.mk'' (f x) : Quotient s₂)
· 使用定理 `liftFun_antisymmRel`：liftFun_antisymmRel (f : α ->o β) : ((AntisymmRel.s
etoid α (· <= ·)).r ⇒ (AntisymmRel.setoid β (· <= ·)).r) f f

--- 原说明 ---
Turns an order homomorphism from `α` to `β` into one from `Antisymmetrization α`
 to
`Antisymmetrization β`. `Antisymmetrization` is actually a functor. See `Preorde
r_to_PartialOrder`.
-/
protected def OrderHom.antisymmetrization (f : α →o β) :
    Antisymmetrization α (· ≤ ·) →o Antisymmetrization β (· ≤ ·) :=
  ⟨Quotient.map' f <| liftFun_antisymmRel f, fun a b => Quotient.inductionOn₂' a b f.mono⟩

@[simp]
/-
**OrderHom.coe_antisymmetrization** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OrderHom.coe_antisymmetrization (f : α ->o β) : ⇑f.antisymmetrization = Qu
otient.map' f (liftFun_antisymmRel f)
参数：f : α ->o β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsPreorderLe`：∀ {α : Type u} [inst : Preorder α], IsPreorder α fun x
1 x2 => x1 ≤ x2
-/
theorem OrderHom.coe_antisymmetrization (f : α →o β) :
    ⇑f.antisymmetrization = Quotient.map' f (liftFun_antisymmRel f) :=
  rfl
/-
**OrderHom.antisymmetrization_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OrderHom.antisymmetrization_apply (f : α ->o β) (a : Antisymmetrization α 
(· <= ·)) : f.antisymmetrization a = Quotient.map' f (liftFun_antisymmRel f) a
参数：f : α ->o β；a : Antisymmetrization α (· <= ·)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsPreorderLe`：∀ {α : Type u} [inst : Preorder α], IsPreorder α fun x
1 x2 => x1 ≤ x2
-/
theorem OrderHom.antisymmetrization_apply (f : α →o β) (a : Antisymmetrization α (· ≤ ·)) :
    f.antisymmetrization a = Quotient.map' f (liftFun_antisymmRel f) a :=
  rfl

@[simp]
/-
**OrderHom.antisymmetrization_apply_mk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OrderHom.antisymmetrization_apply_mk (f : α ->o β) (a : α) : f.antisymmetr
ization (toAntisymmetrization _ a) = toAntisymmetrization _ (f a)
参数：f : α ->o β；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.map_mk`：map_mk (f : α -> β) (h) (x : α) : Quotient.map f h (⟦x⟧
 : Quotient sa) = (⟦f x⟧ : Quotient sb)
· 使用定理 `instIsPreorderLe`：∀ {α : Type u} [inst : Preorder α], IsPreorder α fun x
1 x2 => x1 ≤ x2
· 使用定理 `liftFun_antisymmRel`：liftFun_antisymmRel (f : α ->o β) : ((AntisymmRel.s
etoid α (· <= ·)).r ⇒ (AntisymmRel.setoid β (· <= ·)).r) f f
-/
theorem OrderHom.antisymmetrization_apply_mk (f : α →o β) (a : α) :
    f.antisymmetrization (toAntisymmetrization _ a) = toAntisymmetrization _ (f a) :=
  @Quotient.map_mk _ _ (_root_.id _) (_root_.id _) f (liftFun_antisymmRel f) _

variable (α)

/-- `ofAntisymmetrization` as an order embedding. -/
@[simps]
/-
**OrderEmbedding.ofAntisymmetrization** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OrderEmbedding.ofAntisymmetrization : Antisymmetrization α (· <= ·) ↪o α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instIsPreorderLe`：∀ {α : Type u} [inst : Preorder α], IsPreorder α fun x
1 x2 => x1 ≤ x2

--- 原说明 ---
`ofAntisymmetrization` as an order embedding.
-/
noncomputable def OrderEmbedding.ofAntisymmetrization : Antisymmetrization α (· ≤ ·) ↪o α :=
  { Quotient.outRelEmbedding _ with toFun := _root_.ofAntisymmetrization _ }

set_option backward.isDefEq.respectTransparency false in
/-- `Antisymmetrization` and `orderDual` commute. -/
/-
**OrderIso.dualAntisymmetrization** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OrderIso.dualAntisymmetrization : (Antisymmetrization α (· <= ·))ᵒᵈ ≃o Ant
isymmetrization αᵒᵈ (· <= ·) where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instIsPreorderLe`：∀ {α : Type u} [inst : Preorder α], IsPreorder α fun x
1 x2 => x1 ≤ x2
· 使用定理 `Quotient.map'`：map'_mk'' (f : α -> β) (h) (x : α) : (Quotient.mk'' x : Q
uotient s₁).map' f h = (Quotient.mk'' (f x) : Quotient s₂)

--- 原说明 ---
`Antisymmetrization` and `orderDual` commute.
-/
def OrderIso.dualAntisymmetrization :
    (Antisymmetrization α (· ≤ ·))ᵒᵈ ≃o Antisymmetrization αᵒᵈ (· ≤ ·) where
  toFun := (Quotient.map' id) fun _ _ => And.symm
  invFun := (Quotient.map' id) fun _ _ => And.symm
  left_inv a := Quotient.inductionOn' a fun a => by simp_rw [Quotient.map'_mk'', id]
  right_inv a := Quotient.inductionOn' a fun a => by simp_rw [Quotient.map'_mk'', id]
  map_rel_iff' := @fun a b => Quotient.inductionOn₂' a b fun _ _ => Iff.rfl

@[simp]
/-
**OrderIso.dualAntisymmetrization_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OrderIso.dualAntisymmetrization_apply (a : α) : OrderIso.dualAntisymmetriz
ation _ (toDual <| toAntisymmetrization _ a) = toAntisymmetrization _ (toDual a)
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsPreorderLe`：∀ {α : Type u} [inst : Preorder α], IsPreorder α fun x
1 x2 => x1 ≤ x2
-/
theorem OrderIso.dualAntisymmetrization_apply (a : α) :
    OrderIso.dualAntisymmetrization _ (toDual <| toAntisymmetrization _ a) =
      toAntisymmetrization _ (toDual a) :=
  rfl

@[simp]
/-
**OrderIso.dualAntisymmetrization_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OrderIso.dualAntisymmetrization_symm_apply (a : α) : (OrderIso.dualAntisym
metrization _).symm (toAntisymmetrization _ <| toDual a) = toDual (toAntisymmetr
ization _ a)
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsPreorderLe`：∀ {α : Type u} [inst : Preorder α], IsPreorder α fun x
1 x2 => x1 ≤ x2
-/
theorem OrderIso.dualAntisymmetrization_symm_apply (a : α) :
    (OrderIso.dualAntisymmetrization _).symm (toAntisymmetrization _ <| toDual a) =
      toDual (toAntisymmetrization _ a) :=
  rfl

end Preorder

section SymmGen

open Relation

variable {r : α → α → Prop}

/-
**AntisymmRel.symmGen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntisymmRel.symmGen (h : AntisymmRel r a b) : SymmGen r a b
参数：h : AntisymmRel r a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem AntisymmRel.symmGen (h : AntisymmRel r a b) : SymmGen r a b :=
  Or.inl h.1

variable [Preorder α]
/-
**Relation.SymmGen.of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Relation.SymmGen.of_lt (h : a < b) : SymmGen (· <= ·) a b
参数：h : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.symmGen`：∀ {α : Type u_7} [inst : LE α] {a b : α}, a ≤ b → Relatio
n.SymmGen (fun x1 x2 => x1 ≤ x2) a b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem Relation.SymmGen.of_lt (h : a < b) : SymmGen (· ≤ ·) a b := h.le.symmGen
/-
**Relation.SymmGen.of_gt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Relation.SymmGen.of_gt (h : b < a) : SymmGen (· <= ·) a b
参数：h : b < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.symmGen_symm`：∀ {α : Type u_7} [inst : LE α] {a b : α}, b ≤ a → Re
lation.SymmGen (fun x1 x2 => x1 ≤ x2) a b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem Relation.SymmGen.of_gt (h : b < a) : SymmGen (· ≤ ·) a b := h.le.symmGen_symm

alias _root_.LT.lt.symmGen := SymmGen.of_lt
alias _root_.LT.lt.symmGen_symm := SymmGen.of_gt

@[trans]
/-
**Relation.SymmGen.of_symmGen_of_antisymmRel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Relation.SymmGen.of_symmGen_of_antisymmRel (h₁ : SymmGen (· <= ·) a b) (h₂
 : AntisymmRel (· <= ·) b c) : SymmGen (· <= ·) a c
参数：h₁ : SymmGen (· <= ·) a b；h₂ : AntisymmRel (· <= ·) b c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.symmGen`：∀ {α : Type u_7} [inst : LE α] {a b : α}, a ≤ b → Relatio
n.SymmGen (fun x1 x2 => x1 ≤ x2) a b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `AntisymmRel.le`：AntisymmRel.le (h : AntisymmRel (· <= ·) a b) : a <= b
· 使用定理 `LE.le.symmGen_symm`：∀ {α : Type u_7} [inst : LE α] {a b : α}, b ≤ a → Re
lation.SymmGen (fun x1 x2 => x1 ≤ x2) a b
· 使用定理 `AntisymmRel.ge`：AntisymmRel.ge (h : AntisymmRel (· <= ·) a b) : b <= a
-/
theorem Relation.SymmGen.of_symmGen_of_antisymmRel
    (h₁ : SymmGen (· ≤ ·) a b) (h₂ : AntisymmRel (· ≤ ·) b c) : SymmGen (· ≤ ·) a c := by
  obtain (h | h) := h₁
  · exact (h.trans h₂.le).symmGen
  · exact (h₂.ge.trans h).symmGen_symm

alias Relation.SymmGen.trans_antisymmRel := SymmGen.of_symmGen_of_antisymmRel
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : @Trans α α α (SymmGen (· ≤ ·)) (AntisymmRel (· ≤ ·)) (SymmGen (· ≤ ·)) where
  trans := SymmGen.of_symmGen_of_antisymmRel

@[trans]
/-
**Relation.SymmGen.of_antisymmRel_of_symmGen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Relation.SymmGen.of_antisymmRel_of_symmGen (h₁ : AntisymmRel (· <= ·) a b)
 (h₂ : SymmGen (· <= ·) b c) : SymmGen (· <= ·) a c
参数：h₁ : AntisymmRel (· <= ·) a b；h₂ : SymmGen (· <= ·) b c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.SymmGen.symm`：symm : SymmGen r a b -> SymmGen r b a
· 使用定理 `Relation.SymmGen.trans_antisymmRel`：∀ {α : Type u_1} {a b c : α} [inst :
 Preorder α],   Relation.SymmGen (fun x1 x2 => x1 ≤ x2) a b →     AntisymmRel (f
un x1 x2 => x1 ≤ x2) b c…
· 使用定理 `AntisymmRel.symm`：AntisymmRel.symm : AntisymmRel r a b -> AntisymmRel r 
b a
-/
theorem Relation.SymmGen.of_antisymmRel_of_symmGen
    (h₁ : AntisymmRel (· ≤ ·) a b) (h₂ : SymmGen (· ≤ ·) b c) : SymmGen (· ≤ ·) a c :=
  (h₂.symm.trans_antisymmRel h₁.symm).symm

alias AntisymmRel.trans_symmGen := SymmGen.of_antisymmRel_of_symmGen
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : @Trans α α α (AntisymmRel (· ≤ ·)) (SymmGen (· ≤ ·)) (SymmGen (· ≤ ·)) where
  trans := SymmGen.of_antisymmRel_of_symmGen
/-
**AntisymmRel.symmGen_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntisymmRel.symmGen_congr (h₁ : AntisymmRel (· <= ·) a b) (h₂ : AntisymmRe
l (· <= ·) c d) : SymmGen (· <= ·) a c ↔ SymmGen (· <= ·) b d where mp h
参数：h₁ : AntisymmRel (· <= ·) a b；h₂ : AntisymmRel (· <= ·) c d。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.SymmGen.trans_antisymmRel`：∀ {α : Type u_1} {a b c : α} [inst :
 Preorder α],   Relation.SymmGen (fun x1 x2 => x1 ≤ x2) a b →     AntisymmRel (f
un x1 x2 => x1 ≤ x2) b c…
· 使用定理 `AntisymmRel.trans_symmGen`：∀ {α : Type u_1} {a b c : α} [inst : Preorder
 α],   AntisymmRel (fun x1 x2 => x1 ≤ x2) a b →     Relation.SymmGen (fun x1 x2 
=> x1 ≤ x2) b c…
· 使用定理 `AntisymmRel.symm`：AntisymmRel.symm : AntisymmRel r a b -> AntisymmRel r 
b a
-/
theorem AntisymmRel.symmGen_congr (h₁ : AntisymmRel (· ≤ ·) a b) (h₂ : AntisymmRel (· ≤ ·) c d) :
    SymmGen (· ≤ ·) a c ↔ SymmGen (· ≤ ·) b d where
  mp h := (h₁.symm.trans_symmGen h).trans_antisymmRel h₂
  mpr h := (h₁.trans_symmGen h).trans_antisymmRel h₂.symm
/-
**AntisymmRel.symmGen_congr_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntisymmRel.symmGen_congr_left (h : AntisymmRel (· <= ·) a b) : SymmGen (·
 <= ·) a c ↔ SymmGen (· <= ·) b c
参数：h : AntisymmRel (· <= ·) a b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntisymmRel.symmGen_congr`：AntisymmRel.symmGen_congr (h₁ : AntisymmRel (
· <= ·) a b) (h₂ : AntisymmRel (· <= ·) c d) : SymmGen (· <= ·) a c ↔ SymmGen (·
 <= ·) b d wher…
· 使用引理 `AntisymmRel.rfl`：AntisymmRel.rfl [Std.Refl r] {a : α} : AntisymmRel r a 
a
-/
theorem AntisymmRel.symmGen_congr_left (h : AntisymmRel (· ≤ ·) a b) :
    SymmGen (· ≤ ·) a c ↔ SymmGen (· ≤ ·) b c :=
  h.symmGen_congr .rfl
/-
**AntisymmRel.symmGen_congr_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntisymmRel.symmGen_congr_right (h : AntisymmRel (· <= ·) b c) : SymmGen (
· <= ·) a b ↔ SymmGen (· <= ·) a c
参数：h : AntisymmRel (· <= ·) b c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntisymmRel.symmGen_congr`：AntisymmRel.symmGen_congr (h₁ : AntisymmRel (
· <= ·) a b) (h₂ : AntisymmRel (· <= ·) c d) : SymmGen (· <= ·) a c ↔ SymmGen (·
 <= ·) b d wher…
· 使用引理 `AntisymmRel.rfl`：AntisymmRel.rfl [Std.Refl r] {a : α} : AntisymmRel r a 
a
-/
theorem AntisymmRel.symmGen_congr_right (h : AntisymmRel (· ≤ ·) b c) :
    SymmGen (· ≤ ·) a b ↔ SymmGen (· ≤ ·) a c :=
  AntisymmRel.rfl.symmGen_congr h

end SymmGen

section Prod

variable (α β) [Preorder α] [Preorder β]

namespace Antisymmetrization

/-- The antisymmetrization of a product preorder is order isomorphic
to the product of antisymmetrizations. -/
/-
**Antisymmetrization.prodEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Antisymmetrization`。
形式化陈述：prodEquiv : Antisymmetrization (α × β) (· <= ·) ≃o Antisymmetrization α (·
 <= ·) × Antisymmetrization β (· <= ·) where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instIsPreorderLe`：∀ {α : Type u} [inst : Preorder α], IsPreorder α fun x
1 x2 => x1 ≤ x2

--- 原说明 ---
The antisymmetrization of a product preorder is order isomorphic
to the product of antisymmetrizations.
-/
def prodEquiv : Antisymmetrization (α × β) (· ≤ ·) ≃o
    Antisymmetrization α (· ≤ ·) × Antisymmetrization β (· ≤ ·) where
  toFun := Quotient.lift (fun ab ↦ (⟦ab.1⟧, ⟦ab.2⟧)) fun ab₁ ab₂ h ↦
    Prod.ext (Quotient.sound ⟨h.1.1, h.2.1⟩) (Quotient.sound ⟨h.1.2, h.2.2⟩)
  invFun := Function.uncurry <| Quotient.lift₂ (fun a b ↦ ⟦(a, b)⟧)
    fun a₁ b₁ a₂ b₂ h₁ h₂ ↦ Quotient.sound ⟨⟨h₁.1, h₂.1⟩, h₁.2, h₂.2⟩
  left_inv := by rintro ⟨_⟩; rfl
  right_inv := by rintro ⟨⟨_⟩, ⟨_⟩⟩; rfl
  map_rel_iff' := by rintro ⟨_⟩ ⟨_⟩; rfl
/-
**Antisymmetrization.prodEquiv_apply_mk** 是 Mathlib 中的一个定理，位于命名空间 `Antisymmetriz
ation`。
形式化陈述：∀ (α : Type u_1) (β : Type u_2) [inst : Preorder α] [inst_1 : Preorder β] 
{ab : α × β},   (Antisymmetrization.prodEquiv α β) ⟦ab⟧ = (⟦ab.1⟧, ⟦ab.2⟧)
参数：α : Type u_1；β : Type u_2；Antisymmetrization.prodEquiv α β；⟦ab.1⟧, ⟦ab.2⟧。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsPreorderLe`：∀ {α : Type u} [inst : Preorder α], IsPreorder α fun x
1 x2 => x1 ≤ x2
-/
@[simp] lemma prodEquiv_apply_mk {ab} : prodEquiv α β ⟦ab⟧ = (⟦ab.1⟧, ⟦ab.2⟧) := rfl
/-
**Antisymmetrization.prodEquiv_symm_apply_mk** 是 Mathlib 中的一个定理，位于命名空间 `Antisymm
etrization`。
形式化陈述：∀ (α : Type u_1) (β : Type u_2) [inst : Preorder α] [inst_1 : Preorder β] 
{a : α} {b : β},   (Antisymmetrization.prodEquiv α β).symm (⟦a⟧, ⟦b⟧) = ⟦(a, b)⟧
参数：α : Type u_1；β : Type u_2；Antisymmetrization.prodEquiv α β；⟦a⟧, ⟦b⟧；a, b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsPreorderLe`：∀ {α : Type u} [inst : Preorder α], IsPreorder α fun x
1 x2 => x1 ≤ x2
-/
@[simp] lemma prodEquiv_symm_apply_mk {a b} : (prodEquiv α β).symm (⟦a⟧, ⟦b⟧) = ⟦(a, b)⟧ := rfl

end Antisymmetrization

end Prod

