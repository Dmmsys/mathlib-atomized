/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.SetLike.Basic
public import Mathlib.Order.ModularLattice
public import Mathlib.Order.SuccPred.Basic
public import Mathlib.Order.WellFounded
public import Mathlib.Tactic.Nontriviality
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed
public import Mathlib.Tactic.Attr.Core

/-!
# Atoms, Coatoms, and Simple Lattices

This module defines atoms, which are minimal non-`⊥` elements in bounded lattices, simple lattices,
which are lattices with only two elements, and related ideas.

## Main definitions

### Atoms and Coatoms
* `IsAtom a` indicates that the only element below `a` is `⊥`.
* `IsCoatom a` indicates that the only element above `a` is `⊤`.

### Atomic and Atomistic Lattices
* `IsAtomic` indicates that every element other than `⊥` is above an atom.
* `IsCoatomic` indicates that every element other than `⊤` is below a coatom.
* `IsAtomistic` indicates that every element is the `sSup` of a set of atoms.
* `IsCoatomistic` indicates that every element is the `sInf` of a set of coatoms.
* `IsStronglyAtomic` indicates that for all `a < b`, there is some `x` with `a ⋖ x ≤ b`.
* `IsStronglyCoatomic` indicates that for all `a < b`, there is some `x` with `a ≤ x ⋖ b`.

### Simple Lattices
* `IsSimpleOrder` indicates that an order has only two unique elements, `⊥` and `⊤`.
* `IsSimpleOrder.boundedOrder`
* `IsSimpleOrder.distribLattice`
* Given an instance of `IsSimpleOrder`, we provide the following definitions. These are not
  made global instances as they contain data :
  * `IsSimpleOrder.booleanAlgebra`
  * `IsSimpleOrder.completeLattice`
  * `IsSimpleOrder.completeBooleanAlgebra`

## Main results
* `isAtom_dual_iff_isCoatom` and `isCoatom_dual_iff_isAtom` express the (definitional) duality
  of `IsAtom` and `IsCoatom`.
* `isSimpleOrder_iff_isAtom_top` and `isSimpleOrder_iff_isCoatom_bot` express the
  connection between atoms, coatoms, and simple lattices
* `IsCompl.isAtom_iff_isCoatom` and `IsCompl.isCoatom_if_isAtom`: In a modular
  bounded lattice, a complement of an atom is a coatom and vice versa.
* `isAtomic_iff_isCoatomic`: A modular complemented lattice is atomic iff it is coatomic.

-/

@[expose] public section

open Order

variable {ι : Sort*} {α β : Type*}

section Atoms

section IsAtom

section Preorder

variable [Preorder α] [OrderBot α] {a b x : α}

/-- An atom of an `OrderBot` is an element with no other element between it and `⊥`,
  which is not `⊥`. -/
/-
**IsAtom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsAtom (a : α) : Prop
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An atom of an `OrderBot` is an element with no other element between it and `⊥`,
  which is not `⊥`.
-/
def IsAtom (a : α) : Prop :=
  a ≠ ⊥ ∧ ∀ b, b < a → b = ⊥
/-
**IsAtom.Iic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsAtom.Iic (ha : IsAtom a) (hax : a <= x) : IsAtom (⟨a, hax⟩ : Set.Iic x)
参数：ha : IsAtom a；hax : a <= x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.mk_eq_mk`：mk_eq_mk {a h a' h'} : @mk α p a h = @mk α p a' h' ↔ a
 = a'
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsAtom.Iic (ha : IsAtom a) (hax : a ≤ x) : IsAtom (⟨a, hax⟩ : Set.Iic x) :=
  ⟨fun con => ha.1 (Subtype.mk_eq_mk.1 con), fun ⟨b, _⟩ hba => Subtype.mk_eq_mk.2 (ha.2 b hba)⟩
/-
**IsAtom.of_isAtom_coe_Iic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsAtom.of_isAtom_coe_Iic {a : Set.Iic x} (ha : IsAtom a) : IsAtom (a : α)
参数：ha : IsAtom a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Subtype.mk_eq_mk`：mk_eq_mk {a h a' h'} : @mk α p a h = @mk α p a' h' ↔ a
 = a'
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsAtom.of_isAtom_coe_Iic {a : Set.Iic x} (ha : IsAtom a) : IsAtom (a : α) :=
  ⟨fun con => ha.1 (Subtype.ext con), fun b hba =>
    Subtype.mk_eq_mk.1 (ha.2 ⟨b, hba.le.trans a.prop⟩ hba)⟩
/-
**isAtom_iff_le_of_ge** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isAtom_iff_le_of_ge : IsAtom a ↔ a != ⊥ ∧ forall b != ⊥, b <= a -> a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_imp_comm`：not_imp_comm : ¬a -> b ↔ ¬b -> a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isAtom_iff_le_of_ge : IsAtom a ↔ a ≠ ⊥ ∧ ∀ b ≠ ⊥, b ≤ a → a ≤ b :=
  and_congr Iff.rfl <|
    forall_congr' fun b => by
      simp only [Ne, @not_imp_comm (b = ⊥), Classical.not_imp, lt_iff_le_not_ge]
/-
**IsAtom.ne_bot** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsAtom.ne_bot (ha : IsAtom a) : a != ⊥
参数：ha : IsAtom a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma IsAtom.ne_bot (ha : IsAtom a) : a ≠ ⊥ := ha.1

end Preorder

section PartialOrder

variable [PartialOrder α] [OrderBot α] {a b x : α}

/-
**IsAtom.lt_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsAtom.lt_iff (h : IsAtom a) : x < a ↔ x = ⊥
参数：h : IsAtom a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsAtom.lt_iff (h : IsAtom a) : x < a ↔ x = ⊥ :=
  ⟨h.2 x, fun hx => hx.symm ▸ h.1.bot_lt⟩
/-
**IsAtom.le_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsAtom.le_iff (h : IsAtom a) : x <= a ↔ x = ⊥ ∨ x = a
参数：h : IsAtom a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `le_iff_lt_or_eq`：le_iff_lt_or_eq : a <= b ↔ a < b ∨ a = b
· 使用定理 `IsAtom.lt_iff`：IsAtom.lt_iff (h : IsAtom a) : x < a ↔ x = ⊥
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem IsAtom.le_iff (h : IsAtom a) : x ≤ a ↔ x = ⊥ ∨ x = a := by rw [le_iff_lt_or_eq, h.lt_iff]
/-
**IsAtom.bot_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsAtom.bot_lt (h : IsAtom a) : ⊥ < a
参数：h : IsAtom a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsAtom.lt_iff`：IsAtom.lt_iff (h : IsAtom a) : x < a ↔ x = ⊥
-/
lemma IsAtom.bot_lt (h : IsAtom a) : ⊥ < a :=
  h.lt_iff.mpr rfl
/-
**IsAtom.le_iff_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsAtom.le_iff_eq (ha : IsAtom a) (hb : b != ⊥) : b <= a ↔ b = a
参数：ha : IsAtom a；hb : b != ⊥。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `IsAtom.le_iff`：IsAtom.le_iff (h : IsAtom a) : x <= a ↔ x = ⊥ ∨ x = a
· 使用定理 `or_iff_right`：∀ {a b : Prop}, ¬a → (a ∨ b ↔ b)
-/
lemma IsAtom.le_iff_eq (ha : IsAtom a) (hb : b ≠ ⊥) : b ≤ a ↔ b = a :=
  ha.le_iff.trans <| or_iff_right hb
/-
**IsAtom.ne_iff_eq_bot** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsAtom.ne_iff_eq_bot (ha : IsAtom a) (hba : b <= a) : b != a ↔ b = ⊥ where
 mp
参数：ha : IsAtom a；hba : b <= a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsAtom.le_iff`：IsAtom.le_iff (h : IsAtom a) : x <= a ↔ x = ⊥ ∨ x = a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用引理 `IsAtom.ne_bot`：IsAtom.ne_bot (ha : IsAtom a) : a != ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma IsAtom.ne_iff_eq_bot (ha : IsAtom a) (hba : b ≤ a) : b ≠ a ↔ b = ⊥ where
  mp := (ha.le_iff.1 hba).resolve_right
  mpr := by rintro rfl; exact ha.ne_bot.symm
/-
**IsAtom.ne_bot_iff_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsAtom.ne_bot_iff_eq (ha : IsAtom a) (hba : b <= a) : b != ⊥ ↔ b = a
参数：ha : IsAtom a；hba : b <= a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Iff.not_right`：Iff.not_right (h : ¬a ↔ b) : a ↔ ¬b
· 使用引理 `IsAtom.ne_iff_eq_bot`：IsAtom.ne_iff_eq_bot (ha : IsAtom a) (hba : b <= a
) : b != a ↔ b = ⊥ where mp
-/
lemma IsAtom.ne_bot_iff_eq (ha : IsAtom a) (hba : b ≤ a) : b ≠ ⊥ ↔ b = a :=
  (ha.ne_iff_eq_bot hba).not_right.symm
/-
**IsAtom.Iic_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsAtom.Iic_eq (h : IsAtom a) : Set.Iic a = {⊥, a}
参数：h : IsAtom a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `IsAtom.le_iff`：IsAtom.le_iff (h : IsAtom a) : x <= a ↔ x = ⊥ ∨ x = a
-/
theorem IsAtom.Iic_eq (h : IsAtom a) : Set.Iic a = {⊥, a} :=
  Set.ext fun _ => h.le_iff
/-
**Set.Iio_eq_singleton_bot_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Set.Iio_eq_singleton_bot_iff : Iio a = {⊥} ↔ IsAtom a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Set.Iio_eq_singleton_bot_iff : Iio a = {⊥} ↔ IsAtom a := by
  simp [IsAtom, superset_antisymm_iff, bot_lt_iff_ne_bot]

@[simp]
/-
**bot_covBy_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bot_covBy_iff : ⊥ ⋖ a ↔ IsAtom a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem bot_covBy_iff : ⊥ ⋖ a ↔ IsAtom a := by
  simp only [CovBy, bot_lt_iff_ne_bot, IsAtom, not_imp_not]

alias ⟨CovBy.is_atom, IsAtom.bot_covBy⟩ := bot_covBy_iff

end PartialOrder

section Frame
variable [Frame α] {f : ι → α} {s : Set α} {a : α}

/-
**IsAtom.le_iSup** 是 Mathlib 中的一个定理，位于命名空间 `IsAtom`。
形式化陈述：∀ {ι : Sort u_1} {α : Type u_2} [inst : Order.Frame α] {f : ι → α} {a : α}
, IsAtom a → (a ≤ iSup f ↔ ∃ i, a ≤ f i)
参数：a ≤ iSup f ↔ ∃ i, a ≤ f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_not_not`：of_not_not {a : Prop} : ¬¬a -> a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `disjoint_iSup_iff`：∀ {α : Type u} {ι : Sort w} [inst : Order.Frame α] {a
 : α} {f : ι → α},   Disjoint a (⨆ i, f i) ↔ ∀ (i : ι), Disjoint a (f i)
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_iff_eq_or_lt`：le_iff_eq_or_lt : a <= b ↔ a = b ∨ a < b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
-/
protected lemma IsAtom.le_iSup (ha : IsAtom a) : a ≤ iSup f ↔ ∃ i, a ≤ f i := by
  refine ⟨?_, fun ⟨i, hi⟩ => le_trans hi (le_iSup _ _)⟩
  change (a ≤ ⨆ i, f i) → _
  refine fun h => of_not_not fun ha' => ?_
  push Not at ha'
  have ha'' : Disjoint a (⨆ i, f i) :=
    disjoint_iSup_iff.2 fun i => fun x hxa hxf => le_bot_iff.2 <| of_not_not fun hx =>
      have hxa : x < a := (le_iff_eq_or_lt.1 hxa).resolve_left (by rintro rfl; exact ha' _ hxf)
      hx (ha.2 _ hxa)
  obtain rfl := le_bot_iff.1 (ha'' le_rfl h)
  exact ha.1 rfl
/-
**IsAtom.le_sSup** 是 Mathlib 中的一个定理，位于命名空间 `IsAtom`。
形式化陈述：∀ {α : Type u_2} [inst : Order.Frame α] {s : Set α} {a : α}, IsAtom a → (a
 ≤ sSup s ↔ ∃ b ∈ s, a ≤ b)
参数：a ≤ sSup s ↔ ∃ b ∈ s, a ≤ b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sSup_eq_iSup'`：sSup_eq_iSup' (s : Set α) : sSup s = ⨆ a : s, (a : α)
· 使用定理 `IsAtom.le_iSup`：∀ {ι : Sort u_1} {α : Type u_2} [inst : Order.Frame α] {
f : ι → α} {a : α}, IsAtom a → (a ≤ iSup f ↔ ∃ i, a ≤ f i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected lemma IsAtom.le_sSup (ha : IsAtom a) : a ≤ sSup s ↔ ∃ b ∈ s, a ≤ b := by
  simp [sSup_eq_iSup', ha.le_iSup]

end Frame
end IsAtom

section IsCoatom

section Preorder

variable [Preorder α]

/-- A coatom of an `OrderTop` is an element with no other element between it and `⊤`,
  which is not `⊤`. -/
/-
**IsCoatom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsCoatom [OrderTop α] (a : α) : Prop
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A coatom of an `OrderTop` is an element with no other element between it and `⊤`
,
  which is not `⊤`.
-/
def IsCoatom [OrderTop α] (a : α) : Prop :=
  a ≠ ⊤ ∧ ∀ b, a < b → b = ⊤

@[simp]
/-
**isCoatom_dual_iff_isAtom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCoatom_dual_iff_isAtom [OrderBot α] {a : α} : IsCoatom (OrderDual.toDual
 a) ↔ IsAtom a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isCoatom_dual_iff_isAtom [OrderBot α] {a : α} :
    IsCoatom (OrderDual.toDual a) ↔ IsAtom a :=
  Iff.rfl

@[simp]
/-
**isAtom_dual_iff_isCoatom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isAtom_dual_iff_isCoatom [OrderTop α] {a : α} : IsAtom (OrderDual.toDual a
) ↔ IsCoatom a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isAtom_dual_iff_isCoatom [OrderTop α] {a : α} :
    IsAtom (OrderDual.toDual a) ↔ IsCoatom a :=
  Iff.rfl

alias ⟨_, IsAtom.dual⟩ := isCoatom_dual_iff_isAtom

alias ⟨_, IsCoatom.dual⟩ := isAtom_dual_iff_isCoatom

variable [OrderTop α] {a x : α}
/-
**IsCoatom.Ici** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCoatom.Ici (ha : IsCoatom a) (hax : x <= a) : IsCoatom (⟨a, hax⟩ : Set.I
ci x)
参数：ha : IsCoatom a；hax : x <= a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAtom.Iic`：IsAtom.Iic (ha : IsAtom a) (hax : a <= x) : IsAtom (⟨a, hax⟩
 : Set.Iic x)
· 使用定理 `IsCoatom.dual`：∀ {α : Type u_2} [inst : Preorder α] [inst_1 : OrderTop α
] {a : α}, IsCoatom a → IsAtom (OrderDual.toDual a)
-/
theorem IsCoatom.Ici (ha : IsCoatom a) (hax : x ≤ a) : IsCoatom (⟨a, hax⟩ : Set.Ici x) :=
  ha.dual.Iic hax
/-
**IsCoatom.of_isCoatom_coe_Ici** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCoatom.of_isCoatom_coe_Ici {a : Set.Ici x} (ha : IsCoatom a) : IsCoatom 
(a : α)
参数：ha : IsCoatom a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAtom.of_isAtom_coe_Iic`：IsAtom.of_isAtom_coe_Iic {a : Set.Iic x} (ha :
 IsAtom a) : IsAtom (a : α)
-/
theorem IsCoatom.of_isCoatom_coe_Ici {a : Set.Ici x} (ha : IsCoatom a) : IsCoatom (a : α) :=
  @IsAtom.of_isAtom_coe_Iic αᵒᵈ _ _ x a ha
/-
**isCoatom_iff_ge_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCoatom_iff_ge_of_le : IsCoatom a ↔ a != ⊤ ∧ forall b != ⊤, a <= b -> b <
= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isAtom_iff_le_of_ge`：isAtom_iff_le_of_ge : IsAtom a ↔ a != ⊥ ∧ forall b 
!= ⊥, b <= a -> a <= b
-/
theorem isCoatom_iff_ge_of_le : IsCoatom a ↔ a ≠ ⊤ ∧ ∀ b ≠ ⊤, a ≤ b → b ≤ a :=
  isAtom_iff_le_of_ge (α := αᵒᵈ)
/-
**IsCoatom.ne_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsCoatom.ne_top (ha : IsCoatom a) : a != ⊤
参数：ha : IsCoatom a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma IsCoatom.ne_top (ha : IsCoatom a) : a ≠ ⊤ := ha.1

end Preorder

section PartialOrder

variable [PartialOrder α] [OrderTop α] {a b x : α}

/-
**IsCoatom.lt_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCoatom.lt_iff (h : IsCoatom a) : a < x ↔ x = ⊤
参数：h : IsCoatom a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAtom.lt_iff`：IsAtom.lt_iff (h : IsAtom a) : x < a ↔ x = ⊥
· 使用定理 `IsCoatom.dual`：∀ {α : Type u_2} [inst : Preorder α] [inst_1 : OrderTop α
] {a : α}, IsCoatom a → IsAtom (OrderDual.toDual a)
-/
theorem IsCoatom.lt_iff (h : IsCoatom a) : a < x ↔ x = ⊤ :=
  h.dual.lt_iff
/-
**IsCoatom.le_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCoatom.le_iff (h : IsCoatom a) : a <= x ↔ x = ⊤ ∨ x = a
参数：h : IsCoatom a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAtom.le_iff`：IsAtom.le_iff (h : IsAtom a) : x <= a ↔ x = ⊥ ∨ x = a
· 使用定理 `IsCoatom.dual`：∀ {α : Type u_2} [inst : Preorder α] [inst_1 : OrderTop α
] {a : α}, IsCoatom a → IsAtom (OrderDual.toDual a)
-/
theorem IsCoatom.le_iff (h : IsCoatom a) : a ≤ x ↔ x = ⊤ ∨ x = a :=
  h.dual.le_iff
/-
**IsCoatom.lt_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsCoatom.lt_top (h : IsCoatom a) : a < ⊤
参数：h : IsCoatom a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsCoatom.lt_iff`：IsCoatom.lt_iff (h : IsCoatom a) : a < x ↔ x = ⊤
-/
lemma IsCoatom.lt_top (h : IsCoatom a) : a < ⊤ :=
  h.lt_iff.mpr rfl
/-
**IsCoatom.le_iff_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsCoatom.le_iff_eq (ha : IsCoatom a) (hb : b != ⊤) : a <= b ↔ b = a
参数：ha : IsCoatom a；hb : b != ⊤。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsAtom.le_iff_eq`：IsAtom.le_iff_eq (ha : IsAtom a) (hb : b != ⊥) : b <= 
a ↔ b = a
· 使用定理 `IsCoatom.dual`：∀ {α : Type u_2} [inst : Preorder α] [inst_1 : OrderTop α
] {a : α}, IsCoatom a → IsAtom (OrderDual.toDual a)
-/
lemma IsCoatom.le_iff_eq (ha : IsCoatom a) (hb : b ≠ ⊤) : a ≤ b ↔ b = a := ha.dual.le_iff_eq hb
/-
**IsCoatom.ne_iff_eq_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsCoatom.ne_iff_eq_top (ha : IsCoatom a) (hab : a <= b) : b != a ↔ b = ⊤ w
here mp
参数：ha : IsCoatom a；hab : a <= b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsCoatom.le_iff`：IsCoatom.le_iff (h : IsCoatom a) : a <= x ↔ x = ⊤ ∨ x =
 a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用引理 `IsCoatom.ne_top`：IsCoatom.ne_top (ha : IsCoatom a) : a != ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma IsCoatom.ne_iff_eq_top (ha : IsCoatom a) (hab : a ≤ b) : b ≠ a ↔ b = ⊤ where
  mp := (ha.le_iff.1 hab).resolve_right
  mpr := by rintro rfl; exact ha.ne_top.symm
/-
**IsCoatom.ne_top_iff_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsCoatom.ne_top_iff_eq (ha : IsCoatom a) (hab : a <= b) : b != ⊤ ↔ b = a
参数：ha : IsCoatom a；hab : a <= b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Iff.not_right`：Iff.not_right (h : ¬a ↔ b) : a ↔ ¬b
· 使用引理 `IsCoatom.ne_iff_eq_top`：IsCoatom.ne_iff_eq_top (ha : IsCoatom a) (hab : 
a <= b) : b != a ↔ b = ⊤ where mp
-/
lemma IsCoatom.ne_top_iff_eq (ha : IsCoatom a) (hab : a ≤ b) : b ≠ ⊤ ↔ b = a :=
  (ha.ne_iff_eq_top hab).not_right.symm
/-
**IsCoatom.Ici_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCoatom.Ici_eq (h : IsCoatom a) : Set.Ici a = {⊤, a}
参数：h : IsCoatom a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAtom.Iic_eq`：IsAtom.Iic_eq (h : IsAtom a) : Set.Iic a = {⊥, a}
· 使用定理 `IsCoatom.dual`：∀ {α : Type u_2} [inst : Preorder α] [inst_1 : OrderTop α
] {a : α}, IsCoatom a → IsAtom (OrderDual.toDual a)
-/
theorem IsCoatom.Ici_eq (h : IsCoatom a) : Set.Ici a = {⊤, a} :=
  h.dual.Iic_eq
/-
**Set.Ioi_eq_singleton_top_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Set.Ioi_eq_singleton_top_iff : Ioi a = {⊤} ↔ IsCoatom a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Set.Ioi_eq_singleton_top_iff : Ioi a = {⊤} ↔ IsCoatom a := by
  simp [IsCoatom, superset_antisymm_iff, lt_top_iff_ne_top]

@[simp]
/-
**covBy_top_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：covBy_top_iff : a ⋖ ⊤ ↔ IsCoatom a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `toDual_covBy_toDual_iff`：toDual_covBy_toDual_iff : toDual b ⋖ toDual a ↔
 a ⋖ b
· 使用定理 `bot_covBy_iff`：bot_covBy_iff : ⊥ ⋖ a ↔ IsAtom a
-/
theorem covBy_top_iff : a ⋖ ⊤ ↔ IsCoatom a :=
  toDual_covBy_toDual_iff.symm.trans bot_covBy_iff

alias ⟨CovBy.isCoatom, IsCoatom.covBy_top⟩ := covBy_top_iff

namespace SetLike

variable {A B : Type*} [PartialOrder A] [SetLike A B] [IsConcreteLE A B]

/-
**SetLike.isAtom_iff** 是 Mathlib 中的一个定理，位于命名空间 `SetLike`。
形式化陈述：isAtom_iff [OrderBot A] {K : A} : IsAtom K ↔ K != ⊥ ∧ forall H g, H <= K -
> g ∉ H -> g in K -> H = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isAtom_iff [OrderBot A] {K : A} :
    IsAtom K ↔ K ≠ ⊥ ∧ ∀ H g, H ≤ K → g ∉ H → g ∈ K → H = ⊥ := by
  simp_rw [IsAtom, lt_iff_le_not_ge, SetLike.not_le_iff_exists,
    and_comm (a := _ ≤ _), and_imp, exists_imp, ← and_imp, and_comm]
/-
**SetLike.isCoatom_iff** 是 Mathlib 中的一个定理，位于命名空间 `SetLike`。
形式化陈述：isCoatom_iff [OrderTop A] {K : A} : IsCoatom K ↔ K != ⊤ ∧ forall H g, K <=
 H -> g ∉ K -> g in H -> H = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isCoatom_iff [OrderTop A] {K : A} :
    IsCoatom K ↔ K ≠ ⊤ ∧ ∀ H g, K ≤ H → g ∉ K → g ∈ H → H = ⊤ := by
  simp_rw [IsCoatom, lt_iff_le_not_ge, SetLike.not_le_iff_exists,
    and_comm (a := _ ≤ _), and_imp, exists_imp, ← and_imp, and_comm]
/-
**SetLike.covBy_iff** 是 Mathlib 中的一个定理，位于命名空间 `SetLike`。
形式化陈述：covBy_iff {K L : A} : K ⋖ L ↔ K < L ∧ forall H g, K <= H -> H <= L -> g ∉ 
K -> g in H -> H = L
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₁`：contrapose_iff₁ {p q : Prop} 
: (¬ p ↔ ¬ q) -> (p ↔ q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `lt_iff_le_not_ge`：lt_iff_le_not_ge : a < b ↔ a <= b ∧ ¬b <= a
· 使用定理 `lt_iff_le_and_ne`：lt_iff_le_and_ne : a < b ↔ a <= b ∧ a != b
· 使用定理 `and_and_and_comm`：∀ {a b c d : Prop}, (a ∧ b) ∧ c ∧ d ↔ (a ∧ c) ∧ b ∧ d
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem covBy_iff {K L : A} :
    K ⋖ L ↔ K < L ∧ ∀ H g, K ≤ H → H ≤ L → g ∉ K → g ∈ H → H = L := by
  refine and_congr_right fun _ ↦ forall_congr' fun H ↦ ?_
  contrapose!
  rw [lt_iff_le_not_ge, lt_iff_le_and_ne, and_and_and_comm]
  simp_rw [exists_and_left, and_assoc, and_congr_right_iff, ← and_assoc, and_comm, exists_and_left,
    SetLike.not_le_iff_exists, and_comm, implies_true]

/-- Dual variant of `SetLike.covBy_iff` -/
/-
**SetLike.covBy_iff'** 是 Mathlib 中的一个定理，位于命名空间 `SetLike`。
形式化陈述：covBy_iff' {K L : A} : K ⋖ L ↔ K < L ∧ forall H g, K <= H -> H <= L -> g ∉
 H -> g in L -> H = K
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `lt_iff_le_and_ne`：lt_iff_le_and_ne : a < b ↔ a <= b ∧ a != b
· 使用引理 `lt_iff_le_not_ge`：lt_iff_le_not_ge : a < b ↔ a <= b ∧ ¬b <= a
· 使用定理 `and_and_and_comm`：∀ {a b c d : Prop}, (a ∧ b) ∧ c ∧ d ↔ (a ∧ c) ∧ b ∧ d
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
Dual variant of `SetLike.covBy_iff`
-/
theorem covBy_iff' {K L : A} :
    K ⋖ L ↔ K < L ∧ ∀ H g, K ≤ H → H ≤ L → g ∉ H → g ∈ L → H = K := by
  refine and_congr_right fun _ ↦ forall_congr' fun H ↦ not_iff_not.mp ?_
  push Not
  rw [lt_iff_le_and_ne, lt_iff_le_not_ge, and_and_and_comm]
  simp_rw [exists_and_left, and_assoc, and_congr_right_iff, ← and_assoc, and_comm, exists_and_left,
    SetLike.not_le_iff_exists, ne_comm, implies_true]

end SetLike

end PartialOrder

section Coframe
variable [Coframe α] {f : ι → α} {s : Set α} {a : α}

/-
**IsCoatom.iInf_le** 是 Mathlib 中的一个定理，位于命名空间 `IsCoatom`。
形式化陈述：∀ {ι : Sort u_1} {α : Type u_2} [inst : Order.Coframe α] {f : ι → α} {a : 
α}, IsCoatom a → (iInf f ≤ a ↔ ∃ i, f i ≤ a)
参数：iInf f ≤ a ↔ ∃ i, f i ≤ a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAtom.le_iSup`：∀ {ι : Sort u_1} {α : Type u_2} [inst : Order.Frame α] {
f : ι → α} {a : α}, IsAtom a → (a ≤ iSup f ↔ ∃ i, a ≤ f i)
-/
protected lemma IsCoatom.iInf_le (ha : IsCoatom a) : iInf f ≤ a ↔ ∃ i, f i ≤ a :=
  IsAtom.le_iSup (α := αᵒᵈ) ha
/-
**IsCoatom.sInf_le** 是 Mathlib 中的一个定理，位于命名空间 `IsCoatom`。
形式化陈述：∀ {α : Type u_2} [inst : Order.Coframe α] {s : Set α} {a : α}, IsCoatom a 
→ (sInf s ≤ a ↔ ∃ b ∈ s, b ≤ a)
参数：sInf s ≤ a ↔ ∃ b ∈ s, b ≤ a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sInf_eq_iInf'`：∀ {α : Type u_1} [inst : InfSet α] (s : Set α), sInf s = 
⨅ a, ↑a
· 使用定理 `IsCoatom.iInf_le`：∀ {ι : Sort u_1} {α : Type u_2} [inst : Order.Coframe 
α] {f : ι → α} {a : α}, IsCoatom a → (iInf f ≤ a ↔ ∃ i, f i ≤ a)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected lemma IsCoatom.sInf_le (ha : IsCoatom a) : sInf s ≤ a ↔ ∃ b ∈ s, b ≤ a := by
  simp [sInf_eq_iInf', ha.iInf_le]

end Coframe
end IsCoatom

section PartialOrder

variable [PartialOrder α] {a b : α}

@[simp]
/-
**Set.Ici.isAtom_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Ici.isAtom_iff {b : Set.Ici a} : IsAtom b ↔ a ⋖ b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `bot_covBy_iff`：bot_covBy_iff : ⊥ ⋖ a ↔ IsAtom a
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Set.OrdConnected.apply_covBy_apply_iff`：Set.OrdConnected.apply_covBy_app
ly_iff (f : α ↪o β) (h : (range f).OrdConnected) : f a ⋖ f b ↔ a ⋖ b
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
-/
theorem Set.Ici.isAtom_iff {b : Set.Ici a} : IsAtom b ↔ a ⋖ b := by
  rw [← bot_covBy_iff]
  refine (Set.OrdConnected.apply_covBy_apply_iff (OrderEmbedding.subtype fun c => a ≤ c) ?_).symm
  simpa only [OrderEmbedding.coe_subtype, Subtype.range_coe_subtype] using! Set.ordConnected_Ici

@[simp]
/-
**Set.Iic.isCoatom_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Iic.isCoatom_iff {a : Set.Iic b} : IsCoatom a ↔ ↑a ⋖ b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `covBy_top_iff`：covBy_top_iff : a ⋖ ⊤ ↔ IsCoatom a
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Set.OrdConnected.apply_covBy_apply_iff`：Set.OrdConnected.apply_covBy_app
ly_iff (f : α ↪o β) (h : (range f).OrdConnected) : f a ⋖ f b ↔ a ⋖ b
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `Set.ordConnected_Iic`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, (Set
.Iic a).OrdConnected
-/
theorem Set.Iic.isCoatom_iff {a : Set.Iic b} : IsCoatom a ↔ ↑a ⋖ b := by
  rw [← covBy_top_iff]
  refine (Set.OrdConnected.apply_covBy_apply_iff (OrderEmbedding.subtype fun c => c ≤ b) ?_).symm
  simpa only [OrderEmbedding.coe_subtype, Subtype.range_coe_subtype] using! Set.ordConnected_Iic
/-
**covBy_iff_atom_Ici** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：covBy_iff_atom_Ici (h : a <= b) : a ⋖ b ↔ IsAtom (⟨b, h⟩ : Set.Ici a)
参数：h : a <= b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem covBy_iff_atom_Ici (h : a ≤ b) : a ⋖ b ↔ IsAtom (⟨b, h⟩ : Set.Ici a) := by simp
/-
**covBy_iff_coatom_Iic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：covBy_iff_coatom_Iic (h : a <= b) : a ⋖ b ↔ IsCoatom (⟨a, h⟩ : Set.Iic b)
参数：h : a <= b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem covBy_iff_coatom_Iic (h : a ≤ b) : a ⋖ b ↔ IsCoatom (⟨a, h⟩ : Set.Iic b) := by simp

end PartialOrder

section SemilatticeInf
variable [SemilatticeInf α] [OrderBot α] {a b : α}

/-
**IsAtom.not_disjoint_iff_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsAtom.not_disjoint_iff_le (ha : IsAtom a) : ¬ Disjoint a b ↔ a <= b
参数：ha : IsAtom a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_iff`：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inf_eq_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b =
 a ↔ a ≤ b
· 使用引理 `IsAtom.ne_bot_iff_eq`：IsAtom.ne_bot_iff_eq (ha : IsAtom a) (hba : b <= a
) : b != ⊥ ↔ b = a
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
lemma IsAtom.not_disjoint_iff_le (ha : IsAtom a) : ¬ Disjoint a b ↔ a ≤ b := by
  rw [disjoint_iff, ← inf_eq_left]; exact ha.ne_bot_iff_eq inf_le_left
/-
**IsAtom.not_le_iff_disjoint** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsAtom.not_le_iff_disjoint (ha : IsAtom a) : ¬ a <= b ↔ Disjoint a b
参数：ha : IsAtom a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Iff.not_right`：Iff.not_right (h : ¬a ↔ b) : a ↔ ¬b
· 使用引理 `IsAtom.not_disjoint_iff_le`：IsAtom.not_disjoint_iff_le (ha : IsAtom a) :
 ¬ Disjoint a b ↔ a <= b
-/
lemma IsAtom.not_le_iff_disjoint (ha : IsAtom a) : ¬ a ≤ b ↔ Disjoint a b :=
  ha.not_disjoint_iff_le.not_right.symm
/-
**IsAtom.disjoint_of_ne** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsAtom.disjoint_of_ne (ha : IsAtom a) (hb : IsAtom b) (hab : a != b) : Dis
joint a b
参数：ha : IsAtom a；hb : IsAtom b；hab : a != b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `IsAtom.not_le_iff_disjoint`：IsAtom.not_le_iff_disjoint (ha : IsAtom a) :
 ¬ a <= b ↔ Disjoint a b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsAtom.le_iff`：IsAtom.le_iff (h : IsAtom a) : x <= a ↔ x = ⊥ ∨ x = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用引理 `IsAtom.ne_bot`：IsAtom.ne_bot (ha : IsAtom a) : a != ⊥
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma IsAtom.disjoint_of_ne (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) : Disjoint a b := by
  simp [← ha.not_le_iff_disjoint, hb.le_iff, hab, ha.ne_bot]

end SemilatticeInf

section SemilatticeSup
variable [SemilatticeSup α] [OrderTop α] {a b : α}

/-
**IsCoatom.not_codisjoint_iff_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsCoatom.not_codisjoint_iff_le (ha : IsCoatom a) : ¬ Codisjoint a b ↔ b <=
 a
参数：ha : IsCoatom a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `codisjoint_iff`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : Ord
erTop α] {a b : α}, Codisjoint a b ↔ a ⊔ b = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sup_eq_left`：sup_eq_left : a ⊔ b = a ↔ b <= a
· 使用引理 `IsCoatom.ne_top_iff_eq`：IsCoatom.ne_top_iff_eq (ha : IsCoatom a) (hab : 
a <= b) : b != ⊤ ↔ b = a
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
-/
lemma IsCoatom.not_codisjoint_iff_le (ha : IsCoatom a) : ¬ Codisjoint a b ↔ b ≤ a := by
  rw [codisjoint_iff, ← sup_eq_left]; exact ha.ne_top_iff_eq le_sup_left
/-
**IsCoatom.not_le_iff_codisjoint** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsCoatom.not_le_iff_codisjoint (ha : IsCoatom a) : ¬ b <= a ↔ Codisjoint a
 b
参数：ha : IsCoatom a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Iff.not_right`：Iff.not_right (h : ¬a ↔ b) : a ↔ ¬b
· 使用引理 `IsCoatom.not_codisjoint_iff_le`：IsCoatom.not_codisjoint_iff_le (ha : IsC
oatom a) : ¬ Codisjoint a b ↔ b <= a
-/
lemma IsCoatom.not_le_iff_codisjoint (ha : IsCoatom a) : ¬ b ≤ a ↔ Codisjoint a b :=
  ha.not_codisjoint_iff_le.not_right.symm
/-
**IsCoatom.codisjoint_of_ne** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsCoatom.codisjoint_of_ne (ha : IsCoatom a) (hb : IsCoatom b) (hab : a != 
b) : Codisjoint a b
参数：ha : IsCoatom a；hb : IsCoatom b；hab : a != b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `IsCoatom.not_le_iff_codisjoint`：IsCoatom.not_le_iff_codisjoint (ha : IsC
oatom a) : ¬ b <= a ↔ Codisjoint a b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsCoatom.le_iff`：IsCoatom.le_iff (h : IsCoatom a) : a <= x ↔ x = ⊤ ∨ x =
 a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用引理 `IsCoatom.ne_top`：IsCoatom.ne_top (ha : IsCoatom a) : a != ⊤
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma IsCoatom.codisjoint_of_ne (ha : IsCoatom a) (hb : IsCoatom b) (hab : a ≠ b) :
    Codisjoint a b := by
  simp [← ha.not_le_iff_codisjoint, hb.le_iff, hab, ha.ne_top]
/-
**IsCoatom.sup_eq_top_of_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCoatom.sup_eq_top_of_ne (ha : IsCoatom a) (hb : IsCoatom b) (hab : a != 
b) : a ⊔ b = ⊤
参数：ha : IsCoatom a；hb : IsCoatom b；hab : a != b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `codisjoint_iff`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : Ord
erTop α] {a b : α}, Codisjoint a b ↔ a ⊔ b = ⊤
· 使用引理 `IsCoatom.codisjoint_of_ne`：IsCoatom.codisjoint_of_ne (ha : IsCoatom a) (
hb : IsCoatom b) (hab : a != b) : Codisjoint a b
-/
theorem IsCoatom.sup_eq_top_of_ne (ha : IsCoatom a) (hb : IsCoatom b) (hab : a ≠ b) : a ⊔ b = ⊤ :=
  codisjoint_iff.1 <| ha.codisjoint_of_ne hb hab

end SemilatticeSup

end Atoms

section Atomic

variable [PartialOrder α] (α)

/-- A lattice is atomic iff every element other than `⊥` has an atom below it. -/
@[mk_iff]
/-
**IsAtomic** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_2) → [inst : PartialOrder α] → [OrderBot α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A lattice is atomic iff every element other than `⊥` has an atom below it.
-/
class IsAtomic [OrderBot α] : Prop where
  /-- Every element other than `⊥` has an atom below it. -/
  eq_bot_or_exists_atom_le : ∀ b : α, b = ⊥ ∨ ∃ a : α, IsAtom a ∧ a ≤ b

/-- A lattice is coatomic iff every element other than `⊤` has a coatom above it. -/
@[mk_iff]
/-
**IsCoatomic** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_2) → [inst : PartialOrder α] → [OrderTop α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A lattice is coatomic iff every element other than `⊤` has a coatom above it.
-/
class IsCoatomic [OrderTop α] : Prop where
  /-- Every element other than `⊤` has an atom above it. -/
  eq_top_or_exists_le_coatom : ∀ b : α, b = ⊤ ∨ ∃ a : α, IsCoatom a ∧ b ≤ a

export IsAtomic (eq_bot_or_exists_atom_le)

export IsCoatomic (eq_top_or_exists_le_coatom)
/-
**IsAtomic.exists_atom** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsAtomic.exists_atom [OrderBot α] [Nontrivial α] [IsAtomic α] : exists a :
 α, IsAtom a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `IsAtomic.eq_bot_or_exists_atom_le`：∀ {α : Type u_2} {inst : PartialOrder
 α} {inst_1 : OrderBot α} [self : IsAtomic α] (b : α),   b = ⊥ ∨ ∃ a, IsAtom a ∧
 a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma IsAtomic.exists_atom [OrderBot α] [Nontrivial α] [IsAtomic α] : ∃ a : α, IsAtom a :=
  have ⟨b, hb⟩ := exists_ne (⊥ : α)
  have ⟨a, ha⟩ := (eq_bot_or_exists_atom_le b).resolve_left hb
  ⟨a, ha.1⟩
/-
**IsCoatomic.exists_coatom** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsCoatomic.exists_coatom [OrderTop α] [Nontrivial α] [IsCoatomic α] : exis
ts a : α, IsCoatom a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `IsCoatomic.eq_top_or_exists_le_coatom`：∀ {α : Type u_2} {inst : PartialO
rder α} {inst_1 : OrderTop α} [self : IsCoatomic α] (b : α),   b = ⊤ ∨ ∃ a, IsCo
atom a ∧ b ≤ a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma IsCoatomic.exists_coatom [OrderTop α] [Nontrivial α] [IsCoatomic α] : ∃ a : α, IsCoatom a :=
  have ⟨b, hb⟩ := exists_ne (⊤ : α)
  have ⟨a, ha⟩ := (eq_top_or_exists_le_coatom b).resolve_left hb
  ⟨a, ha.1⟩

variable {α}

@[simp]
/-
**isCoatomic_dual_iff_isAtomic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCoatomic_dual_iff_isAtomic [OrderBot α] : IsCoatomic αᵒᵈ ↔ IsAtomic α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCoatomic.eq_top_or_exists_le_coatom`：∀ {α : Type u_2} {inst : PartialO
rder α} {inst_1 : OrderTop α} [self : IsCoatomic α] (b : α),   b = ⊤ ∨ ∃ a, IsCo
atom a ∧ b ≤ a
· 使用定理 `IsAtomic.eq_bot_or_exists_atom_le`：∀ {α : Type u_2} {inst : PartialOrder
 α} {inst_1 : OrderBot α} [self : IsAtomic α] (b : α),   b = ⊥ ∨ ∃ a, IsAtom a ∧
 a ≤ b
-/
theorem isCoatomic_dual_iff_isAtomic [OrderBot α] : IsCoatomic αᵒᵈ ↔ IsAtomic α :=
  ⟨fun h => ⟨fun b => by apply h.eq_top_or_exists_le_coatom⟩, fun h =>
    ⟨fun b => by apply h.eq_bot_or_exists_atom_le⟩⟩

@[simp]
/-
**isAtomic_dual_iff_isCoatomic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isAtomic_dual_iff_isCoatomic [OrderTop α] : IsAtomic αᵒᵈ ↔ IsCoatomic α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAtomic.eq_bot_or_exists_atom_le`：∀ {α : Type u_2} {inst : PartialOrder
 α} {inst_1 : OrderBot α} [self : IsAtomic α] (b : α),   b = ⊥ ∨ ∃ a, IsAtom a ∧
 a ≤ b
· 使用定理 `IsCoatomic.eq_top_or_exists_le_coatom`：∀ {α : Type u_2} {inst : PartialO
rder α} {inst_1 : OrderTop α} [self : IsCoatomic α] (b : α),   b = ⊤ ∨ ∃ a, IsCo
atom a ∧ b ≤ a
-/
theorem isAtomic_dual_iff_isCoatomic [OrderTop α] : IsAtomic αᵒᵈ ↔ IsCoatomic α :=
  ⟨fun h => ⟨fun b => by apply h.eq_bot_or_exists_atom_le⟩, fun h =>
    ⟨fun b => by apply h.eq_top_or_exists_le_coatom⟩⟩

namespace IsAtomic

variable [OrderBot α] [IsAtomic α]

/-
**IsAtomic._root_.OrderDual.instIsCoatomic** 是 Mathlib 中的一个实例，位于命名空间 `IsAtomic`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.OrderDual.instIsCoatomic : IsCoatomic αᵒᵈ :=
  isCoatomic_dual_iff_isAtomic.2 ‹IsAtomic α›
/-
**IsAtomic.Set.Iic.isAtomic** 是 Mathlib 中的一个定理，位于命名空间 `IsAtomic.Set.Iic`。
形式化陈述：∀ {α : Type u_2} [inst : PartialOrder α] [inst_1 : OrderBot α] [IsAtomic α
] {x : α}, IsAtomic ↑(Set.Iic x)
参数：Set.Iic x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subtype.mk_eq_mk`：mk_eq_mk {a h a' h'} : @mk α p a h = @mk α p a' h' ↔ a
 = a'
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `IsAtom.Iic`：IsAtom.Iic (ha : IsAtom a) (hax : a <= x) : IsAtom (⟨a, hax⟩
 : Set.Iic x)
· 使用定理 `IsAtomic.eq_bot_or_exists_atom_le`：∀ {α : Type u_2} {inst : PartialOrder
 α} {inst_1 : OrderBot α} [self : IsAtomic α] (b : α),   b = ⊥ ∨ ∃ a, IsAtom a ∧
 a ≤ b
-/
instance Set.Iic.isAtomic {x : α} : IsAtomic (Set.Iic x) :=
  ⟨fun ⟨y, hy⟩ =>
    (eq_bot_or_exists_atom_le y).imp Subtype.mk_eq_mk.2 fun ⟨a, ha, hay⟩ =>
      ⟨⟨a, hay.trans hy⟩, ha.Iic (hay.trans hy), hay⟩⟩

end IsAtomic

namespace IsCoatomic

variable [OrderTop α] [IsCoatomic α]

/-
**IsCoatomic._root_.OrderDual.instIsAtomic** 是 Mathlib 中的一个实例，位于命名空间 `IsCoatomic
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.OrderDual.instIsAtomic : IsAtomic αᵒᵈ :=
  isAtomic_dual_iff_isCoatomic.2 ‹IsCoatomic α›
/-
**IsCoatomic.Set.Ici.isCoatomic** 是 Mathlib 中的一个定理，位于命名空间 `IsCoatomic.Set.Ici`。
形式化陈述：∀ {α : Type u_2} [inst : PartialOrder α] [inst_1 : OrderTop α] [IsCoatomic
 α] {x : α}, IsCoatomic ↑(Set.Ici x)
参数：Set.Ici x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subtype.mk_eq_mk`：mk_eq_mk {a h a' h'} : @mk α p a h = @mk α p a' h' ↔ a
 = a'
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `IsCoatom.Ici`：IsCoatom.Ici (ha : IsCoatom a) (hax : x <= a) : IsCoatom (
⟨a, hax⟩ : Set.Ici x)
· 使用定理 `IsCoatomic.eq_top_or_exists_le_coatom`：∀ {α : Type u_2} {inst : PartialO
rder α} {inst_1 : OrderTop α} [self : IsCoatomic α] (b : α),   b = ⊤ ∨ ∃ a, IsCo
atom a ∧ b ≤ a
-/
instance Set.Ici.isCoatomic {x : α} : IsCoatomic (Set.Ici x) :=
  ⟨fun ⟨y, hy⟩ =>
    (eq_top_or_exists_le_coatom y).imp Subtype.mk_eq_mk.2 fun ⟨a, ha, hay⟩ =>
      ⟨⟨a, le_trans hy hay⟩, ha.Ici (le_trans hy hay), hay⟩⟩

end IsCoatomic

/-
**isAtomic_iff_forall_isAtomic_Iic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isAtomic_iff_forall_isAtomic_Iic [OrderBot α] : IsAtomic α ↔ forall x : α,
 IsAtomic (Set.Iic x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAtomic.Set.Iic.isAtomic`：∀ {α : Type u_2} [inst : PartialOrder α] [ins
t_1 : OrderBot α] [IsAtomic α] {x : α}, IsAtomic ↑(Set.Iic x)
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.mk_eq_mk`：mk_eq_mk {a h a' h'} : @mk α p a h = @mk α p a' h' ↔ a
 = a'
· 使用定理 `Exists.imp'`：∀ {α : Sort u_2} {p : α → Prop} {β : Sort u_1} {q : β → Pro
p} (f : α → β),   (∀ (a : α), p a → q (f a)) → (∃ a, p a) → ∃ b, q b
· 使用定理 `And.imp_left`：∀ {a b c : Prop}, (a → b) → a ∧ c → b ∧ c
· 使用定理 `IsAtom.of_isAtom_coe_Iic`：IsAtom.of_isAtom_coe_Iic {a : Set.Iic x} (ha :
 IsAtom a) : IsAtom (a : α)
· 使用定理 `IsAtomic.eq_bot_or_exists_atom_le`：∀ {α : Type u_2} {inst : PartialOrder
 α} {inst_1 : OrderBot α} [self : IsAtomic α] (b : α),   b = ⊥ ∨ ∃ a, IsAtom a ∧
 a ≤ b
-/
theorem isAtomic_iff_forall_isAtomic_Iic [OrderBot α] :
    IsAtomic α ↔ ∀ x : α, IsAtomic (Set.Iic x) :=
  ⟨@IsAtomic.Set.Iic.isAtomic _ _ _, fun h =>
    ⟨fun x =>
      ((@eq_bot_or_exists_atom_le _ _ _ (h x)) (⊤ : Set.Iic x)).imp Subtype.mk_eq_mk.1
        (Exists.imp' (↑) fun ⟨_, _⟩ => And.imp_left IsAtom.of_isAtom_coe_Iic)⟩⟩
/-
**isCoatomic_iff_forall_isCoatomic_Ici** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCoatomic_iff_forall_isCoatomic_Ici [OrderTop α] : IsCoatomic α ↔ forall 
x : α, IsCoatomic (Set.Ici x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `isAtomic_dual_iff_isCoatomic`：isAtomic_dual_iff_isCoatomic [OrderTop α] 
: IsAtomic αᵒᵈ ↔ IsCoatomic α
· 使用定理 `isAtomic_iff_forall_isAtomic_Iic`：isAtomic_iff_forall_isAtomic_Iic [Orde
rBot α] : IsAtomic α ↔ forall x : α, IsAtomic (Set.Iic x)
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `isCoatomic_dual_iff_isAtomic`：isCoatomic_dual_iff_isAtomic [OrderBot α] 
: IsCoatomic αᵒᵈ ↔ IsAtomic α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isCoatomic_iff_forall_isCoatomic_Ici [OrderTop α] :
    IsCoatomic α ↔ ∀ x : α, IsCoatomic (Set.Ici x) :=
  isAtomic_dual_iff_isCoatomic.symm.trans <|
    isAtomic_iff_forall_isAtomic_Iic.trans <|
      forall_congr' fun _ => isCoatomic_dual_iff_isAtomic.symm.trans Iff.rfl

section StronglyAtomic

variable {α : Type*} {a b : α} [Preorder α]

/-- An order is strongly atomic if every nontrivial interval `[a, b]`
contains an element covering `a`. -/
@[mk_iff]
/-
**IsStronglyAtomic** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_5) → [Preorder α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An order is strongly atomic if every nontrivial interval `[a, b]`
contains an element covering `a`.
-/
class IsStronglyAtomic (α : Type*) [Preorder α] : Prop where
  exists_covBy_le_of_lt : ∀ (a b : α), a < b → ∃ x, a ⋖ x ∧ x ≤ b
/-
**exists_covBy_le_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_covBy_le_of_lt [IsStronglyAtomic α] (h : a < b) : exists x, a ⋖ x ∧
 x <= b
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStronglyAtomic.exists_covBy_le_of_lt`：∀ {α : Type u_5} {inst : Preorde
r α} [self : IsStronglyAtomic α] (a b : α), a < b → ∃ x, a ⋖ x ∧ x ≤ b
-/
theorem exists_covBy_le_of_lt [IsStronglyAtomic α] (h : a < b) : ∃ x, a ⋖ x ∧ x ≤ b :=
  IsStronglyAtomic.exists_covBy_le_of_lt a b h

alias LT.lt.exists_covby_le := exists_covBy_le_of_lt

/-- An order is strongly coatomic if every nontrivial interval `[a, b]`
contains an element covered by `b`. -/
@[mk_iff]
/-
**IsStronglyCoatomic** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_5) → [Preorder α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An order is strongly coatomic if every nontrivial interval `[a, b]`
contains an element covered by `b`.
-/
class IsStronglyCoatomic (α : Type*) [Preorder α] : Prop where
  (exists_le_covBy_of_lt : ∀ (a b : α), a < b → ∃ x, a ≤ x ∧ x ⋖ b)
/-
**exists_le_covBy_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_le_covBy_of_lt [IsStronglyCoatomic α] (h : a < b) : exists x, a <= 
x ∧ x ⋖ b
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStronglyCoatomic.exists_le_covBy_of_lt`：∀ {α : Type u_5} {inst : Preor
der α} [self : IsStronglyCoatomic α] (a b : α), a < b → ∃ x, a ≤ x ∧ x ⋖ b
-/
theorem exists_le_covBy_of_lt [IsStronglyCoatomic α] (h : a < b) : ∃ x, a ≤ x ∧ x ⋖ b :=
  IsStronglyCoatomic.exists_le_covBy_of_lt a b h

alias LT.lt.exists_le_covby := exists_le_covBy_of_lt
/-
**isStronglyAtomic_dual_iff_is_stronglyCoatomic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isStronglyAtomic_dual_iff_is_stronglyCoatomic : IsStronglyAtomic αᵒᵈ ↔ IsS
tronglyCoatomic α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
-/
theorem isStronglyAtomic_dual_iff_is_stronglyCoatomic :
    IsStronglyAtomic αᵒᵈ ↔ IsStronglyCoatomic α := by
  simpa [isStronglyAtomic_iff, OrderDual.exists, OrderDual.forall,
    OrderDual.toDual_le_toDual, and_comm, isStronglyCoatomic_iff] using forall_comm
/-
**isStronglyCoatomic_dual_iff_is_stronglyAtomic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_4} [inst : Preorder α], IsStronglyCoatomic αᵒᵈ ↔ IsStronglyA
tomic α
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isStronglyAtomic_dual_iff_is_stronglyCoatomic`：isStronglyAtomic_dual_iff
_is_stronglyCoatomic : IsStronglyAtomic αᵒᵈ ↔ IsStronglyCoatomic α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem isStronglyCoatomic_dual_iff_is_stronglyAtomic :
    IsStronglyCoatomic αᵒᵈ ↔ IsStronglyAtomic α := by
  rw [← isStronglyAtomic_dual_iff_is_stronglyCoatomic]; rfl
/-
**OrderDual.instIsStronglyCoatomic** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：OrderDual.instIsStronglyCoatomic [IsStronglyAtomic α] : IsStronglyCoatomic
 αᵒᵈ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isStronglyCoatomic_dual_iff_is_stronglyAtomic`：∀ {α : Type u_4} [inst : 
Preorder α], IsStronglyCoatomic αᵒᵈ ↔ IsStronglyAtomic α
-/
instance OrderDual.instIsStronglyCoatomic [IsStronglyAtomic α] : IsStronglyCoatomic αᵒᵈ := by
  rwa [isStronglyCoatomic_dual_iff_is_stronglyAtomic]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsStronglyCoatomic α] : IsStronglyAtomic αᵒᵈ := by
  rwa [isStronglyAtomic_dual_iff_is_stronglyCoatomic]
/-
**IsStronglyAtomic.isAtomic** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsStronglyAtomic.isAtomic (α : Type*) [PartialOrder α] [OrderBot α] [IsStr
onglyAtomic α] : IsAtomic α where eq_bot_or_exists_atom_le a
参数：α : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `bot_lt_iff_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Orde
rBot α] {a : α}, ⊥ < a ↔ a ≠ ⊥
· 使用定理 `LT.lt.exists_covby_le`：∀ {α : Type u_4} {a b : α} [inst : Preorder α] [I
sStronglyAtomic α], a < b → ∃ x, a ⋖ x ∧ x ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `bot_covBy_iff`：bot_covBy_iff : ⊥ ⋖ a ↔ IsAtom a
-/
instance IsStronglyAtomic.isAtomic (α : Type*) [PartialOrder α] [OrderBot α] [IsStronglyAtomic α] :
    IsAtomic α where
  eq_bot_or_exists_atom_le a := by
    rw [or_iff_not_imp_left, ← Ne, ← bot_lt_iff_ne_bot]
    refine fun hlt ↦ ?_
    obtain ⟨x, hx, hxa⟩ := hlt.exists_covby_le
    exact ⟨x, bot_covBy_iff.1 hx, hxa⟩
/-
**IsStronglyCoatomic.toIsCoatomic** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsStronglyCoatomic.toIsCoatomic (α : Type*) [PartialOrder α] [OrderTop α] 
[IsStronglyCoatomic α] : IsCoatomic α
参数：α : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isAtomic_dual_iff_isCoatomic`：isAtomic_dual_iff_isCoatomic [OrderTop α] 
: IsAtomic αᵒᵈ ↔ IsCoatomic α
· 使用定理 `instIsStronglyAtomicOrderDualOfIsStronglyCoatomic`：∀ {α : Type u_4} [ins
t : Preorder α] [IsStronglyCoatomic α], IsStronglyAtomic αᵒᵈ
-/
instance IsStronglyCoatomic.toIsCoatomic (α : Type*) [PartialOrder α] [OrderTop α]
    [IsStronglyCoatomic α] : IsCoatomic α :=
  isAtomic_dual_iff_isCoatomic.1 <| IsStronglyAtomic.isAtomic (α := αᵒᵈ)
/-
**Set.OrdConnected.isStronglyAtomic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.OrdConnected.isStronglyAtomic [IsStronglyAtomic α] {s : Set α} (h : Se
t.OrdConnected s) : IsStronglyAtomic s where exists_covBy_le_of_lt
参数：h : Set.OrdConnected s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.exists_covby_le`：∀ {α : Type u_4} {a b : α} [inst : Preorder α] [I
sStronglyAtomic α], a < b → ∃ x, a ⋖ x ∧ x ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.mk_lt_mk`：mk_lt_mk [LT α] {p : α -> Prop} {x y : α} {hx : p x} {
hy : p y} : (⟨x, hx⟩ : Subtype p) < ⟨y, hy⟩ ↔ x < y
· 使用定理 `Set.OrdConnected.out'`：∀ {α : Type u_1} {inst : Preorder α} {s : Set α} 
[self : s.OrdConnected] ⦃x : α⦄,   x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s
· 使用定理 `CovBy.le`：CovBy.le (h : a ⋖ b) : a <= b
· 使用定理 `CovBy.lt`：CovBy.lt (h : a ⋖ b) : a < b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Set.OrdConnected.isStronglyAtomic [IsStronglyAtomic α] {s : Set α}
    (h : Set.OrdConnected s) : IsStronglyAtomic s where
  exists_covBy_le_of_lt := by
    rintro ⟨c, hc⟩ ⟨d, hd⟩ hcd
    obtain ⟨x, hcx, hxd⟩ := (Subtype.mk_lt_mk.1 hcd).exists_covby_le
    exact ⟨⟨x, h.out' hc hd ⟨hcx.le, hxd⟩⟩,
      ⟨by simpa
        using! hcx.lt, fun y hy hy' ↦ hcx.2 (by simpa using! hy) (by simpa using! hy')⟩, hxd⟩
/-
**Set.OrdConnected.isStronglyCoatomic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.OrdConnected.isStronglyCoatomic [IsStronglyCoatomic α] {s : Set α} (h 
: Set.OrdConnected s) : IsStronglyCoatomic s
参数：h : Set.OrdConnected s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isStronglyAtomic_dual_iff_is_stronglyCoatomic`：isStronglyAtomic_dual_iff
_is_stronglyCoatomic : IsStronglyAtomic αᵒᵈ ↔ IsStronglyCoatomic α
· 使用定理 `Set.OrdConnected.isStronglyAtomic`：Set.OrdConnected.isStronglyAtomic [Is
StronglyAtomic α] {s : Set α} (h : Set.OrdConnected s) : IsStronglyAtomic s wher
e exists_covBy_le_of_lt
· 使用定理 `instIsStronglyAtomicOrderDualOfIsStronglyCoatomic`：∀ {α : Type u_4} [ins
t : Preorder α] [IsStronglyCoatomic α], IsStronglyAtomic αᵒᵈ
· 使用定理 `Set.OrdConnected.dual`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α},
 s.OrdConnected → (⇑OrderDual.ofDual ⁻¹' s).OrdConnected
-/
theorem Set.OrdConnected.isStronglyCoatomic [IsStronglyCoatomic α] {s : Set α}
    (h : Set.OrdConnected s) : IsStronglyCoatomic s :=
  isStronglyAtomic_dual_iff_is_stronglyCoatomic.1 h.dual.isStronglyAtomic
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsStronglyAtomic α] {s : Set α} [Set.OrdConnected s] : IsStronglyAtomic s :=
  Set.OrdConnected.isStronglyAtomic <| by assumption
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsStronglyCoatomic α] {s : Set α} [h : Set.OrdConnected s] : IsStronglyCoatomic s :=
  Set.OrdConnected.isStronglyCoatomic <| by assumption
/-
**SuccOrder.toIsStronglyAtomic** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：SuccOrder.toIsStronglyAtomic [SuccOrder α] : IsStronglyAtomic α where exis
ts_covBy_le_of_lt a _ hab
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.covBy_succ_of_not_isMax`：covBy_succ_of_not_isMax (h : ¬IsMax a) : 
a ⋖ succ a
· 使用定理 `IsMax.not_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, IsMax a → 
¬a < b
· 使用定理 `SuccOrder.succ_le_of_lt`：∀ {α : Type u_3} {inst : Preorder α} [self : Su
ccOrder α] {a b : α}, a < b → SuccOrder.succ a ≤ b
-/
instance SuccOrder.toIsStronglyAtomic [SuccOrder α] : IsStronglyAtomic α where
  exists_covBy_le_of_lt a _ hab :=
    ⟨SuccOrder.succ a, Order.covBy_succ_of_not_isMax fun ha ↦ ha.not_lt hab,
      SuccOrder.succ_le_of_lt hab⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [PredOrder α] : IsStronglyCoatomic α := by
  rw [← isStronglyAtomic_dual_iff_is_stronglyCoatomic]; infer_instance

end StronglyAtomic

section WellFounded

/-
**IsStronglyAtomic.of_wellFounded_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsStronglyAtomic.of_wellFounded_lt (h : WellFounded ((· < ·) : α -> α -> P
rop)) : IsStronglyAtomic α where exists_covBy_le_of_lt a b hab
参数：h : WellFounded ((· < ·) : α -> α -> Prop)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `WellFounded.min_mem`：min_mem {r : α -> α -> Prop} (H : WellFounded r) (s
 : Set α) (h : s.Nonempty) : H.min s h in s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `WellFounded.not_lt_min`：not_lt_min {r : α -> α -> Prop} (H : WellFounded
 r) (s : Set α) {x} (hx : x in s) : ¬r x (H.min s ⟨x, hx⟩)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsStronglyAtomic.of_wellFounded_lt (h : WellFounded ((· < ·) : α → α → Prop)) :
    IsStronglyAtomic α where
  exists_covBy_le_of_lt a b hab := by
    refine ⟨WellFounded.min h (Set.Ioc a b) ⟨b, hab,rfl.le⟩, ?_⟩
    have hmem := (WellFounded.min_mem h (Set.Ioc a b) ⟨b, hab,rfl.le⟩)
    exact ⟨⟨hmem.1,fun c hac hlt ↦ WellFounded.not_lt_min h
      (Set.Ioc a b) ⟨hac, hlt.le.trans hmem.2⟩ hlt⟩, hmem.2⟩
/-
**IsStronglyCoatomic.of_wellFounded_gt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsStronglyCoatomic.of_wellFounded_gt (h : WellFounded ((· > ·) : α -> α ->
 Prop)) : IsStronglyCoatomic α
参数：h : WellFounded ((· > ·) : α -> α -> Prop)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isStronglyAtomic_dual_iff_is_stronglyCoatomic`：isStronglyAtomic_dual_iff
_is_stronglyCoatomic : IsStronglyAtomic αᵒᵈ ↔ IsStronglyCoatomic α
· 使用定理 `IsStronglyAtomic.of_wellFounded_lt`：IsStronglyAtomic.of_wellFounded_lt (
h : WellFounded ((· < ·) : α -> α -> Prop)) : IsStronglyAtomic α where exists_co
vBy_le_of_lt a b hab
-/
theorem IsStronglyCoatomic.of_wellFounded_gt (h : WellFounded ((· > ·) : α → α → Prop)) :
    IsStronglyCoatomic α :=
  isStronglyAtomic_dual_iff_is_stronglyCoatomic.1 <| IsStronglyAtomic.of_wellFounded_lt (α := αᵒᵈ) h
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [WellFoundedLT α] : IsStronglyAtomic α :=
  IsStronglyAtomic.of_wellFounded_lt wellFounded_lt
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [WellFoundedGT α] : IsStronglyCoatomic α :=
    IsStronglyCoatomic.of_wellFounded_gt wellFounded_gt
/-
**isAtomic_of_orderBot_wellFounded_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isAtomic_of_orderBot_wellFounded_lt [OrderBot α] (h : WellFounded ((· < ·)
 : α -> α -> Prop)) : IsAtomic α
参数：h : WellFounded ((· < ·) : α -> α -> Prop)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStronglyAtomic.of_wellFounded_lt`：IsStronglyAtomic.of_wellFounded_lt (
h : WellFounded ((· < ·) : α -> α -> Prop)) : IsStronglyAtomic α where exists_co
vBy_le_of_lt a b hab
-/
theorem isAtomic_of_orderBot_wellFounded_lt [OrderBot α]
    (h : WellFounded ((· < ·) : α → α → Prop)) : IsAtomic α :=
  (IsStronglyAtomic.of_wellFounded_lt h).isAtomic
/-
**isCoatomic_of_orderTop_gt_wellFounded** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCoatomic_of_orderTop_gt_wellFounded [OrderTop α] (h : WellFounded ((· > 
·) : α -> α -> Prop)) : IsCoatomic α
参数：h : WellFounded ((· > ·) : α -> α -> Prop)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isAtomic_dual_iff_isCoatomic`：isAtomic_dual_iff_isCoatomic [OrderTop α] 
: IsAtomic αᵒᵈ ↔ IsCoatomic α
· 使用定理 `isAtomic_of_orderBot_wellFounded_lt`：isAtomic_of_orderBot_wellFounded_lt
 [OrderBot α] (h : WellFounded ((· < ·) : α -> α -> Prop)) : IsAtomic α
-/
theorem isCoatomic_of_orderTop_gt_wellFounded [OrderTop α]
    (h : WellFounded ((· > ·) : α → α → Prop)) : IsCoatomic α :=
  isAtomic_dual_iff_isCoatomic.1 (@isAtomic_of_orderBot_wellFounded_lt αᵒᵈ _ _ h)

end WellFounded

namespace BooleanAlgebra

/-
**BooleanAlgebra.le_iff_atom_le_imp** 是 Mathlib 中的一个定理，位于命名空间 `BooleanAlgebra`。
形式化陈述：le_iff_atom_le_imp {α} [BooleanAlgebra α] [IsAtomic α] {x y : α} : x <= y 
↔ forall a, IsAtom a -> a <= x -> a <= y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `of_not_not`：of_not_not {a : Prop} : ¬¬a -> a
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `IsAtomic.eq_bot_or_exists_atom_le`：∀ {α : Type u_2} {inst : PartialOrder
 α} {inst_1 : OrderBot α} [self : IsAtomic α] (b : α),   b = ⊥ ∨ ∃ a, IsAtom a ∧
 a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_inf_iff`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a 
⊓ b ↔ c ≤ a ∧ c ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_compl_self`：inf_compl_self (a : α) : a ⊓ aᶜ = ⊥
· 使用定理 `IsCompl.inf_right_eq_bot_iff`：inf_right_eq_bot_iff (h : IsCompl y z) : x
 ⊓ z = ⊥ ↔ x <= y
· 使用定理 `eq_compl_iff_isCompl`：eq_compl_iff_isCompl : x = yᶜ ↔ IsCompl x y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem le_iff_atom_le_imp {α} [BooleanAlgebra α] [IsAtomic α] {x y : α} :
    x ≤ y ↔ ∀ a, IsAtom a → a ≤ x → a ≤ y := by
  refine ⟨fun h a _ => (le_trans · h), fun h => ?_⟩
  have : x ⊓ yᶜ = ⊥ := of_not_not fun hbot =>
    have ⟨a, ha, hle⟩ := (eq_bot_or_exists_atom_le _).resolve_left hbot
    have ⟨hx, hy'⟩ := le_inf_iff.1 hle
    have hy := h a ha hx
    have : a ≤ y ⊓ yᶜ := le_inf_iff.2 ⟨hy, hy'⟩
    ha.1 (by simpa using this)
  exact (eq_compl_iff_isCompl.1 (by simp)).inf_right_eq_bot_iff.1 this
/-
**BooleanAlgebra.eq_iff_atom_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `BooleanAlgebra`。
形式化陈述：eq_iff_atom_le_iff {α} [BooleanAlgebra α] [IsAtomic α] {x y : α} : x = y ↔
 forall a, IsAtom a -> (a <= x ↔ a <= y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `BooleanAlgebra.le_iff_atom_le_imp`：le_iff_atom_le_imp {α} [BooleanAlgebr
a α] [IsAtomic α] {x y : α} : x <= y ↔ forall a, IsAtom a -> a <= x -> a <= y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem eq_iff_atom_le_iff {α} [BooleanAlgebra α] [IsAtomic α] {x y : α} :
    x = y ↔ ∀ a, IsAtom a → (a ≤ x ↔ a ≤ y) := by
  refine ⟨fun h => h ▸ by simp, fun h => ?_⟩
  exact le_antisymm (le_iff_atom_le_imp.2 fun a ha hx => (h a ha).1 hx)
    (le_iff_atom_le_imp.2 fun a ha hy => (h a ha).2 hy)

end BooleanAlgebra

namespace CompleteBooleanAlgebra

/-- Every atomic complete Boolean algebra is completely atomic.

This is not made an instance to avoid typeclass loops. -/
-- See note [reducible non-instances]
/-
**CompleteBooleanAlgebra.toCompleteAtomicBooleanAlgebra** 是 Mathlib 中的一个缩写定义，位于命
名空间 `CompleteBooleanAlgebra`。
形式化陈述：toCompleteAtomicBooleanAlgebra {α} [CompleteBooleanAlgebra α] [IsAtomic α]
 : CompleteAtomicBooleanAlgebra α where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev toCompleteAtomicBooleanAlgebra {α} [CompleteBooleanAlgebra α] [IsAtomic α] :
    CompleteAtomicBooleanAlgebra α where
  __ := ‹CompleteBooleanAlgebra α›
  iInf_iSup_eq f := BooleanAlgebra.eq_iff_atom_le_iff.2 fun a ha => by
    simp only [le_iInf_iff, ha.le_iSup, Classical.skolem]

end CompleteBooleanAlgebra

end Atomic

section Atomistic

variable (α) [PartialOrder α]

/-- A lattice is atomistic iff every element is a `sSup` of a set of atoms. -/
@[mk_iff]
/-
**IsAtomistic** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_2) → [inst : PartialOrder α] → [OrderBot α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A lattice is atomistic iff every element is a `sSup` of a set of atoms.
-/
class IsAtomistic [OrderBot α] : Prop where
  /-- Every element is a `sSup` of a set of atoms. -/
  isLUB_atoms : ∀ b : α, ∃ s : Set α, IsLUB s b ∧ ∀ a, a ∈ s → IsAtom a

/-- A lattice is coatomistic iff every element is an `sInf` of a set of coatoms. -/
@[mk_iff]
/-
**IsCoatomistic** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_2) → [inst : PartialOrder α] → [OrderTop α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A lattice is coatomistic iff every element is an `sInf` of a set of coatoms.
-/
class IsCoatomistic [OrderTop α] : Prop where
  /-- Every element is a `sInf` of a set of coatoms. -/
  isGLB_coatoms : ∀ b : α, ∃ s : Set α, IsGLB s b ∧ ∀ a, a ∈ s → IsCoatom a

export IsAtomistic (isLUB_atoms)

export IsCoatomistic (isGLB_coatoms)

variable {α}

@[simp]
/-
**isCoatomistic_dual_iff_isAtomistic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCoatomistic_dual_iff_isAtomistic [OrderBot α] : IsCoatomistic αᵒᵈ ↔ IsAt
omistic α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCoatomistic.isGLB_coatoms`：∀ {α : Type u_2} {inst : PartialOrder α} {i
nst_1 : OrderTop α} [self : IsCoatomistic α] (b : α),   ∃ s, IsGLB s b ∧ ∀ a ∈ s
, IsCoatom a
· 使用定理 `IsAtomistic.isLUB_atoms`：∀ {α : Type u_2} {inst : PartialOrder α} {inst_
1 : OrderBot α} [self : IsAtomistic α] (b : α),   ∃ s, IsLUB s b ∧ ∀ a ∈ s, IsAt
om a
-/
theorem isCoatomistic_dual_iff_isAtomistic [OrderBot α] : IsCoatomistic αᵒᵈ ↔ IsAtomistic α :=
  ⟨fun h => ⟨fun b => by apply h.isGLB_coatoms⟩, fun h => ⟨fun b => by apply h.isLUB_atoms⟩⟩

@[simp]
/-
**isAtomistic_dual_iff_isCoatomistic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isAtomistic_dual_iff_isCoatomistic [OrderTop α] : IsAtomistic αᵒᵈ ↔ IsCoat
omistic α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAtomistic.isLUB_atoms`：∀ {α : Type u_2} {inst : PartialOrder α} {inst_
1 : OrderBot α} [self : IsAtomistic α] (b : α),   ∃ s, IsLUB s b ∧ ∀ a ∈ s, IsAt
om a
· 使用定理 `IsCoatomistic.isGLB_coatoms`：∀ {α : Type u_2} {inst : PartialOrder α} {i
nst_1 : OrderTop α} [self : IsCoatomistic α] (b : α),   ∃ s, IsGLB s b ∧ ∀ a ∈ s
, IsCoatom a
-/
theorem isAtomistic_dual_iff_isCoatomistic [OrderTop α] : IsAtomistic αᵒᵈ ↔ IsCoatomistic α :=
  ⟨fun h => ⟨fun b => by apply h.isLUB_atoms⟩, fun h => ⟨fun b => by apply h.isGLB_coatoms⟩⟩

namespace IsAtomistic

/-
**IsAtomistic._root_.OrderDual.instIsCoatomistic** 是 Mathlib 中的一个实例，位于命名空间 `IsAt
omistic`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.OrderDual.instIsCoatomistic [OrderBot α] [h : IsAtomistic α] : IsCoatomistic αᵒᵈ :=
  isCoatomistic_dual_iff_isAtomistic.2 h

variable [OrderBot α] [IsAtomistic α]
/-
**IsAtomistic.** 是 Mathlib 中的一个实例，位于命名空间 `IsAtomistic`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) : IsAtomic α :=
  ⟨fun b => by
    rcases isLUB_atoms b with ⟨s, hsb, hs⟩
    rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · simp_all
    · exact Or.inr ⟨a, hs _ ha, hsb.1 ha⟩⟩

end IsAtomistic

section IsAtomistic

variable [OrderBot α] [IsAtomistic α]

/-
**isLUB_atoms_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLUB_atoms_le (b : α) : IsLUB { a : α | IsAtom a ∧ a <= b } b
参数：b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAtomistic.isLUB_atoms`：∀ {α : Type u_2} {inst : PartialOrder α} {inst_
1 : OrderBot α} [self : IsAtomistic α] (b : α),   ∃ s, IsLUB s b ∧ ∀ a ∈ s, IsAt
om a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem isLUB_atoms_le (b : α) : IsLUB { a : α | IsAtom a ∧ a ≤ b } b := by
  rcases isLUB_atoms b with ⟨s, hsb, hs⟩
  exact ⟨fun c hc ↦ hc.2, fun c hc ↦ hsb.2 fun i hi ↦ hc ⟨hs _ hi, hsb.1 hi⟩⟩
/-
**isLUB_atoms_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLUB_atoms_top [OrderTop α] : IsLUB { a : α | IsAtom a } ⊤
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `isLUB_atoms_le`：isLUB_atoms_le (b : α) : IsLUB { a : α | IsAtom a ∧ a <=
 b } b
-/
theorem isLUB_atoms_top [OrderTop α] : IsLUB { a : α | IsAtom a } ⊤ := by
  simpa using isLUB_atoms_le (⊤ : α)
/-
**le_iff_atom_le_imp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_iff_atom_le_imp {a b : α} : a <= b ↔ forall c : α, IsAtom c -> c <= a -
> c <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `IsLUB.mono`：IsLUB.mono (ha : IsLUB s a) (hb : IsLUB t b) (hst : s subset
eq t) : a <= b
· 使用定理 `isLUB_atoms_le`：isLUB_atoms_le (b : α) : IsLUB { a : α | IsAtom a ∧ a <=
 b } b
-/
theorem le_iff_atom_le_imp {a b : α} : a ≤ b ↔ ∀ c : α, IsAtom c → c ≤ a → c ≤ b :=
  ⟨fun hab _ _ hca ↦ hca.trans hab,
   fun h ↦ (isLUB_atoms_le a).mono (isLUB_atoms_le b) fun _ ⟨h₁, h₂⟩ ↦ ⟨h₁, h _ h₁ h₂⟩⟩
/-
**eq_iff_atom_le_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_iff_atom_le_iff {a b : α} : a = b ↔ forall c, IsAtom c -> (c <= a ↔ c <
= b)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `le_antisymm_iff`：le_antisymm_iff : a = b ↔ a <= b ∧ b <= a
· 使用定理 `le_iff_atom_le_imp`：le_iff_atom_le_imp {a b : α} : a <= b ↔ forall c : α
, IsAtom c -> c <= a -> c <= b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem eq_iff_atom_le_iff {a b : α} : a = b ↔ ∀ c, IsAtom c → (c ≤ a ↔ c ≤ b) := by
  refine ⟨fun h => by simp [h], fun h => ?_⟩
  rw [le_antisymm_iff, le_iff_atom_le_imp, le_iff_atom_le_imp]
  simp_all

end IsAtomistic

namespace IsCoatomistic

variable [OrderTop α]

/-
**IsCoatomistic._root_.OrderDual.instIsAtomistic** 是 Mathlib 中的一个实例，位于命名空间 `IsCo
atomistic`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.OrderDual.instIsAtomistic [h : IsCoatomistic α] : IsAtomistic αᵒᵈ :=
  isAtomistic_dual_iff_isCoatomistic.2 h

variable [IsCoatomistic α]
/-
**IsCoatomistic.** 是 Mathlib 中的一个实例，位于命名空间 `IsCoatomistic`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) : IsCoatomic α :=
  ⟨fun b => by
    rcases isGLB_coatoms b with ⟨s, hsb, hs⟩
    rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · simp_all
    · exact Or.inr ⟨a, hs _ ha, hsb.1 ha⟩⟩

end IsCoatomistic

section CompleteLattice

@[simp]
/-
**sSup_atoms_le_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sSup_atoms_le_eq {α} [CompleteLattice α] [IsAtomistic α] (b : α) : sSup { 
a : α | IsAtom a ∧ a <= b } = b
参数：b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLUB.sSup_eq`：∀ {α : Type u_1} [inst : CompleteSemilatticeSup α] {s : S
et α} {a : α}, IsLUB s a → sSup s = a
· 使用定理 `isLUB_atoms_le`：isLUB_atoms_le (b : α) : IsLUB { a : α | IsAtom a ∧ a <=
 b } b
-/
theorem sSup_atoms_le_eq {α} [CompleteLattice α] [IsAtomistic α] (b : α) :
    sSup { a : α | IsAtom a ∧ a ≤ b } = b :=
  (isLUB_atoms_le b).sSup_eq

@[simp]
/-
**sSup_atoms_eq_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sSup_atoms_eq_top {α} [CompleteLattice α] [IsAtomistic α] : sSup { a : α |
 IsAtom a } = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLUB.sSup_eq`：∀ {α : Type u_1} [inst : CompleteSemilatticeSup α] {s : S
et α} {a : α}, IsLUB s a → sSup s = a
· 使用定理 `isLUB_atoms_top`：isLUB_atoms_top [OrderTop α] : IsLUB { a : α | IsAtom a
 } ⊤
-/
theorem sSup_atoms_eq_top {α} [CompleteLattice α] [IsAtomistic α] :
    sSup { a : α | IsAtom a } = ⊤ :=
  isLUB_atoms_top.sSup_eq

nonrec lemma CompleteLattice.isAtomistic_iff {α} [CompleteLattice α] :
    IsAtomistic α ↔ ∀ b : α, ∃ s : Set α, b = sSup s ∧ ∀ a ∈ s, IsAtom a := by
  simp_rw [isAtomistic_iff, isLUB_iff_sSup_eq, eq_comm]
/-
**eq_sSup_atoms** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eq_sSup_atoms {α} [CompleteLattice α] [IsAtomistic α] (b : α) : exists s :
 Set α, b = sSup s ∧ forall a in s, IsAtom a
参数：b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CompleteLattice.isAtomistic_iff`：∀ {α : Type u_4} [inst : CompleteLattic
e α], IsAtomistic α ↔ ∀ (b : α), ∃ s, b = sSup s ∧ ∀ a ∈ s, IsAtom a
-/
lemma eq_sSup_atoms {α} [CompleteLattice α] [IsAtomistic α] (b : α) :
    ∃ s : Set α, b = sSup s ∧ ∀ a ∈ s, IsAtom a :=
  CompleteLattice.isAtomistic_iff.1 ‹_› b

nonrec lemma CompleteLattice.isCoatomistic_iff {α} [CompleteLattice α] :
    IsCoatomistic α ↔ ∀ b : α, ∃ s : Set α, b = sInf s ∧ ∀ a ∈ s, IsCoatom a := by
  simp_rw [isCoatomistic_iff, isGLB_iff_sInf_eq, eq_comm]
/-
**eq_sInf_coatoms** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eq_sInf_coatoms {α} [CompleteLattice α] [IsCoatomistic α] (b : α) : exists
 s : Set α, b = sInf s ∧ forall a in s, IsCoatom a
参数：b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CompleteLattice.isCoatomistic_iff`：∀ {α : Type u_4} [inst : CompleteLatt
ice α], IsCoatomistic α ↔ ∀ (b : α), ∃ s, b = sInf s ∧ ∀ a ∈ s, IsCoatom a
-/
lemma eq_sInf_coatoms {α} [CompleteLattice α] [IsCoatomistic α] (b : α) :
    ∃ s : Set α, b = sInf s ∧ ∀ a ∈ s, IsCoatom a :=
  CompleteLattice.isCoatomistic_iff.1 ‹_› b

end CompleteLattice

namespace CompleteAtomicBooleanAlgebra

/-
**CompleteAtomicBooleanAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `CompleteAtomicBoolean
Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α} [CompleteAtomicBooleanAlgebra α] : IsAtomistic α :=
  CompleteLattice.isAtomistic_iff.2 fun b ↦ by
    inhabit α
    refine ⟨{ a | IsAtom a ∧ a ≤ b }, ?_, fun a ha => ha.1⟩
    refine le_antisymm ?_ (sSup_le fun c hc => hc.2)
    have : (⨅ c : α, ⨆ x, b ⊓ cond x c (cᶜ)) = b := by simp [iSup_bool_eq]
    rw [← this]; clear this
    simp_rw [iInf_iSup_eq, iSup_le_iff]; intro g
    if h : (⨅ a, b ⊓ cond (g a) a (aᶜ)) = ⊥ then simp [h] else
    refine le_sSup ⟨⟨h, fun c hc => ?_⟩, le_trans (by rfl) (le_iSup _ g)⟩; clear h
    have := lt_of_lt_of_le hc (le_trans (iInf_le _ c) inf_le_right)
    revert this
    nontriviality α
    cases g c <;> simp
/-
**CompleteAtomicBooleanAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `CompleteAtomicBoolean
Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α} [CompleteAtomicBooleanAlgebra α] : IsCoatomistic α :=
  isAtomistic_dual_iff_isCoatomistic.1 inferInstance
/-
**CompleteAtomicBooleanAlgebra.eq_setOfPred_le_sSup_and_isAtom** 是 Mathlib 中的一个引
理，位于命名空间 `CompleteAtomicBooleanAlgebra`。
形式化陈述：eq_setOfPred_le_sSup_and_isAtom {α} [CompleteAtomicBooleanAlgebra α] {S : 
Set α} (hS : forall a in S, IsAtom a) : S = {a | a <= sSup S ∧ IsAtom a}
参数：hS : forall a in S, IsAtom a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsAtom.le_sSup`：∀ {α : Type u_2} [inst : Order.Frame α] {s : Set α} {a :
 α}, IsAtom a → (a ≤ sSup s ↔ ∃ b ∈ s, a ≤ b)
· 使用定理 `IsAtom.le_iff`：IsAtom.le_iff (h : IsAtom a) : x <= a ↔ x = ⊥ ∨ x = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma eq_setOfPred_le_sSup_and_isAtom {α} [CompleteAtomicBooleanAlgebra α] {S : Set α}
    (hS : ∀ a ∈ S, IsAtom a) : S = {a | a ≤ sSup S ∧ IsAtom a} := by
  ext a
  refine ⟨fun h => ⟨le_sSup h, hS a h⟩, fun ⟨hale, hatom⟩ => ?_⟩
  obtain ⟨b, hbS, hba⟩ := (IsAtom.le_sSup hatom).mp hale
  obtain rfl | rfl := (hS b hbS).le_iff.mp hba
  · simpa using hatom.1
  assumption

@[deprecated (since := "2026-07-09")]
alias eq_setOf_le_sSup_and_isAtom := eq_setOfPred_le_sSup_and_isAtom

set_option backward.isDefEq.respectTransparency false in
/--
Representation theorem for complete atomic boolean algebras:
For a complete atomic Boolean algebra `α`, `toSetOfIsAtom` is an order isomorphism
between `α` and the set of subsets of its atoms.
-/
/-
**CompleteAtomicBooleanAlgebra.toSetOfIsAtom** 是 Mathlib 中的一个定义，位于命名空间 `Complete
AtomicBooleanAlgebra`。
形式化陈述：toSetOfIsAtom {α} [CompleteAtomicBooleanAlgebra α] : α ≃o (Set {a : α // I
sAtom a}) where toFun A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Representation theorem for complete atomic boolean algebras:
For a complete atomic Boolean algebra `α`, `toSetOfIsAtom` is an order isomorphi
sm
between `α` and the set of subsets of its atoms.
-/
def toSetOfIsAtom {α} [CompleteAtomicBooleanAlgebra α] : α ≃o (Set {a : α // IsAtom a}) where
  toFun A := {a | a ≤ A}
  invFun S := sSup (Subtype.val '' S)
  left_inv A := by simp [Subtype.coe_image]
  right_inv S := by
    have h : ∀ a ∈ Subtype.val '' S, IsAtom a := by
      rintro a ⟨a', ha', rfl⟩
      exact a'.prop
    rw [← Subtype.val_injective.image_injective.eq_iff, eq_setOfPred_le_sSup_and_isAtom h]
    ext a
    simp
  map_rel_iff' {a b} := by
    simpa using le_iff_atom_le_imp.symm

end CompleteAtomicBooleanAlgebra

end Atomistic

/-- An order is simple iff it has exactly two elements, `⊥` and `⊤`. -/
@[mk_iff]
/-
**IsSimpleOrder** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_4) → [inst : LE α] → [BoundedOrder α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An order is simple iff it has exactly two elements, `⊥` and `⊤`.
-/
class IsSimpleOrder (α : Type*) [LE α] [BoundedOrder α] : Prop extends Nontrivial α where
  /-- Every element is either `⊥` or `⊤` -/
  eq_bot_or_eq_top : ∀ a : α, a = ⊥ ∨ a = ⊤

export IsSimpleOrder (eq_bot_or_eq_top)
/-
**IsSimpleOrder.of_forall_eq_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsSimpleOrder.of_forall_eq_top {α : Type*} [LE α] [BoundedOrder α] [Nontri
vial α] (h : forall a : α, a != ⊥ -> a = ⊤) : IsSimpleOrder α where eq_bot_or_eq
_top a
参数：h : forall a : α, a != ⊥ -> a = ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
-/
lemma IsSimpleOrder.of_forall_eq_top {α : Type*} [LE α] [BoundedOrder α] [Nontrivial α]
    (h : ∀ a : α, a ≠ ⊥ → a = ⊤) :
    IsSimpleOrder α where
  eq_bot_or_eq_top a := or_iff_not_imp_left.mpr <| h a
/-
**isSimpleOrder_iff_isSimpleOrder_orderDual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isSimpleOrder_iff_isSimpleOrder_orderDual [LE α] [BoundedOrder α] : IsSimp
leOrder α ↔ IsSimpleOrder αᵒᵈ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderDual.instNontrivial`：∀ {α : Type u_1} [h : Nontrivial α], Nontrivia
l αᵒᵈ
· 使用定理 `IsSimpleOrder.toNontrivial`：∀ {α : Type u_4} {inst : LE α} {inst_1 : Bou
ndedOrder α} [self : IsSimpleOrder α], Nontrivial α
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
· 使用定理 `IsSimpleOrder.eq_bot_or_eq_top`：∀ {α : Type u_4} {inst : LE α} {inst_1 :
 BoundedOrder α} [self : IsSimpleOrder α] (a : α), a = ⊥ ∨ a = ⊤
· 使用定理 `exists_pair_ne`：exists_pair_ne (α : Type*) [Nontrivial α] : exists x y :
 α, x != y
-/
theorem isSimpleOrder_iff_isSimpleOrder_orderDual [LE α] [BoundedOrder α] :
    IsSimpleOrder α ↔ IsSimpleOrder αᵒᵈ := by
  constructor <;> intro i
  · exact
      { eq_bot_or_eq_top := fun a => Or.symm (eq_bot_or_eq_top (OrderDual.ofDual a) : _ ∨ _) }
  · exact
      { exists_pair_ne := @exists_pair_ne αᵒᵈ _
        eq_bot_or_eq_top := fun a => Or.symm (eq_bot_or_eq_top (OrderDual.toDual a)) }
/-
**IsSimpleOrder.bot_ne_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSimpleOrder.bot_ne_top [LE α] [BoundedOrder α] [IsSimpleOrder α] : (⊥ : 
α) != (⊤ : α)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_pair_ne`：exists_pair_ne (α : Type*) [Nontrivial α] : exists x y :
 α, x != y
· 使用定理 `IsSimpleOrder.toNontrivial`：∀ {α : Type u_4} {inst : LE α} {inst_1 : Bou
ndedOrder α} [self : IsSimpleOrder α], Nontrivial α
· 使用定理 `IsSimpleOrder.eq_bot_or_eq_top`：∀ {α : Type u_4} {inst : LE α} {inst_1 :
 BoundedOrder α} [self : IsSimpleOrder α] (a : α), a = ⊥ ∨ a = ⊤
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsSimpleOrder.bot_ne_top [LE α] [BoundedOrder α] [IsSimpleOrder α] : (⊥ : α) ≠ (⊤ : α) := by
  obtain ⟨a, b, h⟩ := exists_pair_ne α
  rcases eq_bot_or_eq_top a with (rfl | rfl) <;> rcases eq_bot_or_eq_top b with (rfl | rfl) <;>
    first | simpa | simpa using h.symm

section IsSimpleOrder

variable [PartialOrder α] [BoundedOrder α] [IsSimpleOrder α]

/-
**OrderDual.instIsSimpleOrder** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：OrderDual.instIsSimpleOrder {α} [LE α] [BoundedOrder α] [IsSimpleOrder α] 
: IsSimpleOrder αᵒᵈ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isSimpleOrder_iff_isSimpleOrder_orderDual`：isSimpleOrder_iff_isSimpleOrd
er_orderDual [LE α] [BoundedOrder α] : IsSimpleOrder α ↔ IsSimpleOrder αᵒᵈ
-/
instance OrderDual.instIsSimpleOrder {α} [LE α] [BoundedOrder α] [IsSimpleOrder α] :
    IsSimpleOrder αᵒᵈ := isSimpleOrder_iff_isSimpleOrder_orderDual.1 (by infer_instance)

/-- A simple `BoundedOrder` induces a preorder. This is not an instance to prevent loops. -/
@[instance_reducible]
/-
**IsSimpleOrder.preorder** 是 Mathlib 中的一个定义，位于命名空间 `IsSimpleOrder`。
形式化陈述：{α : Type u_4} → [inst : LE α] → [inst_1 : BoundedOrder α] → [IsSimpleOrde
r α] → Preorder α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A simple `BoundedOrder` induces a preorder. This is not an instance to prevent l
oops.
-/
protected def IsSimpleOrder.preorder {α} [LE α] [BoundedOrder α] [IsSimpleOrder α] :
    Preorder α where
  le_refl a := by rcases eq_bot_or_eq_top a with (rfl | rfl) <;> simp
  le_trans a b c := by
    rcases eq_bot_or_eq_top a with (rfl | rfl)
    · simp
    · rcases eq_bot_or_eq_top b with (rfl | rfl)
      · rcases eq_bot_or_eq_top c with (rfl | rfl) <;> simp
      · simp

/-- A simple partial ordered `BoundedOrder` induces a linear order.
This is not an instance to prevent loops. -/
@[instance_reducible]
/-
**IsSimpleOrder.linearOrder** 是 Mathlib 中的一个定义，位于命名空间 `IsSimpleOrder`。
形式化陈述：{α : Type u_2} →   [inst : PartialOrder α] → [inst_1 : BoundedOrder α] → [
IsSimpleOrder α] → [DecidableEq α] → LinearOrder α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A simple partial ordered `BoundedOrder` induces a linear order.
This is not an instance to prevent loops.
-/
protected def IsSimpleOrder.linearOrder [DecidableEq α] : LinearOrder α :=
  { (inferInstance : PartialOrder α) with
    le_total := fun a b => by rcases eq_bot_or_eq_top a with (rfl | rfl) <;> simp
    -- Note from https://github.com/leanprover-community/mathlib4/issues/23976: do we want this inlined or should this be a separate definition?
    toDecidableLE := fun a b =>
      if ha : a = ⊥ then isTrue (ha.le.trans bot_le)
      else
        if hb : b = ⊤ then isTrue (le_top.trans hb.ge)
        else
          isFalse fun H =>
            hb (top_unique (le_trans (top_le_iff.mpr (Or.resolve_left
              (eq_bot_or_eq_top a) ha)) H))
    toDecidableEq := ‹_› }
/-
**isAtom_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isAtom_top : IsAtom (⊤ : α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `top_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : BoundedOrde
r α] [Nontrivial α], ⊤ ≠ ⊥
· 使用定理 `IsSimpleOrder.toNontrivial`：∀ {α : Type u_4} {inst : LE α} {inst_1 : Bou
ndedOrder α} [self : IsSimpleOrder α], Nontrivial α
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `IsSimpleOrder.eq_bot_or_eq_top`：∀ {α : Type u_4} {inst : LE α} {inst_1 :
 BoundedOrder α} [self : IsSimpleOrder α] (a : α), a = ⊥ ∨ a = ⊤
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
-/
theorem isAtom_top : IsAtom (⊤ : α) :=
  ⟨top_ne_bot, fun a ha => Or.resolve_right (eq_bot_or_eq_top a) (ne_of_lt ha)⟩

@[simp]
/-
**isAtom_iff_eq_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isAtom_iff_eq_top {a : α} : IsAtom a ↔ a = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `IsSimpleOrder.eq_bot_or_eq_top`：∀ {α : Type u_4} {inst : LE α} {inst_1 :
 BoundedOrder α} [self : IsSimpleOrder α] (a : α), a = ⊥ ∨ a = ⊤
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `isAtom_top`：isAtom_top : IsAtom (⊤ : α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isAtom_iff_eq_top {a : α} : IsAtom a ↔ a = ⊤ :=
  ⟨fun h ↦ (eq_bot_or_eq_top a).resolve_left h.1, (· ▸ isAtom_top)⟩
/-
**isCoatom_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCoatom_bot : IsCoatom (⊥ : α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isAtom_dual_iff_isCoatom`：isAtom_dual_iff_isCoatom [OrderTop α] {a : α} 
: IsAtom (OrderDual.toDual a) ↔ IsCoatom a
· 使用定理 `isAtom_top`：isAtom_top : IsAtom (⊤ : α)
-/
theorem isCoatom_bot : IsCoatom (⊥ : α) :=
  isAtom_dual_iff_isCoatom.1 isAtom_top

@[simp]
/-
**isCoatom_iff_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCoatom_iff_eq_bot {a : α} : IsCoatom a ↔ a = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `IsSimpleOrder.eq_bot_or_eq_top`：∀ {α : Type u_4} {inst : LE α} {inst_1 :
 BoundedOrder α} [self : IsSimpleOrder α] (a : α), a = ⊥ ∨ a = ⊤
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `isCoatom_bot`：isCoatom_bot : IsCoatom (⊥ : α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isCoatom_iff_eq_bot {a : α} : IsCoatom a ↔ a = ⊥ :=
  ⟨fun h ↦ (eq_bot_or_eq_top a).resolve_right h.1, (· ▸ isCoatom_bot)⟩
/-
**bot_covBy_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bot_covBy_top : (⊥ : α) ⋖ ⊤
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAtom.bot_covBy`：∀ {α : Type u_2} [inst : PartialOrder α] [inst_1 : Ord
erBot α] {a : α}, IsAtom a → ⊥ ⋖ a
· 使用定理 `isAtom_top`：isAtom_top : IsAtom (⊤ : α)
-/
theorem bot_covBy_top : (⊥ : α) ⋖ ⊤ :=
  isAtom_top.bot_covBy

end IsSimpleOrder

namespace IsSimpleOrder

section Preorder

variable [Preorder α] [BoundedOrder α] [IsSimpleOrder α] {a b : α} (h : a < b)
include h

/-
**IsSimpleOrder.eq_bot_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `IsSimpleOrder`。
形式化陈述：eq_bot_of_lt : a = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `IsSimpleOrder.eq_bot_or_eq_top`：∀ {α : Type u_4} {inst : LE α} {inst_1 :
 BoundedOrder α} [self : IsSimpleOrder α] (a : α), a = ⊥ ∨ a = ⊤
· 使用定理 `LT.lt.ne_top`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderTop α] {
a b : α}, a < b → a ≠ ⊤
-/
theorem eq_bot_of_lt : a = ⊥ :=
  (IsSimpleOrder.eq_bot_or_eq_top _).resolve_right h.ne_top
/-
**IsSimpleOrder.eq_top_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `IsSimpleOrder`。
形式化陈述：eq_top_of_lt : b = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `IsSimpleOrder.eq_bot_or_eq_top`：∀ {α : Type u_4} {inst : LE α} {inst_1 :
 BoundedOrder α} [self : IsSimpleOrder α] (a : α), a = ⊥ ∨ a = ⊤
· 使用定理 `LT.lt.ne_bot`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {
a b : α}, b < a → a ≠ ⊥
-/
theorem eq_top_of_lt : b = ⊤ :=
  (IsSimpleOrder.eq_bot_or_eq_top _).resolve_left h.ne_bot

alias _root_.LT.lt.eq_bot := eq_bot_of_lt
alias _root_.LT.lt.eq_top := eq_top_of_lt
end Preorder

section BoundedOrder

variable [Lattice α] [BoundedOrder α] [IsSimpleOrder α]

/-- A simple partial ordered `BoundedOrder` induces a lattice.
This is not an instance to prevent loops -/
@[instance_reducible]
/-
**IsSimpleOrder.lattice** 是 Mathlib 中的一个定义，位于命名空间 `IsSimpleOrder`。
形式化陈述：{α : Type u_4} → [DecidableEq α] → [inst : PartialOrder α] → [inst_1 : Bou
ndedOrder α] → [IsSimpleOrder α] → Lattice α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A simple partial ordered `BoundedOrder` induces a lattice.
This is not an instance to prevent loops
-/
protected def lattice {α} [DecidableEq α] [PartialOrder α] [BoundedOrder α] [IsSimpleOrder α] :
    Lattice α :=
  @LinearOrder.toLattice α IsSimpleOrder.linearOrder

/-- A lattice that is a `BoundedOrder` is a distributive lattice.
This is not an instance to prevent loops -/
@[instance_reducible]
/-
**IsSimpleOrder.distribLattice** 是 Mathlib 中的一个定义，位于命名空间 `IsSimpleOrder`。
形式化陈述：{α : Type u_2} → [inst : Lattice α] → [inst_1 : BoundedOrder α] → [IsSimpl
eOrder α] → DistribLattice α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A lattice that is a `BoundedOrder` is a distributive lattice.
This is not an instance to prevent loops
-/
protected def distribLattice : DistribLattice α :=
  { (inferInstance : Lattice α) with
    le_sup_inf := fun x y z => by rcases eq_bot_or_eq_top x with (rfl | rfl) <;> simp }

-- see Note [lower instance priority]
/-
**IsSimpleOrder.** 是 Mathlib 中的一个实例，位于命名空间 `IsSimpleOrder`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) : IsAtomic α :=
  ⟨fun b => (eq_bot_or_eq_top b).imp_right fun h => ⟨⊤, ⟨isAtom_top, ge_of_eq h⟩⟩⟩

-- see Note [lower instance priority]
/-
**IsSimpleOrder.** 是 Mathlib 中的一个实例，位于命名空间 `IsSimpleOrder`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) : IsCoatomic α :=
  isAtomic_dual_iff_isCoatomic.1 (by infer_instance)

end BoundedOrder

-- It is important that in this section `IsSimpleOrder` is the last type-class argument.
section DecidableEq

variable [DecidableEq α] [PartialOrder α] [BoundedOrder α] [IsSimpleOrder α]

/-- Every simple lattice is isomorphic to `Bool`, regardless of order. -/
@[simps]
/-
**IsSimpleOrder.equivBool** 是 Mathlib 中的一个定义，位于命名空间 `IsSimpleOrder`。
形式化陈述：equivBool {α} [DecidableEq α] [LE α] [BoundedOrder α] [IsSimpleOrder α] : 
α ≃ Bool where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every simple lattice is isomorphic to `Bool`, regardless of order.
-/
def equivBool {α} [DecidableEq α] [LE α] [BoundedOrder α] [IsSimpleOrder α] : α ≃ Bool where
  toFun x := x = ⊤
  invFun x := x.casesOn ⊥ ⊤
  left_inv x := by rcases eq_bot_or_eq_top x with (rfl | rfl) <;> simp [bot_ne_top]
  right_inv x := by cases x <;> simp [bot_ne_top]

/-- Every simple lattice over a partial order is order-isomorphic to `Bool`. -/
/-
**IsSimpleOrder.orderIsoBool** 是 Mathlib 中的一个定义，位于命名空间 `IsSimpleOrder`。
形式化陈述：orderIsoBool : α ≃o Bool
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every simple lattice over a partial order is order-isomorphic to `Bool`.
-/
def orderIsoBool : α ≃o Bool :=
  { equivBool with
    map_rel_iff' := @fun a b => by
      rcases eq_bot_or_eq_top a with (rfl | rfl)
      · simp
      · rcases eq_bot_or_eq_top b with (rfl | rfl)
        · simp [bot_ne_top.symm, Bool.false_lt_true]
        · simp }

/-- A simple `BoundedOrder` is also a `BooleanAlgebra`. -/
@[instance_reducible]
/-
**IsSimpleOrder.booleanAlgebra** 是 Mathlib 中的一个定义，位于命名空间 `IsSimpleOrder`。
形式化陈述：{α : Type u_4} → [DecidableEq α] → [inst : Lattice α] → [inst_1 : BoundedO
rder α] → [IsSimpleOrder α] → BooleanAlgebra α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A simple `BoundedOrder` is also a `BooleanAlgebra`.
-/
protected def booleanAlgebra {α} [DecidableEq α] [Lattice α] [BoundedOrder α] [IsSimpleOrder α] :
    BooleanAlgebra α :=
  { (inferInstance : BoundedOrder α), IsSimpleOrder.distribLattice with
    compl := fun x => if x = ⊥ then ⊤ else ⊥
    sdiff := fun x y => if x = ⊤ ∧ y = ⊥ then ⊤ else ⊥
    sdiff_eq := fun x y => by
      rcases eq_bot_or_eq_top x with (rfl | rfl) <;> simp
    inf_compl_le_bot := fun x => by
      rcases eq_bot_or_eq_top x with (rfl | rfl)
      · simp
      · simp
    top_le_sup_compl := fun x => by rcases eq_bot_or_eq_top x with (rfl | rfl) <;> simp }

end DecidableEq

variable [Lattice α] [BoundedOrder α] [IsSimpleOrder α]

open scoped Classical in
/-- A simple `BoundedOrder` is also complete. -/
@[instance_reducible]
/-
**IsSimpleOrder.completeLattice** 是 Mathlib 中的一个定义，位于命名空间 `IsSimpleOrder`。
形式化陈述：{α : Type u_2} → [inst : Lattice α] → [inst_1 : BoundedOrder α] → [IsSimpl
eOrder α] → CompleteLattice α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A simple `BoundedOrder` is also complete.
-/
protected noncomputable def completeLattice : CompleteLattice α :=
  { (inferInstance : Lattice α),
    (inferInstance : BoundedOrder α) with
    sSup := fun s => if ⊤ ∈ s then ⊤ else ⊥
    sInf := fun s => if ⊥ ∈ s then ⊥ else ⊤
    isLUB_sSup s := by
      refine ⟨fun x h ↦ ?_, fun x h ↦ ?_⟩
      · rcases eq_bot_or_eq_top x with (rfl | rfl)
        · exact bot_le
        · rw [if_pos h]
      · rcases eq_bot_or_eq_top x with (rfl | rfl)
        · rw [if_neg]
          intro con
          exact bot_ne_top (eq_top_iff.2 (h con))
        · exact le_top
    isGLB_sInf s := by
      refine ⟨fun x h ↦ ?_, fun x h ↦ ?_⟩
      · rcases eq_bot_or_eq_top x with (rfl | rfl)
        · rw [if_pos h]
        · exact le_top
      · rcases eq_bot_or_eq_top x with (rfl | rfl)
        · exact bot_le
        · rw [if_neg]
          intro con
          exact top_ne_bot (eq_bot_iff.2 (h con)) }

open scoped Classical in
/-- A simple `BoundedOrder` is also a `CompleteBooleanAlgebra`. -/
@[instance_reducible]
/-
**IsSimpleOrder.completeBooleanAlgebra** 是 Mathlib 中的一个定义，位于命名空间 `IsSimpleOrder`
。
形式化陈述：{α : Type u_2} → [inst : Lattice α] → [inst_1 : BoundedOrder α] → [IsSimpl
eOrder α] → CompleteBooleanAlgebra α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `BooleanAlgebra.inf_compl_le_bot`：∀ {α : Type u} [self : BooleanAlgebra α
] (x : α), x ⊓ xᶜ ≤ ⊥
· 使用定理 `BooleanAlgebra.top_le_sup_compl`：∀ {α : Type u} [self : BooleanAlgebra α
] (x : α), ⊤ ≤ x ⊔ xᶜ
· 使用定理 `BooleanAlgebra.sdiff_eq`：∀ {α : Type u} [self : BooleanAlgebra α] (x y :
 α), x \ y = x ⊓ yᶜ
· 使用定理 `BooleanAlgebra.himp_eq`：∀ {α : Type u} [self : BooleanAlgebra α] (x y : 
α), x ⇨ y = y ⊔ xᶜ

--- 原说明 ---
A simple `BoundedOrder` is also a `CompleteBooleanAlgebra`.
-/
protected noncomputable def completeBooleanAlgebra : CompleteBooleanAlgebra α :=
  { __ := IsSimpleOrder.completeLattice
    __ := IsSimpleOrder.booleanAlgebra }
/-
**IsSimpleOrder.** 是 Mathlib 中的一个实例，位于命名空间 `IsSimpleOrder`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ComplementedLattice α :=
  letI := IsSimpleOrder.completeBooleanAlgebra (α := α); inferInstance

end IsSimpleOrder

namespace IsSimpleOrder

variable [PartialOrder α] [BoundedOrder α] [IsSimpleOrder α]

/-
**IsSimpleOrder.** 是 Mathlib 中的一个实例，位于命名空间 `IsSimpleOrder`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) : IsAtomistic α where
  isLUB_atoms b := (eq_bot_or_eq_top b).elim (fun h ↦ ⟨∅, by simp [h]⟩) (fun h ↦ ⟨{⊤}, by simp [h]⟩)
/-
**IsSimpleOrder.** 是 Mathlib 中的一个实例，位于命名空间 `IsSimpleOrder`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) : IsCoatomistic α :=
  isAtomistic_dual_iff_isCoatomistic.1 (by infer_instance)
/-
**IsSimpleOrder.bot_lt_iff_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `IsSimpleOrder`。
形式化陈述：∀ {α : Type u_2} [inst : PartialOrder α] [inst_1 : BoundedOrder α] [IsSimp
leOrder α] {a : α}, ⊥ < a ↔ a = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSimpleOrder.eq_top_of_lt`：eq_top_of_lt : b = ⊤
· 使用定理 `bot_lt_top`：bot_lt_top : (⊥ : α) < ⊤
· 使用定理 `IsSimpleOrder.toNontrivial`：∀ {α : Type u_4} {inst : LE α} {inst_1 : Bou
ndedOrder α} [self : IsSimpleOrder α], Nontrivial α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp] lemma bot_lt_iff_eq_top {a : α} : ⊥ < a ↔ a = ⊤ :=
  ⟨eq_top_of_lt, fun h ↦ h ▸ bot_lt_top⟩
/-
**IsSimpleOrder.lt_top_iff_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `IsSimpleOrder`。
形式化陈述：∀ {α : Type u_2} [inst : PartialOrder α] [inst_1 : BoundedOrder α] [IsSimp
leOrder α] {a : α}, a < ⊤ ↔ a = ⊥
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSimpleOrder.eq_bot_of_lt`：eq_bot_of_lt : a = ⊥
· 使用定理 `bot_lt_top`：bot_lt_top : (⊥ : α) < ⊤
· 使用定理 `IsSimpleOrder.toNontrivial`：∀ {α : Type u_4} {inst : LE α} {inst_1 : Bou
ndedOrder α} [self : IsSimpleOrder α], Nontrivial α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp] lemma lt_top_iff_eq_bot {a : α} : a < ⊤ ↔ a = ⊥ :=
  ⟨eq_bot_of_lt, fun h ↦ h ▸ bot_lt_top⟩

end IsSimpleOrder

/-
**isSimpleOrder_iff_isAtom_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isSimpleOrder_iff_isAtom_top [PartialOrder α] [BoundedOrder α] : IsSimpleO
rder α ↔ IsAtom (⊤ : α)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isAtom_top`：isAtom_top : IsAtom (⊤ : α)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem isSimpleOrder_iff_isAtom_top [PartialOrder α] [BoundedOrder α] :
    IsSimpleOrder α ↔ IsAtom (⊤ : α) :=
  ⟨fun h => @isAtom_top _ _ _ h, fun h =>
    { exists_pair_ne := ⟨⊤, ⊥, h.1⟩
      eq_bot_or_eq_top := fun a => ((eq_or_lt_of_le le_top).imp_right (h.2 a)).symm }⟩
/-
**isSimpleOrder_iff_isCoatom_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isSimpleOrder_iff_isCoatom_bot [PartialOrder α] [BoundedOrder α] : IsSimpl
eOrder α ↔ IsCoatom (⊥ : α)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `isSimpleOrder_iff_isSimpleOrder_orderDual`：isSimpleOrder_iff_isSimpleOrd
er_orderDual [LE α] [BoundedOrder α] : IsSimpleOrder α ↔ IsSimpleOrder αᵒᵈ
· 使用定理 `isSimpleOrder_iff_isAtom_top`：isSimpleOrder_iff_isAtom_top [PartialOrder
 α] [BoundedOrder α] : IsSimpleOrder α ↔ IsAtom (⊤ : α)
-/
theorem isSimpleOrder_iff_isCoatom_bot [PartialOrder α] [BoundedOrder α] :
    IsSimpleOrder α ↔ IsCoatom (⊥ : α) :=
  isSimpleOrder_iff_isSimpleOrder_orderDual.trans isSimpleOrder_iff_isAtom_top

namespace Set

/-
**Set.isSimpleOrder_Iic_iff_isAtom** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：isSimpleOrder_Iic_iff_isAtom [PartialOrder α] [OrderBot α] {a : α} : IsSim
pleOrder (Iic a) ↔ IsAtom a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `isSimpleOrder_iff_isAtom_top`：isSimpleOrder_iff_isAtom_top [PartialOrder
 α] [BoundedOrder α] : IsSimpleOrder α ↔ IsAtom (⊤ : α)
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Subtype.mk_eq_mk`：mk_eq_mk {a h a' h'} : @mk α p a h = @mk α p a' h' ↔ a
 = a'
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subtype.mk_lt_mk`：mk_lt_mk [LT α] {p : α -> Prop} {x y : α} {hx : p x} {
hy : p y} : (⟨x, hx⟩ : Subtype p) < ⟨y, hy⟩ ↔ x < y
-/
theorem isSimpleOrder_Iic_iff_isAtom [PartialOrder α] [OrderBot α] {a : α} :
    IsSimpleOrder (Iic a) ↔ IsAtom a :=
  isSimpleOrder_iff_isAtom_top.trans <|
    and_congr (not_congr Subtype.mk_eq_mk)
      ⟨fun h b ab => Subtype.mk_eq_mk.1 (h ⟨b, le_of_lt ab⟩ ab), fun h ⟨b, _⟩ hbotb =>
        Subtype.mk_eq_mk.2 (h b (Subtype.mk_lt_mk.1 hbotb))⟩
/-
**Set.isSimpleOrder_Ici_iff_isCoatom** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：isSimpleOrder_Ici_iff_isCoatom [PartialOrder α] [OrderTop α] {a : α} : IsS
impleOrder (Ici a) ↔ IsCoatom a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `isSimpleOrder_iff_isCoatom_bot`：isSimpleOrder_iff_isCoatom_bot [PartialO
rder α] [BoundedOrder α] : IsSimpleOrder α ↔ IsCoatom (⊥ : α)
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Subtype.mk_eq_mk`：mk_eq_mk {a h a' h'} : @mk α p a h = @mk α p a' h' ↔ a
 = a'
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subtype.mk_lt_mk`：mk_lt_mk [LT α] {p : α -> Prop} {x y : α} {hx : p x} {
hy : p y} : (⟨x, hx⟩ : Subtype p) < ⟨y, hy⟩ ↔ x < y
-/
theorem isSimpleOrder_Ici_iff_isCoatom [PartialOrder α] [OrderTop α] {a : α} :
    IsSimpleOrder (Ici a) ↔ IsCoatom a :=
  isSimpleOrder_iff_isCoatom_bot.trans <|
    and_congr (not_congr Subtype.mk_eq_mk)
      ⟨fun h b ab => Subtype.mk_eq_mk.1 (h ⟨b, le_of_lt ab⟩ ab), fun h ⟨b, _⟩ hbotb =>
        Subtype.mk_eq_mk.2 (h b (Subtype.mk_lt_mk.1 hbotb))⟩

end Set

namespace OrderEmbedding

variable [PartialOrder α] [PartialOrder β]

/-
**OrderEmbedding.isAtom_of_map_bot_of_image** 是 Mathlib 中的一个定理，位于命名空间 `OrderEmbe
dding`。
形式化陈述：isAtom_of_map_bot_of_image [OrderBot α] [OrderBot β] (f : β ↪o α) (hbot : 
f ⊥ = ⊥) {b : β} (hb : IsAtom (f b)) : IsAtom b
参数：f : β ↪o α；hbot : f ⊥ = ⊥；hb : IsAtom (f b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CovBy.of_image`：CovBy.of_image (f : α ↪o β) (h : f a ⋖ f b) : a ⋖ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isAtom_of_map_bot_of_image [OrderBot α] [OrderBot β] (f : β ↪o α) (hbot : f ⊥ = ⊥) {b : β}
    (hb : IsAtom (f b)) : IsAtom b := by
  simp only [← bot_covBy_iff] at hb ⊢
  exact CovBy.of_image f (hbot.symm ▸ hb)
/-
**OrderEmbedding.isCoatom_of_map_top_of_image** 是 Mathlib 中的一个定理，位于命名空间 `OrderEm
bedding`。
形式化陈述：isCoatom_of_map_top_of_image [OrderTop α] [OrderTop β] (f : β ↪o α) (htop 
: f ⊤ = ⊤) {b : β} (hb : IsCoatom (f b)) : IsCoatom b
参数：f : β ↪o α；htop : f ⊤ = ⊤；hb : IsCoatom (f b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.isAtom_of_map_bot_of_image`：isAtom_of_map_bot_of_image [O
rderBot α] [OrderBot β] (f : β ↪o α) (hbot : f ⊥ = ⊥) {b : β} (hb : IsAtom (f b)
) : IsAtom b
-/
theorem isCoatom_of_map_top_of_image [OrderTop α] [OrderTop β] (f : β ↪o α) (htop : f ⊤ = ⊤)
    {b : β} (hb : IsCoatom (f b)) : IsCoatom b :=
  f.dual.isAtom_of_map_bot_of_image htop hb

end OrderEmbedding

namespace GaloisInsertion

variable [PartialOrder α] [PartialOrder β]

/-
**GaloisInsertion.isAtom_of_u_bot** 是 Mathlib 中的一个定理，位于命名空间 `GaloisInsertion`。
形式化陈述：isAtom_of_u_bot [OrderBot α] [OrderBot β] {l : α -> β} {u : β -> α} (gi : 
GaloisInsertion l u) (hbot : u ⊥ = ⊥) {b : β} (hb : IsAtom (u b)) : IsAtom b
参数：gi : GaloisInsertion l u；hbot : u ⊥ = ⊥；hb : IsAtom (u b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.isAtom_of_map_bot_of_image`：isAtom_of_map_bot_of_image [O
rderBot α] [OrderBot β] (f : β ↪o α) (hbot : f ⊥ = ⊥) {b : β} (hb : IsAtom (f b)
) : IsAtom b
· 使用定理 `GaloisInsertion.u_injective`：u_injective [Preorder α] [PartialOrder β] (
gi : GaloisInsertion l u) : Injective u
· 使用定理 `GaloisInsertion.u_le_u_iff`：u_le_u_iff [Preorder α] [Preorder β] (gi : G
aloisInsertion l u) {a b} : u a <= u b ↔ a <= b
-/
theorem isAtom_of_u_bot [OrderBot α] [OrderBot β] {l : α → β} {u : β → α}
    (gi : GaloisInsertion l u) (hbot : u ⊥ = ⊥) {b : β} (hb : IsAtom (u b)) : IsAtom b :=
  OrderEmbedding.isAtom_of_map_bot_of_image
    ⟨⟨u, gi.u_injective⟩, @GaloisInsertion.u_le_u_iff _ _ _ _ _ _ gi⟩ hbot hb
/-
**GaloisInsertion.isAtom_iff** 是 Mathlib 中的一个定理，位于命名空间 `GaloisInsertion`。
形式化陈述：isAtom_iff [OrderBot α] [IsAtomic α] [OrderBot β] {l : α -> β} {u : β -> α
} (gi : GaloisInsertion l u) (hbot : u ⊥ = ⊥) (h_atom : forall a, IsAtom a -> u 
(l a) = a) (a : α) : IsAtom (l a) ↔ IsAtom a
参数：gi : GaloisInsertion l u；hbot : u ⊥ = ⊥；h_atom : forall a, IsAtom a -> u (l a
) = a；a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `IsAtomic.eq_bot_or_exists_atom_le`：∀ {α : Type u_2} {inst : PartialOrder
 α} {inst_1 : OrderBot α} [self : IsAtomic α] (b : α),   b = ⊥ ∨ ∃ a, IsAtom a ∧
 a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `GaloisInsertion.u_injective`：u_injective [Preorder α] [PartialOrder β] (
gi : GaloisInsertion l u) : Injective u
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsAtom.le_iff`：IsAtom.le_iff (h : IsAtom a) : x <= a ↔ x = ⊥ ∨ x = a
· 使用定理 `GaloisConnection.monotone_l`：∀ {α : Type u} {β : Type v} [inst : Preorde
r α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → Mon
otone l
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
· 使用定理 `GaloisInsertion.l_u_eq`：l_u_eq [Preorder α] [PartialOrder β] (gi : Galoi
sInsertion l u) (b : β) : l (u b) = b
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `GaloisConnection.le_u_l`：le_u_l (a) : a <= u (l a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `GaloisConnection.l_bot`：∀ {α : Type u} {β : Type v} [inst : PartialOrder
 α] [inst_1 : Preorder β] [inst_2 : OrderBot α] [inst_3 : OrderBot β]   {u : α →
 β} {l : β →…
· 使用定理 `GaloisInsertion.isAtom_of_u_bot`：isAtom_of_u_bot [OrderBot α] [OrderBot 
β] {l : α -> β} {u : β -> α} (gi : GaloisInsertion l u) (hbot : u ⊥ = ⊥) {b : β}
 (hb : IsAtom (u b)) …
-/
theorem isAtom_iff [OrderBot α] [IsAtomic α] [OrderBot β] {l : α → β} {u : β → α}
    (gi : GaloisInsertion l u) (hbot : u ⊥ = ⊥) (h_atom : ∀ a, IsAtom a → u (l a) = a) (a : α) :
    IsAtom (l a) ↔ IsAtom a := by
  refine ⟨fun hla => ?_, fun ha => gi.isAtom_of_u_bot hbot ((h_atom a ha).symm ▸ ha)⟩
  obtain ⟨a', ha', hab'⟩ :=
    (eq_bot_or_exists_atom_le (u (l a))).resolve_left (hbot ▸ fun h => hla.1 (gi.u_injective h))
  have :=
    (hla.le_iff.mp <| (gi.l_u_eq (l a) ▸ gi.gc.monotone_l hab' : l a' ≤ l a)).resolve_left fun h =>
      ha'.1 (hbot ▸ h_atom a' ha' ▸ congr_arg u h)
  have haa' : a = a' :=
    (ha'.le_iff.mp <|
          (gi.gc.le_u_l a).trans_eq (h_atom a' ha' ▸ congr_arg u this.symm)).resolve_left
      (mt (congr_arg l) (gi.gc.l_bot.symm ▸ hla.1))
  exact haa'.symm ▸ ha'
/-
**GaloisInsertion.isAtom_iff'** 是 Mathlib 中的一个定理，位于命名空间 `GaloisInsertion`。
形式化陈述：isAtom_iff' [OrderBot α] [IsAtomic α] [OrderBot β] {l : α -> β} {u : β -> 
α} (gi : GaloisInsertion l u) (hbot : u ⊥ = ⊥) (h_atom : forall a, IsAtom a -> u
 (l a) = a) (b : β) : IsAtom (u b) ↔ IsAtom b
参数：gi : GaloisInsertion l u；hbot : u ⊥ = ⊥；h_atom : forall a, IsAtom a -> u (l a
) = a；b : β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `GaloisInsertion.isAtom_iff`：isAtom_iff [OrderBot α] [IsAtomic α] [OrderB
ot β] {l : α -> β} {u : β -> α} (gi : GaloisInsertion l u) (hbot : u ⊥ = ⊥) (h_a
tom : forall a, …
· 使用定理 `GaloisInsertion.l_u_eq`：l_u_eq [Preorder α] [PartialOrder β] (gi : Galoi
sInsertion l u) (b : β) : l (u b) = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isAtom_iff' [OrderBot α] [IsAtomic α] [OrderBot β] {l : α → β} {u : β → α}
    (gi : GaloisInsertion l u) (hbot : u ⊥ = ⊥) (h_atom : ∀ a, IsAtom a → u (l a) = a) (b : β) :
    IsAtom (u b) ↔ IsAtom b := by rw [← gi.isAtom_iff hbot h_atom, gi.l_u_eq]
/-
**GaloisInsertion.isCoatom_of_image** 是 Mathlib 中的一个定理，位于命名空间 `GaloisInsertion`。
形式化陈述：isCoatom_of_image [OrderTop α] [OrderTop β] {l : α -> β} {u : β -> α} (gi 
: GaloisInsertion l u) {b : β} (hb : IsCoatom (u b)) : IsCoatom b
参数：gi : GaloisInsertion l u；hb : IsCoatom (u b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.isCoatom_of_map_top_of_image`：isCoatom_of_map_top_of_imag
e [OrderTop α] [OrderTop β] (f : β ↪o α) (htop : f ⊤ = ⊤) {b : β} (hb : IsCoatom
 (f b)) : IsCoatom b
· 使用定理 `GaloisInsertion.u_injective`：u_injective [Preorder α] [PartialOrder β] (
gi : GaloisInsertion l u) : Injective u
· 使用定理 `GaloisInsertion.u_le_u_iff`：u_le_u_iff [Preorder α] [Preorder β] (gi : G
aloisInsertion l u) {a b} : u a <= u b ↔ a <= b
· 使用定理 `GaloisConnection.u_top`：u_top [OrderTop β] {l : α -> β} {u : β -> α} (gc
 : GaloisConnection l u) : u ⊤ = ⊤
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
-/
theorem isCoatom_of_image [OrderTop α] [OrderTop β] {l : α → β} {u : β → α}
    (gi : GaloisInsertion l u) {b : β} (hb : IsCoatom (u b)) : IsCoatom b :=
  OrderEmbedding.isCoatom_of_map_top_of_image
    ⟨⟨u, gi.u_injective⟩, @GaloisInsertion.u_le_u_iff _ _ _ _ _ _ gi⟩ gi.gc.u_top hb
/-
**GaloisInsertion.isCoatom_iff** 是 Mathlib 中的一个定理，位于命名空间 `GaloisInsertion`。
形式化陈述：isCoatom_iff [OrderTop α] [IsCoatomic α] [OrderTop β] {l : α -> β} {u : β 
-> α} (gi : GaloisInsertion l u) (h_coatom : forall a : α, IsCoatom a -> u (l a)
 = a) (b : β) : IsCoatom (u b) ↔ IsCoatom b
参数：gi : GaloisInsertion l u；h_coatom : forall a : α, IsCoatom a -> u (l a) = a；b
 : β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.isCoatom_of_image`：isCoatom_of_image [OrderTop α] [Order
Top β] {l : α -> β} {u : β -> α} (gi : GaloisInsertion l u) {b : β} (hb : IsCoat
om (u b)) : IsCoatom b
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `IsCoatomic.eq_top_or_exists_le_coatom`：∀ {α : Type u_2} {inst : PartialO
rder α} {inst_1 : OrderTop α} [self : IsCoatomic α] (b : α),   b = ⊤ ∨ ∃ a, IsCo
atom a ∧ b ≤ a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `GaloisInsertion.l_u_eq`：l_u_eq [Preorder α] [PartialOrder β] (gi : Galoi
sInsertion l u) (b : β) : l (u b) = b
· 使用定理 `GaloisConnection.u_top`：u_top [OrderTop β] {l : α -> β} {u : β -> α} (gc
 : GaloisConnection l u) : u ⊤ = ⊤
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsCoatom.le_iff`：IsCoatom.le_iff (h : IsCoatom a) : a <= x ↔ x = ⊤ ∨ x =
 a
· 使用定理 `GaloisConnection.monotone_l`：∀ {α : Type u} {β : Type v} [inst : Preorde
r α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → Mon
otone l
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isCoatom_iff [OrderTop α] [IsCoatomic α] [OrderTop β] {l : α → β} {u : β → α}
    (gi : GaloisInsertion l u) (h_coatom : ∀ a : α, IsCoatom a → u (l a) = a) (b : β) :
    IsCoatom (u b) ↔ IsCoatom b := by
  refine ⟨fun hb => gi.isCoatom_of_image hb, fun hb => ?_⟩
  obtain ⟨a, ha, hab⟩ :=
    (eq_top_or_exists_le_coatom (u b)).resolve_left fun h =>
      hb.1 <| (gi.gc.u_top ▸ gi.l_u_eq ⊤ : l ⊤ = ⊤) ▸ gi.l_u_eq b ▸ congr_arg l h
  have : l a = b :=
    (hb.le_iff.mp (gi.l_u_eq b ▸ gi.gc.monotone_l hab : b ≤ l a)).resolve_left fun hla =>
      ha.1 (gi.gc.u_top ▸ h_coatom a ha ▸ congr_arg u hla)
  exact this ▸ (h_coatom a ha).symm ▸ ha

end GaloisInsertion

namespace GaloisCoinsertion

variable [PartialOrder α] [PartialOrder β]

/-
**GaloisCoinsertion.isCoatom_of_l_top** 是 Mathlib 中的一个定理，位于命名空间 `GaloisCoinserti
on`。
形式化陈述：isCoatom_of_l_top [OrderTop α] [OrderTop β] {l : α -> β} {u : β -> α} (gi 
: GaloisCoinsertion l u) (hbot : l ⊤ = ⊤) {a : α} (hb : IsCoatom (l a)) : IsCoat
om a
参数：gi : GaloisCoinsertion l u；hbot : l ⊤ = ⊤；hb : IsCoatom (l a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.isAtom_of_u_bot`：isAtom_of_u_bot [OrderBot α] [OrderBot 
β] {l : α -> β} {u : β -> α} (gi : GaloisInsertion l u) (hbot : u ⊥ = ⊥) {b : β}
 (hb : IsAtom (u b)) …
· 使用定理 `IsCoatom.dual`：∀ {α : Type u_2} [inst : Preorder α] [inst_1 : OrderTop α
] {a : α}, IsCoatom a → IsAtom (OrderDual.toDual a)
-/
theorem isCoatom_of_l_top [OrderTop α] [OrderTop β] {l : α → β} {u : β → α}
    (gi : GaloisCoinsertion l u) (hbot : l ⊤ = ⊤) {a : α} (hb : IsCoatom (l a)) : IsCoatom a :=
  gi.dual.isAtom_of_u_bot hbot hb.dual
/-
**GaloisCoinsertion.isCoatom_iff** 是 Mathlib 中的一个定理，位于命名空间 `GaloisCoinsertion`。
形式化陈述：isCoatom_iff [OrderTop α] [OrderTop β] [IsCoatomic β] {l : α -> β} {u : β 
-> α} (gi : GaloisCoinsertion l u) (htop : l ⊤ = ⊤) (h_coatom : forall b, IsCoat
om b -> l (u b) = b) (b : β) : IsCoatom (u b) ↔ IsCoatom b
参数：gi : GaloisCoinsertion l u；htop : l ⊤ = ⊤；h_coatom : forall b, IsCoatom b -> 
l (u b) = b；b : β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.isAtom_iff`：isAtom_iff [OrderBot α] [IsAtomic α] [OrderB
ot β] {l : α -> β} {u : β -> α} (gi : GaloisInsertion l u) (hbot : u ⊥ = ⊥) (h_a
tom : forall a, …
· 使用定理 `OrderDual.instIsAtomic`：∀ {α : Type u_2} [inst : PartialOrder α] [inst_1
 : OrderTop α] [IsCoatomic α], IsAtomic αᵒᵈ
-/
theorem isCoatom_iff [OrderTop α] [OrderTop β] [IsCoatomic β] {l : α → β} {u : β → α}
    (gi : GaloisCoinsertion l u) (htop : l ⊤ = ⊤) (h_coatom : ∀ b, IsCoatom b → l (u b) = b)
    (b : β) : IsCoatom (u b) ↔ IsCoatom b :=
  gi.dual.isAtom_iff htop h_coatom b
/-
**GaloisCoinsertion.isCoatom_iff'** 是 Mathlib 中的一个定理，位于命名空间 `GaloisCoinsertion`。
形式化陈述：isCoatom_iff' [OrderTop α] [OrderTop β] [IsCoatomic β] {l : α -> β} {u : β
 -> α} (gi : GaloisCoinsertion l u) (htop : l ⊤ = ⊤) (h_coatom : forall b, IsCoa
tom b -> l (u b) = b) (a : α) : IsCoatom (l a) ↔ IsCoatom a
参数：gi : GaloisCoinsertion l u；htop : l ⊤ = ⊤；h_coatom : forall b, IsCoatom b -> 
l (u b) = b；a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.isAtom_iff'`：isAtom_iff' [OrderBot α] [IsAtomic α] [Orde
rBot β] {l : α -> β} {u : β -> α} (gi : GaloisInsertion l u) (hbot : u ⊥ = ⊥) (h
_atom : forall a,…
· 使用定理 `OrderDual.instIsAtomic`：∀ {α : Type u_2} [inst : PartialOrder α] [inst_1
 : OrderTop α] [IsCoatomic α], IsAtomic αᵒᵈ
-/
theorem isCoatom_iff' [OrderTop α] [OrderTop β] [IsCoatomic β] {l : α → β} {u : β → α}
    (gi : GaloisCoinsertion l u) (htop : l ⊤ = ⊤) (h_coatom : ∀ b, IsCoatom b → l (u b) = b)
    (a : α) : IsCoatom (l a) ↔ IsCoatom a :=
  gi.dual.isAtom_iff' htop h_coatom a
/-
**GaloisCoinsertion.isAtom_of_image** 是 Mathlib 中的一个定理，位于命名空间 `GaloisCoinsertion
`。
形式化陈述：isAtom_of_image [OrderBot α] [OrderBot β] {l : α -> β} {u : β -> α} (gi : 
GaloisCoinsertion l u) {a : α} (hb : IsAtom (l a)) : IsAtom a
参数：gi : GaloisCoinsertion l u；hb : IsAtom (l a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.isCoatom_of_image`：isCoatom_of_image [OrderTop α] [Order
Top β] {l : α -> β} {u : β -> α} (gi : GaloisInsertion l u) {b : β} (hb : IsCoat
om (u b)) : IsCoatom b
· 使用定理 `IsAtom.dual`：∀ {α : Type u_2} [inst : Preorder α] [inst_1 : OrderBot α] 
{a : α}, IsAtom a → IsCoatom (OrderDual.toDual a)
-/
theorem isAtom_of_image [OrderBot α] [OrderBot β] {l : α → β} {u : β → α}
    (gi : GaloisCoinsertion l u) {a : α} (hb : IsAtom (l a)) : IsAtom a :=
  gi.dual.isCoatom_of_image hb.dual
/-
**GaloisCoinsertion.isAtom_iff** 是 Mathlib 中的一个定理，位于命名空间 `GaloisCoinsertion`。
形式化陈述：isAtom_iff [OrderBot α] [OrderBot β] [IsAtomic β] {l : α -> β} {u : β -> α
} (gi : GaloisCoinsertion l u) (h_atom : forall b, IsAtom b -> l (u b) = b) (a :
 α) : IsAtom (l a) ↔ IsAtom a
参数：gi : GaloisCoinsertion l u；h_atom : forall b, IsAtom b -> l (u b) = b；a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.isCoatom_iff`：isCoatom_iff [OrderTop α] [IsCoatomic α] [
OrderTop β] {l : α -> β} {u : β -> α} (gi : GaloisInsertion l u) (h_coatom : for
all a : α, IsCoato…
· 使用定理 `OrderDual.instIsCoatomic`：∀ {α : Type u_2} [inst : PartialOrder α] [inst
_1 : OrderBot α] [IsAtomic α], IsCoatomic αᵒᵈ
-/
theorem isAtom_iff [OrderBot α] [OrderBot β] [IsAtomic β] {l : α → β} {u : β → α}
    (gi : GaloisCoinsertion l u) (h_atom : ∀ b, IsAtom b → l (u b) = b) (a : α) :
    IsAtom (l a) ↔ IsAtom a :=
  gi.dual.isCoatom_iff h_atom a

end GaloisCoinsertion

namespace OrderIso

variable [PartialOrder α] [PartialOrder β]

@[simp]
/-
**OrderIso.isAtom_iff** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：isAtom_iff [OrderBot α] [OrderBot β] (f : α ≃o β) (a : α) : IsAtom (f a) ↔
 IsAtom a
参数：f : α ≃o β；a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.isAtom_of_image`：isAtom_of_image [OrderBot α] [OrderBo
t β] {l : α -> β} {u : β -> α} (gi : GaloisCoinsertion l u) {a : α} (hb : IsAtom
 (l a)) : IsAtom a
· 使用定理 `GaloisInsertion.isAtom_of_u_bot`：isAtom_of_u_bot [OrderBot α] [OrderBot 
β] {l : α -> β} {u : β -> α} (gi : GaloisInsertion l u) (hbot : u ⊥ = ⊥) {b : β}
 (hb : IsAtom (u b)) …
· 使用定理 `OrderIso.map_bot`：OrderIso.map_bot [LE α] [PartialOrder β] [OrderBot α] 
[OrderBot β] (f : α ≃o β) : f ⊥ = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderIso.symm_apply_apply`：symm_apply_apply (e : α ≃o β) (x : α) : e.sym
m (e x) = x
-/
theorem isAtom_iff [OrderBot α] [OrderBot β] (f : α ≃o β) (a : α) : IsAtom (f a) ↔ IsAtom a :=
  ⟨f.toGaloisCoinsertion.isAtom_of_image, fun ha =>
    f.toGaloisInsertion.isAtom_of_u_bot (map_bot f.symm) <| (f.symm_apply_apply a).symm ▸ ha⟩

@[simp]
/-
**OrderIso.isCoatom_iff** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：isCoatom_iff [OrderTop α] [OrderTop β] (f : α ≃o β) (a : α) : IsCoatom (f 
a) ↔ IsCoatom a
参数：f : α ≃o β；a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.isAtom_iff`：isAtom_iff [OrderBot α] [OrderBot β] (f : α ≃o β) (
a : α) : IsAtom (f a) ↔ IsAtom a
-/
theorem isCoatom_iff [OrderTop α] [OrderTop β] (f : α ≃o β) (a : α) :
    IsCoatom (f a) ↔ IsCoatom a :=
  f.dual.isAtom_iff a
/-
**OrderIso.isSimpleOrder_iff** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：isSimpleOrder_iff [BoundedOrder α] [BoundedOrder β] (f : α ≃o β) : IsSimpl
eOrder α ↔ IsSimpleOrder β
参数：f : α ≃o β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isSimpleOrder_iff_isAtom_top`：isSimpleOrder_iff_isAtom_top [PartialOrder
 α] [BoundedOrder α] : IsSimpleOrder α ↔ IsAtom (⊤ : α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderIso.isAtom_iff`：isAtom_iff [OrderBot α] [OrderBot β] (f : α ≃o β) (
a : α) : IsAtom (f a) ↔ IsAtom a
· 使用定理 `OrderIso.map_top`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst_1 
: PartialOrder β] [inst_2 : OrderTop α] [inst_3 : OrderTop β]   (f : α ≃o β), f 
⊤ = ⊤
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isSimpleOrder_iff [BoundedOrder α] [BoundedOrder β] (f : α ≃o β) :
    IsSimpleOrder α ↔ IsSimpleOrder β := by
  rw [isSimpleOrder_iff_isAtom_top, isSimpleOrder_iff_isAtom_top, ← f.isAtom_iff ⊤,
    f.map_top]
/-
**OrderIso.isSimpleOrder** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：isSimpleOrder [BoundedOrder α] [BoundedOrder β] [h : IsSimpleOrder β] (f :
 α ≃o β) : IsSimpleOrder α
参数：f : α ≃o β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `OrderIso.isSimpleOrder_iff`：isSimpleOrder_iff [BoundedOrder α] [BoundedO
rder β] (f : α ≃o β) : IsSimpleOrder α ↔ IsSimpleOrder β
-/
theorem isSimpleOrder [BoundedOrder α] [BoundedOrder β] [h : IsSimpleOrder β] (f : α ≃o β) :
    IsSimpleOrder α :=
  f.isSimpleOrder_iff.mpr h
/-
**OrderIso.isAtomic_iff** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : PartialOrder α] [inst_1 : PartialO
rder β] [inst_2 : OrderBot α]   [inst_3 : OrderBot β] (f : α ≃o β), IsAtomic α ↔
 IsAtomic β
参数：f : α ≃o β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderIso.map_bot`：OrderIso.map_bot [LE α] [PartialOrder β] [OrderBot α] 
[OrderBot β] (f : α ≃o β) : f ⊥ = ⊥
· 使用定理 `Function.Surjective.exists`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Surjective f → ∀ {p : β → Prop}, (∃ y, p y) ↔ ∃ x, p (f x)
· 使用定理 `OrderIso.surjective`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst
_1 : LE β] (e : α ≃o β), Function.Surjective ⇑e
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `OrderIso.isAtom_iff`：isAtom_iff [OrderBot α] [OrderBot β] (f : α ≃o β) (
a : α) : IsAtom (f a) ↔ IsAtom a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `RelIso.eq_iff_eq`：eq_iff_eq (f : r ≃r s) {a b} : f a = f b ↔ a = b
· 使用定理 `OrderIso.le_iff_le`：le_iff_le (e : α ≃o β) {x y : α} : e x <= e y ↔ x <=
 y
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected theorem isAtomic_iff [OrderBot α] [OrderBot β] (f : α ≃o β) :
    IsAtomic α ↔ IsAtomic β := by
  simp only [isAtomic_iff, f.surjective.forall, f.surjective.exists, ← map_bot f, f.eq_iff_eq,
    f.le_iff_le, f.isAtom_iff]
/-
**OrderIso.isCoatomic_iff** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : PartialOrder α] [inst_1 : PartialO
rder β] [inst_2 : OrderTop α]   [inst_3 : OrderTop β] (f : α ≃o β), IsCoatomic α
 ↔ IsCoatomic β
参数：f : α ≃o β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderIso.isAtomic_iff`：∀ {α : Type u_2} {β : Type u_3} [inst : PartialOr
der α] [inst_1 : PartialOrder β] [inst_2 : OrderBot α]   [inst_3 : OrderBot β] (
f : α ≃o β)…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected theorem isCoatomic_iff [OrderTop α] [OrderTop β] (f : α ≃o β) :
    IsCoatomic α ↔ IsCoatomic β := by
  simp only [← isAtomic_dual_iff_isCoatomic, f.dual.isAtomic_iff]

end OrderIso
section Lattice

variable [Lattice α]

/-- An upper-modular lattice that is atomistic is strongly atomic.
Not an instance to prevent loops. -/
/-
**Lattice.isStronglyAtomic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Lattice.isStronglyAtomic [OrderBot α] [IsUpperModularLattice α] [IsAtomist
ic α] : IsStronglyAtomic α where exists_covBy_le_of_lt a b hab
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAtomistic.isLUB_atoms`：∀ {α : Type u_2} {inst : PartialOrder α} {inst_
1 : OrderBot α} [self : IsAtomistic α] (b : α),   ∃ s, IsLUB s b ∧ ∀ a ∈ s, IsAt
om a
· 使用定理 `by_contra`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isLUB_le_iff`：isLUB_le_iff (h : IsLUB s a) : a <= b ↔ b in upperBounds s
· 使用定理 `CovBy.eq_or_eq`：CovBy.eq_or_eq (h : a ⋖ b) (h2 : a <= c) (h3 : c <= b) :
 c = a ∨ c = b
· 使用定理 `IsAtom.bot_covBy`：∀ {α : Type u_2} [inst : PartialOrder α] [inst_1 : Ord
erBot α] {a : α}, IsAtom a → ⊥ ⋖ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `IsUpperModularLattice.covBy_sup_of_inf_covBy`：∀ {α : Type u_2} {inst : L
attice α} [self : IsUpperModularLattice α] {a b : α}, a ⊓ b ⋖ a → b ⋖ a ⊔ b
· 使用定理 `inf_eq_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b =
 a ↔ a ≤ b

--- 原说明 ---
An upper-modular lattice that is atomistic is strongly atomic.
Not an instance to prevent loops.
-/
theorem Lattice.isStronglyAtomic [OrderBot α] [IsUpperModularLattice α] [IsAtomistic α] :
    IsStronglyAtomic α where
  exists_covBy_le_of_lt a b hab := by
    obtain ⟨s, hsb, h⟩ := isLUB_atoms b
    refine by_contra fun hcon ↦ hab.not_ge <| (isLUB_le_iff hsb).2 fun x hx ↦ ?_
    simp_rw [not_exists, and_comm (b := _ ≤ _), not_and] at hcon
    specialize hcon (x ⊔ a) (sup_le (hsb.1 hx) hab.le)
    obtain (hbot | h_inf) := (h x hx).bot_covBy.eq_or_eq (c := x ⊓ a) (by simp) (by simp)
    · exact False.elim <| hcon <|
        (hbot ▸ IsUpperModularLattice.covBy_sup_of_inf_covBy) (h x hx).bot_covBy
    rwa [inf_eq_left] at h_inf

/-- A lower-modular lattice that is coatomistic is strongly coatomic.
Not an instance to prevent loops. -/
/-
**Lattice.isStronglyCoatomic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Lattice.isStronglyCoatomic [OrderTop α] [IsLowerModularLattice α] [IsCoato
mistic α] : IsStronglyCoatomic α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isStronglyAtomic_dual_iff_is_stronglyCoatomic`：isStronglyAtomic_dual_iff
_is_stronglyCoatomic : IsStronglyAtomic αᵒᵈ ↔ IsStronglyCoatomic α
· 使用定理 `Lattice.isStronglyAtomic`：Lattice.isStronglyAtomic [OrderBot α] [IsUpper
ModularLattice α] [IsAtomistic α] : IsStronglyAtomic α where exists_covBy_le_of_
lt a b hab
· 使用定理 `instIsUpperModularLatticeOrderDual`：∀ {α : Type u_1} [inst : Lattice α] 
[IsLowerModularLattice α], IsUpperModularLattice αᵒᵈ
· 使用定理 `OrderDual.instIsAtomistic`：∀ {α : Type u_2} [inst : PartialOrder α] [ins
t_1 : OrderTop α] [h : IsCoatomistic α], IsAtomistic αᵒᵈ

--- 原说明 ---
A lower-modular lattice that is coatomistic is strongly coatomic.
Not an instance to prevent loops.
-/
theorem Lattice.isStronglyCoatomic [OrderTop α] [IsLowerModularLattice α]
    [IsCoatomistic α] : IsStronglyCoatomic α := by
  rw [← isStronglyAtomic_dual_iff_is_stronglyCoatomic]
  exact Lattice.isStronglyAtomic

end Lattice

section IsModularLattice

variable [Lattice α] [BoundedOrder α] [IsModularLattice α]

namespace IsCompl

variable {a b : α} (hc : IsCompl a b)
include hc

/-
**IsCompl.isAtom_iff_isCoatom** 是 Mathlib 中的一个定理，位于命名空间 `IsCompl`。
形式化陈述：isAtom_iff_isCoatom : IsAtom a ↔ IsCoatom b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Set.isSimpleOrder_Iic_iff_isAtom`：isSimpleOrder_Iic_iff_isAtom [PartialO
rder α] [OrderBot α] {a : α} : IsSimpleOrder (Iic a) ↔ IsAtom a
· 使用定理 `OrderIso.isSimpleOrder_iff`：isSimpleOrder_iff [BoundedOrder α] [BoundedO
rder β] (f : α ≃o β) : IsSimpleOrder α ↔ IsSimpleOrder β
· 使用定理 `Set.isSimpleOrder_Ici_iff_isCoatom`：isSimpleOrder_Ici_iff_isCoatom [Part
ialOrder α] [OrderTop α] {a : α} : IsSimpleOrder (Ici a) ↔ IsCoatom a
-/
theorem isAtom_iff_isCoatom : IsAtom a ↔ IsCoatom b :=
  Set.isSimpleOrder_Iic_iff_isAtom.symm.trans <|
    hc.IicOrderIsoIci.isSimpleOrder_iff.trans Set.isSimpleOrder_Ici_iff_isCoatom
/-
**IsCompl.isCoatom_iff_isAtom** 是 Mathlib 中的一个定理，位于命名空间 `IsCompl`。
形式化陈述：isCoatom_iff_isAtom : IsCoatom a ↔ IsAtom b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `IsCompl.isAtom_iff_isCoatom`：isAtom_iff_isCoatom : IsAtom a ↔ IsCoatom b
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
-/
theorem isCoatom_iff_isAtom : IsCoatom a ↔ IsAtom b :=
  hc.symm.isAtom_iff_isCoatom.symm

end IsCompl

variable [ComplementedLattice α]

/-
**isCoatomic_of_isAtomic_of_complementedLattice_of_isModular** 是 Mathlib 中的一个定理，
位于命名空间 ``。
形式化陈述：isCoatomic_of_isAtomic_of_complementedLattice_of_isModular [IsAtomic α] : 
IsCoatomic α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ComplementedLattice.exists_isCompl`：∀ {α : Type u_2} {inst : Lattice α} 
{inst_1 : BoundedOrder α} [self : ComplementedLattice α] (a : α), ∃ b, IsCompl a
 b
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `eq_top_of_isCompl_bot`：eq_top_of_isCompl_bot (h : IsCompl x ⊥) : x = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
· 使用定理 `IsCoatom.of_isCoatom_coe_Ici`：IsCoatom.of_isCoatom_coe_Ici {a : Set.Ici 
x} (ha : IsCoatom a) : IsCoatom (a : α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsCompl.isAtom_iff_isCoatom`：isAtom_iff_isCoatom : IsAtom a ↔ IsCoatom b
· 使用定理 `OrderIso.isAtom_iff`：isAtom_iff [OrderBot α] [OrderBot β] (f : α ≃o β) (
a : α) : IsAtom (f a) ↔ IsAtom a
· 使用定理 `IsAtom.Iic`：IsAtom.Iic (ha : IsAtom a) (hax : a <= x) : IsAtom (⟨a, hax⟩
 : Set.Iic x)
· 使用定理 `IsAtomic.eq_bot_or_exists_atom_le`：∀ {α : Type u_2} {inst : PartialOrder
 α} {inst_1 : OrderBot α} [self : IsAtomic α] (b : α),   b = ⊥ ∨ ∃ a, IsAtom a ∧
 a ≤ b
-/
theorem isCoatomic_of_isAtomic_of_complementedLattice_of_isModular [IsAtomic α] :
    IsCoatomic α :=
  ⟨fun x => by
    rcases exists_isCompl x with ⟨y, xy⟩
    apply (eq_bot_or_exists_atom_le y).imp _ _
    · rintro rfl
      exact eq_top_of_isCompl_bot xy
    · rintro ⟨a, ha, ay⟩
      rcases exists_isCompl (xy.symm.IicOrderIsoIci ⟨a, ay⟩) with ⟨⟨b, xb⟩, hb⟩
      refine ⟨↑(⟨b, xb⟩ : Set.Ici x), IsCoatom.of_isCoatom_coe_Ici ?_, xb⟩
      rw [← hb.isAtom_iff_isCoatom, OrderIso.isAtom_iff]
      apply ha.Iic⟩
/-
**isAtomic_of_isCoatomic_of_complementedLattice_of_isModular** 是 Mathlib 中的一个定理，
位于命名空间 ``。
形式化陈述：isAtomic_of_isCoatomic_of_complementedLattice_of_isModular [IsCoatomic α] 
: IsAtomic α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isCoatomic_dual_iff_isAtomic`：isCoatomic_dual_iff_isAtomic [OrderBot α] 
: IsCoatomic αᵒᵈ ↔ IsAtomic α
· 使用定理 `isCoatomic_of_isAtomic_of_complementedLattice_of_isModular`：isCoatomic_o
f_isAtomic_of_complementedLattice_of_isModular [IsAtomic α] : IsCoatomic α
· 使用定理 `instIsModularLatticeOrderDual`：∀ {α : Type u_1} [inst : Lattice α] [IsMo
dularLattice α], IsModularLattice αᵒᵈ
· 使用定理 `ComplementedLattice.instOrderDual`：∀ {α : Type u_1} [inst : Lattice α] [
inst_1 : BoundedOrder α] [ComplementedLattice α], ComplementedLattice αᵒᵈ
· 使用定理 `OrderDual.instIsAtomic`：∀ {α : Type u_2} [inst : PartialOrder α] [inst_1
 : OrderTop α] [IsCoatomic α], IsAtomic αᵒᵈ
-/
theorem isAtomic_of_isCoatomic_of_complementedLattice_of_isModular [IsCoatomic α] :
    IsAtomic α :=
  isCoatomic_dual_iff_isAtomic.1 isCoatomic_of_isAtomic_of_complementedLattice_of_isModular
/-
**isAtomic_iff_isCoatomic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isAtomic_iff_isCoatomic : IsAtomic α ↔ IsCoatomic α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isCoatomic_of_isAtomic_of_complementedLattice_of_isModular`：isCoatomic_o
f_isAtomic_of_complementedLattice_of_isModular [IsAtomic α] : IsCoatomic α
· 使用定理 `isAtomic_of_isCoatomic_of_complementedLattice_of_isModular`：isAtomic_of_
isCoatomic_of_complementedLattice_of_isModular [IsCoatomic α] : IsAtomic α
-/
theorem isAtomic_iff_isCoatomic : IsAtomic α ↔ IsCoatomic α :=
  ⟨fun _ => isCoatomic_of_isAtomic_of_complementedLattice_of_isModular,
   fun _ => isAtomic_of_isCoatomic_of_complementedLattice_of_isModular⟩

set_option backward.isDefEq.respectTransparency false in
/-- A complemented modular atomic lattice is strongly atomic.
Not an instance to prevent loops. -/
/-
**ComplementedLattice.isStronglyAtomic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ComplementedLattice.isStronglyAtomic [IsAtomic α] : IsStronglyAtomic α whe
re exists_covBy_le_of_lt a b hab
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `ComplementedLattice.exists_isCompl`：∀ {α : Type u_2} {inst : Lattice α} 
{inst_1 : BoundedOrder α} [self : ComplementedLattice α] (a : α), ∃ b, IsCompl a
 b
· 使用定理 `IsAtomic.eq_bot_or_exists_atom_le`：∀ {α : Type u_2} {inst : PartialOrder
 α} {inst_1 : OrderBot α} [self : IsAtomic α] (b : α),   b = ⊥ ∨ ∃ a, IsAtom a ∧
 a ≤ b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.mk_bot`：mk_bot [OrderBot α] [OrderBot (Subtype p)] (hbot : p ⊥) 
: mk ⊥ hbot = ⊥
· 使用定理 `IsCompl.codisjoint`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : B
oundedOrder α] {x y : α}, IsCompl x y → Codisjoint x y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsUpperModularLattice.covBy_sup_of_inf_covBy`：∀ {α : Type u_2} {inst : L
attice α} [self : IsUpperModularLattice α] {a b : α}, a ⊓ b ⋖ a → b ⋖ a ⊔ b
· 使用定理 `IsModularLattice.to_isUpperModularLattice`：∀ {α : Type u_1} [inst : Latt
ice α] [IsModularLattice α], IsUpperModularLattice α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subtype.coe_inj`：coe_inj {a b : Subtype p} : (a : α) = b ↔ a = b
· 使用定理 `IsCompl.inf_eq_bot`：inf_eq_bot (h : IsCompl x y) : x ⊓ y = ⊥
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `inf_le_inf_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α} (c :
 α), b ≤ a → c ⊓ b ≤ c ⊓ a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `IsAtom.bot_covBy`：∀ {α : Type u_2} [inst : PartialOrder α] [inst_1 : Ord
erBot α] {a : α}, IsAtom a → ⊥ ⋖ a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c

--- 原说明 ---
A complemented modular atomic lattice is strongly atomic.
Not an instance to prevent loops.
-/
theorem ComplementedLattice.isStronglyAtomic [IsAtomic α] : IsStronglyAtomic α where
  exists_covBy_le_of_lt a b hab := by
    obtain ⟨⟨a', ha'b : a' ≤ b⟩, ha'⟩ := exists_isCompl (α := Set.Iic b) ⟨a, hab.le⟩
    obtain (rfl | ⟨d, hd⟩) := eq_bot_or_exists_atom_le a'
    · obtain rfl : a = b := by simpa [codisjoint_bot, ← Subtype.coe_inj] using ha'.codisjoint
      exact False.elim <| hab.ne rfl
    refine ⟨d ⊔ a, IsUpperModularLattice.covBy_sup_of_inf_covBy ?_, sup_le (hd.2.trans ha'b) hab.le⟩
    convert! hd.1.bot_covBy
    rw [← le_bot_iff, ← show a ⊓ a' = ⊥ by simpa using Subtype.coe_inj.2 ha'.inf_eq_bot, inf_comm]
    exact inf_le_inf_left _ hd.2

/-- A complemented modular coatomic lattice is strongly coatomic.
Not an instance to prevent loops. -/
/-
**ComplementedLattice.isStronglyCoatomic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ComplementedLattice.isStronglyCoatomic [IsCoatomic α] : IsStronglyCoatomic
 α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isStronglyAtomic_dual_iff_is_stronglyCoatomic`：isStronglyAtomic_dual_iff
_is_stronglyCoatomic : IsStronglyAtomic αᵒᵈ ↔ IsStronglyCoatomic α
· 使用定理 `ComplementedLattice.isStronglyAtomic`：ComplementedLattice.isStronglyAtom
ic [IsAtomic α] : IsStronglyAtomic α where exists_covBy_le_of_lt a b hab
· 使用定理 `instIsModularLatticeOrderDual`：∀ {α : Type u_1} [inst : Lattice α] [IsMo
dularLattice α], IsModularLattice αᵒᵈ
· 使用定理 `ComplementedLattice.instOrderDual`：∀ {α : Type u_1} [inst : Lattice α] [
inst_1 : BoundedOrder α] [ComplementedLattice α], ComplementedLattice αᵒᵈ
· 使用定理 `OrderDual.instIsAtomic`：∀ {α : Type u_2} [inst : PartialOrder α] [inst_1
 : OrderTop α] [IsCoatomic α], IsAtomic αᵒᵈ

--- 原说明 ---
A complemented modular coatomic lattice is strongly coatomic.
Not an instance to prevent loops.
-/
theorem ComplementedLattice.isStronglyCoatomic [IsCoatomic α] : IsStronglyCoatomic α :=
  isStronglyAtomic_dual_iff_is_stronglyCoatomic.1 <| ComplementedLattice.isStronglyAtomic

/-- A complemented modular atomic lattice is strongly coatomic.
Not an instance to prevent loops. -/
/-
**ComplementedLattice.isStronglyAtomic'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ComplementedLattice.isStronglyAtomic' [h : IsAtomic α] : IsStronglyCoatomi
c α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ComplementedLattice.isStronglyCoatomic`：ComplementedLattice.isStronglyCo
atomic [IsCoatomic α] : IsStronglyCoatomic α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isAtomic_iff_isCoatomic`：isAtomic_iff_isCoatomic : IsAtomic α ↔ IsCoatom
ic α

--- 原说明 ---
A complemented modular atomic lattice is strongly coatomic.
Not an instance to prevent loops.
-/
theorem ComplementedLattice.isStronglyAtomic' [h : IsAtomic α] : IsStronglyCoatomic α := by
  rw [isAtomic_iff_isCoatomic] at h
  exact isStronglyCoatomic

/-- A complemented modular coatomic lattice is strongly atomic.
Not an instance to prevent loops. -/
/-
**ComplementedLattice.isStronglyCoatomic'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ComplementedLattice.isStronglyCoatomic' [h : IsCoatomic α] : IsStronglyAto
mic α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ComplementedLattice.isStronglyAtomic`：ComplementedLattice.isStronglyAtom
ic [IsAtomic α] : IsStronglyAtomic α where exists_covBy_le_of_lt a b hab
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isAtomic_iff_isCoatomic`：isAtomic_iff_isCoatomic : IsAtomic α ↔ IsCoatom
ic α

--- 原说明 ---
A complemented modular coatomic lattice is strongly atomic.
Not an instance to prevent loops.
-/
theorem ComplementedLattice.isStronglyCoatomic' [h : IsCoatomic α] : IsStronglyAtomic α := by
  rw [← isAtomic_iff_isCoatomic] at h
  exact isStronglyAtomic

end IsModularLattice

namespace «Prop»

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsSimpleOrder Prop where
  eq_bot_or_eq_top p := by simp [em']
/-
**isAtom_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isAtom_iff {p : Prop} : IsAtom p ↔ p := by simp
/-
**isCoatom_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isCoatom_iff {p : Prop} : IsCoatom p ↔ ¬ p := by simp

end «Prop»

namespace Pi

universe u
variable {ι : Type*} {π : ι → Type u}

/-
**Pi.eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：∀ {ι : Type u_4} {π : ι → Type u} [inst : (i : ι) → Bot (π i)] {f : (i : ι
) → π i}, f = ⊥ ↔ ∀ (i : ι), f i = ⊥
参数：i : ι；π i；i : ι；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x
-/
protected theorem eq_bot_iff [∀ i, Bot (π i)] {f : ∀ i, π i} : f = ⊥ ↔ ∀ i, f i = ⊥ :=
  funext_iff
/-
**Pi.isAtom_iff** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：isAtom_iff {f : forall i, π i} [forall i, PartialOrder (π i)] [forall i, O
rderBot (π i)] : IsAtom f ↔ exists i, IsAtom (f i) ∧ forall j, j != i -> f j = ⊥
参数：π i；π i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isAtom_iff {f : ∀ i, π i} [∀ i, PartialOrder (π i)] [∀ i, OrderBot (π i)] :
    IsAtom f ↔ ∃ i, IsAtom (f i) ∧ ∀ j, j ≠ i → f j = ⊥ := by
  simp only [← bot_covBy_iff, Pi.covBy_iff, bot_apply, eq_comm]
/-
**Pi.isAtom_single** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：isAtom_single {i : ι} [DecidableEq ι] [forall i, PartialOrder (π i)] [fora
ll i, OrderBot (π i)] {a : π i} (h : IsAtom a) : IsAtom (Function.update (⊥ : fo
rall i, π i) i a)
参数：π i；π i；h : IsAtom a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Pi.isAtom_iff`：isAtom_iff {f : forall i, π i} [forall i, PartialOrder (π
 i)] [forall i, OrderBot (π i)] : IsAtom f ↔ exists i, IsAtom (f i) ∧ forall j, 
j !…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
-/
theorem isAtom_single {i : ι} [DecidableEq ι] [∀ i, PartialOrder (π i)] [∀ i, OrderBot (π i)]
    {a : π i} (h : IsAtom a) : IsAtom (Function.update (⊥ : ∀ i, π i) i a) :=
  isAtom_iff.2 ⟨i, by simpa, fun _ hji => Function.update_of_ne hji ..⟩
/-
**Pi.isAtom_iff_eq_single** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：isAtom_iff_eq_single [DecidableEq ι] [forall i, PartialOrder (π i)] [foral
l i, OrderBot (π i)] {f : forall i, π i} : IsAtom f ↔ exists i a, IsAtom a ∧ f =
 Function.update ⊥ i a
参数：π i；π i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isAtom_iff_eq_single [DecidableEq ι] [∀ i, PartialOrder (π i)]
    [∀ i, OrderBot (π i)] {f : ∀ i, π i} :
    IsAtom f ↔ ∃ i a, IsAtom a ∧ f = Function.update ⊥ i a := by
  simp [← bot_covBy_iff, covBy_iff_exists_right_eq]
/-
**Pi.isAtomic** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：isAtomic [forall i, PartialOrder (π i)] [forall i, OrderBot (π i)] [forall
 i, IsAtomic (π i)] : IsAtomic (forall i, π i) where eq_bot_or_exists_atom_le b
参数：π i；π i；π i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `Not.imp`：∀ {a b : Prop}, ¬b → (a → b) → ¬a
· 使用定理 `Pi.eq_bot_iff`：∀ {ι : Type u_4} {π : ι → Type u} [inst : (i : ι) → Bot (
π i)] {f : (i : ι) → π i}, f = ⊥ ↔ ∀ (i : ι), f i = ⊥
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `IsAtomic.eq_bot_or_exists_atom_le`：∀ {α : Type u_2} {inst : PartialOrder
 α} {inst_1 : OrderBot α} [self : IsAtomic α] (b : α),   b = ⊥ ∨ ∃ a, IsAtom a ∧
 a ≤ b
· 使用定理 `Pi.isAtom_single`：isAtom_single {i : ι} [DecidableEq ι] [forall i, Parti
alOrder (π i)] [forall i, OrderBot (π i)] {a : π i} (h : IsAtom a) : IsAtom (Fun
ction.…
· 使用定理 `update_le_iff`：∀ {ι : Type u_1} {π : ι → Type u_4} [inst : DecidableEq ι
] [inst_1 : (i : ι) → Preorder (π i)] {x y : (i : ι) → π i}   {i : ι} {a : π i},
 Fu…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
instance isAtomic [∀ i, PartialOrder (π i)] [∀ i, OrderBot (π i)] [∀ i, IsAtomic (π i)] :
    IsAtomic (∀ i, π i) where
  eq_bot_or_exists_atom_le b := or_iff_not_imp_left.2 fun h =>
    have ⟨i, hi⟩ : ∃ i, b i ≠ ⊥ := not_forall.1 (h.imp Pi.eq_bot_iff.2)
    have ⟨a, ha, hab⟩ := (eq_bot_or_exists_atom_le (b i)).resolve_left hi
    by classical exact ⟨Function.update ⊥ i a, isAtom_single ha, update_le_iff.2 ⟨hab, by simp⟩⟩
/-
**Pi.isCoatomic** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：isCoatomic [forall i, PartialOrder (π i)] [forall i, OrderTop (π i)] [fora
ll i, IsCoatomic (π i)] : IsCoatomic (forall i, π i)
参数：π i；π i；π i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isAtomic_dual_iff_isCoatomic`：isAtomic_dual_iff_isCoatomic [OrderTop α] 
: IsAtomic αᵒᵈ ↔ IsCoatomic α
· 使用定理 `OrderDual.instIsAtomic`：∀ {α : Type u_2} [inst : PartialOrder α] [inst_1
 : OrderTop α] [IsCoatomic α], IsAtomic αᵒᵈ
-/
instance isCoatomic [∀ i, PartialOrder (π i)] [∀ i, OrderTop (π i)] [∀ i, IsCoatomic (π i)] :
    IsCoatomic (∀ i, π i) :=
  isAtomic_dual_iff_isCoatomic.1 <|
    show IsAtomic (∀ i, (π i)ᵒᵈ) from inferInstance
/-
**Pi.isAtomistic** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：isAtomistic [forall i, PartialOrder (π i)] [forall i, OrderBot (π i)] [for
all i, IsAtomistic (π i)] : IsAtomistic (forall i, π i) where isLUB_atoms s
参数：π i；π i；π i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isLUB_pi`：isLUB_pi {s : Set (forall a, π a)} {f : forall a, π a} : IsLUB
 s f ↔ forall a, IsLUB (Function.eval a '' s) (f a)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `isLUB_atoms_le`：isLUB_atoms_le (b : α) : IsLUB { a : α | IsAtom a ∧ a <=
 b } b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
-/
instance isAtomistic [∀ i, PartialOrder (π i)] [∀ i, OrderBot (π i)] [∀ i, IsAtomistic (π i)] :
    IsAtomistic (∀ i, π i) where
  isLUB_atoms s := by
    classical
    refine ⟨{f | IsAtom f ∧ f ≤ s}, ?_, by simp +contextual⟩
    rw [isLUB_pi]
    intro i
    simp_rw [isAtom_iff_eq_single]
    refine ⟨?_, ?_⟩
    · rintro _ ⟨_, ⟨⟨_, _, _, rfl⟩, hs⟩, rfl⟩
      exact hs i
    · refine fun j hj ↦ (isLUB_atoms_le (s i)).2 fun x ⟨hx₁, hx₂⟩ ↦ ?_
      exact hj ⟨Function.update ⊥ i x, ⟨⟨_, x, hx₁, rfl⟩, by simp [update_le_iff, hx₂]⟩, by simp⟩
/-
**Pi.isCoatomistic** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：isCoatomistic [forall i, CompleteLattice (π i)] [forall i, IsCoatomistic (
π i)] : IsCoatomistic (forall i, π i)
参数：π i；π i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isAtomistic_dual_iff_isCoatomistic`：isAtomistic_dual_iff_isCoatomistic [
OrderTop α] : IsAtomistic αᵒᵈ ↔ IsCoatomistic α
· 使用定理 `OrderDual.instIsAtomistic`：∀ {α : Type u_2} [inst : PartialOrder α] [ins
t_1 : OrderTop α] [h : IsCoatomistic α], IsAtomistic αᵒᵈ
-/
instance isCoatomistic [∀ i, CompleteLattice (π i)] [∀ i, IsCoatomistic (π i)] :
    IsCoatomistic (∀ i, π i) :=
  isAtomistic_dual_iff_isCoatomistic.1 <|
    show IsAtomistic (∀ i, (π i)ᵒᵈ) from inferInstance

end Pi

section BooleanAlgebra
variable [BooleanAlgebra α] {a b : α}

/-
**isAtom_compl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} [inst : BooleanAlgebra α] {a : α}, IsAtom aᶜ ↔ IsCoatom a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.isAtom_iff_isCoatom`：isAtom_iff_isCoatom : IsAtom a ↔ IsCoatom b
· 使用定理 `DistribLattice.instIsModularLattice`：∀ {α : Type u_1} [inst : DistribLat
tice α], IsModularLattice α
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
· 使用定理 `isCompl_compl`：isCompl_compl : IsCompl x xᶜ
-/
@[simp] lemma isAtom_compl : IsAtom aᶜ ↔ IsCoatom a := isCompl_compl.symm.isAtom_iff_isCoatom
/-
**isCoatom_compl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} [inst : BooleanAlgebra α] {a : α}, IsCoatom aᶜ ↔ IsAtom a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.isCoatom_iff_isAtom`：isCoatom_iff_isAtom : IsCoatom a ↔ IsAtom b
· 使用定理 `DistribLattice.instIsModularLattice`：∀ {α : Type u_1} [inst : DistribLat
tice α], IsModularLattice α
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
· 使用定理 `isCompl_compl`：isCompl_compl : IsCompl x xᶜ
-/
@[simp] lemma isCoatom_compl : IsCoatom aᶜ ↔ IsAtom a := isCompl_compl.symm.isCoatom_iff_isAtom

protected alias ⟨IsAtom.of_compl, IsCoatom.compl⟩ := isAtom_compl
protected alias ⟨IsCoatom.of_compl, IsAtom.compl⟩ := isCoatom_compl

end BooleanAlgebra

namespace Set

/-
**Set.isAtom_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：isAtom_singleton (x : α) : IsAtom ({x} : Set α)
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.singleton_ne_empty`：singleton_ne_empty (a : α) : ({a} : Set α) != ∅
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.ssubset_singleton_iff`：ssubset_singleton_iff {s : Set α} {x : α} : s
 ⊂ {x} ↔ s = ∅
-/
theorem isAtom_singleton (x : α) : IsAtom ({x} : Set α) :=
  ⟨singleton_ne_empty _, fun _ hs => ssubset_singleton_iff.mp hs⟩
/-
**Set.isAtom_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：isAtom_iff {s : Set α} : IsAtom s ↔ exists x, s = {x}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isAtom_iff_le_of_ge`：isAtom_iff_le_of_ge : IsAtom a ↔ a != ⊥ ∧ forall b 
!= ⊥, b <= a -> a <= b
· 使用定理 `Set.bot_eq_empty`：bot_eq_empty : (⊥ : Set α) = ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.eq_singleton_iff_unique_mem`：eq_singleton_iff_unique_mem : s = {a} ↔
 a in s ∧ forall x in s, x = a
· 使用定理 `Set.singleton_ne_empty`：singleton_ne_empty (a : α) : ({a} : Set α) != ∅
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `Set.isAtom_singleton`：isAtom_singleton (x : α) : IsAtom ({x} : Set α)
-/
theorem isAtom_iff {s : Set α} : IsAtom s ↔ ∃ x, s = {x} := by
  refine
    ⟨?_, by
      rintro ⟨x, rfl⟩
      exact isAtom_singleton x⟩
  rw [isAtom_iff_le_of_ge, bot_eq_empty, ← nonempty_iff_ne_empty]
  rintro ⟨⟨x, hx⟩, hs⟩
  exact
    ⟨x, eq_singleton_iff_unique_mem.2
        ⟨hx, fun y hy => (hs {y} (singleton_ne_empty _) (singleton_subset_iff.2 hy) hx).symm⟩⟩
/-
**Set.isCoatom_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：isCoatom_iff (s : Set α) : IsCoatom s ↔ exists x, s = {x}ᶜ
参数：s : Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsCompl.isCoatom_iff_isAtom`：isCoatom_iff_isAtom : IsCoatom a ↔ IsAtom b
· 使用定理 `DistribLattice.instIsModularLattice`：∀ {α : Type u_1} [inst : DistribLat
tice α], IsModularLattice α
· 使用定理 `isCompl_compl`：isCompl_compl : IsCompl x xᶜ
· 使用定理 `Set.isAtom_iff`：isAtom_iff {s : Set α} : IsAtom s ↔ exists x, s = {x}
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isCoatom_iff (s : Set α) : IsCoatom s ↔ ∃ x, s = {x}ᶜ := by
  rw [isCompl_compl.isCoatom_iff_isAtom, isAtom_iff]
  simp_rw [@eq_comm _ s, compl_eq_comm]
/-
**Set.isCoatom_singleton_compl** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：isCoatom_singleton_compl (x : α) : IsCoatom ({x}ᶜ : Set α)
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.isCoatom_iff`：isCoatom_iff (s : Set α) : IsCoatom s ↔ exists x, s = 
{x}ᶜ
-/
theorem isCoatom_singleton_compl (x : α) : IsCoatom ({x}ᶜ : Set α) :=
  (isCoatom_iff {x}ᶜ).mpr ⟨x, rfl⟩
/-
**Set.** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsAtomistic (Set α) := inferInstance
/-
**Set.** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsCoatomistic (Set α) := inferInstance

end Set

