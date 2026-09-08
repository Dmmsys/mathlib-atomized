/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Fintype.Defs

/-!
# `Finset`s are a Boolean algebra

This file provides the `BooleanAlgebra (Finset α)` instance, under the assumption that `α` is a
`Fintype`.

## Main results

* `Finset.boundedOrder`: `Finset.univ` is the top element of `Finset α`
* `Finset.booleanAlgebra`: `Finset α` is a Boolean algebra if `α` is finite
-/

public section

assert_not_exists Monoid

open Function

open Nat

universe u v

variable {α β γ : Type*}

namespace Finset

variable {s t : Finset α}

section Fintypeα

variable [Fintype α]

/-
**Finset.Nonempty.eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nonempty`。
形式化陈述：∀ {α : Type u_1} {s : Finset α} [inst : Fintype α] [Subsingleton α], s.Non
empty → s = Finset.univ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_univ_of_forall`：eq_univ_of_forall : (forall x, x in s) -> s = 
univ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem Nonempty.eq_univ [Subsingleton α] : s.Nonempty → s = univ := by
  rintro ⟨x, hx⟩
  exact eq_univ_of_forall fun y => by rwa [Subsingleton.elim y x]
/-
**Finset.univ_nonempty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：univ_nonempty_iff : (univ : Finset α).Nonempty ↔ Nonempty α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_nonempty`：coe_nonempty {s : Finset α} : (s : Set α).Nonempty 
↔ s.Nonempty
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `Set.nonempty_iff_univ_nonempty`：nonempty_iff_univ_nonempty : Nonempty α 
↔ (univ : Set α).Nonempty
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem univ_nonempty_iff : (univ : Finset α).Nonempty ↔ Nonempty α := by
  rw [← coe_nonempty, coe_univ, Set.nonempty_iff_univ_nonempty]

@[simp, aesop unsafe apply (rule_sets := [finsetNonempty])]
/-
**Finset.univ_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：univ_nonempty [Nonempty α] : (univ : Finset α).Nonempty
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.univ_nonempty_iff`：univ_nonempty_iff : (univ : Finset α).Nonempty
 ↔ Nonempty α
-/
theorem univ_nonempty [Nonempty α] : (univ : Finset α).Nonempty :=
  univ_nonempty_iff.2 ‹_›
/-
**Finset.univ_eq_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：univ_eq_empty_iff : (univ : Finset α) = ∅ ↔ IsEmpty α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₁`：contrapose_iff₁ {p q : Prop} 
: (¬ p ↔ ¬ q) -> (p ↔ q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.univ_nonempty_iff`：univ_nonempty_iff : (univ : Finset α).Nonempty
 ↔ Nonempty α
-/
theorem univ_eq_empty_iff : (univ : Finset α) = ∅ ↔ IsEmpty α := by
  contrapose!; exact univ_nonempty_iff
/-
**Finset.univ_nontrivial_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：univ_nontrivial_iff : (Finset.univ : Finset α).Nontrivial ↔ Nontrivial α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.Nontrivial.eq_1`：∀ {α : Type u_1} (s : Finset α), s.Nontrivial = 
(↑s).Nontrivial
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `Set.nontrivial_univ_iff`：nontrivial_univ_iff : (univ : Set α).Nontrivial
 ↔ Nontrivial α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem univ_nontrivial_iff :
    (Finset.univ : Finset α).Nontrivial ↔ Nontrivial α := by
  rw [Finset.Nontrivial, Finset.coe_univ, Set.nontrivial_univ_iff]
/-
**Finset.univ_neq_empty** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：univ_neq_empty (α : Type*) [Fintype α] [Nonempty α] : (Finset.univ : Finse
t α) != ∅
参数：α : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.univ_eq_empty_iff`：univ_eq_empty_iff : (univ : Finset α) = ∅ ↔ Is
Empty α
-/
lemma univ_neq_empty (α : Type*) [Fintype α] [Nonempty α] :
    (Finset.univ : Finset α) ≠ ∅ :=
  fun h ↦ (Finset.univ_eq_empty_iff.1 h).elim (Classical.arbitrary _)
/-
**Finset.univ_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：univ_nontrivial [h : Nontrivial α] : (Finset.univ : Finset α).Nontrivial
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.univ_nontrivial_iff`：univ_nontrivial_iff : (Finset.univ : Finset 
α).Nontrivial ↔ Nontrivial α
-/
theorem univ_nontrivial [h : Nontrivial α] :
    (Finset.univ : Finset α).Nontrivial :=
  univ_nontrivial_iff.mpr h
/-
**Finset.singleton_ne_univ** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : Fintype α] [Nontrivial α] (a : α), {a} ≠ Finset.u
niv
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.coe_ne_coe`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p
 q : A}, ↑p ≠ ↑q ↔ p ≠ q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
@[simp] lemma singleton_ne_univ [Nontrivial α] (a : α) : {a} ≠ univ := by
  apply SetLike.coe_ne_coe.1
  simp

@[simp]
/-
**Finset.univ_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：univ_eq_empty [IsEmpty α] : (univ : Finset α) = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.univ_eq_empty_iff`：univ_eq_empty_iff : (univ : Finset α) = ∅ ↔ Is
Empty α
-/
theorem univ_eq_empty [IsEmpty α] : (univ : Finset α) = ∅ :=
  univ_eq_empty_iff.2 ‹_›

@[simp]
/-
**Finset.univ_unique** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：univ_unique [Unique α] : (univ : Finset α) = {default}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `iff_of_true`：∀ {a b : Prop}, a → b → (a ↔ b)
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Finset α) ↔ 
b = a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem univ_unique [Unique α] : (univ : Finset α) = {default} :=
  Finset.ext fun x => iff_of_true (mem_univ _) <| mem_singleton.2 <| Subsingleton.elim x default
/-
**Finset.boundedOrder** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
形式化陈述：boundedOrder : BoundedOrder (Finset α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.subset_univ`：subset_univ (s : Finset α) : s subseteq univ
-/
instance boundedOrder : BoundedOrder (Finset α) :=
  { (inferInstance : OrderBot (Finset α)) with
    top := univ
    le_top := subset_univ }

@[simp]
/-
**Finset.top_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：top_eq_univ : (⊤ : Finset α) = univ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem top_eq_univ : (⊤ : Finset α) = univ :=
  rfl
/-
**Finset.ssubset_univ_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：ssubset_univ_iff {s : Finset α} : s ⊂ univ ↔ s != univ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
-/
theorem ssubset_univ_iff {s : Finset α} : s ⊂ univ ↔ s ≠ univ :=
  lt_top_iff_ne_top

@[simp]
/-
**Finset.univ_subset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：univ_subset_iff {s : Finset α} : univ subseteq s ↔ s = univ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
-/
theorem univ_subset_iff {s : Finset α} : univ ⊆ s ↔ s = univ :=
  top_le_iff
/-
**Finset.codisjoint_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：codisjoint_left : Codisjoint s t ↔ forall ⦃a⦄, a ∉ s -> a in t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem codisjoint_left : Codisjoint s t ↔ ∀ ⦃a⦄, a ∉ s → a ∈ t := by
  classical simp [codisjoint_iff, eq_univ_iff_forall, or_iff_not_imp_left]
/-
**Finset.codisjoint_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：codisjoint_right : Codisjoint s t ↔ forall ⦃a⦄, a ∉ t -> a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `codisjoint_comm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Orde
rTop α] {a b : α}, Codisjoint a b ↔ Codisjoint b a
· 使用定理 `Finset.codisjoint_left`：codisjoint_left : Codisjoint s t ↔ forall ⦃a⦄, a
 ∉ s -> a in t
-/
theorem codisjoint_right : Codisjoint s t ↔ ∀ ⦃a⦄, a ∉ t → a ∈ s :=
  codisjoint_comm.trans codisjoint_left
/-
**Finset.booleanAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
形式化陈述：booleanAlgebra [DecidableEq α] : BooleanAlgebra (Finset α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance booleanAlgebra [DecidableEq α] : BooleanAlgebra (Finset α) :=
  GeneralizedBooleanAlgebra.toBooleanAlgebra

section BooleanAlgebra
variable [DecidableEq α] {a : α}

open symmDiff

/-
**Finset.sdiff_eq_inter_compl** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sdiff_eq_inter_compl (s t : Finset α) : s \ t = s inter tᶜ
参数：s t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiff_eq`：sdiff_eq : x \ y = x ⊓ yᶜ
-/
theorem sdiff_eq_inter_compl (s t : Finset α) : s \ t = s ∩ tᶜ :=
  sdiff_eq
/-
**Finset.compl_eq_univ_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：compl_eq_univ_sdiff (s : Finset α) : sᶜ = univ \ s
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compl_eq_univ_sdiff (s : Finset α) : sᶜ = univ \ s :=
  rfl

@[simp]
/-
**Finset.mem_compl** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_compl : a in sᶜ ↔ a ∉ s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_compl : a ∈ sᶜ ↔ a ∉ s := by simp [compl_eq_univ_sdiff]
/-
**Finset.notMem_compl** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：notMem_compl : a ∉ sᶜ ↔ a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_compl`：mem_compl : a in sᶜ ↔ a ∉ s
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem notMem_compl : a ∉ sᶜ ↔ a ∈ s := by rw [mem_compl, not_not]
/-
**Finset.mem_himp_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {s t : Finset α} [inst : Fintype α] [inst_1 : DecidableEq
 α] {a : α}, a ∈ s ⇨ t ↔ a ∈ s → a ∈ t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `himp_eq`：himp_eq : x ⇨ y = y ⊔ xᶜ
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem mem_himp_iff : a ∈ s ⇨ t ↔ a ∈ s → a ∈ t := by simp [himp_eq, imp_iff_or_not]
/-
**Finset.himp_def** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {s t : Finset α} [inst : Fintype α] [inst_1 : DecidableEq
 α], s ⇨ t = t ∪ sᶜ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `himp_eq`：himp_eq : x ⇨ y = y ⊔ xᶜ
-/
protected theorem himp_def : s ⇨ t = t ∪ sᶜ := himp_eq ..
/-
**Finset.mem_bihimp_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {s t : Finset α} [inst : Fintype α] [inst_1 : DecidableEq
 α] {a : α}, a ∈ bihimp s t ↔ (a ∈ s ↔ a ∈ t)
参数：a ∈ s ↔ a ∈ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem mem_bihimp_iff : a ∈ s ⇔ t ↔ (a ∈ s ↔ a ∈ t) := by simp [bihimp, iff_def']
/-
**Finset.bihimp_def** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {s t : Finset α} [inst : Fintype α] [inst_1 : DecidableEq
 α], bihimp s t = (s ∪ tᶜ) ∩ (t ∪ sᶜ)
参数：s ∪ tᶜ；t ∪ sᶜ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bihimp_eq`：bihimp_eq : a ⇔ b = (a ⊔ bᶜ) ⊓ (b ⊔ aᶜ)
-/
protected theorem bihimp_def : s ⇔ t = (s ∪ tᶜ) ∩ (t ∪ sᶜ) := bihimp_eq ..

@[simp, norm_cast]
/-
**Finset.coe_compl** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_compl (s : Finset α) : ↑sᶜ = (↑s : Set α)ᶜ
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Finset.mem_compl`：mem_compl : a in sᶜ ↔ a ∉ s
-/
theorem coe_compl (s : Finset α) : ↑sᶜ = (↑s : Set α)ᶜ :=
  Set.ext fun _ => mem_compl
/-
**Finset.compl_subset_compl** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：compl_subset_compl : sᶜ subseteq tᶜ ↔ t subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `compl_le_compl_iff_le`：compl_le_compl_iff_le : yᶜ <= xᶜ ↔ x <= y
-/
lemma compl_subset_compl : sᶜ ⊆ tᶜ ↔ t ⊆ s := compl_le_compl_iff_le
/-
**Finset.compl_ssubset_compl** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：compl_ssubset_compl : sᶜ ⊂ tᶜ ↔ t ⊂ s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `compl_lt_compl_iff_lt`：∀ {α : Type u} {x y : α} [inst : BooleanAlgebra α
], yᶜ < xᶜ ↔ x < y
-/
lemma compl_ssubset_compl : sᶜ ⊂ tᶜ ↔ t ⊂ s := compl_lt_compl_iff_lt
/-
**Finset.subset_compl_comm** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：subset_compl_comm : s subseteq tᶜ ↔ t subseteq sᶜ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_compl_iff_le_compl`：∀ {α : Type u_2} [inst : HeytingAlgebra α] {a b :
 α}, a ≤ bᶜ ↔ b ≤ aᶜ
-/
lemma subset_compl_comm : s ⊆ tᶜ ↔ t ⊆ sᶜ := le_compl_iff_le_compl
/-
**Finset.subset_compl_iff_disjoint_right** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：subset_compl_iff_disjoint_right : s subseteq tᶜ ↔ Disjoint s t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_compl_iff_disjoint_right`：le_compl_iff_disjoint_right : a <= bᶜ ↔ Dis
joint a b
-/
lemma subset_compl_iff_disjoint_right : s ⊆ tᶜ ↔ Disjoint s t :=
  le_compl_iff_disjoint_right
/-
**Finset.subset_compl_iff_disjoint_left** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：subset_compl_iff_disjoint_left : s subseteq tᶜ ↔ Disjoint t s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_compl_iff_disjoint_left`：le_compl_iff_disjoint_left : a <= bᶜ ↔ Disjo
int b a
-/
lemma subset_compl_iff_disjoint_left : s ⊆ tᶜ ↔ Disjoint t s :=
  le_compl_iff_disjoint_left
/-
**Finset.subset_compl_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {s : Finset α} [inst : Fintype α] [inst_1 : DecidableEq α
] {a : α}, s ⊆ {a}ᶜ ↔ a ∉ s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.subset_compl_comm`：subset_compl_comm : s subseteq tᶜ ↔ t subseteq
 sᶜ
· 使用定理 `Finset.singleton_subset_iff`：singleton_subset_iff {s : Finset α} {a : α}
 : {a} subseteq s ↔ a in s
· 使用定理 `Finset.mem_compl`：mem_compl : a in sᶜ ↔ a ∉ s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma subset_compl_singleton : s ⊆ {a}ᶜ ↔ a ∉ s := by
  rw [subset_compl_comm, singleton_subset_iff, mem_compl]

@[simp]
/-
**Finset.compl_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：compl_empty : (∅ : Finset α)ᶜ = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `compl_bot`：compl_bot : (⊥ : α)ᶜ = ⊤
-/
theorem compl_empty : (∅ : Finset α)ᶜ = univ :=
  compl_bot

@[simp]
/-
**Finset.compl_univ** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：compl_univ : (univ : Finset α)ᶜ = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `compl_top`：compl_top : (⊤ : α)ᶜ = ⊥
-/
theorem compl_univ : (univ : Finset α)ᶜ = ∅ :=
  compl_top

@[simp]
/-
**Finset.compl_eq_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：compl_eq_empty_iff (s : Finset α) : sᶜ = ∅ ↔ s = univ
参数：s : Finset α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `compl_eq_bot`：compl_eq_bot : xᶜ = ⊥ ↔ x = ⊤
-/
theorem compl_eq_empty_iff (s : Finset α) : sᶜ = ∅ ↔ s = univ :=
  compl_eq_bot

@[simp]
/-
**Finset.compl_eq_univ_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：compl_eq_univ_iff (s : Finset α) : sᶜ = univ ↔ s = ∅
参数：s : Finset α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `compl_eq_top`：compl_eq_top : xᶜ = ⊤ ↔ x = ⊥
-/
theorem compl_eq_univ_iff (s : Finset α) : sᶜ = univ ↔ s = ∅ :=
  compl_eq_top

@[simp]
/-
**Finset.union_compl** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：union_compl (s : Finset α) : s union sᶜ = univ
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_compl_eq_top`：sup_compl_eq_top : x ⊔ xᶜ = ⊤
-/
theorem union_compl (s : Finset α) : s ∪ sᶜ = univ :=
  sup_compl_eq_top

@[simp]
/-
**Finset.inter_compl** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inter_compl (s : Finset α) : s inter sᶜ = ∅
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_compl_eq_bot`：inf_compl_eq_bot : a ⊓ aᶜ = ⊥
-/
theorem inter_compl (s : Finset α) : s ∩ sᶜ = ∅ :=
  inf_compl_eq_bot

@[simp]
/-
**Finset.compl_union** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：compl_union (s t : Finset α) : (s union t)ᶜ = sᶜ inter tᶜ
参数：s t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `compl_sup`：compl_sup : (a ⊔ b)ᶜ = aᶜ ⊓ bᶜ
-/
theorem compl_union (s t : Finset α) : (s ∪ t)ᶜ = sᶜ ∩ tᶜ :=
  compl_sup

@[simp]
/-
**Finset.compl_inter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：compl_inter (s t : Finset α) : (s inter t)ᶜ = sᶜ union tᶜ
参数：s t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `compl_inf`：compl_inf : (x ⊓ y)ᶜ = xᶜ ⊔ yᶜ
-/
theorem compl_inter (s t : Finset α) : (s ∩ t)ᶜ = sᶜ ∪ tᶜ :=
  compl_inf

@[simp]
/-
**Finset.compl_erase** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：compl_erase : (s.erase a)ᶜ = insert a sᶜ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem compl_erase : (s.erase a)ᶜ = insert a sᶜ := by
  ext
  simp only [or_iff_not_imp_left, mem_insert, not_and, mem_compl, mem_erase]

@[simp]
/-
**Finset.compl_insert** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：compl_insert : (insert a s)ᶜ = sᶜ.erase a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem compl_insert : (insert a s)ᶜ = sᶜ.erase a := by
  ext
  simp only [not_or, mem_insert, mem_compl, mem_erase]
/-
**Finset.insert_compl_insert** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：insert_compl_insert (ha : a ∉ s) : insert a (insert a s)ᶜ = sᶜ
参数：ha : a ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.compl_insert`：compl_insert : (insert a s)ᶜ = sᶜ.erase a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.insert_erase`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset
 α} {a : α}, a ∈ s → insert a (s.erase a) = s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_compl`：mem_compl : a in sᶜ ↔ a ∉ s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem insert_compl_insert (ha : a ∉ s) : insert a (insert a s)ᶜ = sᶜ := by
  simp_rw [compl_insert, insert_erase (mem_compl.2 ha)]

@[simp]
/-
**Finset.insert_compl_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：insert_compl_self (x : α) : insert x ({x}ᶜ : Finset α) = univ
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.compl_erase`：compl_erase : (s.erase a)ᶜ = insert a sᶜ
· 使用定理 `Finset.erase_singleton`：erase_singleton (a : α) : ({a} : Finset α).erase
 a = ∅
· 使用定理 `Finset.compl_empty`：compl_empty : (∅ : Finset α)ᶜ = univ
-/
theorem insert_compl_self (x : α) : insert x ({x}ᶜ : Finset α) = univ := by
  rw [← compl_erase, erase_singleton, compl_empty]

@[simp]
/-
**Finset.compl_filter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：compl_filter (p : α -> Prop) [DecidablePred p] [forall x, Decidable ¬p x] 
: (univ.filter p)ᶜ = univ.filter fun x => ¬p x
参数：p : α -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem compl_filter (p : α → Prop) [DecidablePred p] [∀ x, Decidable ¬p x] :
    (univ.filter p)ᶜ = univ.filter fun x => ¬p x :=
  ext <| by simp
/-
**Finset.compl_ne_univ_iff_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：compl_ne_univ_iff_nonempty (s : Finset α) : sᶜ != univ ↔ s.Nonempty
参数：s : Finset α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem compl_ne_univ_iff_nonempty (s : Finset α) : sᶜ ≠ univ ↔ s.Nonempty := by
  simp [eq_univ_iff_forall, Finset.Nonempty]
/-
**Finset.compl_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：compl_singleton (a : α) : ({a} : Finset α)ᶜ = univ.erase a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.compl_eq_univ_sdiff`：compl_eq_univ_sdiff (s : Finset α) : sᶜ = un
iv \ s
· 使用定理 `Finset.sdiff_singleton_eq_erase`：sdiff_singleton_eq_erase (a : α) (s : F
inset α) : s \ {a} = s.erase a
-/
theorem compl_singleton (a : α) : ({a} : Finset α)ᶜ = univ.erase a := by
  rw [compl_eq_univ_sdiff, sdiff_singleton_eq_erase]
/-
**Finset.insert_inj_on'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：insert_inj_on' (s : Finset α) : Set.InjOn (fun a => insert a s) (sᶜ : Fins
et α)
参数：s : Finset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_compl`：coe_compl (s : Finset α) : ↑sᶜ = (↑s : Set α)ᶜ
· 使用定理 `Finset.insert_inj_on`：insert_inj_on (s : Finset α) : Set.InjOn (fun a =>
 insert a s) sᶜ
-/
theorem insert_inj_on' (s : Finset α) : Set.InjOn (fun a => insert a s) (sᶜ : Finset α) := by
  rw [coe_compl]
  exact s.insert_inj_on
/-
**Finset.image_univ_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_univ_of_surjective [Fintype β] {f : β -> α} (hf : Surjective f) : un
iv.image f = univ
参数：hf : Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_univ_of_forall`：eq_univ_of_forall : (forall x, x in s) -> s = 
univ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Finset.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {a} (h : a in s) 
: f a in s.image f
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
-/
theorem image_univ_of_surjective [Fintype β] {f : β → α} (hf : Surjective f) :
    univ.image f = univ :=
  eq_univ_of_forall <| hf.forall.2 fun _ => mem_image_of_mem _ <| mem_univ _

@[simp]
/-
**Finset.image_univ_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_univ_equiv [Fintype β] (f : β ≃ α) : univ.image f = univ
参数：f : β ≃ α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image_univ_of_surjective`：image_univ_of_surjective [Fintype β] {f
 : β -> α} (hf : Surjective f) : univ.image f = univ
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
-/
theorem image_univ_equiv [Fintype β] (f : β ≃ α) : univ.image f = univ :=
  Finset.image_univ_of_surjective f.surjective
/-
**Finset.univ_inter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α] (s : Finset α
), Finset.univ ∩ s = s
参数：s : Finset α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma univ_inter (s : Finset α) : univ ∩ s = s := by ext a; simp
/-
**Finset.inter_univ** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α] (s : Finset α
), s ∩ Finset.univ = s
参数：s : Finset α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.inter_comm`：inter_comm (s₁ s₂ : Finset α) : s₁ inter s₂ = s₂ inte
r s₁
· 使用定理 `Finset.univ_inter`：∀ {α : Type u_1} [inst : Fintype α] [inst_1 : Decidab
leEq α] (s : Finset α), Finset.univ ∩ s = s
-/
@[simp] lemma inter_univ (s : Finset α) : s ∩ univ = s := by rw [inter_comm, univ_inter]
/-
**Finset.inter_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {s t : Finset α} [inst : Fintype α] [inst_1 : DecidableEq
 α],   s ∩ t = Finset.univ ↔ s = Finset.univ ∧ t = Finset.univ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_eq_top_iff`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : Ord
erTop α] {a b : α}, a ⊓ b = ⊤ ↔ a = ⊤ ∧ b = ⊤
-/
@[simp] lemma inter_eq_univ : s ∩ t = univ ↔ s = univ ∧ t = univ := inf_eq_top_iff

end BooleanAlgebra

-- @[simp] --Note this would loop with `Finset.univ_unique`
/-
**Finset.singleton_eq_univ** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：singleton_eq_univ [Subsingleton α] (a : α) : ({a} : Finset α) = univ
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma singleton_eq_univ [Subsingleton α] (a : α) : ({a} : Finset α) = univ := by
  ext b; simp [Subsingleton.elim a b]
/-
**Finset.map_univ_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：map_univ_of_surjective [Fintype β] {f : β ↪ α} (hf : Surjective f) : univ.
map f = univ
参数：hf : Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_univ_of_forall`：eq_univ_of_forall : (forall x, x in s) -> s = 
univ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Finset.mem_map_of_mem`：mem_map_of_mem (f : α ↪ β) {a} {s : Finset α} : a
 in s -> f a in s.map f
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
-/
theorem map_univ_of_surjective [Fintype β] {f : β ↪ α} (hf : Surjective f) : univ.map f = univ :=
  eq_univ_of_forall <| hf.forall.2 fun _ => mem_map_of_mem _ <| mem_univ _

@[simp]
/-
**Finset.map_univ_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：map_univ_equiv [Fintype β] (f : β ≃ α) : univ.map f.toEmbedding = univ
参数：f : β ≃ α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.map_univ_of_surjective`：map_univ_of_surjective [Fintype β] {f : β
 ↪ α} (hf : Surjective f) : univ.map f = univ
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
-/
theorem map_univ_equiv [Fintype β] (f : β ≃ α) : univ.map f.toEmbedding = univ :=
  map_univ_of_surjective f.surjective
/-
**Finset.univ_map_equiv_to_embedding** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：univ_map_equiv_to_embedding {α β : Type*} [Fintype α] [Fintype β] (e : α ≃
 β) : univ.map e.toEmbedding = univ
参数：e : α ≃ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.eq_univ_iff_forall`：eq_univ_iff_forall : s = univ ↔ forall x, x i
n s
· 使用定理 `Finset.mem_map`：mem_map {b : β} : b in s.map f ↔ exists a in s, f a = b
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem univ_map_equiv_to_embedding {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β) :
    univ.map e.toEmbedding = univ :=
  eq_univ_iff_forall.mpr fun b => mem_map.mpr ⟨e.symm b, mem_univ _, by simp⟩

@[simp]
/-
**Finset.univ_filter_exists** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：univ_filter_exists (f : α -> β) [Fintype β] [DecidablePred fun y => exists
 x, f x = y] [DecidableEq β] : (Finset.univ.filter fun y => exists x, f x = y) =
 Finset.univ.image f
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem univ_filter_exists (f : α → β) [Fintype β] [DecidablePred fun y => ∃ x, f x = y]
    [DecidableEq β] : (Finset.univ.filter fun y => ∃ x, f x = y) = Finset.univ.image f := by
  ext
  simp

/-- Note this is a special case of `(Finset.image_preimage f univ _).symm`. -/
/-
**Finset.univ_filter_mem_range** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：univ_filter_mem_range (f : α -> β) [Fintype β] [DecidablePred fun y => y i
n Set.range f] [DecidableEq β] : (Finset.univ.filter fun y => y in Set.range f) 
= Finset.univ.image f
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Note this is a special case of `(Finset.image_preimage f univ _).symm`.
-/
theorem univ_filter_mem_range (f : α → β) [Fintype β] [DecidablePred fun y => y ∈ Set.range f]
    [DecidableEq β] : (Finset.univ.filter fun y => y ∈ Set.range f) = Finset.univ.image f := by
  grind
/-
**Finset.coe_filter_univ** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_filter_univ (p : α -> Prop) [DecidablePred p] : (univ.filter p : Set α
) = { x | p x }
参数：p : α -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_filter`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePred
 p] (s : Finset α), ↑(Finset.filter p s) = {x | x ∈ s ∧ p x}
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_filter_univ (p : α → Prop) [DecidablePred p] :
    (univ.filter p : Set α) = { x | p x } := by simp

end Fintypeα

/-
**Finset.subtype_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {s : Finset α} {p : α → Prop} [inst : DecidablePred p] [i
nst_1 : Fintype { a // p a }],   Finset.subtype p s = Finset.univ ↔ ∀ ⦃a : α⦄, p
 a → a ∈ s
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma subtype_eq_univ {p : α → Prop} [DecidablePred p] [Fintype {a // p a}] :
    s.subtype p = univ ↔ ∀ ⦃a⦄, p a → a ∈ s := by simp [Finset.ext_iff]
/-
**Finset.subtype_univ** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : Fintype α] (p : α → Prop) [inst_1 : DecidablePred
 p] [inst_2 : Fintype { a // p a }],   Finset.subtype p Finset.univ = Finset.uni
v
参数：p : α → Prop。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] lemma subtype_univ [Fintype α] (p : α → Prop) [DecidablePred p] [Fintype {a // p a}] :
    univ.subtype p = univ := by simp
/-
**Finset.univ_map_subtype** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：univ_map_subtype [Fintype α] (p : α -> Prop) [DecidablePred p] [Fintype {a
 // p a}] : univ.map (Function.Embedding.subtype p) = univ.filter p
参数：p : α -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.subtype_map`：subtype_map (p : α -> Prop) [DecidablePred p] {s : F
inset α} : (s.subtype p).map (Embedding.subtype _) = s.filter p
· 使用定理 `Finset.subtype_univ`：∀ {α : Type u_1} [inst : Fintype α] (p : α → Prop) 
[inst_1 : DecidablePred p] [inst_2 : Fintype { a // p a }],   Finset.subtype p F
inset.uni…
-/
lemma univ_map_subtype [Fintype α] (p : α → Prop) [DecidablePred p] [Fintype {a // p a}] :
    univ.map (Function.Embedding.subtype p) = univ.filter p := by
  rw [← subtype_map, subtype_univ]
/-
**Finset.univ_val_map_subtype_val** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：univ_val_map_subtype_val [Fintype α] (p : α -> Prop) [DecidablePred p] [Fi
ntype {a // p a}] : univ.val.map ((↑) : { a // p a } -> α) = (univ.filter p).val
参数：p : α -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.map_val`：map_val (f : α ↪ β) (s : Finset α) : (map f s).1 = s.1.m
ap f
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `Finset.univ_map_subtype`：univ_map_subtype [Fintype α] (p : α -> Prop) [D
ecidablePred p] [Fintype {a // p a}] : univ.map (Function.Embedding.subtype p) =
 univ.filter …
-/
lemma univ_val_map_subtype_val [Fintype α] (p : α → Prop) [DecidablePred p] [Fintype {a // p a}] :
    univ.val.map ((↑) : { a // p a } → α) = (univ.filter p).val := by
  apply (map_val (Function.Embedding.subtype p) univ).symm.trans
  apply congr_arg
  apply univ_map_subtype
/-
**Finset.univ_val_map_subtype_restrict** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：univ_val_map_subtype_restrict [Fintype α] (f : α -> β) (p : α -> Prop) [De
cidablePred p] [Fintype {a // p a}] : univ.val.map (Subtype.restrict p f) = (uni
v.filter p).val.map f
参数：f : α -> β；p : α -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.univ_val_map_subtype_val`：univ_val_map_subtype_val [Fintype α] (p
 : α -> Prop) [DecidablePred p] [Fintype {a // p a}] : univ.val.map ((↑) : { a /
/ p a } -> α) = (univ…
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Subtype.restrict_def`：restrict_def {α β} (f : α -> β) (p : α -> Prop) : 
restrict p f = f ∘ (fun (a : Subtype p) => a)
-/
lemma univ_val_map_subtype_restrict [Fintype α] (f : α → β)
    (p : α → Prop) [DecidablePred p] [Fintype {a // p a}] :
    univ.val.map (Subtype.restrict p f) = (univ.filter p).val.map f := by
  rw [← univ_val_map_subtype_val, Multiset.map_map, Subtype.restrict_def]

section DecEq

variable [Fintype α] [DecidableEq α]

/-
**Finset.filter_univ_mem** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：filter_univ_mem (s : Finset α) : univ.filter (· in s) = s
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.filter_mem_eq_of_subset`：∀ {α : Type u_1} {s t : Finset α} [inst 
: DecidablePred fun x => x ∈ s], s ⊆ t → {x ∈ t | x ∈ s} = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma filter_univ_mem (s : Finset α) : univ.filter (· ∈ s) = s := by simp
/-
**Finset.decidableCodisjoint** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
形式化陈述：decidableCodisjoint : Decidable (Codisjoint s t)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableCodisjoint : Decidable (Codisjoint s t) :=
  decidable_of_iff _ codisjoint_left.symm
/-
**Finset.decidableIsCompl** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
形式化陈述：decidableIsCompl : Decidable (IsCompl s t)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableIsCompl : Decidable (IsCompl s t) :=
  decidable_of_iff' _ isCompl_iff

end DecEq

end Finset

