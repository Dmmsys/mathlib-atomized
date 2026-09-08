/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
module

public import Mathlib.Data.Set.Insert
public import Mathlib.Tactic.ByContra

/-!
# Subsingleton

Defines the predicate `Subsingleton s : Prop`, saying that `s` has at most one element.

Also defines `Nontrivial s : Prop` : the predicate saying that `s` has at least two distinct
elements.

-/

@[expose] public section

assert_not_exists HeytingAlgebra RelIso

open Function

universe u v

namespace Set

/-! ### Subsingleton -/

section Subsingleton

variable {α : Type u} {a : α} {s t : Set α}

/-- A set `s` is a `Subsingleton` if it has at most one element. -/
/-
**Set.Subsingleton** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：{α : Type u} → Set α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set `s` is a `Subsingleton` if it has at most one element.
-/
protected def Subsingleton (s : Set α) : Prop :=
  ∀ ⦃x⦄ (_ : x ∈ s) ⦃y⦄ (_ : y ∈ s), x = y
/-
**Set.Subsingleton.anti** 是 Mathlib 中的一个定理，位于命名空间 `Set.Subsingleton`。
形式化陈述：∀ {α : Type u} {s t : Set α}, t.Subsingleton → s ⊆ t → s.Subsingleton
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Subsingleton.anti (ht : t.Subsingleton) (hst : s ⊆ t) : s.Subsingleton := fun _ hx _ hy =>
  ht (hst hx) (hst hy)
/-
**Set.Subsingleton.eq_singleton_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set.Subsinglet
on`。
形式化陈述：∀ {α : Type u} {s : Set α}, s.Subsingleton → ∀ {x : α}, x ∈ s → s = {x}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.eq_of_mem_singleton`：eq_of_mem_singleton {x y : α} (h : x in ({y} : 
Set α)) : x = y
-/
theorem Subsingleton.eq_singleton_of_mem (hs : s.Subsingleton) {x : α} (hx : x ∈ s) : s = {x} :=
  ext fun _ => ⟨fun hy => hs hx hy ▸ mem_singleton _, fun hy => (eq_of_mem_singleton hy).symm ▸ hx⟩

@[simp]
/-
**Set.subsingleton_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subsingleton_empty : (∅ : Set α).Subsingleton
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subsingleton_empty : (∅ : Set α).Subsingleton := fun _ => False.elim

@[simp]
/-
**Set.subsingleton_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subsingleton_singleton {a} : ({a} : Set α).Subsingleton
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.eq_of_mem_singleton`：eq_of_mem_singleton {x y : α} (h : x in ({y} : 
Set α)) : x = y
-/
theorem subsingleton_singleton {a} : ({a} : Set α).Subsingleton := fun _ hx _ hy =>
  (eq_of_mem_singleton hx).symm ▸ (eq_of_mem_singleton hy).symm ▸ rfl
/-
**Set.subsingleton_of_subset_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subsingleton_of_subset_singleton (h : s subseteq {a}) : s.Subsingleton
参数：h : s subseteq {a}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.anti`：∀ {α : Type u} {s t : Set α}, t.Subsingleton → s 
⊆ t → s.Subsingleton
· 使用定理 `Set.subsingleton_singleton`：subsingleton_singleton {a} : ({a} : Set α).S
ubsingleton
-/
theorem subsingleton_of_subset_singleton (h : s ⊆ {a}) : s.Subsingleton :=
  subsingleton_singleton.anti h
/-
**Set.subsingleton_of_forall_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subsingleton_of_forall_eq (a : α) (h : forall b in s, b = a) : s.Subsingle
ton
参数：a : α；h : forall b in s, b = a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem subsingleton_of_forall_eq (a : α) (h : ∀ b ∈ s, b = a) : s.Subsingleton := fun _ hb _ hc =>
  (h _ hb).trans (h _ hc).symm
/-
**Set.subsingleton_iff_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subsingleton_iff_singleton {x} (hx : x in s) : s.Subsingleton ↔ s = {x}
参数：hx : x in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.eq_singleton_of_mem`：∀ {α : Type u} {s : Set α}, s.Subs
ingleton → ∀ {x : α}, x ∈ s → s = {x}
· 使用定理 `Set.subsingleton_singleton`：subsingleton_singleton {a} : ({a} : Set α).S
ubsingleton
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem subsingleton_iff_singleton {x} (hx : x ∈ s) : s.Subsingleton ↔ s = {x} :=
  ⟨fun h => h.eq_singleton_of_mem hx, fun h => h.symm ▸ subsingleton_singleton⟩
/-
**Set.Subsingleton.eq_empty_or_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set.Subsingl
eton`。
形式化陈述：∀ {α : Type u} {s : Set α}, s.Subsingleton → s = ∅ ∨ ∃ x, s = {x}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `Set.Subsingleton.eq_singleton_of_mem`：∀ {α : Type u} {s : Set α}, s.Subs
ingleton → ∀ {x : α}, x ∈ s → s = {x}
-/
theorem Subsingleton.eq_empty_or_singleton (hs : s.Subsingleton) : s = ∅ ∨ ∃ x, s = {x} :=
  s.eq_empty_or_nonempty.elim Or.inl fun ⟨x, hx⟩ => Or.inr ⟨x, hs.eq_singleton_of_mem hx⟩
/-
**Set.subsingleton_iff_eq_empty_or_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subsingleton_iff_eq_empty_or_singleton : s.Subsingleton ↔ s = ∅ ∨ exists x
, s = {x}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.eq_empty_or_singleton`：∀ {α : Type u} {s : Set α}, s.Su
bsingleton → s = ∅ ∨ ∃ x, s = {x}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem subsingleton_iff_eq_empty_or_singleton : s.Subsingleton ↔ s = ∅ ∨ ∃ x, s = {x} :=
  ⟨Subsingleton.eq_empty_or_singleton, by rintro (_ | ⟨_, rfl⟩) <;> simp_all⟩
/-
**Set.Subsingleton.induction_on** 是 Mathlib 中的一个定理，位于命名空间 `Set.Subsingleton`。
形式化陈述：∀ {α : Type u} {s : Set α} {p : Set α → Prop}, s.Subsingleton → p ∅ → (∀ (
x : α), p {x}) → p s
参数：∀ (x : α), p {x}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.eq_empty_or_singleton`：∀ {α : Type u} {s : Set α}, s.Su
bsingleton → s = ∅ ∨ ∃ x, s = {x}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Subsingleton.induction_on {p : Set α → Prop} (hs : s.Subsingleton) (he : p ∅)
    (h₁ : ∀ x, p {x}) : p s := by
  rcases hs.eq_empty_or_singleton with (rfl | ⟨x, rfl⟩)
  exacts [he, h₁ _]
/-
**Set.subsingleton_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subsingleton_univ [Subsingleton α] : (univ : Set α).Subsingleton
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem subsingleton_univ [Subsingleton α] : (univ : Set α).Subsingleton := fun x _ y _ =>
  Subsingleton.elim x y
/-
**Set.subsingleton_of_univ_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subsingleton_of_univ_subsingleton (h : (univ : Set α).Subsingleton) : Subs
ingleton α
参数：h : (univ : Set α).Subsingleton。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem subsingleton_of_univ_subsingleton (h : (univ : Set α).Subsingleton) : Subsingleton α :=
  ⟨fun a b => h (mem_univ a) (mem_univ b)⟩

@[simp]
/-
**Set.subsingleton_univ_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subsingleton_univ_iff : (univ : Set α).Subsingleton ↔ Subsingleton α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subsingleton_of_univ_subsingleton`：subsingleton_of_univ_subsingleton
 (h : (univ : Set α).Subsingleton) : Subsingleton α
· 使用定理 `Set.subsingleton_univ`：subsingleton_univ [Subsingleton α] : (univ : Set 
α).Subsingleton
-/
theorem subsingleton_univ_iff : (univ : Set α).Subsingleton ↔ Subsingleton α :=
  ⟨subsingleton_of_univ_subsingleton, fun h => @subsingleton_univ _ h⟩
/-
**Set.Subsingleton.inter_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set.Subsingleton`。
形式化陈述：∀ {α : Type u} {a : α} {s : Set α}, (s ∩ {a}).Subsingleton
参数：s ∩ {a}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subsingleton_of_subset_singleton`：subsingleton_of_subset_singleton (
h : s subseteq {a}) : s.Subsingleton
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
lemma Subsingleton.inter_singleton : (s ∩ {a}).Subsingleton :=
  Set.subsingleton_of_subset_singleton Set.inter_subset_right
/-
**Set.Subsingleton.singleton_inter** 是 Mathlib 中的一个定理，位于命名空间 `Set.Subsingleton`。
形式化陈述：∀ {α : Type u} {a : α} {s : Set α}, ({a} ∩ s).Subsingleton
参数：{a} ∩ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subsingleton_of_subset_singleton`：subsingleton_of_subset_singleton (
h : s subseteq {a}) : s.Subsingleton
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
lemma Subsingleton.singleton_inter : ({a} ∩ s).Subsingleton :=
  Set.subsingleton_of_subset_singleton Set.inter_subset_left
/-
**Set.subsingleton_of_subsingleton_inter_left** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：subsingleton_of_subsingleton_inter_left (h : (s union t).Subsingleton) : s
.Subsingleton
参数：h : (s union t).Subsingleton。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma subsingleton_of_subsingleton_inter_left (h : (s ∪ t).Subsingleton) :
    s.Subsingleton :=
  fun _ h₁ _ h₂ ↦ h (.inl h₁) (.inl h₂)
/-
**Set.subsingleton_of_subsingleton_inter_right** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：subsingleton_of_subsingleton_inter_right (h : (s union t).Subsingleton) : 
t.Subsingleton
参数：h : (s union t).Subsingleton。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma subsingleton_of_subsingleton_inter_right (h : (s ∪ t).Subsingleton) :
    t.Subsingleton :=
  fun _ h₁ _ h₂ ↦ h (.inr h₁) (.inr h₂)
/-
**Set.subsingleton_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subsingleton_of_subsingleton [Subsingleton α] {s : Set α} : s.Subsingleton
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.anti`：∀ {α : Type u} {s t : Set α}, t.Subsingleton → s 
⊆ t → s.Subsingleton
· 使用定理 `Set.subsingleton_univ`：subsingleton_univ [Subsingleton α] : (univ : Set 
α).Subsingleton
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
theorem subsingleton_of_subsingleton [Subsingleton α] {s : Set α} : s.Subsingleton :=
  subsingleton_univ.anti (subset_univ s)

@[to_dual]
/-
**Set.subsingleton_isTop** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subsingleton_isTop (α : Type*) [PartialOrder α] : { x : α | IsTop x }.Subs
ingleton
参数：α : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMax.eq_of_le`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, IsMa
x a → a ≤ b → a = b
· 使用定理 `IsTop.isMax`：∀ {α : Type u_1} [inst : LE α] {a : α}, IsTop a → IsMax a
-/
theorem subsingleton_isTop (α : Type*) [PartialOrder α] : { x : α | IsTop x }.Subsingleton :=
  fun x hx _ hy => hx.isMax.eq_of_le (hy x)
/-
**Set.exists_eq_singleton_iff_nonempty_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `S
et`。
形式化陈述：exists_eq_singleton_iff_nonempty_subsingleton : (exists a : α, s = {a}) ↔ 
s.Nonempty ∧ s.Subsingleton
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.singleton_nonempty`：singleton_nonempty (a : α) : ({a} : Set α).Nonem
pty
· 使用定理 `Set.subsingleton_singleton`：subsingleton_singleton {a} : ({a} : Set α).S
ubsingleton
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Set.Subsingleton.eq_empty_or_singleton`：∀ {α : Type u} {s : Set α}, s.Su
bsingleton → s = ∅ ∨ ∃ x, s = {x}
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.Nonempty.ne_empty`：∀ {α : Type u} {s : Set α}, s.Nonempty → s ≠ ∅
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem exists_eq_singleton_iff_nonempty_subsingleton :
    (∃ a : α, s = {a}) ↔ s.Nonempty ∧ s.Subsingleton := by
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨a, rfl⟩
    exact ⟨singleton_nonempty a, subsingleton_singleton⟩
  · exact h.2.eq_empty_or_singleton.resolve_left h.1.ne_empty
/-
**Set.eq_empty_or_singleton_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：eq_empty_or_singleton_of_subsingleton [Subsingleton α] (s : Set α) : s = ∅
 ∨ exists a, s = {a}
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.eq_empty_or_singleton`：∀ {α : Type u} {s : Set α}, s.Su
bsingleton → s = ∅ ∨ ∃ x, s = {x}
· 使用定理 `Set.subsingleton_of_subsingleton`：subsingleton_of_subsingleton [Subsingl
eton α] {s : Set α} : s.Subsingleton
-/
theorem eq_empty_or_singleton_of_subsingleton [Subsingleton α] (s : Set α) :
    s = ∅ ∨ ∃ a, s = {a} :=
  subsingleton_of_subsingleton.eq_empty_or_singleton
/-
**Set.eq_empty_or_singleton_of_unique** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：eq_empty_or_singleton_of_unique [Unique α] (s : Set α) : s = ∅ ∨ s = {defa
ult}
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c
· 使用定理 `Unique.eq_default`：eq_default (a : α) : a = default
· 使用定理 `Set.eq_empty_or_singleton_of_subsingleton`：eq_empty_or_singleton_of_subs
ingleton [Subsingleton α] (s : Set α) : s = ∅ ∨ exists a, s = {a}
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem eq_empty_or_singleton_of_unique [Unique α] (s : Set α) :
    s = ∅ ∨ s = {default} :=
  s.eq_empty_or_singleton_of_subsingleton.imp_right fun ⟨a, ha⟩ => Unique.eq_default a ▸ ha

/-- `s`, coerced to a type, is a subsingleton type if and only if `s` is a subsingleton set. -/
@[simp, norm_cast]
/-
**Set.subsingleton_coe** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subsingleton_coe (s : Set α) : Subsingleton s ↔ s.Subsingleton
参数：s : Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SetCoe.ext_iff`：SetCoe.ext_iff {s : Set α} {a b : s} : (↑a : α) = ↑b ↔ a
 = b
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `SetCoe.ext`：SetCoe.ext {s : Set α} {a b : s} : (a : α) = b -> a = b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
`s`, coerced to a type, is a subsingleton type if and only if `s` is a subsingle
ton set.
-/
theorem subsingleton_coe (s : Set α) : Subsingleton s ↔ s.Subsingleton := by
  constructor
  · intro h a ha b hb
    exact SetCoe.ext_iff.2 (@Subsingleton.elim s h ⟨a, ha⟩ ⟨b, hb⟩)
  · exact fun h => Subsingleton.intro fun a b => SetCoe.ext (h a.property b.property)
/-
**Set.Subsingleton.coe_sort** 是 Mathlib 中的一个定理，位于命名空间 `Set.Subsingleton`。
形式化陈述：∀ {α : Type u} {s : Set α}, s.Subsingleton → Subsingleton ↑s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.subsingleton_coe`：subsingleton_coe (s : Set α) : Subsingleton s ↔ s.
Subsingleton
-/
theorem Subsingleton.coe_sort {s : Set α} : s.Subsingleton → Subsingleton s :=
  s.subsingleton_coe.2

/-- The `coe_sort` of a set `s` in a subsingleton type is a subsingleton.
For the corresponding result for `Subtype`, see `subtype.subsingleton`. -/
/-
**Set.subsingleton_coe_of_subsingleton** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：subsingleton_coe_of_subsingleton [Subsingleton α] {s : Set α} : Subsinglet
on s
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.subsingleton_coe`：subsingleton_coe (s : Set α) : Subsingleton s ↔ s.
Subsingleton
· 使用定理 `Set.subsingleton_of_subsingleton`：subsingleton_of_subsingleton [Subsingl
eton α] {s : Set α} : s.Subsingleton

--- 原说明 ---
The `coe_sort` of a set `s` in a subsingleton type is a subsingleton.
For the corresponding result for `Subtype`, see `subtype.subsingleton`.
-/
instance subsingleton_coe_of_subsingleton [Subsingleton α] {s : Set α} : Subsingleton s := by
  rw [s.subsingleton_coe]
  exact subsingleton_of_subsingleton
/-
**Set.Subsingleton.denselyOrdered** 是 Mathlib 中的一个定理，位于命名空间 `Set.Subsingleton`。
形式化陈述：∀ {α : Type u} {s : Set α} [inst : LT α], s.Subsingleton → DenselyOrdered 
↑s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.subsingleton_coe`：subsingleton_coe (s : Set α) : Subsingleton s ↔ s.
Subsingleton
· 使用定理 `LT.lt.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a < b → b = 
c → a < c
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
lemma Subsingleton.denselyOrdered {s : Set α} [LT α] (hs : s.Subsingleton) :
    DenselyOrdered s :=
  have := (subsingleton_coe _).mpr hs
  ⟨fun _ _ h ↦ ⟨_, h.trans_eq (Subsingleton.elim _ _), h⟩⟩
/-
**Set._root_.ExistsUnique.setSubsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.ExistsUnique.setSubsingleton {α : Type*} {p : α → Prop} (h : ExistsUnique p) :
    {x | p x}.Subsingleton :=
  fun _ hx _ hy => h.unique hx hy

end Subsingleton

/-! ### Nontrivial -/

section Nontrivial

variable {α : Type u} {a : α} {s t : Set α}

/-- A set `s` is `Set.Nontrivial` if it has at least two distinct elements. -/
/-
**Set.Nontrivial** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：{α : Type u} → Set α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set `s` is `Set.Nontrivial` if it has at least two distinct elements.
-/
protected def Nontrivial (s : Set α) : Prop :=
  ∃ x ∈ s, ∃ y ∈ s, x ≠ y
/-
**Set.nontrivial_of_mem_mem_ne** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：nontrivial_of_mem_mem_ne {x y} (hx : x in s) (hy : y in s) (hxy : x != y) 
: s.Nontrivial
参数：hx : x in s；hy : y in s；hxy : x != y。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nontrivial_of_mem_mem_ne {x y} (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y) : s.Nontrivial :=
  ⟨x, hx, y, hy, hxy⟩

/-- Extract witnesses from s.nontrivial. This function might be used instead of case analysis on the
argument. Note that it makes a proof depend on the classical.choice axiom. -/
/-
**Set.Nontrivial.choose** 是 Mathlib 中的一个定义，位于命名空间 `Set.Nontrivial`。
形式化陈述：{α : Type u} → {s : Set α} → s.Nontrivial → α × α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extract witnesses from s.nontrivial. This function might be used instead of case
 analysis on the
argument. Note that it makes a proof depend on the classical.choice axiom.
-/
protected noncomputable def Nontrivial.choose (hs : s.Nontrivial) : α × α :=
  (Exists.choose hs, hs.choose_spec.right.choose)
/-
**Set.Nontrivial.choose_fst_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nontrivial`。
形式化陈述：∀ {α : Type u} {s : Set α} (hs : s.Nontrivial), hs.choose.1 ∈ s
参数：hs : s.Nontrivial。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
protected theorem Nontrivial.choose_fst_mem (hs : s.Nontrivial) : hs.choose.fst ∈ s :=
  hs.choose_spec.left
/-
**Set.Nontrivial.choose_snd_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nontrivial`。
形式化陈述：∀ {α : Type u} {s : Set α} (hs : s.Nontrivial), hs.choose.2 ∈ s
参数：hs : s.Nontrivial。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
protected theorem Nontrivial.choose_snd_mem (hs : s.Nontrivial) : hs.choose.snd ∈ s :=
  hs.choose_spec.right.choose_spec.left
/-
**Set.Nontrivial.choose_fst_ne_choose_snd** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nontriv
ial`。
形式化陈述：∀ {α : Type u} {s : Set α} (hs : s.Nontrivial), hs.choose.1 ≠ hs.choose.2
参数：hs : s.Nontrivial。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
protected theorem Nontrivial.choose_fst_ne_choose_snd (hs : s.Nontrivial) :
    hs.choose.fst ≠ hs.choose.snd :=
  hs.choose_spec.right.choose_spec.right
/-
**Set.Nontrivial.mono** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nontrivial`。
形式化陈述：∀ {α : Type u} {s t : Set α}, s.Nontrivial → s ⊆ t → t.Nontrivial
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Nontrivial.mono (hs : s.Nontrivial) (hst : s ⊆ t) : t.Nontrivial :=
  let ⟨x, hx, y, hy, hxy⟩ := hs
  ⟨x, hst hx, y, hst hy, hxy⟩
/-
**Set.nontrivial_pair** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：nontrivial_pair {x y} (hxy : x != y) : ({x, y} : Set α).Nontrivial
参数：hxy : x != y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
· 使用定理 `Set.mem_insert_of_mem`：mem_insert_of_mem {x : α} {s : Set α} (y : α) : x
 in s -> x in insert y s
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
-/
theorem nontrivial_pair {x y} (hxy : x ≠ y) : ({x, y} : Set α).Nontrivial :=
  ⟨x, mem_insert _ _, y, mem_insert_of_mem _ (mem_singleton _), hxy⟩
/-
**Set.nontrivial_of_pair_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：nontrivial_of_pair_subset {x y} (hxy : x != y) (h : {x, y} subseteq s) : s
.Nontrivial
参数：hxy : x != y；h : {x, y} subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nontrivial.mono`：∀ {α : Type u} {s t : Set α}, s.Nontrivial → s ⊆ t 
→ t.Nontrivial
· 使用定理 `Set.nontrivial_pair`：nontrivial_pair {x y} (hxy : x != y) : ({x, y} : Se
t α).Nontrivial
-/
theorem nontrivial_of_pair_subset {x y} (hxy : x ≠ y) (h : {x, y} ⊆ s) : s.Nontrivial :=
  (nontrivial_pair hxy).mono h
/-
**Set.Nontrivial.pair_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nontrivial`。
形式化陈述：∀ {α : Type u} {s : Set α}, s.Nontrivial → ∃ x y, x ≠ y ∧ {x, y} ⊆ s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.insert_subset`：insert_subset (ha : a in t) (hs : s subseteq t) : ins
ert a s subseteq t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
-/
theorem Nontrivial.pair_subset (hs : s.Nontrivial) : ∃ x y, x ≠ y ∧ {x, y} ⊆ s :=
  let ⟨x, hx, y, hy, hxy⟩ := hs
  ⟨x, y, hxy, insert_subset hx <| singleton_subset_iff.2 hy⟩
/-
**Set.nontrivial_iff_pair_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：nontrivial_iff_pair_subset : s.Nontrivial ↔ exists x y, x != y ∧ {x, y} su
bseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nontrivial.pair_subset`：∀ {α : Type u} {s : Set α}, s.Nontrivial → ∃
 x y, x ≠ y ∧ {x, y} ⊆ s
· 使用定理 `Set.nontrivial_of_pair_subset`：nontrivial_of_pair_subset {x y} (hxy : x 
!= y) (h : {x, y} subseteq s) : s.Nontrivial
-/
theorem nontrivial_iff_pair_subset : s.Nontrivial ↔ ∃ x y, x ≠ y ∧ {x, y} ⊆ s :=
  ⟨Nontrivial.pair_subset, fun H =>
    let ⟨_, _, hxy, h⟩ := H
    nontrivial_of_pair_subset hxy h⟩
/-
**Set.nontrivial_of_exists_ne** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：nontrivial_of_exists_ne {x} (hx : x in s) (h : exists y in s, y != x) : s.
Nontrivial
参数：hx : x in s；h : exists y in s, y != x。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nontrivial_of_exists_ne {x} (hx : x ∈ s) (h : ∃ y ∈ s, y ≠ x) : s.Nontrivial :=
  let ⟨y, hy, hyx⟩ := h
  ⟨y, hy, x, hx, hyx⟩
/-
**Set.Nontrivial.exists_ne** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nontrivial`。
形式化陈述：∀ {α : Type u} {s : Set α}, s.Nontrivial → ∀ (z : α), ∃ x ∈ s, x ≠ z
参数：z : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem Nontrivial.exists_ne (hs : s.Nontrivial) (z) : ∃ x ∈ s, x ≠ z := by
  by_contra! H
  rcases hs with ⟨x, hx, y, hy, hxy⟩
  rw [H x hx, H y hy] at hxy
  exact hxy rfl
/-
**Set.nontrivial_iff_exists_ne** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：nontrivial_iff_exists_ne {x} (hx : x in s) : s.Nontrivial ↔ exists y in s,
 y != x
参数：hx : x in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nontrivial.exists_ne`：∀ {α : Type u} {s : Set α}, s.Nontrivial → ∀ (
z : α), ∃ x ∈ s, x ≠ z
· 使用定理 `Set.nontrivial_of_exists_ne`：nontrivial_of_exists_ne {x} (hx : x in s) (
h : exists y in s, y != x) : s.Nontrivial
-/
theorem nontrivial_iff_exists_ne {x} (hx : x ∈ s) : s.Nontrivial ↔ ∃ y ∈ s, y ≠ x :=
  ⟨fun H => H.exists_ne _, nontrivial_of_exists_ne hx⟩
/-
**Set.nontrivial_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：nontrivial_of_lt [Preorder α] {x y} (hx : x in s) (hy : y in s) (hxy : x <
 y) : s.Nontrivial
参数：hx : x in s；hy : y in s；hxy : x < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
-/
theorem nontrivial_of_lt [Preorder α] {x y} (hx : x ∈ s) (hy : y ∈ s) (hxy : x < y) :
    s.Nontrivial :=
  ⟨x, hx, y, hy, ne_of_lt hxy⟩
/-
**Set.nontrivial_of_exists_lt** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：nontrivial_of_exists_lt [Preorder α] (H : existsᵉ (x in s) (y in s), x < y
) : s.Nontrivial
参数：H : existsᵉ (x in s) (y in s), x < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.nontrivial_of_lt`：nontrivial_of_lt [Preorder α] {x y} (hx : x in s) 
(hy : y in s) (hxy : x < y) : s.Nontrivial
-/
theorem nontrivial_of_exists_lt [Preorder α]
    (H : ∃ᵉ (x ∈ s) (y ∈ s), x < y) : s.Nontrivial :=
  let ⟨_, hx, _, hy, hxy⟩ := H
  nontrivial_of_lt hx hy hxy
/-
**Set.Nontrivial.exists_lt** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nontrivial`。
形式化陈述：∀ {α : Type u} {s : Set α} [inst : LinearOrder α], s.Nontrivial → ∃ x ∈ s,
 ∃ y ∈ s, x < y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用引理 `lt_or_gt_of_ne`：lt_or_gt_of_ne (h : a != b) : a < b ∨ b < a
-/
theorem Nontrivial.exists_lt [LinearOrder α] (hs : s.Nontrivial) : ∃ᵉ (x ∈ s) (y ∈ s), x < y :=
  let ⟨x, hx, y, hy, hxy⟩ := hs
  Or.elim (lt_or_gt_of_ne hxy) (fun H => ⟨x, hx, y, hy, H⟩) fun H => ⟨y, hy, x, hx, H⟩
/-
**Set.nontrivial_iff_exists_lt** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：nontrivial_iff_exists_lt [LinearOrder α] : s.Nontrivial ↔ existsᵉ (x in s)
 (y in s), x < y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nontrivial.exists_lt`：∀ {α : Type u} {s : Set α} [inst : LinearOrder
 α], s.Nontrivial → ∃ x ∈ s, ∃ y ∈ s, x < y
· 使用定理 `Set.nontrivial_of_exists_lt`：nontrivial_of_exists_lt [Preorder α] (H : e
xistsᵉ (x in s) (y in s), x < y) : s.Nontrivial
-/
theorem nontrivial_iff_exists_lt [LinearOrder α] :
    s.Nontrivial ↔ ∃ᵉ (x ∈ s) (y ∈ s), x < y :=
  ⟨Nontrivial.exists_lt, nontrivial_of_exists_lt⟩
/-
**Set.Nontrivial.nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nontrivial`。
形式化陈述：∀ {α : Type u} {s : Set α}, s.Nontrivial → s.Nonempty
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem Nontrivial.nonempty (hs : s.Nontrivial) : s.Nonempty :=
  let ⟨x, hx, _⟩ := hs
  ⟨x, hx⟩
/-
**Set.Nontrivial.ne_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nontrivial`。
形式化陈述：∀ {α : Type u} {s : Set α}, s.Nontrivial → s ≠ ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.ne_empty`：∀ {α : Type u} {s : Set α}, s.Nonempty → s ≠ ∅
· 使用定理 `Set.Nontrivial.nonempty`：∀ {α : Type u} {s : Set α}, s.Nontrivial → s.No
nempty
-/
protected theorem Nontrivial.ne_empty (hs : s.Nontrivial) : s ≠ ∅ :=
  hs.nonempty.ne_empty
/-
**Set.Nontrivial.not_subset_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nontrivial`。
形式化陈述：∀ {α : Type u} {s : Set α}, s.Nontrivial → ¬s ⊆ ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.not_subset_empty`：∀ {α : Type u} {s : Set α}, s.Nonempty → 
¬s ⊆ ∅
· 使用定理 `Set.Nontrivial.nonempty`：∀ {α : Type u} {s : Set α}, s.Nontrivial → s.No
nempty
-/
theorem Nontrivial.not_subset_empty (hs : s.Nontrivial) : ¬s ⊆ ∅ :=
  hs.nonempty.not_subset_empty

@[simp]
/-
**Set.not_nontrivial_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：not_nontrivial_empty : ¬(∅ : Set α).Nontrivial
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nontrivial.ne_empty`：∀ {α : Type u} {s : Set α}, s.Nontrivial → s ≠ 
∅
-/
theorem not_nontrivial_empty : ¬(∅ : Set α).Nontrivial := fun h => h.ne_empty rfl

@[simp]
/-
**Set.not_nontrivial_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：not_nontrivial_singleton {x} : ¬({x} : Set α).Nontrivial
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.nontrivial_iff_exists_ne`：nontrivial_iff_exists_ne {x} (hx : x in s)
 : s.Nontrivial ↔ exists y in s, y != x
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
-/
theorem not_nontrivial_singleton {x} : ¬({x} : Set α).Nontrivial := fun H => by
  rw [nontrivial_iff_exists_ne (mem_singleton x)] at H
  let ⟨y, hy, hya⟩ := H
  exact hya (mem_singleton_iff.1 hy)
/-
**Set.Nontrivial.ne_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nontrivial`。
形式化陈述：∀ {α : Type u} {s : Set α} {x : α}, s.Nontrivial → s ≠ {x}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.not_nontrivial_singleton`：not_nontrivial_singleton {x} : ¬({x} : Set
 α).Nontrivial
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem Nontrivial.ne_singleton {x} (hs : s.Nontrivial) : s ≠ {x} := fun H => by
  rw [H] at hs
  exact not_nontrivial_singleton hs
/-
**Set.Nontrivial.not_subset_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nontrivial`
。
形式化陈述：∀ {α : Type u} {s : Set α} {x : α}, s.Nontrivial → ¬s ⊆ {x}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Set.subset_singleton_iff_eq`：subset_singleton_iff_eq {s : Set α} {x : α}
 : s subseteq {x} ↔ s = ∅ ∨ s = {x}
· 使用定理 `not_or_intro`：∀ {a b : Prop}, ¬a → ¬b → ¬(a ∨ b)
· 使用定理 `Set.Nontrivial.ne_empty`：∀ {α : Type u} {s : Set α}, s.Nontrivial → s ≠ 
∅
· 使用定理 `Set.Nontrivial.ne_singleton`：∀ {α : Type u} {s : Set α} {x : α}, s.Nontr
ivial → s ≠ {x}
-/
theorem Nontrivial.not_subset_singleton {x} (hs : s.Nontrivial) : ¬s ⊆ {x} :=
  (not_congr subset_singleton_iff_eq).2 (not_or_intro hs.ne_empty hs.ne_singleton)
/-
**Set.nontrivial_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：nontrivial_univ [Nontrivial α] : (univ : Set α).Nontrivial
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_pair_ne`：exists_pair_ne (α : Type*) [Nontrivial α] : exists x y :
 α, x != y
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem nontrivial_univ [Nontrivial α] : (univ : Set α).Nontrivial :=
  let ⟨x, y, hxy⟩ := exists_pair_ne α
  ⟨x, mem_univ _, y, mem_univ _, hxy⟩
/-
**Set.nontrivial_of_univ_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：nontrivial_of_univ_nontrivial (h : (univ : Set α).Nontrivial) : Nontrivial
 α
参数：h : (univ : Set α).Nontrivial。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nontrivial_of_univ_nontrivial (h : (univ : Set α).Nontrivial) : Nontrivial α :=
  let ⟨x, _, y, _, hxy⟩ := h
  ⟨⟨x, y, hxy⟩⟩

@[simp]
/-
**Set.nontrivial_univ_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：nontrivial_univ_iff : (univ : Set α).Nontrivial ↔ Nontrivial α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.nontrivial_of_univ_nontrivial`：nontrivial_of_univ_nontrivial (h : (u
niv : Set α).Nontrivial) : Nontrivial α
· 使用定理 `Set.nontrivial_univ`：nontrivial_univ [Nontrivial α] : (univ : Set α).Non
trivial
-/
theorem nontrivial_univ_iff : (univ : Set α).Nontrivial ↔ Nontrivial α :=
  ⟨nontrivial_of_univ_nontrivial, fun h => @nontrivial_univ _ h⟩

@[simp]
/-
**Set.singleton_ne_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：singleton_ne_univ [Nontrivial α] (a : α) : {a} != univ
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nontrivial.not_subset_singleton`：∀ {α : Type u} {s : Set α} {x : α},
 s.Nontrivial → ¬s ⊆ {x}
· 使用定理 `Set.nontrivial_univ`：nontrivial_univ [Nontrivial α] : (univ : Set α).Non
trivial
· 使用定理 `Eq.superset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preord
er α] {a b : α}, a = b → b ⊆ a
-/
theorem singleton_ne_univ [Nontrivial α] (a : α) : {a} ≠ univ :=
  fun h ↦ nontrivial_univ.not_subset_singleton h.superset

@[simp]
/-
**Set.singleton_ssubset_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：singleton_ssubset_univ [Nontrivial α] (a : α) : {a} ⊂ univ
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.ssubset_univ_iff`：ssubset_univ_iff : s ⊂ univ ↔ s != univ
· 使用定理 `Set.singleton_ne_univ`：singleton_ne_univ [Nontrivial α] (a : α) : {a} !=
 univ
-/
theorem singleton_ssubset_univ [Nontrivial α] (a : α) : {a} ⊂ univ :=
  ssubset_univ_iff.mpr <| singleton_ne_univ a
/-
**Set.nontrivial_of_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：nontrivial_of_nontrivial (hs : s.Nontrivial) : Nontrivial α
参数：hs : s.Nontrivial。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nontrivial_of_nontrivial (hs : s.Nontrivial) : Nontrivial α :=
  let ⟨x, _, y, _, hxy⟩ := hs
  ⟨⟨x, y, hxy⟩⟩

/-- `s`, coerced to a type, is a nontrivial type if and only if `s` is a nontrivial set. -/
@[simp, norm_cast]
/-
**Set.nontrivial_coe_sort** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：nontrivial_coe_sort {s : Set α} : Nontrivial s ↔ s.Nontrivial
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
`s`, coerced to a type, is a nontrivial type if and only if `s` is a nontrivial 
set.
-/
theorem nontrivial_coe_sort {s : Set α} : Nontrivial s ↔ s.Nontrivial := by
  simp [← nontrivial_univ_iff, Set.Nontrivial]

alias ⟨_, Nontrivial.coe_sort⟩ := nontrivial_coe_sort

/-- A type with a set `s` whose `coe_sort` is a nontrivial type is nontrivial.
For the corresponding result for `Subtype`, see `Subtype.nontrivial_iff_exists_ne`. -/
/-
**Set.nontrivial_of_nontrivial_coe** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：nontrivial_of_nontrivial_coe (hs : Nontrivial s) : Nontrivial α
参数：hs : Nontrivial s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.nontrivial_of_nontrivial`：nontrivial_of_nontrivial (hs : s.Nontrivia
l) : Nontrivial α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.nontrivial_coe_sort`：nontrivial_coe_sort {s : Set α} : Nontrivial s 
↔ s.Nontrivial

--- 原说明 ---
A type with a set `s` whose `coe_sort` is a nontrivial type is nontrivial.
For the corresponding result for `Subtype`, see `Subtype.nontrivial_iff_exists_n
e`.
-/
theorem nontrivial_of_nontrivial_coe (hs : Nontrivial s) : Nontrivial α :=
  nontrivial_of_nontrivial <| nontrivial_coe_sort.1 hs
/-
**Set.nontrivial_mono** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：nontrivial_mono {α : Type*} {s t : Set α} (hst : s subseteq t) (hs : Nontr
ivial s) : Nontrivial t
参数：hst : s subseteq t；hs : Nontrivial s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nontrivial.coe_sort`：∀ {α : Type u} {s : Set α}, s.Nontrivial → Nont
rivial ↑s
· 使用定理 `Set.Nontrivial.mono`：∀ {α : Type u} {s t : Set α}, s.Nontrivial → s ⊆ t 
→ t.Nontrivial
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.nontrivial_coe_sort`：nontrivial_coe_sort {s : Set α} : Nontrivial s 
↔ s.Nontrivial
-/
theorem nontrivial_mono {α : Type*} {s t : Set α} (hst : s ⊆ t) (hs : Nontrivial s) :
    Nontrivial t :=
  Nontrivial.coe_sort <| (nontrivial_coe_sort.1 hs).mono hst

@[simp, push]
/-
**Set.not_subsingleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：not_subsingleton_iff : ¬s.Subsingleton ↔ s.Nontrivial
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem not_subsingleton_iff : ¬s.Subsingleton ↔ s.Nontrivial := by
  simp_rw [Set.Subsingleton, Set.Nontrivial, not_forall, exists_prop]

@[simp, push]
/-
**Set.not_nontrivial_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：not_nontrivial_iff : ¬s.Nontrivial ↔ s.Subsingleton
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not_left`：Iff.not_left (h : a ↔ ¬b) : ¬a ↔ b
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Set.not_subsingleton_iff`：not_subsingleton_iff : ¬s.Subsingleton ↔ s.Non
trivial
-/
theorem not_nontrivial_iff : ¬s.Nontrivial ↔ s.Subsingleton :=
  Iff.not_left not_subsingleton_iff.symm

alias ⟨_, Subsingleton.not_nontrivial⟩ := not_nontrivial_iff

alias ⟨_, Nontrivial.not_subsingleton⟩ := not_subsingleton_iff
/-
**Set.subsingleton_or_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u} (s : Set α), s.Subsingleton ∨ s.Nontrivial
参数：s : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
protected lemma subsingleton_or_nontrivial (s : Set α) : s.Subsingleton ∨ s.Nontrivial := by
  simp [or_iff_not_imp_right]
/-
**Set.eq_singleton_or_nontrivial** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：eq_singleton_or_nontrivial (ha : a in s) : s = {a} ∨ s.Nontrivial
参数：ha : a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.subsingleton_iff_singleton`：subsingleton_iff_singleton {x} (hx : x i
n s) : s.Subsingleton ↔ s = {x}
· 使用定理 `Set.subsingleton_or_nontrivial`：∀ {α : Type u} (s : Set α), s.Subsinglet
on ∨ s.Nontrivial
-/
lemma eq_singleton_or_nontrivial (ha : a ∈ s) : s = {a} ∨ s.Nontrivial := by
  rw [← subsingleton_iff_singleton ha]; exact s.subsingleton_or_nontrivial
/-
**Set.nontrivial_iff_ne_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：nontrivial_iff_ne_singleton (ha : a in s) : s.Nontrivial ↔ s != {a}
参数：ha : a in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nontrivial.ne_singleton`：∀ {α : Type u} {s : Set α} {x : α}, s.Nontr
ivial → s ≠ {x}
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用引理 `Set.eq_singleton_or_nontrivial`：eq_singleton_or_nontrivial (ha : a in s)
 : s = {a} ∨ s.Nontrivial
-/
lemma nontrivial_iff_ne_singleton (ha : a ∈ s) : s.Nontrivial ↔ s ≠ {a} :=
  ⟨Nontrivial.ne_singleton, (eq_singleton_or_nontrivial ha).resolve_left⟩
/-
**Set.Nonempty.exists_eq_singleton_or_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `Set.
Nonempty`。
形式化陈述：∀ {α : Type u} {s : Set α}, s.Nonempty → (∃ a, s = {a}) ∨ s.Nontrivial
参数：∃ a, s = {a}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp_left`：∀ {a b c : Prop}, (a → b) → a ∨ c → b ∨ c
· 使用引理 `Set.eq_singleton_or_nontrivial`：eq_singleton_or_nontrivial (ha : a in s)
 : s = {a} ∨ s.Nontrivial
-/
lemma Nonempty.exists_eq_singleton_or_nontrivial : s.Nonempty → (∃ a, s = {a}) ∨ s.Nontrivial :=
  fun ⟨a, ha⟩ ↦ (eq_singleton_or_nontrivial ha).imp_left <| Exists.intro a
/-
**Set.univ_eq_true_false** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：univ_eq_true_false : univ = ({True, False} : Set Prop)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.eq_univ_of_forall`：eq_univ_of_forall {s : Set α} : (forall x, x in s
) -> s = univ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_insert_iff`：mem_insert_iff {x a : α} {s : Set α} : x in insert a
 s ↔ x = a ∨ x in s
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `Classical.propComplete`：∀ (a : Prop), a = True ∨ a = False
-/
theorem univ_eq_true_false : univ = ({True, False} : Set Prop) :=
  Eq.symm <| eq_univ_of_forall fun x => by
    rw [mem_insert_iff, mem_singleton_iff]
    exact Classical.propComplete x

@[simp]
/-
**Set.univ_set_of_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：univ_set_of_isEmpty [IsEmpty α] : @univ (Set α) = {∅}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.eq_empty_of_isEmpty`：eq_empty_of_isEmpty (s : Set α) [IsEmpty s] : s
 = ∅
· 使用定理 `instIsEmptySubtype`：∀ {α : Sort u} [IsEmpty α] (p : α → Prop), IsEmpty (
Subtype p)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem univ_set_of_isEmpty [IsEmpty α] : @univ (Set α) = {∅} :=
  subset_antisymm (fun S hS ↦ by simp [Set.eq_empty_of_isEmpty S]) (by simp)

@[simp]
/-
**Set.univ_set_eq_singleton_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：univ_set_eq_singleton_empty_iff : @Set.univ (Set α) = {∅} ↔ IsEmpty α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.univ_set_of_isEmpty`：univ_set_of_isEmpty [IsEmpty α] : @univ (Set α)
 = {∅}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem univ_set_eq_singleton_empty_iff : @Set.univ (Set α) = {∅} ↔ IsEmpty α := by
  refine ⟨fun h ↦ ?_, fun _ ↦ by simp⟩
  suffices @univ α ∈ univ by aesop
  simp

end Nontrivial
section Monotonicity

/-! ### Monotonicity on singletons -/

variable {α : Type u} {β : Type v} {a : α} {s : Set α} [Preorder α] [Preorder β] (f : α → β)

/-
**Set.Subsingleton.monotoneOn** 是 Mathlib 中的一个定理，位于命名空间 `Set.Subsingleton`。
形式化陈述：∀ {α : Type u} {β : Type v} {s : Set α} [inst : Preorder α] [inst_1 : Preo
rder β] (f : α → β),   s.Subsingleton → MonotoneOn f s
参数：f : α → β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
protected theorem Subsingleton.monotoneOn (h : s.Subsingleton) : MonotoneOn f s :=
  fun _ ha _ hb _ => (congr_arg _ (h ha hb)).le
/-
**Set.Subsingleton.antitoneOn** 是 Mathlib 中的一个定理，位于命名空间 `Set.Subsingleton`。
形式化陈述：∀ {α : Type u} {β : Type v} {s : Set α} [inst : Preorder α] [inst_1 : Preo
rder β] (f : α → β),   s.Subsingleton → AntitoneOn f s
参数：f : α → β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
protected theorem Subsingleton.antitoneOn (h : s.Subsingleton) : AntitoneOn f s :=
  fun _ ha _ hb _ => (congr_arg _ (h hb ha)).le
/-
**Set.Subsingleton.strictMonoOn** 是 Mathlib 中的一个定理，位于命名空间 `Set.Subsingleton`。
形式化陈述：∀ {α : Type u} {β : Type v} {s : Set α} [inst : Preorder α] [inst_1 : Preo
rder β] (f : α → β),   s.Subsingleton → StrictMonoOn f s
参数：f : α → β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
-/
protected theorem Subsingleton.strictMonoOn (h : s.Subsingleton) : StrictMonoOn f s :=
  fun _ ha _ hb hlt => (hlt.ne (h ha hb)).elim
/-
**Set.Subsingleton.strictAntiOn** 是 Mathlib 中的一个定理，位于命名空间 `Set.Subsingleton`。
形式化陈述：∀ {α : Type u} {β : Type v} {s : Set α} [inst : Preorder α] [inst_1 : Preo
rder β] (f : α → β),   s.Subsingleton → StrictAntiOn f s
参数：f : α → β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
-/
protected theorem Subsingleton.strictAntiOn (h : s.Subsingleton) : StrictAntiOn f s :=
  fun _ ha _ hb hlt => (hlt.ne (h ha hb)).elim

@[simp]
/-
**Set.monotoneOn_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：monotoneOn_singleton : MonotoneOn f {a}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.monotoneOn`：∀ {α : Type u} {β : Type v} {s : Set α} [in
st : Preorder α] [inst_1 : Preorder β] (f : α → β),   s.Subsingleton → MonotoneO
n f s
· 使用定理 `Set.subsingleton_singleton`：subsingleton_singleton {a} : ({a} : Set α).S
ubsingleton
-/
theorem monotoneOn_singleton : MonotoneOn f {a} :=
  subsingleton_singleton.monotoneOn f

@[simp]
/-
**Set.antitoneOn_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：antitoneOn_singleton : AntitoneOn f {a}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.antitoneOn`：∀ {α : Type u} {β : Type v} {s : Set α} [in
st : Preorder α] [inst_1 : Preorder β] (f : α → β),   s.Subsingleton → AntitoneO
n f s
· 使用定理 `Set.subsingleton_singleton`：subsingleton_singleton {a} : ({a} : Set α).S
ubsingleton
-/
theorem antitoneOn_singleton : AntitoneOn f {a} :=
  subsingleton_singleton.antitoneOn f

@[simp]
/-
**Set.strictMonoOn_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：strictMonoOn_singleton : StrictMonoOn f {a}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.strictMonoOn`：∀ {α : Type u} {β : Type v} {s : Set α} [
inst : Preorder α] [inst_1 : Preorder β] (f : α → β),   s.Subsingleton → StrictM
onoOn f s
· 使用定理 `Set.subsingleton_singleton`：subsingleton_singleton {a} : ({a} : Set α).S
ubsingleton
-/
theorem strictMonoOn_singleton : StrictMonoOn f {a} :=
  subsingleton_singleton.strictMonoOn f

@[simp]
/-
**Set.strictAntiOn_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：strictAntiOn_singleton : StrictAntiOn f {a}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.strictAntiOn`：∀ {α : Type u} {β : Type v} {s : Set α} [
inst : Preorder α] [inst_1 : Preorder β] (f : α → β),   s.Subsingleton → StrictA
ntiOn f s
· 使用定理 `Set.subsingleton_singleton`：subsingleton_singleton {a} : ({a} : Set α).S
ubsingleton
-/
theorem strictAntiOn_singleton : StrictAntiOn f {a} :=
  subsingleton_singleton.strictAntiOn f

end Monotonicity

end Set

