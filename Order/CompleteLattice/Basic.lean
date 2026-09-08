/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Data.Set.NAry
public import Mathlib.Data.ULift
public import Mathlib.Order.Bounds.Image
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.Hom.Set

/-!
# Theory of complete lattices

This file contains basic results on complete lattices.

## Naming conventions

In lemma names,
* `sSup` is called `sSup`
* `sInf` is called `sInf`
* `⨆ i, s i` is called `iSup`
* `⨅ i, s i` is called `iInf`
* `⨆ i j, s i j` is called `iSup₂`. This is an `iSup` inside an `iSup`.
* `⨅ i j, s i j` is called `iInf₂`. This is an `iInf` inside an `iInf`.
* `⨆ i ∈ s, t i` is called `biSup` for "bounded `iSup`". This is the special case of `iSup₂`
  where `j : i ∈ s`.
* `⨅ i ∈ s, t i` is called `biInf` for "bounded `iInf`". This is the special case of `iInf₂`
  where `j : i ∈ s`.

## Notation

* `⨆ i, f i` : `iSup f`, the supremum of the range of `f`;
* `⨅ i, f i` : `iInf f`, the infimum of the range of `f`.
-/

public section

open Function OrderDual Set

variable {α β γ : Type*} {ι ι' : Sort*} {κ : ι → Sort*} {κ' : ι' → Sort*}

/-
**iSup_ulift** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} {ι : Type u_8} [inst : SupSet α] (f : ULift.{u_9, u_8} ι 
→ α), ⨆ i, f i = ⨆ i, f { down := i }
参数：f : ULift.{u_9, u_8} ι → α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[to_dual (attr := simp)] lemma iSup_ulift {ι : Type*} [SupSet α] (f : ULift ι → α) :
    ⨆ i : ULift ι, f i = ⨆ i, f (.up i) := by simp only [iSup]; congr with x; simp

section

variable [CompleteSemilatticeSup α] {s t : Set α} {a b : α}

@[to_dual]
/-
**sSup_le_sSup_of_isCofinalFor** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sSup_le_sSup_of_isCofinalFor (h : IsCofinalFor s t) : sSup s <= sSup t
参数：h : IsCofinalFor s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLeast.mono`：IsLeast.mono (ha : IsLeast s a) (hb : IsLeast t b) (hst : 
s subseteq t) : b <= a
· 使用定理 `isLUB_sSup`：isLUB_sSup (s : Set α) : IsLUB s (sSup s)
· 使用引理 `upperBounds_mono_of_isCofinalFor`：upperBounds_mono_of_isCofinalFor (hst 
: IsCofinalFor s t) : upperBounds t subseteq upperBounds s
-/
theorem sSup_le_sSup_of_isCofinalFor (h : IsCofinalFor s t) : sSup s ≤ sSup t :=
  IsLeast.mono (isLUB_sSup t) (isLUB_sSup s) <| upperBounds_mono_of_isCofinalFor h

-- We will generalize this to conditionally complete lattices in `csSup_singleton`.
@[to_dual (attr := simp)]
/-
**sSup_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sSup_singleton {a : α} : sSup {a} = a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLUB.sSup_eq`：∀ {α : Type u_1} [inst : CompleteSemilatticeSup α] {s : S
et α} {a : α}, IsLUB s a → sSup s = a
· 使用定理 `isLUB_singleton`：isLUB_singleton : IsLUB {a} a
-/
theorem sSup_singleton {a : α} : sSup {a} = a :=
  isLUB_singleton.sSup_eq

end

open OrderDual

section

variable [CompleteLattice α] {s t : Set α} {b : α}

/-
**sInf_le_sSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sInf_le_sSup (hs : s.Nonempty) : sInf s <= sSup s
参数：hs : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isGLB_le_isLUB`：isGLB_le_isLUB (ha : IsGLB s a) (hb : IsLUB s b) (hs : s
.Nonempty) : a <= b
· 使用定理 `isGLB_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] (s : Set 
α), IsGLB s (sInf s)
· 使用定理 `isLUB_sSup`：isLUB_sSup (s : Set α) : IsLUB s (sSup s)
-/
theorem sInf_le_sSup (hs : s.Nonempty) : sInf s ≤ sSup s :=
  isGLB_le_isLUB (isGLB_sInf s) (isLUB_sSup s) hs
/-
**sInf_le_sSup_of_nonempty_inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sInf_le_sSup_of_nonempty_inter (h : (s inter t).Nonempty) : sInf s <= sSup
 t
参数：h : (s inter t).Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isGLB_le_isLUB_of_nonempty_inter`：isGLB_le_isLUB_of_nonempty_inter (h : 
(s inter s').Nonempty) (ha : IsGLB s a) (hb : IsLUB s' b) : a <= b
· 使用定理 `isGLB_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] (s : Set 
α), IsGLB s (sInf s)
· 使用定理 `isLUB_sSup`：isLUB_sSup (s : Set α) : IsLUB s (sSup s)
-/
theorem sInf_le_sSup_of_nonempty_inter (h : (s ∩ t).Nonempty) : sInf s ≤ sSup t :=
  isGLB_le_isLUB_of_nonempty_inter h (isGLB_sInf s) (isLUB_sSup t)

@[to_dual]
/-
**sSup_union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sSup_union {s t : Set α} : sSup (s union t) = sSup s ⊔ sSup t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLUB.sSup_eq`：∀ {α : Type u_1} [inst : CompleteSemilatticeSup α] {s : S
et α} {a : α}, IsLUB s a → sSup s = a
· 使用定理 `IsLUB.union`：IsLUB.union [SemilatticeSup γ] {a b : γ} {s t : Set γ} (hs 
: IsLUB s a) (ht : IsLUB t b) : IsLUB (s union t) (a ⊔ b)
· 使用定理 `isLUB_sSup`：isLUB_sSup (s : Set α) : IsLUB s (sSup s)
-/
theorem sSup_union {s t : Set α} : sSup (s ∪ t) = sSup s ⊔ sSup t :=
  ((isLUB_sSup s).union (isLUB_sSup t)).sSup_eq

@[to_dual le_sInf_inter]
/-
**sSup_inter_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sSup_inter_le {s t : Set α} : sSup (s inter t) <= sSup s ⊓ sSup t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sSup_le`：sSup_le (h : forall b in s, b <= a) : sSup s <= a
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem sSup_inter_le {s t : Set α} : sSup (s ∩ t) ≤ sSup s ⊓ sSup t :=
  sSup_le fun _ hb => le_inf (le_sSup hb.1) (le_sSup hb.2)

@[to_dual (attr := simp)]
/-
**sSup_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sSup_empty : sSup ∅ = (⊥ : α)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLUB.sSup_eq`：∀ {α : Type u_1} [inst : CompleteSemilatticeSup α] {s : S
et α} {a : α}, IsLUB s a → sSup s = a
· 使用定理 `isLUB_empty`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : OrderBot α],
 IsLUB ∅ ⊥
-/
theorem sSup_empty : sSup ∅ = (⊥ : α) :=
  (@isLUB_empty α _ _).sSup_eq

@[to_dual (attr := simp)]
/-
**sSup_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sSup_univ : sSup univ = (⊤ : α)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLUB.sSup_eq`：∀ {α : Type u_1} [inst : CompleteSemilatticeSup α] {s : S
et α} {a : α}, IsLUB s a → sSup s = a
· 使用定理 `isLUB_univ`：isLUB_univ [OrderTop α] : IsLUB (univ : Set α) ⊤
-/
theorem sSup_univ : sSup univ = (⊤ : α) :=
  (@isLUB_univ α _ _).sSup_eq

-- TODO(Jeremy): get this automatically
@[to_dual (attr := simp)]
/-
**sSup_insert** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sSup_insert {a : α} {s : Set α} : sSup (insert a s) = a ⊔ sSup s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLUB.sSup_eq`：∀ {α : Type u_1} [inst : CompleteSemilatticeSup α] {s : S
et α} {a : α}, IsLUB s a → sSup s = a
· 使用定理 `IsLUB.insert`：∀ {γ : Type u_3} [inst : SemilatticeSup γ] (a : γ) {b : γ}
 {s : Set γ}, IsLUB s b → IsLUB (insert a s) (a ⊔ b)
· 使用定理 `isLUB_sSup`：isLUB_sSup (s : Set α) : IsLUB s (sSup s)
-/
theorem sSup_insert {a : α} {s : Set α} : sSup (insert a s) = a ⊔ sSup s :=
  ((isLUB_sSup s).insert a).sSup_eq

@[to_dual]
/-
**sSup_le_sSup_of_subset_insert_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sSup_le_sSup_of_subset_insert_bot (h : s subseteq insert ⊥ t) : sSup s <= 
sSup t
参数：h : s subseteq insert ⊥ t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `sSup_le_sSup`：sSup_le_sSup (h : s subseteq t) : sSup s <= sSup t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sSup_insert`：sSup_insert {a : α} {s : Set α} : sSup (insert a s) = a ⊔ s
Sup s
· 使用定理 `bot_sup_eq`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderBo
t α] (a : α), ⊥ ⊔ a = a
-/
theorem sSup_le_sSup_of_subset_insert_bot (h : s ⊆ insert ⊥ t) : sSup s ≤ sSup t :=
  (sSup_le_sSup h).trans_eq (sSup_insert.trans (bot_sup_eq _))

@[to_dual (attr := simp)]
/-
**sSup_sdiff_singleton_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sSup_sdiff_singleton_bot (s : Set α) : sSup (s \ {⊥}) = sSup s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `sSup_le_sSup`：sSup_le_sSup (h : s subseteq t) : sSup s <= sSup t
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `sSup_le_sSup_of_subset_insert_bot`：sSup_le_sSup_of_subset_insert_bot (h 
: s subseteq insert ⊥ t) : sSup s <= sSup t
· 使用引理 `Set.subset_insert_sdiff_singleton`：subset_insert_sdiff_singleton (x : α)
 (s : Set α) : s subseteq insert x (s \ {x})
-/
theorem sSup_sdiff_singleton_bot (s : Set α) : sSup (s \ {⊥}) = sSup s :=
  (sSup_le_sSup sdiff_subset).antisymm <|
    sSup_le_sSup_of_subset_insert_bot <| subset_insert_sdiff_singleton _ _

@[deprecated (since := "2026-06-03")] alias sSup_diff_singleton_bot := sSup_sdiff_singleton_bot

@[to_dual]
/-
**sSup_pair** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sSup_pair {a b : α} : sSup {a, b} = a ⊔ b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLUB.sSup_eq`：∀ {α : Type u_1} [inst : CompleteSemilatticeSup α] {s : S
et α} {a : α}, IsLUB s a → sSup s = a
· 使用定理 `isLUB_pair`：isLUB_pair [SemilatticeSup γ] {a b : γ} : IsLUB {a, b} (a ⊔ 
b)
-/
theorem sSup_pair {a b : α} : sSup {a, b} = a ⊔ b :=
  (@isLUB_pair α _ a b).sSup_eq

@[to_dual (attr := simp)]
/-
**sSup_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sSup_eq_bot : sSup s = ⊥ ↔ forall a in s, a = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_unique`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ → a = ⊥
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s
· 使用定理 `sSup_le`：sSup_le (h : forall b in s, b <= a) : sSup s <= a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
-/
theorem sSup_eq_bot : sSup s = ⊥ ↔ ∀ a ∈ s, a = ⊥ :=
  ⟨fun h _ ha => bot_unique <| h ▸ le_sSup ha, fun h =>
    bot_unique <| sSup_le fun a ha => le_bot_iff.2 <| h a ha⟩

@[to_dual]
/-
**sSup_eq_bot'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sSup_eq_bot' {s : Set α} : sSup s = ⊥ ↔ s = ∅ ∨ s = {⊥}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sSup_eq_bot`：sSup_eq_bot : sSup s = ⊥ ↔ forall a in s, a = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.subset_singleton_iff_eq`：subset_singleton_iff_eq {s : Set α} {x : α}
 : s subseteq {x} ↔ s = ∅ ∨ s = {x}
· 使用定理 `Set.subset_singleton_iff`：subset_singleton_iff {α : Type*} {s : Set α} {
x : α} : s subseteq {x} ↔ forall y in s, y = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma sSup_eq_bot' {s : Set α} : sSup s = ⊥ ↔ s = ∅ ∨ s = {⊥} := by
  rw [sSup_eq_bot, ← subset_singleton_iff_eq, subset_singleton_iff]

@[to_dual]
/-
**eq_singleton_bot_of_sSup_eq_bot_of_nonempty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_singleton_bot_of_sSup_eq_bot_of_nonempty {s : Set α} (h_sup : sSup s = 
⊥) (hne : s.Nonempty) : s = {⊥}
参数：h_sup : sSup s = ⊥；hne : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.eq_singleton_iff_nonempty_unique_mem`：eq_singleton_iff_nonempty_uniq
ue_mem : s = {a} ↔ s.Nonempty ∧ forall x in s, x = a
· 使用定理 `sSup_eq_bot`：sSup_eq_bot : sSup s = ⊥ ↔ forall a in s, a = ⊥
-/
theorem eq_singleton_bot_of_sSup_eq_bot_of_nonempty {s : Set α} (h_sup : sSup s = ⊥)
    (hne : s.Nonempty) : s = {⊥} := by
  rw [Set.eq_singleton_iff_nonempty_unique_mem]
  rw [sSup_eq_bot] at h_sup
  exact ⟨hne, h_sup⟩

/-- Introduction rule to prove that `b` is the supremum of `s`: it suffices to check that `b`
is larger than all elements of `s`, and that this is not the case of any `w < b`.
See `csSup_eq_of_forall_le_of_forall_lt_exists_gt` for a version in conditionally complete
lattices. -/
@[to_dual sInf_eq_of_forall_ge_of_forall_gt_exists_lt
/-- Introduction rule to prove that `b` is the infimum of `s`: it suffices to check that `b`
is smaller than all elements of `s`, and that this is not the case of any `w > b`.
See `csInf_eq_of_forall_ge_of_forall_gt_exists_lt` for a version in conditionally complete
lattices. -/]
/-
**sSup_eq_of_forall_le_of_forall_lt_exists_gt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sSup_eq_of_forall_le_of_forall_lt_exists_gt (h₁ : forall a in s, a <= b) (
h₂ : forall w, w < b -> exists a in s, w < a) : sSup s = b
参数：h₁ : forall a in s, a <= b；h₂ : forall w, w < b -> exists a in s, w < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_of_not_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, 
a ≤ b → ¬a < b → a = b
· 使用定理 `sSup_le`：sSup_le (h : forall b in s, b <= a) : sSup s <= a
· 使用定理 `LT.lt.false`：∀ {α : Type u_2} [inst : Preorder α] {a : α}, a < a → False
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s
-/
theorem sSup_eq_of_forall_le_of_forall_lt_exists_gt (h₁ : ∀ a ∈ s, a ≤ b)
    (h₂ : ∀ w, w < b → ∃ a ∈ s, w < a) : sSup s = b :=
  (sSup_le h₁).eq_of_not_lt fun h =>
    let ⟨_, ha, ha'⟩ := h₂ _ h
    ((le_sSup ha).trans_lt ha').false

end

/-
### iSup & iInf
-/
section SupSet

variable [SupSet α] {f g : ι → α}

@[to_dual]
/-
**sSup_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sSup_range : sSup (range f) = iSup f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sSup_range : sSup (range f) = iSup f :=
  rfl

@[to_dual]
/-
**sSup_eq_iSup'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sSup_eq_iSup' (s : Set α) : sSup s = ⨆ a : s, (a : α)
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : SupSet α] (s : ι → α), iS
up s = sSup (Set.range s)
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
-/
theorem sSup_eq_iSup' (s : Set α) : sSup s = ⨆ a : s, (a : α) := by rw [iSup, Subtype.range_coe]

@[to_dual]
/-
**iSup_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_congr (h : forall i, f i = g i) : ⨆ i, f i = ⨆ i, g i
参数：h : forall i, f i = g i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem iSup_congr (h : ∀ i, f i = g i) : ⨆ i, f i = ⨆ i, g i :=
  congr_arg _ <| funext h

@[to_dual]
/-
**biSup_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：biSup_congr {p : ι -> Prop} (h : forall i, p i -> f i = g i) : ⨆ (i) (_ : 
p i), f i = ⨆ (i) (_ : p i), g i
参数：h : forall i, p i -> f i = g i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_congr`：iSup_congr (h : forall i, f i = g i) : ⨆ i, f i = ⨆ i, g i
-/
theorem biSup_congr {p : ι → Prop} (h : ∀ i, p i → f i = g i) :
    ⨆ (i) (_ : p i), f i = ⨆ (i) (_ : p i), g i :=
  iSup_congr fun i ↦ iSup_congr (h i)

@[to_dual]
/-
**biSup_congr'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：biSup_congr' {p : ι -> Prop} {f g : (i : ι) -> p i -> α} (h : forall i (hi
 : p i), f i hi = g i hi) : ⨆ i, ⨆ (hi : p i), f i hi = ⨆ i, ⨆ (hi : p i), g i h
i
参数：i : ι；h : forall i (hi : p i), f i hi = g i hi。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem biSup_congr' {p : ι → Prop} {f g : (i : ι) → p i → α}
    (h : ∀ i (hi : p i), f i hi = g i hi) :
    ⨆ i, ⨆ (hi : p i), f i hi = ⨆ i, ⨆ (hi : p i), g i hi := by
  #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
  (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal.
  It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in the new
  canonicalizer; a minimization would help. The original proof was: `grind` -/
  simp_all

@[to_dual]
/-
**Function.Surjective.iSup_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.Surjective.iSup_comp {f : ι -> ι'} (hf : Surjective f) (g : ι' ->
 α) : ⨆ x, g (f x) = ⨆ y, g y
参数：hf : Surjective f；g : ι' -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : SupSet α] (s : ι → α), iS
up s = sSup (Set.range s)
· 使用定理 `Function.Surjective.range_comp`：∀ {α : Type u_1} {ι : Sort u_3} {ι' : So
rt u_4} {f : ι → ι'},   Function.Surjective f → ∀ (g : ι' → α), Set.range (g ∘ f
) = Set.range g
-/
theorem Function.Surjective.iSup_comp {f : ι → ι'} (hf : Surjective f) (g : ι' → α) :
    ⨆ x, g (f x) = ⨆ y, g y := by
  simp only [iSup.eq_1]
  congr
  exact hf.range_comp g

@[to_dual]
/-
**Equiv.iSup_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equiv.iSup_comp {g : ι' -> α} (e : ι ≃ ι') : ⨆ x, g (e x) = ⨆ y, g y
参数：e : ι ≃ ι'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.iSup_comp`：Function.Surjective.iSup_comp {f : ι -> ι
'} (hf : Surjective f) (g : ι' -> α) : ⨆ x, g (f x) = ⨆ y, g y
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
-/
theorem Equiv.iSup_comp {g : ι' → α} (e : ι ≃ ι') : ⨆ x, g (e x) = ⨆ y, g y :=
  e.surjective.iSup_comp _

@[to_dual]
/-
**Function.Surjective.iSup_congr** 是 Mathlib 中的一个定理，位于命名空间 `Function.Surjective`
。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort u_5} [inst : SupSet α] {f : ι →
 α} {g : ι' → α} (h : ι → ι'),   Function.Surjective h → (∀ (x : ι), g (h x) = f
 x) → ⨆ x, f x = ⨆ y, g y
参数：h : ι → ι'；∀ (x : ι), g (h x) = f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.Surjective.iSup_comp`：Function.Surjective.iSup_comp {f : ι -> ι
'} (hf : Surjective f) (g : ι' -> α) : ⨆ x, g (f x) = ⨆ y, g y
-/
protected theorem Function.Surjective.iSup_congr {g : ι' → α} (h : ι → ι') (h1 : Surjective h)
    (h2 : ∀ x, g (h x) = f x) : ⨆ x, f x = ⨆ y, g y := by
  convert! h1.iSup_comp g
  exact (h2 _).symm

@[to_dual]
/-
**Equiv.iSup_congr** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort u_5} [inst : SupSet α] {f : ι →
 α} {g : ι' → α} (e : ι ≃ ι'),   (∀ (x : ι), g (e x) = f x) → ⨆ x, f x = ⨆ y, g 
y
参数：e : ι ≃ ι'；∀ (x : ι), g (e x) = f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.iSup_congr`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : So
rt u_5} [inst : SupSet α] {f : ι → α} {g : ι' → α} (h : ι → ι'),   Function.Surj
ective h → (∀ (x : ι…
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
-/
protected theorem Equiv.iSup_congr {g : ι' → α} (e : ι ≃ ι') (h : ∀ x, g (e x) = f x) :
    ⨆ x, f x = ⨆ y, g y :=
  e.surjective.iSup_congr _ h

@[to_dual (attr := congr)]
/-
**iSup_congr_Prop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α} (pq : p ↔ q) (f :
 forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
参数：pq : p ↔ q；f : forall x, f₁ (pq.mpr x) = f₂ x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem iSup_congr_Prop {p q : Prop} {f₁ : p → α} {f₂ : q → α} (pq : p ↔ q)
    (f : ∀ x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂ := by
  obtain rfl := propext pq
  congr with x
  apply f

@[to_dual]
/-
**iSup_plift_up** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_plift_up (f : PLift ι -> α) : ⨆ i, f (PLift.up i) = ⨆ i, f i
参数：f : PLift ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.iSup_congr`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : So
rt u_5} [inst : SupSet α] {f : ι → α} {g : ι' → α} (h : ι → ι'),   Function.Surj
ective h → (∀ (x : ι…
· 使用定理 `PLift.up_surjective`：up_surjective : Surjective (@up α)
-/
theorem iSup_plift_up (f : PLift ι → α) : ⨆ i, f (PLift.up i) = ⨆ i, f i :=
  (PLift.up_surjective.iSup_congr _) fun _ => rfl

@[to_dual]
/-
**iSup_plift_down** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_plift_down (f : ι -> α) : ⨆ i, f (PLift.down i) = ⨆ i, f i
参数：f : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.iSup_congr`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : So
rt u_5} [inst : SupSet α] {f : ι → α} {g : ι' → α} (h : ι → ι'),   Function.Surj
ective h → (∀ (x : ι…
· 使用定理 `PLift.down_surjective`：down_surjective : Surjective (@down α)
-/
theorem iSup_plift_down (f : ι → α) : ⨆ i, f (PLift.down i) = ⨆ i, f i :=
  (PLift.down_surjective.iSup_congr _) fun _ => rfl

@[to_dual]
/-
**iSup_range'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_range' (g : β -> α) (f : ι -> β) : ⨆ b : range f, g b = ⨆ i, g (f i)
参数：g : β -> α；f : ι -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : SupSet α] (s : ι → α), iS
up s = sSup (Set.range s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_eq_range`：image_eq_range (f : α -> β) (s : Set α) : f '' s = r
ange fun x : s => f x
· 使用定理 `Set.range_comp'`：range_comp' (g : α -> β) (f : ι -> α) : range (fun x =>
 g (f x)) = g '' range f
-/
theorem iSup_range' (g : β → α) (f : ι → β) : ⨆ b : range f, g b = ⨆ i, g (f i) := by
  rw [iSup, iSup, ← image_eq_range, ← range_comp']

@[to_dual]
/-
**sSup_image'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sSup_image' {s : Set β} {f : β -> α} : sSup (f '' s) = ⨆ a : s, f a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : SupSet α] (s : ι → α), iS
up s = sSup (Set.range s)
· 使用定理 `Set.image_eq_range`：image_eq_range (f : α -> β) (s : Set α) : f '' s = r
ange fun x : s => f x
-/
theorem sSup_image' {s : Set β} {f : β → α} : sSup (f '' s) = ⨆ a : s, f a := by
  rw [iSup, image_eq_range]

end SupSet

section

variable [CompleteLattice α] {f g s : ι → α} {a b : α}

@[to_dual iInf_le]
/-
**le_iSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
参数：f : ι -> α；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s
-/
theorem le_iSup (f : ι → α) (i : ι) : f i ≤ iSup f :=
  le_sSup ⟨i, rfl⟩
/-
**iInf_le_iSup** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iInf_le_iSup [Nonempty ι] : ⨅ i, f i <= ⨆ i, f i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
-/
lemma iInf_le_iSup [Nonempty ι] : ⨅ i, f i ≤ ⨆ i, f i :=
  (iInf_le _ (Classical.arbitrary _)).trans <| le_iSup _ (Classical.arbitrary _)

@[to_dual]
/-
**isLUB_iSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLUB_iSup : IsLUB (range f) (⨆ j, f j)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isLUB_sSup`：isLUB_sSup (s : Set α) : IsLUB s (sSup s)
-/
theorem isLUB_iSup : IsLUB (range f) (⨆ j, f j) :=
  isLUB_sSup _

@[to_dual]
/-
**IsLUB.iSup_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLUB.iSup_eq (h : IsLUB (range f) a) : ⨆ j, f j = a
参数：h : IsLUB (range f) a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLUB.sSup_eq`：∀ {α : Type u_1} [inst : CompleteSemilatticeSup α] {s : S
et α} {a : α}, IsLUB s a → sSup s = a
-/
theorem IsLUB.iSup_eq (h : IsLUB (range f) a) : ⨆ j, f j = a :=
  h.sSup_eq

@[to_dual iInf_le_of_le]
/-
**le_iSup_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
参数：i : ι；h : a <= f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
-/
theorem le_iSup_of_le (i : ι) (h : a ≤ f i) : a ≤ iSup f :=
  h.trans <| le_iSup _ i

@[to_dual iInf₂_le]
/-
**le_iSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
参数：f : ι -> α；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s
-/
theorem le_iSup₂ {f : ∀ i, κ i → α} (i : ι) (j : κ i) : f i j ≤ ⨆ (i) (j), f i j :=
  le_iSup_of_le i <| le_iSup (f i) j

@[to_dual iInf₂_le_of_le]
/-
**le_iSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
参数：f : ι -> α；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s
-/
theorem le_iSup₂_of_le {f : ∀ i, κ i → α} (i : ι) (j : κ i) (h : a ≤ f i j) :
    a ≤ ⨆ (i) (j), f i j :=
  h.trans <| le_iSup₂ i j

@[to_dual le_iInf]
/-
**iSup_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_le (h : forall i, f i <= a) : iSup f <= a
参数：h : forall i, f i <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sSup_le`：sSup_le (h : forall b in s, b <= a) : sSup s <= a
-/
theorem iSup_le (h : ∀ i, f i ≤ a) : iSup f ≤ a :=
  sSup_le fun _ ⟨i, Eq⟩ => Eq ▸ h i

@[to_dual le_iInf₂]
/-
**iSup** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：iSup [SupSet α] (s : ι -> α) : α
参数：s : ι -> α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iSup₂_le {f : ∀ i, κ i → α} (h : ∀ i j, f i j ≤ a) : ⨆ (i) (j), f i j ≤ a :=
  iSup_le fun i => iSup_le <| h i

@[to_dual iInf_le_iInf₂]
/-
**iSup** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：iSup [SupSet α] (s : ι -> α) : α
参数：s : ι -> α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iSup₂_le_iSup (κ : ι → Sort*) (f : ι → α) : ⨆ (i) (_ : κ i), f i ≤ ⨆ i, f i :=
  iSup₂_le fun i _ => le_iSup f i

@[to_dual (attr := gcongr)]
/-
**iSup_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_mono (h : forall i, f i <= g i) : iSup f <= iSup g
参数：h : forall i, f i <= g i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
-/
theorem iSup_mono (h : ∀ i, f i ≤ g i) : iSup f ≤ iSup g :=
  iSup_le fun i => le_iSup_of_le i <| h i

@[to_dual]
/-
**iSup** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：iSup [SupSet α] (s : ι -> α) : α
参数：s : ι -> α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iSup₂_mono {f g : ∀ i, κ i → α} (h : ∀ i j, f i j ≤ g i j) :
    ⨆ (i) (j), f i j ≤ ⨆ (i) (j), g i j :=
  iSup_mono fun i => iSup_mono <| h i

@[to_dual]
/-
**iSup_mono'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_mono' {g : ι' -> α} (h : forall i, exists i', f i <= g i') : iSup f <
= iSup g
参数：h : forall i, exists i', f i <= g i'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
-/
theorem iSup_mono' {g : ι' → α} (h : ∀ i, ∃ i', f i ≤ g i') : iSup f ≤ iSup g :=
  iSup_le fun i => Exists.elim (h i) le_iSup_of_le

@[to_dual]
/-
**iSup** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：iSup [SupSet α] (s : ι -> α) : α
参数：s : ι -> α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iSup₂_mono' {f : ∀ i, κ i → α} {g : ∀ i', κ' i' → α} (h : ∀ i j, ∃ i' j', f i j ≤ g i' j') :
    ⨆ (i) (j), f i j ≤ ⨆ (i) (j), g i j :=
  iSup₂_le fun i j =>
    let ⟨i', j', h⟩ := h i j
    le_iSup₂_of_le i' j' h

@[to_dual]
/-
**iSup_const_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_const_mono (h : ι -> ι') : ⨆ _ : ι, a <= ⨆ _ : ι', a
参数：h : ι -> ι'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
-/
theorem iSup_const_mono (h : ι → ι') : ⨆ _ : ι, a ≤ ⨆ _ : ι', a :=
  iSup_le <| le_iSup _ ∘ h

@[to_dual none]
/-
**iSup_iInf_le_iInf_iSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_iInf_le_iInf_iSup (f : ι -> ι' -> α) : ⨆ i, ⨅ j, f i j <= ⨅ j, ⨆ i, f
 i j
参数：f : ι -> ι' -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `iInf_mono`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f
 g : ι → α}, (∀ (i : ι), g i ≤ f i) → iInf g ≤ iInf f
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
-/
theorem iSup_iInf_le_iInf_iSup (f : ι → ι' → α) : ⨆ i, ⨅ j, f i j ≤ ⨅ j, ⨆ i, f i j :=
  iSup_le fun i => iInf_mono fun j => le_iSup (fun i => f i j) i

@[to_dual]
/-
**biSup_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：biSup_mono {p q : ι -> Prop} (hpq : forall i, p i -> q i) : ⨆ (i) (_ : p i
), f i <= ⨆ (i) (_ : q i), f i
参数：hpq : forall i, p i -> q i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_mono`：iSup_mono (h : forall i, f i <= g i) : iSup f <= iSup g
· 使用定理 `iSup_const_mono`：iSup_const_mono (h : ι -> ι') : ⨆ _ : ι, a <= ⨆ _ : ι',
 a
-/
theorem biSup_mono {p q : ι → Prop} (hpq : ∀ i, p i → q i) :
    ⨆ (i) (_ : p i), f i ≤ ⨆ (i) (_ : q i), f i :=
  iSup_mono fun i => iSup_const_mono (hpq i)

@[to_dual (attr := simp) le_iInf_iff]
/-
**iSup_le_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_le_iff : iSup f <= a ↔ forall i, f i <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `isLUB_le_iff`：isLUB_le_iff (h : IsLUB s a) : a <= b ↔ b in upperBounds s
· 使用定理 `isLUB_iSup`：isLUB_iSup : IsLUB (range f) (⨆ j, f j)
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
-/
theorem iSup_le_iff : iSup f ≤ a ↔ ∀ i, f i ≤ a :=
  (isLUB_le_iff isLUB_iSup).trans forall_mem_range

@[to_dual le_iInf₂_iff]
/-
**iSup** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：iSup [SupSet α] (s : ι -> α) : α
参数：s : ι -> α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iSup₂_le_iff {f : ∀ i, κ i → α} : ⨆ (i) (j), f i j ≤ a ↔ ∀ i j, f i j ≤ a := by
  simp_rw [iSup_le_iff]

@[to_dual]
/-
**sSup_eq_iSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sSup_eq_iSup {s : Set α} : sSup s = ⨆ a in s, a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `sSup_le`：sSup_le (h : forall b in s, b <= a) : sSup s <= a
· 使用定理 `le_iSup₂`：le_iSup₂ {f : forall i, κ i -> α} (i : ι) (j : κ i) : f i j <=
 ⨆ (i) (j), f i j
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s
-/
theorem sSup_eq_iSup {s : Set α} : sSup s = ⨆ a ∈ s, a :=
  le_antisymm (sSup_le le_iSup₂) (iSup₂_le fun _ => le_sSup)

@[to_dual]
/-
**sSup_lowerBounds_eq_sInf** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sSup_lowerBounds_eq_sInf (s : Set α) : sSup (lowerBounds s) = sInf s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLUB.unique`：IsLUB.unique (Ha : IsLUB s a) (Hb : IsLUB s b) : a = b
· 使用定理 `isLUB_sSup`：isLUB_sSup (s : Set α) : IsLUB s (sSup s)
· 使用定理 `IsGreatest.isLUB`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α} {a : 
α}, IsGreatest s a → IsLUB s a
· 使用定理 `isGLB_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] (s : Set 
α), IsGLB s (sInf s)
-/
lemma sSup_lowerBounds_eq_sInf (s : Set α) : sSup (lowerBounds s) = sInf s :=
  (isLUB_sSup _).unique (isGLB_sInf _).isLUB

@[deprecated (since := "2026-02-01")] alias sInf_upperBounds_eq_csSup := sInf_upperBounds_eq_sSup

@[to_dual map_iInf_le]
/-
**Monotone.le_map_iSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.le_map_iSup [CompleteLattice β] {f : α -> β} (hf : Monotone f) : 
⨆ i, f (s i) <= f (iSup s)
参数：hf : Monotone f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
-/
theorem Monotone.le_map_iSup [CompleteLattice β] {f : α → β} (hf : Monotone f) :
    ⨆ i, f (s i) ≤ f (iSup s) :=
  iSup_le fun _ => hf <| le_iSup _ _

@[to_dual map_iSup_le]
/-
**Antitone.le_map_iInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.le_map_iInf [CompleteLattice β] {f : α -> β} (hf : Antitone f) : 
⨆ i, f (s i) <= f (iInf s)
参数：hf : Antitone f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.le_map_iSup`：Monotone.le_map_iSup [CompleteLattice β] {f : α ->
 β} (hf : Monotone f) : ⨆ i, f (s i) <= f (iSup s)
· 使用定理 `Antitone.dual_left`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [ins
t_1 : Preorder β] {f : α → β},   Antitone f → Monotone (f ∘ ⇑OrderDual.ofDual)
-/
theorem Antitone.le_map_iInf [CompleteLattice β] {f : α → β} (hf : Antitone f) :
    ⨆ i, f (s i) ≤ f (iInf s) :=
  hf.dual_left.le_map_iSup

@[to_dual map_iInf₂_le]
/-
**Monotone.le_map_iSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.le_map_iSup [CompleteLattice β] {f : α -> β} (hf : Monotone f) : 
⨆ i, f (s i) <= f (iSup s)
参数：hf : Monotone f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
-/
theorem Monotone.le_map_iSup₂ [CompleteLattice β] {f : α → β} (hf : Monotone f) (s : ∀ i, κ i → α) :
    ⨆ (i) (j), f (s i j) ≤ f (⨆ (i) (j), s i j) :=
  iSup₂_le fun _ _ => hf <| le_iSup₂ _ _

@[to_dual map_iSup₂_le]
/-
**Antitone.le_map_iInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.le_map_iInf [CompleteLattice β] {f : α -> β} (hf : Antitone f) : 
⨆ i, f (s i) <= f (iInf s)
参数：hf : Antitone f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.le_map_iSup`：Monotone.le_map_iSup [CompleteLattice β] {f : α ->
 β} (hf : Monotone f) : ⨆ i, f (s i) <= f (iSup s)
· 使用定理 `Antitone.dual_left`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [ins
t_1 : Preorder β] {f : α → β},   Antitone f → Monotone (f ∘ ⇑OrderDual.ofDual)
-/
theorem Antitone.le_map_iInf₂ [CompleteLattice β] {f : α → β} (hf : Antitone f) (s : ∀ i, κ i → α) :
    ⨆ (i) (j), f (s i j) ≤ f (⨅ (i) (j), s i j) :=
  hf.dual_left.le_map_iSup₂ _

@[to_dual map_sInf_le]
/-
**Monotone.le_map_sSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.le_map_sSup [CompleteLattice β] {s : Set α} {f : α -> β} (hf : Mo
notone f) : ⨆ a in s, f a <= f (sSup s)
参数：hf : Monotone f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sSup_eq_iSup`：sSup_eq_iSup {s : Set α} : sSup s = ⨆ a in s, a
· 使用定理 `Monotone.le_map_iSup₂`：Monotone.le_map_iSup₂ [CompleteLattice β] {f : α 
-> β} (hf : Monotone f) (s : forall i, κ i -> α) : ⨆ (i) (j), f (s i j) <= f (⨆ 
(i) (j), s …
-/
theorem Monotone.le_map_sSup [CompleteLattice β] {s : Set α} {f : α → β} (hf : Monotone f) :
    ⨆ a ∈ s, f a ≤ f (sSup s) := by rw [sSup_eq_iSup]; exact hf.le_map_iSup₂ _

@[to_dual map_sSup_le]
/-
**Antitone.le_map_sInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.le_map_sInf [CompleteLattice β] {s : Set α} {f : α -> β} (hf : An
titone f) : ⨆ a in s, f a <= f (sInf s)
参数：hf : Antitone f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.le_map_sSup`：Monotone.le_map_sSup [CompleteLattice β] {s : Set 
α} {f : α -> β} (hf : Monotone f) : ⨆ a in s, f a <= f (sSup s)
· 使用定理 `Antitone.dual_left`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [ins
t_1 : Preorder β] {f : α → β},   Antitone f → Monotone (f ∘ ⇑OrderDual.ofDual)
-/
theorem Antitone.le_map_sInf [CompleteLattice β] {s : Set α} {f : α → β} (hf : Antitone f) :
    ⨆ a ∈ s, f a ≤ f (sInf s) :=
  hf.dual_left.le_map_sSup

@[to_dual]
/-
**OrderIso.map_iSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OrderIso.map_iSup [CompleteLattice β] (f : α ≃o β) (x : ι -> α) : f (⨆ i, 
x i) = ⨆ i, f (x i)
参数：f : α ≃o β；x : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `OrderIso.surjective`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst
_1 : LE β] (e : α ≃o β), Function.Surjective ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderIso.le_iff_le`：le_iff_le (e : α ≃o β) {x y : α} : e x <= e y ↔ x <=
 y
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem OrderIso.map_iSup [CompleteLattice β] (f : α ≃o β) (x : ι → α) :
    f (⨆ i, x i) = ⨆ i, f (x i) :=
  eq_of_forall_ge_iff <| f.surjective.forall.2
  fun x => by simp only [f.le_iff_le, iSup_le_iff]

@[to_dual]
/-
**OrderIso.map_iSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OrderIso.map_iSup [CompleteLattice β] (f : α ≃o β) (x : ι -> α) : f (⨆ i, 
x i) = ⨆ i, f (x i)
参数：f : α ≃o β；x : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `OrderIso.surjective`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst
_1 : LE β] (e : α ≃o β), Function.Surjective ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderIso.le_iff_le`：le_iff_le (e : α ≃o β) {x y : α} : e x <= e y ↔ x <=
 y
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma OrderIso.map_iSup₂ [CompleteLattice β] (f : α ≃o β) (x : ∀ i, κ i → α) :
    f (⨆ i, ⨆ j, x i j) = ⨆ i, ⨆ j, f (x i j) :=
  eq_of_forall_ge_iff <| f.surjective.forall.2
  fun x => by simp only [f.le_iff_le, iSup_le_iff]

@[to_dual]
/-
**OrderIso.map_sSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OrderIso.map_sSup [CompleteLattice β] (f : α ≃o β) (s : Set α) : f (sSup s
) = ⨆ a in s, f a
参数：f : α ≃o β；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sSup_eq_iSup`：sSup_eq_iSup {s : Set α} : sSup s = ⨆ a in s, a
· 使用定理 `OrderIso.map_iSup`：OrderIso.map_iSup [CompleteLattice β] (f : α ≃o β) (x
 : ι -> α) : f (⨆ i, x i) = ⨆ i, f (x i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem OrderIso.map_sSup [CompleteLattice β] (f : α ≃o β) (s : Set α) :
    f (sSup s) = ⨆ a ∈ s, f a := by
  simp only [sSup_eq_iSup, OrderIso.map_iSup]

@[to_dual le_iInf_comp]
/-
**iSup_comp_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_comp_le {ι' : Sort*} (f : ι' -> α) (g : ι -> ι') : ⨆ x, f (g x) <= ⨆ 
y, f y
参数：f : ι' -> α；g : ι -> ι'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_mono'`：iSup_mono' {g : ι' -> α} (h : forall i, exists i', f i <= g 
i') : iSup f <= iSup g
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem iSup_comp_le {ι' : Sort*} (f : ι' → α) (g : ι → ι') : ⨆ x, f (g x) ≤ ⨆ y, f y :=
  iSup_mono' fun _ => ⟨_, le_rfl⟩

@[to_dual]
/-
**Monotone.iSup_comp_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.iSup_comp_eq [Preorder β] {f : β -> α} (hf : Monotone f) {s : ι -
> β} (hs : forall x, exists i, x <= s i) : ⨆ x, f (s x) = ⨆ y, f y
参数：hf : Monotone f；hs : forall x, exists i, x <= s i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iSup_comp_le`：iSup_comp_le {ι' : Sort*} (f : ι' -> α) (g : ι -> ι') : ⨆ 
x, f (g x) <= ⨆ y, f y
· 使用定理 `iSup_mono'`：iSup_mono' {g : ι' -> α} (h : forall i, exists i', f i <= g 
i') : iSup f <= iSup g
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
-/
theorem Monotone.iSup_comp_eq [Preorder β] {f : β → α} (hf : Monotone f) {s : ι → β}
    (hs : ∀ x, ∃ i, x ≤ s i) : ⨆ x, f (s x) = ⨆ y, f y :=
  le_antisymm (iSup_comp_le _ _) (iSup_mono' fun x => (hs x).imp fun _ hi => hf hi)

@[to_dual le_iInf_const]
/-
**iSup_const_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_const_le : ⨆ _ : ι, a <= a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem iSup_const_le : ⨆ _ : ι, a ≤ a :=
  iSup_le fun _ => le_rfl

-- We generalize this to conditionally complete lattices in `ciSup_const` and `ciInf_const`.
@[to_dual]
/-
**iSup_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_const [Nonempty ι] : ⨆ _ : ι, a = a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : SupSet α] (s : ι → α), iS
up s = sSup (Set.range s)
· 使用定理 `Set.range_const`：range_const : forall [Nonempty ι] {c : α}, (range fun _
 : ι => c) = {c}
· 使用定理 `sSup_singleton`：sSup_singleton {a : α} : sSup {a} = a
-/
theorem iSup_const [Nonempty ι] : ⨆ _ : ι, a = a := by rw [iSup, range_const, sSup_singleton]

@[to_dual]
/-
**iSup_unique** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iSup_unique [Unique ι] (f : ι -> α) : ⨆ i, f i = f default
参数：f : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Unique.eq_default`：eq_default (a : α) : a = default
· 使用定理 `iSup_const`：iSup_const [Nonempty ι] : ⨆ _ : ι, a = a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma iSup_unique [Unique ι] (f : ι → α) : ⨆ i, f i = f default := by
  simp only [congr_arg f (Unique.eq_default _), iSup_const]

@[to_dual (attr := simp)]
/-
**iSup_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_bot : (⨆ _ : ι, ⊥ : α) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_unique`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ → a = ⊥
· 使用定理 `iSup_const_le`：iSup_const_le : ⨆ _ : ι, a <= a
-/
theorem iSup_bot : (⨆ _ : ι, ⊥ : α) = ⊥ :=
  bot_unique iSup_const_le

@[to_dual (attr := simp)]
/-
**iSup_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_eq_bot : iSup s = ⊥ ↔ forall i, s i = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `sSup_eq_bot`：sSup_eq_bot : sSup s = ⊥ ↔ forall a in s, a = ⊥
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
-/
theorem iSup_eq_bot : iSup s = ⊥ ↔ ∀ i, s i = ⊥ :=
  sSup_eq_bot.trans forall_mem_range

@[to_dual (attr := simp) iInf_lt_top]
/-
**bot_lt_iSup** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：bot_lt_iSup : ⊥ < ⨆ i, s i ↔ exists i, ⊥ < s i
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma bot_lt_iSup : ⊥ < ⨆ i, s i ↔ ∃ i, ⊥ < s i := by simp [bot_lt_iff_ne_bot]

@[to_dual]
/-
**iSup** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：iSup [SupSet α] (s : ι -> α) : α
参数：s : ι -> α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iSup₂_eq_bot {f : ∀ i, κ i → α} : ⨆ (i) (j), f i j = ⊥ ↔ ∀ i j, f i j = ⊥ := by
  simp

@[to_dual (attr := simp)]
/-
**iSup_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_pos {p : Prop} {f : p -> α} (hp : p) : ⨆ h : p, f h = f hp
参数：hp : p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
-/
theorem iSup_pos {p : Prop} {f : p → α} (hp : p) : ⨆ h : p, f h = f hp :=
  le_antisymm (iSup_le fun _ => le_rfl) (le_iSup _ _)

@[to_dual (attr := simp)]
/-
**iSup_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_neg {p : Prop} {f : p -> α} (hp : ¬p) : ⨆ h : p, f h = ⊥
参数：hp : ¬p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
theorem iSup_neg {p : Prop} {f : p → α} (hp : ¬p) : ⨆ h : p, f h = ⊥ :=
  le_antisymm (iSup_le fun h => (hp h).elim) bot_le

/-- Introduction rule to prove that `b` is the supremum of `f`: it suffices to check that `b`
is larger than `f i` for all `i`, and that this is not the case of any `w<b`.
See `ciSup_eq_of_forall_le_of_forall_lt_exists_gt` for a version in conditionally complete
lattices. -/
@[to_dual iInf_eq_of_forall_ge_of_forall_gt_exists_lt
/-- Introduction rule to prove that `b` is the infimum of `f`: it suffices to check that `b`
is smaller than `f i` for all `i`, and that this is not the case of any `w>b`.
See `ciInf_eq_of_forall_ge_of_forall_gt_exists_lt` for a version in conditionally complete
lattices. -/]
/-
**iSup_eq_of_forall_le_of_forall_lt_exists_gt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_eq_of_forall_le_of_forall_lt_exists_gt {f : ι -> α} (h₁ : forall i, f
 i <= b) (h₂ : forall w, w < b -> exists i, w < f i) : ⨆ i : ι, f i = b
参数：h₁ : forall i, f i <= b；h₂ : forall w, w < b -> exists i, w < f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sSup_eq_of_forall_le_of_forall_lt_exists_gt`：sSup_eq_of_forall_le_of_for
all_lt_exists_gt (h₁ : forall a in s, a <= b) (h₂ : forall w, w < b -> exists a 
in s, w < a) : sSup s = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
· 使用定理 `Set.exists_range_iff`：exists_range_iff {p : α -> Prop} : (exists a in ra
nge f, p a) ↔ exists i, p (f i)
-/
theorem iSup_eq_of_forall_le_of_forall_lt_exists_gt {f : ι → α} (h₁ : ∀ i, f i ≤ b)
    (h₂ : ∀ w, w < b → ∃ i, w < f i) : ⨆ i : ι, f i = b :=
  sSup_eq_of_forall_le_of_forall_lt_exists_gt (forall_mem_range.mpr h₁) fun w hw =>
    exists_range_iff.mpr <| h₂ w hw

@[to_dual]
/-
**iSup_eq_dif** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_eq_dif {p : Prop} [Decidable p] (a : p -> α) : ⨆ h : p, a h = if h : 
p then a h else ⊥
参数：a : p -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `iSup_pos`：iSup_pos {p : Prop} {f : p -> α} (hp : p) : ⨆ h : p, f h = f h
p
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `iSup_neg`：iSup_neg {p : Prop} {f : p -> α} (hp : ¬p) : ⨆ h : p, f h = ⊥
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
-/
theorem iSup_eq_dif {p : Prop} [Decidable p] (a : p → α) :
    ⨆ h : p, a h = if h : p then a h else ⊥ := by by_cases h : p <;> simp [h]

@[to_dual]
/-
**iSup_eq_if** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_eq_if {p : Prop} [Decidable p] (a : α) : ⨆ _ : p, a = if p then a els
e ⊥
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_eq_dif`：iSup_eq_dif {p : Prop} [Decidable p] (a : p -> α) : ⨆ h : p
, a h = if h : p then a h else ⊥
-/
theorem iSup_eq_if {p : Prop} [Decidable p] (a : α) : ⨆ _ : p, a = if p then a else ⊥ :=
  iSup_eq_dif fun _ => a

@[to_dual]
/-
**iSup_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_comm {f : ι -> ι' -> α} : ⨆ (i) (j), f i j = ⨆ (j) (i), f i j
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `iSup_mono`：iSup_mono (h : forall i, f i <= g i) : iSup f <= iSup g
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
-/
theorem iSup_comm {f : ι → ι' → α} : ⨆ (i) (j), f i j = ⨆ (j) (i), f i j :=
  le_antisymm (iSup_le fun i => iSup_mono fun j => le_iSup (fun i => f i j) i)
    (iSup_le fun _ => iSup_mono fun _ => le_iSup _ _)

@[to_dual]
/-
**iSup** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：iSup [SupSet α] (s : ι -> α) : α
参数：s : ι -> α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iSup₂_comm {ι₁ ι₂ : Sort*} {κ₁ : ι₁ → Sort*} {κ₂ : ι₂ → Sort*}
    (f : ∀ i₁, κ₁ i₁ → ∀ i₂, κ₂ i₂ → α) :
    ⨆ (i₁) (j₁) (i₂) (j₂), f i₁ j₁ i₂ j₂ = ⨆ (i₂) (j₂) (i₁) (j₁), f i₁ j₁ i₂ j₂ := by
  simp only [@iSup_comm _ (κ₁ _), @iSup_comm _ ι₁]

@[to_dual (attr := simp)]
/-
**iSup_iSup_eq_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_iSup_eq_left {b : β} {f : forall x : β, x = b -> α} : ⨆ x, ⨆ h : x = 
b, f x h = f b rfl
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `le_iSup₂`：le_iSup₂ {f : forall i, κ i -> α} (i : ι) (j : κ i) : f i j <=
 ⨆ (i) (j), f i j
-/
theorem iSup_iSup_eq_left {b : β} {f : ∀ x : β, x = b → α} : ⨆ x, ⨆ h : x = b, f x h = f b rfl :=
  le_antisymm (iSup₂_le fun _ h ↦ h ▸ le_rfl) (le_iSup₂ (f := f) b rfl)

@[to_dual (attr := simp)]
/-
**iSup_iSup_eq_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_iSup_eq_right {b : β} {f : forall x : β, b = x -> α} : ⨆ x, ⨆ h : b =
 x, f x h = f b rfl
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `le_iSup₂`：le_iSup₂ {f : forall i, κ i -> α} (i : ι) (j : κ i) : f i j <=
 ⨆ (i) (j), f i j
-/
theorem iSup_iSup_eq_right {b : β} {f : ∀ x : β, b = x → α} : ⨆ x, ⨆ h : b = x, f x h = f b rfl :=
  le_antisymm (iSup₂_le fun _ h ↦ h ▸ le_refl (f b rfl)) (le_iSup₂ b rfl)

@[to_dual]
/-
**iSup_subtype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_subtype {p : ι -> Prop} {f : Subtype p -> α} : iSup f = ⨆ (i) (h : p 
i), f ⟨i, h⟩
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `le_iSup₂`：le_iSup₂ {f : forall i, κ i -> α} (i : ι) (j : κ i) : f i j <=
 ⨆ (i) (j), f i j
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
-/
theorem iSup_subtype {p : ι → Prop} {f : Subtype p → α} : iSup f = ⨆ (i) (h : p i), f ⟨i, h⟩ :=
  le_antisymm (iSup_le fun ⟨i, h⟩ => @le_iSup₂ _ _ p _ (fun i h => f ⟨i, h⟩) i h)
    (iSup₂_le fun _ _ => le_iSup _ _)

@[to_dual]
/-
**iSup_subtype'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_subtype' {p : ι -> Prop} {f : forall i, p i -> α} : ⨆ (i) (h), f i h 
= ⨆ x : Subtype p, f x x.property
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `iSup_subtype`：iSup_subtype {p : ι -> Prop} {f : Subtype p -> α} : iSup f
 = ⨆ (i) (h : p i), f ⟨i, h⟩
-/
theorem iSup_subtype' {p : ι → Prop} {f : ∀ i, p i → α} :
    ⨆ (i) (h), f i h = ⨆ x : Subtype p, f x x.property :=
  (@iSup_subtype _ _ _ p fun x => f x.val x.property).symm

@[to_dual]
/-
**iSup_subtype''** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_subtype'' {ι} (s : Set ι) (f : ι -> α) : ⨆ i : s, f i = ⨆ (t : ι) (_ 
: t in s), f t
参数：s : Set ι；f : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_subtype`：iSup_subtype {p : ι -> Prop} {f : Subtype p -> α} : iSup f
 = ⨆ (i) (h : p i), f ⟨i, h⟩
-/
theorem iSup_subtype'' {ι} (s : Set ι) (f : ι → α) : ⨆ i : s, f i = ⨆ (t : ι) (_ : t ∈ s), f t :=
  iSup_subtype

@[to_dual]
/-
**biSup_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：biSup_const {a : α} {s : Set β} (hs : s.Nonempty) : ⨆ i in s, a = a
参数：hs : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.nonempty_coe_sort`：nonempty_coe_sort {s : Set α} : Nonempty ↥s ↔ s.N
onempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iSup_subtype''`：iSup_subtype'' {ι} (s : Set ι) (f : ι -> α) : ⨆ i : s, f
 i = ⨆ (t : ι) (_ : t in s), f t
· 使用定理 `iSup_const`：iSup_const [Nonempty ι] : ⨆ _ : ι, a = a
-/
theorem biSup_const {a : α} {s : Set β} (hs : s.Nonempty) : ⨆ i ∈ s, a = a := by
  have : Nonempty s := Set.nonempty_coe_sort.mpr hs
  rw [← iSup_subtype'', iSup_const]

@[to_dual]
/-
**iSup_sup_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_sup_eq : ⨆ x, f x ⊔ g x = (⨆ x, f x) ⊔ ⨆ x, g x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `sup_le_sup`：sup_le_sup (h₁ : a <= b) (h₂ : c <= d) : a ⊔ c <= b ⊔ d
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `iSup_mono`：iSup_mono (h : forall i, f i <= g i) : iSup f <= iSup g
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
theorem iSup_sup_eq : ⨆ x, f x ⊔ g x = (⨆ x, f x) ⊔ ⨆ x, g x :=
  le_antisymm (iSup_le fun _ => sup_le_sup (le_iSup _ _) <| le_iSup _ _)
    (sup_le (iSup_mono fun _ => le_sup_left) <| iSup_mono fun _ => le_sup_right)

@[to_dual]
/-
**Equiv.biSup_comp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Equiv.biSup_comp {ι ι' : Type*} {g : ι' -> α} (e : ι ≃ ι') (s : Set ι') : 
⨆ i in e.symm '' s, g (e i) = ⨆ i in s, g i
参数：e : ι ≃ ι'；s : Set ι'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_subtype'`：iSup_subtype' {p : ι -> Prop} {f : forall i, p i -> α} : 
⨆ (i) (h), f i h = ⨆ x : Subtype p, f x x.property
· 使用定理 `Equiv.iSup_comp`：Equiv.iSup_comp {g : ι' -> α} (e : ι ≃ ι') : ⨆ x, g (e 
x) = ⨆ y, g y
-/
lemma Equiv.biSup_comp {ι ι' : Type*} {g : ι' → α} (e : ι ≃ ι') (s : Set ι') :
    ⨆ i ∈ e.symm '' s, g (e i) = ⨆ i ∈ s, g i := by
  simpa only [iSup_subtype'] using! (image e.symm s).symm.iSup_comp (g := g ∘ (↑))

@[to_dual biInf_le]
/-
**le_biSup** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_biSup {ι : Type*} {s : Set ι} (f : ι -> α) {i : ι} (hi : i in s) : f i 
<= ⨆ i in s, f i
参数：f : ι -> α；hi : i in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iSup₂_of_le`：le_iSup₂_of_le {f : forall i, κ i -> α} (i : ι) (j : κ i
) (h : a <= f i j) : a <= ⨆ (i) (j), f i j
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma le_biSup {ι : Type*} {s : Set ι} (f : ι → α) {i : ι} (hi : i ∈ s) : f i ≤ ⨆ i ∈ s, f i :=
  le_iSup₂_of_le i hi le_rfl
/-
**biInf_le_biSup** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：biInf_le_biSup {ι : Type*} {s : Set ι} (hs : s.Nonempty) {f : ι -> α} : ⨅ 
i in s, f i <= ⨆ i in s, f i
参数：hs : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `biInf_le`：∀ {α : Type u_1} [inst : CompleteLattice α] {ι : Type u_8} {s 
: Set ι} (f : ι → α) {i : ι}, i ∈ s → ⨅ i ∈ s, f i ≤ f i
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用引理 `le_biSup`：le_biSup {ι : Type*} {s : Set ι} (f : ι -> α) {i : ι} (hi : i 
in s) : f i <= ⨆ i in s, f i
-/
lemma biInf_le_biSup {ι : Type*} {s : Set ι} (hs : s.Nonempty) {f : ι → α} :
    ⨅ i ∈ s, f i ≤ ⨆ i ∈ s, f i :=
  (biInf_le _ hs.choose_spec).trans <| le_biSup _ hs.choose_spec

@[to_dual]
/-
**iSup_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_sup [Nonempty ι] {f : ι -> α} {a : α} : (⨆ x, f x) ⊔ a = ⨆ x, f x ⊔ a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_sup_eq`：iSup_sup_eq : ⨆ x, f x ⊔ g x = (⨆ x, f x) ⊔ ⨆ x, g x
· 使用定理 `iSup_const`：iSup_const [Nonempty ι] : ⨆ _ : ι, a = a
-/
theorem iSup_sup [Nonempty ι] {f : ι → α} {a : α} : (⨆ x, f x) ⊔ a = ⨆ x, f x ⊔ a := by
  rw [iSup_sup_eq, iSup_const]

@[to_dual]
/-
**sup_iSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_iSup [Nonempty ι] {f : ι -> α} {a : α} : (a ⊔ ⨆ x, f x) = ⨆ x, a ⊔ f x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_sup_eq`：iSup_sup_eq : ⨆ x, f x ⊔ g x = (⨆ x, f x) ⊔ ⨆ x, g x
· 使用定理 `iSup_const`：iSup_const [Nonempty ι] : ⨆ _ : ι, a = a
-/
theorem sup_iSup [Nonempty ι] {f : ι → α} {a : α} : (a ⊔ ⨆ x, f x) = ⨆ x, a ⊔ f x := by
  rw [iSup_sup_eq, iSup_const]

@[to_dual]
/-
**biSup_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：biSup_sup {p : ι -> Prop} {f : forall i, p i -> α} {a : α} (h : exists i, 
p i) : (⨆ (i) (h : p i), f i h) ⊔ a = ⨆ (i) (h : p i), f i h ⊔ a
参数：h : exists i, p i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_subtype'`：iSup_subtype' {p : ι -> Prop} {f : forall i, p i -> α} : 
⨆ (i) (h), f i h = ⨆ x : Subtype p, f x x.property
· 使用定理 `iSup_sup`：iSup_sup [Nonempty ι] {f : ι -> α} {a : α} : (⨆ x, f x) ⊔ a = 
⨆ x, f x ⊔ a
-/
theorem biSup_sup {p : ι → Prop} {f : ∀ i, p i → α} {a : α} (h : ∃ i, p i) :
    (⨆ (i) (h : p i), f i h) ⊔ a = ⨆ (i) (h : p i), f i h ⊔ a := by
  have : Nonempty { i // p i } :=
    let ⟨i, hi⟩ := h
    ⟨⟨i, hi⟩⟩
  rw [iSup_subtype', iSup_subtype', iSup_sup]

@[to_dual]
/-
**sup_biSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_biSup {p : ι -> Prop} {f : forall i, p i -> α} {a : α} (h : exists i, 
p i) : (a ⊔ ⨆ (i) (h : p i), f i h) = ⨆ (i) (h : p i), a ⊔ f i h
参数：h : exists i, p i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `biSup_sup`：biSup_sup {p : ι -> Prop} {f : forall i, p i -> α} {a : α} (h
 : exists i, p i) : (⨆ (i) (h : p i), f i h) ⊔ a = ⨆ (i) (h : p i), f i h ⊔ a
-/
theorem sup_biSup {p : ι → Prop} {f : ∀ i, p i → α} {a : α} (h : ∃ i, p i) :
    (a ⊔ ⨆ (i) (h : p i), f i h) = ⨆ (i) (h : p i), a ⊔ f i h := by
  simpa only [sup_comm] using @biSup_sup α _ _ p _ _ h

@[to_dual (dont_translate := ι)]
/-
**biSup_lt_eq_iSup** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：biSup_lt_eq_iSup {ι : Type*} [LT ι] [NoMaxOrder ι] {f : ι -> α} : ⨆ (i) (j
 < i), f j = ⨆ i, f i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `NoMaxOrder.exists_gt`：∀ {α : Type u_3} {inst : LT α} [self : NoMaxOrder 
α] (a : α), ∃ b, a < b
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
· 使用定理 `le_iSup₂_of_le`：le_iSup₂_of_le {f : forall i, κ i -> α} (i : ι) (j : κ i
) (h : a <= f i j) : a <= ⨆ (i) (j), f i j
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma biSup_lt_eq_iSup {ι : Type*} [LT ι] [NoMaxOrder ι] {f : ι → α} :
    ⨆ (i) (j < i), f j = ⨆ i, f i := by
  apply le_antisymm
  · exact iSup_le fun _ ↦ iSup₂_le fun _ _ ↦ le_iSup _ _
  · refine iSup_le fun j ↦ ?_
    obtain ⟨i, jlt⟩ := exists_gt j
    exact le_iSup_of_le i (le_iSup₂_of_le j jlt le_rfl)

@[to_dual (dont_translate := ι)]
/-
**biSup_le_eq_iSup** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：biSup_le_eq_iSup {ι : Type*} [Preorder ι] {f : ι -> α} : ⨆ (i) (j <= i), f
 j = ⨆ i, f i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
· 使用定理 `le_iSup₂_of_le`：le_iSup₂_of_le {f : forall i, κ i -> α} (i : ι) (j : κ i
) (h : a <= f i j) : a <= ⨆ (i) (j), f i j
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma biSup_le_eq_iSup {ι : Type*} [Preorder ι] {f : ι → α} :
    ⨆ (i) (j ≤ i), f j = ⨆ i, f i := by
  apply le_antisymm
  · exact iSup_le fun _ ↦ iSup₂_le fun _ _ ↦ le_iSup _ _
  · exact iSup_le fun j ↦ le_iSup_of_le j (le_iSup₂_of_le j le_rfl le_rfl)

@[to_dual (dont_translate := ι)]
/-
**biSup_gt_eq_iSup** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：biSup_gt_eq_iSup {ι : Type*} [LT ι] [NoMinOrder ι] {f : ι -> α} : ⨆ (i) (j
 > i), f j = ⨆ i, f i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `NoMinOrder.exists_lt`：∀ {α : Type u_3} {inst : LT α} [self : NoMinOrder 
α] (a : α), ∃ b, b < a
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
· 使用定理 `le_iSup₂_of_le`：le_iSup₂_of_le {f : forall i, κ i -> α} (i : ι) (j : κ i
) (h : a <= f i j) : a <= ⨆ (i) (j), f i j
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma biSup_gt_eq_iSup {ι : Type*} [LT ι] [NoMinOrder ι] {f : ι → α} :
    ⨆ (i) (j > i), f j = ⨆ i, f i := by
  apply le_antisymm
  · exact iSup_le fun _ ↦ iSup₂_le fun _ _ ↦ le_iSup _ _
  · refine iSup_le fun j ↦ ?_
    obtain ⟨i, jlt⟩ := exists_lt j
    exact le_iSup_of_le i (le_iSup₂_of_le j jlt le_rfl)

@[to_dual (dont_translate := ι)]
/-
**biSup_ge_eq_iSup** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：biSup_ge_eq_iSup {ι : Type*} [Preorder ι] {f : ι -> α} : ⨆ (i) (j >= i), f
 j = ⨆ i, f i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
· 使用定理 `le_iSup₂_of_le`：le_iSup₂_of_le {f : forall i, κ i -> α} (i : ι) (j : κ i
) (h : a <= f i j) : a <= ⨆ (i) (j), f i j
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma biSup_ge_eq_iSup {ι : Type*} [Preorder ι] {f : ι → α} : ⨆ (i) (j ≥ i), f j = ⨆ i, f i := by
  apply le_antisymm
  · exact iSup_le fun _ ↦ iSup₂_le fun _ _ ↦ le_iSup _ _
  · exact iSup_le fun j ↦ le_iSup_of_le j (le_iSup₂_of_le j le_rfl le_rfl)

@[to_dual biInf_ge_eq_of_monotone]
/-
**biSup_le_eq_of_monotone** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：biSup_le_eq_of_monotone [Preorder β] {f : β -> α} (hf : Monotone f) (b : β
) : ⨆ (b' <= b), f b' = f b
参数：hf : Monotone f；b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `iSup₂_le_iff`：iSup₂_le_iff {f : forall i, κ i -> α} : ⨆ (i) (j), f i j <
= a ↔ forall i j, f i j <= a
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
· 使用定理 `ge_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `iSup_pos`：iSup_pos {p : Prop} {f : p -> α} (hp : p) : ⨆ h : p, f h = f h
p
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma biSup_le_eq_of_monotone [Preorder β] {f : β → α} (hf : Monotone f) (b : β) :
    ⨆ (b' ≤ b), f b' = f b :=
  le_antisymm (iSup₂_le_iff.2 (fun _ hji ↦ hf hji))
    (le_iSup_of_le b (ge_of_eq (iSup_pos le_rfl)))

@[to_dual biSup_ge_eq_of_antitone]
/-
**biInf_le_eq_of_antitone** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：biInf_le_eq_of_antitone [Preorder β] {f : β -> α} (hf : Antitone f) (b : β
) : ⨅ (b' <= b), f b' = f b
参数：hf : Antitone f；b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iInf₂_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst
 : CompleteLattice α] {a : α} {f : (i : ι) → κ i → α} (i : ι)   (j : κ i), f i j
 ≤ a…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `le_iInf₂`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {a : α} {f : (i : ι) → κ i → α},   (∀ (i : ι) (j : κ i), a ≤ f…
-/
lemma biInf_le_eq_of_antitone [Preorder β] {f : β → α} (hf : Antitone f) (b : β) :
    ⨅ (b' ≤ b), f b' = f b :=
  le_antisymm (iInf₂_le_of_le b le_rfl le_rfl)
    (le_iInf₂ fun _ hji ↦ hf hji)

/-! ### `iSup` and `iInf` under `Prop` -/

@[to_dual]
/-
**iSup_false** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_false {s : False -> α} : iSup s = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_neg`：iSup_neg {p : Prop} {f : p -> α} (hp : ¬p) : ⨆ h : p, f h = ⊥
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
### `iSup` and `iInf` under `Prop`
-/
theorem iSup_false {s : False → α} : iSup s = ⊥ := by simp

@[to_dual]
/-
**iSup_true** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_true {s : True -> α} : iSup s = s trivial
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_pos`：iSup_pos {p : Prop} {f : p -> α} (hp : p) : ⨆ h : p, f h = f h
p
· 使用定理 `trivial`：True
-/
theorem iSup_true {s : True → α} : iSup s = s trivial :=
  iSup_pos trivial

@[to_dual (attr := simp)]
/-
**iSup_exists** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_exists {p : ι -> Prop} {f : Exists p -> α} : ⨆ x, f x = ⨆ (i) (h), f 
⟨i, h⟩
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `le_iSup₂`：le_iSup₂ {f : forall i, κ i -> α} (i : ι) (j : κ i) : f i j <=
 ⨆ (i) (j), f i j
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
-/
theorem iSup_exists {p : ι → Prop} {f : Exists p → α} : ⨆ x, f x = ⨆ (i) (h), f ⟨i, h⟩ :=
  le_antisymm (iSup_le fun ⟨i, h⟩ => @le_iSup₂ _ _ _ _ (fun _ _ => _) i h)
    (iSup₂_le fun _ _ => le_iSup _ _)

@[to_dual]
/-
**iSup_and** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_and {p q : Prop} {s : p ∧ q -> α} : iSup s = ⨆ (h₁) (h₂), s ⟨h₁, h₂⟩
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `le_iSup₂`：le_iSup₂ {f : forall i, κ i -> α} (i : ι) (j : κ i) : f i j <=
 ⨆ (i) (j), f i j
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
-/
theorem iSup_and {p q : Prop} {s : p ∧ q → α} : iSup s = ⨆ (h₁) (h₂), s ⟨h₁, h₂⟩ :=
  le_antisymm (iSup_le fun ⟨i, h⟩ => @le_iSup₂ _ _ _ _ (fun _ _ => _) i h)
    (iSup₂_le fun _ _ => le_iSup _ _)

/-- The symmetric case of `iSup_and`, useful for rewriting into a supremum over a conjunction -/
@[to_dual /-- The symmetric case of `iInf_and`,
useful for rewriting into an infimum over a conjunction. -/]
/-
**iSup_and'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_and' {p q : Prop} {s : p -> q -> α} : ⨆ (h₁ : p) (h₂ : q), s h₁ h₂ = 
⨆ h : p ∧ q, s h.1 h.2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `iSup_and`：iSup_and {p q : Prop} {s : p ∧ q -> α} : iSup s = ⨆ (h₁) (h₂),
 s ⟨h₁, h₂⟩
-/
theorem iSup_and' {p q : Prop} {s : p → q → α} :
    ⨆ (h₁ : p) (h₂ : q), s h₁ h₂ = ⨆ h : p ∧ q, s h.1 h.2 :=
  Eq.symm iSup_and

@[to_dual]
/-
**iSup_or** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_or {p q : Prop} {s : p ∨ q -> α} : ⨆ x, s x = (⨆ i, s (Or.inl i)) ⊔ ⨆
 j, s (Or.inr j)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `le_sup_of_le_left`：le_sup_of_le_left (h : c <= a) : c <= a ⊔ b
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `le_sup_of_le_right`：le_sup_of_le_right (h : c <= b) : c <= a ⊔ b
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `iSup_comp_le`：iSup_comp_le {ι' : Sort*} (f : ι' -> α) (g : ι -> ι') : ⨆ 
x, f (g x) <= ⨆ y, f y
-/
theorem iSup_or {p q : Prop} {s : p ∨ q → α} :
    ⨆ x, s x = (⨆ i, s (Or.inl i)) ⊔ ⨆ j, s (Or.inr j) :=
  le_antisymm
    (iSup_le fun i =>
      match i with
      | Or.inl _ => le_sup_of_le_left <| le_iSup (fun _ => s _) _
      | Or.inr _ => le_sup_of_le_right <| le_iSup (fun _ => s _) _)
    (sup_le (iSup_comp_le _ _) (iSup_comp_le _ _))

section

variable (p : ι → Prop) [DecidablePred p]

@[to_dual]
/-
**iSup_dite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_dite (f : forall i, p i -> α) (g : forall i, ¬p i -> α) : ⨆ i, (if h 
: p i then f i h else g i h) = (⨆ (i) (h : p i), f i h) ⊔ ⨆ (i) (h : ¬p i), g i 
h
参数：f : forall i, p i -> α；g : forall i, ¬p i -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iSup_sup_eq`：iSup_sup_eq : ⨆ x, f x ⊔ g x = (⨆ x, f x) ⊔ ⨆ x, g x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `iSup_pos`：iSup_pos {p : Prop} {f : p -> α} (hp : p) : ⨆ h : p, f h = f h
p
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `iSup_neg`：iSup_neg {p : Prop} {f : p -> α} (hp : ¬p) : ⨆ h : p, f h = ⊥
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
-/
theorem iSup_dite (f : ∀ i, p i → α) (g : ∀ i, ¬p i → α) :
    ⨆ i, (if h : p i then f i h else g i h) = (⨆ (i) (h : p i), f i h) ⊔ ⨆ (i) (h : ¬p i),
    g i h := by
  rw [← iSup_sup_eq]
  congr 1 with i
  split_ifs with h <;> simp [h]

@[to_dual]
/-
**iSup_ite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_ite (f g : ι -> α) : ⨆ i, (if p i then f i else g i) = (⨆ (i) (_ : p 
i), f i) ⊔ ⨆ (i) (_ : ¬p i), g i
参数：f g : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_dite`：iSup_dite (f : forall i, p i -> α) (g : forall i, ¬p i -> α) 
: ⨆ i, (if h : p i then f i h else g i h) = (⨆ (i) (h : p i), f i h) ⊔ ⨆ (i) (h…
-/
theorem iSup_ite (f g : ι → α) :
    ⨆ i, (if p i then f i else g i) = (⨆ (i) (_ : p i), f i) ⊔ ⨆ (i) (_ : ¬p i), g i :=
  iSup_dite _ _ _

end

@[to_dual]
/-
**iSup_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_range {g : β -> α} {f : ι -> β} : ⨆ b in range f, g b = ⨆ i, g (f i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iSup_subtype''`：iSup_subtype'' {ι} (s : Set ι) (f : ι -> α) : ⨆ i : s, f
 i = ⨆ (t : ι) (_ : t in s), f t
· 使用定理 `iSup_range'`：iSup_range' (g : β -> α) (f : ι -> β) : ⨆ b : range f, g b 
= ⨆ i, g (f i)
-/
theorem iSup_range {g : β → α} {f : ι → β} : ⨆ b ∈ range f, g b = ⨆ i, g (f i) := by
  rw [← iSup_subtype'', iSup_range']

@[to_dual]
/-
**sSup_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sSup_image {s : Set β} {f : β -> α} : sSup (f '' s) = ⨆ a in s, f a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iSup_subtype''`：iSup_subtype'' {ι} (s : Set ι) (f : ι -> α) : ⨆ i : s, f
 i = ⨆ (t : ι) (_ : t in s), f t
· 使用定理 `sSup_image'`：sSup_image' {s : Set β} {f : β -> α} : sSup (f '' s) = ⨆ a 
: s, f a
-/
theorem sSup_image {s : Set β} {f : β → α} : sSup (f '' s) = ⨆ a ∈ s, f a := by
  rw [← iSup_subtype'', sSup_image']

@[to_dual]
/-
**OrderIso.map_sSup_eq_sSup_symm_preimage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OrderIso.map_sSup_eq_sSup_symm_preimage [CompleteLattice β] (f : α ≃o β) (
s : Set α) : f (sSup s) = sSup (f.symm ⁻¹' s)
参数：f : α ≃o β；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderIso.map_sSup`：OrderIso.map_sSup [CompleteLattice β] (f : α ≃o β) (s
 : Set α) : f (sSup s) = ⨆ a in s, f a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sSup_image`：sSup_image {s : Set β} {f : β -> α} : sSup (f '' s) = ⨆ a in
 s, f a
· 使用定理 `OrderIso.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃o β) (s 
: Set α) : e '' s = e.symm ⁻¹' s
-/
theorem OrderIso.map_sSup_eq_sSup_symm_preimage [CompleteLattice β] (f : α ≃o β) (s : Set α) :
    f (sSup s) = sSup (f.symm ⁻¹' s) := by
  rw [map_sSup, ← sSup_image, f.image_eq_preimage_symm]

/-
### iSup and iInf under set constructions
-/

@[to_dual]
/-
**iSup_emptyset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_emptyset {f : β -> α} : ⨆ x in (∅ : Set β), f x = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iSup_neg`：iSup_neg {p : Prop} {f : p -> α} (hp : ¬p) : ⨆ h : p, f h = ⊥
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iSup_bot`：iSup_bot : (⨆ _ : ι, ⊥ : α) = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
### iSup and iInf under set constructions
-/
theorem iSup_emptyset {f : β → α} : ⨆ x ∈ (∅ : Set β), f x = ⊥ := by simp

@[to_dual]
/-
**iSup_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_univ {f : β -> α} : ⨆ x in (univ : Set β), f x = ⨆ x, f x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iSup_pos`：iSup_pos {p : Prop} {f : p -> α} (hp : p) : ⨆ h : p, f h = f h
p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iSup_univ {f : β → α} : ⨆ x ∈ (univ : Set β), f x = ⨆ x, f x := by simp

@[to_dual]
/-
**iSup_union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_union {f : β -> α} {s t : Set β} : ⨆ x in s union t, f x = (⨆ x in s,
 f x) ⊔ ⨆ x in t, f x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iSup_or`：iSup_or {p q : Prop} {s : p ∨ q -> α} : ⨆ x, s x = (⨆ i, s (Or.
inl i)) ⊔ ⨆ j, s (Or.inr j)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iSup_sup_eq`：iSup_sup_eq : ⨆ x, f x ⊔ g x = (⨆ x, f x) ⊔ ⨆ x, g x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iSup_union {f : β → α} {s t : Set β} :
    ⨆ x ∈ s ∪ t, f x = (⨆ x ∈ s, f x) ⊔ ⨆ x ∈ t, f x := by
  simp_rw [mem_union, iSup_or, iSup_sup_eq]

@[to_dual]
/-
**iSup_split** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_split (f : β -> α) (p : β -> Prop) : ⨆ i, f i = (⨆ (i) (_ : p i), f i
) ⊔ ⨆ (i) (_ : ¬p i), f i
参数：f : β -> α；p : β -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iSup_pos`：iSup_pos {p : Prop} {f : p -> α} (hp : p) : ⨆ h : p, f h = f h
p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iSup_union`：iSup_union {f : β -> α} {s t : Set β} : ⨆ x in s union t, f 
x = (⨆ x in s, f x) ⊔ ⨆ x in t, f x
-/
theorem iSup_split (f : β → α) (p : β → Prop) :
    ⨆ i, f i = (⨆ (i) (_ : p i), f i) ⊔ ⨆ (i) (_ : ¬p i), f i := by
  simpa [Classical.em] using @iSup_union _ _ _ f { i | p i } { i | ¬p i }

@[to_dual]
/-
**iSup_split_single** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_split_single (f : β -> α) (i₀ : β) : ⨆ i, f i = f i₀ ⊔ ⨆ (i) (_ : i !
= i₀), f i
参数：f : β -> α；i₀ : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_iSup_eq_left`：iSup_iSup_eq_left {b : β} {f : forall x : β, x = b ->
 α} : ⨆ x, ⨆ h : x = b, f x h = f b rfl
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iSup_split`：iSup_split (f : β -> α) (p : β -> Prop) : ⨆ i, f i = (⨆ (i) 
(_ : p i), f i) ⊔ ⨆ (i) (_ : ¬p i), f i
-/
theorem iSup_split_single (f : β → α) (i₀ : β) : ⨆ i, f i = f i₀ ⊔ ⨆ (i) (_ : i ≠ i₀), f i := by
  convert! iSup_split f (fun i => i = i₀)
  simp

@[to_dual]
/-
**iSup_le_iSup_of_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_le_iSup_of_subset {f : β -> α} {s t : Set β} : s subseteq t -> ⨆ x in
 s, f x <= ⨆ x in t, f x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `biSup_mono`：biSup_mono {p q : ι -> Prop} (hpq : forall i, p i -> q i) : 
⨆ (i) (_ : p i), f i <= ⨆ (i) (_ : q i), f i
-/
theorem iSup_le_iSup_of_subset {f : β → α} {s t : Set β} : s ⊆ t → ⨆ x ∈ s, f x ≤ ⨆ x ∈ t, f x :=
  biSup_mono

@[to_dual]
/-
**iSup_insert** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_insert {f : β -> α} {s : Set β} {b : β} : ⨆ x in insert b s, f x = f 
b ⊔ ⨆ x in s, f x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iSup_or`：iSup_or {p q : Prop} {s : p ∨ q -> α} : ⨆ x, s x = (⨆ i, s (Or.
inl i)) ⊔ ⨆ j, s (Or.inr j)
· 使用定理 `iSup_sup_eq`：iSup_sup_eq : ⨆ x, f x ⊔ g x = (⨆ x, f x) ⊔ ⨆ x, g x
· 使用定理 `iSup_iSup_eq_left`：iSup_iSup_eq_left {b : β} {f : forall x : β, x = b ->
 α} : ⨆ x, ⨆ h : x = b, f x h = f b rfl
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iSup_insert {f : β → α} {s : Set β} {b : β} :
    ⨆ x ∈ insert b s, f x = f b ⊔ ⨆ x ∈ s, f x := by
  simp [iSup_or, iSup_sup_eq]

@[to_dual]
/-
**iSup_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_singleton {f : β -> α} {b : β} : ⨆ x in (singleton b : Set β), f x = 
f b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iSup_iSup_eq_left`：iSup_iSup_eq_left {b : β} {f : forall x : β, x = b ->
 α} : ⨆ x, ⨆ h : x = b, f x h = f b rfl
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iSup_singleton {f : β → α} {b : β} : ⨆ x ∈ (singleton b : Set β), f x = f b := by simp

@[to_dual]
/-
**iSup_pair** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_pair {f : β -> α} {a b : β} : ⨆ x in ({a, b} : Set β), f x = f a ⊔ f 
b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_insert`：iSup_insert {f : β -> α} {s : Set β} {b : β} : ⨆ x in inser
t b s, f x = f b ⊔ ⨆ x in s, f x
· 使用定理 `iSup_singleton`：iSup_singleton {f : β -> α} {b : β} : ⨆ x in (singleton 
b : Set β), f x = f b
-/
theorem iSup_pair {f : β → α} {a b : β} : ⨆ x ∈ ({a, b} : Set β), f x = f a ⊔ f b := by
  rw [iSup_insert, iSup_singleton]

@[to_dual]
/-
**iSup_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_image {γ} {f : β -> γ} {g : γ -> α} {t : Set β} : ⨆ c in f '' t, g c 
= ⨆ b in t, g (f b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sSup_image`：sSup_image {s : Set β} {f : β -> α} : sSup (f '' s) = ⨆ a in
 s, f a
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
-/
theorem iSup_image {γ} {f : β → γ} {g : γ → α} {t : Set β} :
    ⨆ c ∈ f '' t, g c = ⨆ b ∈ t, g (f b) := by
  rw [← sSup_image, ← sSup_image, ← image_comp, comp_def]

@[to_dual]
/-
**iSup_extend_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_extend_bot {e : ι -> β} (he : Injective e) (f : ι -> α) : ⨆ j, extend
 e f ⊥ j = ⨆ i, f i
参数：he : Injective e；f : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_split`：iSup_split (f : β -> α) (p : β -> Prop) : ⨆ i, f i = (⨆ (i) 
(_ : p i), f i) ⊔ ⨆ (i) (_ : ¬p i), f i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_exists`：iSup_exists {p : ι -> Prop} {f : Exists p -> α} : ⨆ x, f x 
= ⨆ (i) (h), f ⟨i, h⟩
· 使用定理 `iSup_comm`：iSup_comm {f : ι -> ι' -> α} : ⨆ (i) (j), f i j = ⨆ (j) (i), 
f i j
· 使用定理 `iSup_iSup_eq_right`：iSup_iSup_eq_right {b : β} {f : forall x : β, b = x 
-> α} : ⨆ x, ⨆ h : b = x, f x h = f b rfl
· 使用定理 `Function.Injective.extend_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Injective f → ∀ (g : α → γ) (e' : β → γ) (a : α)
, Function.extend f g…
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Function.extend_apply'`：extend_apply' (g : α -> γ) (e' : β -> γ) (b : β)
 (hb : ¬exists a, f a = b) : extend f g e' b = e' b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iSup_bot`：iSup_bot : (⨆ _ : ι, ⊥ : α) = ⊥
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iSup_extend_bot {e : ι → β} (he : Injective e) (f : ι → α) :
    ⨆ j, extend e f ⊥ j = ⨆ i, f i := by
  rw [iSup_split _ fun j => ∃ i, e i = j]
  simp +contextual [he.extend_apply, extend_apply', @iSup_comm _ β ι]

@[to_dual]
/-
**Set.BijOn.iSup_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.BijOn.iSup_comp {s : Set β} {t : Set γ} {f : β -> γ} (g : γ -> α) (hf 
: Set.BijOn f s t) : ⨆ x in s, g (f x) = ⨆ y in t, g y
参数：g : γ -> α；hf : Set.BijOn f s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.BijOn.image_eq`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set
 β} {f : α → β}, Set.BijOn f s t → f '' s = t
· 使用定理 `iSup_image`：iSup_image {γ} {f : β -> γ} {g : γ -> α} {t : Set β} : ⨆ c i
n f '' t, g c = ⨆ b in t, g (f b)
-/
theorem Set.BijOn.iSup_comp {s : Set β} {t : Set γ} {f : β → γ} (g : γ → α)
    (hf : Set.BijOn f s t) : ⨆ x ∈ s, g (f x) = ⨆ y ∈ t, g y := by
  rw [← hf.image_eq, iSup_image]

@[to_dual]
/-
**Set.BijOn.iSup_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.BijOn.iSup_congr {s : Set β} {t : Set γ} (f : β -> α) (g : γ -> α) {h 
: β -> γ} (h1 : Set.BijOn h s t) (h2 : forall x, g (h x) = f x) : ⨆ x in s, f x 
= ⨆ y in t, g y
参数：f : β -> α；g : γ -> α；h1 : Set.BijOn h s t；h2 : forall x, g (h x) = f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.BijOn.iSup_comp`：Set.BijOn.iSup_comp {s : Set β} {t : Set γ} {f : β 
-> γ} (g : γ -> α) (hf : Set.BijOn f s t) : ⨆ x in s, g (f x) = ⨆ y in t, g y
-/
theorem Set.BijOn.iSup_congr {s : Set β} {t : Set γ} (f : β → α) (g : γ → α) {h : β → γ}
    (h1 : Set.BijOn h s t) (h2 : ∀ x, g (h x) = f x) : ⨆ x ∈ s, f x = ⨆ y ∈ t, g y := by
  simpa only [h2] using h1.iSup_comp g

section le

variable {ι : Type*} [PartialOrder ι] (f : ι → α) (i : ι)

@[to_dual (dont_translate := ι)]
/-
**biSup_le_eq_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：biSup_le_eq_sup : (⨆ j <= i, f j) = (⨆ j < i, f j) ⊔ f i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_split_single`：iSup_split_single (f : β -> α) (i₀ : β) : ⨆ i, f i = 
f i₀ ⊔ ⨆ (i) (_ : i != i₀), f i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iSup_pos`：iSup_pos {p : Prop} {f : p -> α} (hp : p) : ⨆ h : p, f h = f h
p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_and'`：iSup_and' {p q : Prop} {s : p -> q -> α} : ⨆ (h₁ : p) (h₂ : q
), s h₁ h₂ = ⨆ h : p ∧ q, s h.1 h.2
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem biSup_le_eq_sup : (⨆ j ≤ i, f j) = (⨆ j < i, f j) ⊔ f i := by
  rw [iSup_split_single _ i]
  -- Squeezed for a ~10x speedup, though it's still reasonably fast unsqueezed.
  simp only [le_refl, iSup_pos, iSup_and', lt_iff_le_and_ne, and_comm, sup_comm]

@[to_dual (dont_translate := ι)]
/-
**biSup_ge_eq_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：biSup_ge_eq_sup : (⨆ j >= i, f j) = f i ⊔ (⨆ j > i, f j)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_split_single`：iSup_split_single (f : β -> α) (i₀ : β) : ⨆ i, f i = 
f i₀ ⊔ ⨆ (i) (_ : i != i₀), f i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iSup_pos`：iSup_pos {p : Prop} {f : p -> α} (hp : p) : ⨆ h : p, f h = f h
p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_and'`：iSup_and' {p q : Prop} {s : p -> q -> α} : ⨆ (h₁ : p) (h₂ : q
), s h₁ h₂ = ⨆ h : p ∧ q, s h.1 h.2
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem biSup_ge_eq_sup : (⨆ j ≥ i, f j) = f i ⊔ (⨆ j > i, f j) := by
  rw [iSup_split_single _ i]
  -- Squeezed for a ~10x speedup, though it's still reasonably fast unsqueezed.
  simp only [ge_iff_le, le_refl, iSup_pos, ne_comm, iSup_and', gt_iff_lt, lt_iff_le_and_ne,
    and_comm]

end le

/-!
### `iSup` and `iInf` under `Type`
-/

@[to_dual iInf_of_isEmpty]
/-
**iSup_of_empty'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_of_empty' {α ι} [SupSet α] [IsEmpty ι] (f : ι -> α) : iSup f = sSup (
∅ : Set α)
参数：f : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Set.range_eq_empty`：range_eq_empty [IsEmpty ι] (f : ι -> α) : range f = 
∅

--- 原说明 ---
### `iSup` and `iInf` under `Type`
-/
theorem iSup_of_empty' {α ι} [SupSet α] [IsEmpty ι] (f : ι → α) : iSup f = sSup (∅ : Set α) :=
  congr_arg sSup (range_eq_empty f)

@[to_dual]
/-
**iSup_of_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_of_empty [IsEmpty ι] (f : ι -> α) : iSup f = ⊥
参数：f : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iSup_of_empty'`：iSup_of_empty' {α ι} [SupSet α] [IsEmpty ι] (f : ι -> α)
 : iSup f = sSup (∅ : Set α)
· 使用定理 `sSup_empty`：sSup_empty : sSup ∅ = (⊥ : α)
-/
theorem iSup_of_empty [IsEmpty ι] (f : ι → α) : iSup f = ⊥ :=
  (iSup_of_empty' f).trans sSup_empty

@[to_dual]
/-
**isLUB_biSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLUB_biSup {s : Set β} {f : β -> α} : IsLUB (f '' s) (⨆ x in s, f x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_subtype'`：iSup_subtype' {p : ι -> Prop} {f : forall i, p i -> α} : 
⨆ (i) (h), f i h = ⨆ x : Subtype p, f x x.property
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
· 使用定理 `isLUB_iSup`：isLUB_iSup : IsLUB (range f) (⨆ j, f j)
-/
theorem isLUB_biSup {s : Set β} {f : β → α} : IsLUB (f '' s) (⨆ x ∈ s, f x) := by
  simpa only [range_comp, Subtype.range_coe, iSup_subtype'] using!
    @isLUB_iSup α s _ (f ∘ fun x => (x : β))

@[to_dual]
/-
**iSup_sigma** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_sigma {p : β -> Type*} {f : Sigma p -> α} : ⨆ x, f x = ⨆ (i) (j), f ⟨
i, j⟩
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem iSup_sigma {p : β → Type*} {f : Sigma p → α} : ⨆ x, f x = ⨆ (i) (j), f ⟨i, j⟩ :=
  eq_of_forall_ge_iff fun c => by simp only [iSup_le_iff, Sigma.forall]

@[to_dual]
/-
**iSup_sigma'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iSup_sigma' {κ : β -> Type*} (f : forall i, κ i -> α) : (⨆ i, ⨆ j, f i j) 
= ⨆ x : Σ i, κ i, f x.1 x.2
参数：f : forall i, κ i -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iSup_sigma`：iSup_sigma {p : β -> Type*} {f : Sigma p -> α} : ⨆ x, f x = 
⨆ (i) (j), f ⟨i, j⟩
-/
lemma iSup_sigma' {κ : β → Type*} (f : ∀ i, κ i → α) :
    (⨆ i, ⨆ j, f i j) = ⨆ x : Σ i, κ i, f x.1 x.2 := (iSup_sigma (f := fun x ↦ f x.1 x.2)).symm

@[to_dual]
/-
**iSup_psigma** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iSup_psigma {ι : Sort*} {κ : ι -> Sort*} (f : (Σ' i, κ i) -> α) : ⨆ ij, f 
ij = ⨆ i, ⨆ j, f ⟨i, j⟩
参数：f : (Σ' i, κ i) -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma iSup_psigma {ι : Sort*} {κ : ι → Sort*} (f : (Σ' i, κ i) → α) :
    ⨆ ij, f ij = ⨆ i, ⨆ j, f ⟨i, j⟩ :=
  eq_of_forall_ge_iff fun c ↦ by simp only [iSup_le_iff, PSigma.forall]

@[to_dual]
/-
**iSup_psigma'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iSup_psigma' {ι : Sort*} {κ : ι -> Sort*} (f : forall i, κ i -> α) : (⨆ i,
 ⨆ j, f i j) = ⨆ ij : Σ' i, κ i, f ij.1 ij.2
参数：f : forall i, κ i -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `iSup_psigma`：iSup_psigma {ι : Sort*} {κ : ι -> Sort*} (f : (Σ' i, κ i) -
> α) : ⨆ ij, f ij = ⨆ i, ⨆ j, f ⟨i, j⟩
-/
lemma iSup_psigma' {ι : Sort*} {κ : ι → Sort*} (f : ∀ i, κ i → α) :
    (⨆ i, ⨆ j, f i j) = ⨆ ij : Σ' i, κ i, f ij.1 ij.2 := (iSup_psigma fun x ↦ f x.1 x.2).symm

@[to_dual]
/-
**iSup_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_prod {f : β × γ -> α} : ⨆ x, f x = ⨆ (i) (j), f (i, j)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem iSup_prod {f : β × γ → α} : ⨆ x, f x = ⨆ (i) (j), f (i, j) :=
  eq_of_forall_ge_iff fun c => by simp only [iSup_le_iff, Prod.forall]

@[to_dual]
/-
**iSup_prod'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iSup_prod' (f : β -> γ -> α) : (⨆ i, ⨆ j, f i j) = ⨆ x : β × γ, f x.1 x.2
参数：f : β -> γ -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iSup_prod`：iSup_prod {f : β × γ -> α} : ⨆ x, f x = ⨆ (i) (j), f (i, j)
-/
lemma iSup_prod' (f : β → γ → α) : (⨆ i, ⨆ j, f i j) = ⨆ x : β × γ, f x.1 x.2 :=
(iSup_prod (f := fun x ↦ f x.1 x.2)).symm

@[to_dual]
/-
**biSup_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：biSup_prod {f : β × γ -> α} {s : Set β} {t : Set γ} : ⨆ x in s ×ˢ t, f x =
 ⨆ (a in s) (b in t), f (a, b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_prod`：iSup_prod {f : β × γ -> α} : ⨆ x, f x = ⨆ (i) (j), f (i, j)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iSup_and`：iSup_and {p q : Prop} {s : p ∧ q -> α} : iSup s = ⨆ (h₁) (h₂),
 s ⟨h₁, h₂⟩
· 使用定理 `iSup_congr`：iSup_congr (h : forall i, f i = g i) : ⨆ i, f i = ⨆ i, g i
· 使用定理 `iSup_comm`：iSup_comm {f : ι -> ι' -> α} : ⨆ (i) (j), f i j = ⨆ (j) (i), 
f i j
-/
theorem biSup_prod {f : β × γ → α} {s : Set β} {t : Set γ} :
    ⨆ x ∈ s ×ˢ t, f x = ⨆ (a ∈ s) (b ∈ t), f (a, b) := by
  simp_rw [iSup_prod, mem_prod, iSup_and]
  exact iSup_congr fun _ => iSup_comm

@[to_dual]
/-
**biSup_prod'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：biSup_prod' {f : β -> γ -> α} {s : Set β} {t : Set γ} : ⨆ x in s ×ˢ t, f x
.1 x.2 = ⨆ (a in s) (b in t), f a b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `biSup_prod`：biSup_prod {f : β × γ -> α} {s : Set β} {t : Set γ} : ⨆ x in
 s ×ˢ t, f x = ⨆ (a in s) (b in t), f (a, b)
-/
theorem biSup_prod' {f : β → γ → α} {s : Set β} {t : Set γ} :
    ⨆ x ∈ s ×ˢ t, f x.1 x.2 = ⨆ (a ∈ s) (b ∈ t), f a b :=
  biSup_prod

@[to_dual]
/-
**iSup_image2** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_image2 {γ δ} (f : β -> γ -> δ) (s : Set β) (t : Set γ) (g : δ -> α) :
 ⨆ d in image2 f s t, g d = ⨆ b in s, ⨆ c in t, g (f b c)
参数：f : β -> γ -> δ；s : Set β；t : Set γ；g : δ -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.image_prod`：image_prod : (fun x : α × β => f x.1 x.2) '' s ×ˢ t = im
age2 f s t
· 使用定理 `iSup_image`：iSup_image {γ} {f : β -> γ} {g : γ -> α} {t : Set β} : ⨆ c i
n f '' t, g c = ⨆ b in t, g (f b)
· 使用定理 `biSup_prod`：biSup_prod {f : β × γ -> α} {s : Set β} {t : Set γ} : ⨆ x in
 s ×ˢ t, f x = ⨆ (a in s) (b in t), f (a, b)
-/
theorem iSup_image2 {γ δ} (f : β → γ → δ) (s : Set β) (t : Set γ) (g : δ → α) :
    ⨆ d ∈ image2 f s t, g d = ⨆ b ∈ s, ⨆ c ∈ t, g (f b c) := by
  rw [← image_prod, iSup_image, biSup_prod]

@[to_dual]
/-
**iSup_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_sum {f : β oplus γ -> α} : ⨆ x, f x = (⨆ i, f (Sum.inl i)) ⊔ ⨆ j, f (
Sum.inr j)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem iSup_sum {f : β ⊕ γ → α} : ⨆ x, f x = (⨆ i, f (Sum.inl i)) ⊔ ⨆ j, f (Sum.inr j) :=
  eq_of_forall_ge_iff fun c => by simp only [sup_le_iff, iSup_le_iff, Sum.forall]

@[to_dual]
/-
**iSup_option** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_option (f : Option β -> α) : ⨆ o, f o = f none ⊔ ⨆ b, f (Option.some 
b)
参数：f : Option β -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem iSup_option (f : Option β → α) : ⨆ o, f o = f none ⊔ ⨆ b, f (Option.some b) :=
  eq_of_forall_ge_iff fun c => by simp only [iSup_le_iff, sup_le_iff, Option.forall]

/-- A version of `iSup_option` useful for rewriting right-to-left. -/
@[to_dual /-- A version of `iInf_option` useful for rewriting right-to-left. -/]
/-
**iSup_option_elim** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_option_elim (a : α) (f : β -> α) : ⨆ o : Option β, o.elim a f = a ⊔ ⨆
 b, f b
参数：a : α；f : β -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_option`：iSup_option (f : Option β -> α) : ⨆ o, f o = f none ⊔ ⨆ b, 
f (Option.some b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A version of `iSup_option` useful for rewriting right-to-left.
-/
theorem iSup_option_elim (a : α) (f : β → α) : ⨆ o : Option β, o.elim a f = a ⊔ ⨆ b, f b := by
  simp [iSup_option]

/-- When taking the supremum of `f : ι → α`, the elements of `ι` on which `f` gives `⊥` can be
dropped, without changing the result. -/
@[to_dual /-- When taking the infimum of `f : ι → α`, the elements of `ι` on which `f` gives `⊤`
can be dropped, without changing the result. -/, simp]
/-
**iSup_ne_bot_subtype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_ne_bot_subtype (f : ι -> α) : ⨆ i : { i // f i != ⊥ }, f i = ⨆ i, f i
参数：f : ι -> α。
该定理/引理给出了一组等式。
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
· 使用定理 `iSup_bot`：iSup_bot : (⨆ _ : ι, ⊥ : α) = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `iSup_comp_le`：iSup_comp_le {ι' : Sort*} (f : ι' -> α) (g : ι -> ι') : ⨆ 
x, f (g x) <= ⨆ y, f y
· 使用定理 `iSup_mono'`：iSup_mono' {g : ι' -> α} (h : forall i, exists i', f i <= g 
i') : iSup f <= iSup g
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
theorem iSup_ne_bot_subtype (f : ι → α) : ⨆ i : { i // f i ≠ ⊥ }, f i = ⨆ i, f i := by
  by_cases! htriv : ∀ i, f i = ⊥
  · simp only [iSup_bot, (funext htriv : f = _)]
  refine (iSup_comp_le f _).antisymm (iSup_mono' fun i => ?_)
  by_cases hi : f i = ⊥
  · rw [hi]
    obtain ⟨i₀, hi₀⟩ := htriv
    exact ⟨⟨i₀, hi₀⟩, bot_le⟩
  · exact ⟨⟨i, hi⟩, rfl.le⟩

@[to_dual]
/-
**sSup_image2** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sSup_image2 {f : β -> γ -> α} {s : Set β} {t : Set γ} : sSup (image2 f s t
) = ⨆ (a in s) (b in t), f a b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.image_prod`：image_prod : (fun x : α × β => f x.1 x.2) '' s ×ˢ t = im
age2 f s t
· 使用定理 `sSup_image`：sSup_image {s : Set β} {f : β -> α} : sSup (f '' s) = ⨆ a in
 s, f a
· 使用定理 `biSup_prod`：biSup_prod {f : β × γ -> α} {s : Set β} {t : Set γ} : ⨆ x in
 s ×ˢ t, f x = ⨆ (a in s) (b in t), f (a, b)
-/
theorem sSup_image2 {f : β → γ → α} {s : Set β} {t : Set γ} :
    sSup (image2 f s t) = ⨆ (a ∈ s) (b ∈ t), f a b := by rw [← image_prod, sSup_image, biSup_prod]

end

section CompleteLinearOrder

variable [CompleteLinearOrder α]

@[to_dual]
/-
**iSup** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：iSup [SupSet α] (s : ι -> α) : α
参数：s : ι -> α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma iSup₂_eq_top (f : ∀ i, κ i → α) : ⨆ i, ⨆ j, f i j = ⊤ ↔ ∀ b < ⊤, ∃ i j, b < f i j := by
  simp_rw [iSup_psigma', iSup_eq_top, PSigma.exists]

end CompleteLinearOrder

/-!
### Instances
-/


/-
**Prop.instCompleteLattice** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prop.instCompleteLattice : CompleteLattice Prop where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Instances
-/
instance Prop.instCompleteLattice : CompleteLattice Prop where
  __ := Prop.instBoundedOrder
  __ := Prop.instDistribLattice
  sSup s := ∃ a ∈ s, a
  isLUB_sSup _ := ⟨fun a h p ↦ ⟨a, h, p⟩, fun _ h ⟨_, h', p⟩ => h h' p⟩
  sInf s := ∀ a ∈ s, a
  isGLB_sInf _ := ⟨fun a h p ↦ p a h, fun _ h p _ hb ↦ h hb p⟩
/-
**Prop.instCompleteLinearOrder** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prop.instCompleteLinearOrder : CompleteLinearOrder Prop where __
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `BiheytingAlgebra.sdiff_le_iff`：∀ {α : Type u_4} [self : BiheytingAlgebra
 α] (a b c : α), a \ b ≤ c ↔ a ≤ b ⊔ c
· 使用定理 `BiheytingAlgebra.top_sdiff`：∀ {α : Type u_4} [self : BiheytingAlgebra α]
 (a : α), ⊤ \ a = ￢a
· 使用定理 `LinearOrder.le_total`：∀ {α : Type u_2} [self : LinearOrder α] (a b : α),
 a ≤ b ∨ b ≤ a
· 使用定理 `LinearOrder.compare_eq_compareOfLessAndEq`：∀ {α : Type u_2} [self : Line
arOrder α] (a b : α), compare a b = compareOfLessAndEq a b
-/
noncomputable instance Prop.instCompleteLinearOrder : CompleteLinearOrder Prop where
  __ := Prop.instCompleteLattice
  __ := Prop.linearOrder
  __ := BooleanAlgebra.toBiheytingAlgebra

@[simp]
/-
**sSup_Prop_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sSup_Prop_eq {s : Set Prop} : sSup s = exists p in s, p
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sSup_Prop_eq {s : Set Prop} : sSup s = ∃ p ∈ s, p :=
  rfl

@[simp]
/-
**sInf_Prop_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sInf_Prop_eq {s : Set Prop} : sInf s = forall p in s, p
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sInf_Prop_eq {s : Set Prop} : sInf s = ∀ p ∈ s, p :=
  rfl

@[simp]
/-
**iSup_Prop_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_Prop_eq {p : ι -> Prop} : ⨆ i, p i = exists i, p i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem iSup_Prop_eq {p : ι → Prop} : ⨆ i, p i = ∃ i, p i :=
  le_antisymm (fun ⟨_, ⟨i, (eq : p i = _)⟩, hq⟩ => ⟨i, eq.symm ▸ hq⟩) fun ⟨i, hi⟩ =>
    ⟨p i, ⟨i, rfl⟩, hi⟩

@[simp]
/-
**iInf_Prop_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iInf_Prop_eq {p : ι -> Prop} : ⨅ i, p i = forall i, p i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
-/
theorem iInf_Prop_eq {p : ι → Prop} : ⨅ i, p i = ∀ i, p i :=
  le_antisymm (fun h i => h _ ⟨i, rfl⟩) fun h _ ⟨i, Eq⟩ => Eq ▸ h i

@[to_dual]
/-
**Pi.supSet** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.supSet {α : Type*} {β : α -> Type*} [forall i, SupSet (β i)] : SupSet (
forall i, β i)
参数：β i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Pi.supSet {α : Type*} {β : α → Type*} [∀ i, SupSet (β i)] : SupSet (∀ i, β i) :=
  ⟨fun s i => ⨆ f : s, (f : ∀ i, β i) i⟩

@[to_dual (attr := simp)]
/-
**sSup_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sSup_apply {α : Type*} {β : α -> Type*} [forall i, SupSet (β i)] {s : Set 
(forall a, β a)} {a : α} : (sSup s) a = ⨆ f : s, (f : forall a, β a) a
参数：β i；forall a, β a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sSup_apply {α : Type*} {β : α → Type*} [∀ i, SupSet (β i)] {s : Set (∀ a, β a)} {a : α} :
    (sSup s) a = ⨆ f : s, (f : ∀ a, β a) a :=
  rfl

@[to_dual]
/-
**sSup_apply_eq_sSup_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sSup_apply_eq_sSup_image {α : Type*} {β : α -> Type*} [forall i, SupSet (β
 i)] {s : Set (forall a, β a)} {a : α} : sSup s a = sSup (eval a '' s)
参数：β i；forall a, β a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.image_eq_range`：image_eq_range (f : α -> β) (s : Set α) : f '' s = r
ange fun x : s => f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sSup_apply_eq_sSup_image {α : Type*} {β : α → Type*} [∀ i, SupSet (β i)]
    {s : Set (∀ a, β a)} {a : α} :
    sSup s a = sSup (eval a '' s) := by
  simp [sSup_apply, iSup, image_eq_range]
/-
**Pi.instCompleteLattice** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.instCompleteLattice {α : Type*} {β : α -> Type*} [forall i, CompleteLat
tice (β i)] : CompleteLattice (forall i, β i) where __
参数：β i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Pi.instCompleteLattice {α : Type*} {β : α → Type*} [∀ i, CompleteLattice (β i)] :
    CompleteLattice (∀ i, β i) where
  __ := instBoundedOrder
  isLUB_sSup _ := isLUB_pi.mpr fun _ ↦ by rw [sSup_apply_eq_sSup_image]; exact isLUB_sSup _
  isGLB_sInf _ := isGLB_pi.mpr fun _ ↦ by rw [sInf_apply_eq_sInf_image]; exact isGLB_sInf _

@[to_dual (attr := simp)]
/-
**iSup_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_apply {α : Type*} {β : α -> Type*} {ι : Sort*} [forall i, SupSet (β i
)] {f : ι -> forall a, β a} {a : α} : (⨆ i, f i) a = ⨆ i, f i a
参数：β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : SupSet α] (s : ι → α), iS
up s = sSup (Set.range s)
· 使用定理 `sSup_apply`：sSup_apply {α : Type*} {β : α -> Type*} [forall i, SupSet (β
 i)] {s : Set (forall a, β a)} {a : α} : (sSup s) a = ⨆ f : s, (f : forall a, β 
…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_eq_range`：image_eq_range (f : α -> β) (s : Set α) : f '' s = r
ange fun x : s => f x
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
-/
theorem iSup_apply {α : Type*} {β : α → Type*} {ι : Sort*} [∀ i, SupSet (β i)] {f : ι → ∀ a, β a}
    {a : α} : (⨆ i, f i) a = ⨆ i, f i a := by
  rw [iSup, sSup_apply, iSup, iSup, ← image_eq_range (fun f : ∀ i, β i => f a) (range f), ←
    range_comp]; rfl
/-
**unary_relation_sSup_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：unary_relation_sSup_iff {α : Type*} (s : Set (α -> Prop)) {a : α} : sSup s
 a ↔ exists r in s, r a
参数：s : Set (α -> Prop)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_Prop_eq`：iSup_Prop_eq {p : ι -> Prop} : ⨆ i, p i = exists i, p i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem unary_relation_sSup_iff {α : Type*} (s : Set (α → Prop)) {a : α} :
    sSup s a ↔ ∃ r ∈ s, r a := by
  simp
/-
**unary_relation_sInf_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：unary_relation_sInf_iff {α : Type*} (s : Set (α -> Prop)) {a : α} : sInf s
 a ↔ forall r in s, r a
参数：s : Set (α -> Prop)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf_Prop_eq`：iInf_Prop_eq {p : ι -> Prop} : ⨅ i, p i = forall i, p i
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem unary_relation_sInf_iff {α : Type*} (s : Set (α → Prop)) {a : α} :
    sInf s a ↔ ∀ r ∈ s, r a := by
  simp
/-
**binary_relation_sSup_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：binary_relation_sSup_iff {α β : Type*} (s : Set (α -> β -> Prop)) {a : α} 
{b : β} : sSup s a b ↔ exists r in s, r a b
参数：s : Set (α -> β -> Prop)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_apply`：iSup_apply {α : Type*} {β : α -> Type*} {ι : Sort*} [forall 
i, SupSet (β i)] {f : ι -> forall a, β a} {a : α} : (⨆ i, f i) a = ⨆ i, f i a
· 使用定理 `iSup_Prop_eq`：iSup_Prop_eq {p : ι -> Prop} : ⨆ i, p i = exists i, p i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem binary_relation_sSup_iff {α β : Type*} (s : Set (α → β → Prop)) {a : α} {b : β} :
    sSup s a b ↔ ∃ r ∈ s, r a b := by
  simp
/-
**binary_relation_sInf_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：binary_relation_sInf_iff {α β : Type*} (s : Set (α -> β -> Prop)) {a : α} 
{b : β} : sInf s a b ↔ forall r in s, r a b
参数：s : Set (α -> β -> Prop)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf_apply`：∀ {α : Type u_8} {β : α → Type u_9} {ι : Sort u_10} [inst : 
(i : α) → InfSet (β i)] {f : ι → (a : α) → β a} {a : α},   (⨅ i, f i) a = ⨅ i, f
…
· 使用定理 `iInf_Prop_eq`：iInf_Prop_eq {p : ι -> Prop} : ⨅ i, p i = forall i, p i
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem binary_relation_sInf_iff {α β : Type*} (s : Set (α → β → Prop)) {a : α} {b : β} :
    sInf s a b ↔ ∀ r ∈ s, r a b := by
  simp

section CompleteLattice

variable [Preorder α] [CompleteLattice β] {s : Set (α → β)} {f : ι → α → β}

@[to_dual]
/-
**Monotone.sSup** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : CompleteLatt
ice β] {s : Set (α → β)},   (∀ f ∈ s, Monotone f) → Monotone (sSup s)
参数：α → β；∀ f ∈ s, Monotone f；sSup s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_mono`：iSup_mono (h : forall i, f i <= g i) : iSup f <= iSup g
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
protected lemma Monotone.sSup (hs : ∀ f ∈ s, Monotone f) : Monotone (sSup s) :=
  fun _ _ h ↦ iSup_mono fun f ↦ hs f f.2 h

@[to_dual]
/-
**Antitone.sSup** 是 Mathlib 中的一个定理，位于命名空间 `Antitone`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : CompleteLatt
ice β] {s : Set (α → β)},   (∀ f ∈ s, Antitone f) → Antitone (sSup s)
参数：α → β；∀ f ∈ s, Antitone f；sSup s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_mono`：iSup_mono (h : forall i, f i <= g i) : iSup f <= iSup g
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
protected lemma Antitone.sSup (hs : ∀ f ∈ s, Antitone f) : Antitone (sSup s) :=
  fun _ _ h ↦ iSup_mono fun f ↦ hs f f.2 h

@[to_dual]
/-
**Monotone.iSup** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} [inst : Preorder α] [inst_1
 : CompleteLattice β] {f : ι → α → β},   (∀ (i : ι), Monotone (f i)) → Monotone 
(⨆ i, f i)
参数：∀ (i : ι), Monotone (f i)；⨆ i, f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.sSup`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst
_1 : CompleteLattice β] {s : Set (α → β)},   (∀ f ∈ s, Monotone f) → Monotone (s
Sup…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
protected lemma Monotone.iSup (hf : ∀ i, Monotone (f i)) : Monotone (⨆ i, f i) :=
  Monotone.sSup (by simpa)

@[to_dual]
/-
**Antitone.iSup** 是 Mathlib 中的一个定理，位于命名空间 `Antitone`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} [inst : Preorder α] [inst_1
 : CompleteLattice β] {f : ι → α → β},   (∀ (i : ι), Antitone (f i)) → Antitone 
(⨆ i, f i)
参数：∀ (i : ι), Antitone (f i)；⨆ i, f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Antitone.sSup`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst
_1 : CompleteLattice β] {s : Set (α → β)},   (∀ f ∈ s, Antitone f) → Antitone (s
Sup…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
protected lemma Antitone.iSup (hf : ∀ i, Antitone (f i)) : Antitone (⨆ i, f i) :=
  Antitone.sSup (by simpa)

end CompleteLattice

namespace Prod

variable (α β)

@[to_dual]
/-
**Prod.supSet** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：supSet [SupSet α] [SupSet β] : SupSet (α × β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance supSet [SupSet α] [SupSet β] : SupSet (α × β) :=
  ⟨fun s => (sSup (Prod.fst '' s), sSup (Prod.snd '' s))⟩

variable {α β}

@[to_dual]
/-
**Prod.fst_sSup** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：fst_sSup [SupSet α] [SupSet β] (s : Set (α × β)) : (sSup s).fst = sSup (Pr
od.fst '' s)
参数：s : Set (α × β)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_sSup [SupSet α] [SupSet β] (s : Set (α × β)) : (sSup s).fst = sSup (Prod.fst '' s) :=
  rfl

@[to_dual]
/-
**Prod.snd_sSup** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：snd_sSup [SupSet α] [SupSet β] (s : Set (α × β)) : (sSup s).snd = sSup (Pr
od.snd '' s)
参数：s : Set (α × β)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_sSup [SupSet α] [SupSet β] (s : Set (α × β)) : (sSup s).snd = sSup (Prod.snd '' s) :=
  rfl

@[to_dual]
/-
**Prod.swap_sSup** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：swap_sSup [SupSet α] [SupSet β] (s : Set (α × β)) : (sSup s).swap = sSup (
Prod.swap '' s)
参数：s : Set (α × β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
-/
theorem swap_sSup [SupSet α] [SupSet β] (s : Set (α × β)) : (sSup s).swap = sSup (Prod.swap '' s) :=
  Prod.ext (congr_arg sSup <| image_comp Prod.fst swap s)
    (congr_arg sSup <| image_comp Prod.snd swap s)

@[to_dual]
/-
**Prod.fst_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：fst_iSup [SupSet α] [SupSet β] (f : ι -> α × β) : (iSup f).fst = ⨆ i, (f i
).fst
参数：f : ι -> α × β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
-/
theorem fst_iSup [SupSet α] [SupSet β] (f : ι → α × β) : (iSup f).fst = ⨆ i, (f i).fst :=
  congr_arg sSup (range_comp _ _).symm

@[to_dual]
/-
**Prod.snd_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：snd_iSup [SupSet α] [SupSet β] (f : ι -> α × β) : (iSup f).snd = ⨆ i, (f i
).snd
参数：f : ι -> α × β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
-/
theorem snd_iSup [SupSet α] [SupSet β] (f : ι → α × β) : (iSup f).snd = ⨆ i, (f i).snd :=
  congr_arg sSup (range_comp _ _).symm

@[to_dual]
/-
**Prod.swap_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：swap_iSup [SupSet α] [SupSet β] (f : ι -> α × β) : (iSup f).swap = ⨆ i, (f
 i).swap
参数：f : ι -> α × β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prod.swap_sSup`：swap_sSup [SupSet α] [SupSet β] (s : Set (α × β)) : (sSu
p s).swap = sSup (Prod.swap '' s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem swap_iSup [SupSet α] [SupSet β] (f : ι → α × β) : (iSup f).swap = ⨆ i, (f i).swap := by
  simp_rw [iSup, swap_sSup, ← range_comp, comp_def]

@[to_dual]
/-
**Prod.iSup_mk** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：iSup_mk [SupSet α] [SupSet β] (f : ι -> α) (g : ι -> β) : ⨆ i, (f i, g i) 
= (⨆ i, f i, ⨆ i, g i)
参数：f : ι -> α；g : ι -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Prod.fst_iSup`：fst_iSup [SupSet α] [SupSet β] (f : ι -> α × β) : (iSup f
).fst = ⨆ i, (f i).fst
· 使用定理 `Prod.snd_iSup`：snd_iSup [SupSet α] [SupSet β] (f : ι -> α × β) : (iSup f
).snd = ⨆ i, (f i).snd
-/
theorem iSup_mk [SupSet α] [SupSet β] (f : ι → α) (g : ι → β) :
    ⨆ i, (f i, g i) = (⨆ i, f i, ⨆ i, g i) :=
  congr_arg₂ Prod.mk (fst_iSup _) (snd_iSup _)
/-
**Prod.instCompleteLattice** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：instCompleteLattice [CompleteLattice α] [CompleteLattice β] : CompleteLatt
ice (α × β) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCompleteLattice [CompleteLattice α] [CompleteLattice β] : CompleteLattice (α × β) where
  __ := instBoundedOrder α β
  isLUB_sSup _ := isLUB_prod.mpr ⟨isLUB_sSup _, isLUB_sSup _⟩
  isGLB_sInf _ := isGLB_prod.mpr ⟨isGLB_sInf _, isGLB_sInf _⟩

end Prod

@[to_dual]
/-
**sSup_prod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sSup_prod [SupSet α] [SupSet β] {s : Set α} {t : Set β} (hs : s.Nonempty) 
(ht : t.Nonempty) : sSup (s ×ˢ t) = (sSup s, sSup t)
参数：hs : s.Nonempty；ht : t.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Set.fst_image_prod`：fst_image_prod (s : Set β) {t : Set α} (ht : t.Nonem
pty) : Prod.fst '' s ×ˢ t = s
· 使用定理 `Set.snd_image_prod`：snd_image_prod {s : Set α} (hs : s.Nonempty) (t : Se
t β) : Prod.snd '' s ×ˢ t = t
-/
lemma sSup_prod [SupSet α] [SupSet β] {s : Set α} {t : Set β} (hs : s.Nonempty) (ht : t.Nonempty) :
    sSup (s ×ˢ t) = (sSup s, sSup t) :=
congr_arg₂ Prod.mk (congr_arg sSup <| fst_image_prod _ ht) (congr_arg sSup <| snd_image_prod hs _)

-- See note [reducible non-instances]
/-- Pullback a `CompleteLattice` along an injection. -/
/-
**Function.Injective.completeLattice** 是 Mathlib 中的一个定义，位于命名空间 `Function.Injecti
ve`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     [inst : Max α] →       [inst_1 : M
in α] →         [inst_2 : LE α] →           [inst_3 : LT α] →             [inst_
4 : SupSet α] →               [inst_5 : InfSet α] →                 [inst_6 : To
p α] →                   [inst_7 : Bot α] →                     [inst_8 : Comple
teLattice β] →                       (f : α → β) →                         Funct
ion.Injective f →                           (∀ {x y : α}, f x ≤ f y ↔ x ≤ y) →  
                           (∀ {x y : α}, f x < f y ↔ x < y) →                   
            (∀ (a b : α), f (a ⊔ b) = f a ⊔ f b) →                              
   (∀ (a b : α), f (a ⊓ b) = f a ⊓ f b) →                                   (∀ (
s : Set α), f (sSup s) = ⨆ a ∈ s, f a) →                                     (∀ 
(s : Set α), f (sInf s) = ⨅ a ∈ s, f a) → f ⊤ = ⊤ → f ⊥ = ⊥ → CompleteLattice α
参数：f : α → β；∀ {x y : α}, f x ≤ f y ↔ x ≤ y；∀ {x y : α}, f x < f y ↔ x < y；∀ (a 
b : α), f (a ⊔ b) = f a ⊔ f b；∀ (a b : α), f (a ⊓ b) = f a ⊓ f b；∀ (s : Set α), 
f (sSup s) = ⨆ a ∈ s, f a；∀ (s : Set α), f (sInf s) = ⨅ a ∈ s, f a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pullback a `CompleteLattice` along an injection.
-/
protected abbrev Function.Injective.completeLattice [Max α] [Min α] [LE α] [LT α]
    [SupSet α] [InfSet α] [Top α] [Bot α] [CompleteLattice β]
    (f : α → β) (hf : Function.Injective f)
    (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y) (lt : ∀ {x y}, f x < f y ↔ x < y)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_sSup : ∀ s, f (sSup s) = ⨆ a ∈ s, f a) (map_sInf : ∀ s, f (sInf s) = ⨅ a ∈ s, f a)
    (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) : CompleteLattice α where
  __ := hf.lattice f le lt map_sup map_inf
  __ := BoundedOrder.lift f (fun _ _ ↦ le.1) map_top map_bot
  isLUB_sSup _ := .of_image le (by rw [map_sSup]; exact isLUB_biSup)
  isGLB_sInf _ := .of_image le (by rw [map_sInf]; exact isGLB_biInf)

namespace Equiv

variable (e : α ≃ β)

/-- Transfer `CompleteLattice` across an `Equiv`. -/
/-
**Equiv.completeLattice** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → α ≃ β → [CompleteLattice β] → CompleteLa
ttice α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
Transfer `CompleteLattice` across an `Equiv`.
-/
protected abbrev completeLattice [CompleteLattice β] : CompleteLattice α := by
  let top := e.top
  let bot := e.bot
  let supSet := e.supSet
  let infSet := e.infSet
  let lattice := e.lattice
  apply e.injective.completeLattice <;> intros <;> first | rfl | exact e.apply_symm_apply _

end Equiv

