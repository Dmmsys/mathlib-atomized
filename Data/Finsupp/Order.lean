/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Aaron Anderson
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.Algebra.Order.Pi
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.SMulWithZero
public import Mathlib.Order.Preorder.Finsupp

/-!
# Pointwise order on finitely supported functions

This file lifts order structures on `α` to `ι →₀ α`.

## Main declarations

* `Finsupp.orderEmbeddingToFun`: The order embedding from finitely supported functions to
  functions.
-/

public section

noncomputable section

open Finset

variable {ι κ α β : Type*}

namespace Finsupp

/-! ### Order structures -/


section Zero

variable [Zero α]

section OrderedAddCommMonoid
variable [AddCommMonoid β] [Preorder β] [IsOrderedAddMonoid β] {f : ι →₀ α} {h₁ h₂ : ι → α → β}

@[gcongr only]
/-
**Finsupp.sum_le_sum** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：sum_le_sum (h : forall i in f.support, h₁ i (f i) <= h₂ i (f i)) : f.sum h
₁ <= f.sum h₂
参数：h : forall i in f.support, h₁ i (f i) <= h₂ i (f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
lemma sum_le_sum (h : ∀ i ∈ f.support, h₁ i (f i) ≤ h₂ i (f i)) : f.sum h₁ ≤ f.sum h₂ :=
  Finset.sum_le_sum h
/-
**Finsupp.sum_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：sum_nonneg (h : forall i in f.support, 0 <= h₁ i (f i)) : 0 <= f.sum h₁
参数：h : forall i in f.support, 0 <= h₁ i (f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem sum_nonneg (h : ∀ i ∈ f.support, 0 ≤ h₁ i (f i)) : 0 ≤ f.sum h₁ := Finset.sum_nonneg h
/-
**Finsupp.sum_nonneg'** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：sum_nonneg' (h : forall i, 0 <= h₁ i (f i)) : 0 <= f.sum h₁
参数：h : forall i, 0 <= h₁ i (f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.sum_nonneg`：sum_nonneg (h : forall i in f.support, 0 <= h₁ i (f 
i)) : 0 <= f.sum h₁
-/
theorem sum_nonneg' (h : ∀ i, 0 ≤ h₁ i (f i)) : 0 ≤ f.sum h₁ := sum_nonneg fun _ _ ↦ h _
/-
**Finsupp.sum_nonpos** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：sum_nonpos (h : forall i in f.support, h₁ i (f i) <= 0) : f.sum h₁ <= 0
参数：h : forall i in f.support, h₁ i (f i) <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_nonpos`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, f i ≤…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem sum_nonpos (h : ∀ i ∈ f.support, h₁ i (f i) ≤ 0) : f.sum h₁ ≤ 0 := Finset.sum_nonpos h

end OrderedAddCommMonoid

section IsOrderedCancelAddMonoid

variable [AddCommMonoid β] [Preorder β] [IsOrderedCancelAddMonoid β] [AddLeftStrictMono β]
variable {f : ι →₀ α} {g : ι → α → β}

/-
**Finsupp.sum_pos** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：sum_pos (h : forall i in f.support, 0 < g i (f i)) (hf : f != 0) : 0 < f.s
um g
参数：h : forall i in f.support, 0 < g i (f i)；hf : f != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_pos`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid M]
 [inst_1 : Preorder M] [IsOrderedCancelAddMonoid M] {f : ι → M}   {s : Finset ι}
 [Ad…
-/
theorem sum_pos (h : ∀ i ∈ f.support, 0 < g i (f i)) (hf : f ≠ 0) : 0 < f.sum g :=
  Finset.sum_pos h (by simpa)
/-
**Finsupp.sum_pos'** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：sum_pos' (h : forall i in f.support, 0 <= g i (f i)) (hf : exists i in f.s
upport, 0 < g i (f i)) : 0 < f.sum g
参数：h : forall i in f.support, 0 <= g i (f i)；hf : exists i in f.support, 0 < g i
 (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_pos'`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid M
] [inst_1 : Preorder M] [IsOrderedCancelAddMonoid M] {f : ι → M}   {s : Finset ι
} [Ad…
-/
theorem sum_pos' (h : ∀ i ∈ f.support, 0 ≤ g i (f i)) (hf : ∃ i ∈ f.support, 0 < g i (f i)) :
    0 < f.sum g := Finset.sum_pos' h hf

end IsOrderedCancelAddMonoid

section Preorder
variable [Preorder α] {f g : ι →₀ α} {i : ι} {a b : α}

/-
**Finsupp.single_le_single** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_3} [inst : Zero α] [inst_1 : Preorder α] {i :
 ι} {a b : α},   ((fun₀ | i => a) ≤ fun₀ | i => b) ↔ a ≤ b
参数：(fun₀ | i => a) ≤ fun₀ | i => b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.single_le_single`：∀ {ι : Type u_6} {α : ι → Type u_7} [inst : Decidab
leEq ι] [inst_1 : (i : ι) → Zero (α i)]   [inst_2 : (i : ι) → Preorder (α i)] {i
 : ι} {a …
-/
@[simp, gcongr] lemma single_le_single : single i a ≤ single i b ↔ a ≤ b := by
  classical exact Pi.single_le_single
/-
**Finsupp.single_mono** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：single_mono : Monotone (single i : α -> ι ->₀ α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finsupp.single_le_single`：∀ {ι : Type u_1} {α : Type u_3} [inst : Zero α
] [inst_1 : Preorder α] {i : ι} {a b : α},   ((fun₀ | i => a) ≤ fun₀ | i => b) ↔
 a ≤ b
-/
lemma single_mono : Monotone (single i : α → ι →₀ α) := fun _ _ ↦ single_le_single.2
/-
**Finsupp.single_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_3} [inst : Zero α] [inst_1 : Preorder α] {i :
 ι} {a : α}, (0 ≤ fun₀ | i => a) ↔ 0 ≤ a
参数：0 ≤ fun₀ | i => a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.single_nonneg`：∀ {ι : Type u_6} {α : ι → Type u_7} [inst : DecidableE
q ι] [inst_1 : (i : ι) → Zero (α i)]   [inst_2 : (i : ι) → Preorder (α i)] {i : 
ι} {a …
-/
@[simp] lemma single_nonneg : 0 ≤ single i a ↔ 0 ≤ a := by classical exact Pi.single_nonneg
/-
**Finsupp.single_nonpos** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_3} [inst : Zero α] [inst_1 : Preorder α] {i :
 ι} {a : α}, (fun₀ | i => a) ≤ 0 ↔ a ≤ 0
参数：fun₀ | i => a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.single_nonpos`：∀ {ι : Type u_6} {α : ι → Type u_7} [inst : DecidableE
q ι] [inst_1 : (i : ι) → Zero (α i)]   [inst_2 : (i : ι) → Preorder (α i)] {i : 
ι} {a …
-/
@[simp] lemma single_nonpos : single i a ≤ 0 ↔ a ≤ 0 := by classical exact Pi.single_nonpos

variable [AddCommMonoid β] [Preorder β] [IsOrderedAddMonoid β]
/-
**Finsupp.sum_le_sum_index** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：sum_le_sum_index [DecidableEq ι] {f₁ f₂ : ι ->₀ α} {h : ι -> α -> β} (hf :
 f₁ <= f₂) (hh : forall i in f₁.support union f₂.support, Monotone (h i)) (hh₀ :
 forall i in f₁.support union f₂.support, h i 0 = 0) : f₁.sum h <= f₂.sum h
参数：hf : f₁ <= f₂；hh : forall i in f₁.support union f₂.support, Monotone (h i)；hh
₀ : forall i in f₁.support union f₂.support, h i 0 = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.sum_of_support_subset`：∀ {α : Type u_1} {M : Type u_8} {N : Type
 u_10} [inst : Zero M] [inst_1 : AddCommMonoid N] (f : α →₀ M) {s : Finset α},  
 f.support ⊆ s → ∀ …
· 使用定理 `Finset.subset_union_left`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s₂
 : Finset α}, s₁ ⊆ s₁ ∪ s₂
· 使用定理 `Finset.subset_union_right`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s
₂ : Finset α}, s₂ ⊆ s₁ ∪ s₂
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
lemma sum_le_sum_index [DecidableEq ι] {f₁ f₂ : ι →₀ α} {h : ι → α → β} (hf : f₁ ≤ f₂)
    (hh : ∀ i ∈ f₁.support ∪ f₂.support, Monotone (h i))
    (hh₀ : ∀ i ∈ f₁.support ∪ f₂.support, h i 0 = 0) : f₁.sum h ≤ f₂.sum h := by
  rw [sum_of_support_subset _ Finset.subset_union_left _ hh₀,
    sum_of_support_subset _ Finset.subset_union_right _ hh₀]
  gcongr with i hi
  exact hh _ hi <| hf _

end Preorder

section EmbDomain

@[gcongr]
/-
**Finsupp.embDomain_le_embDomain_iff_le** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：embDomain_le_embDomain_iff_le [LE α] [@Std.Refl α (· <= ·)] (f : ι ↪ κ) (g
₁ g₂ : ι ->₀ α) : g₁.embDomain f <= g₂.embDomain f ↔ g₁ <= g₂
参数：· <= ·；f : ι ↪ κ；g₁ g₂ : ι ->₀ α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finsupp.le_def`：le_def : f <= g ↔ forall i, f i <= g i
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finsupp.embDomain_apply`：embDomain_apply (f : α ↪ β) (v : α ->₀ M) (b : 
β) : embDomain f v b = if h : exists a, f a = b then v h.choose else 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.instEmbeddingLikeEmbedding`：∀ {α : Sort u} {β : Sort v}, Embedd
ingLike (α ↪ β) α β
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Exists.choose.congr_simp`：∀ {α : Sort u_1} {p p_1 : α → Prop} (e_p : p =
 p_1) (P : ∃ a, p a), P.choose = ⋯.choose
· 使用定理 `Classical.choose_eq`：∀ {α : Sort u_1} (a : α), ⋯.choose = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `apply_dite₂`：apply_dite₂ {α β γ : Sort*} (f : α -> β -> γ) (P : Prop) [D
ecidable P] (a : P -> α) (b : ¬P -> α) (c : P -> β) (d : ¬P -> β) : f (dite P a 
b…
· 使用定理 `dite.congr_simp`：∀ {α : Sort u} (c : Prop) {h : Decidable c} [h_1 : Deci
dable c] (t t_1 : c → α),   t = t_1 → ∀ (e e_1 : ¬c → α), e = e_1 → dite c t e =
 dite…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma embDomain_le_embDomain_iff_le [LE α] [@Std.Refl α (· ≤ ·)]
    (f : ι ↪ κ) (g₁ g₂ : ι →₀ α) : g₁.embDomain f ≤ g₂.embDomain f ↔ g₁ ≤ g₂ := by
  constructor
  · rw [Finsupp.le_def]
    intro h' x
    simpa [Finsupp.embDomain_apply] using h' (f x)
  intro h
  simp [Finsupp.le_def, embDomain_apply, apply_dite₂, Finsupp.le_def.mp h]
/-
**Finsupp.embDomain_mono** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：embDomain_mono [Preorder α] (f : ι ↪ κ) : Monotone (embDomain f : (ι ->₀ α
) -> (κ ->₀ α))
参数：f : ι ↪ κ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Finsupp.embDomain_le_embDomain_iff_le`：embDomain_le_embDomain_iff_le [LE
 α] [@Std.Refl α (· <= ·)] (f : ι ↪ κ) (g₁ g₂ : ι ->₀ α) : g₁.embDomain f <= g₂.
embDomain f ↔ g₁ <= g₂
-/
lemma embDomain_mono [Preorder α] (f : ι ↪ κ) : Monotone (embDomain f : (ι →₀ α) → (κ →₀ α)) :=
  fun _ _ ↦ (embDomain_le_embDomain_iff_le f _ _).mpr

@[gcongr]
/-
**Finsupp.embDomain_lt_embDomain_iff_lt** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：embDomain_lt_embDomain_iff_lt [Preorder α] (f : ι ↪ κ) (g₁ g₂ : ι ->₀ α) :
 g₁.embDomain f < g₂.embDomain f ↔ g₁ < g₂
参数：f : ι ↪ κ；g₁ g₂ : ι ->₀ α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma embDomain_lt_embDomain_iff_lt [Preorder α] (f : ι ↪ κ) (g₁ g₂ : ι →₀ α) :
    g₁.embDomain f < g₂.embDomain f ↔ g₁ < g₂ := by
  simp [lt_iff_le_not_ge, embDomain_le_embDomain_iff_le]

end EmbDomain

end Zero

section MapDomain

variable [AddCommMonoid α]

/-
**Finsupp.mapDomain_le_mapDomain_iff_le** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：mapDomain_le_mapDomain_iff_le [LE α] [@Std.Refl α (· <= ·)] {f : ι -> κ} (
h : f.Injective) (g₁ g₂ : ι ->₀ α) : g₁.mapDomain f <= g₂.mapDomain f ↔ g₁ <= g₂
参数：· <= ·；h : f.Injective；g₁ g₂ : ι ->₀ α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finsupp.embDomain_eq_mapDomain`：embDomain_eq_mapDomain (f : α ↪ β) (v : 
α ->₀ M) : embDomain f v = mapDomain f v
· 使用引理 `Finsupp.embDomain_le_embDomain_iff_le`：embDomain_le_embDomain_iff_le [LE
 α] [@Std.Refl α (· <= ·)] (f : ι ↪ κ) (g₁ g₂ : ι ->₀ α) : g₁.embDomain f <= g₂.
embDomain f ↔ g₁ <= g₂
-/
lemma mapDomain_le_mapDomain_iff_le [LE α] [@Std.Refl α (· ≤ ·)] {f : ι → κ} (h : f.Injective)
    (g₁ g₂ : ι →₀ α) : g₁.mapDomain f ≤ g₂.mapDomain f ↔ g₁ ≤ g₂ := by
  simpa [Finsupp.embDomain_eq_mapDomain] using Finsupp.embDomain_le_embDomain_iff_le ⟨f, h⟩ g₁ g₂
/-
**Finsupp.mapDomain_lt_mapDomain_iff_lt** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：mapDomain_lt_mapDomain_iff_lt [Preorder α] {f : ι -> κ} (h : f.Injective) 
(g₁ g₂ : ι ->₀ α) : g₁.mapDomain f < g₂.mapDomain f ↔ g₁ < g₂
参数：h : f.Injective；g₁ g₂ : ι ->₀ α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finsupp.embDomain_eq_mapDomain`：embDomain_eq_mapDomain (f : α ↪ β) (v : 
α ->₀ M) : embDomain f v = mapDomain f v
· 使用引理 `Finsupp.embDomain_lt_embDomain_iff_lt`：embDomain_lt_embDomain_iff_lt [Pr
eorder α] (f : ι ↪ κ) (g₁ g₂ : ι ->₀ α) : g₁.embDomain f < g₂.embDomain f ↔ g₁ <
 g₂
-/
lemma mapDomain_lt_mapDomain_iff_lt [Preorder α] {f : ι → κ} (h : f.Injective)
    (g₁ g₂ : ι →₀ α) : g₁.mapDomain f < g₂.mapDomain f ↔ g₁ < g₂ := by
  simpa [Finsupp.embDomain_eq_mapDomain] using Finsupp.embDomain_lt_embDomain_iff_lt ⟨f, h⟩ g₁ g₂

end MapDomain

/-! ### Algebraic order structures -/

section OrderedAddCommMonoid
variable [AddCommMonoid α] [Preorder α] [IsOrderedAddMonoid α]
  {i : ι} {f : ι → κ} {g g₁ g₂ : ι →₀ α}

/-
**Finsupp.isOrderedAddMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：isOrderedAddMonoid : IsOrderedAddMonoid (ι ->₀ α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `add_le_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [i : Ad
dRightMono α] {b c : α}, b ≤ c → ∀ (a : α), b + a ≤ c + a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
instance isOrderedAddMonoid : IsOrderedAddMonoid (ι →₀ α) :=
  { add_le_add_left := fun _a _b h c s => add_le_add_left (h s) (c s) }

@[gcongr]
/-
**Finsupp.mapDomain_mono** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：mapDomain_mono : Monotone (mapDomain f : (ι ->₀ α) -> (κ ->₀ α))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finsupp.sum_le_sum_index`：sum_le_sum_index [DecidableEq ι] {f₁ f₂ : ι ->
₀ α} {h : ι -> α -> β} (hf : f₁ <= f₂) (hh : forall i in f₁.support union f₂.sup
port, Monotone…
· 使用引理 `Finsupp.single_mono`：single_mono : Monotone (single i : α -> ι ->₀ α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.single_zero`：single_zero (a : α) : (single a 0 : α ->₀ M) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma mapDomain_mono : Monotone (mapDomain f : (ι →₀ α) → (κ →₀ α)) := by
  classical exact fun g₁ g₂ h ↦ sum_le_sum_index h (fun _ _ ↦ single_mono) (by simp)
/-
**Finsupp.mapDomain_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：mapDomain_nonneg (hg : 0 <= g) : 0 <= g.mapDomain f
参数：hg : 0 <= g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.mapDomain_zero`：mapDomain_zero {f : α -> β} : mapDomain f (0 : α
 ->₀ M) = (0 : β ->₀ M)
· 使用引理 `Finsupp.mapDomain_mono`：mapDomain_mono : Monotone (mapDomain f : (ι ->₀ 
α) -> (κ ->₀ α))
-/
lemma mapDomain_nonneg (hg : 0 ≤ g) : 0 ≤ g.mapDomain f := by simpa using mapDomain_mono hg
/-
**Finsupp.mapDomain_nonpos** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：mapDomain_nonpos (hg : g <= 0) : g.mapDomain f <= 0
参数：hg : g <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.mapDomain_zero`：mapDomain_zero {f : α -> β} : mapDomain f (0 : α
 ->₀ M) = (0 : β ->₀ M)
· 使用引理 `Finsupp.mapDomain_mono`：mapDomain_mono : Monotone (mapDomain f : (ι ->₀ 
α) -> (κ ->₀ α))
-/
lemma mapDomain_nonpos (hg : g ≤ 0) : g.mapDomain f ≤ 0 := by simpa using mapDomain_mono hg
/-
**Finsupp.single_le_sum** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：single_le_sum {α M N : Type*} [Zero M] [AddCommMonoid N] [PartialOrder N] 
[IsOrderedAddMonoid N] (f : α ->₀ M) {g : α -> M -> N} (h : 0 <= (g · ·)) (a : α
) : ((single a (f a)).sum g) <= f.sum g
参数：f : α ->₀ M；h : 0 <= (g · ·)；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.single_zero`：single_zero (a : α) : (single a 0 : α ->₀ M) = 0
· 使用定理 `Finsupp.sum_zero_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} 
[inst : Zero M] [inst_1 : AddCommMonoid N] {h : α → M → N},   Finsupp.sum 0 h = 
0
· 使用定理 `Finsupp.sum_nonneg'`：sum_nonneg' (h : forall i, 0 <= h₁ i (f i)) : 0 <= 
f.sum h₁
· 使用定理 `Finsupp.sum.eq_1`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [inst 
: Zero M] [inst_1 : AddCommMonoid N] (f : α →₀ M) (g : α → M → N),   f.sum g = ∑
 a ∈ f…
· 使用定理 `Finsupp.support_single`：∀ {α : Type u_1} {M : Type u_5} [inst : Zero M] 
{b : M} (a : α), b ≠ 0 → (fun₀ | a => b).support = {a}
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `Finset.single_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMon
oid N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i 
∈ s, 0 ≤ f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem single_le_sum {α M N : Type*} [Zero M] [AddCommMonoid N]
    [PartialOrder N] [IsOrderedAddMonoid N] (f : α →₀ M) {g : α → M → N}
    (h : 0 ≤ (g · ·)) (a : α) :
    ((single a (f a)).sum g) ≤ f.sum g := by
  rcases eq_or_ne (f a) 0 with H | H
  · rw [H, single_zero, sum_zero_index]
    exact sum_nonneg' (fun i ↦ h i (f i))
  · rw [sum, support_single _ H, sum_singleton, single_eq_same]
    apply Finset.single_le_sum (fun i hi ↦ h i (f i))
    simpa [mem_support_iff, ne_eq] using H
/-
**Finsupp.single_eval_le_sum** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：single_eval_le_sum {α M N : Type*} [Zero M] [AddCommMonoid N] [PartialOrde
r N] [IsOrderedAddMonoid N] (f : α ->₀ M) {g : M -> N} (hg : g 0 = 0) (h : 0 <= 
(g ·)) (a : α) : g (f a) <= f.sum fun _ m => g m
参数：f : α ->₀ M；hg : g 0 = 0；h : 0 <= (g ·)；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
· 使用定理 `Finsupp.single_le_sum`：single_le_sum {α M N : Type*} [Zero M] [AddCommMo
noid N] [PartialOrder N] [IsOrderedAddMonoid N] (f : α ->₀ M) {g : α -> M -> N} 
(h : 0 <= (…
-/
lemma single_eval_le_sum {α M N : Type*} [Zero M] [AddCommMonoid N] [PartialOrder N]
    [IsOrderedAddMonoid N] (f : α →₀ M) {g : M → N} (hg : g 0 = 0) (h : 0 ≤ (g ·)) (a : α) :
    g (f a) ≤ f.sum fun _ m ↦ g m := by
  simp only [← sum_single_index (h := fun (_ : α) m ↦ g m) (a := a) (b := f a) hg]
  apply single_le_sum _ (fun _ m ↦ h m)

end OrderedAddCommMonoid

/-
**Finsupp.isOrderedCancelAddMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：isOrderedCancelAddMonoid [AddCommMonoid α] [Preorder α] [IsOrderedCancelAd
dMonoid α] : IsOrderedCancelAddMonoid (ι ->₀ α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `le_of_add_le_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [
AddLeftReflectLE α] {a b c : α}, a + b ≤ a + c → b ≤ c
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
-/
instance isOrderedCancelAddMonoid [AddCommMonoid α] [Preorder α] [IsOrderedCancelAddMonoid α] :
    IsOrderedCancelAddMonoid (ι →₀ α) :=
  { le_of_add_le_add_left := fun _f _g _i h s => le_of_add_le_add_left (h s) }
/-
**Finsupp.addLeftReflectLE** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：addLeftReflectLE [AddCommMonoid α] [Preorder α] [AddLeftReflectLE α] : Add
LeftReflectLE (ι ->₀ α) where le_of_add_le_add_left H x
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_add_le_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [
AddLeftReflectLE α] {a b c : α}, a + b ≤ a + c → b ≤ c
-/
instance addLeftReflectLE [AddCommMonoid α] [Preorder α] [AddLeftReflectLE α] :
    AddLeftReflectLE (ι →₀ α) where
  le_of_add_le_add_left H x := le_of_add_le_add_left <| H x

section SMulZeroClass
variable [Zero α] [Preorder α] [Zero β] [Preorder β] [SMulZeroClass α β]

/-
**Finsupp.instPosSMulMono** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：instPosSMulMono [PosSMulMono α β] : PosSMulMono α (ι ->₀ β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `PosSMulMono.lift`：PosSMulMono.lift [PosSMulMono α γ] (hf : forall {b₁ b₂
}, f b₁ <= f b₂ ↔ b₁ <= b₂) (smul : forall (a : α) b, f (a • b) = a • f b) : Pos
SMulMo…
· 使用定理 `Finsupp.coe_le_coe`：∀ {ι : Type u_1} {M : Type u_2} [inst : Zero M] [ins
t_1 : LE M] {f g : ι →₀ M}, ⇑f ≤ ⇑g ↔ f ≤ g
· 使用定理 `Finsupp.coe_smul`：coe_smul [Zero M] [SMulZeroClass R M] (b : R) (v : α -
>₀ M) : ⇑(b • v) = b • ⇑v
-/
instance instPosSMulMono [PosSMulMono α β] : PosSMulMono α (ι →₀ β) :=
  PosSMulMono.lift _ coe_le_coe coe_smul
/-
**Finsupp.instSMulPosMono** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：instSMulPosMono [SMulPosMono α β] : SMulPosMono α (ι ->₀ β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `SMulPosMono.lift`：SMulPosMono.lift [SMulPosMono α γ] (hf : forall {b₁ b₂
}, f b₁ <= f b₂ ↔ b₁ <= b₂) (smul : forall (a : α) b, f (a • b) = a • f b) (zero
 : f 0…
· 使用定理 `Finsupp.coe_le_coe`：∀ {ι : Type u_1} {M : Type u_2} [inst : Zero M] [ins
t_1 : LE M] {f g : ι →₀ M}, ⇑f ≤ ⇑g ↔ f ≤ g
· 使用定理 `Finsupp.coe_smul`：coe_smul [Zero M] [SMulZeroClass R M] (b : R) (v : α -
>₀ M) : ⇑(b • v) = b • ⇑v
· 使用定理 `Finsupp.coe_zero`：∀ {α : Type u_1} {M : Type u_4} [inst : Zero M], ⇑0 = 
0
-/
instance instSMulPosMono [SMulPosMono α β] : SMulPosMono α (ι →₀ β) :=
  SMulPosMono.lift _ coe_le_coe coe_smul coe_zero
/-
**Finsupp.instPosSMulReflectLE** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：instPosSMulReflectLE [PosSMulReflectLE α β] : PosSMulReflectLE α (ι ->₀ β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `PosSMulReflectLE.lift`：PosSMulReflectLE.lift [PosSMulReflectLE α γ] (hf 
: forall {b₁ b₂}, f b₁ <= f b₂ ↔ b₁ <= b₂) (smul : forall (a : α) b, f (a • b) =
 a • f b) :…
· 使用定理 `Finsupp.coe_le_coe`：∀ {ι : Type u_1} {M : Type u_2} [inst : Zero M] [ins
t_1 : LE M] {f g : ι →₀ M}, ⇑f ≤ ⇑g ↔ f ≤ g
· 使用定理 `Finsupp.coe_smul`：coe_smul [Zero M] [SMulZeroClass R M] (b : R) (v : α -
>₀ M) : ⇑(b • v) = b • ⇑v
-/
instance instPosSMulReflectLE [PosSMulReflectLE α β] : PosSMulReflectLE α (ι →₀ β) :=
  PosSMulReflectLE.lift _ coe_le_coe coe_smul
/-
**Finsupp.instSMulPosReflectLE** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：instSMulPosReflectLE [SMulPosReflectLE α β] : SMulPosReflectLE α (ι ->₀ β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `SMulPosReflectLE.lift`：SMulPosReflectLE.lift [SMulPosReflectLE α γ] (hf 
: forall {b₁ b₂}, f b₁ <= f b₂ ↔ b₁ <= b₂) (smul : forall (a : α) b, f (a • b) =
 a • f b) (…
· 使用定理 `Finsupp.coe_le_coe`：∀ {ι : Type u_1} {M : Type u_2} [inst : Zero M] [ins
t_1 : LE M] {f g : ι →₀ M}, ⇑f ≤ ⇑g ↔ f ≤ g
· 使用定理 `Finsupp.coe_smul`：coe_smul [Zero M] [SMulZeroClass R M] (b : R) (v : α -
>₀ M) : ⇑(b • v) = b • ⇑v
· 使用定理 `Finsupp.coe_zero`：∀ {α : Type u_1} {M : Type u_4} [inst : Zero M], ⇑0 = 
0
-/
instance instSMulPosReflectLE [SMulPosReflectLE α β] : SMulPosReflectLE α (ι →₀ β) :=
  SMulPosReflectLE.lift _ coe_le_coe coe_smul coe_zero

end SMulZeroClass

section SMulWithZero
variable [Zero α] [PartialOrder α] [Zero β] [PartialOrder β] [SMulWithZero α β]

/-
**Finsupp.instPosSMulStrictMono** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：instPosSMulStrictMono [PosSMulStrictMono α β] : PosSMulStrictMono α (ι ->₀
 β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `PosSMulStrictMono.lift`：PosSMulStrictMono.lift [PosSMulStrictMono α γ] (
hf : forall {b₁ b₂}, f b₁ <= f b₂ ↔ b₁ <= b₂) (smul : forall (a : α) b, f (a • b
) = a • f b)…
· 使用定理 `Finsupp.coe_le_coe`：∀ {ι : Type u_1} {M : Type u_2} [inst : Zero M] [ins
t_1 : LE M] {f g : ι →₀ M}, ⇑f ≤ ⇑g ↔ f ≤ g
· 使用定理 `Finsupp.coe_smul`：coe_smul [Zero M] [SMulZeroClass R M] (b : R) (v : α -
>₀ M) : ⇑(b • v) = b • ⇑v
-/
instance instPosSMulStrictMono [PosSMulStrictMono α β] : PosSMulStrictMono α (ι →₀ β) :=
  PosSMulStrictMono.lift _ coe_le_coe coe_smul
/-
**Finsupp.instSMulPosStrictMono** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：instSMulPosStrictMono [SMulPosStrictMono α β] : SMulPosStrictMono α (ι ->₀
 β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `SMulPosStrictMono.lift`：SMulPosStrictMono.lift [SMulPosStrictMono α γ] (
hf : forall {b₁ b₂}, f b₁ <= f b₂ ↔ b₁ <= b₂) (smul : forall (a : α) b, f (a • b
) = a • f b)…
· 使用定理 `Finsupp.coe_le_coe`：∀ {ι : Type u_1} {M : Type u_2} [inst : Zero M] [ins
t_1 : LE M] {f g : ι →₀ M}, ⇑f ≤ ⇑g ↔ f ≤ g
· 使用定理 `Finsupp.coe_smul`：coe_smul [Zero M] [SMulZeroClass R M] (b : R) (v : α -
>₀ M) : ⇑(b • v) = b • ⇑v
· 使用定理 `Finsupp.coe_zero`：∀ {α : Type u_1} {M : Type u_4} [inst : Zero M], ⇑0 = 
0
-/
instance instSMulPosStrictMono [SMulPosStrictMono α β] : SMulPosStrictMono α (ι →₀ β) :=
  SMulPosStrictMono.lift _ coe_le_coe coe_smul coe_zero

-- `PosSMulReflectLT α (ι →₀ β)` already follows from the other instances
/-
**Finsupp.instSMulPosReflectLT** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：instSMulPosReflectLT [SMulPosReflectLT α β] : SMulPosReflectLT α (ι ->₀ β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `SMulPosReflectLT.lift`：SMulPosReflectLT.lift [SMulPosReflectLT α γ] (hf 
: forall {b₁ b₂}, f b₁ <= f b₂ ↔ b₁ <= b₂) (smul : forall (a : α) b, f (a • b) =
 a • f b) (…
· 使用定理 `Finsupp.coe_le_coe`：∀ {ι : Type u_1} {M : Type u_2} [inst : Zero M] [ins
t_1 : LE M] {f g : ι →₀ M}, ⇑f ≤ ⇑g ↔ f ≤ g
· 使用定理 `Finsupp.coe_smul`：coe_smul [Zero M] [SMulZeroClass R M] (b : R) (v : α -
>₀ M) : ⇑(b • v) = b • ⇑v
· 使用定理 `Finsupp.coe_zero`：∀ {α : Type u_1} {M : Type u_4} [inst : Zero M], ⇑0 = 
0
-/
instance instSMulPosReflectLT [SMulPosReflectLT α β] : SMulPosReflectLT α (ι →₀ β) :=
  SMulPosReflectLT.lift _ coe_le_coe coe_smul coe_zero

end SMulWithZero

section PartialOrder

variable [AddCommMonoid α] [PartialOrder α] {f g : ι →₀ α}

/-
**Finsupp.orderBot** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：orderBot [IsBotZeroClass α] : OrderBot (ι ->₀ α) where bot
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance orderBot [IsBotZeroClass α] : OrderBot (ι →₀ α) where
  bot := 0
  bot_le := by simp [le_def]
/-
**Finsupp.** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsBotZeroClass α] : IsBotZeroClass (ι →₀ α) where
  isBot_zero := isBot_bot

@[deprecated _root_.bot_eq_zero (since := "2026-05-07")]
/-
**Finsupp.bot_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_3} [inst : AddCommMonoid α] [inst_1 : Partial
Order α] [inst_2 : IsBotZeroClass α], ⊥ = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem bot_eq_zero [IsBotZeroClass α] : (⊥ : ι →₀ α) = 0 :=
  rfl

variable [CanonicallyOrderedAdd α]

@[simp]
/-
**Finsupp.add_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：add_eq_zero_iff (f g : ι ->₀ α) : f + g = 0 ↔ f = 0 ∧ g = 0
参数：f g : ι ->₀ α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem add_eq_zero_iff (f g : ι →₀ α) : f + g = 0 ↔ f = 0 ∧ g = 0 := by
  simp [DFunLike.ext_iff, forall_and]
/-
**Finsupp.le_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：le_iff' (f g : ι ->₀ α) {s : Finset ι} (hf : f.support subseteq s) : f <= 
g ↔ forall i in s, f i <= g i
参数：f g : ι ->₀ α；hf : f.support subseteq s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.notMem_support_iff`：notMem_support_iff {f : α ->₀ M} {a} : a ∉ f
.support ↔ f a = 0
-/
theorem le_iff' (f g : ι →₀ α) {s : Finset ι} (hf : f.support ⊆ s) :
    f ≤ g ↔ ∀ i ∈ s, f i ≤ g i := by
  refine ⟨fun h s _ ↦ h s, fun h s ↦ ?_⟩
  by_cases H : s ∈ f.support
  · exact h s (hf H)
  · exact notMem_support_iff.1 H ▸ zero_le
/-
**Finsupp.le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：le_iff (f g : ι ->₀ α) : f <= g ↔ forall i in f.support, f i <= g i
参数：f g : ι ->₀ α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.le_iff'`：le_iff' (f g : ι ->₀ α) {s : Finset ι} (hf : f.support 
subseteq s) : f <= g ↔ forall i in s, f i <= g i
· 使用定理 `Finset.Subset.refl`：∀ {α : Type u_1} (s : Finset α), s ⊆ s
-/
theorem le_iff (f g : ι →₀ α) : f ≤ g ↔ ∀ i ∈ f.support, f i ≤ g i :=
  le_iff' f g <| Subset.refl _
/-
**Finsupp.support_monotone** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：support_monotone : Monotone (support (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.mem_support_iff`：mem_support_iff {f : α ->₀ M} : forall {a : α},
 a in f.support ↔ f a != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
-/
lemma support_monotone : Monotone (support (α := ι) (M := α)) :=
  fun f g h a ha ↦ by rw [mem_support_iff, ← pos_iff_ne_zero] at ha ⊢; exact ha.trans_le (h _)
/-
**Finsupp.support_mono** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：support_mono (hfg : f <= g) : f.support subseteq g.support
参数：hfg : f <= g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finsupp.support_monotone`：support_monotone : Monotone (support (α
-/
lemma support_mono (hfg : f ≤ g) : f.support ⊆ g.support := support_monotone hfg
/-
**Finsupp.decidableLE** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：decidableLE [DecidableLE α] : DecidableLE (ι ->₀ α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableLE [DecidableLE α] : DecidableLE (ι →₀ α) := fun f g =>
  decidable_of_iff _ (le_iff f g).symm
/-
**Finsupp.decidableLT** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：decidableLT [DecidableLE α] : DecidableLT (ι ->₀ α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableLT [DecidableLE α] : DecidableLT (ι →₀ α) :=
  decidableLTOfDecidableLE

@[simp]
/-
**Finsupp.single_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：single_le_iff {i : ι} {x : α} {f : ι ->₀ α} : single i x <= f ↔ x <= f i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Finsupp.le_iff'`：le_iff' (f g : ι ->₀ α) {s : Finset ι} (hf : f.support 
subseteq s) : f <= g ↔ forall i in s, f i <= g i
· 使用定理 `Finsupp.support_single_subset`：support_single_subset : (single a b).supp
ort subseteq {a}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem single_le_iff {i : ι} {x : α} {f : ι →₀ α} : single i x ≤ f ↔ x ≤ f i :=
  (le_iff' _ _ support_single_subset).trans <| by simp

variable [Sub α] [OrderedSub α] {f g : ι →₀ α} {i : ι} {a b : α}

/-- This is called `tsub` for truncated subtraction, to distinguish it with subtraction in an
additive group. -/
/-
**Finsupp.tsub** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：tsub : Sub (ι ->₀ α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is called `tsub` for truncated subtraction, to distinguish it with subtract
ion in an
additive group.
-/
instance tsub : Sub (ι →₀ α) :=
  ⟨zipWith (fun m n => m - n) (tsub_self 0)⟩
/-
**Finsupp.orderedSub** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：orderedSub : OrderedSub (ι ->₀ α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `tsub_le_iff_right`：tsub_le_iff_right [LE α] [Add α] [Sub α] [OrderedSub 
α] {a b c : α} : a - b <= c ↔ a <= c + b
-/
instance orderedSub : OrderedSub (ι →₀ α) :=
  ⟨fun _n _m _k => forall_congr' fun _x => tsub_le_iff_right⟩
/-
**Finsupp.** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddLeftMono α] : CanonicallyOrderedAdd (ι →₀ α) where
  exists_add_of_le := fun {f g} h => ⟨g - f, ext fun x => (add_tsub_cancel_of_le <| h x).symm⟩
  le_add_self _ _ _ := le_add_self
  le_self_add := fun _f _g _x => le_self_add
/-
**Finsupp.coe_tsub** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_3} [inst : AddCommMonoid α] [inst_1 : Partial
Order α] [inst_2 : CanonicallyOrderedAdd α]   [inst_3 : Sub α] [inst_4 : Ordered
Sub α] (f g : ι →₀ α), ⇑(f - g) = ⇑f - ⇑g
参数：f g : ι →₀ α；f - g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_tsub (f g : ι →₀ α) : ⇑(f - g) = f - g := rfl
/-
**Finsupp.tsub_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：tsub_apply (f g : ι ->₀ α) (a : ι) : (f - g) a = f a - g a
参数：f g : ι ->₀ α；a : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tsub_apply (f g : ι →₀ α) (a : ι) : (f - g) a = f a - g a :=
  rfl

@[simp]
/-
**Finsupp.single_tsub** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：single_tsub : single i (a - b) = single i a - single i b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.tsub_apply`：tsub_apply (f g : ι ->₀ α) (a : ι) : (f - g) a = f a
 - g a
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `Finsupp.single_eq_of_ne`：single_eq_of_ne (h : a' != a) : (single a b : α
 ->₀ M) a' = 0
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
-/
theorem single_tsub : single i (a - b) = single i a - single i b := by
  ext j
  obtain rfl | h := eq_or_ne j i
  · rw [tsub_apply, single_eq_same, single_eq_same, single_eq_same]
  · rw [tsub_apply, single_eq_of_ne h, single_eq_of_ne h, single_eq_of_ne h, tsub_self]
/-
**Finsupp.support_tsub** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：support_tsub {f1 f2 : ι ->₀ α} : (f1 - f2).support subseteq f1.support
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
theorem support_tsub {f1 f2 : ι →₀ α} : (f1 - f2).support ⊆ f1.support := by
  simp +contextual only [subset_iff, tsub_eq_zero_iff_le, mem_support_iff,
    Ne, coe_tsub, Pi.sub_apply, not_imp_not, zero_le, imp_true_iff]
/-
**Finsupp.subset_support_tsub** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：subset_support_tsub [DecidableEq ι] {f1 f2 : ι ->₀ α} : f1.support \ f2.su
pport subseteq (f1 - f2).support
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem subset_support_tsub [DecidableEq ι] {f1 f2 : ι →₀ α} :
    f1.support \ f2.support ⊆ (f1 - f2).support := by
  simp +contextual [subset_iff]
/-
**Finsupp.mapDomain_tsub** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：mapDomain_tsub {f : ι -> κ} (h : f.Injective) (f1 f2 : ι ->₀ α) : (f1 - f2
).mapDomain f = f1.mapDomain f - f2.mapDomain f
参数：h : f.Injective；f1 f2 : ι ->₀ α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.mapDomain_of_notMem_range`：mapDomain_of_notMem_range {f : α -> β
} (x : α ->₀ M) (a : β) (h : a ∉ Set.range f) : mapDomain f x a = 0
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finsupp.mapDomain_apply`：∀ {α : Type u_1} {β : Type u_2} {M : Type u_5} 
[inst : AddCommMonoid M] {f : α → β},   Function.Injective f → ∀ (x : α →₀ M) (a
 : α), (Finsu…
-/
lemma mapDomain_tsub {f : ι → κ} (h : f.Injective) (f1 f2 : ι →₀ α) :
    (f1 - f2).mapDomain f = f1.mapDomain f - f2.mapDomain f := by
  ext y
  by_cases! hy : y ∉ Set.range f
  · simp [mapDomain_of_notMem_range _ _ hy]
  · obtain ⟨x, rfl⟩ := hy
    simp [mapDomain_apply h]
/-
**Finsupp.embDomain_tsub** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：embDomain_tsub (f : ι ↪ κ) (f1 f2 : ι ->₀ α) : (f1 - f2).embDomain f = f1.
embDomain f - f2.embDomain f
参数：f : ι ↪ κ；f1 f2 : ι ->₀ α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.embDomain_eq_mapDomain`：embDomain_eq_mapDomain (f : α ↪ β) (v : 
α ->₀ M) : embDomain f v = mapDomain f v
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Finsupp.mapDomain_tsub`：mapDomain_tsub {f : ι -> κ} (h : f.Injective) (f
1 f2 : ι ->₀ α) : (f1 - f2).mapDomain f = f1.mapDomain f - f2.mapDomain f
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma embDomain_tsub (f : ι ↪ κ) (f1 f2 : ι →₀ α) :
    (f1 - f2).embDomain f = f1.embDomain f - f2.embDomain f := by
  simp_rw [embDomain_eq_mapDomain, mapDomain_tsub f.injective]

/-- The support of a sum is the union of the supports, when the coefficients satisfy
`CanonicallyOrderedAdd`.

In the case where the supports are disjoint, there is also `Finsupp.support_add_eq`,
which holds in any `AddZeroClass`. -/
/-
**Finsupp.support_add_eq_union** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：support_add_eq_union {f1 f2 : ι ->₀ α} [DecidableEq ι] : (f1 + f2).support
 = f1.support union f2.support
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `Finsupp.support_add`：support_add [DecidableEq ι] : (g₁ + g₂).support sub
seteq g₁.support union g₂.support
· 使用定理 `Finset.union_subset`：union_subset (hs : s subseteq u) : t subseteq u -> 
s union t subseteq u
· 使用引理 `Finsupp.support_mono`：support_mono (hfg : f <= g) : f.support subseteq g
.support
· 使用定理 `le_self_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ a + b
· 使用定理 `Finsupp.instCanonicallyOrderedAddOfAddLeftMono`：∀ {ι : Type u_1} {α : Ty
pe u_3} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] [CanonicallyOrderedAd
d α]   [inst_3 : Sub α] [OrderedSub …
· 使用定理 `CanonicallyOrderedAdd.toAddLeftMono`：∀ {α : Type u} [inst : AddSemigroup
 α] [inst_1 : LE α] [CanonicallyOrderedAdd α], AddLeftMono α
· 使用定理 `le_add_self`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ b + a

--- 原说明 ---
The support of a sum is the union of the supports, when the coefficients satisfy
`CanonicallyOrderedAdd`.

In the case where the supports are disjoint, there is also `Finsupp.support_add_
eq`,
which holds in any `AddZeroClass`.
-/
lemma support_add_eq_union {f1 f2 : ι →₀ α} [DecidableEq ι] :
    (f1 + f2).support = f1.support ∪ f2.support :=
  le_antisymm support_add <| Finset.union_subset
    (support_mono le_self_add) (support_mono le_add_self)

end PartialOrder

section LinearOrder

variable [AddCommMonoid α] [LinearOrder α] [IsBotZeroClass α]

@[simp]
/-
**Finsupp.support_inf** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：support_inf [DecidableEq ι] (f g : ι ->₀ α) : (f ⊓ g).support = f.support 
inter g.support
参数：f g : ι ->₀ α。
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
theorem support_inf [DecidableEq ι] (f g : ι →₀ α) : (f ⊓ g).support = f.support ∩ g.support := by
  ext
  simp

@[simp]
/-
**Finsupp.support_sup** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：support_sup [DecidableEq ι] (f g : ι ->₀ α) : (f ⊔ g).support = f.support 
union g.support
参数：f g : ι ->₀ α。
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
theorem support_sup [DecidableEq ι] (f g : ι →₀ α) : (f ⊔ g).support = f.support ∪ g.support := by
  ext
  simp [imp_iff_not_or]

nonrec theorem disjoint_iff {f g : ι →₀ α} : Disjoint f g ↔ Disjoint f.support g.support := by
  classical
  simp [disjoint_iff, bot_eq_zero, ← Finsupp.support_eq_empty]

end LinearOrder

/-! ### Some lemmas about `ℕ` -/

section Nat

/-
**Finsupp.sub_single_one_add** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：sub_single_one_add {a : ι} {u u' : ι ->₀ Nat} (h : u a != 0) : u - single 
a 1 + u' = u + u' - single a 1
参数：h : u a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tsub_add_eq_add_tsub`：tsub_add_eq_add_tsub (h : b <= a) : a - b + c = a 
+ c - b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Finsupp.instCanonicallyOrderedAddOfAddLeftMono`：∀ {ι : Type u_1} {α : Ty
pe u_3} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] [CanonicallyOrderedAd
d α]   [inst_3 : Sub α] [OrderedSub …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finsupp.single_le_iff`：single_le_iff {i : ι} {x : α} {f : ι ->₀ α} : sin
gle i x <= f ↔ x <= f i
· 使用定理 `Nat.one_le_iff_ne_zero`：∀ {n : ℕ}, 1 ≤ n ↔ n ≠ 0
-/
theorem sub_single_one_add {a : ι} {u u' : ι →₀ ℕ} (h : u a ≠ 0) :
    u - single a 1 + u' = u + u' - single a 1 :=
  tsub_add_eq_add_tsub <| single_le_iff.mpr <| Nat.one_le_iff_ne_zero.mpr h
/-
**Finsupp.add_sub_single_one** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：add_sub_single_one {a : ι} {u u' : ι ->₀ Nat} (h : u' a != 0) : u + (u' - 
single a 1) = u + u' - single a 1
参数：h : u' a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_tsub_assoc_of_le`：add_tsub_assoc_of_le (h : c <= b) (a : α) : a + b 
- c = a + (b - c)
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Finsupp.instCanonicallyOrderedAddOfAddLeftMono`：∀ {ι : Type u_1} {α : Ty
pe u_3} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] [CanonicallyOrderedAd
d α]   [inst_3 : Sub α] [OrderedSub …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finsupp.single_le_iff`：single_le_iff {i : ι} {x : α} {f : ι ->₀ α} : sin
gle i x <= f ↔ x <= f i
· 使用定理 `Nat.one_le_iff_ne_zero`：∀ {n : ℕ}, 1 ≤ n ↔ n ≠ 0
-/
theorem add_sub_single_one {a : ι} {u u' : ι →₀ ℕ} (h : u' a ≠ 0) :
    u + (u' - single a 1) = u + u' - single a 1 :=
  (add_tsub_assoc_of_le (single_le_iff.mpr <| Nat.one_le_iff_ne_zero.mpr h) _).symm
/-
**Finsupp.sub_add_single_one_cancel** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：sub_add_single_one_cancel {u : ι ->₀ Nat} {i : ι} (h : u i != 0) : u - sin
gle i 1 + single i 1 = u
参数：h : u i != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.sub_single_one_add`：sub_single_one_add {a : ι} {u u' : ι ->₀ Nat
} (h : u a != 0) : u - single a 1 + u' = u + u' - single a 1
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
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
-/
lemma sub_add_single_one_cancel {u : ι →₀ ℕ} {i : ι} (h : u i ≠ 0) :
    u - single i 1 + single i 1 = u := by
  rw [sub_single_one_add h, add_tsub_cancel_right]
/-
**Finsupp.isLowerSet_range_embDomain** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：isLowerSet_range_embDomain (f : α ↪ β) : IsLowerSet ((Set.range (embDomain
 f)) : Set (β ->₀ Nat))
参数：f : α ↪ β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ExistsAddOfLE.exists_add_of_le`：∀ {α : Type u} {inst : Add α} {inst_1 : 
LE α} [self : ExistsAddOfLE α] {a b : α}, a ≤ b → ∃ c, b = a + c
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Finsupp.instCanonicallyOrderedAddOfAddLeftMono`：∀ {ι : Type u_1} {α : Ty
pe u_3} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] [CanonicallyOrderedAd
d α]   [inst_3 : Sub α] [OrderedSub …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finsupp.mem_range_embDomain_iff`：mem_range_embDomain_iff [AddCommMonoid 
M] (f : α ↪ β) (x : β ->₀ M) : x in Set.range (embDomain f) ↔ ↑x.support subsete
q Set.range f
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Set.preimage_range`：preimage_range (f : α -> β) : f ⁻¹' range f = univ
-/
theorem isLowerSet_range_embDomain (f : α ↪ β) :
    IsLowerSet ((Set.range (embDomain f)) : Set (β →₀ ℕ)) := by
  rintro _ y h ⟨z, rfl⟩
  obtain ⟨w, hw⟩ := exists_add_of_le h
  rw [mem_range_embDomain_iff]
  trans ↑(y + w).support
  · exact fun _ ↦ by simp; grind
  · simp [← hw]

end Nat

end Finsupp

