/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Finset.NAry
public import Mathlib.Data.Finset.Slice
public import Mathlib.Data.Set.Sups

/-!
# Set family operations

This file defines a few binary operations on `Finset α` for use in set family combinatorics.

## Main declarations

* `Finset.sups s t`: Finset of elements of the form `a ⊔ b` where `a ∈ s`, `b ∈ t`.
* `Finset.infs s t`: Finset of elements of the form `a ⊓ b` where `a ∈ s`, `b ∈ t`.
* `Finset.disjSups s t`: Finset of elements of the form `a ⊔ b` where `a ∈ s`, `b ∈ t` and `a`
  and `b` are disjoint.
* `Finset.diffs`: Finset of elements of the form `a \ b` where `a ∈ s`, `b ∈ t`.
* `Finset.compls`: Finset of elements of the form `aᶜ` where `a ∈ s`.

## Notation

We define the following notation in scope `FinsetFamily`:
* `s ⊻ t` for `Finset.sups`
* `s ⊼ t` for `Finset.infs`
* `s ○ t` for `Finset.disjSups s t`
* `s \\ t` for `Finset.diffs`
* `sᶜˢ` for `Finset.compls`

## References

[B. Bollobás, *Combinatorics*][bollobas1986]
-/

@[expose] public section

open Function

open SetFamily

variable {F α β : Type*}

namespace Finset

section Sups
variable [DecidableEq α] [DecidableEq β]
variable [SemilatticeSup α] [SemilatticeSup β] [FunLike F α β] [SupHomClass F α β]
variable (s s₁ s₂ t t₁ t₂ u v : Finset α)

/-- `s ⊻ t` is the finset of elements of the form `a ⊔ b` where `a ∈ s`, `b ∈ t`. -/
@[instance_reducible]
/-
**Finset.hasSups** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：{α : Type u_2} → [DecidableEq α] → [SemilatticeSup α] → HasSups (Finset α)
参数：Finset α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`s ⊻ t` is the finset of elements of the form `a ⊔ b` where `a ∈ s`, `b ∈ t`.
-/
protected def hasSups : HasSups (Finset α) :=
  ⟨image₂ (· ⊔ ·)⟩

scoped[FinsetFamily] attribute [instance] Finset.hasSups

open FinsetFamily

variable {s t} {a b c : α}

@[simp]
/-
**Finset.mem_sups** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_sups : c in s ⊻ t ↔ exists a in s, exists b in t, a ⊔ b = c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_sups : c ∈ s ⊻ t ↔ ∃ a ∈ s, ∃ b ∈ t, a ⊔ b = c := by simp [(· ⊻ ·)]

variable (s t)

@[simp, norm_cast]
/-
**Finset.coe_sups** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_sups : (↑(s ⊻ t) : Set α) = ↑s ⊻ ↑t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_image₂`：coe_image₂ (f : α -> β -> γ) (s : Finset α) (t : Fins
et β) : (image₂ f s t : Set γ) = Set.image2 f s t
-/
theorem coe_sups : (↑(s ⊻ t) : Set α) = ↑s ⊻ ↑t :=
  coe_image₂ _ _ _
/-
**Finset.card_sups_le** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_sups_le : #(s ⊻ t) <= #s * #t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_image₂_le`：card_image₂_le (f : α -> β -> γ) (s : Finset α) (
t : Finset β) : #(image₂ f s t) <= #s * #t
-/
theorem card_sups_le : #(s ⊻ t) ≤ #s * #t := card_image₂_le _ _ _
/-
**Finset.card_sups_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_sups_iff : #(s ⊻ t) = #s * #t ↔ (s ×ˢ t : Set (α × α)).InjOn fun x =>
 x.1 ⊔ x.2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_image₂_iff`：card_image₂_iff : #(image₂ f s t) = #s * #t ↔ (s
 ×ˢ t : Set (α × β)).InjOn fun x => f x.1 x.2
-/
theorem card_sups_iff : #(s ⊻ t) = #s * #t ↔ (s ×ˢ t : Set (α × α)).InjOn fun x => x.1 ⊔ x.2 :=
  card_image₂_iff

variable {s s₁ s₂ t t₁ t₂ u}
/-
**Finset.sup_mem_sups** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sup_mem_sups : a in s -> b in t -> a ⊔ b in s ⊻ t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_image₂_of_mem`：mem_image₂_of_mem (ha : a in s) (hb : b in t) 
: f a b in image₂ f s t
-/
theorem sup_mem_sups : a ∈ s → b ∈ t → a ⊔ b ∈ s ⊻ t :=
  mem_image₂_of_mem
/-
**Finset.sups_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sups_subset : s₁ subseteq s₂ -> t₁ subseteq t₂ -> s₁ ⊻ t₁ subseteq s₂ ⊻ t₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_subset`：image₂_subset (hs : s subseteq s') (ht : t subsete
q t') : image₂ f s t subseteq image₂ f s' t'
-/
theorem sups_subset : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ ⊻ t₁ ⊆ s₂ ⊻ t₂ :=
  image₂_subset
/-
**Finset.sups_subset_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sups_subset_left : t₁ subseteq t₂ -> s ⊻ t₁ subseteq s ⊻ t₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_subset_left`：image₂_subset_left (ht : t subseteq t') : ima
ge₂ f s t subseteq image₂ f s t'
-/
theorem sups_subset_left : t₁ ⊆ t₂ → s ⊻ t₁ ⊆ s ⊻ t₂ :=
  image₂_subset_left
/-
**Finset.sups_subset_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sups_subset_right : s₁ subseteq s₂ -> s₁ ⊻ t subseteq s₂ ⊻ t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_subset_right`：image₂_subset_right (hs : s subseteq s') : i
mage₂ f s t subseteq image₂ f s' t
-/
theorem sups_subset_right : s₁ ⊆ s₂ → s₁ ⊻ t ⊆ s₂ ⊻ t :=
  image₂_subset_right
/-
**Finset.image_subset_sups_left** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：image_subset_sups_left : b in t -> s.image (· ⊔ b) subseteq s ⊻ t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image_subset_image₂_left`：image_subset_image₂_left (hb : b in t) 
: s.image (fun a => f a b) subseteq image₂ f s t
-/
lemma image_subset_sups_left : b ∈ t → s.image (· ⊔ b) ⊆ s ⊻ t := image_subset_image₂_left
/-
**Finset.image_subset_sups_right** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：image_subset_sups_right : a in s -> t.image (a ⊔ ·) subseteq s ⊻ t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image_subset_image₂_right`：image_subset_image₂_right (ha : a in s
) : t.image (fun b => f a b) subseteq image₂ f s t
-/
lemma image_subset_sups_right : a ∈ s → t.image (a ⊔ ·) ⊆ s ⊻ t := image_subset_image₂_right
/-
**Finset.forall_sups_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：forall_sups_iff {p : α -> Prop} : (forall c in s ⊻ t, p c) ↔ forall a in s
, forall b in t, p (a ⊔ b)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.forall_mem_image₂`：forall_mem_image₂ {p : γ -> Prop} : (forall z 
in image₂ f s t, p z) ↔ forall x in s, forall y in t, p (f x y)
-/
theorem forall_sups_iff {p : α → Prop} : (∀ c ∈ s ⊻ t, p c) ↔ ∀ a ∈ s, ∀ b ∈ t, p (a ⊔ b) :=
  forall_mem_image₂

@[simp]
/-
**Finset.sups_subset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sups_subset_iff : s ⊻ t subseteq u ↔ forall a in s, forall b in t, a ⊔ b i
n u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_subset_iff`：image₂_subset_iff : image₂ f s t subseteq u ↔ 
forall x in s, forall y in t, f x y in u
-/
theorem sups_subset_iff : s ⊻ t ⊆ u ↔ ∀ a ∈ s, ∀ b ∈ t, a ⊔ b ∈ u :=
  image₂_subset_iff

@[simp]
/-
**Finset.sups_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sups_nonempty : (s ⊻ t).Nonempty ↔ s.Nonempty ∧ t.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_nonempty_iff`：image₂_nonempty_iff : (image₂ f s t).Nonempt
y ↔ s.Nonempty ∧ t.Nonempty
-/
theorem sups_nonempty : (s ⊻ t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image₂_nonempty_iff

@[aesop safe apply (rule_sets := [finsetNonempty])]
/-
**Finset.Nonempty.sups** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nonempty`。
形式化陈述：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : SemilatticeSup α] {s t :
 Finset α},   s.Nonempty → t.Nonempty → (s ⊻ t).Nonempty
参数：s ⊻ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nonempty.image₂`：∀ {α : Type u_1} {β : Type u_3} {γ : Type u_5} [
inst : DecidableEq γ] {f : α → β → γ} {s : Finset α} {t : Finset β},   s.Nonempt
y → t.Nonemp…
-/
protected theorem Nonempty.sups : s.Nonempty → t.Nonempty → (s ⊻ t).Nonempty :=
  Nonempty.image₂
/-
**Finset.Nonempty.of_sups_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nonempty`。
形式化陈述：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : SemilatticeSup α] {s t :
 Finset α}, (s ⊻ t).Nonempty → s.Nonempty
参数：s ⊻ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nonempty.of_image₂_left`：∀ {α : Type u_1} {β : Type u_3} {γ : Typ
e u_5} [inst : DecidableEq γ] {f : α → β → γ} {s : Finset α} {t : Finset β},   (
Finset.image₂ f s t)…
-/
theorem Nonempty.of_sups_left : (s ⊻ t).Nonempty → s.Nonempty :=
  Nonempty.of_image₂_left
/-
**Finset.Nonempty.of_sups_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nonempty`。
形式化陈述：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : SemilatticeSup α] {s t :
 Finset α}, (s ⊻ t).Nonempty → t.Nonempty
参数：s ⊻ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nonempty.of_image₂_right`：∀ {α : Type u_1} {β : Type u_3} {γ : Ty
pe u_5} [inst : DecidableEq γ] {f : α → β → γ} {s : Finset α} {t : Finset β},   
(Finset.image₂ f s t)…
-/
theorem Nonempty.of_sups_right : (s ⊻ t).Nonempty → t.Nonempty :=
  Nonempty.of_image₂_right

@[simp]
/-
**Finset.empty_sups** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：empty_sups : ∅ ⊻ t = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_empty_left`：image₂_empty_left : image₂ f ∅ t = ∅
-/
theorem empty_sups : ∅ ⊻ t = ∅ :=
  image₂_empty_left

@[simp]
/-
**Finset.sups_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sups_empty : s ⊻ ∅ = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_empty_right`：image₂_empty_right : image₂ f s ∅ = ∅
-/
theorem sups_empty : s ⊻ ∅ = ∅ :=
  image₂_empty_right

@[simp]
/-
**Finset.sups_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sups_eq_empty : s ⊻ t = ∅ ↔ s = ∅ ∨ t = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_eq_empty_iff`：image₂_eq_empty_iff : image₂ f s t = ∅ ↔ s =
 ∅ ∨ t = ∅
-/
theorem sups_eq_empty : s ⊻ t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image₂_eq_empty_iff
/-
**Finset.singleton_sups** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : SemilatticeSup α] {t : F
inset α} {a : α},   {a} ⊻ t = Finset.image (fun x => a ⊔ x) t
参数：fun x => a ⊔ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_singleton_left`：image₂_singleton_left : image₂ f {a} t = t
.image fun b => f a b
-/
@[simp] lemma singleton_sups : {a} ⊻ t = t.image (a ⊔ ·) := image₂_singleton_left
/-
**Finset.sups_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : SemilatticeSup α] {s : F
inset α} {b : α},   s ⊻ {b} = Finset.image (fun x => x ⊔ b) s
参数：fun x => x ⊔ b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_singleton_right`：image₂_singleton_right : image₂ f s {b} =
 s.image fun a => f a b
-/
@[simp] lemma sups_singleton : s ⊻ {b} = s.image (· ⊔ b) := image₂_singleton_right
/-
**Finset.singleton_sups_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：singleton_sups_singleton : ({a} ⊻ {b} : Finset α) = {a ⊔ b}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_singleton`：image₂_singleton : image₂ f {a} {b} = {f a b}
-/
theorem singleton_sups_singleton : ({a} ⊻ {b} : Finset α) = {a ⊔ b} :=
  image₂_singleton
/-
**Finset.sups_union_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sups_union_left : (s₁ union s₂) ⊻ t = s₁ ⊻ t union s₂ ⊻ t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_union_left`：image₂_union_left [DecidableEq α] : image₂ f (
s union s') t = image₂ f s t union image₂ f s' t
-/
theorem sups_union_left : (s₁ ∪ s₂) ⊻ t = s₁ ⊻ t ∪ s₂ ⊻ t :=
  image₂_union_left
/-
**Finset.sups_union_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sups_union_right : s ⊻ (t₁ union t₂) = s ⊻ t₁ union s ⊻ t₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_union_right`：image₂_union_right [DecidableEq β] : image₂ f
 s (t union t') = image₂ f s t union image₂ f s t'
-/
theorem sups_union_right : s ⊻ (t₁ ∪ t₂) = s ⊻ t₁ ∪ s ⊻ t₂ :=
  image₂_union_right
/-
**Finset.sups_inter_subset_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sups_inter_subset_left : (s₁ inter s₂) ⊻ t subseteq s₁ ⊻ t inter s₂ ⊻ t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_inter_subset_left`：image₂_inter_subset_left [DecidableEq α
] : image₂ f (s inter s') t subseteq image₂ f s t inter image₂ f s' t
-/
theorem sups_inter_subset_left : (s₁ ∩ s₂) ⊻ t ⊆ s₁ ⊻ t ∩ s₂ ⊻ t :=
  image₂_inter_subset_left
/-
**Finset.sups_inter_subset_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sups_inter_subset_right : s ⊻ (t₁ inter t₂) subseteq s ⊻ t₁ inter s ⊻ t₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_inter_subset_right`：image₂_inter_subset_right [DecidableEq
 β] : image₂ f s (t inter t') subseteq image₂ f s t inter image₂ f s t'
-/
theorem sups_inter_subset_right : s ⊻ (t₁ ∩ t₂) ⊆ s ⊻ t₁ ∩ s ⊻ t₂ :=
  image₂_inter_subset_right
/-
**Finset.subset_sups** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：subset_sups {s t : Set α} : ↑u subseteq s ⊻ t -> exists s' t' : Finset α, 
↑s' subseteq s ∧ ↑t' subseteq t ∧ u subseteq s' ⊻ t'
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.subset_set_image₂`：subset_set_image₂ {s : Set α} {t : Set β} (hu 
: ↑u subseteq image2 f s t) : exists (s' : Finset α) (t' : Finset β), ↑s' subset
eq s ∧ ↑t' sub…
-/
theorem subset_sups {s t : Set α} :
    ↑u ⊆ s ⊻ t → ∃ s' t' : Finset α, ↑s' ⊆ s ∧ ↑t' ⊆ t ∧ u ⊆ s' ⊻ t' :=
  subset_set_image₂
/-
**Finset.image_sups** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：image_sups (f : F) (s t : Finset α) : image f (s ⊻ t) = image f s ⊻ image 
f t
参数：f : F；s t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image_image₂_distrib`：image_image₂_distrib {g : γ -> δ} {f' : α' 
-> β' -> δ} {g₁ : α -> α'} {g₂ : β -> β'} (h_distrib : forall a b, g (f a b) = f
' (g₁ a) (g₂ b)) …
· 使用定理 `SupHomClass.map_sup`：∀ {F : Type u_6} {α : Type u_7} {β : Type u_8} {ins
t : Max α} {inst_1 : Max β} {inst_2 : FunLike F α β}   [self : SupHomClass F α β
] (f : F)…
-/
lemma image_sups (f : F) (s t : Finset α) : image f (s ⊻ t) = image f s ⊻ image f t :=
  image_image₂_distrib <| map_sup f
/-
**Finset.map_sups** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：map_sups (f : F) (hf) (s t : Finset α) : map ⟨f, hf⟩ (s ⊻ t) = map ⟨f, hf⟩
 s ⊻ map ⟨f, hf⟩ t
参数：f : F；hf；s t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.map_eq_image`：map_eq_image (f : α ↪ β) (s : Finset α) : s.map f =
 s.image f
· 使用引理 `Finset.image_sups`：image_sups (f : F) (s t : Finset α) : image f (s ⊻ t)
 = image f s ⊻ image f t
-/
lemma map_sups (f : F) (hf) (s t : Finset α) :
    map ⟨f, hf⟩ (s ⊻ t) = map ⟨f, hf⟩ s ⊻ map ⟨f, hf⟩ t := by
  simpa [map_eq_image] using image_sups f s t
/-
**Finset.subset_sups_self** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：subset_sups_self : s subseteq s ⊻ s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_sups`：mem_sups : c in s ⊻ t ↔ exists a in s, exists b in t, a
 ⊔ b = c
· 使用定理 `sup_idem`：sup_idem (a : α) : a ⊔ a = a
-/
lemma subset_sups_self : s ⊆ s ⊻ s := fun _a ha ↦ mem_sups.2 ⟨_, ha, _, ha, sup_idem _⟩
/-
**Finset.sups_subset_self** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：sups_subset_self : s ⊻ s subseteq s ↔ SupClosed (s : Set α)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sups_subset_iff`：sups_subset_iff : s ⊻ t subseteq u ↔ forall a in
 s, forall b in t, a ⊔ b in u
-/
lemma sups_subset_self : s ⊻ s ⊆ s ↔ SupClosed (s : Set α) := sups_subset_iff
/-
**Finset.sups_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : SemilatticeSup α] {s : F
inset α}, s ⊻ s = s ↔ SupClosed ↑s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_sups`：coe_sups : (↑(s ⊻ t) : Set α) = ↑s ⊻ ↑t
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma sups_eq_self : s ⊻ s = s ↔ SupClosed (s : Set α) := by simp [← coe_inj]
/-
**Finset.univ_sups_univ** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : SemilatticeSup α] [inst_
2 : Fintype α],   Finset.univ ⊻ Finset.univ = Finset.univ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
-/
@[simp] lemma univ_sups_univ [Fintype α] : (univ : Finset α) ⊻ univ = univ := by simp
/-
**Finset.filter_sups_le** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：filter_sups_le [DecidableLE α] (s t : Finset α) (a : α) : {b in s ⊻ t | b 
<= a} = {b in s | b <= a} ⊻ {b in t | b <= a}
参数：s t : Finset α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_filter`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePred
 p] (s : Finset α), ↑(Finset.filter p s) = {x | x ∈ s ∧ p x}
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_sups`：coe_sups : (↑(s ⊻ t) : Set α) = ↑s ⊻ ↑t
· 使用引理 `Set.sep_sups_le`：sep_sups_le (s t : Set α) (a : α) : {b in s ⊻ t | b <= 
a} = {b in s | b <= a} ⊻ {b in t | b <= a}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma filter_sups_le [DecidableLE α] (s t : Finset α) (a : α) :
    {b ∈ s ⊻ t | b ≤ a} = {b ∈ s | b ≤ a} ⊻ {b ∈ t | b ≤ a} := by
  simp only [← coe_inj, coe_filter, coe_sups, ← mem_coe, Set.sep_sups_le]

variable (s t u)
/-
**Finset.biUnion_image_sup_left** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：biUnion_image_sup_left : s.biUnion (fun a => t.image (a ⊔ ·)) = s ⊻ t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.biUnion_image_left`：biUnion_image_left : (s.biUnion fun a => t.im
age <| f a) = image₂ f s t
-/
lemma biUnion_image_sup_left : s.biUnion (fun a ↦ t.image (a ⊔ ·)) = s ⊻ t := biUnion_image_left
/-
**Finset.biUnion_image_sup_right** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：biUnion_image_sup_right : t.biUnion (fun b => s.image (· ⊔ b)) = s ⊻ t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.biUnion_image_right`：biUnion_image_right : (t.biUnion fun b => s.
image fun a => f a b) = image₂ f s t
-/
lemma biUnion_image_sup_right : t.biUnion (fun b ↦ s.image (· ⊔ b)) = s ⊻ t := biUnion_image_right
/-
**Finset.image_sup_product** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_sup_product (s t : Finset α) : (s ×ˢ t).image (uncurry (· ⊔ ·)) = s 
⊻ t
参数：s t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image_uncurry_product`：image_uncurry_product (f : α -> β -> γ) (s
 : Finset α) (t : Finset β) : (s ×ˢ t).image (uncurry f) = image₂ f s t
-/
theorem image_sup_product (s t : Finset α) : (s ×ˢ t).image (uncurry (· ⊔ ·)) = s ⊻ t :=
  image_uncurry_product _ _ _
/-
**Finset.sups_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sups_assoc : s ⊻ t ⊻ u = s ⊻ (t ⊻ u)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_assoc`：image₂_assoc {γ : Type*} {u : Finset γ} {f : δ -> γ
 -> ε} {g : α -> β -> δ} {f' : α -> ε' -> ε} {g' : β -> γ -> ε'} (h_assoc : fora
ll a b c,…
· 使用定理 `sup_assoc`：sup_assoc (a b c : α) : a ⊔ b ⊔ c = a ⊔ (b ⊔ c)
-/
theorem sups_assoc : s ⊻ t ⊻ u = s ⊻ (t ⊻ u) := image₂_assoc sup_assoc
/-
**Finset.sups_comm** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sups_comm : s ⊻ t = t ⊻ s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_comm`：image₂_comm {g : β -> α -> γ} (h_comm : forall a b, 
f a b = g b a) : image₂ f s t = image₂ g t s
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
-/
theorem sups_comm : s ⊻ t = t ⊻ s := image₂_comm sup_comm
/-
**Finset.sups_left_comm** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sups_left_comm : s ⊻ (t ⊻ u) = t ⊻ (s ⊻ u)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_left_comm`：image₂_left_comm {γ : Type*} {u : Finset γ} {f 
: α -> δ -> ε} {g : β -> γ -> δ} {f' : α -> γ -> δ'} {g' : β -> δ' -> ε} (h_left
_comm : foral…
· 使用定理 `sup_left_comm`：sup_left_comm (a b c : α) : a ⊔ (b ⊔ c) = b ⊔ (a ⊔ c)
-/
theorem sups_left_comm : s ⊻ (t ⊻ u) = t ⊻ (s ⊻ u) :=
  image₂_left_comm sup_left_comm
/-
**Finset.sups_right_comm** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sups_right_comm : s ⊻ t ⊻ u = s ⊻ u ⊻ t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_right_comm`：image₂_right_comm {γ : Type*} {u : Finset γ} {
f : δ -> γ -> ε} {g : α -> β -> δ} {f' : α -> γ -> δ'} {g' : δ' -> β -> ε} (h_ri
ght_comm : for…
· 使用定理 `sup_right_comm`：sup_right_comm (a b c : α) : a ⊔ b ⊔ c = a ⊔ c ⊔ b
-/
theorem sups_right_comm : s ⊻ t ⊻ u = s ⊻ u ⊻ t :=
  image₂_right_comm sup_right_comm
/-
**Finset.sups_sups_sups_comm** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sups_sups_sups_comm : s ⊻ t ⊻ (u ⊻ v) = s ⊻ u ⊻ (t ⊻ v)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_image₂_image₂_comm`：image₂_image₂_image₂_comm {γ δ : Type*
} {u : Finset γ} {v : Finset δ} [DecidableEq ζ] [DecidableEq ζ'] [DecidableEq ν]
 {f : ε -> ζ -> ν} {g …
· 使用定理 `sup_sup_sup_comm`：sup_sup_sup_comm (a b c d : α) : a ⊔ b ⊔ (c ⊔ d) = a ⊔
 c ⊔ (b ⊔ d)
-/
theorem sups_sups_sups_comm : s ⊻ t ⊻ (u ⊻ v) = s ⊻ u ⊻ (t ⊻ v) :=
  image₂_image₂_image₂_comm sup_sup_sup_comm

end Sups

section Infs
variable [DecidableEq α] [DecidableEq β]
variable [SemilatticeInf α] [SemilatticeInf β] [FunLike F α β] [InfHomClass F α β]
variable (s s₁ s₂ t t₁ t₂ u v : Finset α)

/-- `s ⊼ t` is the finset of elements of the form `a ⊓ b` where `a ∈ s`, `b ∈ t`. -/
@[instance_reducible]
/-
**Finset.hasInfs** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：{α : Type u_2} → [DecidableEq α] → [SemilatticeInf α] → HasInfs (Finset α)
参数：Finset α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`s ⊼ t` is the finset of elements of the form `a ⊓ b` where `a ∈ s`, `b ∈ t`.
-/
protected def hasInfs : HasInfs (Finset α) :=
  ⟨image₂ (· ⊓ ·)⟩

scoped[FinsetFamily] attribute [instance] Finset.hasInfs

open FinsetFamily

variable {s t} {a b c : α}

@[simp]
/-
**Finset.mem_infs** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_infs : c in s ⊼ t ↔ exists a in s, exists b in t, a ⊓ b = c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_infs : c ∈ s ⊼ t ↔ ∃ a ∈ s, ∃ b ∈ t, a ⊓ b = c := by simp [(· ⊼ ·)]

variable (s t)

@[simp, norm_cast]
/-
**Finset.coe_infs** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_infs : (↑(s ⊼ t) : Set α) = ↑s ⊼ ↑t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_image₂`：coe_image₂ (f : α -> β -> γ) (s : Finset α) (t : Fins
et β) : (image₂ f s t : Set γ) = Set.image2 f s t
-/
theorem coe_infs : (↑(s ⊼ t) : Set α) = ↑s ⊼ ↑t :=
  coe_image₂ _ _ _
/-
**Finset.card_infs_le** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_infs_le : #(s ⊼ t) <= #s * #t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_image₂_le`：card_image₂_le (f : α -> β -> γ) (s : Finset α) (
t : Finset β) : #(image₂ f s t) <= #s * #t
-/
theorem card_infs_le : #(s ⊼ t) ≤ #s * #t := card_image₂_le _ _ _
/-
**Finset.card_infs_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_infs_iff : #(s ⊼ t) = #s * #t ↔ (s ×ˢ t : Set (α × α)).InjOn fun x =>
 x.1 ⊓ x.2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_image₂_iff`：card_image₂_iff : #(image₂ f s t) = #s * #t ↔ (s
 ×ˢ t : Set (α × β)).InjOn fun x => f x.1 x.2
-/
theorem card_infs_iff : #(s ⊼ t) = #s * #t ↔ (s ×ˢ t : Set (α × α)).InjOn fun x => x.1 ⊓ x.2 :=
  card_image₂_iff

variable {s s₁ s₂ t t₁ t₂ u}
/-
**Finset.inf_mem_infs** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inf_mem_infs : a in s -> b in t -> a ⊓ b in s ⊼ t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_image₂_of_mem`：mem_image₂_of_mem (ha : a in s) (hb : b in t) 
: f a b in image₂ f s t
-/
theorem inf_mem_infs : a ∈ s → b ∈ t → a ⊓ b ∈ s ⊼ t :=
  mem_image₂_of_mem
/-
**Finset.infs_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：infs_subset : s₁ subseteq s₂ -> t₁ subseteq t₂ -> s₁ ⊼ t₁ subseteq s₂ ⊼ t₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_subset`：image₂_subset (hs : s subseteq s') (ht : t subsete
q t') : image₂ f s t subseteq image₂ f s' t'
-/
theorem infs_subset : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ ⊼ t₁ ⊆ s₂ ⊼ t₂ :=
  image₂_subset
/-
**Finset.infs_subset_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：infs_subset_left : t₁ subseteq t₂ -> s ⊼ t₁ subseteq s ⊼ t₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_subset_left`：image₂_subset_left (ht : t subseteq t') : ima
ge₂ f s t subseteq image₂ f s t'
-/
theorem infs_subset_left : t₁ ⊆ t₂ → s ⊼ t₁ ⊆ s ⊼ t₂ :=
  image₂_subset_left
/-
**Finset.infs_subset_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：infs_subset_right : s₁ subseteq s₂ -> s₁ ⊼ t subseteq s₂ ⊼ t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_subset_right`：image₂_subset_right (hs : s subseteq s') : i
mage₂ f s t subseteq image₂ f s' t
-/
theorem infs_subset_right : s₁ ⊆ s₂ → s₁ ⊼ t ⊆ s₂ ⊼ t :=
  image₂_subset_right
/-
**Finset.image_subset_infs_left** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：image_subset_infs_left : b in t -> s.image (· ⊓ b) subseteq s ⊼ t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image_subset_image₂_left`：image_subset_image₂_left (hb : b in t) 
: s.image (fun a => f a b) subseteq image₂ f s t
-/
lemma image_subset_infs_left : b ∈ t → s.image (· ⊓ b) ⊆ s ⊼ t := image_subset_image₂_left
/-
**Finset.image_subset_infs_right** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：image_subset_infs_right : a in s -> t.image (a ⊓ ·) subseteq s ⊼ t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image_subset_image₂_right`：image_subset_image₂_right (ha : a in s
) : t.image (fun b => f a b) subseteq image₂ f s t
-/
lemma image_subset_infs_right : a ∈ s → t.image (a ⊓ ·) ⊆ s ⊼ t := image_subset_image₂_right
/-
**Finset.forall_infs_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：forall_infs_iff {p : α -> Prop} : (forall c in s ⊼ t, p c) ↔ forall a in s
, forall b in t, p (a ⊓ b)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.forall_mem_image₂`：forall_mem_image₂ {p : γ -> Prop} : (forall z 
in image₂ f s t, p z) ↔ forall x in s, forall y in t, p (f x y)
-/
theorem forall_infs_iff {p : α → Prop} : (∀ c ∈ s ⊼ t, p c) ↔ ∀ a ∈ s, ∀ b ∈ t, p (a ⊓ b) :=
  forall_mem_image₂

@[simp]
/-
**Finset.infs_subset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：infs_subset_iff : s ⊼ t subseteq u ↔ forall a in s, forall b in t, a ⊓ b i
n u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_subset_iff`：image₂_subset_iff : image₂ f s t subseteq u ↔ 
forall x in s, forall y in t, f x y in u
-/
theorem infs_subset_iff : s ⊼ t ⊆ u ↔ ∀ a ∈ s, ∀ b ∈ t, a ⊓ b ∈ u :=
  image₂_subset_iff

@[simp]
/-
**Finset.infs_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：infs_nonempty : (s ⊼ t).Nonempty ↔ s.Nonempty ∧ t.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_nonempty_iff`：image₂_nonempty_iff : (image₂ f s t).Nonempt
y ↔ s.Nonempty ∧ t.Nonempty
-/
theorem infs_nonempty : (s ⊼ t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image₂_nonempty_iff

@[aesop safe apply (rule_sets := [finsetNonempty])]
/-
**Finset.Nonempty.infs** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nonempty`。
形式化陈述：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : SemilatticeInf α] {s t :
 Finset α},   s.Nonempty → t.Nonempty → (s ⊼ t).Nonempty
参数：s ⊼ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nonempty.image₂`：∀ {α : Type u_1} {β : Type u_3} {γ : Type u_5} [
inst : DecidableEq γ] {f : α → β → γ} {s : Finset α} {t : Finset β},   s.Nonempt
y → t.Nonemp…
-/
protected theorem Nonempty.infs : s.Nonempty → t.Nonempty → (s ⊼ t).Nonempty :=
  Nonempty.image₂
/-
**Finset.Nonempty.of_infs_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nonempty`。
形式化陈述：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : SemilatticeInf α] {s t :
 Finset α}, (s ⊼ t).Nonempty → s.Nonempty
参数：s ⊼ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nonempty.of_image₂_left`：∀ {α : Type u_1} {β : Type u_3} {γ : Typ
e u_5} [inst : DecidableEq γ] {f : α → β → γ} {s : Finset α} {t : Finset β},   (
Finset.image₂ f s t)…
-/
theorem Nonempty.of_infs_left : (s ⊼ t).Nonempty → s.Nonempty :=
  Nonempty.of_image₂_left
/-
**Finset.Nonempty.of_infs_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nonempty`。
形式化陈述：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : SemilatticeInf α] {s t :
 Finset α}, (s ⊼ t).Nonempty → t.Nonempty
参数：s ⊼ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nonempty.of_image₂_right`：∀ {α : Type u_1} {β : Type u_3} {γ : Ty
pe u_5} [inst : DecidableEq γ] {f : α → β → γ} {s : Finset α} {t : Finset β},   
(Finset.image₂ f s t)…
-/
theorem Nonempty.of_infs_right : (s ⊼ t).Nonempty → t.Nonempty :=
  Nonempty.of_image₂_right

@[simp]
/-
**Finset.empty_infs** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：empty_infs : ∅ ⊼ t = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_empty_left`：image₂_empty_left : image₂ f ∅ t = ∅
-/
theorem empty_infs : ∅ ⊼ t = ∅ :=
  image₂_empty_left

@[simp]
/-
**Finset.infs_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：infs_empty : s ⊼ ∅ = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_empty_right`：image₂_empty_right : image₂ f s ∅ = ∅
-/
theorem infs_empty : s ⊼ ∅ = ∅ :=
  image₂_empty_right

@[simp]
/-
**Finset.infs_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：infs_eq_empty : s ⊼ t = ∅ ↔ s = ∅ ∨ t = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_eq_empty_iff`：image₂_eq_empty_iff : image₂ f s t = ∅ ↔ s =
 ∅ ∨ t = ∅
-/
theorem infs_eq_empty : s ⊼ t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image₂_eq_empty_iff
/-
**Finset.singleton_infs** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : SemilatticeInf α] {t : F
inset α} {a : α},   {a} ⊼ t = Finset.image (fun x => a ⊓ x) t
参数：fun x => a ⊓ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_singleton_left`：image₂_singleton_left : image₂ f {a} t = t
.image fun b => f a b
-/
@[simp] lemma singleton_infs : {a} ⊼ t = t.image (a ⊓ ·) := image₂_singleton_left
/-
**Finset.infs_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : SemilatticeInf α] {s : F
inset α} {b : α},   s ⊼ {b} = Finset.image (fun x => x ⊓ b) s
参数：fun x => x ⊓ b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_singleton_right`：image₂_singleton_right : image₂ f s {b} =
 s.image fun a => f a b
-/
@[simp] lemma infs_singleton : s ⊼ {b} = s.image (· ⊓ b) := image₂_singleton_right
/-
**Finset.singleton_infs_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：singleton_infs_singleton : ({a} ⊼ {b} : Finset α) = {a ⊓ b}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_singleton`：image₂_singleton : image₂ f {a} {b} = {f a b}
-/
theorem singleton_infs_singleton : ({a} ⊼ {b} : Finset α) = {a ⊓ b} :=
  image₂_singleton
/-
**Finset.infs_union_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：infs_union_left : (s₁ union s₂) ⊼ t = s₁ ⊼ t union s₂ ⊼ t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_union_left`：image₂_union_left [DecidableEq α] : image₂ f (
s union s') t = image₂ f s t union image₂ f s' t
-/
theorem infs_union_left : (s₁ ∪ s₂) ⊼ t = s₁ ⊼ t ∪ s₂ ⊼ t :=
  image₂_union_left
/-
**Finset.infs_union_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：infs_union_right : s ⊼ (t₁ union t₂) = s ⊼ t₁ union s ⊼ t₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_union_right`：image₂_union_right [DecidableEq β] : image₂ f
 s (t union t') = image₂ f s t union image₂ f s t'
-/
theorem infs_union_right : s ⊼ (t₁ ∪ t₂) = s ⊼ t₁ ∪ s ⊼ t₂ :=
  image₂_union_right
/-
**Finset.infs_inter_subset_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：infs_inter_subset_left : (s₁ inter s₂) ⊼ t subseteq s₁ ⊼ t inter s₂ ⊼ t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_inter_subset_left`：image₂_inter_subset_left [DecidableEq α
] : image₂ f (s inter s') t subseteq image₂ f s t inter image₂ f s' t
-/
theorem infs_inter_subset_left : (s₁ ∩ s₂) ⊼ t ⊆ s₁ ⊼ t ∩ s₂ ⊼ t :=
  image₂_inter_subset_left
/-
**Finset.infs_inter_subset_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：infs_inter_subset_right : s ⊼ (t₁ inter t₂) subseteq s ⊼ t₁ inter s ⊼ t₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_inter_subset_right`：image₂_inter_subset_right [DecidableEq
 β] : image₂ f s (t inter t') subseteq image₂ f s t inter image₂ f s t'
-/
theorem infs_inter_subset_right : s ⊼ (t₁ ∩ t₂) ⊆ s ⊼ t₁ ∩ s ⊼ t₂ :=
  image₂_inter_subset_right
/-
**Finset.subset_infs** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：subset_infs {s t : Set α} : ↑u subseteq s ⊼ t -> exists s' t' : Finset α, 
↑s' subseteq s ∧ ↑t' subseteq t ∧ u subseteq s' ⊼ t'
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.subset_set_image₂`：subset_set_image₂ {s : Set α} {t : Set β} (hu 
: ↑u subseteq image2 f s t) : exists (s' : Finset α) (t' : Finset β), ↑s' subset
eq s ∧ ↑t' sub…
-/
theorem subset_infs {s t : Set α} :
    ↑u ⊆ s ⊼ t → ∃ s' t' : Finset α, ↑s' ⊆ s ∧ ↑t' ⊆ t ∧ u ⊆ s' ⊼ t' :=
  subset_set_image₂
/-
**Finset.image_infs** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：image_infs (f : F) (s t : Finset α) : image f (s ⊼ t) = image f s ⊼ image 
f t
参数：f : F；s t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image_image₂_distrib`：image_image₂_distrib {g : γ -> δ} {f' : α' 
-> β' -> δ} {g₁ : α -> α'} {g₂ : β -> β'} (h_distrib : forall a b, g (f a b) = f
' (g₁ a) (g₂ b)) …
· 使用定理 `InfHomClass.map_inf`：∀ {F : Type u_6} {α : Type u_7} {β : Type u_8} {ins
t : Min α} {inst_1 : Min β} {inst_2 : FunLike F α β}   [self : InfHomClass F α β
] (f : F)…
-/
lemma image_infs (f : F) (s t : Finset α) : image f (s ⊼ t) = image f s ⊼ image f t :=
  image_image₂_distrib <| map_inf f
/-
**Finset.map_infs** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：map_infs (f : F) (hf) (s t : Finset α) : map ⟨f, hf⟩ (s ⊼ t) = map ⟨f, hf⟩
 s ⊼ map ⟨f, hf⟩ t
参数：f : F；hf；s t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.map_eq_image`：map_eq_image (f : α ↪ β) (s : Finset α) : s.map f =
 s.image f
· 使用引理 `Finset.image_infs`：image_infs (f : F) (s t : Finset α) : image f (s ⊼ t)
 = image f s ⊼ image f t
-/
lemma map_infs (f : F) (hf) (s t : Finset α) :
    map ⟨f, hf⟩ (s ⊼ t) = map ⟨f, hf⟩ s ⊼ map ⟨f, hf⟩ t := by
  simpa [map_eq_image] using image_infs f s t
/-
**Finset.subset_infs_self** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：subset_infs_self : s subseteq s ⊼ s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_infs`：mem_infs : c in s ⊼ t ↔ exists a in s, exists b in t, a
 ⊓ b = c
· 使用定理 `inf_idem`：∀ {α : Type u} [inst : SemilatticeInf α] (a : α), a ⊓ a = a
-/
lemma subset_infs_self : s ⊆ s ⊼ s := fun _a ha ↦ mem_infs.2 ⟨_, ha, _, ha, inf_idem _⟩
/-
**Finset.infs_self_subset** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：infs_self_subset : s ⊼ s subseteq s ↔ InfClosed (s : Set α)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.infs_subset_iff`：infs_subset_iff : s ⊼ t subseteq u ↔ forall a in
 s, forall b in t, a ⊓ b in u
-/
lemma infs_self_subset : s ⊼ s ⊆ s ↔ InfClosed (s : Set α) := infs_subset_iff
/-
**Finset.infs_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : SemilatticeInf α] {s : F
inset α}, s ⊼ s = s ↔ InfClosed ↑s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_infs`：coe_infs : (↑(s ⊼ t) : Set α) = ↑s ⊼ ↑t
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma infs_self : s ⊼ s = s ↔ InfClosed (s : Set α) := by simp [← coe_inj]
/-
**Finset.univ_infs_univ** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : SemilatticeInf α] [inst_
2 : Fintype α],   Finset.univ ⊼ Finset.univ = Finset.univ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
-/
@[simp] lemma univ_infs_univ [Fintype α] : (univ : Finset α) ⊼ univ = univ := by simp
/-
**Finset.filter_infs_le** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：filter_infs_le [DecidableLE α] (s t : Finset α) (a : α) : {b in s ⊼ t | a 
<= b} = {b in s | a <= b} ⊼ {b in t | a <= b}
参数：s t : Finset α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_filter`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePred
 p] (s : Finset α), ↑(Finset.filter p s) = {x | x ∈ s ∧ p x}
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_infs`：coe_infs : (↑(s ⊼ t) : Set α) = ↑s ⊼ ↑t
· 使用引理 `Set.sep_infs_le`：sep_infs_le (s t : Set α) (a : α) : {b in s ⊼ t | a <= 
b} = {b in s | a <= b} ⊼ {b in t | a <= b}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma filter_infs_le [DecidableLE α] (s t : Finset α) (a : α) :
    {b ∈ s ⊼ t | a ≤ b} = {b ∈ s | a ≤ b} ⊼ {b ∈ t | a ≤ b} := by
  simp only [← coe_inj, coe_filter, coe_infs, ← mem_coe, Set.sep_infs_le]

variable (s t u)
/-
**Finset.biUnion_image_inf_left** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：biUnion_image_inf_left : s.biUnion (fun a => t.image (a ⊓ ·)) = s ⊼ t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.biUnion_image_left`：biUnion_image_left : (s.biUnion fun a => t.im
age <| f a) = image₂ f s t
-/
lemma biUnion_image_inf_left : s.biUnion (fun a ↦ t.image (a ⊓ ·)) = s ⊼ t := biUnion_image_left
/-
**Finset.biUnion_image_inf_right** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：biUnion_image_inf_right : t.biUnion (fun b => s.image (· ⊓ b)) = s ⊼ t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.biUnion_image_right`：biUnion_image_right : (t.biUnion fun b => s.
image fun a => f a b) = image₂ f s t
-/
lemma biUnion_image_inf_right : t.biUnion (fun b ↦ s.image (· ⊓ b)) = s ⊼ t := biUnion_image_right
/-
**Finset.image_inf_product** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_inf_product (s t : Finset α) : (s ×ˢ t).image (uncurry (· ⊓ ·)) = s 
⊼ t
参数：s t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image_uncurry_product`：image_uncurry_product (f : α -> β -> γ) (s
 : Finset α) (t : Finset β) : (s ×ˢ t).image (uncurry f) = image₂ f s t
-/
theorem image_inf_product (s t : Finset α) : (s ×ˢ t).image (uncurry (· ⊓ ·)) = s ⊼ t :=
  image_uncurry_product _ _ _
/-
**Finset.infs_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：infs_assoc : s ⊼ t ⊼ u = s ⊼ (t ⊼ u)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_assoc`：image₂_assoc {γ : Type*} {u : Finset γ} {f : δ -> γ
 -> ε} {g : α -> β -> δ} {f' : α -> ε' -> ε} {g' : β -> γ -> ε'} (h_assoc : fora
ll a b c,…
· 使用定理 `inf_assoc`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c : α), a ⊓ b ⊓
 c = a ⊓ (b ⊓ c)
-/
theorem infs_assoc : s ⊼ t ⊼ u = s ⊼ (t ⊼ u) := image₂_assoc inf_assoc
/-
**Finset.infs_comm** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：infs_comm : s ⊼ t = t ⊼ s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_comm`：image₂_comm {g : β -> α -> γ} (h_comm : forall a b, 
f a b = g b a) : image₂ f s t = image₂ g t s
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
-/
theorem infs_comm : s ⊼ t = t ⊼ s := image₂_comm inf_comm
/-
**Finset.infs_left_comm** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：infs_left_comm : s ⊼ (t ⊼ u) = t ⊼ (s ⊼ u)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_left_comm`：image₂_left_comm {γ : Type*} {u : Finset γ} {f 
: α -> δ -> ε} {g : β -> γ -> δ} {f' : α -> γ -> δ'} {g' : β -> δ' -> ε} (h_left
_comm : foral…
· 使用定理 `inf_left_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c : α), a ⊓
 (b ⊓ c) = b ⊓ (a ⊓ c)
-/
theorem infs_left_comm : s ⊼ (t ⊼ u) = t ⊼ (s ⊼ u) :=
  image₂_left_comm inf_left_comm
/-
**Finset.infs_right_comm** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：infs_right_comm : s ⊼ t ⊼ u = s ⊼ u ⊼ t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_right_comm`：image₂_right_comm {γ : Type*} {u : Finset γ} {
f : δ -> γ -> ε} {g : α -> β -> δ} {f' : α -> γ -> δ'} {g' : δ' -> β -> ε} (h_ri
ght_comm : for…
· 使用定理 `inf_right_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c : α), a 
⊓ b ⊓ c = a ⊓ c ⊓ b
-/
theorem infs_right_comm : s ⊼ t ⊼ u = s ⊼ u ⊼ t :=
  image₂_right_comm inf_right_comm
/-
**Finset.infs_infs_infs_comm** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：infs_infs_infs_comm : s ⊼ t ⊼ (u ⊼ v) = s ⊼ u ⊼ (t ⊼ v)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_image₂_image₂_comm`：image₂_image₂_image₂_comm {γ δ : Type*
} {u : Finset γ} {v : Finset δ} [DecidableEq ζ] [DecidableEq ζ'] [DecidableEq ν]
 {f : ε -> ζ -> ν} {g …
· 使用定理 `inf_inf_inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c d : α)
, a ⊓ b ⊓ (c ⊓ d) = a ⊓ c ⊓ (b ⊓ d)
-/
theorem infs_infs_infs_comm : s ⊼ t ⊼ (u ⊼ v) = s ⊼ u ⊼ (t ⊼ v) :=
  image₂_image₂_image₂_comm inf_inf_inf_comm

end Infs

open FinsetFamily

section DistribLattice

variable [DecidableEq α]
variable [DistribLattice α] (s t u : Finset α)

/-
**Finset.sups_infs_subset_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sups_infs_subset_left : s ⊻ t ⊼ u subseteq (s ⊻ t) ⊼ (s ⊻ u)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_distrib_subset_left`：image₂_distrib_subset_left {γ : Type*
} {u : Finset γ} {f : α -> δ -> ε} {g : β -> γ -> δ} {f₁ : α -> β -> β'} {f₂ : α
 -> γ -> γ'} {g' : β' -…
· 使用定理 `sup_inf_left`：sup_inf_left (a b c : α) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c)
-/
theorem sups_infs_subset_left : s ⊻ t ⊼ u ⊆ (s ⊻ t) ⊼ (s ⊻ u) :=
  image₂_distrib_subset_left sup_inf_left
/-
**Finset.sups_infs_subset_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sups_infs_subset_right : t ⊼ u ⊻ s subseteq (t ⊻ s) ⊼ (u ⊻ s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_distrib_subset_right`：image₂_distrib_subset_right {γ : Typ
e*} {u : Finset γ} {f : δ -> γ -> ε} {g : α -> β -> δ} {f₁ : α -> γ -> α'} {f₂ :
 β -> γ -> β'} {g' : α' …
· 使用定理 `sup_inf_right`：sup_inf_right (a b c : α) : a ⊓ b ⊔ c = (a ⊔ c) ⊓ (b ⊔ c)
-/
theorem sups_infs_subset_right : t ⊼ u ⊻ s ⊆ (t ⊻ s) ⊼ (u ⊻ s) :=
  image₂_distrib_subset_right sup_inf_right
/-
**Finset.infs_sups_subset_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：infs_sups_subset_left : s ⊼ (t ⊻ u) subseteq s ⊼ t ⊻ s ⊼ u
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_distrib_subset_left`：image₂_distrib_subset_left {γ : Type*
} {u : Finset γ} {f : α -> δ -> ε} {g : β -> γ -> δ} {f₁ : α -> β -> β'} {f₂ : α
 -> γ -> γ'} {g' : β' -…
· 使用定理 `inf_sup_left`：inf_sup_left (a b c : α) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c
-/
theorem infs_sups_subset_left : s ⊼ (t ⊻ u) ⊆ s ⊼ t ⊻ s ⊼ u :=
  image₂_distrib_subset_left inf_sup_left
/-
**Finset.infs_sups_subset_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：infs_sups_subset_right : (t ⊻ u) ⊼ s subseteq t ⊼ s ⊻ u ⊼ s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_distrib_subset_right`：image₂_distrib_subset_right {γ : Typ
e*} {u : Finset γ} {f : δ -> γ -> ε} {g : α -> β -> δ} {f₁ : α -> γ -> α'} {f₂ :
 β -> γ -> β'} {g' : α' …
· 使用定理 `inf_sup_right`：inf_sup_right (a b c : α) : (a ⊔ b) ⊓ c = a ⊓ c ⊔ b ⊓ c
-/
theorem infs_sups_subset_right : (t ⊻ u) ⊼ s ⊆ t ⊼ s ⊻ u ⊼ s :=
  image₂_distrib_subset_right inf_sup_right

end DistribLattice

section Finset
variable [DecidableEq α]
variable {𝒜 ℬ : Finset (Finset α)} {s t : Finset α}

/-
**Finset.powerset_union** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : DecidableEq α] (s t : Finset α), (s ∪ t).powerset
 = s.powerset ⊻ t.powerset
参数：s t : Finset α；s ∪ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.inter_subset_left`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s₂
 : Finset α}, s₁ ∩ s₂ ⊆ s₁
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.union_inter_distrib_right`：union_inter_distrib_right (s t u : Fin
set α) : (s union t) inter u = s inter u union t inter u
· 使用定理 `Finset.inter_eq_right`：∀ {α : Type u_1} [inst : DecidableEq α] {s t : Fi
nset α}, t ∩ s = s ↔ s ⊆ t
· 使用定理 `Finset.union_subset_union`：union_subset_union (hsu : s subseteq u) (htv 
: t subseteq v) : s union t subseteq u union v
-/
@[simp] lemma powerset_union (s t : Finset α) : (s ∪ t).powerset = s.powerset ⊻ t.powerset := by
  ext u
  simp only [mem_sups, mem_powerset, sup_eq_union]
  refine ⟨fun h ↦ ⟨_, inter_subset_left (s₂ := u), _, inter_subset_left (s₂ := u), ?_⟩, ?_⟩
  · rwa [← union_inter_distrib_right, inter_eq_right]
  · rintro ⟨v, hv, w, hw, rfl⟩
    exact union_subset_union hv hw
/-
**Finset.powerset_inter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : DecidableEq α] (s t : Finset α), (s ∩ t).powerset
 = s.powerset ⊼ t.powerset
参数：s t : Finset α；s ∩ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.inter_subset_left`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s₂
 : Finset α}, s₁ ∩ s₂ ⊆ s₁
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.inter_inter_distrib_right`：inter_inter_distrib_right (s t u : Fin
set α) : s inter t inter u = s inter u inter (t inter u)
· 使用定理 `Finset.inter_eq_right`：∀ {α : Type u_1} [inst : DecidableEq α] {s t : Fi
nset α}, t ∩ s = s ↔ s ⊆ t
· 使用定理 `Finset.inter_subset_inter`：inter_subset_inter {x y s t : Finset α} (h : 
x subseteq y) (h' : s subseteq t) : x inter s subseteq y inter t
-/
@[simp] lemma powerset_inter (s t : Finset α) : (s ∩ t).powerset = s.powerset ⊼ t.powerset := by
  ext u
  simp only [mem_infs, mem_powerset, inf_eq_inter]
  refine ⟨fun h ↦ ⟨_, inter_subset_left (s₂ := u), _, inter_subset_left (s₂ := u), ?_⟩, ?_⟩
  · rwa [← inter_inter_distrib_right, inter_eq_right]
  · rintro ⟨v, hv, w, hw, rfl⟩
    exact inter_subset_inter hv hw
/-
**Finset.powerset_sups_powerset_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : DecidableEq α] (s : Finset α), s.powerset ⊻ s.pow
erset = s.powerset
参数：s : Finset α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.union_idempotent`：union_idempotent (s : Finset α) : s union s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma powerset_sups_powerset_self (s : Finset α) :
    s.powerset ⊻ s.powerset = s.powerset := by simp [← powerset_union]
/-
**Finset.powerset_infs_powerset_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : DecidableEq α] (s : Finset α), s.powerset ⊼ s.pow
erset = s.powerset
参数：s : Finset α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.inter_self`：inter_self (s : Finset α) : s inter s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma powerset_infs_powerset_self (s : Finset α) :
    s.powerset ⊼ s.powerset = s.powerset := by simp [← powerset_inter]
/-
**Finset.union_mem_sups** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：union_mem_sups : s in 𝒜 -> t in ℬ -> s union t in 𝒜 ⊻ ℬ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sup_mem_sups`：sup_mem_sups : a in s -> b in t -> a ⊔ b in s ⊻ t
-/
lemma union_mem_sups : s ∈ 𝒜 → t ∈ ℬ → s ∪ t ∈ 𝒜 ⊻ ℬ := sup_mem_sups
/-
**Finset.inter_mem_infs** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：inter_mem_infs : s in 𝒜 -> t in ℬ -> s inter t in 𝒜 ⊼ ℬ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.inf_mem_infs`：inf_mem_infs : a in s -> b in t -> a ⊓ b in s ⊼ t
-/
lemma inter_mem_infs : s ∈ 𝒜 → t ∈ ℬ → s ∩ t ∈ 𝒜 ⊼ ℬ := inf_mem_infs

end Finset

section DisjSups

variable [DecidableEq α]
variable [SemilatticeSup α] [OrderBot α] [DecidableRel (α := α) Disjoint]
  (s s₁ s₂ t t₁ t₂ u : Finset α)

/-- The finset of elements of the form `a ⊔ b` where `a ∈ s`, `b ∈ t` and `a` and `b` are disjoint.
-/
/-
**disjSups** 是 Mathlib 中的一个定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The finset of elements of the form `a ⊔ b` where `a ∈ s`, `b ∈ t` and `a` and `b
` are disjoint.
-/
def disjSups : Finset α := {ab ∈ s ×ˢ t | Disjoint ab.1 ab.2}.image fun ab => ab.1 ⊔ ab.2

@[inherit_doc]
scoped[FinsetFamily] infixl:74 " ○ " => Finset.disjSups

variable {s t u} {a b c : α}

@[simp]
/-
**mem_disjSups** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_disjSups : c ∈ s ○ t ↔ ∃ a ∈ s, ∃ b ∈ t, Disjoint a b ∧ a ⊔ b = c := by
  simp [disjSups, and_assoc]
/-
**disjSups_subset_sups** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem disjSups_subset_sups : s ○ t ⊆ s ⊻ t := by
  simp_rw [subset_iff, mem_sups, mem_disjSups]
  exact fun c ⟨a, b, ha, hb, _, hc⟩ => ⟨a, b, ha, hb, hc⟩

variable (s t)
/-
**card_disjSups_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem card_disjSups_le : #(s ○ t) ≤ #s * #t :=
  (card_le_card disjSups_subset_sups).trans <| card_sups_le _ _

variable {s s₁ s₂ t t₁ t₂}
/-
**disjSups_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem disjSups_subset (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) : s₁ ○ t₁ ⊆ s₂ ○ t₂ :=
  image_subset_image <| filter_subset_filter _ <| product_subset_product hs ht
/-
**disjSups_subset_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem disjSups_subset_left (ht : t₁ ⊆ t₂) : s ○ t₁ ⊆ s ○ t₂ :=
  disjSups_subset Subset.rfl ht
/-
**disjSups_subset_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem disjSups_subset_right (hs : s₁ ⊆ s₂) : s₁ ○ t ⊆ s₂ ○ t :=
  disjSups_subset hs Subset.rfl
/-
**forall_disjSups_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forall_disjSups_iff {p : α → Prop} :
    (∀ c ∈ s ○ t, p c) ↔ ∀ a ∈ s, ∀ b ∈ t, Disjoint a b → p (a ⊔ b) := by
  simp_rw [mem_disjSups]
  refine ⟨fun h a ha b hb hab => h _ ⟨_, ha, _, hb, hab, rfl⟩, ?_⟩
  rintro h _ ⟨a, ha, b, hb, hab, rfl⟩
  exact h _ ha _ hb hab

@[simp]
/-
**disjSups_subset_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem disjSups_subset_iff : s ○ t ⊆ u ↔ ∀ a ∈ s, ∀ b ∈ t, Disjoint a b → a ⊔ b ∈ u :=
  forall_disjSups_iff
/-
**Nonempty.of_disjSups_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Nonempty.of_disjSups_left : (s ○ t).Nonempty -> s.Nonempty
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Nonempty.of_disjSups_left : (s ○ t).Nonempty → s.Nonempty := by
  simp_rw [Finset.Nonempty, mem_disjSups]
  exact fun ⟨_, a, ha, _⟩ => ⟨a, ha⟩
/-
**Nonempty.of_disjSups_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Nonempty.of_disjSups_right : (s ○ t).Nonempty -> t.Nonempty
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Nonempty.of_disjSups_right : (s ○ t).Nonempty → t.Nonempty := by
  simp_rw [Finset.Nonempty, mem_disjSups]
  exact fun ⟨_, _, _, b, hb, _⟩ => ⟨b, hb⟩

@[simp]
/-
**disjSups_empty_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem disjSups_empty_left : ∅ ○ t = ∅ := by simp [disjSups]

@[simp]
/-
**disjSups_empty_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem disjSups_empty_right : s ○ ∅ = ∅ := by simp [disjSups]
/-
**disjSups_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem disjSups_singleton : ({a} ○ {b} : Finset α) = if Disjoint a b then {a ⊔ b} else ∅ := by
  split_ifs with h <;> simp [disjSups, filter_singleton, h]
/-
**disjSups_union_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem disjSups_union_left : (s₁ ∪ s₂) ○ t = s₁ ○ t ∪ s₂ ○ t := by
  simp [disjSups, filter_union, image_union]
/-
**disjSups_union_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem disjSups_union_right : s ○ (t₁ ∪ t₂) = s ○ t₁ ∪ s ○ t₂ := by
  simp [disjSups, filter_union, image_union]
/-
**disjSups_inter_subset_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem disjSups_inter_subset_left : (s₁ ∩ s₂) ○ t ⊆ s₁ ○ t ∩ s₂ ○ t := by
  simpa only [disjSups, inter_product, filter_inter_distrib] using image_inter_subset _ _ _
/-
**disjSups_inter_subset_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem disjSups_inter_subset_right : s ○ (t₁ ∩ t₂) ⊆ s ○ t₁ ∩ s ○ t₂ := by
  simpa only [disjSups, product_inter, filter_inter_distrib] using image_inter_subset _ _ _

variable (s t)
/-
**disjSups_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem disjSups_comm : s ○ t = t ○ s := by
  aesop (add simp disjoint_comm, simp sup_comm)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : @Std.Commutative (Finset α) (· ○ ·) := ⟨disjSups_comm⟩

end DisjSups

section DistribLattice

variable [DecidableEq α]
variable [DistribLattice α] [OrderBot α] [DecidableRel (α := α) Disjoint] (s t u v : Finset α)

/-
**disjSups_assoc** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem disjSups_assoc : ∀ s t u : Finset α, s ○ t ○ u = s ○ (t ○ u) := by
  refine (associative_of_commutative_of_le inferInstance ?_).assoc
  simp only [disjSups_subset_iff, mem_disjSups]
  rintro s t u _ ⟨a, ha, b, hb, hab, rfl⟩ c hc habc
  rw [disjoint_sup_left] at habc
  exact ⟨a, ha, _, ⟨b, hb, c, hc, habc.2, rfl⟩, hab.sup_right habc.1, (sup_assoc ..).symm⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : @Std.Associative (Finset α) (· ○ ·) := ⟨disjSups_assoc⟩
/-
**disjSups_left_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem disjSups_left_comm : s ○ (t ○ u) = t ○ (s ○ u) := by
  simp_rw [← disjSups_assoc, disjSups_comm s]
/-
**disjSups_right_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem disjSups_right_comm : s ○ t ○ u = s ○ u ○ t := by simp_rw [disjSups_assoc, disjSups_comm]
/-
**disjSups_disjSups_disjSups_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem disjSups_disjSups_disjSups_comm : s ○ t ○ (u ○ v) = s ○ u ○ (t ○ v) := by
  simp_rw [← disjSups_assoc, disjSups_right_comm]

end DistribLattice
section Diffs
variable [DecidableEq α]
variable [GeneralizedBooleanAlgebra α] (s s₁ s₂ t t₁ t₂ u : Finset α)

/-- `s \\ t` is the finset of elements of the form `a \ b` where `a ∈ s`, `b ∈ t`. -/
/-
**diffs** 是 Mathlib 中的一个定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`s \\ t` is the finset of elements of the form `a \ b` where `a ∈ s`, `b ∈ t`.
-/
def diffs : Finset α → Finset α → Finset α := image₂ (· \ ·)

@[inherit_doc]
scoped[FinsetFamily] infixl:74 " \\\\ " => Finset.diffs
  -- This notation is meant to have higher precedence than `\` and `⊓`, but still within the
  -- realm of other binary notation

variable {s t} {a b c : α}
/-
**mem_diffs** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mem_diffs : c ∈ s \\ t ↔ ∃ a ∈ s, ∃ b ∈ t, a \ b = c := by simp [(· \\ ·)]

variable (s t)
/-
**coe_diffs** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_diffs : (↑(s \\ t) : Set α) = Set.image2 (· \ ·) s t :=
  coe_image₂ _ _ _
/-
**card_diffs_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma card_diffs_le : #(s \\ t) ≤ #s * #t := card_image₂_le _ _ _
/-
**card_diffs_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma card_diffs_iff : #(s \\ t) = #s * #t ↔ (s ×ˢ t : Set (α × α)).InjOn fun x ↦ x.1 \ x.2 :=
  card_image₂_iff

variable {s s₁ s₂ t t₁ t₂ u}
/-
**sdiff_mem_diffs** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sdiff_mem_diffs : a ∈ s → b ∈ t → a \ b ∈ s \\ t := mem_image₂_of_mem
/-
**diffs_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma diffs_subset : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ \\ t₁ ⊆ s₂ \\ t₂ := image₂_subset
/-
**diffs_subset_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma diffs_subset_left : t₁ ⊆ t₂ → s \\ t₁ ⊆ s \\ t₂ := image₂_subset_left
/-
**diffs_subset_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma diffs_subset_right : s₁ ⊆ s₂ → s₁ \\ t ⊆ s₂ \\ t := image₂_subset_right
/-
**image_subset_diffs_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma image_subset_diffs_left : b ∈ t → s.image (· \ b) ⊆ s \\ t := image_subset_image₂_left
/-
**image_subset_diffs_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma image_subset_diffs_right : a ∈ s → t.image (a \ ·) ⊆ s \\ t := image_subset_image₂_right
/-
**forall_mem_diffs** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma forall_mem_diffs {p : α → Prop} : (∀ c ∈ s \\ t, p c) ↔ ∀ a ∈ s, ∀ b ∈ t, p (a \ b) :=
  forall_mem_image₂
/-
**diffs_subset_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma diffs_subset_iff : s \\ t ⊆ u ↔ ∀ a ∈ s, ∀ b ∈ t, a \ b ∈ u := image₂_subset_iff

@[simp]
/-
**diffs_nonempty** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma diffs_nonempty : (s \\ t).Nonempty ↔ s.Nonempty ∧ t.Nonempty := image₂_nonempty_iff

@[aesop safe apply (rule_sets := [finsetNonempty])]
/-
**Nonempty.diffs** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma Nonempty.diffs : s.Nonempty → t.Nonempty → (s \\ t).Nonempty := Nonempty.image₂
/-
**Nonempty.of_diffs_left** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：Nonempty.of_diffs_left : (s \\ t).Nonempty -> s.Nonempty
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Nonempty.of_diffs_left : (s \\ t).Nonempty → s.Nonempty := Nonempty.of_image₂_left
/-
**Nonempty.of_diffs_right** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：Nonempty.of_diffs_right : (s \\ t).Nonempty -> t.Nonempty
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Nonempty.of_diffs_right : (s \\ t).Nonempty → t.Nonempty := Nonempty.of_image₂_right
/-
**empty_sdiffs** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma empty_sdiffs : ∅ \\ t = ∅ := image₂_empty_left
/-
**diffs_empty** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma diffs_empty : s \\ ∅ = ∅ := image₂_empty_right
/-
**diffs_eq_empty** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma diffs_eq_empty : s \\ t = ∅ ↔ s = ∅ ∨ t = ∅ := image₂_eq_empty_iff

@[deprecated (since := "2026-06-03")] alias empty_diffs := empty_sdiffs
/-
**singleton_diffs** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma singleton_diffs : {a} \\ t = t.image (a \ ·) := image₂_singleton_left
/-
**diffs_singleton** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma diffs_singleton : s \\ {b} = s.image (· \ b) := image₂_singleton_right
/-
**singleton_diffs_singleton** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma singleton_diffs_singleton : ({a} \\ {b} : Finset α) = {a \ b} := image₂_singleton
/-
**diffs_union_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma diffs_union_left : (s₁ ∪ s₂) \\ t = s₁ \\ t ∪ s₂ \\ t := image₂_union_left
/-
**diffs_union_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma diffs_union_right : s \\ (t₁ ∪ t₂) = s \\ t₁ ∪ s \\ t₂ := image₂_union_right
/-
**diffs_inter_subset_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma diffs_inter_subset_left : (s₁ ∩ s₂) \\ t ⊆ s₁ \\ t ∩ s₂ \\ t := image₂_inter_subset_left
/-
**diffs_inter_subset_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma diffs_inter_subset_right : s \\ (t₁ ∩ t₂) ⊆ s \\ t₁ ∩ s \\ t₂ := image₂_inter_subset_right
/-
**subset_diffs** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma subset_diffs {s t : Set α} :
    ↑u ⊆ Set.image2 (· \ ·) s t → ∃ s' t' : Finset α, ↑s' ⊆ s ∧ ↑t' ⊆ t ∧ u ⊆ s' \\ t' :=
  subset_set_image₂

variable (s t u)
/-
**biUnion_image_sdiff_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma biUnion_image_sdiff_left : s.biUnion (fun a ↦ t.image (a \ ·)) = s \\ t := biUnion_image_left
/-
**biUnion_image_sdiff_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma biUnion_image_sdiff_right : t.biUnion (fun b ↦ s.image (· \ b)) = s \\ t :=
  biUnion_image_right
/-
**image_sdiff_product** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma image_sdiff_product (s t : Finset α) : (s ×ˢ t).image (uncurry (· \ ·)) = s \\ t :=
  image_uncurry_product _ _ _
/-
**diffs_right_comm** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma diffs_right_comm : s \\ t \\ u = s \\ u \\ t := image₂_right_comm sdiff_right_comm

end Diffs

section Compls
variable [BooleanAlgebra α] (s s₁ s₂ t : Finset α)

/-- `sᶜˢ` is the finset of elements of the form `aᶜ` where `a ∈ s`. -/
/-
**compls** 是 Mathlib 中的一个定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`sᶜˢ` is the finset of elements of the form `aᶜ` where `a ∈ s`.
-/
def compls : Finset α → Finset α := map ⟨compl, compl_injective⟩

@[inherit_doc]
scoped[FinsetFamily] postfix:max "ᶜˢ" => Finset.compls

variable {s t} {a : α}
/-
**mem_compls** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mem_compls : a ∈ sᶜˢ ↔ aᶜ ∈ s := by
  rw [Iff.comm, ← mem_map' ⟨compl, compl_injective⟩, Embedding.coeFn_mk, compl_compl, compls]

variable (s t)
/-
**image_compl** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma image_compl [DecidableEq α] : s.image compl = sᶜˢ := by simp [compls, map_eq_image]
/-
**coe_compls** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_compls : (↑sᶜˢ : Set α) = compl '' ↑s := coe_map _ _
/-
**card_compls** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma card_compls : #sᶜˢ = #s := card_map _

variable {s s₁ s₂ t}
/-
**compl_mem_compls** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma compl_mem_compls : a ∈ s → aᶜ ∈ sᶜˢ := mem_map_of_mem _
/-
**compls_subset_compls** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma compls_subset_compls : s₁ᶜˢ ⊆ s₂ᶜˢ ↔ s₁ ⊆ s₂ := map_subset_map
/-
**forall_mem_compls** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma forall_mem_compls {p : α → Prop} : (∀ a ∈ sᶜˢ, p a) ↔ ∀ a ∈ s, p aᶜ := forall_mem_map
/-
**exists_compls_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma exists_compls_iff {p : α → Prop} : (∃ a ∈ sᶜˢ, p a) ↔ ∃ a ∈ s, p aᶜ := by aesop
/-
**compls_compls** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma compls_compls (s : Finset α) : sᶜˢᶜˢ = s := by ext; simp
/-
**compls_subset_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma compls_subset_iff : sᶜˢ ⊆ t ↔ s ⊆ tᶜˢ := by rw [← compls_subset_compls, compls_compls]

@[simp]
/-
**compls_nonempty** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma compls_nonempty : sᶜˢ.Nonempty ↔ s.Nonempty := map_nonempty

protected alias ⟨Nonempty.of_compls, Nonempty.compls⟩ := compls_nonempty
attribute [aesop safe apply (rule_sets := [finsetNonempty])] Nonempty.compls
/-
**compls_empty** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma compls_empty : (∅ : Finset α)ᶜˢ = ∅ := map_empty _
/-
**compls_eq_empty** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma compls_eq_empty : sᶜˢ = ∅ ↔ s = ∅ := map_eq_empty
/-
**compls_singleton** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma compls_singleton (a : α) : {a}ᶜˢ = {aᶜ} := map_singleton _ _
/-
**compls_univ** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma compls_univ [Fintype α] : (univ : Finset α)ᶜˢ = univ := by ext; simp

variable [DecidableEq α]
/-
**compls_union** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma compls_union (s t : Finset α) : (s ∪ t)ᶜˢ = sᶜˢ ∪ tᶜˢ := map_union _ _
/-
**compls_inter** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma compls_inter (s t : Finset α) : (s ∩ t)ᶜˢ = sᶜˢ ∩ tᶜˢ := map_inter _ _
/-
**compls_infs** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma compls_infs (s t : Finset α) : (s ⊼ t)ᶜˢ = sᶜˢ ⊻ tᶜˢ := by
  simp_rw [← image_compl]; exact image_image₂_distrib fun _ _ ↦ compl_inf
/-
**compls_sups** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma compls_sups (s t : Finset α) : (s ⊻ t)ᶜˢ = sᶜˢ ⊼ tᶜˢ := by
  simp_rw [← image_compl]; exact image_image₂_distrib fun _ _ ↦ compl_sup
/-
**infs_compls_eq_diffs** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma infs_compls_eq_diffs (s t : Finset α) : s ⊼ tᶜˢ = s \\ t := by
  ext; simp [sdiff_eq]; aesop
/-
**compls_infs_eq_diffs** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma compls_infs_eq_diffs (s t : Finset α) : sᶜˢ ⊼ t = t \\ s := by
  rw [infs_comm, infs_compls_eq_diffs]
/-
**diffs_compls_eq_infs** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma diffs_compls_eq_infs (s t : Finset α) : s \\ tᶜˢ = s ⊼ t := by
  rw [← infs_compls_eq_diffs, compls_compls]

variable {α : Type*} [DecidableEq α] [Fintype α] {𝒜 : Finset (Finset α)} {n : ℕ}
/-
**_root_.Set.Sized.compls** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma _root_.Set.Sized.compls (h𝒜 : (𝒜 : Set (Finset α)).Sized n) :
    (𝒜ᶜˢ : Set (Finset α)).Sized (Fintype.card α - n) :=
  Finset.forall_mem_compls.2 <| fun s hs ↦ by rw [Finset.card_compl, h𝒜 hs]
/-
**sized_compls** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sized_compls (hn : n ≤ Fintype.card α) :
    (𝒜ᶜˢ : Set (Finset α)).Sized n ↔ (𝒜 : Set (Finset α)).Sized (Fintype.card α - n) where
  mp h𝒜 := by simpa using h𝒜.compls
  mpr h𝒜 := by simpa only [Nat.sub_sub_self hn] using h𝒜.compls

end Compls
end Finset

