/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yaël Dillies
-/
module

public import Mathlib.Data.Finset.NAry
public import Mathlib.Algebra.Group.Pointwise.Set.Finite

/-!
# Pointwise operations of finsets

This file defines pointwise algebraic operations on finsets.

## Main declarations

For finsets `s` and `t`:

* `s +ᵥ t` (`Finset.vadd`): Scalar addition, finset of all `x +ᵥ y` where `x ∈ s` and `y ∈ t`.
* `s • t` (`Finset.smul`): Scalar multiplication, finset of all `x • y` where `x ∈ s` and
  `y ∈ t`.
* `s -ᵥ t` (`Finset.vsub`): Scalar subtraction, finset of all `x -ᵥ y` where `x ∈ s` and
  `y ∈ t`.
* `a • s` (`Finset.smulFinset`): Scaling, finset of all `a • x` where `x ∈ s`.
* `a +ᵥ s` (`Finset.vaddFinset`): Translation, finset of all `a +ᵥ x` where `x ∈ s`.

For `α` a semigroup/monoid, `Finset α` is a semigroup/monoid.
As an unfortunate side effect, this means that `n • s`, where `n : ℕ`, is ambiguous between
pointwise scaling and repeated pointwise addition; the former has `(2 : ℕ) • {1, 2} = {2, 4}`, while
the latter has `(2 : ℕ) • {1, 2} = {2, 3, 4}`. See note [pointwise nat action].

## Implementation notes

We put all instances in the scope `Pointwise`, so that these instances are not available by
default. Note that we do not mark them as reducible (as argued by note [reducible non-instances])
since we expect the scope to be open whenever the instances are actually used (and making the
instances reducible changes the behavior of `simp`).

## Tags

finset multiplication, finset addition, pointwise addition, pointwise multiplication,
pointwise subtraction
-/

@[expose] public section

assert_not_exists Cardinal Finset.dens MonoidWithZero MulAction IsOrderedMonoid

open Function MulOpposite

open scoped Pointwise

variable {F α β γ : Type*}

namespace Finset

open scoped Pointwise

/-! ### Scalar addition/multiplication of finsets -/

section SMul
variable [DecidableEq β] [SMul α β] {s s₁ s₂ : Finset α} {t t₁ t₂ u : Finset β} {a : α} {b : β}

/-- The pointwise product of two finsets `s` and `t`: `s • t = {x • y | x ∈ s, y ∈ t}`. -/
@[to_additive (attr := instance_reducible)
/-- The pointwise sum of two finsets `s` and `t`: `s +ᵥ t = {x +ᵥ y | x ∈ s, y ∈ t}`. -/]
/-
**Finset.smul** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：{α : Type u_2} → {β : Type u_3} → [DecidableEq β] → [SMul α β] → SMul (Fin
set α) (Finset β)
参数：Finset α；Finset β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def smul : SMul (Finset α) (Finset β) := ⟨image₂ (· • ·)⟩

scoped[Pointwise] attribute [instance] Finset.smul Finset.vadd
/-
**Finset.smul_def** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : DecidableEq β] [inst_1 : SMul α β]
 {s : Finset α} {t : Finset β},   s • t = Finset.image (fun p => p.1 • p.2) (s ×
ˢ t)
参数：fun p => p.1 • p.2；s ×ˢ t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] lemma smul_def : s • t = (s ×ˢ t).image fun p : α × β => p.1 • p.2 := rfl

@[to_additive]
/-
**Finset.image_smul_product** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：image_smul_product : ((s ×ˢ t).image fun x : α × β => x.fst • x.snd) = s •
 t
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma image_smul_product : ((s ×ˢ t).image fun x : α × β => x.fst • x.snd) = s • t := rfl
/-
**Finset.mem_smul** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : DecidableEq β] [inst_1 : SMul α β]
 {s : Finset α} {t : Finset β} {x : β},   x ∈ s • t ↔ ∃ y ∈ s, ∃ z ∈ t, y • z = 
x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_image₂`：mem_image₂ : c in image₂ f s t ↔ exists a in s, exist
s b in t, f a b = c
-/
@[to_additive] lemma mem_smul {x : β} : x ∈ s • t ↔ ∃ y ∈ s, ∃ z ∈ t, y • z = x := mem_image₂

@[to_additive (attr := simp, norm_cast)]
/-
**Finset.coe_smul** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：coe_smul (s : Finset α) (t : Finset β) : ↑(s • t) = (s : Set α) • (t : Set
 β)
参数：s : Finset α；t : Finset β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_image₂`：coe_image₂ (f : α -> β -> γ) (s : Finset α) (t : Fins
et β) : (image₂ f s t : Set γ) = Set.image2 f s t
-/
lemma coe_smul (s : Finset α) (t : Finset β) : ↑(s • t) = (s : Set α) • (t : Set β) := coe_image₂ ..
/-
**Finset.smul_mem_smul** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : DecidableEq β] [inst_1 : SMul α β]
 {s : Finset α} {t : Finset β} {a : α}   {b : β}, a ∈ s → b ∈ t → a • b ∈ s • t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_image₂_of_mem`：mem_image₂_of_mem (ha : a in s) (hb : b in t) 
: f a b in image₂ f s t
-/
@[to_additive] lemma smul_mem_smul : a ∈ s → b ∈ t → a • b ∈ s • t := mem_image₂_of_mem
/-
**Finset.card_smul_le** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : DecidableEq β] [inst_1 : SMul α β]
 {s : Finset α} {t : Finset β},   (s • t).card ≤ s.card * t.card
参数：s • t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_image₂_le`：card_image₂_le (f : α -> β -> γ) (s : Finset α) (
t : Finset β) : #(image₂ f s t) <= #s * #t
-/
@[to_additive] lemma card_smul_le : #(s • t) ≤ #s * #t := card_image₂_le ..

@[to_additive (attr := simp)]
/-
**Finset.empty_smul** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：empty_smul (t : Finset β) : (∅ : Finset α) • t = ∅
参数：t : Finset β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_empty_left`：image₂_empty_left : image₂ f ∅ t = ∅
-/
lemma empty_smul (t : Finset β) : (∅ : Finset α) • t = ∅ := image₂_empty_left

@[to_additive (attr := simp)]
/-
**Finset.smul_empty** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：smul_empty (s : Finset α) : s • (∅ : Finset β) = ∅
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_empty_right`：image₂_empty_right : image₂ f s ∅ = ∅
-/
lemma smul_empty (s : Finset α) : s • (∅ : Finset β) = ∅ := image₂_empty_right

@[to_additive (attr := simp)]
/-
**Finset.smul_eq_empty** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：smul_eq_empty : s • t = ∅ ↔ s = ∅ ∨ t = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_eq_empty_iff`：image₂_eq_empty_iff : image₂ f s t = ∅ ↔ s =
 ∅ ∨ t = ∅
-/
lemma smul_eq_empty : s • t = ∅ ↔ s = ∅ ∨ t = ∅ := image₂_eq_empty_iff

@[to_additive (attr := simp)]
/-
**Finset.smul_nonempty_iff** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：smul_nonempty_iff : (s • t).Nonempty ↔ s.Nonempty ∧ t.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_nonempty_iff`：image₂_nonempty_iff : (image₂ f s t).Nonempt
y ↔ s.Nonempty ∧ t.Nonempty
-/
lemma smul_nonempty_iff : (s • t).Nonempty ↔ s.Nonempty ∧ t.Nonempty := image₂_nonempty_iff

@[to_additive (attr := aesop safe apply (rule_sets := [finsetNonempty]))]
/-
**Finset.Nonempty.smul** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nonempty`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : DecidableEq β] [inst_1 : SMul α β]
 {s : Finset α} {t : Finset β},   s.Nonempty → t.Nonempty → (s • t).Nonempty
参数：s • t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nonempty.image₂`：∀ {α : Type u_1} {β : Type u_3} {γ : Type u_5} [
inst : DecidableEq γ] {f : α → β → γ} {s : Finset α} {t : Finset β},   s.Nonempt
y → t.Nonemp…
-/
lemma Nonempty.smul : s.Nonempty → t.Nonempty → (s • t).Nonempty := .image₂
/-
**Finset.Nonempty.of_smul_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nonempty`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : DecidableEq β] [inst_1 : SMul α β]
 {s : Finset α} {t : Finset β},   (s • t).Nonempty → s.Nonempty
参数：s • t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nonempty.of_image₂_left`：∀ {α : Type u_1} {β : Type u_3} {γ : Typ
e u_5} [inst : DecidableEq γ] {f : α → β → γ} {s : Finset α} {t : Finset β},   (
Finset.image₂ f s t)…
-/
@[to_additive] lemma Nonempty.of_smul_left : (s • t).Nonempty → s.Nonempty := .of_image₂_left
/-
**Finset.Nonempty.of_smul_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nonempty`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : DecidableEq β] [inst_1 : SMul α β]
 {s : Finset α} {t : Finset β},   (s • t).Nonempty → t.Nonempty
参数：s • t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nonempty.of_image₂_right`：∀ {α : Type u_1} {β : Type u_3} {γ : Ty
pe u_5} [inst : DecidableEq γ] {f : α → β → γ} {s : Finset α} {t : Finset β},   
(Finset.image₂ f s t)…
-/
@[to_additive] lemma Nonempty.of_smul_right : (s • t).Nonempty → t.Nonempty := .of_image₂_right

@[to_additive]
/-
**Finset.smul_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：smul_singleton (b : β) : s • ({b} : Finset β) = s.image (· • b)
参数：b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_singleton_right`：image₂_singleton_right : image₂ f s {b} =
 s.image fun a => f a b
-/
lemma smul_singleton (b : β) : s • ({b} : Finset β) = s.image (· • b) := image₂_singleton_right

@[to_additive]
/-
**Finset.singleton_smul_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：singleton_smul_singleton (a : α) (b : β) : ({a} : Finset α) • ({b} : Finse
t β) = {a • b}
参数：a : α；b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_singleton`：image₂_singleton : image₂ f {a} {b} = {f a b}
-/
lemma singleton_smul_singleton (a : α) (b : β) : ({a} : Finset α) • ({b} : Finset β) = {a • b} :=
  image₂_singleton

@[to_additive (attr := mono, gcongr)]
/-
**Finset.smul_subset_smul** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：smul_subset_smul : s₁ subseteq s₂ -> t₁ subseteq t₂ -> s₁ • t₁ subseteq s₂
 • t₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_subset`：image₂_subset (hs : s subseteq s') (ht : t subsete
q t') : image₂ f s t subseteq image₂ f s' t'
-/
lemma smul_subset_smul : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ • t₁ ⊆ s₂ • t₂ := image₂_subset
/-
**Finset.smul_subset_smul_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : DecidableEq β] [inst_1 : SMul α β]
 {s : Finset α} {t₁ t₂ : Finset β},   t₁ ⊆ t₂ → s • t₁ ⊆ s • t₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_subset_left`：image₂_subset_left (ht : t subseteq t') : ima
ge₂ f s t subseteq image₂ f s t'
-/
@[to_additive] lemma smul_subset_smul_left : t₁ ⊆ t₂ → s • t₁ ⊆ s • t₂ := image₂_subset_left
/-
**Finset.smul_subset_smul_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : DecidableEq β] [inst_1 : SMul α β]
 {s₁ s₂ : Finset α} {t : Finset β},   s₁ ⊆ s₂ → s₁ • t ⊆ s₂ • t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_subset_right`：image₂_subset_right (hs : s subseteq s') : i
mage₂ f s t subseteq image₂ f s' t
-/
@[to_additive] lemma smul_subset_smul_right : s₁ ⊆ s₂ → s₁ • t ⊆ s₂ • t := image₂_subset_right
/-
**Finset.smul_subset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : DecidableEq β] [inst_1 : SMul α β]
 {s : Finset α} {t u : Finset β},   s • t ⊆ u ↔ ∀ a ∈ s, ∀ b ∈ t, a • b ∈ u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_subset_iff`：image₂_subset_iff : image₂ f s t subseteq u ↔ 
forall x in s, forall y in t, f x y in u
-/
@[to_additive] lemma smul_subset_iff : s • t ⊆ u ↔ ∀ a ∈ s, ∀ b ∈ t, a • b ∈ u := image₂_subset_iff

@[to_additive]
/-
**Finset.union_smul** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：union_smul [DecidableEq α] : (s₁ union s₂) • t = s₁ • t union s₂ • t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_union_left`：image₂_union_left [DecidableEq α] : image₂ f (
s union s') t = image₂ f s t union image₂ f s' t
-/
lemma union_smul [DecidableEq α] : (s₁ ∪ s₂) • t = s₁ • t ∪ s₂ • t := image₂_union_left

@[to_additive]
/-
**Finset.smul_union** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：smul_union : s • (t₁ union t₂) = s • t₁ union s • t₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_union_right`：image₂_union_right [DecidableEq β] : image₂ f
 s (t union t') = image₂ f s t union image₂ f s t'
-/
lemma smul_union : s • (t₁ ∪ t₂) = s • t₁ ∪ s • t₂ := image₂_union_right

@[to_additive]
/-
**Finset.inter_smul_subset** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：inter_smul_subset [DecidableEq α] : (s₁ inter s₂) • t subseteq s₁ • t inte
r s₂ • t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_inter_subset_left`：image₂_inter_subset_left [DecidableEq α
] : image₂ f (s inter s') t subseteq image₂ f s t inter image₂ f s' t
-/
lemma inter_smul_subset [DecidableEq α] : (s₁ ∩ s₂) • t ⊆ s₁ • t ∩ s₂ • t :=
  image₂_inter_subset_left

@[to_additive]
/-
**Finset.smul_inter_subset** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：smul_inter_subset : s • (t₁ inter t₂) subseteq s • t₁ inter s • t₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_inter_subset_right`：image₂_inter_subset_right [DecidableEq
 β] : image₂ f s (t inter t') subseteq image₂ f s t inter image₂ f s t'
-/
lemma smul_inter_subset : s • (t₁ ∩ t₂) ⊆ s • t₁ ∩ s • t₂ := image₂_inter_subset_right

@[to_additive]
/-
**Finset.inter_smul_union_subset_union** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：inter_smul_union_subset_union [DecidableEq α] : (s₁ inter s₂) • (t₁ union 
t₂) subseteq s₁ • t₁ union s₂ • t₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_inter_union_subset_union`：image₂_inter_union_subset_union 
: image₂ f (s inter s') (t union t') subseteq image₂ f s t union image₂ f s' t'
-/
lemma inter_smul_union_subset_union [DecidableEq α] : (s₁ ∩ s₂) • (t₁ ∪ t₂) ⊆ s₁ • t₁ ∪ s₂ • t₂ :=
  image₂_inter_union_subset_union

@[to_additive]
/-
**Finset.union_smul_inter_subset_union** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：union_smul_inter_subset_union [DecidableEq α] : (s₁ union s₂) • (t₁ inter 
t₂) subseteq s₁ • t₁ union s₂ • t₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_union_inter_subset_union`：image₂_union_inter_subset_union 
: image₂ f (s union s') (t inter t') subseteq image₂ f s t union image₂ f s' t'
-/
lemma union_smul_inter_subset_union [DecidableEq α] : (s₁ ∪ s₂) • (t₁ ∩ t₂) ⊆ s₁ • t₁ ∪ s₂ • t₂ :=
  image₂_union_inter_subset_union

/-- If a finset `u` is contained in the scalar product of two sets `s • t`, we can find two finsets
`s'`, `t'` such that `s' ⊆ s`, `t' ⊆ t` and `u ⊆ s' • t'`. -/
@[to_additive
/-- If a finset `u` is contained in the scalar sum of two sets `s +ᵥ t`, we can find two
finsets `s'`, `t'` such that `s' ⊆ s`, `t' ⊆ t` and `u ⊆ s' +ᵥ t'`. -/]
/-
**Finset.subset_smul** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：subset_smul {s : Set α} {t : Set β} : ↑u subseteq s • t -> exists (s' : Fi
nset α) (t' : Finset β), ↑s' subseteq s ∧ ↑t' subseteq t ∧ u subseteq s' • t'
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.subset_set_image₂`：subset_set_image₂ {s : Set α} {t : Set β} (hu 
: ↑u subseteq image2 f s t) : exists (s' : Finset α) (t' : Finset β), ↑s' subset
eq s ∧ ↑t' sub…
-/
lemma subset_smul {s : Set α} {t : Set β} :
    ↑u ⊆ s • t → ∃ (s' : Finset α) (t' : Finset β), ↑s' ⊆ s ∧ ↑t' ⊆ t ∧ u ⊆ s' • t' :=
  subset_set_image₂

end SMul

/-! ### Translation/scaling of finsets -/

section SMul
variable [DecidableEq β] [SMul α β] {s s₁ s₂ t : Finset β} {a : α} {b : β}

/-- The scaling of a finset `s` by a scalar `a`: `a • s = {a • x | x ∈ s}`. -/
@[to_additive (attr := instance_reducible)
  /-- The translation of a finset `s` by a vector `a`: `a +ᵥ s = {a +ᵥ x | x ∈ s}`. -/]
/-
**Finset.smulFinset** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：{α : Type u_2} → {β : Type u_3} → [DecidableEq β] → [SMul α β] → SMul α (F
inset β)
参数：Finset β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def smulFinset : SMul α (Finset β) where smul a := image <| (a • ·)

scoped[Pointwise] attribute [instance] Finset.smulFinset Finset.vaddFinset
/-
**Finset.smul_finset_def** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : DecidableEq β] [inst_1 : SMul α β]
 {s : Finset β} {a : α},   a • s = Finset.image (fun x => a • x) s
参数：fun x => a • x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] lemma smul_finset_def : a • s = s.image (a • ·) := rfl
/-
**Finset.image_smul** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : DecidableEq β] [inst_1 : SMul α β]
 {s : Finset β} {a : α},   Finset.image (fun x => a • x) s = a • s
参数：fun x => a • x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] lemma image_smul : s.image (a • ·) = a • s := rfl

@[to_additive]
/-
**Finset.mem_smul_finset** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：mem_smul_finset {x : β} : x in a • s ↔ exists y, y in s ∧ a • y = x
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
lemma mem_smul_finset {x : β} : x ∈ a • s ↔ ∃ y, y ∈ s ∧ a • y = x := by
  simp only [Finset.smul_finset_def, mem_image]

@[to_additive (attr := simp, norm_cast)]
/-
**Finset.coe_smul_finset** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：coe_smul_finset (a : α) (s : Finset β) : ↑(a • s) = a • (↑s : Set β)
参数：a : α；s : Finset β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
-/
lemma coe_smul_finset (a : α) (s : Finset β) : ↑(a • s) = a • (↑s : Set β) := coe_image
/-
**Finset.smul_mem_smul_finset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : DecidableEq β] [inst_1 : SMul α β]
 {s : Finset β} {a : α} {b : β},   b ∈ s → a • b ∈ a • s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {a} (h : a in s) 
: f a in s.image f
-/
@[to_additive] lemma smul_mem_smul_finset : b ∈ s → a • b ∈ a • s := mem_image_of_mem _
/-
**Finset.card_smul_finset_le** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : DecidableEq β] [inst_1 : SMul α β]
 {s : Finset β} {a : α}, (a • s).card ≤ s.card
参数：a • s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_image_le`：card_image_le [DecidableEq β] : #(s.image f) <= #s
-/
@[to_additive] lemma card_smul_finset_le : #(a • s) ≤ #s := card_image_le
@[deprecated (since := "2026-04-16")] alias smul_finset_card_le := card_smul_finset_le
@[deprecated (since := "2026-04-16")] alias vadd_finset_card_le := card_vadd_finset_le

@[to_additive (attr := simp)]
/-
**Finset.smul_finset_empty** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：smul_finset_empty (a : α) : a • (∅ : Finset β) = ∅
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma smul_finset_empty (a : α) : a • (∅ : Finset β) = ∅ := rfl

@[to_additive (attr := simp)]
/-
**Finset.smul_finset_eq_empty** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：smul_finset_eq_empty : a • s = ∅ ↔ s = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image_eq_empty`：image_eq_empty : s.image f = ∅ ↔ s = ∅
-/
lemma smul_finset_eq_empty : a • s = ∅ ↔ s = ∅ := image_eq_empty

@[to_additive (attr := simp)]
/-
**Finset.smul_finset_nonempty** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：smul_finset_nonempty : (a • s).Nonempty ↔ s.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.image_nonempty`：image_nonempty : (s.image f).Nonempty ↔ s.Nonempt
y
-/
lemma smul_finset_nonempty : (a • s).Nonempty ↔ s.Nonempty := image_nonempty

@[to_additive (attr := aesop safe apply (rule_sets := [finsetNonempty]))]
/-
**Finset.Nonempty.smul_finset** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nonempty`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : DecidableEq β] [inst_1 : SMul α β]
 {s : Finset β} {a : α},   s.Nonempty → (a • s).Nonempty
参数：a • s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} [inst : Decidable
Eq β] {s : Finset α},   s.Nonempty → ∀ (f : α → β), (Finset.image f s).Nonempty
-/
lemma Nonempty.smul_finset (hs : s.Nonempty) : (a • s).Nonempty :=
  hs.image _

@[to_additive (attr := simp)]
/-
**Finset.singleton_smul** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：singleton_smul (a : α) : ({a} : Finset α) • t = a • t
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_singleton_left`：image₂_singleton_left : image₂ f {a} t = t
.image fun b => f a b
-/
lemma singleton_smul (a : α) : ({a} : Finset α) • t = a • t := image₂_singleton_left

@[to_additive (attr := mono, gcongr)]
/-
**Finset.smul_finset_subset_smul_finset** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：smul_finset_subset_smul_finset : s subseteq t -> a • s subseteq a • t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image_subset_image`：image_subset_image {s₁ s₂ : Finset α} (h : s₁
 subseteq s₂) : s₁.image f subseteq s₂.image f
-/
lemma smul_finset_subset_smul_finset : s ⊆ t → a • s ⊆ a • t := image_subset_image

@[to_additive (attr := simp)]
/-
**Finset.smul_finset_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：smul_finset_singleton (b : β) : a • ({b} : Finset β) = {a • b}
参数：b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image_singleton`：image_singleton (f : α -> β) (a : α) : image f {
a} = {f a}
-/
lemma smul_finset_singleton (b : β) : a • ({b} : Finset β) = {a • b} := image_singleton ..

@[to_additive]
/-
**Finset.smul_finset_union** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：smul_finset_union : a • (s₁ union s₂) = a • s₁ union a • s₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image_union`：image_union [DecidableEq α] {f : α -> β} (s₁ s₂ : Fi
nset α) : (s₁ union s₂).image f = s₁.image f union s₂.image f
-/
lemma smul_finset_union : a • (s₁ ∪ s₂) = a • s₁ ∪ a • s₂ := image_union _ _

@[to_additive]
/-
**Finset.smul_finset_insert** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：smul_finset_insert (a : α) (b : β) (s : Finset β) : a • insert b s = inser
t (a • b) (a • s)
参数：a : α；b : β；s : Finset β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image_insert`：image_insert [DecidableEq α] (f : α -> β) (a : α) (
s : Finset α) : (insert a s).image f = insert (f a) (s.image f)
-/
lemma smul_finset_insert (a : α) (b : β) (s : Finset β) : a • insert b s = insert (a • b) (a • s) :=
  image_insert ..

@[to_additive]
/-
**Finset.smul_finset_inter_subset** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：smul_finset_inter_subset : a • (s₁ inter s₂) subseteq a • s₁ inter a • s₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image_inter_subset`：image_inter_subset [DecidableEq α] (f : α -> 
β) (s t : Finset α) : (s inter t).image f subseteq s.image f inter t.image f
-/
lemma smul_finset_inter_subset : a • (s₁ ∩ s₂) ⊆ a • s₁ ∩ a • s₂ := image_inter_subset _ _ _

@[to_additive]
/-
**Finset.smul_finset_subset_smul** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：smul_finset_subset_smul {s : Finset α} : a in s -> a • t subseteq s • t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image_subset_image₂_right`：image_subset_image₂_right (ha : a in s
) : t.image (fun b => f a b) subseteq image₂ f s t
-/
lemma smul_finset_subset_smul {s : Finset α} : a ∈ s → a • t ⊆ s • t := image_subset_image₂_right

@[to_additive (attr := simp)]
/-
**Finset.biUnion_smul_finset** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：biUnion_smul_finset (s : Finset α) (t : Finset β) : s.biUnion (· • t) = s 
• t
参数：s : Finset α；t : Finset β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.biUnion_image_left`：biUnion_image_left : (s.biUnion fun a => t.im
age <| f a) = image₂ f s t
-/
lemma biUnion_smul_finset (s : Finset α) (t : Finset β) : s.biUnion (· • t) = s • t :=
  biUnion_image_left

end SMul

open scoped Pointwise

/-! ### Instances -/

open scoped Pointwise

/-! ### Scalar subtraction of finsets -/

section VSub

variable [VSub α β] [DecidableEq α] {s s₁ s₂ t t₁ t₂ : Finset β} {u : Finset α} {a : α} {b c : β}

/-- The pointwise subtraction of two finsets `s` and `t`: `s -ᵥ t = {x -ᵥ y | x ∈ s, y ∈ t}`. -/
@[instance_reducible]
/-
**Finset.vsub** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：{α : Type u_2} → {β : Type u_3} → [VSub α β] → [DecidableEq α] → VSub (Fin
set α) (Finset β)
参数：Finset α；Finset β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pointwise subtraction of two finsets `s` and `t`: `s -ᵥ t = {x -ᵥ y | x ∈ s,
 y ∈ t}`.
-/
protected def vsub : VSub (Finset α) (Finset β) :=
  ⟨image₂ (· -ᵥ ·)⟩

scoped[Pointwise] attribute [instance] Finset.vsub
/-
**Finset.vsub_def** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：vsub_def : s -ᵥ t = image₂ (· -ᵥ ·) s t
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem vsub_def : s -ᵥ t = image₂ (· -ᵥ ·) s t :=
  rfl

@[simp]
/-
**Finset.image_vsub_product** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_vsub_product : image₂ (· -ᵥ ·) s t = s -ᵥ t
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image_vsub_product : image₂ (· -ᵥ ·) s t = s -ᵥ t :=
  rfl
/-
**Finset.mem_vsub** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_vsub : a in s -ᵥ t ↔ exists b in s, exists c in t, b -ᵥ c = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_image₂`：mem_image₂ : c in image₂ f s t ↔ exists a in s, exist
s b in t, f a b = c
-/
theorem mem_vsub : a ∈ s -ᵥ t ↔ ∃ b ∈ s, ∃ c ∈ t, b -ᵥ c = a :=
  mem_image₂

@[simp, norm_cast]
/-
**Finset.coe_vsub** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_vsub (s t : Finset β) : (↑(s -ᵥ t) : Set α) = (s : Set β) -ᵥ t
参数：s t : Finset β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_image₂`：coe_image₂ (f : α -> β -> γ) (s : Finset α) (t : Fins
et β) : (image₂ f s t : Set γ) = Set.image2 f s t
-/
theorem coe_vsub (s t : Finset β) : (↑(s -ᵥ t) : Set α) = (s : Set β) -ᵥ t :=
  coe_image₂ _ _ _
/-
**Finset.vsub_mem_vsub** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：vsub_mem_vsub : b in s -> c in t -> b -ᵥ c in s -ᵥ t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_image₂_of_mem`：mem_image₂_of_mem (ha : a in s) (hb : b in t) 
: f a b in image₂ f s t
-/
theorem vsub_mem_vsub : b ∈ s → c ∈ t → b -ᵥ c ∈ s -ᵥ t :=
  mem_image₂_of_mem
/-
**Finset.vsub_card_le** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：vsub_card_le : #(s -ᵥ t : Finset α) <= #s * #t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_image₂_le`：card_image₂_le (f : α -> β -> γ) (s : Finset α) (
t : Finset β) : #(image₂ f s t) <= #s * #t
-/
theorem vsub_card_le : #(s -ᵥ t : Finset α) ≤ #s * #t :=
  card_image₂_le _ _ _

@[simp]
/-
**Finset.empty_vsub** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：empty_vsub (t : Finset β) : (∅ : Finset β) -ᵥ t = ∅
参数：t : Finset β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_empty_left`：image₂_empty_left : image₂ f ∅ t = ∅
-/
theorem empty_vsub (t : Finset β) : (∅ : Finset β) -ᵥ t = ∅ :=
  image₂_empty_left

@[simp]
/-
**Finset.vsub_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：vsub_empty (s : Finset β) : s -ᵥ (∅ : Finset β) = ∅
参数：s : Finset β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_empty_right`：image₂_empty_right : image₂ f s ∅ = ∅
-/
theorem vsub_empty (s : Finset β) : s -ᵥ (∅ : Finset β) = ∅ :=
  image₂_empty_right

@[simp]
/-
**Finset.vsub_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：vsub_eq_empty : s -ᵥ t = ∅ ↔ s = ∅ ∨ t = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_eq_empty_iff`：image₂_eq_empty_iff : image₂ f s t = ∅ ↔ s =
 ∅ ∨ t = ∅
-/
theorem vsub_eq_empty : s -ᵥ t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image₂_eq_empty_iff

@[simp]
/-
**Finset.vsub_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：vsub_nonempty : (s -ᵥ t : Finset α).Nonempty ↔ s.Nonempty ∧ t.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_nonempty_iff`：image₂_nonempty_iff : (image₂ f s t).Nonempt
y ↔ s.Nonempty ∧ t.Nonempty
-/
theorem vsub_nonempty : (s -ᵥ t : Finset α).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image₂_nonempty_iff

@[aesop safe apply (rule_sets := [finsetNonempty])]
/-
**Finset.Nonempty.vsub** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nonempty`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : VSub α β] [inst_1 : DecidableEq α]
 {s t : Finset β},   s.Nonempty → t.Nonempty → (s -ᵥ t).Nonempty
参数：s -ᵥ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nonempty.image₂`：∀ {α : Type u_1} {β : Type u_3} {γ : Type u_5} [
inst : DecidableEq γ] {f : α → β → γ} {s : Finset α} {t : Finset β},   s.Nonempt
y → t.Nonemp…
-/
theorem Nonempty.vsub : s.Nonempty → t.Nonempty → (s -ᵥ t : Finset α).Nonempty :=
  Nonempty.image₂
/-
**Finset.Nonempty.of_vsub_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nonempty`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : VSub α β] [inst_1 : DecidableEq α]
 {s t : Finset β},   (s -ᵥ t).Nonempty → s.Nonempty
参数：s -ᵥ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nonempty.of_image₂_left`：∀ {α : Type u_1} {β : Type u_3} {γ : Typ
e u_5} [inst : DecidableEq γ] {f : α → β → γ} {s : Finset α} {t : Finset β},   (
Finset.image₂ f s t)…
-/
theorem Nonempty.of_vsub_left : (s -ᵥ t : Finset α).Nonempty → s.Nonempty :=
  Nonempty.of_image₂_left
/-
**Finset.Nonempty.of_vsub_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nonempty`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : VSub α β] [inst_1 : DecidableEq α]
 {s t : Finset β},   (s -ᵥ t).Nonempty → t.Nonempty
参数：s -ᵥ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nonempty.of_image₂_right`：∀ {α : Type u_1} {β : Type u_3} {γ : Ty
pe u_5} [inst : DecidableEq γ] {f : α → β → γ} {s : Finset α} {t : Finset β},   
(Finset.image₂ f s t)…
-/
theorem Nonempty.of_vsub_right : (s -ᵥ t : Finset α).Nonempty → t.Nonempty :=
  Nonempty.of_image₂_right

@[simp]
/-
**Finset.vsub_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：vsub_singleton (b : β) : s -ᵥ ({b} : Finset β) = s.image (· -ᵥ b)
参数：b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_singleton_right`：image₂_singleton_right : image₂ f s {b} =
 s.image fun a => f a b
-/
theorem vsub_singleton (b : β) : s -ᵥ ({b} : Finset β) = s.image (· -ᵥ b) :=
  image₂_singleton_right
/-
**Finset.singleton_vsub** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：singleton_vsub (a : β) : ({a} : Finset β) -ᵥ t = t.image (a -ᵥ ·)
参数：a : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_singleton_left`：image₂_singleton_left : image₂ f {a} t = t
.image fun b => f a b
-/
theorem singleton_vsub (a : β) : ({a} : Finset β) -ᵥ t = t.image (a -ᵥ ·) :=
  image₂_singleton_left
/-
**Finset.singleton_vsub_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：singleton_vsub_singleton (a b : β) : ({a} : Finset β) -ᵥ {b} = {a -ᵥ b}
参数：a b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_singleton`：image₂_singleton : image₂ f {a} {b} = {f a b}
-/
theorem singleton_vsub_singleton (a b : β) : ({a} : Finset β) -ᵥ {b} = {a -ᵥ b} :=
  image₂_singleton

@[mono, gcongr]
/-
**Finset.vsub_subset_vsub** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：vsub_subset_vsub : s₁ subseteq s₂ -> t₁ subseteq t₂ -> s₁ -ᵥ t₁ subseteq s
₂ -ᵥ t₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_subset`：image₂_subset (hs : s subseteq s') (ht : t subsete
q t') : image₂ f s t subseteq image₂ f s' t'
-/
theorem vsub_subset_vsub : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ -ᵥ t₁ ⊆ s₂ -ᵥ t₂ :=
  image₂_subset
/-
**Finset.vsub_subset_vsub_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：vsub_subset_vsub_left : t₁ subseteq t₂ -> s -ᵥ t₁ subseteq s -ᵥ t₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_subset_left`：image₂_subset_left (ht : t subseteq t') : ima
ge₂ f s t subseteq image₂ f s t'
-/
theorem vsub_subset_vsub_left : t₁ ⊆ t₂ → s -ᵥ t₁ ⊆ s -ᵥ t₂ :=
  image₂_subset_left
/-
**Finset.vsub_subset_vsub_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：vsub_subset_vsub_right : s₁ subseteq s₂ -> s₁ -ᵥ t subseteq s₂ -ᵥ t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_subset_right`：image₂_subset_right (hs : s subseteq s') : i
mage₂ f s t subseteq image₂ f s' t
-/
theorem vsub_subset_vsub_right : s₁ ⊆ s₂ → s₁ -ᵥ t ⊆ s₂ -ᵥ t :=
  image₂_subset_right
/-
**Finset.vsub_subset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：vsub_subset_iff : s -ᵥ t subseteq u ↔ forall x in s, forall y in t, x -ᵥ y
 in u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_subset_iff`：image₂_subset_iff : image₂ f s t subseteq u ↔ 
forall x in s, forall y in t, f x y in u
-/
theorem vsub_subset_iff : s -ᵥ t ⊆ u ↔ ∀ x ∈ s, ∀ y ∈ t, x -ᵥ y ∈ u :=
  image₂_subset_iff

section

variable [DecidableEq β]

/-
**Finset.union_vsub** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：union_vsub : s₁ union s₂ -ᵥ t = s₁ -ᵥ t union (s₂ -ᵥ t)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_union_left`：image₂_union_left [DecidableEq α] : image₂ f (
s union s') t = image₂ f s t union image₂ f s' t
-/
theorem union_vsub : s₁ ∪ s₂ -ᵥ t = s₁ -ᵥ t ∪ (s₂ -ᵥ t) :=
  image₂_union_left
/-
**Finset.vsub_union** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：vsub_union : s -ᵥ (t₁ union t₂) = s -ᵥ t₁ union (s -ᵥ t₂)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_union_right`：image₂_union_right [DecidableEq β] : image₂ f
 s (t union t') = image₂ f s t union image₂ f s t'
-/
theorem vsub_union : s -ᵥ (t₁ ∪ t₂) = s -ᵥ t₁ ∪ (s -ᵥ t₂) :=
  image₂_union_right
/-
**Finset.inter_vsub_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inter_vsub_subset : s₁ inter s₂ -ᵥ t subseteq (s₁ -ᵥ t) inter (s₂ -ᵥ t)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_inter_subset_left`：image₂_inter_subset_left [DecidableEq α
] : image₂ f (s inter s') t subseteq image₂ f s t inter image₂ f s' t
-/
theorem inter_vsub_subset : s₁ ∩ s₂ -ᵥ t ⊆ (s₁ -ᵥ t) ∩ (s₂ -ᵥ t) :=
  image₂_inter_subset_left
/-
**Finset.vsub_inter_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：vsub_inter_subset : s -ᵥ t₁ inter t₂ subseteq (s -ᵥ t₁) inter (s -ᵥ t₂)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_inter_subset_right`：image₂_inter_subset_right [DecidableEq
 β] : image₂ f s (t inter t') subseteq image₂ f s t inter image₂ f s t'
-/
theorem vsub_inter_subset : s -ᵥ t₁ ∩ t₂ ⊆ (s -ᵥ t₁) ∩ (s -ᵥ t₂) :=
  image₂_inter_subset_right

end

/-- If a finset `u` is contained in the pointwise subtraction of two sets `s -ᵥ t`, we can find two
finsets `s'`, `t'` such that `s' ⊆ s`, `t' ⊆ t` and `u ⊆ s' -ᵥ t'`. -/
/-
**Finset.subset_vsub** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：subset_vsub {s t : Set β} : ↑u subseteq s -ᵥ t -> exists s' t' : Finset β,
 ↑s' subseteq s ∧ ↑t' subseteq t ∧ u subseteq s' -ᵥ t'
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.subset_set_image₂`：subset_set_image₂ {s : Set α} {t : Set β} (hu 
: ↑u subseteq image2 f s t) : exists (s' : Finset α) (t' : Finset β), ↑s' subset
eq s ∧ ↑t' sub…

--- 原说明 ---
If a finset `u` is contained in the pointwise subtraction of two sets `s -ᵥ t`, 
we can find two
finsets `s'`, `t'` such that `s' ⊆ s`, `t' ⊆ t` and `u ⊆ s' -ᵥ t'`.
-/
theorem subset_vsub {s t : Set β} :
    ↑u ⊆ s -ᵥ t → ∃ s' t' : Finset β, ↑s' ⊆ s ∧ ↑t' ⊆ t ∧ u ⊆ s' -ᵥ t' :=
  subset_set_image₂

end VSub

section SMul

variable [DecidableEq β] [DecidableEq γ] [SMul αᵐᵒᵖ β] [SMul β γ] [SMul α γ]

-- TODO: replace hypothesis and conclusion with a typeclass
@[to_additive]
/-
**Finset.op_smul_finset_smul_eq_smul_smul_finset** 是 Mathlib 中的一个定理，位于命名空间 `Fins
et`。
形式化陈述：op_smul_finset_smul_eq_smul_smul_finset (a : α) (s : Finset β) (t : Finset
 γ) (h : forall (a : α) (b : β) (c : γ), (op a • b) • c = b • a • c) : (op a • s
) • t = s • a • t
参数：a : α；s : Finset β；t : Finset γ；h : forall (a : α) (b : β) (c : γ), (op a • b
) • c = b • a • c。
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem op_smul_finset_smul_eq_smul_smul_finset (a : α) (s : Finset β) (t : Finset γ)
    (h : ∀ (a : α) (b : β) (c : γ), (op a • b) • c = b • a • c) : (op a • s) • t = s • a • t := by
  ext
  simp [mem_smul, mem_smul_finset, h]

end SMul

@[to_additive]
/-
**Finset.image_smul_comm** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_smul_comm [DecidableEq β] [DecidableEq γ] [SMul α β] [SMul α γ] (f :
 β -> γ) (a : α) (s : Finset β) : (forall b, f (a • b) = a • f b) -> (a • s).ima
ge f = a • s.image f
参数：f : β -> γ；a : α；s : Finset β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image_comm`：image_comm {β'} [DecidableEq β'] [DecidableEq γ] {f :
 β -> γ} {g : α -> β} {f' : α -> β'} {g' : β' -> γ} (h_comm : forall a, f (g a) 
= g' (f…
-/
theorem image_smul_comm [DecidableEq β] [DecidableEq γ] [SMul α β] [SMul α γ] (f : β → γ) (a : α)
    (s : Finset β) : (∀ b, f (a • b) = a • f b) → (a • s).image f = a • s.image f :=
  image_comm

end Finset

open scoped Pointwise

namespace Set

section SMul

variable [SMul α β] [DecidableEq β] {s : Set α} {t : Set β}

@[to_additive (attr := simp)]
/-
**Set.toFinset_smul** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：toFinset_smul (s : Set α) (t : Set β) [Fintype s] [Fintype t] [Fintype ↑(s
 • t)] : (s • t).toFinset = s.toFinset • t.toFinset
参数：s : Set α；t : Set β；s • t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.toFinset_image2`：toFinset_image2 (f : α -> β -> γ) (s : Set α) (t : 
Set β) [Fintype s] [Fintype t] [Fintype (image2 f s t)] : (image2 f s t).toFinse
t = Finse…
-/
theorem toFinset_smul (s : Set α) (t : Set β) [Fintype s] [Fintype t] [Fintype ↑(s • t)] :
    (s • t).toFinset = s.toFinset • t.toFinset :=
  toFinset_image2 _ _ _

@[to_additive]
/-
**Set.Finite.toFinset_smul** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] [inst_1 : DecidableEq β]
 {s : Set α} {t : Set β} (hs : s.Finite)   (ht : t.Finite) (hf : optParam (s • t
).Finite ⋯), hf.toFinset = hs.toFinset • ht.toFinset
参数：hs : s.Finite；ht : t.Finite；hf : optParam (s • t).Finite ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.toFinset_image2`：∀ {α : Type u_1} {β : Type u_3} {γ : Type u_
5} [inst : DecidableEq γ] {s : Set α} {t : Set β} (f : α → β → γ)   (hs : s.Fini
te) (ht : t.Fini…
· 使用定理 `Set.Finite.image2`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : S
et α} {t : Set β} (f : α → β → γ),   s.Finite → t.Finite → (Set.image2 f s t).Fi
nite
-/
theorem Finite.toFinset_smul (hs : s.Finite) (ht : t.Finite) (hf := hs.smul ht) :
    hf.toFinset = hs.toFinset • ht.toFinset :=
  Finite.toFinset_image2 _ _ _

end SMul

section SMul

variable [DecidableEq β] [SMul α β] {a : α} {s : Set β}

@[to_additive (attr := simp)]
/-
**Set.toFinset_smul_set** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：toFinset_smul_set (a : α) (s : Set β) [Fintype s] [Fintype ↑(a • s)] : (a 
• s).toFinset = a • s.toFinset
参数：a : α；s : Set β；a • s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.toFinset_image`：toFinset_image [DecidableEq β] (f : α -> β) (s : Set
 α) [Fintype s] [Fintype (f '' s)] : (f '' s).toFinset = s.toFinset.image f
-/
theorem toFinset_smul_set (a : α) (s : Set β) [Fintype s] [Fintype ↑(a • s)] :
    (a • s).toFinset = a • s.toFinset :=
  toFinset_image _ _

@[to_additive]
/-
**Set.Finite.toFinset_smul_set** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : DecidableEq β] [inst_1 : SMul α β]
 {a : α} {s : Set β} (hs : s.Finite)   (hf : optParam (a • s).Finite ⋯), hf.toFi
nset = a • hs.toFinset
参数：hs : s.Finite；hf : optParam (a • s).Finite ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.toFinset_image`：∀ {α : Type u} {β : Type v} {s : Set α} [inst
 : DecidableEq β] (f : α → β) (hs : s.Finite) (h : (f '' s).Finite),   h.toFinse
t = Finset.imag…
-/
theorem Finite.toFinset_smul_set (hs : s.Finite) (hf : (a • s).Finite := hs.smul_set) :
    hf.toFinset = a • hs.toFinset :=
  Finite.toFinset_image _ _ _

end SMul

section VSub

variable [DecidableEq α] [VSub α β] {s t : Set β}

@[simp]
/-
**Set.toFinset_vsub** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：toFinset_vsub (s t : Set β) [Fintype s] [Fintype t] [Fintype ↑(s -ᵥ t)] : 
(s -ᵥ t : Set α).toFinset = s.toFinset -ᵥ t.toFinset
参数：s t : Set β；s -ᵥ t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.toFinset_image2`：toFinset_image2 (f : α -> β -> γ) (s : Set α) (t : 
Set β) [Fintype s] [Fintype t] [Fintype (image2 f s t)] : (image2 f s t).toFinse
t = Finse…
-/
theorem toFinset_vsub (s t : Set β) [Fintype s] [Fintype t] [Fintype ↑(s -ᵥ t)] :
    (s -ᵥ t : Set α).toFinset = s.toFinset -ᵥ t.toFinset :=
  toFinset_image2 _ _ _
/-
**Set.Finite.toFinset_vsub** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : DecidableEq α] [inst_1 : VSub α β]
 {s t : Set β} (hs : s.Finite) (ht : t.Finite)   (hf : optParam (s -ᵥ t).Finite 
⋯), hf.toFinset = hs.toFinset -ᵥ ht.toFinset
参数：hs : s.Finite；ht : t.Finite；hf : optParam (s -ᵥ t).Finite ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.toFinset_image2`：∀ {α : Type u_1} {β : Type u_3} {γ : Type u_
5} [inst : DecidableEq γ] {s : Set α} {t : Set β} (f : α → β → γ)   (hs : s.Fini
te) (ht : t.Fini…
· 使用定理 `Set.Finite.image2`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : S
et α} {t : Set β} (f : α → β → γ),   s.Finite → t.Finite → (Set.image2 f s t).Fi
nite
-/
theorem Finite.toFinset_vsub (hs : s.Finite) (ht : t.Finite) (hf := hs.vsub ht) :
    hf.toFinset = hs.toFinset -ᵥ ht.toFinset :=
  Finite.toFinset_image2 _ _ _

end VSub

end Set

