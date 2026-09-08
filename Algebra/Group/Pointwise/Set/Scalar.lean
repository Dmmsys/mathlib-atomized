/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Floris van Doorn, Yaël Dillies
-/
module

public import Mathlib.Algebra.Opposites
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Data.Set.NAry
public import Mathlib.Tactic.Monotonicity.Attr

/-!
# Pointwise scalar operations of sets

This file defines pointwise scalar-flavored algebraic operations on sets.

## Main declarations

For sets `s` and `t` and scalar `a`:

* `s • t`: Scalar multiplication, set of all `x • y` where `x ∈ s` and `y ∈ t`.
* `s /ₛ t`: Scalar division, set of all `x /ₛ y` where `x ∈ s` and `y ∈ t`. Available in
  multiplicative torsors.
* `s +ᵥ t`: Scalar addition, set of all `x +ᵥ y` where `x ∈ s` and `y ∈ t`.
* `s -ᵥ t`: Scalar subtraction, set of all `x -ᵥ y` where `x ∈ s` and `y ∈ t`.
* `a • s`: Scaling, set of all `a • x` where `x ∈ s`.
* `a +ᵥ s`: Translation, set of all `a +ᵥ x` where `x ∈ s`.

For `α` a semigroup/monoid, `Set α` is a semigroup/monoid.
As an unfortunate side effect, this means that `n • s`, where `n : ℕ`, is ambiguous between
pointwise scaling and repeated pointwise addition; the former has `(2 : ℕ) • {1, 2} = {2, 4}`, while
the latter has `(2 : ℕ) • {1, 2} = {2, 3, 4}`. See note [pointwise nat action].

Appropriate definitions and results are also transported to the additive theory via `to_additive`.

## Implementation notes

* The following expressions are considered in simp-normal form in a group:
  `(fun h ↦ h * g) ⁻¹' s`, `(fun h ↦ g * h) ⁻¹' s`, `(fun h ↦ h * g⁻¹) ⁻¹' s`,
  `(fun h ↦ g⁻¹ * h) ⁻¹' s`, `s * t`, `s⁻¹`, `(1 : Set _)` (and similarly for additive variants).
  Expressions equal to one of these will be simplified.
* We put all instances in the scope `Pointwise`, so that these instances are not available by
  default. Note that we do not mark them as reducible (as argued by note [reducible non-instances])
  since we expect the scope to be open whenever the instances are actually used (and making the
  instances reducible changes the behavior of `simp`).

## Tags

set multiplication, set addition, pointwise addition, pointwise multiplication,
pointwise subtraction
-/

@[expose] public section

assert_not_exists Set.iUnion MulAction MonoidWithZero IsOrderedMonoid

open Function MulOpposite

variable {F α β γ : Type*}

namespace Set

/-! ### Translation/scaling of sets -/

section SMul

/-- The dilation of set `x • s` is defined as `{x • y | y ∈ s}` in scope `Pointwise`. -/
@[to_additive (attr := instance_reducible)
/-- The translation of set `x +ᵥ s` is defined as `{x +ᵥ y | y ∈ s}` in scope `Pointwise`. -/]
/-
**Set.smulSet** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：{α : Type u_2} → {β : Type u_3} → [SMul α β] → SMul α (Set β)
参数：Set β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def smulSet [SMul α β] : SMul α (Set β) where smul a := image (a • ·)

/-- The pointwise scalar multiplication of sets `s • t` is defined as `{x • y | x ∈ s, y ∈ t}` in
scope `Pointwise`. -/
@[to_additive (attr := instance_reducible)
/-- The pointwise scalar addition of sets `s +ᵥ t` is defined as `{x +ᵥ y | x ∈ s, y ∈ t}` in locale
`Pointwise`. -/]
/-
**Set.smul** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：{α : Type u_2} → {β : Type u_3} → [SMul α β] → SMul (Set α) (Set β)
参数：Set α；Set β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def smul [SMul α β] : SMul (Set α) (Set β) where smul := image2 (· • ·)

scoped[Pointwise] attribute [instance] Set.smulSet Set.smul
scoped[Pointwise] attribute [instance] Set.vaddSet Set.vadd

open scoped Pointwise

section SMul
variable {ι : Sort*} {κ : ι → Sort*} [SMul α β] {s s₁ s₂ : Set α} {t t₁ t₂ u : Set β} {a : α}
  {b : β}

/-
**Set.image2_smul** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {s : Set α} {t : Set β},
 Set.image2 (fun x1 x2 => x1 • x2) s t = s • t
参数：fun x1 x2 => x1 • x2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive (attr := simp)] lemma image2_smul : image2 (· • ·) s t = s • t := rfl

@[to_additive vadd_image_prod]
/-
**Set.image_smul_prod** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_smul_prod : (fun x : α × β => x.fst • x.snd) '' s ×ˢ t = s • t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.image_prod`：image_prod : (fun x : α × β => f x.1 x.2) '' s ×ˢ t = im
age2 f s t
-/
lemma image_smul_prod : (fun x : α × β ↦ x.fst • x.snd) '' s ×ˢ t = s • t := image_prod _
/-
**Set.mem_smul** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {s : Set α} {t : Set β} 
{b : β},   b ∈ s • t ↔ ∃ x ∈ s, ∃ y ∈ t, x • y = b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[to_additive] lemma mem_smul : b ∈ s • t ↔ ∃ x ∈ s, ∃ y ∈ t, x • y = b := Iff.rfl
/-
**Set.smul_mem_smul** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {s : Set α} {t : Set β} 
{a : α} {b : β}, a ∈ s → b ∈ t → a • b ∈ s • t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image2_of_mem`：mem_image2_of_mem (ha : a in s) (hb : b in t) : f
 a b in image2 f s t
-/
@[to_additive] lemma smul_mem_smul : a ∈ s → b ∈ t → a • b ∈ s • t := mem_image2_of_mem
/-
**Set.empty_smul** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {t : Set β}, ∅ • t = ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_empty_left`：image2_empty_left : image2 f ∅ t = ∅
-/
@[to_additive (attr := simp)] lemma empty_smul : (∅ : Set α) • t = ∅ := image2_empty_left
/-
**Set.smul_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {s : Set α}, s • ∅ = ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_empty_right`：image2_empty_right : image2 f s ∅ = ∅
-/
@[to_additive (attr := simp)] lemma smul_empty : s • (∅ : Set β) = ∅ := image2_empty_right
/-
**Set.smul_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {s : Set α} {t : Set β},
 s • t = ∅ ↔ s = ∅ ∨ t = ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_eq_empty_iff`：image2_eq_empty_iff : image2 f s t = ∅ ↔ s = ∅ 
∨ t = ∅
-/
@[to_additive (attr := simp)] lemma smul_eq_empty : s • t = ∅ ↔ s = ∅ ∨ t = ∅ := image2_eq_empty_iff

@[to_additive (attr := simp)]
/-
**Set.smul_nonempty** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：smul_nonempty : (s • t).Nonempty ↔ s.Nonempty ∧ t.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_nonempty_iff`：image2_nonempty_iff : (image2 f s t).Nonempty ↔
 s.Nonempty ∧ t.Nonempty
-/
lemma smul_nonempty : (s • t).Nonempty ↔ s.Nonempty ∧ t.Nonempty := image2_nonempty_iff
/-
**Set.Nonempty.smul** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nonempty`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {s : Set α} {t : Set β},
 s.Nonempty → t.Nonempty → (s • t).Nonempty
参数：s • t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.image2`：∀ {α : Type u_1} {β : Type u_3} {γ : Type u_5} {f :
 α → β → γ} {s : Set α} {t : Set β},   s.Nonempty → t.Nonempty → (Set.image2 f s
 t).Nonem…
-/
@[to_additive] lemma Nonempty.smul : s.Nonempty → t.Nonempty → (s • t).Nonempty := .image2
/-
**Set.Nonempty.of_smul_left** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nonempty`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {s : Set α} {t : Set β},
 (s • t).Nonempty → s.Nonempty
参数：s • t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.of_image2_left`：∀ {α : Type u_1} {β : Type u_3} {γ : Type u
_5} {f : α → β → γ} {s : Set α} {t : Set β},   (Set.image2 f s t).Nonempty → s.N
onempty
-/
@[to_additive] lemma Nonempty.of_smul_left : (s • t).Nonempty → s.Nonempty := .of_image2_left
/-
**Set.Nonempty.of_smul_right** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nonempty`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {s : Set α} {t : Set β},
 (s • t).Nonempty → t.Nonempty
参数：s • t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.of_image2_right`：∀ {α : Type u_1} {β : Type u_3} {γ : Type 
u_5} {f : α → β → γ} {s : Set α} {t : Set β},   (Set.image2 f s t).Nonempty → t.
Nonempty
-/
@[to_additive] lemma Nonempty.of_smul_right : (s • t).Nonempty → t.Nonempty := .of_image2_right

@[to_additive (attr := simp low + 1)]
/-
**Set.smul_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：smul_singleton : s • ({b} : Set β) = (· • b) '' s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_singleton_right`：image2_singleton_right : image2 f s {b} = (f
un a => f a b) '' s
-/
lemma smul_singleton : s • ({b} : Set β) = (· • b) '' s := image2_singleton_right

@[to_additive (attr := simp low + 1)]
/-
**Set.singleton_smul** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：singleton_smul : ({a} : Set α) • t = a • t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_singleton_left`：image2_singleton_left : image2 f {a} t = f a 
'' t
-/
lemma singleton_smul : ({a} : Set α) • t = a • t := image2_singleton_left

@[to_additive (attr := simp high)]
/-
**Set.singleton_smul_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：singleton_smul_singleton : ({a} : Set α) • ({b} : Set β) = {a • b}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_singleton`：image2_singleton : image2 f {a} {b} = {f a b}
-/
lemma singleton_smul_singleton : ({a} : Set α) • ({b} : Set β) = {a • b} := image2_singleton

@[to_additive (attr := mono, gcongr)]
/-
**Set.smul_subset_smul** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：smul_subset_smul : s₁ subseteq s₂ -> t₁ subseteq t₂ -> s₁ • t₁ subseteq s₂
 • t₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_subset`：image2_subset (hs : s subseteq s') (ht : t subseteq t
') : image2 f s t subseteq image2 f s' t'
-/
lemma smul_subset_smul : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ • t₁ ⊆ s₂ • t₂ := image2_subset

@[to_additive]
/-
**Set.smul_subset_smul_left** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：smul_subset_smul_left : t₁ subseteq t₂ -> s • t₁ subseteq s • t₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_subset_left`：image2_subset_left (ht : t subseteq t') : image2
 f s t subseteq image2 f s t'
-/
lemma smul_subset_smul_left : t₁ ⊆ t₂ → s • t₁ ⊆ s • t₂ := image2_subset_left

@[to_additive]
/-
**Set.smul_subset_smul_right** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：smul_subset_smul_right : s₁ subseteq s₂ -> s₁ • t subseteq s₂ • t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_subset_right`：image2_subset_right (hs : s subseteq s') : imag
e2 f s t subseteq image2 f s' t
-/
lemma smul_subset_smul_right : s₁ ⊆ s₂ → s₁ • t ⊆ s₂ • t := image2_subset_right
/-
**Set.smul_subset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {s : Set α} {t u : Set β
}, s • t ⊆ u ↔ ∀ a ∈ s, ∀ b ∈ t, a • b ∈ u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_subset_iff`：image2_subset_iff {u : Set γ} : image2 f s t subs
eteq u ↔ forall x in s, forall y in t, f x y in u
-/
@[to_additive] lemma smul_subset_iff : s • t ⊆ u ↔ ∀ a ∈ s, ∀ b ∈ t, a • b ∈ u := image2_subset_iff
/-
**Set.union_smul** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {s₁ s₂ : Set α} {t : Set
 β}, (s₁ ∪ s₂) • t = s₁ • t ∪ s₂ • t
参数：s₁ ∪ s₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_union_left`：image2_union_left : image2 f (s union s') t = ima
ge2 f s t union image2 f s' t
-/
@[to_additive] lemma union_smul : (s₁ ∪ s₂) • t = s₁ • t ∪ s₂ • t := image2_union_left
/-
**Set.smul_union** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {s : Set α} {t₁ t₂ : Set
 β}, s • (t₁ ∪ t₂) = s • t₁ ∪ s • t₂
参数：t₁ ∪ t₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_union_right`：image2_union_right : image2 f s (t union t') = i
mage2 f s t union image2 f s t'
-/
@[to_additive] lemma smul_union : s • (t₁ ∪ t₂) = s • t₁ ∪ s • t₂ := image2_union_right

@[to_additive]
/-
**Set.inter_smul_subset** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：inter_smul_subset : (s₁ inter s₂) • t subseteq s₁ • t inter s₂ • t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_inter_subset_left`：image2_inter_subset_left : image2 f (s int
er s') t subseteq image2 f s t inter image2 f s' t
-/
lemma inter_smul_subset : (s₁ ∩ s₂) • t ⊆ s₁ • t ∩ s₂ • t := image2_inter_subset_left

@[to_additive]
/-
**Set.smul_inter_subset** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：smul_inter_subset : s • (t₁ inter t₂) subseteq s • t₁ inter s • t₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_inter_subset_right`：image2_inter_subset_right : image2 f s (t
 inter t') subseteq image2 f s t inter image2 f s t'
-/
lemma smul_inter_subset : s • (t₁ ∩ t₂) ⊆ s • t₁ ∩ s • t₂ := image2_inter_subset_right

@[to_additive]
/-
**Set.inter_smul_union_subset_union** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：inter_smul_union_subset_union : (s₁ inter s₂) • (t₁ union t₂) subseteq s₁ 
• t₁ union s₂ • t₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_inter_union_subset_union`：image2_inter_union_subset_union : i
mage2 f (s inter s') (t union t') subseteq image2 f s t union image2 f s' t'
-/
lemma inter_smul_union_subset_union : (s₁ ∩ s₂) • (t₁ ∪ t₂) ⊆ s₁ • t₁ ∪ s₂ • t₂ :=
  image2_inter_union_subset_union

@[to_additive]
/-
**Set.union_smul_inter_subset_union** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：union_smul_inter_subset_union : (s₁ union s₂) • (t₁ inter t₂) subseteq s₁ 
• t₁ union s₂ • t₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_union_inter_subset_union`：image2_union_inter_subset_union : i
mage2 f (s union s') (t inter t') subseteq image2 f s t union image2 f s' t'
-/
lemma union_smul_inter_subset_union : (s₁ ∪ s₂) • (t₁ ∩ t₂) ⊆ s₁ • t₁ ∪ s₂ • t₂ :=
  image2_union_inter_subset_union

@[to_additive]
/-
**Set.smul_set_subset_smul** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：smul_set_subset_smul {s : Set α} : a in s -> a • t subseteq s • t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_subset_image2_right`：image_subset_image2_right (ha : a in s) :
 f a '' t subseteq image2 f s t
-/
lemma smul_set_subset_smul {s : Set α} : a ∈ s → a • t ⊆ s • t := image_subset_image2_right

end SMul

section SMulSet
variable {ι : Sort*} {κ : ι → Sort*} [SMul α β] {s t t₁ t₂ : Set β} {a : α} {b : β} {x y : β}

/-
**Set.image_smul** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {t : Set β} {a : α}, (fu
n x => a • x) '' t = a • t
参数：fun x => a • x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] lemma image_smul : (fun x ↦ a • x) '' t = a • t := rfl

scoped[Pointwise] attribute [simp] Set.image_smul Set.image_vadd
/-
**Set.mem_smul_set** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {t : Set β} {a : α} {x :
 β}, x ∈ a • t ↔ ∃ y ∈ t, a • y = x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[to_additive] lemma mem_smul_set : x ∈ a • t ↔ ∃ y, y ∈ t ∧ a • y = x := Iff.rfl
/-
**Set.smul_mem_smul_set** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {s : Set β} {a : α} {b :
 β}, b ∈ s → a • b ∈ a • s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
@[to_additive] lemma smul_mem_smul_set : b ∈ s → a • b ∈ a • s := mem_image_of_mem _
/-
**Set.smul_set_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {a : α}, a • ∅ = ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
-/
@[to_additive (attr := simp)] lemma smul_set_empty : a • (∅ : Set β) = ∅ := image_empty _
/-
**Set.smul_set_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {s : Set β} {a : α}, a •
 s = ∅ ↔ s = ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_eq_empty`：image_eq_empty {α β} {f : α -> β} {s : Set α} : f ''
 s = ∅ ↔ s = ∅
-/
@[to_additive (attr := simp)] lemma smul_set_eq_empty : a • s = ∅ ↔ s = ∅ := image_eq_empty

@[to_additive (attr := simp)]
/-
**Set.smul_set_nonempty** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：smul_set_nonempty : (a • s).Nonempty ↔ s.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_nonempty`：image_nonempty {f : α -> β} {s : Set α} : (f '' s).N
onempty ↔ s.Nonempty
-/
lemma smul_set_nonempty : (a • s).Nonempty ↔ s.Nonempty := image_nonempty

@[to_additive (attr := simp)]
/-
**Set.smul_set_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：smul_set_singleton : a • ({b} : Set β) = {a • b}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
-/
lemma smul_set_singleton : a • ({b} : Set β) = {a • b} := image_singleton
/-
**Set.smul_set_mono** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {s t : Set β} {a : α}, s
 ⊆ t → a • s ⊆ a • t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
-/
@[to_additive (attr := gcongr)] lemma smul_set_mono : s ⊆ t → a • s ⊆ a • t := image_mono

@[to_additive]
/-
**Set.smul_set_subset_iff** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：smul_set_subset_iff : a • s subseteq t ↔ forall ⦃b⦄, b in s -> a • b in t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
-/
lemma smul_set_subset_iff : a • s ⊆ t ↔ ∀ ⦃b⦄, b ∈ s → a • b ∈ t :=
  image_subset_iff

@[to_additive]
/-
**Set.smul_set_union** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：smul_set_union : a • (t₁ union t₂) = a • t₁ union a • t₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_union`：image_union (f : α -> β) (s t : Set α) : f '' (s union 
t) = f '' s union f '' t
-/
lemma smul_set_union : a • (t₁ ∪ t₂) = a • t₁ ∪ a • t₂ :=
  image_union ..

@[to_additive]
/-
**Set.smul_set_insert** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：smul_set_insert (a : α) (b : β) (s : Set β) : a • insert b s = insert (a •
 b) (a • s)
参数：a : α；b : β；s : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_insert_eq`：image_insert_eq {f : α -> β} {a : α} {s : Set α} : 
f '' insert a s = insert (f a) (f '' s)
-/
lemma smul_set_insert (a : α) (b : β) (s : Set β) : a • insert b s = insert (a • b) (a • s) :=
  image_insert_eq ..

@[to_additive]
/-
**Set.smul_set_inter_subset** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：smul_set_inter_subset : a • (t₁ inter t₂) subseteq a • t₁ inter a • t₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_inter_subset`：image_inter_subset (f : α -> β) (s t : Set α) : 
f '' (s inter t) subseteq f '' s inter f '' t
-/
lemma smul_set_inter_subset : a • (t₁ ∩ t₂) ⊆ a • t₁ ∩ a • t₂ :=
  image_inter_subset ..
/-
**Set.Nonempty.smul_set** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nonempty`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {s : Set β} {a : α}, s.N
onempty → (a • s).Nonempty
参数：a • s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
-/
@[to_additive] lemma Nonempty.smul_set : s.Nonempty → (a • s).Nonempty := Nonempty.image _

end SMulSet

section Pi

variable {M ι : Type*} {π : ι → Type*} [∀ i, SMul M (π i)]

@[to_additive]
/-
**Set.smul_set_pi_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：smul_set_pi_of_surjective (c : M) (I : Set ι) (s : forall i, Set (π i)) (h
surj : forall i ∉ I, Function.Surjective (c • · : π i -> π i)) : c • I.pi s = I.
pi (c • s)
参数：c : M；I : Set ι；s : forall i, Set (π i)；hsurj : forall i ∉ I, Function.Surjec
tive (c • · : π i -> π i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.piMap_image_pi`：piMap_image_pi {f : forall i, α i -> β i} (hf : fora
ll i ∉ s, Surjective (f i)) (t : forall i, Set (α i)) : Pi.map f '' s.pi t = s.p
i fun i …
-/
theorem smul_set_pi_of_surjective (c : M) (I : Set ι) (s : ∀ i, Set (π i))
    (hsurj : ∀ i ∉ I, Function.Surjective (c • · : π i → π i)) : c • I.pi s = I.pi (c • s) :=
  piMap_image_pi hsurj s

@[to_additive]
/-
**Set.smul_set_univ_pi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：smul_set_univ_pi (c : M) (s : forall i, Set (π i)) : c • univ.pi s = univ.
pi (c • s)
参数：c : M；s : forall i, Set (π i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.piMap_image_univ_pi`：piMap_image_univ_pi (f : forall i, α i -> β i) 
(t : forall i, Set (α i)) : Pi.map f '' univ.pi t = univ.pi fun i => f i '' t i
-/
theorem smul_set_univ_pi (c : M) (s : ∀ i, Set (π i)) : c • univ.pi s = univ.pi (c • s) :=
  piMap_image_univ_pi _ s

end Pi

variable {s : Set α} {t : Set β} {a : α} {b : β}

@[to_additive]
/-
**Set.range_smul_range** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：range_smul_range {ι κ : Type*} [SMul α β] (b : ι -> α) (c : κ -> β) : rang
e b • range c = range fun p : ι × κ => b p.1 • c p.2
参数：b : ι -> α；c : κ -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.image2_range`：image2_range (f : α' -> β' -> γ) (g : α -> α') (h : β 
-> β') : image2 f (range g) (range h) = range fun x : α × β => f (g x.1) (h x.2)
-/
lemma range_smul_range {ι κ : Type*} [SMul α β] (b : ι → α) (c : κ → β) :
    range b • range c = range fun p : ι × κ ↦ b p.1 • c p.2 :=
  image2_range ..

@[to_additive]
/-
**Set.smul_set_range** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：smul_set_range [SMul α β] {ι : Sort*} (a : α) (f : ι -> β) : a • range f =
 range fun i => a • f i
参数：a : α；f : ι -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
-/
lemma smul_set_range [SMul α β] {ι : Sort*} (a : α) (f : ι → β) :
    a • range f = range fun i ↦ a • f i :=
  (range_comp ..).symm
/-
**Set.range_smul** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {ι : Sort u_5} (a : α) (
f : ι → β),   (Set.range fun i => a • f i) = a • Set.range f
参数：a : α；f : ι → β；Set.range fun i => a • f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.smul_set_range`：smul_set_range [SMul α β] {ι : Sort*} (a : α) (f : ι
 -> β) : a • range f = range fun i => a • f i
-/
@[to_additive] lemma range_smul [SMul α β] {ι : Sort*} (a : α) (f : ι → β) :
    range (fun i ↦ a • f i) = a • range f := (smul_set_range ..).symm

end SMul

section SDiv
variable {ι : Sort*} {κ : ι → Sort*} [SDiv α β] {s s₁ s₂ t t₁ t₂ : Set β} {u : Set α} {a : α}
  {b c : β}

@[to_additive]
/-
**Set.sdiv** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：sdiv : SDiv (Set α) (Set β) where sdiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance sdiv : SDiv (Set α) (Set β) where sdiv := image2 (· /ₛ ·)

@[to_additive (attr := simp)]
/-
**Set.image2_sdiv** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image2_sdiv : image2 (· /ₛ ·) s t = s /ₛ t
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma image2_sdiv : image2 (· /ₛ ·) s t = s /ₛ t := rfl

@[to_additive Set.image_vsub_prod]
/-
**Set.image_sdiv_prod** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_sdiv_prod : (fun x : β × β => x.fst /ₛ x.snd) '' s ×ˢ t = s /ₛ t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.image_prod`：image_prod : (fun x : α × β => f x.1 x.2) '' s ×ˢ t = im
age2 f s t
-/
lemma image_sdiv_prod : (fun x : β × β ↦ x.fst /ₛ x.snd) '' s ×ˢ t = s /ₛ t := image_prod _

@[to_additive]
/-
**Set.mem_sdiv** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mem_sdiv : a in s /ₛ t ↔ exists x in s, exists y in t, x /ₛ y = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_sdiv : a ∈ s /ₛ t ↔ ∃ x ∈ s, ∃ y ∈ t, x /ₛ y = a := Iff.rfl

@[to_additive]
/-
**Set.sdiv_mem_sdiv** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：sdiv_mem_sdiv (hb : b in s) (hc : c in t) : b /ₛ c in s /ₛ t
参数：hb : b in s；hc : c in t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image2_of_mem`：mem_image2_of_mem (ha : a in s) (hb : b in t) : f
 a b in image2 f s t
-/
lemma sdiv_mem_sdiv (hb : b ∈ s) (hc : c ∈ t) : b /ₛ c ∈ s /ₛ t := mem_image2_of_mem hb hc

@[to_additive (attr := simp)]
/-
**Set.empty_sdiv** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：empty_sdiv (t : Set β) : ∅ /ₛ t = ∅
参数：t : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_empty_left`：image2_empty_left : image2 f ∅ t = ∅
-/
lemma empty_sdiv (t : Set β) : ∅ /ₛ t = ∅ := image2_empty_left

@[to_additive (attr := simp)]
/-
**Set.sdiv_empty** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：sdiv_empty (s : Set β) : s /ₛ ∅ = ∅
参数：s : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_empty_right`：image2_empty_right : image2 f s ∅ = ∅
-/
lemma sdiv_empty (s : Set β) : s /ₛ ∅ = ∅ := image2_empty_right

@[to_additive (attr := simp)]
/-
**Set.sdiv_eq_empty** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：sdiv_eq_empty : s /ₛ t = ∅ ↔ s = ∅ ∨ t = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_eq_empty_iff`：image2_eq_empty_iff : image2 f s t = ∅ ↔ s = ∅ 
∨ t = ∅
-/
lemma sdiv_eq_empty : s /ₛ t = ∅ ↔ s = ∅ ∨ t = ∅ := image2_eq_empty_iff

@[to_additive (attr := simp)]
/-
**Set.sdiv_nonempty** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：sdiv_nonempty : (s /ₛ t : Set α).Nonempty ↔ s.Nonempty ∧ t.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_nonempty_iff`：image2_nonempty_iff : (image2 f s t).Nonempty ↔
 s.Nonempty ∧ t.Nonempty
-/
lemma sdiv_nonempty : (s /ₛ t : Set α).Nonempty ↔ s.Nonempty ∧ t.Nonempty := image2_nonempty_iff

@[to_additive]
/-
**Set.Nonempty.sdiv** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nonempty`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : SDiv α β] {s t : Set β}, s.Nonempt
y → t.Nonempty → (s /ₛ t).Nonempty
参数：s /ₛ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.image2`：∀ {α : Type u_1} {β : Type u_3} {γ : Type u_5} {f :
 α → β → γ} {s : Set α} {t : Set β},   s.Nonempty → t.Nonempty → (Set.image2 f s
 t).Nonem…
-/
lemma Nonempty.sdiv : s.Nonempty → t.Nonempty → (s /ₛ t : Set α).Nonempty := .image2

@[to_additive]
/-
**Set.Nonempty.of_sdiv_left** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nonempty`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : SDiv α β] {s t : Set β}, (s /ₛ t).
Nonempty → s.Nonempty
参数：s /ₛ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.of_image2_left`：∀ {α : Type u_1} {β : Type u_3} {γ : Type u
_5} {f : α → β → γ} {s : Set α} {t : Set β},   (Set.image2 f s t).Nonempty → s.N
onempty
-/
lemma Nonempty.of_sdiv_left : (s /ₛ t : Set α).Nonempty → s.Nonempty := .of_image2_left

@[to_additive]
/-
**Set.Nonempty.of_sdiv_right** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nonempty`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : SDiv α β] {s t : Set β}, (s /ₛ t).
Nonempty → t.Nonempty
参数：s /ₛ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.of_image2_right`：∀ {α : Type u_1} {β : Type u_3} {γ : Type 
u_5} {f : α → β → γ} {s : Set α} {t : Set β},   (Set.image2 f s t).Nonempty → t.
Nonempty
-/
lemma Nonempty.of_sdiv_right : (s /ₛ t : Set α).Nonempty → t.Nonempty := .of_image2_right

@[to_additive (attr := simp low + 1)]
/-
**Set.sdiv_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：sdiv_singleton (s : Set β) (b : β) : s /ₛ {b} = (· /ₛ b) '' s
参数：s : Set β；b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_singleton_right`：image2_singleton_right : image2 f s {b} = (f
un a => f a b) '' s
-/
lemma sdiv_singleton (s : Set β) (b : β) : s /ₛ {b} = (· /ₛ b) '' s := image2_singleton_right

@[to_additive (attr := simp low + 1)]
/-
**Set.singleton_sdiv** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：singleton_sdiv (t : Set β) (b : β) : {b} /ₛ t = (b /ₛ ·) '' t
参数：t : Set β；b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_singleton_left`：image2_singleton_left : image2 f {a} t = f a 
'' t
-/
lemma singleton_sdiv (t : Set β) (b : β) : {b} /ₛ t = (b /ₛ ·) '' t := image2_singleton_left

@[to_additive (attr := simp high)]
/-
**Set.singleton_sdiv_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：singleton_sdiv_singleton : ({b} : Set β) /ₛ {c} = {b /ₛ c}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_singleton`：image2_singleton : image2 f {a} {b} = {f a b}
-/
lemma singleton_sdiv_singleton : ({b} : Set β) /ₛ {c} = {b /ₛ c} := image2_singleton

@[to_additive (attr := mono, gcongr)]
/-
**Set.sdiv_subset_sdiv** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：sdiv_subset_sdiv : s₁ subseteq s₂ -> t₁ subseteq t₂ -> s₁ /ₛ t₁ subseteq s
₂ /ₛ t₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_subset`：image2_subset (hs : s subseteq s') (ht : t subseteq t
') : image2 f s t subseteq image2 f s' t'
-/
lemma sdiv_subset_sdiv : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ /ₛ t₁ ⊆ s₂ /ₛ t₂ := image2_subset

@[to_additive]
/-
**Set.sdiv_subset_sdiv_left** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：sdiv_subset_sdiv_left : t₁ subseteq t₂ -> s /ₛ t₁ subseteq s /ₛ t₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_subset_left`：image2_subset_left (ht : t subseteq t') : image2
 f s t subseteq image2 f s t'
-/
lemma sdiv_subset_sdiv_left : t₁ ⊆ t₂ → s /ₛ t₁ ⊆ s /ₛ t₂ := image2_subset_left

@[to_additive]
/-
**Set.sdiv_subset_sdiv_right** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：sdiv_subset_sdiv_right : s₁ subseteq s₂ -> s₁ /ₛ t subseteq s₂ /ₛ t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_subset_right`：image2_subset_right (hs : s subseteq s') : imag
e2 f s t subseteq image2 f s' t
-/
lemma sdiv_subset_sdiv_right : s₁ ⊆ s₂ → s₁ /ₛ t ⊆ s₂ /ₛ t := image2_subset_right

@[to_additive]
/-
**Set.sdiv_subset_iff** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：sdiv_subset_iff : s /ₛ t subseteq u ↔ forall x in s, forall y in t, x /ₛ y
 in u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_subset_iff`：image2_subset_iff {u : Set γ} : image2 f s t subs
eteq u ↔ forall x in s, forall y in t, f x y in u
-/
lemma sdiv_subset_iff : s /ₛ t ⊆ u ↔ ∀ x ∈ s, ∀ y ∈ t, x /ₛ y ∈ u := image2_subset_iff

@[to_additive]
/-
**Set.sdiv_self_mono** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：sdiv_self_mono (h : s subseteq t) : s /ₛ s subseteq t /ₛ t
参数：h : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.sdiv_subset_sdiv`：sdiv_subset_sdiv : s₁ subseteq s₂ -> t₁ subseteq t
₂ -> s₁ /ₛ t₁ subseteq s₂ /ₛ t₂
-/
lemma sdiv_self_mono (h : s ⊆ t) : s /ₛ s ⊆ t /ₛ t := sdiv_subset_sdiv h h

@[to_additive]
/-
**Set.union_sdiv** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：union_sdiv : s₁ union s₂ /ₛ t = s₁ /ₛ t union (s₂ /ₛ t)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_union_left`：image2_union_left : image2 f (s union s') t = ima
ge2 f s t union image2 f s' t
-/
lemma union_sdiv : s₁ ∪ s₂ /ₛ t = s₁ /ₛ t ∪ (s₂ /ₛ t) := image2_union_left

@[to_additive]
/-
**Set.sdiv_union** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：sdiv_union : s /ₛ (t₁ union t₂) = s /ₛ t₁ union (s /ₛ t₂)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_union_right`：image2_union_right : image2 f s (t union t') = i
mage2 f s t union image2 f s t'
-/
lemma sdiv_union : s /ₛ (t₁ ∪ t₂) = s /ₛ t₁ ∪ (s /ₛ t₂) := image2_union_right

@[to_additive]
/-
**Set.inter_sdiv_subset** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：inter_sdiv_subset : s₁ inter s₂ /ₛ t subseteq (s₁ /ₛ t) inter (s₂ /ₛ t)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_inter_subset_left`：image2_inter_subset_left : image2 f (s int
er s') t subseteq image2 f s t inter image2 f s' t
-/
lemma inter_sdiv_subset : s₁ ∩ s₂ /ₛ t ⊆ (s₁ /ₛ t) ∩ (s₂ /ₛ t) := image2_inter_subset_left

@[to_additive]
/-
**Set.sdiv_inter_subset** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：sdiv_inter_subset : s /ₛ t₁ inter t₂ subseteq (s /ₛ t₁) inter (s /ₛ t₂)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_inter_subset_right`：image2_inter_subset_right : image2 f s (t
 inter t') subseteq image2 f s t inter image2 f s t'
-/
lemma sdiv_inter_subset : s /ₛ t₁ ∩ t₂ ⊆ (s /ₛ t₁) ∩ (s /ₛ t₂) := image2_inter_subset_right

@[to_additive]
/-
**Set.inter_sdiv_union_subset_union** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：inter_sdiv_union_subset_union : s₁ inter s₂ /ₛ (t₁ union t₂) subseteq s₁ /
ₛ t₁ union (s₂ /ₛ t₂)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_inter_union_subset_union`：image2_inter_union_subset_union : i
mage2 f (s inter s') (t union t') subseteq image2 f s t union image2 f s' t'
-/
lemma inter_sdiv_union_subset_union : s₁ ∩ s₂ /ₛ (t₁ ∪ t₂) ⊆ s₁ /ₛ t₁ ∪ (s₂ /ₛ t₂) :=
  image2_inter_union_subset_union

@[to_additive]
/-
**Set.union_sdiv_inter_subset_union** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：union_sdiv_inter_subset_union : s₁ union s₂ /ₛ t₁ inter t₂ subseteq s₁ /ₛ 
t₁ union (s₂ /ₛ t₂)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_union_inter_subset_union`：image2_union_inter_subset_union : i
mage2 f (s union s') (t inter t') subseteq image2 f s t union image2 f s' t'
-/
lemma union_sdiv_inter_subset_union : s₁ ∪ s₂ /ₛ t₁ ∩ t₂ ⊆ s₁ /ₛ t₁ ∪ (s₂ /ₛ t₂) :=
  image2_union_inter_subset_union

end SDiv

open scoped Pointwise

@[to_additive]
/-
**Set.image_smul_comm** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_smul_comm [SMul α β] [SMul α γ] (f : β -> γ) (a : α) (s : Set β) : (
forall b, f (a • b) = a • f b) -> f '' (a • s) = a • f '' s
参数：f : β -> γ；a : α；s : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_comm`：image_comm {β'} {f : β -> γ} {g : α -> β} {f' : α -> β'}
 {g' : β' -> γ} (h_comm : forall a, f (g a) = g' (f' a)) : (s.image g).image f =
 (s.…
-/
lemma image_smul_comm [SMul α β] [SMul α γ] (f : β → γ) (a : α) (s : Set β) :
    (∀ b, f (a • b) = a • f b) → f '' (a • s) = a • f '' s := image_comm

section SMul
variable [SMul αᵐᵒᵖ β] [SMul β γ] [SMul α γ]

-- TODO: replace hypothesis and conclusion with a typeclass
@[to_additive]
/-
**Set.op_smul_set_smul_eq_smul_smul_set** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：op_smul_set_smul_eq_smul_smul_set (a : α) (s : Set β) (t : Set γ) (h : for
all (a : α) (b : β) (c : γ), (op a • b) • c = b • a • c) : (op a • s) • t = s • 
a • t
参数：a : α；s : Set β；t : Set γ；h : forall (a : α) (b : β) (c : γ), (op a • b) • c 
= b • a • c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
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
lemma op_smul_set_smul_eq_smul_smul_set (a : α) (s : Set β) (t : Set γ)
    (h : ∀ (a : α) (b : β) (c : γ), (op a • b) • c = b • a • c) : (op a • s) • t = s • a • t := by
  ext; simp [mem_smul, mem_smul_set, h]

end SMul

end Set

