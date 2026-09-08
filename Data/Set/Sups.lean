/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Set.NAry
public import Mathlib.Order.SupClosed
public import Mathlib.Order.UpperLower.Closure

/-!
# Set family operations

This file defines a few binary operations on `Set α` for use in set family combinatorics.

## Main declarations

* `s ⊻ t`: Set of elements of the form `a ⊔ b` where `a ∈ s`, `b ∈ t`.
* `s ⊼ t`: Set of elements of the form `a ⊓ b` where `a ∈ s`, `b ∈ t`.

## Notation

We define the following notation in scope `SetFamily`:
* `s ⊻ t`
* `s ⊼ t`

## References

[B. Bollobás, *Combinatorics*][bollobas1986]
-/

@[expose] public section


open Function

variable {F α β : Type*}

/-- Notation typeclass for pointwise supremum `⊻`. -/
/-
**HasSups** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_4 → Type u_4
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Notation typeclass for pointwise supremum `⊻`.
-/
class HasSups (α : Type*) where
  /-- The point-wise supremum `a ⊔ b` of `a, b : α`. -/
  sups : α → α → α

/-- Notation typeclass for pointwise infimum `⊼`. -/
/-
**HasInfs** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_4 → Type u_4
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Notation typeclass for pointwise infimum `⊼`.
-/
class HasInfs (α : Type*) where
  /-- The point-wise infimum `a ⊓ b` of `a, b : α`. -/
  infs : α → α → α

-- This notation is meant to have higher precedence than `⊔` and `⊓`, but still within the
-- realm of other binary notation.
@[inherit_doc]
infixl:74 " ⊻ " => HasSups.sups

@[inherit_doc]
infixl:75 " ⊼ " => HasInfs.infs

namespace Set

section Sups
variable [SemilatticeSup α] [SemilatticeSup β] [FunLike F α β] [SupHomClass F α β]
variable (s s₁ s₂ t t₁ t₂ u v : Set α)

/-- `s ⊻ t` is the set of elements of the form `a ⊔ b` where `a ∈ s`, `b ∈ t`. -/
@[instance_reducible]
/-
**Set.hasSups** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：{α : Type u_2} → [SemilatticeSup α] → HasSups (Set α)
参数：Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`s ⊻ t` is the set of elements of the form `a ⊔ b` where `a ∈ s`, `b ∈ t`.
-/
protected def hasSups : HasSups (Set α) :=
  ⟨image2 (· ⊔ ·)⟩

scoped[SetFamily] attribute [instance] Set.hasSups

open SetFamily

variable {s s₁ s₂ t t₁ t₂ u} {a b c : α}

@[simp]
/-
**Set.mem_sups** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
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
/-
**Set.sup_mem_sups** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sup_mem_sups : a in s -> b in t -> a ⊔ b in s ⊻ t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image2_of_mem`：mem_image2_of_mem (ha : a in s) (hb : b in t) : f
 a b in image2 f s t
-/
theorem sup_mem_sups : a ∈ s → b ∈ t → a ⊔ b ∈ s ⊻ t :=
  mem_image2_of_mem
/-
**Set.sups_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sups_subset : s₁ subseteq s₂ -> t₁ subseteq t₂ -> s₁ ⊻ t₁ subseteq s₂ ⊻ t₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_subset`：image2_subset (hs : s subseteq s') (ht : t subseteq t
') : image2 f s t subseteq image2 f s' t'
-/
theorem sups_subset : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ ⊻ t₁ ⊆ s₂ ⊻ t₂ :=
  image2_subset
/-
**Set.sups_subset_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sups_subset_left : t₁ subseteq t₂ -> s ⊻ t₁ subseteq s ⊻ t₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_subset_left`：image2_subset_left (ht : t subseteq t') : image2
 f s t subseteq image2 f s t'
-/
theorem sups_subset_left : t₁ ⊆ t₂ → s ⊻ t₁ ⊆ s ⊻ t₂ :=
  image2_subset_left
/-
**Set.sups_subset_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sups_subset_right : s₁ subseteq s₂ -> s₁ ⊻ t subseteq s₂ ⊻ t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_subset_right`：image2_subset_right (hs : s subseteq s') : imag
e2 f s t subseteq image2 f s' t
-/
theorem sups_subset_right : s₁ ⊆ s₂ → s₁ ⊻ t ⊆ s₂ ⊻ t :=
  image2_subset_right
/-
**Set.image_subset_sups_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_subset_sups_left : b in t -> (fun a => a ⊔ b) '' s subseteq s ⊻ t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_subset_image2_left`：image_subset_image2_left (hb : b in t) : (
fun a => f a b) '' s subseteq image2 f s t
-/
theorem image_subset_sups_left : b ∈ t → (fun a => a ⊔ b) '' s ⊆ s ⊻ t :=
  image_subset_image2_left
/-
**Set.image_subset_sups_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_subset_sups_right : a in s -> (· ⊔ ·) a '' t subseteq s ⊻ t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_subset_image2_right`：image_subset_image2_right (ha : a in s) :
 f a '' t subseteq image2 f s t
-/
theorem image_subset_sups_right : a ∈ s → (· ⊔ ·) a '' t ⊆ s ⊻ t :=
  image_subset_image2_right
/-
**Set.forall_sups_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：forall_sups_iff {p : α -> Prop} : (forall c in s ⊻ t, p c) ↔ forall a in s
, forall b in t, p (a ⊔ b)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.forall_mem_image2`：forall_mem_image2 {p : γ -> Prop} : (forall z in 
image2 f s t, p z) ↔ forall x in s, forall y in t, p (f x y)
-/
theorem forall_sups_iff {p : α → Prop} : (∀ c ∈ s ⊻ t, p c) ↔ ∀ a ∈ s, ∀ b ∈ t, p (a ⊔ b) :=
  forall_mem_image2

@[simp]
/-
**Set.sups_subset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sups_subset_iff : s ⊻ t subseteq u ↔ forall a in s, forall b in t, a ⊔ b i
n u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_subset_iff`：image2_subset_iff {u : Set γ} : image2 f s t subs
eteq u ↔ forall x in s, forall y in t, f x y in u
-/
theorem sups_subset_iff : s ⊻ t ⊆ u ↔ ∀ a ∈ s, ∀ b ∈ t, a ⊔ b ∈ u :=
  image2_subset_iff

@[simp]
/-
**Set.sups_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sups_nonempty : (s ⊻ t).Nonempty ↔ s.Nonempty ∧ t.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_nonempty_iff`：image2_nonempty_iff : (image2 f s t).Nonempty ↔
 s.Nonempty ∧ t.Nonempty
-/
theorem sups_nonempty : (s ⊻ t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image2_nonempty_iff
/-
**Set.Nonempty.sups** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nonempty`。
形式化陈述：∀ {α : Type u_2} [inst : SemilatticeSup α] {s t : Set α}, s.Nonempty → t.N
onempty → (s ⊻ t).Nonempty
参数：s ⊻ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.image2`：∀ {α : Type u_1} {β : Type u_3} {γ : Type u_5} {f :
 α → β → γ} {s : Set α} {t : Set β},   s.Nonempty → t.Nonempty → (Set.image2 f s
 t).Nonem…
-/
protected theorem Nonempty.sups : s.Nonempty → t.Nonempty → (s ⊻ t).Nonempty :=
  Nonempty.image2
/-
**Set.Nonempty.of_sups_left** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nonempty`。
形式化陈述：∀ {α : Type u_2} [inst : SemilatticeSup α] {s t : Set α}, (s ⊻ t).Nonempty
 → s.Nonempty
参数：s ⊻ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.of_image2_left`：∀ {α : Type u_1} {β : Type u_3} {γ : Type u
_5} {f : α → β → γ} {s : Set α} {t : Set β},   (Set.image2 f s t).Nonempty → s.N
onempty
-/
theorem Nonempty.of_sups_left : (s ⊻ t).Nonempty → s.Nonempty :=
  Nonempty.of_image2_left
/-
**Set.Nonempty.of_sups_right** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nonempty`。
形式化陈述：∀ {α : Type u_2} [inst : SemilatticeSup α] {s t : Set α}, (s ⊻ t).Nonempty
 → t.Nonempty
参数：s ⊻ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.of_image2_right`：∀ {α : Type u_1} {β : Type u_3} {γ : Type 
u_5} {f : α → β → γ} {s : Set α} {t : Set β},   (Set.image2 f s t).Nonempty → t.
Nonempty
-/
theorem Nonempty.of_sups_right : (s ⊻ t).Nonempty → t.Nonempty :=
  Nonempty.of_image2_right

@[simp]
/-
**Set.empty_sups** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：empty_sups : ∅ ⊻ t = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_empty_left`：image2_empty_left : image2 f ∅ t = ∅
-/
theorem empty_sups : ∅ ⊻ t = ∅ :=
  image2_empty_left

@[simp]
/-
**Set.sups_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sups_empty : s ⊻ ∅ = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_empty_right`：image2_empty_right : image2 f s ∅ = ∅
-/
theorem sups_empty : s ⊻ ∅ = ∅ :=
  image2_empty_right

@[simp]
/-
**Set.sups_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sups_eq_empty : s ⊻ t = ∅ ↔ s = ∅ ∨ t = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_eq_empty_iff`：image2_eq_empty_iff : image2 f s t = ∅ ↔ s = ∅ 
∨ t = ∅
-/
theorem sups_eq_empty : s ⊻ t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image2_eq_empty_iff

@[simp]
/-
**Set.singleton_sups** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：singleton_sups : {a} ⊻ t = t.image fun b => a ⊔ b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_singleton_left`：image2_singleton_left : image2 f {a} t = f a 
'' t
-/
theorem singleton_sups : {a} ⊻ t = t.image fun b => a ⊔ b :=
  image2_singleton_left

@[simp]
/-
**Set.sups_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sups_singleton : s ⊻ {b} = s.image fun a => a ⊔ b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_singleton_right`：image2_singleton_right : image2 f s {b} = (f
un a => f a b) '' s
-/
theorem sups_singleton : s ⊻ {b} = s.image fun a => a ⊔ b :=
  image2_singleton_right
/-
**Set.singleton_sups_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：singleton_sups_singleton : ({a} ⊻ {b} : Set α) = {a ⊔ b}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_singleton`：image2_singleton : image2 f {a} {b} = {f a b}
-/
theorem singleton_sups_singleton : ({a} ⊻ {b} : Set α) = {a ⊔ b} :=
  image2_singleton
/-
**Set.sups_union_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sups_union_left : (s₁ union s₂) ⊻ t = s₁ ⊻ t union s₂ ⊻ t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_union_left`：image2_union_left : image2 f (s union s') t = ima
ge2 f s t union image2 f s' t
-/
theorem sups_union_left : (s₁ ∪ s₂) ⊻ t = s₁ ⊻ t ∪ s₂ ⊻ t :=
  image2_union_left
/-
**Set.sups_union_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sups_union_right : s ⊻ (t₁ union t₂) = s ⊻ t₁ union s ⊻ t₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_union_right`：image2_union_right : image2 f s (t union t') = i
mage2 f s t union image2 f s t'
-/
theorem sups_union_right : s ⊻ (t₁ ∪ t₂) = s ⊻ t₁ ∪ s ⊻ t₂ :=
  image2_union_right
/-
**Set.sups_inter_subset_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sups_inter_subset_left : (s₁ inter s₂) ⊻ t subseteq s₁ ⊻ t inter s₂ ⊻ t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_inter_subset_left`：image2_inter_subset_left : image2 f (s int
er s') t subseteq image2 f s t inter image2 f s' t
-/
theorem sups_inter_subset_left : (s₁ ∩ s₂) ⊻ t ⊆ s₁ ⊻ t ∩ s₂ ⊻ t :=
  image2_inter_subset_left
/-
**Set.sups_inter_subset_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sups_inter_subset_right : s ⊻ (t₁ inter t₂) subseteq s ⊻ t₁ inter s ⊻ t₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_inter_subset_right`：image2_inter_subset_right : image2 f s (t
 inter t') subseteq image2 f s t inter image2 f s t'
-/
theorem sups_inter_subset_right : s ⊻ (t₁ ∩ t₂) ⊆ s ⊻ t₁ ∩ s ⊻ t₂ :=
  image2_inter_subset_right
/-
**Set.image_sups** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_sups (f : F) (s t : Set α) : f '' (s ⊻ t) = f '' s ⊻ f '' t
参数：f : F；s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_image2_distrib`：image_image2_distrib {g : γ -> δ} {f' : α' -> 
β' -> δ} {g₁ : α -> α'} {g₂ : β -> β'} (h_distrib : forall a b, g (f a b) = f' (
g₁ a) (g₂ b)) …
· 使用定理 `SupHomClass.map_sup`：∀ {F : Type u_6} {α : Type u_7} {β : Type u_8} {ins
t : Max α} {inst_1 : Max β} {inst_2 : FunLike F α β}   [self : SupHomClass F α β
] (f : F)…
-/
lemma image_sups (f : F) (s t : Set α) : f '' (s ⊻ t) = f '' s ⊻ f '' t :=
  image_image2_distrib <| map_sup f
/-
**Set.subset_sups_self** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：subset_sups_self : s subseteq s ⊻ s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_sups`：mem_sups : c in s ⊻ t ↔ exists a in s, exists b in t, a ⊔ 
b = c
· 使用定理 `sup_idem`：sup_idem (a : α) : a ⊔ a = a
-/
lemma subset_sups_self : s ⊆ s ⊻ s := fun _a ha ↦ mem_sups.2 ⟨_, ha, _, ha, sup_idem _⟩
/-
**Set.sups_subset_self** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：sups_subset_self : s ⊻ s subseteq s ↔ SupClosed s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.sups_subset_iff`：sups_subset_iff : s ⊻ t subseteq u ↔ forall a in s,
 forall b in t, a ⊔ b in u
-/
lemma sups_subset_self : s ⊻ s ⊆ s ↔ SupClosed s := sups_subset_iff
/-
**Set.sups_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_2} [inst : SemilatticeSup α] {s : Set α}, s ⊻ s = s ↔ SupClo
sed s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `LE.le.ge_iff_eq'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b 
≤ a → (a ≤ b ↔ a = b)
· 使用引理 `Set.subset_sups_self`：subset_sups_self : s subseteq s ⊻ s
· 使用引理 `Set.sups_subset_self`：sups_subset_self : s ⊻ s subseteq s ↔ SupClosed s
-/
@[simp] lemma sups_eq_self : s ⊻ s = s ↔ SupClosed s :=
  subset_sups_self.ge_iff_eq'.symm.trans sups_subset_self
/-
**Set.sep_sups_le** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：sep_sups_le (s t : Set α) (a : α) : {b in s ⊻ t | b <= a} = {b in s | b <=
 a} ⊻ {b in t | b <= a}
参数：s t : Set α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
lemma sep_sups_le (s t : Set α) (a : α) :
    {b ∈ s ⊻ t | b ≤ a} = {b ∈ s | b ≤ a} ⊻ {b ∈ t | b ≤ a} := by ext; aesop

variable (s t u)
/-
**Set.iUnion_image_sup_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_image_sup_left : ⋃ a in s, (· ⊔ ·) a '' t = s ⊻ t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.iUnion_image_left`：iUnion_image_left : ⋃ a in s, f a '' t = image2 f
 s t
-/
theorem iUnion_image_sup_left : ⋃ a ∈ s, (· ⊔ ·) a '' t = s ⊻ t :=
  iUnion_image_left _
/-
**Set.iUnion_image_sup_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_image_sup_right : ⋃ b in t, (· ⊔ b) '' s = s ⊻ t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.iUnion_image_right`：iUnion_image_right : ⋃ b in t, (f · b) '' s = im
age2 f s t
-/
theorem iUnion_image_sup_right : ⋃ b ∈ t, (· ⊔ b) '' s = s ⊻ t :=
  iUnion_image_right _

@[simp]
/-
**Set.image_sup_prod** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_sup_prod (s t : Set α) : Set.image2 (· ⊔ ·) s t = s ⊻ t
参数：s t : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image_sup_prod (s t : Set α) : Set.image2 (· ⊔ ·) s t = s ⊻ t := rfl
/-
**Set.sups_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sups_assoc : s ⊻ t ⊻ u = s ⊻ (t ⊻ u)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_assoc`：image2_assoc {f : δ -> γ -> ε} {g : α -> β -> δ} {f' :
 α -> ε' -> ε} {g' : β -> γ -> ε'} (h_assoc : forall a b c, f (g a b) c = f' a (
g' b c…
· 使用定理 `sup_assoc`：sup_assoc (a b c : α) : a ⊔ b ⊔ c = a ⊔ (b ⊔ c)
-/
theorem sups_assoc : s ⊻ t ⊻ u = s ⊻ (t ⊻ u) := image2_assoc sup_assoc
/-
**Set.sups_comm** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sups_comm : s ⊻ t = t ⊻ s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_comm`：image2_comm {g : β -> α -> γ} (h_comm : forall a b, f a
 b = g b a) : image2 f s t = image2 g t s
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
-/
theorem sups_comm : s ⊻ t = t ⊻ s := image2_comm sup_comm
/-
**Set.sups_left_comm** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sups_left_comm : s ⊻ (t ⊻ u) = t ⊻ (s ⊻ u)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_left_comm`：image2_left_comm {f : α -> δ -> ε} {g : β -> γ -> 
δ} {f' : α -> γ -> δ'} {g' : β -> δ' -> ε} (h_left_comm : forall a b c, f a (g b
 c) = g' b…
· 使用定理 `sup_left_comm`：sup_left_comm (a b c : α) : a ⊔ (b ⊔ c) = b ⊔ (a ⊔ c)
-/
theorem sups_left_comm : s ⊻ (t ⊻ u) = t ⊻ (s ⊻ u) :=
  image2_left_comm sup_left_comm
/-
**Set.sups_right_comm** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sups_right_comm : s ⊻ t ⊻ u = s ⊻ u ⊻ t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_right_comm`：image2_right_comm {f : δ -> γ -> ε} {g : α -> β -
> δ} {f' : α -> γ -> δ'} {g' : δ' -> β -> ε} (h_right_comm : forall a b c, f (g 
a b) c = g'…
· 使用定理 `sup_right_comm`：sup_right_comm (a b c : α) : a ⊔ b ⊔ c = a ⊔ c ⊔ b
-/
theorem sups_right_comm : s ⊻ t ⊻ u = s ⊻ u ⊻ t :=
  image2_right_comm sup_right_comm
/-
**Set.sups_sups_sups_comm** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sups_sups_sups_comm : s ⊻ t ⊻ (u ⊻ v) = s ⊻ u ⊻ (t ⊻ v)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_image2_image2_comm`：image2_image2_image2_comm {f : ε -> ζ -> 
ν} {g : α -> β -> ε} {h : γ -> δ -> ζ} {f' : ε' -> ζ' -> ν} {g' : α -> γ -> ε'} 
{h' : β -> δ -> ζ'}…
· 使用定理 `sup_sup_sup_comm`：sup_sup_sup_comm (a b c d : α) : a ⊔ b ⊔ (c ⊔ d) = a ⊔
 c ⊔ (b ⊔ d)
-/
theorem sups_sups_sups_comm : s ⊻ t ⊻ (u ⊻ v) = s ⊻ u ⊻ (t ⊻ v) :=
  image2_image2_image2_comm sup_sup_sup_comm

end Sups

section Infs

variable [SemilatticeInf α] [SemilatticeInf β] [FunLike F α β] [InfHomClass F α β]
variable (s s₁ s₂ t t₁ t₂ u v : Set α)

/-- `s ⊼ t` is the set of elements of the form `a ⊓ b` where `a ∈ s`, `b ∈ t`. -/
@[instance_reducible]
/-
**Set.hasInfs** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：{α : Type u_2} → [SemilatticeInf α] → HasInfs (Set α)
参数：Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`s ⊼ t` is the set of elements of the form `a ⊓ b` where `a ∈ s`, `b ∈ t`.
-/
protected def hasInfs : HasInfs (Set α) :=
  ⟨image2 (· ⊓ ·)⟩

scoped[SetFamily] attribute [instance] Set.hasInfs

open SetFamily

variable {s s₁ s₂ t t₁ t₂ u} {a b c : α}

@[simp]
/-
**Set.mem_infs** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
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
/-
**Set.inf_mem_infs** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inf_mem_infs : a in s -> b in t -> a ⊓ b in s ⊼ t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image2_of_mem`：mem_image2_of_mem (ha : a in s) (hb : b in t) : f
 a b in image2 f s t
-/
theorem inf_mem_infs : a ∈ s → b ∈ t → a ⊓ b ∈ s ⊼ t :=
  mem_image2_of_mem
/-
**Set.infs_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：infs_subset : s₁ subseteq s₂ -> t₁ subseteq t₂ -> s₁ ⊼ t₁ subseteq s₂ ⊼ t₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_subset`：image2_subset (hs : s subseteq s') (ht : t subseteq t
') : image2 f s t subseteq image2 f s' t'
-/
theorem infs_subset : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ ⊼ t₁ ⊆ s₂ ⊼ t₂ :=
  image2_subset
/-
**Set.infs_subset_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：infs_subset_left : t₁ subseteq t₂ -> s ⊼ t₁ subseteq s ⊼ t₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_subset_left`：image2_subset_left (ht : t subseteq t') : image2
 f s t subseteq image2 f s t'
-/
theorem infs_subset_left : t₁ ⊆ t₂ → s ⊼ t₁ ⊆ s ⊼ t₂ :=
  image2_subset_left
/-
**Set.infs_subset_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：infs_subset_right : s₁ subseteq s₂ -> s₁ ⊼ t subseteq s₂ ⊼ t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_subset_right`：image2_subset_right (hs : s subseteq s') : imag
e2 f s t subseteq image2 f s' t
-/
theorem infs_subset_right : s₁ ⊆ s₂ → s₁ ⊼ t ⊆ s₂ ⊼ t :=
  image2_subset_right
/-
**Set.image_subset_infs_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_subset_infs_left : b in t -> (fun a => a ⊓ b) '' s subseteq s ⊼ t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_subset_image2_left`：image_subset_image2_left (hb : b in t) : (
fun a => f a b) '' s subseteq image2 f s t
-/
theorem image_subset_infs_left : b ∈ t → (fun a => a ⊓ b) '' s ⊆ s ⊼ t :=
  image_subset_image2_left
/-
**Set.image_subset_infs_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_subset_infs_right : a in s -> (a ⊓ ·) '' t subseteq s ⊼ t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_subset_image2_right`：image_subset_image2_right (ha : a in s) :
 f a '' t subseteq image2 f s t
-/
theorem image_subset_infs_right : a ∈ s → (a ⊓ ·) '' t ⊆ s ⊼ t :=
  image_subset_image2_right
/-
**Set.forall_infs_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：forall_infs_iff {p : α -> Prop} : (forall c in s ⊼ t, p c) ↔ forall a in s
, forall b in t, p (a ⊓ b)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.forall_mem_image2`：forall_mem_image2 {p : γ -> Prop} : (forall z in 
image2 f s t, p z) ↔ forall x in s, forall y in t, p (f x y)
-/
theorem forall_infs_iff {p : α → Prop} : (∀ c ∈ s ⊼ t, p c) ↔ ∀ a ∈ s, ∀ b ∈ t, p (a ⊓ b) :=
  forall_mem_image2

@[simp]
/-
**Set.infs_subset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：infs_subset_iff : s ⊼ t subseteq u ↔ forall a in s, forall b in t, a ⊓ b i
n u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_subset_iff`：image2_subset_iff {u : Set γ} : image2 f s t subs
eteq u ↔ forall x in s, forall y in t, f x y in u
-/
theorem infs_subset_iff : s ⊼ t ⊆ u ↔ ∀ a ∈ s, ∀ b ∈ t, a ⊓ b ∈ u :=
  image2_subset_iff

@[simp]
/-
**Set.infs_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：infs_nonempty : (s ⊼ t).Nonempty ↔ s.Nonempty ∧ t.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_nonempty_iff`：image2_nonempty_iff : (image2 f s t).Nonempty ↔
 s.Nonempty ∧ t.Nonempty
-/
theorem infs_nonempty : (s ⊼ t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image2_nonempty_iff
/-
**Set.Nonempty.infs** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nonempty`。
形式化陈述：∀ {α : Type u_2} [inst : SemilatticeInf α] {s t : Set α}, s.Nonempty → t.N
onempty → (s ⊼ t).Nonempty
参数：s ⊼ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.image2`：∀ {α : Type u_1} {β : Type u_3} {γ : Type u_5} {f :
 α → β → γ} {s : Set α} {t : Set β},   s.Nonempty → t.Nonempty → (Set.image2 f s
 t).Nonem…
-/
protected theorem Nonempty.infs : s.Nonempty → t.Nonempty → (s ⊼ t).Nonempty :=
  Nonempty.image2
/-
**Set.Nonempty.of_infs_left** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nonempty`。
形式化陈述：∀ {α : Type u_2} [inst : SemilatticeInf α] {s t : Set α}, (s ⊼ t).Nonempty
 → s.Nonempty
参数：s ⊼ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.of_image2_left`：∀ {α : Type u_1} {β : Type u_3} {γ : Type u
_5} {f : α → β → γ} {s : Set α} {t : Set β},   (Set.image2 f s t).Nonempty → s.N
onempty
-/
theorem Nonempty.of_infs_left : (s ⊼ t).Nonempty → s.Nonempty :=
  Nonempty.of_image2_left
/-
**Set.Nonempty.of_infs_right** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nonempty`。
形式化陈述：∀ {α : Type u_2} [inst : SemilatticeInf α] {s t : Set α}, (s ⊼ t).Nonempty
 → t.Nonempty
参数：s ⊼ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.of_image2_right`：∀ {α : Type u_1} {β : Type u_3} {γ : Type 
u_5} {f : α → β → γ} {s : Set α} {t : Set β},   (Set.image2 f s t).Nonempty → t.
Nonempty
-/
theorem Nonempty.of_infs_right : (s ⊼ t).Nonempty → t.Nonempty :=
  Nonempty.of_image2_right

@[simp]
/-
**Set.empty_infs** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：empty_infs : ∅ ⊼ t = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_empty_left`：image2_empty_left : image2 f ∅ t = ∅
-/
theorem empty_infs : ∅ ⊼ t = ∅ :=
  image2_empty_left

@[simp]
/-
**Set.infs_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：infs_empty : s ⊼ ∅ = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_empty_right`：image2_empty_right : image2 f s ∅ = ∅
-/
theorem infs_empty : s ⊼ ∅ = ∅ :=
  image2_empty_right

@[simp]
/-
**Set.infs_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：infs_eq_empty : s ⊼ t = ∅ ↔ s = ∅ ∨ t = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_eq_empty_iff`：image2_eq_empty_iff : image2 f s t = ∅ ↔ s = ∅ 
∨ t = ∅
-/
theorem infs_eq_empty : s ⊼ t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image2_eq_empty_iff

@[simp]
/-
**Set.singleton_infs** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：singleton_infs : {a} ⊼ t = t.image fun b => a ⊓ b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_singleton_left`：image2_singleton_left : image2 f {a} t = f a 
'' t
-/
theorem singleton_infs : {a} ⊼ t = t.image fun b => a ⊓ b :=
  image2_singleton_left

@[simp]
/-
**Set.infs_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：infs_singleton : s ⊼ {b} = s.image fun a => a ⊓ b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_singleton_right`：image2_singleton_right : image2 f s {b} = (f
un a => f a b) '' s
-/
theorem infs_singleton : s ⊼ {b} = s.image fun a => a ⊓ b :=
  image2_singleton_right
/-
**Set.singleton_infs_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：singleton_infs_singleton : ({a} ⊼ {b} : Set α) = {a ⊓ b}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_singleton`：image2_singleton : image2 f {a} {b} = {f a b}
-/
theorem singleton_infs_singleton : ({a} ⊼ {b} : Set α) = {a ⊓ b} :=
  image2_singleton
/-
**Set.infs_union_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：infs_union_left : (s₁ union s₂) ⊼ t = s₁ ⊼ t union s₂ ⊼ t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_union_left`：image2_union_left : image2 f (s union s') t = ima
ge2 f s t union image2 f s' t
-/
theorem infs_union_left : (s₁ ∪ s₂) ⊼ t = s₁ ⊼ t ∪ s₂ ⊼ t :=
  image2_union_left
/-
**Set.infs_union_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：infs_union_right : s ⊼ (t₁ union t₂) = s ⊼ t₁ union s ⊼ t₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_union_right`：image2_union_right : image2 f s (t union t') = i
mage2 f s t union image2 f s t'
-/
theorem infs_union_right : s ⊼ (t₁ ∪ t₂) = s ⊼ t₁ ∪ s ⊼ t₂ :=
  image2_union_right
/-
**Set.infs_inter_subset_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：infs_inter_subset_left : (s₁ inter s₂) ⊼ t subseteq s₁ ⊼ t inter s₂ ⊼ t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_inter_subset_left`：image2_inter_subset_left : image2 f (s int
er s') t subseteq image2 f s t inter image2 f s' t
-/
theorem infs_inter_subset_left : (s₁ ∩ s₂) ⊼ t ⊆ s₁ ⊼ t ∩ s₂ ⊼ t :=
  image2_inter_subset_left
/-
**Set.infs_inter_subset_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：infs_inter_subset_right : s ⊼ (t₁ inter t₂) subseteq s ⊼ t₁ inter s ⊼ t₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_inter_subset_right`：image2_inter_subset_right : image2 f s (t
 inter t') subseteq image2 f s t inter image2 f s t'
-/
theorem infs_inter_subset_right : s ⊼ (t₁ ∩ t₂) ⊆ s ⊼ t₁ ∩ s ⊼ t₂ :=
  image2_inter_subset_right
/-
**Set.image_infs** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_infs (f : F) (s t : Set α) : f '' (s ⊼ t) = f '' s ⊼ f '' t
参数：f : F；s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_image2_distrib`：image_image2_distrib {g : γ -> δ} {f' : α' -> 
β' -> δ} {g₁ : α -> α'} {g₂ : β -> β'} (h_distrib : forall a b, g (f a b) = f' (
g₁ a) (g₂ b)) …
· 使用定理 `InfHomClass.map_inf`：∀ {F : Type u_6} {α : Type u_7} {β : Type u_8} {ins
t : Min α} {inst_1 : Min β} {inst_2 : FunLike F α β}   [self : InfHomClass F α β
] (f : F)…
-/
lemma image_infs (f : F) (s t : Set α) : f '' (s ⊼ t) = f '' s ⊼ f '' t :=
  image_image2_distrib <| map_inf f
/-
**Set.subset_infs_self** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：subset_infs_self : s subseteq s ⊼ s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_infs`：mem_infs : c in s ⊼ t ↔ exists a in s, exists b in t, a ⊓ 
b = c
· 使用定理 `inf_idem`：∀ {α : Type u} [inst : SemilatticeInf α] (a : α), a ⊓ a = a
-/
lemma subset_infs_self : s ⊆ s ⊼ s := fun _a ha ↦ mem_infs.2 ⟨_, ha, _, ha, inf_idem _⟩
/-
**Set.infs_self_subset** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：infs_self_subset : s ⊼ s subseteq s ↔ InfClosed s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.infs_subset_iff`：infs_subset_iff : s ⊼ t subseteq u ↔ forall a in s,
 forall b in t, a ⊓ b in u
-/
lemma infs_self_subset : s ⊼ s ⊆ s ↔ InfClosed s := infs_subset_iff
/-
**Set.infs_self** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_2} [inst : SemilatticeInf α] {s : Set α}, s ⊼ s = s ↔ InfClo
sed s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `LE.le.ge_iff_eq'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b 
≤ a → (a ≤ b ↔ a = b)
· 使用引理 `Set.subset_infs_self`：subset_infs_self : s subseteq s ⊼ s
· 使用引理 `Set.infs_self_subset`：infs_self_subset : s ⊼ s subseteq s ↔ InfClosed s
-/
@[simp] lemma infs_self : s ⊼ s = s ↔ InfClosed s :=
  subset_infs_self.ge_iff_eq'.symm.trans infs_self_subset
/-
**Set.sep_infs_le** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：sep_infs_le (s t : Set α) (a : α) : {b in s ⊼ t | a <= b} = {b in s | a <=
 b} ⊼ {b in t | a <= b}
参数：s t : Set α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
lemma sep_infs_le (s t : Set α) (a : α) :
    {b ∈ s ⊼ t | a ≤ b} = {b ∈ s | a ≤ b} ⊼ {b ∈ t | a ≤ b} := by ext; aesop

variable (s t u)
/-
**Set.iUnion_image_inf_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_image_inf_left : ⋃ a in s, (a ⊓ ·) '' t = s ⊼ t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.iUnion_image_left`：iUnion_image_left : ⋃ a in s, f a '' t = image2 f
 s t
-/
theorem iUnion_image_inf_left : ⋃ a ∈ s, (a ⊓ ·) '' t = s ⊼ t :=
  iUnion_image_left _
/-
**Set.iUnion_image_inf_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_image_inf_right : ⋃ b in t, (· ⊓ b) '' s = s ⊼ t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.iUnion_image_right`：iUnion_image_right : ⋃ b in t, (f · b) '' s = im
age2 f s t
-/
theorem iUnion_image_inf_right : ⋃ b ∈ t, (· ⊓ b) '' s = s ⊼ t :=
  iUnion_image_right _

@[simp]
/-
**Set.image_inf_prod** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_inf_prod (s t : Set α) : Set.image2 (fun x x_1 => x ⊓ x_1) s t = s ⊼
 t
参数：s t : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image_inf_prod (s t : Set α) : Set.image2 (fun x x_1 => x ⊓ x_1) s t = s ⊼ t := rfl
/-
**Set.infs_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：infs_assoc : s ⊼ t ⊼ u = s ⊼ (t ⊼ u)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_assoc`：image2_assoc {f : δ -> γ -> ε} {g : α -> β -> δ} {f' :
 α -> ε' -> ε} {g' : β -> γ -> ε'} (h_assoc : forall a b c, f (g a b) c = f' a (
g' b c…
· 使用定理 `inf_assoc`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c : α), a ⊓ b ⊓
 c = a ⊓ (b ⊓ c)
-/
theorem infs_assoc : s ⊼ t ⊼ u = s ⊼ (t ⊼ u) := image2_assoc inf_assoc
/-
**Set.infs_comm** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：infs_comm : s ⊼ t = t ⊼ s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_comm`：image2_comm {g : β -> α -> γ} (h_comm : forall a b, f a
 b = g b a) : image2 f s t = image2 g t s
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
-/
theorem infs_comm : s ⊼ t = t ⊼ s := image2_comm inf_comm
/-
**Set.infs_left_comm** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：infs_left_comm : s ⊼ (t ⊼ u) = t ⊼ (s ⊼ u)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_left_comm`：image2_left_comm {f : α -> δ -> ε} {g : β -> γ -> 
δ} {f' : α -> γ -> δ'} {g' : β -> δ' -> ε} (h_left_comm : forall a b c, f a (g b
 c) = g' b…
· 使用定理 `inf_left_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c : α), a ⊓
 (b ⊓ c) = b ⊓ (a ⊓ c)
-/
theorem infs_left_comm : s ⊼ (t ⊼ u) = t ⊼ (s ⊼ u) :=
  image2_left_comm inf_left_comm
/-
**Set.infs_right_comm** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：infs_right_comm : s ⊼ t ⊼ u = s ⊼ u ⊼ t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_right_comm`：image2_right_comm {f : δ -> γ -> ε} {g : α -> β -
> δ} {f' : α -> γ -> δ'} {g' : δ' -> β -> ε} (h_right_comm : forall a b c, f (g 
a b) c = g'…
· 使用定理 `inf_right_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c : α), a 
⊓ b ⊓ c = a ⊓ c ⊓ b
-/
theorem infs_right_comm : s ⊼ t ⊼ u = s ⊼ u ⊼ t :=
  image2_right_comm inf_right_comm
/-
**Set.infs_infs_infs_comm** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：infs_infs_infs_comm : s ⊼ t ⊼ (u ⊼ v) = s ⊼ u ⊼ (t ⊼ v)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_image2_image2_comm`：image2_image2_image2_comm {f : ε -> ζ -> 
ν} {g : α -> β -> ε} {h : γ -> δ -> ζ} {f' : ε' -> ζ' -> ν} {g' : α -> γ -> ε'} 
{h' : β -> δ -> ζ'}…
· 使用定理 `inf_inf_inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c d : α)
, a ⊓ b ⊓ (c ⊓ d) = a ⊓ c ⊓ (b ⊓ d)
-/
theorem infs_infs_infs_comm : s ⊼ t ⊼ (u ⊼ v) = s ⊼ u ⊼ (t ⊼ v) :=
  image2_image2_image2_comm inf_inf_inf_comm

end Infs

open SetFamily

section DistribLattice

variable [DistribLattice α] (s t u : Set α)

/-
**Set.sups_infs_subset_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sups_infs_subset_left : s ⊻ t ⊼ u subseteq (s ⊻ t) ⊼ (s ⊻ u)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_distrib_subset_left`：image2_distrib_subset_left {f : α -> δ -
> ε} {g : β -> γ -> δ} {f₁ : α -> β -> β'} {f₂ : α -> γ -> γ'} {g' : β' -> γ' ->
 ε} (h_distrib : for…
· 使用定理 `sup_inf_left`：sup_inf_left (a b c : α) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c)
-/
theorem sups_infs_subset_left : s ⊻ t ⊼ u ⊆ (s ⊻ t) ⊼ (s ⊻ u) :=
  image2_distrib_subset_left sup_inf_left
/-
**Set.sups_infs_subset_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sups_infs_subset_right : t ⊼ u ⊻ s subseteq (t ⊻ s) ⊼ (u ⊻ s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_distrib_subset_right`：image2_distrib_subset_right {f : δ -> γ
 -> ε} {g : α -> β -> δ} {f₁ : α -> γ -> α'} {f₂ : β -> γ -> β'} {g' : α' -> β' 
-> ε} (h_distrib : fo…
· 使用定理 `sup_inf_right`：sup_inf_right (a b c : α) : a ⊓ b ⊔ c = (a ⊔ c) ⊓ (b ⊔ c)
-/
theorem sups_infs_subset_right : t ⊼ u ⊻ s ⊆ (t ⊻ s) ⊼ (u ⊻ s) :=
  image2_distrib_subset_right sup_inf_right
/-
**Set.infs_sups_subset_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：infs_sups_subset_left : s ⊼ (t ⊻ u) subseteq s ⊼ t ⊻ s ⊼ u
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_distrib_subset_left`：image2_distrib_subset_left {f : α -> δ -
> ε} {g : β -> γ -> δ} {f₁ : α -> β -> β'} {f₂ : α -> γ -> γ'} {g' : β' -> γ' ->
 ε} (h_distrib : for…
· 使用定理 `inf_sup_left`：inf_sup_left (a b c : α) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c
-/
theorem infs_sups_subset_left : s ⊼ (t ⊻ u) ⊆ s ⊼ t ⊻ s ⊼ u :=
  image2_distrib_subset_left inf_sup_left
/-
**Set.infs_sups_subset_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：infs_sups_subset_right : (t ⊻ u) ⊼ s subseteq t ⊼ s ⊻ u ⊼ s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_distrib_subset_right`：image2_distrib_subset_right {f : δ -> γ
 -> ε} {g : α -> β -> δ} {f₁ : α -> γ -> α'} {f₂ : β -> γ -> β'} {g' : α' -> β' 
-> ε} (h_distrib : fo…
· 使用定理 `inf_sup_right`：inf_sup_right (a b c : α) : (a ⊔ b) ⊓ c = a ⊓ c ⊔ b ⊓ c
-/
theorem infs_sups_subset_right : (t ⊻ u) ⊼ s ⊆ t ⊼ s ⊻ u ⊼ s :=
  image2_distrib_subset_right inf_sup_right

end DistribLattice

end Set

open SetFamily

@[simp]
/-
**upperClosure_sups** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperClosure_sups [SemilatticeSup α] (s t : Set α) : upperClosure (s ⊻ t) 
= upperClosure s ⊔ upperClosure t
参数：s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperSet.ext`：ext {s t : UpperSet α} : (s : Set α) = t -> s = t
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
-/
theorem upperClosure_sups [SemilatticeSup α] (s t : Set α) :
    upperClosure (s ⊻ t) = upperClosure s ⊔ upperClosure t := by
  ext a
  simp only [SetLike.mem_coe, mem_upperClosure, Set.mem_sups,
    UpperSet.coe_sup, Set.mem_inter_iff]
  constructor
  · rintro ⟨_, ⟨b, hb, c, hc, rfl⟩, ha⟩
    exact ⟨⟨b, hb, le_sup_left.trans ha⟩, c, hc, le_sup_right.trans ha⟩
  · rintro ⟨⟨b, hb, hab⟩, c, hc, hac⟩
    exact ⟨_, ⟨b, hb, c, hc, rfl⟩, sup_le hab hac⟩

@[simp]
/-
**lowerClosure_infs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerClosure_infs [SemilatticeInf α] (s t : Set α) : lowerClosure (s ⊼ t) 
= lowerClosure s ⊓ lowerClosure t
参数：s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerSet.ext`：∀ {α : Type u_1} [inst : LE α] {s t : LowerSet α}, ↑s = ↑t
 → s = t
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
-/
theorem lowerClosure_infs [SemilatticeInf α] (s t : Set α) :
    lowerClosure (s ⊼ t) = lowerClosure s ⊓ lowerClosure t := by
  ext a
  simp only [SetLike.mem_coe, mem_lowerClosure, Set.mem_infs]
  constructor
  · rintro ⟨_, ⟨b, hb, c, hc, rfl⟩, ha⟩
    exact ⟨⟨b, hb, ha.trans inf_le_left⟩, c, hc, ha.trans inf_le_right⟩
  · rintro ⟨⟨b, hb, hab⟩, c, hc, hac⟩
    exact ⟨_, ⟨b, hb, c, hc, rfl⟩, le_inf hab hac⟩
