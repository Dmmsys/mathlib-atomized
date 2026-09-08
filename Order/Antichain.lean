/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Bounds.Basic
public import Mathlib.Order.Preorder.Chain

/-!
# Antichains

This file defines antichains. An antichain is a set where any two distinct elements are not related.
If the relation is `(≤)`, this corresponds to incomparability and usual order antichains. If the
relation is `G.Adj` for `G : SimpleGraph α`, this corresponds to independent sets of `G`.

## Definitions

* `IsAntichain r s`: Any two elements of `s : Set α` are unrelated by `r : α → α → Prop`.
* `IsStrongAntichain r s`: Any two elements of `s : Set α` are not related by `r : α → α → Prop`
  to a common element.
* `IsMaxAntichain r s`: An antichain such that no antichain strictly including `s` exists.
-/

@[expose] public section

assert_not_exists CompleteLattice

open Function Set Set.Notation

section General

variable {α β : Type*} {r r₁ r₂ : α → α → Prop} {r' : β → β → Prop} {s t : Set α} {a b : α}

/-
**Std.Symm.compl** 是 Mathlib 中的一个定理，位于命名空间 `Std.Symm`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} [Std.Symm r], Std.Symm rᶜ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Std.Symm.symm`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Symm r] (a 
b : α), r a b → r b a
-/
protected instance Std.Symm.compl [Std.Symm r] : Std.Symm rᶜ where
  symm a b hr hr' := hr <| symm b a hr'

@[deprecated (since := "2026-06-10")] alias Symmetric.compl := Std.Symm.compl

/-- An antichain is a set such that no two distinct elements are related. -/
/-
**IsAntichain** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsAntichain (r : α -> α -> Prop) (s : Set α) : Prop
参数：r : α -> α -> Prop；s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An antichain is a set such that no two distinct elements are related.
-/
def IsAntichain (r : α → α → Prop) (s : Set α) : Prop :=
  s.Pairwise rᶜ

namespace IsAntichain

/-
**IsAntichain.empty** 是 Mathlib 中的一个定理，位于命名空间 `IsAntichain`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop}, IsAntichain r ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.pairwise_empty`：pairwise_empty (r : α -> α -> Prop) : (∅ : Set α).Pa
irwise r
-/
@[simp] protected theorem empty : IsAntichain r ∅ :=
  pairwise_empty _
/-
**IsAntichain.singleton** 是 Mathlib 中的一个定理，位于命名空间 `IsAntichain`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} {a : α}, IsAntichain r {a}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.pairwise_singleton`：pairwise_singleton (a : α) (r : α -> α -> Prop) 
: Set.Pairwise {a} r
-/
@[simp] protected theorem singleton : IsAntichain r {a} :=
  pairwise_singleton _ _
/-
**IsAntichain.subset** 是 Mathlib 中的一个定理，位于命名空间 `IsAntichain`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} {s t : Set α}, IsAntichain r s → t ⊆ s
 → IsAntichain r t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Pairwise.mono`：∀ {α : Type u_1} {r : α → α → Prop} {s t : Set α}, t 
⊆ s → s.Pairwise r → t.Pairwise r
-/
protected theorem subset (hs : IsAntichain r s) (h : t ⊆ s) : IsAntichain r t :=
  hs.mono h
/-
**IsAntichain.mono** 是 Mathlib 中的一个定理，位于命名空间 `IsAntichain`。
形式化陈述：mono (hs : IsAntichain r₁ s) (h : r₂ <= r₁) : IsAntichain r₂ s
参数：hs : IsAntichain r₁ s；h : r₂ <= r₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Pairwise.mono'`：∀ {α : Type u_1} {r p : α → α → Prop} {s : Set α}, r
 ≤ p → s.Pairwise r → s.Pairwise p
· 使用定理 `compl_le_compl`：compl_le_compl (h : a <= b) : bᶜ <= aᶜ
-/
theorem mono (hs : IsAntichain r₁ s) (h : r₂ ≤ r₁) : IsAntichain r₂ s :=
  hs.mono' <| compl_le_compl h
/-
**IsAntichain.mono_on** 是 Mathlib 中的一个定理，位于命名空间 `IsAntichain`。
形式化陈述：mono_on (hs : IsAntichain r₁ s) (h : s.Pairwise fun ⦃a b⦄ => r₂ a b -> r₁ 
a b) : IsAntichain r₂ s
参数：hs : IsAntichain r₁ s；h : s.Pairwise fun ⦃a b⦄ => r₂ a b -> r₁ a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Pairwise.imp_on`：∀ {α : Type u_1} {r p : α → α → Prop} {s : Set α}, 
s.Pairwise r → (s.Pairwise fun ⦃a b⦄ => r a b → p a b) → s.Pairwise p
· 使用定理 `Set.Pairwise.imp`：∀ {α : Type u_1} {r p : α → α → Prop} {s : Set α}, s.P
airwise r → (∀ ⦃a b : α⦄, r a b → p a b) → s.Pairwise p
-/
theorem mono_on (hs : IsAntichain r₁ s) (h : s.Pairwise fun ⦃a b⦄ => r₂ a b → r₁ a b) :
    IsAntichain r₂ s :=
  hs.imp_on <| h.imp fun _ _ h h₁ h₂ => h₁ <| h h₂
/-
**IsAntichain.eq** 是 Mathlib 中的一个定理，位于命名空间 `IsAntichain`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α}, IsAntichain r s → ∀ {a b 
: α}, a ∈ s → b ∈ s → r a b → a = b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Pairwise.eq`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α} {a b : 
α}, s.Pairwise r → a ∈ s → b ∈ s → ¬r a b → a = b
· 使用定理 `not_not_intro`：∀ {p : Prop}, p → ¬¬p
-/
protected theorem eq (hs : IsAntichain r s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) (h : r a b) :
    a = b :=
  Set.Pairwise.eq hs ha hb <| not_not_intro h
/-
**IsAntichain.eq'** 是 Mathlib 中的一个定理，位于命名空间 `IsAntichain`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α}, IsAntichain r s → ∀ {a b 
: α}, a ∈ s → b ∈ s → r b a → a = b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsAntichain.eq`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α}, IsAntic
hain r s → ∀ {a b : α}, a ∈ s → b ∈ s → r a b → a = b
-/
protected theorem eq' (hs : IsAntichain r s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) (h : r b a) :
    a = b :=
  (hs.eq hb ha h).symm
/-
**IsAntichain.antisymm** 是 Mathlib 中的一个定理，位于命名空间 `IsAntichain`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop}, IsAntichain r Set.univ → Std.Antisymm
 r
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAntichain.eq`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α}, IsAntic
hain r s → ∀ {a b : α}, a ∈ s → b ∈ s → r a b → a = b
· 使用定理 `trivial`：True
-/
protected theorem antisymm (h : IsAntichain r univ) : Std.Antisymm r :=
  ⟨fun _ _ ha _ => h.eq trivial trivial ha⟩

@[deprecated (since := "2026-01-06")] protected alias isAntisymm := antisymm
/-
**IsAntichain.subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `IsAntichain`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α} [Std.Trichotomous r], IsAn
tichain r s → s.Subsingleton
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `trichotomous_of`：trichotomous_of [Std.Trichotomous r] : forall a b : α, 
a ≺ b ∨ a = b ∨ b ≺ a
· 使用定理 `IsAntichain.eq`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α}, IsAntic
hain r s → ∀ {a b : α}, a ∈ s → b ∈ s → r a b → a = b
· 使用定理 `IsAntichain.eq'`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α}, IsAnti
chain r s → ∀ {a b : α}, a ∈ s → b ∈ s → r b a → a = b
-/
protected theorem subsingleton [Std.Trichotomous r] (h : IsAntichain r s) : s.Subsingleton := by
  rintro a ha b hb
  obtain hab | hab | hab := trichotomous_of r a b
  · exact h.eq ha hb hab
  · exact hab
  · exact h.eq' ha hb hab
/-
**IsAntichain.flip** 是 Mathlib 中的一个定理，位于命名空间 `IsAntichain`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α}, IsAntichain r s → IsAntic
hain (flip r) s
参数：flip r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
protected theorem flip (hs : IsAntichain r s) : IsAntichain (flip r) s := fun _ ha _ hb h =>
  hs hb ha h.symm
/-
**IsAntichain.swap** 是 Mathlib 中的一个定理，位于命名空间 `IsAntichain`。
形式化陈述：swap (hs : IsAntichain r s) : IsAntichain (swap r) s
参数：hs : IsAntichain r s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAntichain.flip`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α}, IsAnt
ichain r s → IsAntichain (flip r) s
-/
theorem swap (hs : IsAntichain r s) : IsAntichain (swap r) s :=
  hs.flip
/-
**IsAntichain.image** 是 Mathlib 中的一个定理，位于命名空间 `IsAntichain`。
形式化陈述：image (hs : IsAntichain r s) (f : α -> β) (h : forall ⦃a b⦄, r' (f a) (f b
) -> r a b) : IsAntichain r' (f '' s)
参数：hs : IsAntichain r s；f : α -> β；h : forall ⦃a b⦄, r' (f a) (f b) -> r a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
-/
theorem image (hs : IsAntichain r s) (f : α → β) (h : ∀ ⦃a b⦄, r' (f a) (f b) → r a b) :
    IsAntichain r' (f '' s) := by
  rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩ hbc hr
  exact hs hb hc (ne_of_apply_ne _ hbc) (h hr)
/-
**IsAntichain.preimage** 是 Mathlib 中的一个定理，位于命名空间 `IsAntichain`。
形式化陈述：preimage (hs : IsAntichain r s) {f : β -> α} (hf : Injective f) (h : foral
l ⦃a b⦄, r' a b -> r (f a) (f b)) : IsAntichain r' (f ⁻¹' s)
参数：hs : IsAntichain r s；hf : Injective f；h : forall ⦃a b⦄, r' a b -> r (f a) (f 
b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
-/
theorem preimage (hs : IsAntichain r s) {f : β → α} (hf : Injective f)
    (h : ∀ ⦃a b⦄, r' a b → r (f a) (f b)) : IsAntichain r' (f ⁻¹' s) := fun _ hb _ hc hbc hr =>
  hs hb hc (hf.ne hbc) <| h hr
/-
**IsAntichain._root_.isAntichain_insert** 是 Mathlib 中的一个定理，位于命名空间 `IsAntichain`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.isAntichain_insert :
    IsAntichain r (insert a s) ↔ IsAntichain r s ∧ ∀ ⦃b⦄, b ∈ s → a ≠ b → ¬r a b ∧ ¬r b a :=
  Set.pairwise_insert
/-
**IsAntichain.insert** 是 Mathlib 中的一个定理，位于命名空间 `IsAntichain`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α} {a : α},   IsAntichain r s
 →     (∀ ⦃b : α⦄, b ∈ s → a ≠ b → ¬r b a) → (∀ ⦃b : α⦄, b ∈ s → a ≠ b → ¬r a b)
 → IsAntichain r (insert a s)
参数：∀ ⦃b : α⦄, b ∈ s → a ≠ b → ¬r b a；∀ ⦃b : α⦄, b ∈ s → a ≠ b → ¬r a b；insert a 
s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isAntichain_insert`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α} {a :
 α},   IsAntichain r (insert a s) ↔ IsAntichain r s ∧ ∀ ⦃b : α⦄, b ∈ s → a ≠ b →
 ¬r a b …
-/
protected theorem insert (hs : IsAntichain r s) (hl : ∀ ⦃b⦄, b ∈ s → a ≠ b → ¬r b a)
    (hr : ∀ ⦃b⦄, b ∈ s → a ≠ b → ¬r a b) : IsAntichain r (insert a s) :=
  isAntichain_insert.2 ⟨hs, fun _ hb hab => ⟨hr hb hab, hl hb hab⟩⟩
/-
**IsAntichain._root_.isAntichain_insert_of_symm** 是 Mathlib 中的一个定理，位于命名空间 `IsAnt
ichain`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.isAntichain_insert_of_symm [Std.Symm r] :
    IsAntichain r (insert a s) ↔ IsAntichain r s ∧ ∀ ⦃b⦄, b ∈ s → a ≠ b → ¬r a b :=
  pairwise_insert_of_symm

@[deprecated (since := "2026-06-10")]
alias _root_.isAntichain_insert_of_symmetric := _root_.isAntichain_insert_of_symm
/-
**IsAntichain.insert_of_symm** 是 Mathlib 中的一个定理，位于命名空间 `IsAntichain`。
形式化陈述：insert_of_symm (hs : IsAntichain r s) [Std.Symm r] (h : forall ⦃b⦄, b in s
 -> a != b -> ¬r a b) : IsAntichain r (insert a s)
参数：hs : IsAntichain r s；h : forall ⦃b⦄, b in s -> a != b -> ¬r a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isAntichain_insert_of_symm`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set
 α} {a : α} [Std.Symm r],   IsAntichain r (insert a s) ↔ IsAntichain r s ∧ ∀ ⦃b 
: α⦄, b ∈ s → a …
-/
theorem insert_of_symm (hs : IsAntichain r s) [Std.Symm r] (h : ∀ ⦃b⦄, b ∈ s → a ≠ b → ¬r a b) :
    IsAntichain r (insert a s) :=
  isAntichain_insert_of_symm.mpr ⟨hs, h⟩

@[deprecated (since := "2026-06-10")] alias insert_of_symmetric := insert_of_symm
/-
**IsAntichain.image_relEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `IsAntichain`。
形式化陈述：image_relEmbedding (hs : IsAntichain r s) (φ : r ↪r r') : IsAntichain r' (
φ '' s)
参数：hs : IsAntichain r s；φ : r ↪r r'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `RelEmbedding.map_rel_iff`：map_rel_iff (f : r ↪r s) {a b} : s (f a) (f b)
 ↔ r a b
-/
theorem image_relEmbedding (hs : IsAntichain r s) (φ : r ↪r r') : IsAntichain r' (φ '' s) := by
  intro b hb b' hb' h₁ h₂
  rw [Set.mem_image] at hb hb'
  obtain ⟨⟨a, has, rfl⟩, ⟨a', has', rfl⟩⟩ := hb, hb'
  exact hs has has' (fun haa' => h₁ (by rw [haa'])) (φ.map_rel_iff.mp h₂)
/-
**IsAntichain.preimage_relEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `IsAntichain`。
形式化陈述：preimage_relEmbedding {t : Set β} (ht : IsAntichain r' t) (φ : r ↪r r') : 
IsAntichain r (φ ⁻¹' t)
参数：ht : IsAntichain r' t；φ : r ↪r r'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelEmbedding.injective`：injective (f : r ↪r s) : Injective f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `RelEmbedding.map_rel_iff`：map_rel_iff (f : r ↪r s) {a b} : s (f a) (f b)
 ↔ r a b
-/
theorem preimage_relEmbedding {t : Set β} (ht : IsAntichain r' t) (φ : r ↪r r') :
    IsAntichain r (φ ⁻¹' t) := fun _ ha _s ha' hne hle =>
  ht ha ha' (fun h => hne (φ.injective h)) (φ.map_rel_iff.mpr hle)
/-
**IsAntichain.image_relIso** 是 Mathlib 中的一个定理，位于命名空间 `IsAntichain`。
形式化陈述：image_relIso (hs : IsAntichain r s) (φ : r ≃r r') : IsAntichain r' (φ '' s
)
参数：hs : IsAntichain r s；φ : r ≃r r'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAntichain.image_relEmbedding`：image_relEmbedding (hs : IsAntichain r s
) (φ : r ↪r r') : IsAntichain r' (φ '' s)
-/
theorem image_relIso (hs : IsAntichain r s) (φ : r ≃r r') : IsAntichain r' (φ '' s) :=
  hs.image_relEmbedding φ.toRelEmbedding
/-
**IsAntichain.preimage_relIso** 是 Mathlib 中的一个定理，位于命名空间 `IsAntichain`。
形式化陈述：preimage_relIso {t : Set β} (hs : IsAntichain r' t) (φ : r ≃r r') : IsAnti
chain r (φ ⁻¹' t)
参数：hs : IsAntichain r' t；φ : r ≃r r'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAntichain.preimage_relEmbedding`：preimage_relEmbedding {t : Set β} (ht
 : IsAntichain r' t) (φ : r ↪r r') : IsAntichain r (φ ⁻¹' t)
-/
theorem preimage_relIso {t : Set β} (hs : IsAntichain r' t) (φ : r ≃r r') :
    IsAntichain r (φ ⁻¹' t) :=
  hs.preimage_relEmbedding φ.toRelEmbedding
/-
**IsAntichain.image_relEmbedding_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsAntichain`。
形式化陈述：image_relEmbedding_iff {φ : r ↪r r'} : IsAntichain r' (φ '' s) ↔ IsAnticha
in r s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.subst`：∀ {α : Sort u} {motive : α → Prop} {a b : α}, a = b → motive a
 → motive b
· 使用定理 `Function.Injective.preimage_image`：∀ {α : Type u_1} {β : Type u_2} {f : 
α → β}, Function.Injective f → ∀ (s : Set α), f ⁻¹' f '' s = s
· 使用定理 `RelEmbedding.injective`：injective (f : r ↪r s) : Injective f
· 使用定理 `IsAntichain.preimage_relEmbedding`：preimage_relEmbedding {t : Set β} (ht
 : IsAntichain r' t) (φ : r ↪r r') : IsAntichain r (φ ⁻¹' t)
· 使用定理 `IsAntichain.image_relEmbedding`：image_relEmbedding (hs : IsAntichain r s
) (φ : r ↪r r') : IsAntichain r' (φ '' s)
-/
theorem image_relEmbedding_iff {φ : r ↪r r'} : IsAntichain r' (φ '' s) ↔ IsAntichain r s :=
  ⟨fun h => (φ.injective.preimage_image s).subst (h.preimage_relEmbedding φ), fun h =>
    h.image_relEmbedding φ⟩
/-
**IsAntichain.image_relIso_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsAntichain`。
形式化陈述：image_relIso_iff {φ : r ≃r r'} : IsAntichain r' (φ '' s) ↔ IsAntichain r s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAntichain.image_relEmbedding_iff`：image_relEmbedding_iff {φ : r ↪r r'}
 : IsAntichain r' (φ '' s) ↔ IsAntichain r s
-/
theorem image_relIso_iff {φ : r ≃r r'} : IsAntichain r' (φ '' s) ↔ IsAntichain r s :=
  @image_relEmbedding_iff _ _ _ _ _ (φ : r ↪r r')
/-
**IsAntichain.image_embedding** 是 Mathlib 中的一个定理，位于命名空间 `IsAntichain`。
形式化陈述：image_embedding [LE α] [LE β] (hs : IsAntichain (· <= ·) s) (φ : α ↪o β) :
 IsAntichain (· <= ·) (φ '' s)
参数：hs : IsAntichain (· <= ·) s；φ : α ↪o β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAntichain.image_relEmbedding`：image_relEmbedding (hs : IsAntichain r s
) (φ : r ↪r r') : IsAntichain r' (φ '' s)
-/
theorem image_embedding [LE α] [LE β] (hs : IsAntichain (· ≤ ·) s) (φ : α ↪o β) :
    IsAntichain (· ≤ ·) (φ '' s) :=
  image_relEmbedding hs _
/-
**IsAntichain.preimage_embedding** 是 Mathlib 中的一个定理，位于命名空间 `IsAntichain`。
形式化陈述：preimage_embedding [LE α] [LE β] {t : Set β} (ht : IsAntichain (· <= ·) t)
 (φ : α ↪o β) : IsAntichain (· <= ·) (φ ⁻¹' t)
参数：ht : IsAntichain (· <= ·) t；φ : α ↪o β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAntichain.preimage_relEmbedding`：preimage_relEmbedding {t : Set β} (ht
 : IsAntichain r' t) (φ : r ↪r r') : IsAntichain r (φ ⁻¹' t)
-/
theorem preimage_embedding [LE α] [LE β] {t : Set β} (ht : IsAntichain (· ≤ ·) t) (φ : α ↪o β) :
    IsAntichain (· ≤ ·) (φ ⁻¹' t) :=
  preimage_relEmbedding ht _
/-
**IsAntichain.image_embedding_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsAntichain`。
形式化陈述：image_embedding_iff [LE α] [LE β] {φ : α ↪o β} : IsAntichain (· <= ·) (φ '
' s) ↔ IsAntichain (· <= ·) s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAntichain.image_relEmbedding_iff`：image_relEmbedding_iff {φ : r ↪r r'}
 : IsAntichain r' (φ '' s) ↔ IsAntichain r s
-/
theorem image_embedding_iff [LE α] [LE β] {φ : α ↪o β} :
    IsAntichain (· ≤ ·) (φ '' s) ↔ IsAntichain (· ≤ ·) s :=
  image_relEmbedding_iff
/-
**IsAntichain.image_iso** 是 Mathlib 中的一个定理，位于命名空间 `IsAntichain`。
形式化陈述：image_iso [LE α] [LE β] (hs : IsAntichain (· <= ·) s) (φ : α ≃o β) : IsAnt
ichain (· <= ·) (φ '' s)
参数：hs : IsAntichain (· <= ·) s；φ : α ≃o β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAntichain.image_relEmbedding`：image_relEmbedding (hs : IsAntichain r s
) (φ : r ↪r r') : IsAntichain r' (φ '' s)
-/
theorem image_iso [LE α] [LE β] (hs : IsAntichain (· ≤ ·) s) (φ : α ≃o β) :
    IsAntichain (· ≤ ·) (φ '' s) :=
  image_relEmbedding hs _
/-
**IsAntichain.image_iso_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsAntichain`。
形式化陈述：image_iso_iff [LE α] [LE β] {φ : α ≃o β} : IsAntichain (· <= ·) (φ '' s) ↔
 IsAntichain (· <= ·) s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAntichain.image_relEmbedding_iff`：image_relEmbedding_iff {φ : r ↪r r'}
 : IsAntichain r' (φ '' s) ↔ IsAntichain r s
-/
theorem image_iso_iff [LE α] [LE β] {φ : α ≃o β} :
    IsAntichain (· ≤ ·) (φ '' s) ↔ IsAntichain (· ≤ ·) s :=
  image_relEmbedding_iff
/-
**IsAntichain.preimage_iso** 是 Mathlib 中的一个定理，位于命名空间 `IsAntichain`。
形式化陈述：preimage_iso [LE α] [LE β] {t : Set β} (ht : IsAntichain (· <= ·) t) (φ : 
α ≃o β) : IsAntichain (· <= ·) (φ ⁻¹' t)
参数：ht : IsAntichain (· <= ·) t；φ : α ≃o β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAntichain.preimage_relEmbedding`：preimage_relEmbedding {t : Set β} (ht
 : IsAntichain r' t) (φ : r ↪r r') : IsAntichain r (φ ⁻¹' t)
-/
theorem preimage_iso [LE α] [LE β] {t : Set β} (ht : IsAntichain (· ≤ ·) t) (φ : α ≃o β) :
    IsAntichain (· ≤ ·) (φ ⁻¹' t) :=
  preimage_relEmbedding ht _
/-
**IsAntichain.preimage_iso_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsAntichain`。
形式化陈述：preimage_iso_iff [LE α] [LE β] {t : Set β} {φ : α ≃o β} : IsAntichain (· <
= ·) (φ ⁻¹' t) ↔ IsAntichain (· <= ·) t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.subst`：∀ {α : Sort u} {motive : α → Prop} {a b : α}, a = b → motive a
 → motive b
· 使用定理 `OrderIso.image_preimage`：image_preimage (e : α ≃o β) (s : Set β) : e '' 
e ⁻¹' s = s
· 使用定理 `IsAntichain.image_iso`：image_iso [LE α] [LE β] (hs : IsAntichain (· <= ·
) s) (φ : α ≃o β) : IsAntichain (· <= ·) (φ '' s)
· 使用定理 `IsAntichain.preimage_iso`：preimage_iso [LE α] [LE β] {t : Set β} (ht : I
sAntichain (· <= ·) t) (φ : α ≃o β) : IsAntichain (· <= ·) (φ ⁻¹' t)
-/
theorem preimage_iso_iff [LE α] [LE β] {t : Set β} {φ : α ≃o β} :
    IsAntichain (· ≤ ·) (φ ⁻¹' t) ↔ IsAntichain (· ≤ ·) t :=
  ⟨fun h => (φ.image_preimage t).subst (h.image_iso φ), fun h => h.preimage_iso _⟩
/-
**IsAntichain.to_dual** 是 Mathlib 中的一个定理，位于命名空间 `IsAntichain`。
形式化陈述：to_dual [LE α] (hs : IsAntichain (· <= ·) s) : @IsAntichain αᵒᵈ (· <= ·) s
参数：hs : IsAntichain (· <= ·) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
theorem to_dual [LE α] (hs : IsAntichain (· ≤ ·) s) : @IsAntichain αᵒᵈ (· ≤ ·) s :=
  fun _ ha _ hb hab => hs hb ha hab.symm
/-
**IsAntichain.to_dual_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsAntichain`。
形式化陈述：to_dual_iff [LE α] : IsAntichain (· <= ·) s ↔ @IsAntichain αᵒᵈ (· <= ·) s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAntichain.to_dual`：to_dual [LE α] (hs : IsAntichain (· <= ·) s) : @IsA
ntichain αᵒᵈ (· <= ·) s
-/
theorem to_dual_iff [LE α] : IsAntichain (· ≤ ·) s ↔ @IsAntichain αᵒᵈ (· ≤ ·) s :=
  ⟨to_dual, to_dual⟩
/-
**IsAntichain.image_compl** 是 Mathlib 中的一个定理，位于命名空间 `IsAntichain`。
形式化陈述：image_compl [BooleanAlgebra α] (hs : IsAntichain (· <= ·) s) : IsAntichain
 (· <= ·) (compl '' s)
参数：hs : IsAntichain (· <= ·) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAntichain.flip`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α}, IsAnt
ichain r s → IsAntichain (flip r) s
· 使用定理 `IsAntichain.image_embedding`：image_embedding [LE α] [LE β] (hs : IsAntic
hain (· <= ·) s) (φ : α ↪o β) : IsAntichain (· <= ·) (φ '' s)
-/
theorem image_compl [BooleanAlgebra α] (hs : IsAntichain (· ≤ ·) s) :
    IsAntichain (· ≤ ·) (compl '' s) :=
  (hs.image_embedding (OrderIso.compl α).toOrderEmbedding).flip
/-
**IsAntichain.preimage_compl** 是 Mathlib 中的一个定理，位于命名空间 `IsAntichain`。
形式化陈述：preimage_compl [BooleanAlgebra α] (hs : IsAntichain (· <= ·) s) : IsAntich
ain (· <= ·) (compl ⁻¹' s)
参数：hs : IsAntichain (· <= ·) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `compl_inj_iff`：compl_inj_iff : xᶜ = yᶜ ↔ x = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `compl_le_compl`：compl_le_compl (h : a <= b) : bᶜ <= aᶜ
-/
theorem preimage_compl [BooleanAlgebra α] (hs : IsAntichain (· ≤ ·) s) :
    IsAntichain (· ≤ ·) (compl ⁻¹' s) := fun _ ha _ ha' hne hle =>
  hs ha' ha (fun h => hne (compl_inj_iff.mp h.symm)) (compl_le_compl hle)
/-
**IsAntichain.diff** 是 Mathlib 中的一个定理，位于命名空间 `IsAntichain`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} {s t : Set α}, IsAntichain r s → IsAnt
ichain r (s \ t)
参数：s \ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAntichain.subset`：∀ {α : Type u_1} {r : α → α → Prop} {s t : Set α}, I
sAntichain r s → t ⊆ s → IsAntichain r t
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
-/
@[simp] protected theorem diff {s t : Set α} (h : IsAntichain r s) : IsAntichain r (s \ t) :=
  h.subset Set.sdiff_subset

end IsAntichain

/-
**isAntichain_preimage_subtypeVal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isAntichain_preimage_subtypeVal (s t : Set α) : @IsAntichain ↑s (r · ·) (s
 ↓inter t) ↔ IsAntichain r (s inter t)
参数：s t : Set α。
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
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isAntichain_preimage_subtypeVal (s t : Set α) :
    @IsAntichain ↑s (r · ·) (s ↓∩ t) ↔ IsAntichain r (s ∩ t) := by
  simp [IsAntichain, Set.Pairwise]
/-
**isAntichain_coe_univ_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isAntichain_coe_univ_iff {s : Set α} : @IsAntichain ↑s (r · ·) univ ↔ IsAn
tichain r s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `isAntichain_preimage_subtypeVal`：isAntichain_preimage_subtypeVal (s t : 
Set α) : @IsAntichain ↑s (r · ·) (s ↓inter t) ↔ IsAntichain r (s inter t)
-/
theorem isAntichain_coe_univ_iff {s : Set α} : @IsAntichain ↑s (r · ·) univ ↔ IsAntichain r s := by
  simpa using isAntichain_preimage_subtypeVal s univ
/-
**isAntichain_union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isAntichain_union : IsAntichain r (s union t) ↔ IsAntichain r s ∧ IsAntich
ain r t ∧ forall a in s, forall b in t, a != b -> rᶜ a b ∧ rᶜ b a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsAntichain.eq_1`：∀ {α : Type u_1} (r : α → α → Prop) (s : Set α), IsAnt
ichain r s = s.Pairwise rᶜ
· 使用定理 `Set.pairwise_union`：pairwise_union : (s union t).Pairwise r ↔ s.Pairwise
 r ∧ t.Pairwise r ∧ forall a in s, forall b in t, a != b -> r a b ∧ r b a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isAntichain_union :
    IsAntichain r (s ∪ t) ↔
      IsAntichain r s ∧ IsAntichain r t ∧ ∀ a ∈ s, ∀ b ∈ t, a ≠ b → rᶜ a b ∧ rᶜ b a := by
  rw [IsAntichain, IsAntichain, IsAntichain, pairwise_union]
/-
**Set.Subsingleton.isAntichain** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Subsingleton.isAntichain (hs : s.Subsingleton) (r : α -> α -> Prop) : 
IsAntichain r s
参数：hs : s.Subsingleton；r : α -> α -> Prop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.pairwise`：∀ {α : Type u_1} {s : Set α}, s.Subsingleton 
→ ∀ (r : α → α → Prop), s.Pairwise r
-/
theorem Set.Subsingleton.isAntichain (hs : s.Subsingleton) (r : α → α → Prop) : IsAntichain r s :=
  hs.pairwise _

/-- A set which is simultaneously a chain and antichain is subsingleton. -/
/-
**subsingleton_of_isChain_of_isAntichain** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：subsingleton_of_isChain_of_isAntichain (hs : IsChain r s) (ht : IsAntichai
n r s) : s.Subsingleton
参数：hs : IsChain r s；ht : IsAntichain r s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a

--- 原说明 ---
A set which is simultaneously a chain and antichain is subsingleton.
-/
lemma subsingleton_of_isChain_of_isAntichain (hs : IsChain r s) (ht : IsAntichain r s) :
    s.Subsingleton := by
  intro x hx y hy
  by_contra! hne
  cases hs hx hy hne with
  | inl h => exact ht hx hy hne h
  | inr h => exact ht hy hx hne.symm h
/-
**isChain_and_isAntichain_iff_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isChain_and_isAntichain_iff_subsingleton : IsChain r s ∧ IsAntichain r s ↔
 s.Subsingleton
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `subsingleton_of_isChain_of_isAntichain`：subsingleton_of_isChain_of_isAnt
ichain (hs : IsChain r s) (ht : IsAntichain r s) : s.Subsingleton
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.Subsingleton.isChain`：Set.Subsingleton.isChain (hs : s.Subsingleton)
 : IsChain r s
· 使用定理 `Set.Subsingleton.isAntichain`：Set.Subsingleton.isAntichain (hs : s.Subsi
ngleton) (r : α -> α -> Prop) : IsAntichain r s
-/
lemma isChain_and_isAntichain_iff_subsingleton : IsChain r s ∧ IsAntichain r s ↔ s.Subsingleton :=
  ⟨fun h ↦ subsingleton_of_isChain_of_isAntichain h.1 h.2, fun h ↦ ⟨h.isChain, h.isAntichain _⟩⟩

/-- The intersection of a chain and an antichain is subsingleton. -/
/-
**inter_subsingleton_of_isChain_of_isAntichain** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：inter_subsingleton_of_isChain_of_isAntichain (hs : IsChain r s) (ht : IsAn
tichain r t) : (s inter t).Subsingleton
参数：hs : IsChain r s；ht : IsAntichain r t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `subsingleton_of_isChain_of_isAntichain`：subsingleton_of_isChain_of_isAnt
ichain (hs : IsChain r s) (ht : IsAntichain r s) : s.Subsingleton
· 使用定理 `IsChain.mono`：IsChain.mono : s subseteq t -> IsChain r t -> IsChain r s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsAntichain.subset`：∀ {α : Type u_1} {r : α → α → Prop} {s t : Set α}, I
sAntichain r s → t ⊆ s → IsAntichain r t

--- 原说明 ---
The intersection of a chain and an antichain is subsingleton.
-/
lemma inter_subsingleton_of_isChain_of_isAntichain (hs : IsChain r s) (ht : IsAntichain r t) :
    (s ∩ t).Subsingleton :=
  subsingleton_of_isChain_of_isAntichain (hs.mono (by simp)) (ht.subset (by simp))

/-- The intersection of an antichain and a chain is subsingleton. -/
/-
**inter_subsingleton_of_isAntichain_of_isChain** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：inter_subsingleton_of_isAntichain_of_isChain (hs : IsAntichain r s) (ht : 
IsChain r t) : (s inter t).Subsingleton
参数：hs : IsAntichain r s；ht : IsChain r t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `inter_subsingleton_of_isChain_of_isAntichain`：inter_subsingleton_of_isCh
ain_of_isAntichain (hs : IsChain r s) (ht : IsAntichain r t) : (s inter t).Subsi
ngleton
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a

--- 原说明 ---
The intersection of an antichain and a chain is subsingleton.
-/
lemma inter_subsingleton_of_isAntichain_of_isChain (hs : IsAntichain r s) (ht : IsChain r t) :
    (s ∩ t).Subsingleton :=
  inter_comm _ _ ▸ inter_subsingleton_of_isChain_of_isAntichain ht hs

section Preorder

variable [Preorder α]

/-
**IsAntichain.not_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsAntichain.not_lt (hs : IsAntichain (· <= ·) s) (ha : a in s) (hb : b in 
s) : ¬a < b
参数：hs : IsAntichain (· <= ·) s；ha : a in s；hb : b in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem IsAntichain.not_lt (hs : IsAntichain (· ≤ ·) s) (ha : a ∈ s) (hb : b ∈ s) : ¬a < b :=
  fun h => hs ha hb h.ne h.le
/-
**isAntichain_and_least_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isAntichain_and_least_iff : IsAntichain (· <= ·) s ∧ IsLeast s a ↔ s = {a}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.eq_singleton_iff_unique_mem`：eq_singleton_iff_unique_mem : s = {a} ↔
 a in s ∧ forall x in s, x = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `IsAntichain.eq'`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α}, IsAnti
chain r s → ∀ {a b : α}, a ∈ s → b ∈ s → r b a → a = b
· 使用定理 `IsAntichain.singleton`：∀ {α : Type u_1} {r : α → α → Prop} {a : α}, IsAn
tichain r {a}
· 使用定理 `isLeast_singleton`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, IsLeast
 {a} a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isAntichain_and_least_iff : IsAntichain (· ≤ ·) s ∧ IsLeast s a ↔ s = {a} :=
  ⟨fun h => eq_singleton_iff_unique_mem.2 ⟨h.2.1, fun _ hb => h.1.eq' hb h.2.1 (h.2.2 hb)⟩, by
    rintro rfl
    exact ⟨IsAntichain.singleton, isLeast_singleton⟩⟩
/-
**isAntichain_and_greatest_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isAntichain_and_greatest_iff : IsAntichain (· <= ·) s ∧ IsGreatest s a ↔ s
 = {a}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.eq_singleton_iff_unique_mem`：eq_singleton_iff_unique_mem : s = {a} ↔
 a in s ∧ forall x in s, x = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `IsAntichain.eq`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α}, IsAntic
hain r s → ∀ {a b : α}, a ∈ s → b ∈ s → r a b → a = b
· 使用定理 `IsAntichain.singleton`：∀ {α : Type u_1} {r : α → α → Prop} {a : α}, IsAn
tichain r {a}
· 使用定理 `isGreatest_singleton`：isGreatest_singleton : IsGreatest {a} a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isAntichain_and_greatest_iff : IsAntichain (· ≤ ·) s ∧ IsGreatest s a ↔ s = {a} :=
  ⟨fun h => eq_singleton_iff_unique_mem.2 ⟨h.2.1, fun _ hb => h.1.eq hb h.2.1 (h.2.2 hb)⟩, by
    rintro rfl
    exact ⟨IsAntichain.singleton, isGreatest_singleton⟩⟩
/-
**IsAntichain.least_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsAntichain.least_iff (hs : IsAntichain (· <= ·) s) : IsLeast s a ↔ s = {a
}
参数：hs : IsAntichain (· <= ·) s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `isAntichain_and_least_iff`：isAntichain_and_least_iff : IsAntichain (· <=
 ·) s ∧ IsLeast s a ↔ s = {a}
-/
theorem IsAntichain.least_iff (hs : IsAntichain (· ≤ ·) s) : IsLeast s a ↔ s = {a} :=
  (and_iff_right hs).symm.trans isAntichain_and_least_iff
/-
**IsAntichain.greatest_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsAntichain.greatest_iff (hs : IsAntichain (· <= ·) s) : IsGreatest s a ↔ 
s = {a}
参数：hs : IsAntichain (· <= ·) s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `isAntichain_and_greatest_iff`：isAntichain_and_greatest_iff : IsAntichain
 (· <= ·) s ∧ IsGreatest s a ↔ s = {a}
-/
theorem IsAntichain.greatest_iff (hs : IsAntichain (· ≤ ·) s) : IsGreatest s a ↔ s = {a} :=
  (and_iff_right hs).symm.trans isAntichain_and_greatest_iff
/-
**IsLeast.antichain_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLeast.antichain_iff (hs : IsLeast s a) : IsAntichain (· <= ·) s ↔ s = {a
}
参数：hs : IsLeast s a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `isAntichain_and_least_iff`：isAntichain_and_least_iff : IsAntichain (· <=
 ·) s ∧ IsLeast s a ↔ s = {a}
-/
theorem IsLeast.antichain_iff (hs : IsLeast s a) : IsAntichain (· ≤ ·) s ↔ s = {a} :=
  (and_iff_left hs).symm.trans isAntichain_and_least_iff
/-
**IsGreatest.antichain_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsGreatest.antichain_iff (hs : IsGreatest s a) : IsAntichain (· <= ·) s ↔ 
s = {a}
参数：hs : IsGreatest s a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `isAntichain_and_greatest_iff`：isAntichain_and_greatest_iff : IsAntichain
 (· <= ·) s ∧ IsGreatest s a ↔ s = {a}
-/
theorem IsGreatest.antichain_iff (hs : IsGreatest s a) : IsAntichain (· ≤ ·) s ↔ s = {a} :=
  (and_iff_left hs).symm.trans isAntichain_and_greatest_iff
/-
**IsAntichain.bot_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsAntichain.bot_mem_iff [OrderBot α] (hs : IsAntichain (· <= ·) s) : ⊥ in 
s ↔ s = {⊥}
参数：hs : IsAntichain (· <= ·) s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `isLeast_bot_iff`：isLeast_bot_iff [OrderBot α] : IsLeast s ⊥ ↔ ⊥ in s
· 使用定理 `IsAntichain.least_iff`：IsAntichain.least_iff (hs : IsAntichain (· <= ·) 
s) : IsLeast s a ↔ s = {a}
-/
theorem IsAntichain.bot_mem_iff [OrderBot α] (hs : IsAntichain (· ≤ ·) s) : ⊥ ∈ s ↔ s = {⊥} :=
  isLeast_bot_iff.symm.trans hs.least_iff
/-
**IsAntichain.top_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsAntichain.top_mem_iff [OrderTop α] (hs : IsAntichain (· <= ·) s) : ⊤ in 
s ↔ s = {⊤}
参数：hs : IsAntichain (· <= ·) s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `isGreatest_top_iff`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α} [in
st_1 : OrderTop α], IsGreatest s ⊤ ↔ ⊤ ∈ s
· 使用定理 `IsAntichain.greatest_iff`：IsAntichain.greatest_iff (hs : IsAntichain (· 
<= ·) s) : IsGreatest s a ↔ s = {a}
-/
theorem IsAntichain.top_mem_iff [OrderTop α] (hs : IsAntichain (· ≤ ·) s) : ⊤ ∈ s ↔ s = {⊤} :=
  isGreatest_top_iff.symm.trans hs.greatest_iff
/-
**IsAntichain.minimal_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsAntichain.minimal_mem_iff (hs : IsAntichain (· <= ·) s) : Minimal (· in 
s) a ↔ a in s
参数：hs : IsAntichain (· <= ·) s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Minimal.prop`：Minimal.prop (h : Minimal P x) : P x
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsAntichain.eq`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α}, IsAntic
hain r s → ∀ {a b : α}, a ∈ s → b ∈ s → r a b → a = b
-/
theorem IsAntichain.minimal_mem_iff (hs : IsAntichain (· ≤ ·) s) : Minimal (· ∈ s) a ↔ a ∈ s :=
  ⟨fun h ↦ h.prop, fun h ↦ ⟨h, fun _ hys hyx ↦ (hs.eq hys h hyx).symm.le⟩⟩
/-
**IsAntichain.maximal_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsAntichain.maximal_mem_iff (hs : IsAntichain (· <= ·) s) : Maximal (· in 
s) a ↔ a in s
参数：hs : IsAntichain (· <= ·) s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAntichain.minimal_mem_iff`：IsAntichain.minimal_mem_iff (hs : IsAnticha
in (· <= ·) s) : Minimal (· in s) a ↔ a in s
· 使用定理 `IsAntichain.to_dual`：to_dual [LE α] (hs : IsAntichain (· <= ·) s) : @IsA
ntichain αᵒᵈ (· <= ·) s
-/
theorem IsAntichain.maximal_mem_iff (hs : IsAntichain (· ≤ ·) s) : Maximal (· ∈ s) a ↔ a ∈ s :=
  hs.to_dual.minimal_mem_iff

/-- If `t` is an antichain shadowing and including the set of maximal elements of `s`,
then `t` *is* the set of maximal elements of `s`. -/
/-
**IsAntichain.eq_setOfPred_maximal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsAntichain.eq_setOfPred_maximal (ht : IsAntichain (· <= ·) t) (h : forall
 x, Maximal (· in s) x -> x in t) (hs : forall a in t, exists b, b <= a ∧ Maxima
l (· in s) b) : {x | Maximal (· in s) x} = t
参数：ht : IsAntichain (· <= ·) t；h : forall x, Maximal (· in s) x -> x in t；hs : f
orall a in t, exists b, b <= a ∧ Maximal (· in s) b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsAntichain.eq`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α}, IsAntic
hain r s → ∀ {a b : α}, a ∈ s → b ∈ s → r a b → a = b

--- 原说明 ---
If `t` is an antichain shadowing and including the set of maximal elements of `s
`,
then `t` *is* the set of maximal elements of `s`.
-/
theorem IsAntichain.eq_setOfPred_maximal (ht : IsAntichain (· ≤ ·) t)
    (h : ∀ x, Maximal (· ∈ s) x → x ∈ t) (hs : ∀ a ∈ t, ∃ b, b ≤ a ∧ Maximal (· ∈ s) b) :
    {x | Maximal (· ∈ s) x} = t := by
  refine Set.ext fun x ↦ ⟨h _, fun hx ↦ ?_⟩
  obtain ⟨y, hyx, hy⟩ := hs x hx
  rwa [← ht.eq (h y hy) hx hyx]

@[deprecated (since := "2026-07-09")]
alias IsAntichain.eq_setOf_maximal := IsAntichain.eq_setOfPred_maximal

/-- If `t` is an antichain shadowed by and including the set of minimal elements of `s`,
then `t` *is* the set of minimal elements of `s`. -/
/-
**IsAntichain.eq_setOfPred_minimal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsAntichain.eq_setOfPred_minimal (ht : IsAntichain (· <= ·) t) (h : forall
 x, Minimal (· in s) x -> x in t) (hs : forall a in t, exists b, a <= b ∧ Minima
l (· in s) b) : {x | Minimal (· in s) x} = t
参数：ht : IsAntichain (· <= ·) t；h : forall x, Minimal (· in s) x -> x in t；hs : f
orall a in t, exists b, a <= b ∧ Minimal (· in s) b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAntichain.eq_setOfPred_maximal`：IsAntichain.eq_setOfPred_maximal (ht :
 IsAntichain (· <= ·) t) (h : forall x, Maximal (· in s) x -> x in t) (hs : fora
ll a in t, exists b, b…
· 使用定理 `IsAntichain.to_dual`：to_dual [LE α] (hs : IsAntichain (· <= ·) s) : @IsA
ntichain αᵒᵈ (· <= ·) s

--- 原说明 ---
If `t` is an antichain shadowed by and including the set of minimal elements of 
`s`,
then `t` *is* the set of minimal elements of `s`.
-/
theorem IsAntichain.eq_setOfPred_minimal (ht : IsAntichain (· ≤ ·) t)
    (h : ∀ x, Minimal (· ∈ s) x → x ∈ t) (hs : ∀ a ∈ t, ∃ b, a ≤ b ∧ Minimal (· ∈ s) b) :
    {x | Minimal (· ∈ s) x} = t :=
  ht.to_dual.eq_setOfPred_maximal h hs

@[deprecated (since := "2026-07-09")]
alias IsAntichain.eq_setOf_minimal := IsAntichain.eq_setOfPred_minimal

end Preorder

section PartialOrder

variable [PartialOrder α] [PartialOrder β] {f : α → β} {s : Set α}

/-
**IsAntichain.of_strictMonoOn_antitoneOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsAntichain.of_strictMonoOn_antitoneOn (hf : StrictMonoOn f s) (hf' : Anti
toneOn f s) : IsAntichain (· <= ·) s
参数：hf : StrictMonoOn f s；hf' : AntitoneOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
-/
lemma IsAntichain.of_strictMonoOn_antitoneOn (hf : StrictMonoOn f s) (hf' : AntitoneOn f s) :
    IsAntichain (· ≤ ·) s :=
  fun _a ha _b hb hab' hab ↦ (hf ha hb <| hab.lt_of_ne hab').not_ge (hf' ha hb hab)
/-
**IsAntichain.of_monotoneOn_strictAntiOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsAntichain.of_monotoneOn_strictAntiOn (hf : MonotoneOn f s) (hf' : Strict
AntiOn f s) : IsAntichain (· <= ·) s
参数：hf : MonotoneOn f s；hf' : StrictAntiOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
-/
lemma IsAntichain.of_monotoneOn_strictAntiOn (hf : MonotoneOn f s) (hf' : StrictAntiOn f s) :
    IsAntichain (· ≤ ·) s :=
  fun _a ha _b hb hab' hab ↦ (hf ha hb hab).not_gt (hf' ha hb <| hab.lt_of_ne hab')
/-
**isAntichain_iff_forall_not_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isAntichain_iff_forall_not_lt : IsAntichain (· <= ·) s ↔ forall ⦃a⦄, a in 
s -> forall ⦃b⦄, b in s -> ¬a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAntichain.not_lt`：IsAntichain.not_lt (hs : IsAntichain (· <= ·) s) (ha
 : a in s) (hb : b in s) : ¬a < b
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
-/
theorem isAntichain_iff_forall_not_lt :
    IsAntichain (· ≤ ·) s ↔ ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → ¬a < b :=
  ⟨fun hs _ ha _ => hs.not_lt ha, fun hs _ ha _ hb h h' => hs ha hb <| h'.lt_of_ne h⟩
/-
**setOfPred_maximal_antichain** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：setOfPred_maximal_antichain (P : α -> Prop) : IsAntichain (· <= ·) {x | Ma
ximal P x}
参数：P : α -> Prop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem setOfPred_maximal_antichain (P : α → Prop) : IsAntichain (· ≤ ·) {x | Maximal P x} :=
  fun _ hx _ ⟨hy, _⟩ hne hle ↦ hne (hle.antisymm <| hx.2 hy hle)

@[deprecated (since := "2026-07-09")]
alias setOf_maximal_antichain := setOfPred_maximal_antichain
/-
**setOfPred_minimal_antichain** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：setOfPred_minimal_antichain (P : α -> Prop) : IsAntichain (· <= ·) {x | Mi
nimal P x}
参数：P : α -> Prop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAntichain.swap`：swap (hs : IsAntichain r s) : IsAntichain (swap r) s
· 使用定理 `setOfPred_maximal_antichain`：setOfPred_maximal_antichain (P : α -> Prop)
 : IsAntichain (· <= ·) {x | Maximal P x}
-/
theorem setOfPred_minimal_antichain (P : α → Prop) : IsAntichain (· ≤ ·) {x | Minimal P x} :=
  (setOfPred_maximal_antichain (α := αᵒᵈ) P).swap

@[deprecated (since := "2026-07-09")] alias setOf_minimal_antichain := setOfPred_minimal_antichain

end PartialOrder

/-! ### Strong antichains -/


/-- A strong (upward) antichain is a set such that no two distinct elements are related to a common
element. -/
/-
**IsStrongAntichain** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsStrongAntichain (r : α -> α -> Prop) (s : Set α) : Prop
参数：r : α -> α -> Prop；s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A strong (upward) antichain is a set such that no two distinct elements are rela
ted to a common
element.
-/
def IsStrongAntichain (r : α → α → Prop) (s : Set α) : Prop :=
  s.Pairwise fun a b => ∀ c, ¬r a c ∨ ¬r b c

namespace IsStrongAntichain

/-
**IsStrongAntichain.subset** 是 Mathlib 中的一个定理，位于命名空间 `IsStrongAntichain`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} {s t : Set α}, IsStrongAntichain r s →
 t ⊆ s → IsStrongAntichain r t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Pairwise.mono`：∀ {α : Type u_1} {r : α → α → Prop} {s t : Set α}, t 
⊆ s → s.Pairwise r → t.Pairwise r
-/
protected theorem subset (hs : IsStrongAntichain r s) (h : t ⊆ s) : IsStrongAntichain r t :=
  hs.mono h
/-
**IsStrongAntichain.mono** 是 Mathlib 中的一个定理，位于命名空间 `IsStrongAntichain`。
形式化陈述：mono (hs : IsStrongAntichain r₁ s) (h : r₂ <= r₁) : IsStrongAntichain r₂ s
参数：hs : IsStrongAntichain r₁ s；h : r₂ <= r₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Pairwise.mono'`：∀ {α : Type u_1} {r p : α → α → Prop} {s : Set α}, r
 ≤ p → s.Pairwise r → s.Pairwise p
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `compl_le_compl`：compl_le_compl (h : a <= b) : bᶜ <= aᶜ
-/
theorem mono (hs : IsStrongAntichain r₁ s) (h : r₂ ≤ r₁) : IsStrongAntichain r₂ s :=
  hs.mono' fun _ _ hab c => (hab c).imp (compl_le_compl h _ _) (compl_le_compl h _ _)
/-
**IsStrongAntichain.eq** 是 Mathlib 中的一个定理，位于命名空间 `IsStrongAntichain`。
形式化陈述：eq (hs : IsStrongAntichain r s) {a b c : α} (ha : a in s) (hb : b in s) (h
ac : r a c) (hbc : r b c) : a = b
参数：hs : IsStrongAntichain r s；ha : a in s；hb : b in s；hac : r a c；hbc : r b c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Pairwise.eq`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α} {a b : 
α}, s.Pairwise r → a ∈ s → b ∈ s → ¬r a b → a = b
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `not_not_intro`：∀ {p : Prop}, p → ¬¬p
-/
theorem eq (hs : IsStrongAntichain r s) {a b c : α} (ha : a ∈ s) (hb : b ∈ s) (hac : r a c)
    (hbc : r b c) : a = b :=
  (Set.Pairwise.eq hs ha hb) fun h =>
    False.elim <| (h c).elim (not_not_intro hac) (not_not_intro hbc)
/-
**IsStrongAntichain.isAntichain** 是 Mathlib 中的一个定理，位于命名空间 `IsStrongAntichain`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α} [Std.Refl r], IsStrongAnti
chain r s → IsAntichain r s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Pairwise.imp`：∀ {α : Type u_1} {r p : α → α → Prop} {s : Set α}, s.P
airwise r → (∀ ⦃a b : α⦄, r a b → p a b) → s.Pairwise p
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `not_not_intro`：∀ {p : Prop}, p → ¬¬p
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
-/
protected theorem isAntichain [Std.Refl r] (h : IsStrongAntichain r s) : IsAntichain r s :=
  h.imp fun _ b hab => (hab b).resolve_right (not_not_intro <| refl _)
/-
**IsStrongAntichain.subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `IsStrongAntichain`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α} [IsDirected α r], IsStrong
Antichain r s → s.Subsingleton
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `directed_of`：directed_of (r : α -> α -> Prop) [IsDirected α r] (a b : α)
 : exists c, r a c ∧ r b c
· 使用定理 `IsStrongAntichain.eq`：eq (hs : IsStrongAntichain r s) {a b c : α} (ha : 
a in s) (hb : b in s) (hac : r a c) (hbc : r b c) : a = b
-/
protected theorem subsingleton [IsDirected α r] (h : IsStrongAntichain r s) : s.Subsingleton :=
  fun a ha b hb =>
  let ⟨_, hac, hbc⟩ := directed_of r a b
  h.eq ha hb hac hbc
/-
**IsStrongAntichain.flip** 是 Mathlib 中的一个定理，位于命名空间 `IsStrongAntichain`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α} [Std.Symm r], IsStrongAnti
chain r s → IsStrongAntichain (flip r) s
参数：flip r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `symm_of`：∀ {α : Sort u_1} (r : α → α → Prop) {a b : α} [Std.Symm r], r a
 b → r b a
-/
protected theorem flip [Std.Symm r] (hs : IsStrongAntichain r s) : IsStrongAntichain (flip r) s :=
  fun _ ha _ hb h c => (hs ha hb h c).imp (mt <| symm_of r) (mt <| symm_of r)
/-
**IsStrongAntichain.swap** 是 Mathlib 中的一个定理，位于命名空间 `IsStrongAntichain`。
形式化陈述：swap [Std.Symm r] (hs : IsStrongAntichain r s) : IsStrongAntichain (swap r
) s
参数：hs : IsStrongAntichain r s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrongAntichain.flip`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α} 
[Std.Symm r], IsStrongAntichain r s → IsStrongAntichain (flip r) s
-/
theorem swap [Std.Symm r] (hs : IsStrongAntichain r s) : IsStrongAntichain (swap r) s :=
  hs.flip
/-
**IsStrongAntichain.image** 是 Mathlib 中的一个定理，位于命名空间 `IsStrongAntichain`。
形式化陈述：image (hs : IsStrongAntichain r s) {f : α -> β} (hf : Surjective f) (h : f
orall a b, r' (f a) (f b) -> r a b) : IsStrongAntichain r' (f '' s)
参数：hs : IsStrongAntichain r s；hf : Surjective f；h : forall a b, r' (f a) (f b) -
> r a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
-/
theorem image (hs : IsStrongAntichain r s) {f : α → β} (hf : Surjective f)
    (h : ∀ a b, r' (f a) (f b) → r a b) : IsStrongAntichain r' (f '' s) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab c
  obtain ⟨c, rfl⟩ := hf c
  exact (hs ha hb (ne_of_apply_ne _ hab) _).imp (mt <| h _ _) (mt <| h _ _)
/-
**IsStrongAntichain.preimage** 是 Mathlib 中的一个定理，位于命名空间 `IsStrongAntichain`。
形式化陈述：preimage (hs : IsStrongAntichain r s) {f : β -> α} (hf : Injective f) (h :
 forall a b, r' a b -> r (f a) (f b)) : IsStrongAntichain r' (f ⁻¹' s)
参数：hs : IsStrongAntichain r s；hf : Injective f；h : forall a b, r' a b -> r (f a)
 (f b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
-/
theorem preimage (hs : IsStrongAntichain r s) {f : β → α} (hf : Injective f)
    (h : ∀ a b, r' a b → r (f a) (f b)) : IsStrongAntichain r' (f ⁻¹' s) := fun _ ha _ hb hab _ =>
  (hs ha hb (hf.ne hab) _).imp (mt <| h _ _) (mt <| h _ _)
/-
**IsStrongAntichain._root_.isStrongAntichain_insert** 是 Mathlib 中的一个定理，位于命名空间 `I
sStrongAntichain`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.isStrongAntichain_insert :
    IsStrongAntichain r (insert a s) ↔
      IsStrongAntichain r s ∧ ∀ ⦃b⦄, b ∈ s → a ≠ b → ∀ c, ¬r a c ∨ ¬r b c :=
  have : Std.Symm fun a b ↦ ∀ c, ¬r a c ∨ ¬r b c := { symm _ _ h c := h c |>.symm }
  Set.pairwise_insert_of_symm
/-
**IsStrongAntichain.insert** 是 Mathlib 中的一个定理，位于命名空间 `IsStrongAntichain`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α} {a : α},   IsStrongAnticha
in r s → (∀ ⦃b : α⦄, b ∈ s → a ≠ b → ∀ (c : α), ¬r a c ∨ ¬r b c) → IsStrongAntic
hain r (insert a s)
参数：∀ ⦃b : α⦄, b ∈ s → a ≠ b → ∀ (c : α), ¬r a c ∨ ¬r b c；insert a s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isStrongAntichain_insert`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α
} {a : α},   IsStrongAntichain r (insert a s) ↔ IsStrongAntichain r s ∧ ∀ ⦃b : α
⦄, b ∈ s → a ≠…
-/
protected theorem insert (hs : IsStrongAntichain r s)
    (h : ∀ ⦃b⦄, b ∈ s → a ≠ b → ∀ c, ¬r a c ∨ ¬r b c) : IsStrongAntichain r (insert a s) :=
  isStrongAntichain_insert.2 ⟨hs, h⟩

end IsStrongAntichain

/-
**Set.Subsingleton.isStrongAntichain** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Subsingleton.isStrongAntichain (hs : s.Subsingleton) (r : α -> α -> Pr
op) : IsStrongAntichain r s
参数：hs : s.Subsingleton；r : α -> α -> Prop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.pairwise`：∀ {α : Type u_1} {s : Set α}, s.Subsingleton 
→ ∀ (r : α → α → Prop), s.Pairwise r
-/
theorem Set.Subsingleton.isStrongAntichain (hs : s.Subsingleton) (r : α → α → Prop) :
    IsStrongAntichain r s :=
  hs.pairwise _

/-! ### Maximal antichains -/

/-- An antichain `s` is a maximal antichain if there does not exists an antichain strictly including
`s`. -/
/-
**IsMaxAntichain** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsMaxAntichain (r : α -> α -> Prop) (s : Set α) : Prop
参数：r : α -> α -> Prop；s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An antichain `s` is a maximal antichain if there does not exists an antichain st
rictly including
`s`.
-/
def IsMaxAntichain (r : α → α → Prop) (s : Set α) : Prop :=
  IsAntichain r s ∧ ∀ ⦃t⦄, IsAntichain r t → s ⊆ t → s = t

namespace IsMaxAntichain

/-
**IsMaxAntichain.isAntichain** 是 Mathlib 中的一个定理，位于命名空间 `IsMaxAntichain`。
形式化陈述：isAntichain (h : IsMaxAntichain r s) : IsAntichain r s
参数：h : IsMaxAntichain r s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem isAntichain (h : IsMaxAntichain r s) : IsAntichain r s :=
  h.1
/-
**IsMaxAntichain.image** 是 Mathlib 中的一个定理，位于命名空间 `IsMaxAntichain`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (e :
 r ≃r s) {c : Set α},   IsMaxAntichain r c → IsMaxAntichain s (⇑e '' c)
参数：e : r ≃r s；⇑e '' c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAntichain.image`：image (hs : IsAntichain r s) (f : α -> β) (h : forall
 ⦃a b⦄, r' (f a) (f b) -> r a b) : IsAntichain r' (f '' s)
· 使用定理 `IsMaxAntichain.isAntichain`：isAntichain (h : IsMaxAntichain r s) : IsAnt
ichain r s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `RelIso.map_rel_iff'`：∀ {α : Type u_5} {β : Type u_6} {r : α → α → Prop} 
{s : β → β → Prop} (self : r ≃r s) {a b : α},   s (self.toEquiv a) (self.toEquiv
 b) ↔ r a…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RelIso.coe_fn_toEquiv`：coe_fn_toEquiv (f : r ≃r s) : (f.toEquiv : α -> β
) = f
· 使用定理 `Equiv.eq_preimage_iff_image_eq`：eq_preimage_iff_image_eq {α β} (e : α ≃ 
β) (s t) : s = e ⁻¹' t ↔ e '' s = t
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `Equiv.image_symm_eq_preimage`：image_symm_eq_preimage (e : α ≃ β) (s : Se
t β) : e.symm '' s = e ⁻¹' s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `RelIso.map_rel_iff`：map_rel_iff (f : r ≃r s) {a b} : s (f a) (f b) ↔ r a
 b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.subset_symm_image`：∀ {α : Type u_3} {β : Type u_4} (e : α ≃ β) (s 
: Set α) (t : Set β), s ⊆ ⇑e.symm '' t ↔ ⇑e '' s ⊆ t
-/
protected theorem image {s : β → β → Prop} (e : r ≃r s) {c : Set α} (hc : IsMaxAntichain r c) :
    IsMaxAntichain s (e '' c) where
  left := hc.isAntichain.image _ fun _ _ ↦ e.map_rel_iff'.mp
  right t ht hf := by
    rw [← e.coe_fn_toEquiv, ← e.toEquiv.eq_preimage_iff_image_eq, ← Equiv.image_symm_eq_preimage]
    exact hc.2 (ht.image _ fun _ _ ↦ e.symm.map_rel_iff.mp)
      ((e.toEquiv.subset_symm_image _ _).2 hf)
/-
**IsMaxAntichain.isEmpty_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsMaxAntichain`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α}, IsMaxAntichain r s → (IsE
mpty α ↔ s = ∅)
参数：IsEmpty α ↔ s = ∅。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.eq_empty_of_isEmpty`：eq_empty_of_isEmpty (s : Set α) [IsEmpty s] : s
 = ∅
· 使用定理 `instIsEmptySubtype`：∀ {α : Sort u} [IsEmpty α] (p : α → Prop), IsEmpty (
Subtype p)
· 使用定理 `Set.singleton_ne_empty`：singleton_ne_empty (a : α) : ({a} : Set α) != ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `IsAntichain.singleton`：∀ {α : Type u_1} {r : α → α → Prop} {a : α}, IsAn
tichain r {a}
-/
protected theorem isEmpty_iff (h : IsMaxAntichain r s) : IsEmpty α ↔ s = ∅ := by
  refine ⟨fun _ ↦ s.eq_empty_of_isEmpty, fun h' ↦ ?_⟩
  constructor
  intro x
  simp only [IsMaxAntichain, h', IsAntichain.empty, empty_subset, forall_const, true_and] at h
  exact singleton_ne_empty x (h IsAntichain.singleton).symm
/-
**IsMaxAntichain.nonempty_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsMaxAntichain`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α}, IsMaxAntichain r s → (Non
empty α ↔ s.Nonempty)
参数：Nonempty α ↔ s.Nonempty。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsMaxAntichain.isEmpty_iff`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set
 α}, IsMaxAntichain r s → (IsEmpty α ↔ s = ∅)
-/
protected theorem nonempty_iff (h : IsMaxAntichain r s) : Nonempty α ↔ s.Nonempty :=
  not_iff_not.mp <| by simpa [Set.not_nonempty_iff_eq_empty] using h.isEmpty_iff
/-
**IsMaxAntichain.symm** 是 Mathlib 中的一个定理，位于命名空间 `IsMaxAntichain`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α}, IsMaxAntichain r s → IsMa
xAntichain (flip r) s
参数：flip r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAntichain.flip`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α}, IsAnt
ichain r s → IsAntichain (flip r) s
· 使用定理 `IsMaxAntichain.isAntichain`：isAntichain (h : IsMaxAntichain r s) : IsAnt
ichain r s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
protected theorem symm (h : IsMaxAntichain r s) : IsMaxAntichain (flip r) s :=
  ⟨h.isAntichain.flip, fun _ ht₁ ht₂ ↦ h.2 ht₁.flip ht₂⟩

end IsMaxAntichain

end General

/-! ### Weak antichains -/


section Pi

variable {ι : Type*} {α : ι → Type*} [∀ i, Preorder (α i)] {s t : Set (∀ i, α i)}
  {a b : ∀ i, α i}


@[inherit_doc]
local infixl:50 " ≺ " => StrongLT

/-- A weak antichain in `Π i, α i` is a set such that no two distinct elements are strongly less
than each other. -/
/-
**IsWeakAntichain** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsWeakAntichain (s : Set (forall i, α i)) : Prop
参数：s : Set (forall i, α i)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A weak antichain in `Π i, α i` is a set such that no two distinct elements are s
trongly less
than each other.
-/
def IsWeakAntichain (s : Set (∀ i, α i)) : Prop :=
  IsAntichain (· ≺ ·) s

namespace IsWeakAntichain

/-
**IsWeakAntichain.subset** 是 Mathlib 中的一个定理，位于命名空间 `IsWeakAntichain`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : (i : ι) → Preorder (α i)] {s t
 : Set ((i : ι) → α i)},   IsWeakAntichain s → t ⊆ s → IsWeakAntichain t
参数：i : ι；α i；(i : ι) → α i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAntichain.subset`：∀ {α : Type u_1} {r : α → α → Prop} {s t : Set α}, I
sAntichain r s → t ⊆ s → IsAntichain r t
-/
protected theorem subset (hs : IsWeakAntichain s) : t ⊆ s → IsWeakAntichain t :=
  IsAntichain.subset hs
/-
**IsWeakAntichain.eq** 是 Mathlib 中的一个定理，位于命名空间 `IsWeakAntichain`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : (i : ι) → Preorder (α i)] {s :
 Set ((i : ι) → α i)} {a b : (i : ι) → α i},   IsWeakAntichain s → a ∈ s → b ∈ s
 → StrongLT a b → a = b
参数：i : ι；α i；(i : ι) → α i；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAntichain.eq`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α}, IsAntic
hain r s → ∀ {a b : α}, a ∈ s → b ∈ s → r a b → a = b
-/
protected theorem eq (hs : IsWeakAntichain s) : a ∈ s → b ∈ s → a ≺ b → a = b :=
  IsAntichain.eq hs
/-
**IsWeakAntichain.insert** 是 Mathlib 中的一个定理，位于命名空间 `IsWeakAntichain`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : (i : ι) → Preorder (α i)] {s :
 Set ((i : ι) → α i)} {a : (i : ι) → α i},   IsWeakAntichain s →     (∀ ⦃b : (i 
: ι) → α i⦄, b ∈ s → a ≠ b → ¬StrongLT b a) →       (∀ ⦃b : (i : ι) → α i⦄, b ∈ 
s → a ≠ b → ¬StrongLT a b) → IsWeakAntichain (insert a s)
参数：i : ι；α i；(i : ι) → α i；i : ι；∀ ⦃b : (i : ι) → α i⦄, b ∈ s → a ≠ b → ¬StrongL
T b a；∀ ⦃b : (i : ι) → α i⦄, b ∈ s → a ≠ b → ¬StrongLT a b；insert a s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAntichain.insert`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α} {a :
 α},   IsAntichain r s →     (∀ ⦃b : α⦄, b ∈ s → a ≠ b → ¬r b a) → (∀ ⦃b : α⦄, b
 ∈ s → a…
-/
protected theorem insert (hs : IsWeakAntichain s) :
    (∀ ⦃b⦄, b ∈ s → a ≠ b → ¬b ≺ a) →
      (∀ ⦃b⦄, b ∈ s → a ≠ b → ¬a ≺ b) → IsWeakAntichain (insert a s) :=
  IsAntichain.insert hs

end IsWeakAntichain

/-
**_root_.isWeakAntichain_insert** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：_root_.isWeakAntichain_insert : IsWeakAntichain (insert a s) ↔ IsWeakAntic
hain s ∧ forall ⦃b⦄, b in s -> a != b -> ¬a ≺ b ∧ ¬b ≺ a
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.isWeakAntichain_insert :
    IsWeakAntichain (insert a s) ↔ IsWeakAntichain s ∧ ∀ ⦃b⦄, b ∈ s → a ≠ b → ¬a ≺ b ∧ ¬b ≺ a :=
  isAntichain_insert
/-
**IsAntichain.isWeakAntichain** 是 Mathlib 中的一个定理，位于命名空间 `IsAntichain`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : (i : ι) → Preorder (α i)] {s :
 Set ((i : ι) → α i)},   IsAntichain (fun x1 x2 => x1 ≤ x2) s → IsWeakAntichain 
s
参数：i : ι；α i；(i : ι) → α i；fun x1 x2 => x1 ≤ x2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAntichain.mono`：mono (hs : IsAntichain r₁ s) (h : r₂ <= r₁) : IsAntich
ain r₂ s
· 使用定理 `le_of_strongLT`：le_of_strongLT (h : a ≺ b) : a <= b
-/
protected theorem IsAntichain.isWeakAntichain (hs : IsAntichain (· ≤ ·) s) : IsWeakAntichain s :=
  hs.mono fun _ _ => le_of_strongLT
/-
**Set.Subsingleton.isWeakAntichain** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Subsingleton.isWeakAntichain (hs : s.Subsingleton) : IsWeakAntichain s
参数：hs : s.Subsingleton。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.isAntichain`：Set.Subsingleton.isAntichain (hs : s.Subsi
ngleton) (r : α -> α -> Prop) : IsAntichain r s
-/
theorem Set.Subsingleton.isWeakAntichain (hs : s.Subsingleton) : IsWeakAntichain s :=
  hs.isAntichain _

end Pi

