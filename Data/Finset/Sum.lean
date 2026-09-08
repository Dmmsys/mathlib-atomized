/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Fold
public import Mathlib.Data.Multiset.Sum

/-!
# Disjoint sum of finsets

This file defines the disjoint sum of two finsets as `Finset (α ⊕ β)`. Beware not to confuse with
the `Finset.sum` operation which computes the additive sum.

## Main declarations

* `Finset.disjSum`: `s.disjSum t` is the disjoint sum of `s` and `t`.
* `Finset.toLeft`: Given a finset of elements `α ⊕ β`, extracts all the elements of the form `α`.
* `Finset.toRight`: Given a finset of elements `α ⊕ β`, extracts all the elements of the form `β`.
-/

@[expose] public section

open Function Multiset Sum

namespace Finset

variable {α β γ : Type*} (s : Finset α) (t : Finset β)

/-- Disjoint sum of finsets. -/
/-
**Finset.disjSum** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：disjSum : Finset (α oplus β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Disjoint sum of finsets.
-/
def disjSum : Finset (α ⊕ β) :=
  ⟨s.1.disjSum t.1, s.2.disjSum t.2⟩

@[simp]
/-
**Finset.val_disjSum** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：val_disjSum : (s.disjSum t).1 = s.1.disjSum t.1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem val_disjSum : (s.disjSum t).1 = s.1.disjSum t.1 :=
  rfl

@[simp]
/-
**Finset.empty_disjSum** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：empty_disjSum : (∅ : Finset α).disjSum t = t.map Embedding.inr
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.val_inj`：val_inj {s t : Finset α} : s.1 = t.1 ↔ s = t
· 使用定理 `Multiset.zero_disjSum`：zero_disjSum : (0 : Multiset α).disjSum t = t.map
 inr
-/
theorem empty_disjSum : (∅ : Finset α).disjSum t = t.map Embedding.inr :=
  val_inj.1 <| Multiset.zero_disjSum _

@[simp]
/-
**Finset.disjSum_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：disjSum_empty : s.disjSum (∅ : Finset β) = s.map Embedding.inl
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.val_inj`：val_inj {s t : Finset α} : s.1 = t.1 ↔ s = t
· 使用定理 `Multiset.disjSum_zero`：disjSum_zero : s.disjSum (0 : Multiset β) = s.map
 inl
-/
theorem disjSum_empty : s.disjSum (∅ : Finset β) = s.map Embedding.inl :=
  val_inj.1 <| Multiset.disjSum_zero _

@[simp]
/-
**Finset.card_disjSum** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_disjSum : (s.disjSum t).card = s.card + t.card
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.card_disjSum`：card_disjSum : Multiset.card (s.disjSum t) = Mult
iset.card s + Multiset.card t
-/
theorem card_disjSum : (s.disjSum t).card = s.card + t.card :=
  Multiset.card_disjSum _ _
/-
**Finset.disjoint_map_inl_map_inr** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：disjoint_map_inl_map_inr : Disjoint (s.map Embedding.inl) (t.map Embedding
.inr)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem disjoint_map_inl_map_inr : Disjoint (s.map Embedding.inl) (t.map Embedding.inr) := by
  simp_rw [disjoint_left, mem_map]
  rintro x ⟨a, _, rfl⟩ ⟨b, _, ⟨⟩⟩

@[simp]
/-
**Finset.map_inl_disjUnion_map_inr** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：map_inl_disjUnion_map_inr : (s.map Embedding.inl).disjUnion (t.map Embeddi
ng.inr) (disjoint_map_inl_map_inr _ _) = s.disjSum t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.disjoint_map_inl_map_inr`：disjoint_map_inl_map_inr : Disjoint (s.
map Embedding.inl) (t.map Embedding.inr)
-/
theorem map_inl_disjUnion_map_inr :
    (s.map Embedding.inl).disjUnion (t.map Embedding.inr) (disjoint_map_inl_map_inr _ _) =
      s.disjSum t :=
  rfl

variable {s t} {s₁ s₂ : Finset α} {t₁ t₂ : Finset β} {a : α} {b : β} {x : α ⊕ β}
/-
**Finset.mem_disjSum** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_disjSum : x in s.disjSum t ↔ (exists a, a in s ∧ inl a = x) ∨ exists b
, b in t ∧ inr b = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.mem_disjSum`：mem_disjSum : x in s.disjSum t ↔ (exists a, a in s
 ∧ inl a = x) ∨ exists b, b in t ∧ inr b = x
-/
theorem mem_disjSum : x ∈ s.disjSum t ↔ (∃ a, a ∈ s ∧ inl a = x) ∨ ∃ b, b ∈ t ∧ inr b = x :=
  Multiset.mem_disjSum

@[simp]
/-
**Finset.inl_mem_disjSum** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inl_mem_disjSum : inl a in s.disjSum t ↔ a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.inl_mem_disjSum`：inl_mem_disjSum : inl a in s.disjSum t ↔ a in 
s
-/
theorem inl_mem_disjSum : inl a ∈ s.disjSum t ↔ a ∈ s :=
  Multiset.inl_mem_disjSum

@[simp]
/-
**Finset.inr_mem_disjSum** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inr_mem_disjSum : inr b in s.disjSum t ↔ b in t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.inr_mem_disjSum`：inr_mem_disjSum : inr b in s.disjSum t ↔ b in 
t
-/
theorem inr_mem_disjSum : inr b ∈ s.disjSum t ↔ b ∈ t :=
  Multiset.inr_mem_disjSum

@[simp]
/-
**Finset.disjSum_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：disjSum_eq_empty : s.disjSum t = ∅ ↔ s = ∅ ∧ t = ∅
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
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem disjSum_eq_empty : s.disjSum t = ∅ ↔ s = ∅ ∧ t = ∅ := by simp [Finset.ext_iff]
/-
**Finset.disjSum_mono** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：disjSum_mono (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂) : s₁.disjSum t₁ s
ubseteq s₂.disjSum t₂
参数：hs : s₁ subseteq s₂；ht : t₁ subseteq t₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.val_le_iff`：val_le_iff {s₁ s₂ : Finset α} : s₁.1 <= s₂.1 ↔ s₁ sub
seteq s₂
· 使用定理 `Multiset.disjSum_mono`：disjSum_mono (hs : s₁ <= s₂) (ht : t₁ <= t₂) : s₁
.disjSum t₁ <= s₂.disjSum t₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem disjSum_mono (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) : s₁.disjSum t₁ ⊆ s₂.disjSum t₂ :=
  val_le_iff.1 <| Multiset.disjSum_mono (val_le_iff.2 hs) (val_le_iff.2 ht)
/-
**Finset.disjSum_mono_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：disjSum_mono_left (t : Finset β) : Monotone fun s : Finset α => s.disjSum 
t
参数：t : Finset β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.disjSum_mono`：disjSum_mono (hs : s₁ subseteq s₂) (ht : t₁ subsete
q t₂) : s₁.disjSum t₁ subseteq s₂.disjSum t₂
· 使用定理 `Finset.Subset.rfl`：∀ {α : Type u_1} {s : Finset α}, s ⊆ s
-/
theorem disjSum_mono_left (t : Finset β) : Monotone fun s : Finset α => s.disjSum t :=
  fun _ _ hs => disjSum_mono hs Subset.rfl
/-
**Finset.disjSum_mono_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：disjSum_mono_right (s : Finset α) : Monotone (s.disjSum : Finset β -> Fins
et (α oplus β))
参数：s : Finset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.disjSum_mono`：disjSum_mono (hs : s₁ subseteq s₂) (ht : t₁ subsete
q t₂) : s₁.disjSum t₁ subseteq s₂.disjSum t₂
· 使用定理 `Finset.Subset.rfl`：∀ {α : Type u_1} {s : Finset α}, s ⊆ s
-/
theorem disjSum_mono_right (s : Finset α) : Monotone (s.disjSum : Finset β → Finset (α ⊕ β)) :=
  fun _ _ => disjSum_mono Subset.rfl
/-
**Finset.disjSum_ssubset_disjSum_of_ssubset_of_subset** 是 Mathlib 中的一个定理，位于命名空间 
`Finset`。
形式化陈述：disjSum_ssubset_disjSum_of_ssubset_of_subset (hs : s₁ ⊂ s₂) (ht : t₁ subse
teq t₂) : s₁.disjSum t₁ ⊂ s₂.disjSum t₂
参数：hs : s₁ ⊂ s₂；ht : t₁ subseteq t₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.val_lt_iff`：val_lt_iff {s₁ s₂ : Finset α} : s₁.1 < s₂.1 ↔ s₁ ⊂ s₂
· 使用定理 `Multiset.disjSum_lt_disjSum_of_lt_of_le`：disjSum_lt_disjSum_of_lt_of_le 
(hs : s₁ < s₂) (ht : t₁ <= t₂) : s₁.disjSum t₁ < s₂.disjSum t₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.val_le_iff`：val_le_iff {s₁ s₂ : Finset α} : s₁.1 <= s₂.1 ↔ s₁ sub
seteq s₂
-/
theorem disjSum_ssubset_disjSum_of_ssubset_of_subset (hs : s₁ ⊂ s₂) (ht : t₁ ⊆ t₂) :
    s₁.disjSum t₁ ⊂ s₂.disjSum t₂ :=
  val_lt_iff.1 <| disjSum_lt_disjSum_of_lt_of_le (val_lt_iff.2 hs) (val_le_iff.2 ht)
/-
**Finset.disjSum_ssubset_disjSum_of_subset_of_ssubset** 是 Mathlib 中的一个定理，位于命名空间 
`Finset`。
形式化陈述：disjSum_ssubset_disjSum_of_subset_of_ssubset (hs : s₁ subseteq s₂) (ht : t
₁ ⊂ t₂) : s₁.disjSum t₁ ⊂ s₂.disjSum t₂
参数：hs : s₁ subseteq s₂；ht : t₁ ⊂ t₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.val_lt_iff`：val_lt_iff {s₁ s₂ : Finset α} : s₁.1 < s₂.1 ↔ s₁ ⊂ s₂
· 使用定理 `Multiset.disjSum_lt_disjSum_of_le_of_lt`：disjSum_lt_disjSum_of_le_of_lt 
(hs : s₁ <= s₂) (ht : t₁ < t₂) : s₁.disjSum t₁ < s₂.disjSum t₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.val_le_iff`：val_le_iff {s₁ s₂ : Finset α} : s₁.1 <= s₂.1 ↔ s₁ sub
seteq s₂
-/
theorem disjSum_ssubset_disjSum_of_subset_of_ssubset (hs : s₁ ⊆ s₂) (ht : t₁ ⊂ t₂) :
    s₁.disjSum t₁ ⊂ s₂.disjSum t₂ :=
  val_lt_iff.1 <| disjSum_lt_disjSum_of_le_of_lt (val_le_iff.2 hs) (val_lt_iff.2 ht)
/-
**Finset.disjSum_strictMono_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：disjSum_strictMono_left (t : Finset β) : StrictMono fun s : Finset α => s.
disjSum t
参数：t : Finset β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.disjSum_ssubset_disjSum_of_ssubset_of_subset`：disjSum_ssubset_dis
jSum_of_ssubset_of_subset (hs : s₁ ⊂ s₂) (ht : t₁ subseteq t₂) : s₁.disjSum t₁ ⊂
 s₂.disjSum t₂
· 使用定理 `Finset.Subset.rfl`：∀ {α : Type u_1} {s : Finset α}, s ⊆ s
-/
theorem disjSum_strictMono_left (t : Finset β) : StrictMono fun s : Finset α => s.disjSum t :=
  fun _ _ hs => disjSum_ssubset_disjSum_of_ssubset_of_subset hs Subset.rfl
/-
**Finset.disjSum_strictMono_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：disjSum_strictMono_right (s : Finset α) : StrictMono (s.disjSum : Finset β
 -> Finset (α oplus β))
参数：s : Finset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.disjSum_ssubset_disjSum_of_subset_of_ssubset`：disjSum_ssubset_dis
jSum_of_subset_of_ssubset (hs : s₁ subseteq s₂) (ht : t₁ ⊂ t₂) : s₁.disjSum t₁ ⊂
 s₂.disjSum t₂
· 使用定理 `Finset.Subset.rfl`：∀ {α : Type u_1} {s : Finset α}, s ⊆ s
-/
theorem disjSum_strictMono_right (s : Finset α) :
    StrictMono (s.disjSum : Finset β → Finset (α ⊕ β)) := fun _ _ =>
  disjSum_ssubset_disjSum_of_subset_of_ssubset Subset.rfl
/-
**Finset.disjSum_inj** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_4} {β : Type u_5} {s₁ s₂ : Finset α} {t₁ t₂ : Finset β}, s₁.
disjSum t₁ = s₂.disjSum t₂ ↔ s₁ = s₂ ∧ t₁ = t₂
黑盒证明引用了以下数学事实（定理与引理）：
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
@[simp] lemma disjSum_inj {α β : Type*} {s₁ s₂ : Finset α} {t₁ t₂ : Finset β} :
    s₁.disjSum t₁ = s₂.disjSum t₂ ↔ s₁ = s₂ ∧ t₁ = t₂ := by
  simp [Finset.ext_iff]
/-
**Finset.Injective2_disjSum** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：Injective2_disjSum {α β : Type*} : Function.Injective2 (@disjSum α β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
lemma Injective2_disjSum {α β : Type*} : Function.Injective2 (@disjSum α β) :=
  fun _ _ _ _ => by simp [Finset.ext_iff]

/--
Given a finset of elements `α ⊕ β`, extract all the elements of the form `α`. This
forms a quasi-inverse to `disjSum`, in that it recovers its left input.

See also `List.partitionMap`.
-/
/-
**Finset.toLeft** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：toLeft (u : Finset (α oplus β)) : Finset α
参数：u : Finset (α oplus β)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a finset of elements `α ⊕ β`, extract all the elements of the form `α`. Th
is
forms a quasi-inverse to `disjSum`, in that it recovers its left input.

See also `List.partitionMap`.
-/
def toLeft (u : Finset (α ⊕ β)) : Finset α :=
  u.filterMap (Sum.elim some fun _ => none) (by clear x; aesop)

/--
Given a finset of elements `α ⊕ β`, extract all the elements of the form `β`. This
forms a quasi-inverse to `disjSum`, in that it recovers its right input.

See also `List.partitionMap`.
-/
/-
**Finset.toRight** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：toRight (u : Finset (α oplus β)) : Finset β
参数：u : Finset (α oplus β)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a finset of elements `α ⊕ β`, extract all the elements of the form `β`. Th
is
forms a quasi-inverse to `disjSum`, in that it recovers its right input.

See also `List.partitionMap`.
-/
def toRight (u : Finset (α ⊕ β)) : Finset β :=
  u.filterMap (Sum.elim (fun _ => none) some) (by clear x; aesop)

variable {u v : Finset (α ⊕ β)} {a : α} {b : β}
/-
**Finset.mem_toLeft** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {u : Finset (α ⊕ β)} {a : α}, a ∈ u.toLeft
 ↔ Sum.inl a ∈ u
参数：α ⊕ β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma mem_toLeft : a ∈ u.toLeft ↔ .inl a ∈ u := by simp [toLeft]
/-
**Finset.mem_toRight** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {u : Finset (α ⊕ β)} {b : β}, b ∈ u.toRigh
t ↔ Sum.inr b ∈ u
参数：α ⊕ β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma mem_toRight : b ∈ u.toRight ↔ .inr b ∈ u := by simp [toRight]

@[gcongr]
/-
**Finset.toLeft_subset_toLeft** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：toLeft_subset_toLeft : u subseteq v -> u.toLeft subseteq v.toLeft
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma toLeft_subset_toLeft : u ⊆ v → u.toLeft ⊆ v.toLeft :=
  fun h _ => by simpa only [mem_toLeft] using @h _

@[gcongr]
/-
**Finset.toRight_subset_toRight** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：toRight_subset_toRight : u subseteq v -> u.toRight subseteq v.toRight
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma toRight_subset_toRight : u ⊆ v → u.toRight ⊆ v.toRight :=
  fun h _ => by simpa only [mem_toRight] using @h _
/-
**Finset.toLeft_monotone** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：toLeft_monotone : Monotone (@toLeft α β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.toLeft_subset_toLeft`：toLeft_subset_toLeft : u subseteq v -> u.to
Left subseteq v.toLeft
-/
lemma toLeft_monotone : Monotone (@toLeft α β) := fun _ _ => toLeft_subset_toLeft
/-
**Finset.toRight_monotone** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：toRight_monotone : Monotone (@toRight α β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.toRight_subset_toRight`：toRight_subset_toRight : u subseteq v -> 
u.toRight subseteq v.toRight
-/
lemma toRight_monotone : Monotone (@toRight α β) := fun _ _ => toRight_subset_toRight
/-
**Finset.toLeft_disjSum_toRight** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：toLeft_disjSum_toRight : u.toLeft.disjSum u.toRight = u
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma toLeft_disjSum_toRight : u.toLeft.disjSum u.toRight = u := by
  ext (x | x) <;> simp
/-
**Finset.card_toLeft_add_card_toRight** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：card_toLeft_add_card_toRight : #u.toLeft + #u.toRight = #u
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_disjSum`：card_disjSum : (s.disjSum t).card = s.card + t.card
· 使用引理 `Finset.toLeft_disjSum_toRight`：toLeft_disjSum_toRight : u.toLeft.disjSum
 u.toRight = u
-/
lemma card_toLeft_add_card_toRight : #u.toLeft + #u.toRight = #u := by
  rw [← card_disjSum, toLeft_disjSum_toRight]
/-
**Finset.card_toLeft_le** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：card_toLeft_le : #u.toLeft <= #u
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
· 使用引理 `Finset.card_toLeft_add_card_toRight`：card_toLeft_add_card_toRight : #u.t
oLeft + #u.toRight = #u
-/
lemma card_toLeft_le : #u.toLeft ≤ #u :=
  (Nat.le_add_right _ _).trans_eq card_toLeft_add_card_toRight
/-
**Finset.card_toRight_le** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：card_toRight_le : #u.toRight <= #u
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Nat.le_add_left`：∀ (n m : ℕ), n ≤ m + n
· 使用引理 `Finset.card_toLeft_add_card_toRight`：card_toLeft_add_card_toRight : #u.t
oLeft + #u.toRight = #u
-/
lemma card_toRight_le : #u.toRight ≤ #u :=
  (Nat.le_add_left _ _).trans_eq card_toLeft_add_card_toRight
/-
**Finset.toLeft_disjSum** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Finset α} {t : Finset β}, (s.disjSum 
t).toLeft = s
参数：s.disjSum t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma toLeft_disjSum : (s.disjSum t).toLeft = s := by ext x; simp
/-
**Finset.toRight_disjSum** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Finset α} {t : Finset β}, (s.disjSum 
t).toRight = t
参数：s.disjSum t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma toRight_disjSum : (s.disjSum t).toRight = t := by ext x; simp
/-
**Finset.disjSum_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：disjSum_eq_iff : s.disjSum t = u ↔ s = u.toLeft ∧ t = u.toRight
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.toLeft_disjSum`：∀ {α : Type u_1} {β : Type u_2} {s : Finset α} {t
 : Finset β}, (s.disjSum t).toLeft = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.toRight_disjSum`：∀ {α : Type u_1} {β : Type u_2} {s : Finset α} {
t : Finset β}, (s.disjSum t).toRight = t
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Finset.toLeft_disjSum_toRight`：toLeft_disjSum_toRight : u.toLeft.disjSum
 u.toRight = u
-/
lemma disjSum_eq_iff : s.disjSum t = u ↔ s = u.toLeft ∧ t = u.toRight :=
  ⟨fun h => by simp [← h], fun h => by simp [h, toLeft_disjSum_toRight]⟩
/-
**Finset.eq_disjSum_iff** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：eq_disjSum_iff : u = s.disjSum t ↔ u.toLeft = s ∧ u.toRight = t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.toLeft_disjSum`：∀ {α : Type u_1} {β : Type u_2} {s : Finset α} {t
 : Finset β}, (s.disjSum t).toLeft = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.toRight_disjSum`：∀ {α : Type u_1} {β : Type u_2} {s : Finset α} {
t : Finset β}, (s.disjSum t).toRight = t
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.toLeft_disjSum_toRight`：toLeft_disjSum_toRight : u.toLeft.disjSum
 u.toRight = u
-/
lemma eq_disjSum_iff : u = s.disjSum t ↔ u.toLeft = s ∧ u.toRight = t :=
  ⟨fun h => by simp [h], fun h => by simp [← h, toLeft_disjSum_toRight]⟩
/-
**Finset.disjSum_subset** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：disjSum_subset : s.disjSum t subseteq u ↔ s subseteq u.toLeft ∧ t subseteq
 u.toRight
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma disjSum_subset : s.disjSum t ⊆ u ↔ s ⊆ u.toLeft ∧ t ⊆ u.toRight := by simp [subset_iff]
/-
**Finset.subset_disjSum** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：subset_disjSum : u subseteq s.disjSum t ↔ u.toLeft subseteq s ∧ u.toRight 
subseteq t
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma subset_disjSum : u ⊆ s.disjSum t ↔ u.toLeft ⊆ s ∧ u.toRight ⊆ t := by simp [subset_iff]
/-
**Finset.subset_map_inl** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：subset_map_inl : u subseteq s.map .inl ↔ u.toLeft subseteq s ∧ u.toRight =
 ∅
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
lemma subset_map_inl : u ⊆ s.map .inl ↔ u.toLeft ⊆ s ∧ u.toRight = ∅ := by
  simp [← disjSum_empty, subset_disjSum]
/-
**Finset.subset_map_inr** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：subset_map_inr : u subseteq t.map .inr ↔ u.toLeft = ∅ ∧ u.toRight subseteq
 t
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
lemma subset_map_inr : u ⊆ t.map .inr ↔ u.toLeft = ∅ ∧ u.toRight ⊆ t := by
  simp [← empty_disjSum, subset_disjSum]
/-
**Finset.map_inl_subset_iff_subset_toLeft** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：map_inl_subset_iff_subset_toLeft : s.map .inl subseteq u ↔ s subseteq u.to
Left
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma map_inl_subset_iff_subset_toLeft : s.map .inl ⊆ u ↔ s ⊆ u.toLeft := by
  simp [← disjSum_empty, disjSum_subset]
/-
**Finset.map_inr_subset_iff_subset_toRight** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：map_inr_subset_iff_subset_toRight : t.map .inr subseteq u ↔ t subseteq u.t
oRight
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
lemma map_inr_subset_iff_subset_toRight : t.map .inr ⊆ u ↔ t ⊆ u.toRight := by
  simp [← empty_disjSum, disjSum_subset]
/-
**Finset.gc_map_inl_toLeft** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：gc_map_inl_toLeft : GaloisConnection (·.map (.inl : α ↪ α oplus β)) toLeft
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.map_inl_subset_iff_subset_toLeft`：map_inl_subset_iff_subset_toLef
t : s.map .inl subseteq u ↔ s subseteq u.toLeft
-/
lemma gc_map_inl_toLeft : GaloisConnection (·.map (.inl : α ↪ α ⊕ β)) toLeft :=
  fun _ _ ↦ map_inl_subset_iff_subset_toLeft
/-
**Finset.gc_map_inr_toRight** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：gc_map_inr_toRight : GaloisConnection (·.map (.inr : β ↪ α oplus β)) toRig
ht
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.map_inr_subset_iff_subset_toRight`：map_inr_subset_iff_subset_toRi
ght : t.map .inr subseteq u ↔ t subseteq u.toRight
-/
lemma gc_map_inr_toRight : GaloisConnection (·.map (.inr : β ↪ α ⊕ β)) toRight :=
  fun _ _ ↦ map_inr_subset_iff_subset_toRight
/-
**Finset.toLeft_map_sumComm** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {u : Finset (α ⊕ β)}, (Finset.map (Equiv.s
umComm α β).toEmbedding u).toLeft = u.toRight
参数：α ⊕ β；Finset.map (Equiv.sumComm α β).toEmbedding u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Equiv.sumComm_apply`：∀ (α : Type u_9) (β : Type u_10), ⇑(Equiv.sumComm α
 β) = Sum.swap
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma toLeft_map_sumComm : (u.map (Equiv.sumComm _ _).toEmbedding).toLeft = u.toRight := by
  ext x; simp
/-
**Finset.toRight_map_sumComm** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {u : Finset (α ⊕ β)}, (Finset.map (Equiv.s
umComm α β).toEmbedding u).toRight = u.toLeft
参数：α ⊕ β；Finset.map (Equiv.sumComm α β).toEmbedding u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Equiv.sumComm_apply`：∀ (α : Type u_9) (β : Type u_10), ⇑(Equiv.sumComm α
 β) = Sum.swap
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma toRight_map_sumComm : (u.map (Equiv.sumComm _ _).toEmbedding).toRight = u.toLeft := by
  ext x; simp
/-
**Finset.toLeft_cons_inl** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {u : Finset (α ⊕ β)} {a : α} (ha : Sum.inl
 a ∉ u),   (Finset.cons (Sum.inl a) u ha).toLeft = Finset.cons a u.toLeft ⋯
参数：α ⊕ β；ha : Sum.inl a ∉ u；Finset.cons (Sum.inl a) u ha。
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
· 使用定理 `Sum.inl.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : α), (Sum.inl val
 = Sum.inl val_1) = (val = val_1)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma toLeft_cons_inl (ha) :
    (cons (inl a) u ha).toLeft = cons a u.toLeft (by simpa) := by ext y; simp
/-
**Finset.toLeft_cons_inr** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {u : Finset (α ⊕ β)} {b : β} (hb : Sum.inr
 b ∉ u),   (Finset.cons (Sum.inr b) u hb).toLeft = u.toLeft
参数：α ⊕ β；hb : Sum.inr b ∉ u；Finset.cons (Sum.inr b) u hb。
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
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma toLeft_cons_inr (hb) :
    (cons (inr b) u hb).toLeft = u.toLeft := by ext y; simp
/-
**Finset.toRight_cons_inl** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {u : Finset (α ⊕ β)} {a : α} (ha : Sum.inl
 a ∉ u),   (Finset.cons (Sum.inl a) u ha).toRight = u.toRight
参数：α ⊕ β；ha : Sum.inl a ∉ u；Finset.cons (Sum.inl a) u ha。
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
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma toRight_cons_inl (ha) :
    (cons (inl a) u ha).toRight = u.toRight := by ext y; simp
/-
**Finset.toRight_cons_inr** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {u : Finset (α ⊕ β)} {b : β} (hb : Sum.inr
 b ∉ u),   (Finset.cons (Sum.inr b) u hb).toRight = Finset.cons b u.toRight ⋯
参数：α ⊕ β；hb : Sum.inr b ∉ u；Finset.cons (Sum.inr b) u hb。
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
· 使用定理 `Sum.inr.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : β), (Sum.inr val
 = Sum.inr val_1) = (val = val_1)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma toRight_cons_inr (hb) :
    (cons (inr b) u hb).toRight = cons b u.toRight (by simpa) := by ext y; simp

section
variable [DecidableEq α] [DecidableEq β]

/-
**Finset.toLeft_image_swap** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：toLeft_image_swap : (u.image Sum.swap).toLeft = u.toRight
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
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `Sum.inl.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : α), (Sum.inl val
 = Sum.inl val_1) = (val = val_1)
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma toLeft_image_swap : (u.image Sum.swap).toLeft = u.toRight := by
  ext x; simp
/-
**Finset.toRight_image_swap** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：toRight_image_swap : (u.image Sum.swap).toRight = u.toLeft
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
· 使用定理 `Sum.inr.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : β), (Sum.inr val
 = Sum.inr val_1) = (val = val_1)
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma toRight_image_swap : (u.image Sum.swap).toRight = u.toLeft := by
  ext x; simp
/-
**Finset.toLeft_insert_inl** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {u : Finset (α ⊕ β)} {a : α} [inst : Decid
ableEq α] [inst_1 : DecidableEq β],   (insert (Sum.inl a) u).toLeft = insert a u
.toLeft
参数：α ⊕ β；insert (Sum.inl a) u。
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
· 使用定理 `Sum.inl.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : α), (Sum.inl val
 = Sum.inl val_1) = (val = val_1)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma toLeft_insert_inl : (insert (inl a) u).toLeft = insert a u.toLeft := by ext y; simp
/-
**Finset.toLeft_insert_inr** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {u : Finset (α ⊕ β)} {b : β} [inst : Decid
ableEq α] [inst_1 : DecidableEq β],   (insert (Sum.inr b) u).toLeft = u.toLeft
参数：α ⊕ β；insert (Sum.inr b) u。
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
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma toLeft_insert_inr : (insert (inr b) u).toLeft = u.toLeft := by ext y; simp
/-
**Finset.toRight_insert_inl** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {u : Finset (α ⊕ β)} {a : α} [inst : Decid
ableEq α] [inst_1 : DecidableEq β],   (insert (Sum.inl a) u).toRight = u.toRight
参数：α ⊕ β；insert (Sum.inl a) u。
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
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma toRight_insert_inl : (insert (inl a) u).toRight = u.toRight := by ext y; simp
/-
**Finset.toRight_insert_inr** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {u : Finset (α ⊕ β)} {b : β} [inst : Decid
ableEq α] [inst_1 : DecidableEq β],   (insert (Sum.inr b) u).toRight = insert b 
u.toRight
参数：α ⊕ β；insert (Sum.inr b) u。
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
· 使用定理 `Sum.inr.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : β), (Sum.inr val
 = Sum.inr val_1) = (val = val_1)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma toRight_insert_inr : (insert (inr b) u).toRight = insert b u.toRight := by ext y; simp
/-
**Finset.toLeft_inter** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：toLeft_inter : (u inter v).toLeft = u.toLeft inter v.toLeft
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
lemma toLeft_inter : (u ∩ v).toLeft = u.toLeft ∩ v.toLeft := by ext x; simp
/-
**Finset.toRight_inter** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：toRight_inter : (u inter v).toRight = u.toRight inter v.toRight
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
lemma toRight_inter : (u ∩ v).toRight = u.toRight ∩ v.toRight := by ext x; simp
/-
**Finset.toLeft_union** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：toLeft_union : (u union v).toLeft = u.toLeft union v.toLeft
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
lemma toLeft_union : (u ∪ v).toLeft = u.toLeft ∪ v.toLeft := by ext x; simp
/-
**Finset.toRight_union** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：toRight_union : (u union v).toRight = u.toRight union v.toRight
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
lemma toRight_union : (u ∪ v).toRight = u.toRight ∪ v.toRight := by ext x; simp
/-
**Finset.toLeft_sdiff** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：toLeft_sdiff : (u \ v).toLeft = u.toLeft \ v.toLeft
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
lemma toLeft_sdiff : (u \ v).toLeft = u.toLeft \ v.toLeft := by ext x; simp
/-
**Finset.toRight_sdiff** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：toRight_sdiff : (u \ v).toRight = u.toRight \ v.toRight
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
lemma toRight_sdiff : (u \ v).toRight = u.toRight \ v.toRight := by ext x; simp

end

set_option backward.isDefEq.respectTransparency false in
/-- Finsets on sum types are equivalent to pairs of finsets on each summand. -/
@[simps apply_fst apply_snd]
/-
**Finset.sumEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：sumEquiv {α β : Type*} : Finset (α oplus β) ≃o Finset α × Finset β where t
oFun s
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.toLeft_disjSum_toRight`：toLeft_disjSum_toRight : u.toLeft.disjSum
 u.toRight = u

--- 原说明 ---
Finsets on sum types are equivalent to pairs of finsets on each summand.
-/
def sumEquiv {α β : Type*} : Finset (α ⊕ β) ≃o Finset α × Finset β where
  toFun s := (s.toLeft, s.toRight)
  invFun s := disjSum s.1 s.2
  left_inv s := toLeft_disjSum_toRight
  right_inv s := by simp
  map_rel_iff' := by simp [← Finset.coe_subset, Set.subset_def]

@[simp]
/-
**Finset.sumEquiv_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：sumEquiv_symm_apply {α β : Type*} (s : Finset α × Finset β) : sumEquiv.sym
m s = disjSum s.1 s.2
参数：s : Finset α × Finset β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sumEquiv_symm_apply {α β : Type*} (s : Finset α × Finset β) :
    sumEquiv.symm s = disjSum s.1 s.2 := rfl
/-
**Finset.map_disjSum** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：map_disjSum (f : α oplus β ↪ γ) : (s.disjSum t).map f = (s.map (.trans .in
l f)).disjUnion (t.map (.trans .inr f)) (by as_aux_lemma => simpa only [← map_ma
p] using (Finset.disjoint_map f).2 (disjoint_map_inl_map_inr _ _))
参数：f : α oplus β ↪ γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.val_injective`：val_injective : Injective (val : Finset α -> Multi
set α)
· 使用定理 `Multiset.map_disjSum`：map_disjSum (f : α oplus β -> γ) : (s.disjSum t).m
ap f = s.map (f <| .inl ·) + t.map (f <| .inr ·)
-/
theorem map_disjSum (f : α ⊕ β ↪ γ) :
    (s.disjSum t).map f =
      (s.map (.trans .inl f)).disjUnion (t.map (.trans .inr f)) (by
        as_aux_lemma =>
          simpa only [← map_map]
            using (Finset.disjoint_map f).2 (disjoint_map_inl_map_inr _ _)) :=
  val_injective <| Multiset.map_disjSum _
/-
**Finset.fold_disjSum** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：fold_disjSum (s : Finset α) (t : Finset β) (f : α oplus β -> γ) (b₁ b₂ : γ
) (op : γ -> γ -> γ) [Std.Commutative op] [Std.Associative op] : (s.disjSum t).f
old op (op b₁ b₂) f = op (s.fold op b₁ (f <| .inl ·)) (t.fold op b₂ (f <| .inr ·
))
参数：s : Finset α；t : Finset β；f : α oplus β -> γ；b₁ b₂ : γ；op : γ -> γ -> γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.fold.congr_simp`：∀ {α : Type u_1} (op op_1 : α → α → α) (e_op :
 op = op_1) [hc : Std.Commutative op] [ha : Std.Associative op]   (a a_1 : α), a
 = a_1 → ∀ (a_…
· 使用定理 `Multiset.map_disjSum`：map_disjSum (f : α oplus β -> γ) : (s.disjSum t).m
ap f = s.map (f <| .inl ·) + t.map (f <| .inr ·)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.fold_add`：fold_add (b₁ b₂ : α) (s₁ s₂ : Multiset α) : (s₁ + s₂)
.fold op (b₁ * b₂) = s₁.fold op b₁ * s₂.fold op b₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fold_disjSum (s : Finset α) (t : Finset β) (f : α ⊕ β → γ) (b₁ b₂ : γ) (op : γ → γ → γ)
    [Std.Commutative op] [Std.Associative op] :
    (s.disjSum t).fold op (op b₁ b₂) f =
      op (s.fold op b₁ (f <| .inl ·)) (t.fold op b₂ (f <| .inr ·)) := by
  simp_rw [fold, disjSum, Multiset.map_disjSum, fold_add]

end Finset

