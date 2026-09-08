/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Group.Multiset

/-!
# Disjoint sum of multisets

This file defines the disjoint sum of two multisets as `Multiset (α ⊕ β)`. Beware not to confuse
with the `Multiset.sum` operation which computes the additive sum.

## Main declarations

* `Multiset.disjSum`: `s.disjSum t` is the disjoint sum of `s` and `t`.
-/

@[expose] public section


open Sum

namespace Multiset

variable {α β γ : Type*} (s : Multiset α) (t : Multiset β)

/-- Disjoint sum of multisets. -/
/-
**Multiset.disjSum** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：disjSum : Multiset (α oplus β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Disjoint sum of multisets.
-/
def disjSum : Multiset (α ⊕ β) :=
  s.map inl + t.map inr

@[simp]
/-
**Multiset.zero_disjSum** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：zero_disjSum : (0 : Multiset α).disjSum t = t.map inr
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.zero_add`：∀ {α : Type u_1} (s : Multiset α), 0 + s = s
-/
theorem zero_disjSum : (0 : Multiset α).disjSum t = t.map inr :=
  Multiset.zero_add _

@[simp]
/-
**Multiset.disjSum_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：disjSum_zero : s.disjSum (0 : Multiset β) = s.map inl
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.add_zero`：∀ {α : Type u_1} (s : Multiset α), s + 0 = s
-/
theorem disjSum_zero : s.disjSum (0 : Multiset β) = s.map inl :=
  Multiset.add_zero _

@[simp]
/-
**Multiset.card_disjSum** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：card_disjSum : Multiset.card (s.disjSum t) = Multiset.card s + Multiset.ca
rd t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.disjSum.eq_1`：∀ {α : Type u_1} {β : Type u_2} (s : Multiset α) 
(t : Multiset β),   s.disjSum t = Multiset.map Sum.inl s + Multiset.map Sum.inr 
t
· 使用定理 `Multiset.card_add`：card_add (s t : Multiset α) : card (s + t) = card s +
 card t
· 使用定理 `Multiset.card_map`：card_map (f : α -> β) (s) : card (map f s) = card s
-/
theorem card_disjSum : Multiset.card (s.disjSum t) = Multiset.card s + Multiset.card t := by
  rw [disjSum, card_add, card_map, card_map]

variable {s t} {s₁ s₂ : Multiset α} {t₁ t₂ : Multiset β} {a : α} {b : β} {x : α ⊕ β}
/-
**Multiset.mem_disjSum** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：mem_disjSum : x in s.disjSum t ↔ (exists a, a in s ∧ inl a = x) ∨ exists b
, b in t ∧ inr b = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_disjSum : x ∈ s.disjSum t ↔ (∃ a, a ∈ s ∧ inl a = x) ∨ ∃ b, b ∈ t ∧ inr b = x := by
  simp_rw [disjSum, mem_add, mem_map]

@[simp]
/-
**Multiset.inl_mem_disjSum** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：inl_mem_disjSum : inl a in s.disjSum t ↔ a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.mem_disjSum`：mem_disjSum : x in s.disjSum t ↔ (exists a, a in s
 ∧ inl a = x) ∨ exists b, b in t ∧ inr b = x
· 使用定理 `or_iff_left`：∀ {b a : Prop}, ¬b → (a ∨ b ↔ a)
· 使用定理 `Sum.inr_ne_inl`：∀ {β : Type u_1} {b : β} {α : Type u_2} {a : α}, Sum.inr
 b ≠ Sum.inl a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Sum.inl.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : α), (Sum.inl val
 = Sum.inl val_1) = (val = val_1)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem inl_mem_disjSum : inl a ∈ s.disjSum t ↔ a ∈ s := by
  rw [mem_disjSum, or_iff_left]
  · simp only [inl.injEq, exists_eq_right]
  rintro ⟨b, _, hb⟩
  exact inr_ne_inl hb

@[simp]
/-
**Multiset.inr_mem_disjSum** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：inr_mem_disjSum : inr b in s.disjSum t ↔ b in t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.mem_disjSum`：mem_disjSum : x in s.disjSum t ↔ (exists a, a in s
 ∧ inl a = x) ∨ exists b, b in t ∧ inr b = x
· 使用定理 `or_iff_right`：∀ {a b : Prop}, ¬a → (a ∨ b ↔ b)
· 使用定理 `Sum.inl_ne_inr`：∀ {α : Type u_1} {a : α} {β : Type u_2} {b : β}, Sum.inl
 a ≠ Sum.inr b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Sum.inr.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : β), (Sum.inr val
 = Sum.inr val_1) = (val = val_1)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem inr_mem_disjSum : inr b ∈ s.disjSum t ↔ b ∈ t := by
  rw [mem_disjSum, or_iff_right]
  · simp only [inr.injEq, exists_eq_right]
  rintro ⟨a, _, ha⟩
  exact inl_ne_inr ha
/-
**Multiset.disjSum_mono** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：disjSum_mono (hs : s₁ <= s₂) (ht : t₁ <= t₂) : s₁.disjSum t₁ <= s₂.disjSum
 t₂
参数：hs : s₁ <= s₂；ht : t₁ <= t₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Multiset.map_le_map`：map_le_map {f : α -> β} {s t : Multiset α} (h : s <
= t) : map f s <= map f t
-/
theorem disjSum_mono (hs : s₁ ≤ s₂) (ht : t₁ ≤ t₂) : s₁.disjSum t₁ ≤ s₂.disjSum t₂ :=
  add_le_add (map_le_map hs) (map_le_map ht)
/-
**Multiset.disjSum_mono_left** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：disjSum_mono_left (t : Multiset β) : Monotone fun s : Multiset α => s.disj
Sum t
参数：t : Multiset β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.add_le_add_right`：∀ {α : Type u_1} {s t u : Multiset α}, s ≤ t 
→ s + u ≤ t + u
· 使用定理 `Multiset.map_le_map`：map_le_map {f : α -> β} {s t : Multiset α} (h : s <
= t) : map f s <= map f t
-/
theorem disjSum_mono_left (t : Multiset β) : Monotone fun s : Multiset α => s.disjSum t :=
  fun _ _ hs => Multiset.add_le_add_right (map_le_map hs)
/-
**Multiset.disjSum_mono_right** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：disjSum_mono_right (s : Multiset α) : Monotone (s.disjSum : Multiset β -> 
Multiset (α oplus β))
参数：s : Multiset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.add_le_add_left`：∀ {α : Type u_1} {s t u : Multiset α}, t ≤ u →
 s + t ≤ s + u
· 使用定理 `Multiset.map_le_map`：map_le_map {f : α -> β} {s t : Multiset α} (h : s <
= t) : map f s <= map f t
-/
theorem disjSum_mono_right (s : Multiset α) :
    Monotone (s.disjSum : Multiset β → Multiset (α ⊕ β)) := fun _ _ ht =>
  Multiset.add_le_add_left (map_le_map ht)
/-
**Multiset.disjSum_lt_disjSum_of_lt_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：disjSum_lt_disjSum_of_lt_of_le (hs : s₁ < s₂) (ht : t₁ <= t₂) : s₁.disjSum
 t₁ < s₂.disjSum t₂
参数：hs : s₁ < s₂；ht : t₁ <= t₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_lt_add_of_lt_of_le`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preord
er α] [AddLeftMono α] [AddRightStrictMono α] {a b c d : α},   a < b → c ≤ d → a 
+ c < b + d
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Multiset.map_lt_map`：map_lt_map {f : α -> β} {s t : Multiset α} (h : s <
 t) : s.map f < t.map f
· 使用定理 `Multiset.map_le_map`：map_le_map {f : α -> β} {s t : Multiset α} (h : s <
= t) : map f s <= map f t
-/
theorem disjSum_lt_disjSum_of_lt_of_le (hs : s₁ < s₂) (ht : t₁ ≤ t₂) :
    s₁.disjSum t₁ < s₂.disjSum t₂ :=
  add_lt_add_of_lt_of_le (map_lt_map hs) (map_le_map ht)
/-
**Multiset.disjSum_lt_disjSum_of_le_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：disjSum_lt_disjSum_of_le_of_lt (hs : s₁ <= s₂) (ht : t₁ < t₂) : s₁.disjSum
 t₁ < s₂.disjSum t₂
参数：hs : s₁ <= s₂；ht : t₁ < t₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_lt_add_of_le_of_lt`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preord
er α] [AddLeftStrictMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c < d → a 
+ c < b + d
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Multiset.map_le_map`：map_le_map {f : α -> β} {s t : Multiset α} (h : s <
= t) : map f s <= map f t
· 使用定理 `Multiset.map_lt_map`：map_lt_map {f : α -> β} {s t : Multiset α} (h : s <
 t) : s.map f < t.map f
-/
theorem disjSum_lt_disjSum_of_le_of_lt (hs : s₁ ≤ s₂) (ht : t₁ < t₂) :
    s₁.disjSum t₁ < s₂.disjSum t₂ :=
  add_lt_add_of_le_of_lt (map_le_map hs) (map_lt_map ht)
/-
**Multiset.disjSum_strictMono_left** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：disjSum_strictMono_left (t : Multiset β) : StrictMono fun s : Multiset α =
> s.disjSum t
参数：t : Multiset β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.disjSum_lt_disjSum_of_lt_of_le`：disjSum_lt_disjSum_of_lt_of_le 
(hs : s₁ < s₂) (ht : t₁ <= t₂) : s₁.disjSum t₁ < s₂.disjSum t₂
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem disjSum_strictMono_left (t : Multiset β) : StrictMono fun s : Multiset α => s.disjSum t :=
  fun _ _ hs => disjSum_lt_disjSum_of_lt_of_le hs le_rfl
/-
**Multiset.disjSum_strictMono_right** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：disjSum_strictMono_right (s : Multiset α) : StrictMono (s.disjSum : Multis
et β -> Multiset (α oplus β))
参数：s : Multiset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.disjSum_lt_disjSum_of_le_of_lt`：disjSum_lt_disjSum_of_le_of_lt 
(hs : s₁ <= s₂) (ht : t₁ < t₂) : s₁.disjSum t₁ < s₂.disjSum t₂
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem disjSum_strictMono_right (s : Multiset α) :
    StrictMono (s.disjSum : Multiset β → Multiset (α ⊕ β)) := fun _ _ =>
  disjSum_lt_disjSum_of_le_of_lt le_rfl
/-
**Multiset.Nodup.disjSum** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Nodup`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Multiset α} {t : Multiset β}, s.Nodup
 → t.Nodup → (s.disjSum t).Nodup
参数：s.disjSum t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.Nodup.add_iff`：∀ {α : Type u_1} {s t : Multiset α}, s.Nodup → t
.Nodup → ((s + t).Nodup ↔ Disjoint s t)
· 使用定理 `Multiset.Nodup.map`：∀ {α : Type u_1} {β : Type v} {f : α → β} {s : Multi
set α}, Function.Injective f → s.Nodup → (Multiset.map f s).Nodup
· 使用定理 `Sum.inl_injective`：inl_injective : Function.Injective (inl : α -> α oplu
s β)
· 使用定理 `Sum.inr_injective`：inr_injective : Function.Injective (inr : β -> α oplu
s β)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.disjoint_map_map`：disjoint_map_map {f : α -> γ} {g : β -> γ} {s
 : Multiset α} {t : Multiset β} : Disjoint (s.map f) (t.map g) ↔ forall a in s, 
forall b in t, …
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Sum.inr_ne_inl`：∀ {β : Type u_1} {b : β} {α : Type u_2} {a : α}, Sum.inr
 b ≠ Sum.inl a
-/
protected theorem Nodup.disjSum (hs : s.Nodup) (ht : t.Nodup) : (s.disjSum t).Nodup := by
  refine ((hs.map inl_injective).add_iff <| ht.map inr_injective).2 ?_
  rw [disjoint_map_map]
  exact fun _ _ _ _ ↦ inr_ne_inl.symm
/-
**Multiset.map_disjSum** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：map_disjSum (f : α oplus β -> γ) : (s.disjSum t).map f = s.map (f <| .inl 
·) + t.map (f <| .inr ·)
参数：f : α oplus β -> γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_add`：map_add (f : α -> β) (s t) : map f (s + t) = map f s +
 map f t
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_disjSum (f : α ⊕ β → γ) :
    (s.disjSum t).map f = s.map (f <| .inl ·) + t.map (f <| .inr ·) := by
  simp_rw [disjSum, map_add, map_map, Function.comp_def]

end Multiset

