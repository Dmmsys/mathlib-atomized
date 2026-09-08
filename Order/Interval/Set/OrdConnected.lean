/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Order.Interval.Set.OrderEmbedding
public import Mathlib.Order.Antichain
public import Mathlib.Order.SetNotation

/-!
# Order-connected sets

We say that a set `s : Set α` is `OrdConnected` if for all `x y ∈ s` it includes the
interval `[[x, y]]`. If `α` is a `DenselyOrdered` `ConditionallyCompleteLinearOrder` with
the `OrderTopology`, then this condition is equivalent to `IsPreconnected s`. If `α` is a
linearly ordered field, then this condition is also equivalent to `Convex α s`.

In this file we prove that intersection of a family of `OrdConnected` sets is `OrdConnected` and
that all standard intervals are `OrdConnected`.
-/

@[expose] public section

open scoped Interval
open Set
open OrderDual (toDual ofDual)

namespace Set

section Preorder

variable {α β : Type*} [Preorder α] [Preorder β] {s : Set α}

/-
**Set.OrdConnected.out** 是 Mathlib 中的一个定理，位于命名空间 `Set.OrdConnected`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, s.OrdConnected → ∀ ⦃x : 
α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.OrdConnected.out'`：∀ {α : Type u_1} {inst : Preorder α} {s : Set α} 
[self : s.OrdConnected] ⦃x : α⦄,   x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s
-/
theorem OrdConnected.out (h : OrdConnected s) : ∀ ⦃x⦄ (_ : x ∈ s) ⦃y⦄ (_ : y ∈ s), Icc x y ⊆ s :=
  h.1
/-
**Set.ordConnected_def** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ordConnected_def : OrdConnected s ↔ forall ⦃x⦄ (_ : x in s) ⦃y⦄ (_ : y in 
s), Icc x y subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.OrdConnected.out'`：∀ {α : Type u_1} {inst : Preorder α} {s : Set α} 
[self : s.OrdConnected] ⦃x : α⦄,   x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s
-/
theorem ordConnected_def : OrdConnected s ↔ ∀ ⦃x⦄ (_ : x ∈ s) ⦃y⦄ (_ : y ∈ s), Icc x y ⊆ s :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

/-- It suffices to prove `[[x, y]] ⊆ s` for `x y ∈ s`, `x ≤ y`. -/
/-
**Set.ordConnected_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ordConnected_iff : OrdConnected s ↔ forall x in s, forall y in s, x <= y -
> Icc x y subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Set.ordConnected_def`：ordConnected_def : OrdConnected s ↔ forall ⦃x⦄ (_ 
: x in s) ⦃y⦄ (_ : y in s), Icc x y subseteq s
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
It suffices to prove `[[x, y]] ⊆ s` for `x y ∈ s`, `x ≤ y`.
-/
theorem ordConnected_iff : OrdConnected s ↔ ∀ x ∈ s, ∀ y ∈ s, x ≤ y → Icc x y ⊆ s :=
  ordConnected_def.trans
    ⟨fun hs _ hx _ hy _ => hs hx hy, fun H x hx y hy _ hz => H x hx y hy (le_trans hz.1 hz.2) hz⟩
/-
**Set.ordConnected_of_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ordConnected_of_Ioo {α : Type*} [PartialOrder α] {s : Set α} (hs : forall 
x in s, forall y in s, x < y -> Ioo x y subseteq s) : OrdConnected s
参数：hs : forall x in s, forall y in s, x < y -> Ioo x y subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ordConnected_iff`：ordConnected_iff : OrdConnected s ↔ forall x in s,
 forall y in s, x <= y -> Icc x y subseteq s
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.Icc_self`：Icc_self (a : α) : Icc a a = {a}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Ioc_insert_left`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α},
 b ≤ a → insert b (Set.Ioc b a) = Set.Icc b a
· 使用定理 `Set.Ioo_insert_right`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}
, b < a → insert a (Set.Ioo b a) = Set.Ioc b a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.insert_subset_iff`：insert_subset_iff : insert a s subseteq t ↔ a in 
t ∧ s subseteq t
-/
theorem ordConnected_of_Ioo {α : Type*} [PartialOrder α] {s : Set α}
    (hs : ∀ x ∈ s, ∀ y ∈ s, x < y → Ioo x y ⊆ s) : OrdConnected s := by
  rw [ordConnected_iff]
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with (rfl | hxy'); · simpa
  rw [← Ioc_insert_left hxy, ← Ioo_insert_right hxy']
  exact insert_subset_iff.2 ⟨hx, insert_subset_iff.2 ⟨hy, hs x hx y hy hxy'⟩⟩
/-
**Set.OrdConnected.preimage_mono** 是 Mathlib 中的一个定理，位于命名空间 `Set.OrdConnected`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
{s : Set α} {f : β → α},   s.OrdConnected → Monotone f → (f ⁻¹' s).OrdConnected
参数：f ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.OrdConnected.out`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, 
s.OrdConnected → ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem OrdConnected.preimage_mono {f : β → α} (hs : OrdConnected s) (hf : Monotone f) :
    OrdConnected (f ⁻¹' s) :=
  ⟨fun _ hx _ hy _ hz => hs.out hx hy ⟨hf hz.1, hf hz.2⟩⟩
/-
**Set.OrdConnected.preimage_anti** 是 Mathlib 中的一个定理，位于命名空间 `Set.OrdConnected`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
{s : Set α} {f : β → α},   s.OrdConnected → Antitone f → (f ⁻¹' s).OrdConnected
参数：f ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.OrdConnected.out`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, 
s.OrdConnected → ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem OrdConnected.preimage_anti {f : β → α} (hs : OrdConnected s) (hf : Antitone f) :
    OrdConnected (f ⁻¹' s) :=
  ⟨fun _ hx _ hy _ hz => hs.out hy hx ⟨hf hz.2, hf hz.1⟩⟩
/-
**Set.Icc_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] (s : Set α) [hs : s.OrdConnected] {x 
y : α}, x ∈ s → y ∈ s → Set.Icc x y ⊆ s
参数：s : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.OrdConnected.out`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, 
s.OrdConnected → ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s
-/
protected theorem Icc_subset (s : Set α) [hs : OrdConnected s] {x y} (hx : x ∈ s) (hy : y ∈ s) :
    Icc x y ⊆ s :=
  hs.out hx hy

end Preorder

end Set

namespace OrderEmbedding

variable {α β : Type*} [Preorder α] [Preorder β]

/-
**OrderEmbedding.image_Icc** 是 Mathlib 中的一个定理，位于命名空间 `OrderEmbedding`。
形式化陈述：image_Icc (e : α ↪o β) (he : OrdConnected (range e)) (x y : α) : e '' Icc 
x y = Icc (e x) (e y)
参数：e : α ↪o β；he : OrdConnected (range e)；x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderEmbedding.preimage_Icc`：∀ {α : Type u_1} {β : Type u_2} [inst : Pre
order α] [inst_1 : Preorder β] (e : α ↪o β) (x y : α),   ⇑e ⁻¹' Set.Icc (e x) (e
 y) = Set.Icc x y
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.inter_eq_left`：∀ {α : Type u} {s t : Set α}, s ∩ t = s ↔ s ⊆ t
· 使用定理 `Set.OrdConnected.out`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, 
s.OrdConnected → ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s
-/
theorem image_Icc (e : α ↪o β) (he : OrdConnected (range e)) (x y : α) :
    e '' Icc x y = Icc (e x) (e y) := by
  rw [← e.preimage_Icc, image_preimage_eq_inter_range, inter_eq_left.2 (he.out ⟨_, rfl⟩ ⟨_, rfl⟩)]
/-
**OrderEmbedding.image_Ico** 是 Mathlib 中的一个定理，位于命名空间 `OrderEmbedding`。
形式化陈述：image_Ico (e : α ↪o β) (he : OrdConnected (range e)) (x y : α) : e '' Ico 
x y = Ico (e x) (e y)
参数：e : α ↪o β；he : OrdConnected (range e)；x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderEmbedding.preimage_Ico`：∀ {α : Type u_1} {β : Type u_2} [inst : Pre
order α] [inst_1 : Preorder β] (e : α ↪o β) (x y : α),   ⇑e ⁻¹' Set.Ico (e x) (e
 y) = Set.Ico x y
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.inter_eq_left`：∀ {α : Type u} {s t : Set α}, s ∩ t = s ↔ s ⊆ t
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.Ico_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ico b a ⊆ Set.Icc b a
· 使用定理 `Set.OrdConnected.out`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, 
s.OrdConnected → ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s
-/
theorem image_Ico (e : α ↪o β) (he : OrdConnected (range e)) (x y : α) :
    e '' Ico x y = Ico (e x) (e y) := by
  rw [← e.preimage_Ico, image_preimage_eq_inter_range,
    inter_eq_left.2 <| Ico_subset_Icc_self.trans <| he.out ⟨_, rfl⟩ ⟨_, rfl⟩]
/-
**OrderEmbedding.image_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `OrderEmbedding`。
形式化陈述：image_Ioc (e : α ↪o β) (he : OrdConnected (range e)) (x y : α) : e '' Ioc 
x y = Ioc (e x) (e y)
参数：e : α ↪o β；he : OrdConnected (range e)；x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderEmbedding.preimage_Ioc`：∀ {α : Type u_1} {β : Type u_2} [inst : Pre
order α] [inst_1 : Preorder β] (e : α ↪o β) (x y : α),   ⇑e ⁻¹' Set.Ioc (e x) (e
 y) = Set.Ioc x y
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.inter_eq_left`：∀ {α : Type u} {s t : Set α}, s ∩ t = s ↔ s ⊆ t
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.Ioc_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc a b ⊆ Set.Icc a b
· 使用定理 `Set.OrdConnected.out`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, 
s.OrdConnected → ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s
-/
theorem image_Ioc (e : α ↪o β) (he : OrdConnected (range e)) (x y : α) :
    e '' Ioc x y = Ioc (e x) (e y) := by
  rw [← e.preimage_Ioc, image_preimage_eq_inter_range,
    inter_eq_left.2 <| Ioc_subset_Icc_self.trans <| he.out ⟨_, rfl⟩ ⟨_, rfl⟩]
/-
**OrderEmbedding.image_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `OrderEmbedding`。
形式化陈述：image_Ioo (e : α ↪o β) (he : OrdConnected (range e)) (x y : α) : e '' Ioo 
x y = Ioo (e x) (e y)
参数：e : α ↪o β；he : OrdConnected (range e)；x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderEmbedding.preimage_Ioo`：∀ {α : Type u_1} {β : Type u_2} [inst : Pre
order α] [inst_1 : Preorder β] (e : α ↪o β) (x y : α),   ⇑e ⁻¹' Set.Ioo (e x) (e
 y) = Set.Ioo x y
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.inter_eq_left`：∀ {α : Type u} {s t : Set α}, s ∩ t = s ↔ s ⊆ t
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.Ioo_subset_Icc_self`：Ioo_subset_Icc_self : Ioo a b subseteq Icc a b
· 使用定理 `Set.OrdConnected.out`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, 
s.OrdConnected → ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s
-/
theorem image_Ioo (e : α ↪o β) (he : OrdConnected (range e)) (x y : α) :
    e '' Ioo x y = Ioo (e x) (e y) := by
  rw [← e.preimage_Ioo, image_preimage_eq_inter_range,
    inter_eq_left.2 <| Ioo_subset_Icc_self.trans <| he.out ⟨_, rfl⟩ ⟨_, rfl⟩]

end OrderEmbedding

namespace Set

section Preorder

variable {α β : Type*} [Preorder α] [Preorder β]

@[simp]
/-
**Set.image_subtype_val_Icc** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_subtype_val_Icc {s : Set α} [OrdConnected s] (x y : s) : Subtype.val
 '' Icc x y = Icc x.1 y
参数：x y : s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.image_Icc`：image_Icc (e : α ↪o β) (he : OrdConnected (ran
ge e)) (x y : α) : e '' Icc x y = Icc (e x) (e y)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
-/
lemma image_subtype_val_Icc {s : Set α} [OrdConnected s] (x y : s) :
    Subtype.val '' Icc x y = Icc x.1 y :=
  (OrderEmbedding.subtype (· ∈ s)).image_Icc (by simpa) x y

@[simp]
/-
**Set.image_subtype_val_Ico** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_subtype_val_Ico {s : Set α} [OrdConnected s] (x y : s) : Subtype.val
 '' Ico x y = Ico x.1 y
参数：x y : s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.image_Ico`：image_Ico (e : α ↪o β) (he : OrdConnected (ran
ge e)) (x y : α) : e '' Ico x y = Ico (e x) (e y)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
-/
lemma image_subtype_val_Ico {s : Set α} [OrdConnected s] (x y : s) :
    Subtype.val '' Ico x y = Ico x.1 y :=
  (OrderEmbedding.subtype (· ∈ s)).image_Ico (by simpa) x y

@[simp]
/-
**Set.image_subtype_val_Ioc** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_subtype_val_Ioc {s : Set α} [OrdConnected s] (x y : s) : Subtype.val
 '' Ioc x y = Ioc x.1 y
参数：x y : s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.image_Ioc`：image_Ioc (e : α ↪o β) (he : OrdConnected (ran
ge e)) (x y : α) : e '' Ioc x y = Ioc (e x) (e y)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
-/
lemma image_subtype_val_Ioc {s : Set α} [OrdConnected s] (x y : s) :
    Subtype.val '' Ioc x y = Ioc x.1 y :=
  (OrderEmbedding.subtype (· ∈ s)).image_Ioc (by simpa) x y

@[simp]
/-
**Set.image_subtype_val_Ioo** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_subtype_val_Ioo {s : Set α} [OrdConnected s] (x y : s) : Subtype.val
 '' Ioo x y = Ioo x.1 y
参数：x y : s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.image_Ioo`：image_Ioo (e : α ↪o β) (he : OrdConnected (ran
ge e)) (x y : α) : e '' Ioo x y = Ioo (e x) (e y)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
-/
lemma image_subtype_val_Ioo {s : Set α} [OrdConnected s] (x y : s) :
    Subtype.val '' Ioo x y = Ioo x.1 y :=
  (OrderEmbedding.subtype (· ∈ s)).image_Ioo (by simpa) x y
/-
**Set.OrdConnected.inter** 是 Mathlib 中的一个定理，位于命名空间 `Set.OrdConnected`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {s t : Set α}, s.OrdConnected → t.Ord
Connected → (s ∩ t).OrdConnected
参数：s ∩ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_inter`：subset_inter {s t r : Set α} (rs : r subseteq s) (rt :
 r subseteq t) : r subseteq s inter t
· 使用定理 `Set.OrdConnected.out`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, 
s.OrdConnected → ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem OrdConnected.inter {s t : Set α} (hs : OrdConnected s) (ht : OrdConnected t) :
    OrdConnected (s ∩ t) :=
  ⟨fun _ hx _ hy => subset_inter (hs.out hx.1 hy.1) (ht.out hx.2 hy.2)⟩
/-
**Set.OrdConnected.inter'** 是 Mathlib 中的一个定理，位于命名空间 `Set.OrdConnected`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {s t : Set α} [s.OrdConnected] [t.Ord
Connected], (s ∩ t).OrdConnected
参数：s ∩ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.OrdConnected.inter`：∀ {α : Type u_1} [inst : Preorder α] {s t : Set 
α}, s.OrdConnected → t.OrdConnected → (s ∩ t).OrdConnected
-/
instance OrdConnected.inter' {s t : Set α} [OrdConnected s] [OrdConnected t] :
    OrdConnected (s ∩ t) :=
  OrdConnected.inter ‹_› ‹_›
/-
**Set.OrdConnected.dual** 是 Mathlib 中的一个定理，位于命名空间 `Set.OrdConnected`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, s.OrdConnected → (⇑Order
Dual.ofDual ⁻¹' s).OrdConnected
参数：⇑OrderDual.ofDual ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.OrdConnected.out`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, 
s.OrdConnected → ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem OrdConnected.dual {s : Set α} (hs : OrdConnected s) :
    OrdConnected (OrderDual.ofDual ⁻¹' s) :=
  ⟨fun _ hx _ hy _ hz => hs.out hy hx ⟨hz.2, hz.1⟩⟩

@[instance]
/-
**Set.dual_ordConnected** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：dual_ordConnected {s : Set α} [OrdConnected s] : OrdConnected (ofDual ⁻¹' 
s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.OrdConnected.dual`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α},
 s.OrdConnected → (⇑OrderDual.ofDual ⁻¹' s).OrdConnected
-/
theorem dual_ordConnected {s : Set α} [OrdConnected s] : OrdConnected (ofDual ⁻¹' s) :=
  .dual ‹OrdConnected s›

@[simp]
/-
**Set.ordConnected_dual** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ordConnected_dual {s : Set α} : OrdConnected (OrderDual.ofDual ⁻¹' s) ↔ Or
dConnected s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.OrdConnected.dual`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α},
 s.OrdConnected → (⇑OrderDual.ofDual ⁻¹' s).OrdConnected
-/
theorem ordConnected_dual {s : Set α} : OrdConnected (OrderDual.ofDual ⁻¹' s) ↔ OrdConnected s :=
  ⟨fun h => by simpa only [ordConnected_def] using! h.dual, fun h => h.dual⟩
/-
**Set.ordConnected_sInter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ordConnected_sInter {S : Set (Set α)} (hS : forall s in S, OrdConnected s)
 : OrdConnected (⋂₀ S)
参数：Set α；hS : forall s in S, OrdConnected s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.OrdConnected.out`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, 
s.OrdConnected → ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s
-/
theorem ordConnected_sInter {S : Set (Set α)} (hS : ∀ s ∈ S, OrdConnected s) :
    OrdConnected (⋂₀ S) :=
  ⟨fun _x hx _y hy _z hz s hs => (hS s hs).out (hx s hs) (hy s hs) hz⟩
/-
**Set.ordConnected_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ordConnected_iInter {ι : Sort*} {s : ι -> Set α} (hs : forall i, OrdConnec
ted (s i)) : OrdConnected (⋂ i, s i)
参数：hs : forall i, OrdConnected (s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ordConnected_sInter`：ordConnected_sInter {S : Set (Set α)} (hS : for
all s in S, OrdConnected s) : OrdConnected (⋂₀ S)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
-/
theorem ordConnected_iInter {ι : Sort*} {s : ι → Set α} (hs : ∀ i, OrdConnected (s i)) :
    OrdConnected (⋂ i, s i) :=
  ordConnected_sInter <| forall_mem_range.2 hs
/-
**Set.ordConnected_iInter'** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：ordConnected_iInter' {ι : Sort*} {s : ι -> Set α} [forall i, OrdConnected 
(s i)] : OrdConnected (⋂ i, s i)
参数：s i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ordConnected_iInter`：ordConnected_iInter {ι : Sort*} {s : ι -> Set α
} (hs : forall i, OrdConnected (s i)) : OrdConnected (⋂ i, s i)
-/
instance ordConnected_iInter' {ι : Sort*} {s : ι → Set α} [∀ i, OrdConnected (s i)] :
    OrdConnected (⋂ i, s i) :=
  ordConnected_iInter ‹_›
/-
**Set.ordConnected_biInter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ordConnected_biInter {ι : Sort*} {p : ι -> Prop} {s : forall i, p i -> Set
 α} (hs : forall i hi, OrdConnected (s i hi)) : OrdConnected (⋂ (i) (hi), s i hi
)
参数：hs : forall i hi, OrdConnected (s i hi)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ordConnected_iInter`：ordConnected_iInter {ι : Sort*} {s : ι -> Set α
} (hs : forall i, OrdConnected (s i)) : OrdConnected (⋂ i, s i)
-/
theorem ordConnected_biInter {ι : Sort*} {p : ι → Prop} {s : ∀ i, p i → Set α}
    (hs : ∀ i hi, OrdConnected (s i hi)) : OrdConnected (⋂ (i) (hi), s i hi) :=
  ordConnected_iInter fun i => ordConnected_iInter <| hs i
/-
**Set.ordConnected_pi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ordConnected_pi {ι : Type*} {α : ι -> Type*} [forall i, Preorder (α i)] {s
 : Set ι} {t : forall i, Set (α i)} (h : forall i in s, OrdConnected (t i)) : Or
dConnected (s.pi t)
参数：α i；α i；h : forall i in s, OrdConnected (t i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.OrdConnected.out`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, 
s.OrdConnected → ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem ordConnected_pi {ι : Type*} {α : ι → Type*} [∀ i, Preorder (α i)] {s : Set ι}
    {t : ∀ i, Set (α i)} (h : ∀ i ∈ s, OrdConnected (t i)) : OrdConnected (s.pi t) :=
  ⟨fun _ hx _ hy _ hz i hi => (h i hi).out (hx i hi) (hy i hi) ⟨hz.1 i, hz.2 i⟩⟩
/-
**Set.ordConnected_pi'** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：ordConnected_pi' {ι : Type*} {α : ι -> Type*} [forall i, Preorder (α i)] {
s : Set ι} {t : forall i, Set (α i)} [h : forall i, OrdConnected (t i)] : OrdCon
nected (s.pi t)
参数：α i；α i；t i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ordConnected_pi`：ordConnected_pi {ι : Type*} {α : ι -> Type*} [foral
l i, Preorder (α i)] {s : Set ι} {t : forall i, Set (α i)} (h : forall i in s, O
rdConnect…
-/
instance ordConnected_pi' {ι : Type*} {α : ι → Type*} [∀ i, Preorder (α i)] {s : Set ι}
    {t : ∀ i, Set (α i)} [h : ∀ i, OrdConnected (t i)] : OrdConnected (s.pi t) :=
  ordConnected_pi fun i _ => h i

@[to_dual]
/-
**Set.ordConnected_Ici** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：ordConnected_Ici {a : α} : OrdConnected (Ici a)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
instance ordConnected_Ici {a : α} : OrdConnected (Ici a) :=
  ⟨fun _ hx _ _ _ hz => le_trans hx hz.1⟩

@[to_dual]
/-
**Set.ordConnected_Ioi** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：ordConnected_Ioi {a : α} : OrdConnected (Ioi a)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
instance ordConnected_Ioi {a : α} : OrdConnected (Ioi a) :=
  ⟨fun _ hx _ _ _ hz => lt_of_lt_of_le hx hz.1⟩

@[to_dual self]
/-
**Set.ordConnected_Icc** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：ordConnected_Icc {a b : α} : OrdConnected (Icc a b)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.OrdConnected.inter`：∀ {α : Type u_1} [inst : Preorder α] {s t : Set 
α}, s.OrdConnected → t.OrdConnected → (s ∩ t).OrdConnected
· 使用定理 `Set.ordConnected_Iic`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, (Set
.Iic a).OrdConnected
-/
instance ordConnected_Icc {a b : α} : OrdConnected (Icc a b) :=
  ordConnected_Ici.inter ordConnected_Iic

@[to_dual]
/-
**Set.ordConnected_Ico** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：ordConnected_Ico {a b : α} : OrdConnected (Ico a b)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.OrdConnected.inter`：∀ {α : Type u_1} [inst : Preorder α] {s t : Set 
α}, s.OrdConnected → t.OrdConnected → (s ∩ t).OrdConnected
· 使用定理 `Set.ordConnected_Iio`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, (Set
.Iio a).OrdConnected
-/
instance ordConnected_Ico {a b : α} : OrdConnected (Ico a b) :=
  ordConnected_Ici.inter ordConnected_Iio

@[to_dual self]
/-
**Set.ordConnected_Ioo** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：ordConnected_Ioo {a b : α} : OrdConnected (Ioo a b)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.OrdConnected.inter`：∀ {α : Type u_1} [inst : Preorder α] {s t : Set 
α}, s.OrdConnected → t.OrdConnected → (s ∩ t).OrdConnected
· 使用定理 `Set.ordConnected_Iio`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, (Set
.Iio a).OrdConnected
-/
instance ordConnected_Ioo {a b : α} : OrdConnected (Ioo a b) :=
  ordConnected_Ioi.inter ordConnected_Iio

@[instance]
/-
**Set.ordConnected_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ordConnected_singleton {α : Type*} [PartialOrder α] {a : α} : OrdConnected
 ({a} : Set α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Icc_self`：Icc_self (a : α) : Icc a a = {a}
-/
theorem ordConnected_singleton {α : Type*} [PartialOrder α] {a : α} :
    OrdConnected ({a} : Set α) := by
  rw [← Icc_self]
  exact ordConnected_Icc

@[instance]
/-
**Set.ordConnected_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ordConnected_empty : OrdConnected (∅ : Set α)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ordConnected_empty : OrdConnected (∅ : Set α) :=
  ⟨fun _ => False.elim⟩

@[instance]
/-
**Set.ordConnected_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ordConnected_univ : OrdConnected (univ : Set α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
theorem ordConnected_univ : OrdConnected (univ : Set α) :=
  ⟨fun _ _ _ _ => subset_univ _⟩

/-- In a dense order `α`, the subtype from an `OrdConnected` set is also densely ordered. -/
/-
**Set.instDenselyOrdered** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：instDenselyOrdered [DenselyOrdered α] {s : Set α} [hs : OrdConnected s] : 
DenselyOrdered s
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用定理 `Set.OrdConnected.out`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, 
s.OrdConnected → ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Set.Ioo_subset_Icc_self`：Ioo_subset_Icc_self : Ioo a b subseteq Icc a b

--- 原说明 ---
In a dense order `α`, the subtype from an `OrdConnected` set is also densely ord
ered.
-/
instance instDenselyOrdered [DenselyOrdered α] {s : Set α} [hs : OrdConnected s] :
    DenselyOrdered s :=
  ⟨fun a b (h : (a : α) < b) =>
    let ⟨x, H⟩ := exists_between h
    ⟨⟨x, (hs.out a.2 b.2) (Ioo_subset_Icc_self H)⟩, H⟩⟩

@[instance]
/-
**Set.ordConnected_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ordConnected_preimage {F : Type*} [FunLike F α β] [OrderHomClass F α β] (f
 : F) {s : Set β} [hs : OrdConnected s] : OrdConnected (f ⁻¹' s)
参数：f : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.OrdConnected.out`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, 
s.OrdConnected → ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s
· 使用定理 `OrderHomClass.mono`：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} [inst
 : Preorder α] [inst_1 : Preorder β] [inst_2 : FunLike F α β]   [OrderHomClass F
 α β] (f…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem ordConnected_preimage {F : Type*} [FunLike F α β] [OrderHomClass F α β] (f : F)
    {s : Set β} [hs : OrdConnected s] : OrdConnected (f ⁻¹' s) :=
  ⟨fun _ hx _ hy _ hz => hs.out hx hy ⟨OrderHomClass.mono _ hz.1, OrderHomClass.mono _ hz.2⟩⟩

@[instance]
/-
**Set.ordConnected_image** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ordConnected_image {E : Type*} [EquivLike E α β] [OrderIsoClass E α β] (e 
: E) {s : Set α} [hs : OrdConnected s] : OrdConnected (e '' s)
参数：e : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderIso.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃o β) (s 
: Set α) : e '' s = e.symm ⁻¹' s
· 使用定理 `Set.ordConnected_preimage`：ordConnected_preimage {F : Type*} [FunLike F 
α β] [OrderHomClass F α β] (f : F) {s : Set β} [hs : OrdConnected s] : OrdConnec
ted (f ⁻¹' s)
· 使用定理 `RelIso.instRelHomClass`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Pro
p} {s : β → β → Prop}, RelHomClass (r ≃r s) r s
-/
theorem ordConnected_image {E : Type*} [EquivLike E α β] [OrderIsoClass E α β] (e : E) {s : Set α}
    [hs : OrdConnected s] : OrdConnected (e '' s) := by
  erw [(e : α ≃o β).image_eq_preimage_symm]
  apply ordConnected_preimage (e : α ≃o β).symm

@[instance]
/-
**Set.ordConnected_range** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ordConnected_range {E : Type*} [EquivLike E α β] [OrderIsoClass E α β] (e 
: E) : OrdConnected (range e)
参数：e : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ordConnected_image`：ordConnected_image {E : Type*} [EquivLike E α β]
 [OrderIsoClass E α β] (e : E) {s : Set α} [hs : OrdConnected s] : OrdConnected 
(e '' s)
· 使用定理 `OrderIso.instOrderIsoClass`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α
] [inst_1 : LE β], OrderIsoClass (α ≃o β) α β
· 使用定理 `Set.ordConnected_univ`：ordConnected_univ : OrdConnected (univ : Set α)
-/
theorem ordConnected_range {E : Type*} [EquivLike E α β] [OrderIsoClass E α β] (e : E) :
    OrdConnected (range e) := by
  simp_rw [← image_univ]
  exact ordConnected_image (e : α ≃o β)

/-- The preimage of an `OrdConnected` set under a map which is monotone on a set `t`,
when intersected with `t`, is `OrdConnected`. More precisely, it is the intersection with `t`
of an `OrdConnected` set. -/
/-
**Set.OrdConnected.preimage_monotoneOn** 是 Mathlib 中的一个定理，位于命名空间 `Set.OrdConnect
ed`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
{f : β → α} {t : Set β} {s : Set α},   s.OrdConnected → MonotoneOn f t → ∃ u, u.
OrdConnected ∧ t ∩ f ⁻¹' s = t ∩ u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Set.OrdConnected.out`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, 
s.OrdConnected → ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s

--- 原说明 ---
The preimage of an `OrdConnected` set under a map which is monotone on a set `t`
,
when intersected with `t`, is `OrdConnected`. More precisely, it is the intersec
tion with `t`
of an `OrdConnected` set.
-/
theorem OrdConnected.preimage_monotoneOn {f : β → α} {t : Set β} {s : Set α}
    (hs : OrdConnected s) (hf : MonotoneOn f t) :
    ∃ u, OrdConnected u ∧ t ∩ f ⁻¹' s = t ∩ u := by
  let u := {x | (∃ y ∈ t, y ≤ x ∧ f y ∈ s) ∧ (∃ z ∈ t, x ≤ z ∧ f z ∈ s)}
  refine ⟨u, ⟨?_⟩, Subset.antisymm ?_ ?_⟩
  · rintro x ⟨⟨y, yt, yx, ys⟩, -⟩ x' ⟨-, ⟨z, zt, x'z, zs⟩⟩ a ha
    exact ⟨⟨y, yt, yx.trans ha.1, ys⟩, ⟨z, zt, ha.2.trans x'z, zs⟩⟩
  · rintro x ⟨xt, xs⟩
    exact ⟨xt, ⟨x, xt, le_rfl, xs⟩, ⟨x, xt, le_rfl, xs⟩⟩
  · rintro x ⟨xt, ⟨y, yt, yx, ys⟩, ⟨z, zt, xz, zs⟩⟩
    refine ⟨xt, ?_⟩
    apply hs.out ys zs
    exact ⟨hf yt xt yx, hf xt zt xz⟩

/-- The preimage of an `OrdConnected` set under a map which is antitone on a set `t`,
when intersected with `t`, is `OrdConnected`. More precisely, it is the intersection with `t`
of an `OrdConnected` set. -/
/-
**Set.OrdConnected.preimage_antitoneOn** 是 Mathlib 中的一个定理，位于命名空间 `Set.OrdConnect
ed`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
{f : β → α} {t : Set β} {s : Set α},   s.OrdConnected → AntitoneOn f t → ∃ u, u.
OrdConnected ∧ t ∩ f ⁻¹' s = t ∩ u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.OrdConnected.preimage_monotoneOn`：∀ {α : Type u_1} {β : Type u_2} [i
nst : Preorder α] [inst_1 : Preorder β] {f : β → α} {t : Set β} {s : Set α},   s
.OrdConnected → MonotoneOn…
· 使用定理 `Set.OrdConnected.dual`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α},
 s.OrdConnected → (⇑OrderDual.ofDual ⁻¹' s).OrdConnected
· 使用定理 `AntitoneOn.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [
inst_1 : Preorder β] {f : α → β} {s : Set α},   AntitoneOn f s → MonotoneOn (⇑Or
derDual.toD…

--- 原说明 ---
The preimage of an `OrdConnected` set under a map which is antitone on a set `t`
,
when intersected with `t`, is `OrdConnected`. More precisely, it is the intersec
tion with `t`
of an `OrdConnected` set.
-/
theorem OrdConnected.preimage_antitoneOn {f : β → α} {t : Set β} {s : Set α}
    (hs : OrdConnected s) (hf : AntitoneOn f t) :
    ∃ u, OrdConnected u ∧ t ∩ f ⁻¹' s = t ∩ u :=
  (OrdConnected.preimage_monotoneOn hs.dual hf.dual_right :)

end Preorder

section PartialOrder

variable {α : Type*} [PartialOrder α] {s : Set α} {x y : α}

/-
**Set._root_.IsAntichain.ordConnected** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem _root_.IsAntichain.ordConnected (hs : IsAntichain (· ≤ ·) s) : s.OrdConnected :=
  ⟨fun x hx y hy z hz => by
    obtain rfl := hs.eq hx hy (hz.1.trans hz.2)
    rw [Icc_self, mem_singleton_iff] at hz
    rwa [hz]⟩
/-
**Set.ordConnected_inter_Icc_of_subset** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：ordConnected_inter_Icc_of_subset (h : Ioo x y subseteq s) : OrdConnected (
s inter Icc x y)
参数：h : Ioo x y subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ordConnected_of_Ioo`：ordConnected_of_Ioo {α : Type*} [PartialOrder α
] {s : Set α} (hs : forall x in s, forall y in s, x < y -> Ioo x y subseteq s) :
 OrdConnected…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.Ioo_subset_Ioo`：Ioo_subset_Ioo (ha : a₂ <= a₁) (hb : b₁ <= b₂) : Ioo
 a₁ b₁ subseteq Ioo a₂ b₂
· 使用定理 `Set.subset_inter`：subset_inter {s t r : Set α} (rs : r subseteq s) (rt :
 r subseteq t) : r subseteq s inter t
· 使用定理 `Set.Ioo_subset_Icc_self`：Ioo_subset_Icc_self : Ioo a b subseteq Icc a b
-/
lemma ordConnected_inter_Icc_of_subset (h : Ioo x y ⊆ s) : OrdConnected (s ∩ Icc x y) :=
  ordConnected_of_Ioo fun _u ⟨_, hu, _⟩ _v ⟨_, _, hv⟩ _ ↦
    Ioo_subset_Ioo hu hv |>.trans <| subset_inter h Ioo_subset_Icc_self
/-
**Set.ordConnected_inter_Icc_iff** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：ordConnected_inter_Icc_iff (hx : x in s) (hy : y in s) : OrdConnected (s i
nter Icc x y) ↔ Ioo x y subseteq s
参数：hx : x in s；hy : y in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.Ioo_subset_Icc_self`：Ioo_subset_Icc_self : Ioo a b subseteq Icc a b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.OrdConnected.out`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, 
s.OrdConnected → ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.left_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Se
t.Icc a b ↔ a ≤ b
· 使用定理 `Set.right_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ S
et.Icc b a ↔ b ≤ a
· 使用引理 `Set.ordConnected_inter_Icc_of_subset`：ordConnected_inter_Icc_of_subset (
h : Ioo x y subseteq s) : OrdConnected (s inter Icc x y)
-/
lemma ordConnected_inter_Icc_iff (hx : x ∈ s) (hy : y ∈ s) :
    OrdConnected (s ∩ Icc x y) ↔ Ioo x y ⊆ s := by
  refine ⟨fun h ↦ Ioo_subset_Icc_self.trans fun z hz ↦ ?_, ordConnected_inter_Icc_of_subset⟩
  have hxy : x ≤ y := hz.1.trans hz.2
  exact h.out ⟨hx, left_mem_Icc.2 hxy⟩ ⟨hy, right_mem_Icc.2 hxy⟩ hz |>.1
/-
**Set.not_ordConnected_inter_Icc_iff** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：not_ordConnected_inter_Icc_iff (hx : x in s) (hy : y in s) : ¬ OrdConnecte
d (s inter Icc x y) ↔ exists z ∉ s, z in Ioo x y
参数：hx : x in s；hy : y in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.ordConnected_inter_Icc_iff`：ordConnected_inter_Icc_iff (hx : x in s)
 (hy : y in s) : OrdConnected (s inter Icc x y) ↔ Ioo x y subseteq s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma not_ordConnected_inter_Icc_iff (hx : x ∈ s) (hy : y ∈ s) :
    ¬ OrdConnected (s ∩ Icc x y) ↔ ∃ z ∉ s, z ∈ Ioo x y := by
  simp_rw [ordConnected_inter_Icc_iff hx hy, subset_def, not_forall, exists_prop, and_comm]

end PartialOrder

section LinearOrder

open scoped Interval

variable {α : Type*} [LinearOrder α] {s : Set α} {x : α}

@[instance]
/-
**Set.ordConnected_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ordConnected_uIcc {a b : α} : OrdConnected [[a, b]]
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ordConnected_uIcc {a b : α} : OrdConnected [[a, b]] :=
  ordConnected_Icc

@[instance]
/-
**Set.ordConnected_uIoc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ordConnected_uIoc {a b : α} : OrdConnected (Ι a b)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ordConnected_Ioc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, (S
et.Ioc b a).OrdConnected
-/
theorem ordConnected_uIoc {a b : α} : OrdConnected (Ι a b) :=
  ordConnected_Ioc
/-
**Set.OrdConnected.uIcc_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set.OrdConnected`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {s : Set α},   s.OrdConnected → ∀ 
⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.uIcc x y ⊆ s
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.OrdConnected.out`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, 
s.OrdConnected → ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s
· 使用引理 `min_rec'`：min_rec' (p : α -> Prop) (ha : p a) (hb : p b) : p (min a b)
· 使用定理 `max_rec'`：∀ {α : Type u_2} [inst : LinearOrder α] {a b : α} (p : α → Pro
p), p a → p b → p (max a b)
-/
theorem OrdConnected.uIcc_subset (hs : OrdConnected s) ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s) :
    [[x, y]] ⊆ s :=
  hs.out (min_rec' (· ∈ s) hx hy) (max_rec' (· ∈ s) hx hy)
/-
**Set.OrdConnected.uIoc_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set.OrdConnected`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {s : Set α},   s.OrdConnected → ∀ 
⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.uIoc x y ⊆ s
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.Ioc_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc a b ⊆ Set.Icc a b
· 使用定理 `Set.OrdConnected.uIcc_subset`：∀ {α : Type u_1} [inst : LinearOrder α] {s
 : Set α},   s.OrdConnected → ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.uIcc x y
 ⊆ s
-/
theorem OrdConnected.uIoc_subset (hs : OrdConnected s) ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s) :
    Ι x y ⊆ s :=
  Ioc_subset_Icc_self.trans <| hs.uIcc_subset hx hy
/-
**Set.ordConnected_iff_uIcc_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ordConnected_iff_uIcc_subset : OrdConnected s ↔ forall ⦃x⦄ (_ : x in s) ⦃y
⦄ (_ : y in s), [[x, y]] subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.OrdConnected.uIcc_subset`：∀ {α : Type u_1} [inst : LinearOrder α] {s
 : Set α},   s.OrdConnected → ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.uIcc x y
 ⊆ s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Set.Icc_subset_uIcc`：Icc_subset_uIcc : Icc a b subseteq [[a, b]]
-/
theorem ordConnected_iff_uIcc_subset :
    OrdConnected s ↔ ∀ ⦃x⦄ (_ : x ∈ s) ⦃y⦄ (_ : y ∈ s), [[x, y]] ⊆ s :=
  ⟨fun h => h.uIcc_subset, fun H => ⟨fun _ hx _ hy => Icc_subset_uIcc.trans <| H hx hy⟩⟩
/-
**Set.ordConnected_of_uIcc_subset_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ordConnected_of_uIcc_subset_left (h : forall y in s, [[x, y]] subseteq s) 
: OrdConnected s
参数：h : forall y in s, [[x, y]] subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.ordConnected_iff_uIcc_subset`：ordConnected_iff_uIcc_subset : OrdConn
ected s ↔ forall ⦃x⦄ (_ : x in s) ⦃y⦄ (_ : y in s), [[x, y]] subseteq s
· 使用引理 `Set.uIcc_subset_uIcc_union_uIcc`：uIcc_subset_uIcc_union_uIcc : [[a, c]] 
subseteq [[a, b]] union [[b, c]]
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.uIcc_comm`：uIcc_comm (a b : α) : [[a, b]] = [[b, a]]
· 使用定理 `Set.union_subset`：union_subset {s t r : Set α} (sr : s subseteq r) (tr :
 t subseteq r) : s union t subseteq r
-/
theorem ordConnected_of_uIcc_subset_left (h : ∀ y ∈ s, [[x, y]] ⊆ s) : OrdConnected s :=
  ordConnected_iff_uIcc_subset.2 fun y hy z hz =>
    calc
      [[y, z]] ⊆ [[y, x]] ∪ [[x, z]] := uIcc_subset_uIcc_union_uIcc
      _ = [[x, y]] ∪ [[x, z]] := by rw [uIcc_comm]
      _ ⊆ s := union_subset (h y hy) (h z hz)
/-
**Set.ordConnected_iff_uIcc_subset_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ordConnected_iff_uIcc_subset_left (hx : x in s) : OrdConnected s ↔ forall 
⦃y⦄, y in s -> [[x, y]] subseteq s
参数：hx : x in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.OrdConnected.uIcc_subset`：∀ {α : Type u_1} [inst : LinearOrder α] {s
 : Set α},   s.OrdConnected → ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.uIcc x y
 ⊆ s
· 使用定理 `Set.ordConnected_of_uIcc_subset_left`：ordConnected_of_uIcc_subset_left (
h : forall y in s, [[x, y]] subseteq s) : OrdConnected s
-/
theorem ordConnected_iff_uIcc_subset_left (hx : x ∈ s) :
    OrdConnected s ↔ ∀ ⦃y⦄, y ∈ s → [[x, y]] ⊆ s :=
  ⟨fun hs => hs.uIcc_subset hx, ordConnected_of_uIcc_subset_left⟩
/-
**Set.ordConnected_iff_uIcc_subset_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ordConnected_iff_uIcc_subset_right (hx : x in s) : OrdConnected s ↔ forall
 ⦃y⦄, y in s -> [[y, x]] subseteq s
参数：hx : x in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ordConnected_iff_uIcc_subset_left`：ordConnected_iff_uIcc_subset_left
 (hx : x in s) : OrdConnected s ↔ forall ⦃y⦄, y in s -> [[x, y]] subseteq s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `Set.uIcc_comm`：uIcc_comm (a b : α) : [[a, b]] = [[b, a]]
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ordConnected_iff_uIcc_subset_right (hx : x ∈ s) :
    OrdConnected s ↔ ∀ ⦃y⦄, y ∈ s → [[y, x]] ⊆ s := by
  simp_rw [ordConnected_iff_uIcc_subset_left hx, uIcc_comm]

@[simp]
/-
**Set.image_subtype_val_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_subtype_val_uIcc [OrdConnected s] (a b : s) : Subtype.val '' [[a, b]
] = [[a.1, b.1]]
参数：a b : s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.image_subtype_val_Icc`：image_subtype_val_Icc {s : Set α} [OrdConnect
ed s] (x y : s) : Subtype.val '' Icc x y = Icc x.1 y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Monotone.map_inf`：∀ {α : Type u} {β : Type v} [inst : LinearOrder α] [in
st_1 : SemilatticeInf β] {f : α → β},   Monotone f → ∀ (x y : α), f (min x y) = 
f x ⊓ …
· 使用定理 `Subtype.mono_coe`：Subtype.mono_coe [Preorder α] (p : α -> Prop) : Monoto
ne ((↑) : Subtype p -> α)
· 使用定理 `Monotone.map_sup`：map_sup [SemilatticeSup β] {f : α -> β} (hf : Monotone
 f) (x y : α) : f (x ⊔ y) = f x ⊔ f y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_subtype_val_uIcc [OrdConnected s] (a b : s) :
    Subtype.val '' [[a, b]] = [[a.1, b.1]] := by
  simp [uIcc, (Subtype.mono_coe (· ∈ s)).map_inf, (Subtype.mono_coe (· ∈ s)).map_sup]

@[simp]
/-
**Set.image_subtype_val_uIoc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_subtype_val_uIoc [OrdConnected s] (a b : s) : Subtype.val '' uIoc a 
b = uIoc a.1 b.1
参数：a b : s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.image_subtype_val_Ioc`：image_subtype_val_Ioc {s : Set α} [OrdConnect
ed s] (x y : s) : Subtype.val '' Ioc x y = Ioc x.1 y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Monotone.map_inf`：∀ {α : Type u} {β : Type v} [inst : LinearOrder α] [in
st_1 : SemilatticeInf β] {f : α → β},   Monotone f → ∀ (x y : α), f (min x y) = 
f x ⊓ …
· 使用定理 `Subtype.mono_coe`：Subtype.mono_coe [Preorder α] (p : α -> Prop) : Monoto
ne ((↑) : Subtype p -> α)
· 使用定理 `Monotone.map_sup`：map_sup [SemilatticeSup β] {f : α -> β} (hf : Monotone
 f) (x y : α) : f (x ⊔ y) = f x ⊔ f y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_subtype_val_uIoc [OrdConnected s] (a b : s) :
    Subtype.val '' uIoc a b = uIoc a.1 b.1 := by
  simp [uIoc, (Subtype.mono_coe (· ∈ s)).map_inf, (Subtype.mono_coe (· ∈ s)).map_sup]

@[simp]
/-
**Set.image_subtype_val_uIoo** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_subtype_val_uIoo [OrdConnected s] (a b : s) : Subtype.val '' uIoo a 
b = uIoo a.1 b.1
参数：a b : s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.image_subtype_val_Ioo`：image_subtype_val_Ioo {s : Set α} [OrdConnect
ed s] (x y : s) : Subtype.val '' Ioo x y = Ioo x.1 y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Monotone.map_inf`：∀ {α : Type u} {β : Type v} [inst : LinearOrder α] [in
st_1 : SemilatticeInf β] {f : α → β},   Monotone f → ∀ (x y : α), f (min x y) = 
f x ⊓ …
· 使用定理 `Subtype.mono_coe`：Subtype.mono_coe [Preorder α] (p : α -> Prop) : Monoto
ne ((↑) : Subtype p -> α)
· 使用定理 `Monotone.map_sup`：map_sup [SemilatticeSup β] {f : α -> β} (hf : Monotone
 f) (x y : α) : f (x ⊔ y) = f x ⊔ f y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_subtype_val_uIoo [OrdConnected s] (a b : s) :
    Subtype.val '' uIoo a b = uIoo a.1 b.1 := by
  simp [uIoo, (Subtype.mono_coe (· ∈ s)).map_inf, (Subtype.mono_coe (· ∈ s)).map_sup]

end LinearOrder

end Set

