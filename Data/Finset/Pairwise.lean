/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Set.Pairwise.List

/-!
# Relations holding pairwise on finite sets

In this file we prove a few results about the interaction of `Set.PairwiseDisjoint` and `Finset`,
as well as the interaction of `List.Pairwise Disjoint` and the condition of
`Disjoint` on `List.toFinset`, in `Set` form.
-/

public section


open Finset

variable {α ι ι' : Type*}

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableEq α] {r : α → α → Prop} [DecidableRel r] {s : Finset α} :
    Decidable ((s : Set α).Pairwise r) :=
  decidable_of_iff' (∀ a ∈ s, ∀ b ∈ s, a ≠ b → r a b) Iff.rfl
/-
**Finset.pairwiseDisjoint_range_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.pairwiseDisjoint_range_singleton : (Set.range (singleton : α -> Fin
set α)).PairwiseDisjoint id
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.disjoint_singleton`：disjoint_singleton : Disjoint ({a} : Finset α
) {b} ↔ a != b
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
-/
theorem Finset.pairwiseDisjoint_range_singleton :
    (Set.range (singleton : α → Finset α)).PairwiseDisjoint id := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ h
  exact disjoint_singleton.2 (ne_of_apply_ne _ h)

namespace Set

/-
**Set.PairwiseDisjoint.elim_finset** 是 Mathlib 中的一个定理，位于命名空间 `Set.PairwiseDisjoi
nt`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} {s : Set ι} {f : ι → Finset α},   s.Pairwi
seDisjoint f → ∀ {i j : ι}, i ∈ s → j ∈ s → ∀ a ∈ f i, a ∈ f j → i = j
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.PairwiseDisjoint.elim`：∀ {α : Type u_1} {ι : Type u_4} [inst : Parti
alOrder α] [inst_1 : OrderBot α] {s : Set ι} {f : ι → α},   s.PairwiseDisjoint f
 → ∀ {i j : ι},…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.not_disjoint_iff`：not_disjoint_iff : ¬Disjoint s t ↔ exists a, a 
in s ∧ a in t
-/
theorem PairwiseDisjoint.elim_finset {s : Set ι} {f : ι → Finset α} (hs : s.PairwiseDisjoint f)
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (a : α) (hai : a ∈ f i) (haj : a ∈ f j) : i = j :=
  hs.elim hi hj (Finset.not_disjoint_iff.2 ⟨a, hai, haj⟩)

section SemilatticeInf

variable [SemilatticeInf α] [OrderBot α] {s : Finset ι} {f : ι → α}

/-
**Set.PairwiseDisjoint.image_finset_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Set.Pairwis
eDisjoint`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} [inst : SemilatticeInf α] [inst_1 : OrderB
ot α] [inst_2 : DecidableEq ι] {s : Finset ι}   {f : ι → α},   (↑s).PairwiseDisj
oint f → ∀ {g : ι → ι}, (∀ (a : ι), f (g a) ≤ f a) → (↑(Finset.image g s)).Pairw
iseDisjoint f
参数：↑s；∀ (a : ι), f (g a) ≤ f a；↑(Finset.image g s)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Set.PairwiseDisjoint.image_of_le`：∀ {α : Type u_1} {ι : Type u_4} [inst 
: PartialOrder α] [inst_1 : OrderBot α] {s : Set ι} {f : ι → α},   s.PairwiseDis
joint f → ∀ {g : ι → ι…
-/
theorem PairwiseDisjoint.image_finset_of_le [DecidableEq ι] {s : Finset ι} {f : ι → α}
    (hs : (s : Set ι).PairwiseDisjoint f) {g : ι → ι} (hf : ∀ a, f (g a) ≤ f a) :
    (s.image g : Set ι).PairwiseDisjoint f := by
  rw [coe_image]
  exact hs.image_of_le hf
/-
**Set.PairwiseDisjoint.attach** 是 Mathlib 中的一个定理，位于命名空间 `Set.PairwiseDisjoint`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} [inst : SemilatticeInf α] [inst_1 : OrderB
ot α] {s : Finset ι} {f : ι → α},   (↑s).PairwiseDisjoint f → (↑s.attach).Pairwi
seDisjoint (f ∘ Subtype.val)
参数：↑s；↑s.attach；f ∘ Subtype.val。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
theorem PairwiseDisjoint.attach (hs : (s : Set ι).PairwiseDisjoint f) :
    (s.attach : Set { x // x ∈ s }).PairwiseDisjoint (f ∘ Subtype.val) := fun i _ j _ hij =>
  hs i.2 j.2 <| mt Subtype.ext hij

end SemilatticeInf

variable [Lattice α] [OrderBot α]

/-- Bind operation for `Set.PairwiseDisjoint`. In a complete lattice, you can use
`Set.PairwiseDisjoint.biUnion`. -/
/-
**Set.PairwiseDisjoint.biUnion_finset** 是 Mathlib 中的一个定理，位于命名空间 `Set.PairwiseDis
joint`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} {ι' : Type u_3} [inst : Lattice α] [inst_1
 : OrderBot α] {s : Set ι'}   {g : ι' → Finset ι} {f : ι → α},   (s.PairwiseDisj
oint fun i' => (g i').sup f) →     (∀ i ∈ s, (↑(g i)).PairwiseDisjoint f) → (⋃ i
 ∈ s, ↑(g i)).PairwiseDisjoint f
参数：s.PairwiseDisjoint fun i' => (g i').sup f；∀ i ∈ s, (↑(g i)).PairwiseDisjoint 
f；⋃ i ∈ s, ↑(g i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Disjoint.mono`：Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.s
upport <= f.support) (hg : y.support <= g.support) : Disjoint x y
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y

--- 原说明 ---
Bind operation for `Set.PairwiseDisjoint`. In a complete lattice, you can use
`Set.PairwiseDisjoint.biUnion`.
-/
theorem PairwiseDisjoint.biUnion_finset {s : Set ι'} {g : ι' → Finset ι} {f : ι → α}
    (hs : s.PairwiseDisjoint fun i' : ι' => (g i').sup f)
    (hg : ∀ i ∈ s, (g i : Set ι).PairwiseDisjoint f) : (⋃ i ∈ s, ↑(g i)).PairwiseDisjoint f := by
  rintro a ha b hb hab
  simp_rw [Set.mem_iUnion] at ha hb
  obtain ⟨c, hc, ha⟩ := ha
  obtain ⟨d, hd, hb⟩ := hb
  obtain hcd | hcd := eq_or_ne (g c) (g d)
  · exact hg d hd (by rwa [hcd] at ha) hb hab
  · exact (hs hc hd (ne_of_apply_ne _ hcd)).mono (Finset.le_sup ha) (Finset.le_sup hb)

end Set

namespace List

variable {β : Type*} [DecidableEq α] {r : α → α → Prop} {l : List α}

/-
**List.pairwise_of_coe_toFinset_pairwise** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：pairwise_of_coe_toFinset_pairwise (hl : (l.toFinset : Set α).Pairwise r) (
hn : l.Nodup) : l.Pairwise r
参数：hl : (l.toFinset : Set α).Pairwise r；hn : l.Nodup。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Nodup.pairwise_of_set_pairwise`：∀ {α : Type u_1} {l : List α} {r : 
α → α → Prop}, l.Nodup → {x | x ∈ l}.Pairwise r → List.Pairwise r l
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.coe_toFinset`：coe_toFinset (l : List α) : (l.toFinset : Set α) = { 
a | a in l }
-/
theorem pairwise_of_coe_toFinset_pairwise (hl : (l.toFinset : Set α).Pairwise r) (hn : l.Nodup) :
    l.Pairwise r := by
  rw [coe_toFinset] at hl
  exact hn.pairwise_of_set_pairwise hl
/-
**List.pairwise_iff_coe_toFinset_pairwise** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：pairwise_iff_coe_toFinset_pairwise [Std.Symm r] (hn : l.Nodup) : (l.toFins
et : Set α).Pairwise r ↔ l.Pairwise r
参数：hn : l.Nodup。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.coe_toFinset`：coe_toFinset (l : List α) : (l.toFinset : Set α) = { 
a | a in l }
· 使用定理 `List.Nodup.pairwise_coe`：∀ {α : Type u_1} {r : α → α → Prop} {l : List α
} [Std.Symm r], l.Nodup → ({a | a ∈ l}.Pairwise r ↔ List.Pairwise r l)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem pairwise_iff_coe_toFinset_pairwise [Std.Symm r] (hn : l.Nodup) :
    (l.toFinset : Set α).Pairwise r ↔ l.Pairwise r := by
  rw [coe_toFinset, hn.pairwise_coe]

open scoped Function -- required for scoped `on` notation
/-
**List.pairwise_disjoint_of_coe_toFinset_pairwiseDisjoint** 是 Mathlib 中的一个定理，位于命
名空间 `List`。
形式化陈述：pairwise_disjoint_of_coe_toFinset_pairwiseDisjoint {α ι} [PartialOrder α] 
[OrderBot α] [DecidableEq ι] {l : List ι} {f : ι -> α} (hl : (l.toFinset : Set ι
).PairwiseDisjoint f) (hn : l.Nodup) : l.Pairwise (_root_.Disjoint on f)
参数：hl : (l.toFinset : Set ι).PairwiseDisjoint f；hn : l.Nodup。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.pairwise_of_coe_toFinset_pairwise`：pairwise_of_coe_toFinset_pairwis
e (hl : (l.toFinset : Set α).Pairwise r) (hn : l.Nodup) : l.Pairwise r
-/
theorem pairwise_disjoint_of_coe_toFinset_pairwiseDisjoint {α ι} [PartialOrder α] [OrderBot α]
    [DecidableEq ι] {l : List ι} {f : ι → α} (hl : (l.toFinset : Set ι).PairwiseDisjoint f)
    (hn : l.Nodup) : l.Pairwise (_root_.Disjoint on f) :=
  pairwise_of_coe_toFinset_pairwise hl hn
/-
**List.pairwiseDisjoint_iff_coe_toFinset_pairwise_disjoint** 是 Mathlib 中的一个定理，位于
命名空间 `List`。
形式化陈述：pairwiseDisjoint_iff_coe_toFinset_pairwise_disjoint {α ι} [PartialOrder α]
 [OrderBot α] [DecidableEq ι] {l : List ι} {f : ι -> α} (hn : l.Nodup) : (l.toFi
nset : Set ι).PairwiseDisjoint f ↔ l.Pairwise (_root_.Disjoint on f)
参数：hn : l.Nodup。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.pairwise_iff_coe_toFinset_pairwise`：pairwise_iff_coe_toFinset_pairw
ise [Std.Symm r] (hn : l.Nodup) : (l.toFinset : Set α).Pairwise r ↔ l.Pairwise r
-/
theorem pairwiseDisjoint_iff_coe_toFinset_pairwise_disjoint {α ι} [PartialOrder α] [OrderBot α]
    [DecidableEq ι] {l : List ι} {f : ι → α} (hn : l.Nodup) :
    (l.toFinset : Set ι).PairwiseDisjoint f ↔ l.Pairwise (_root_.Disjoint on f) :=
  pairwise_iff_coe_toFinset_pairwise hn

end List

