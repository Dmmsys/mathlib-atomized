/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Topology.Bornology.Constructions

/-!
# Bornology of order-bounded sets

This file relates the notion of bornology-boundedness (sets that lie in a bornology) to the notion
of order-boundedness (sets that are bounded above and below).

## Main declarations

* `orderBornology`: The bornology of order-bounded sets of a nonempty lattice.
* `IsOrderBornology`: Typeclass predicate for a preorder to be equipped with its order-bornology.
-/

@[expose] public section

open Bornology Set

variable {α : Type*} {s t : Set α}

section Lattice
variable [Lattice α] [Nonempty α]

/-- Order-bornology on a nonempty lattice. The bounded sets are the sets that are bounded both above
and below. -/
@[instance_reducible]
/-
**orderBornology** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：orderBornology : Bornology α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Order-bornology on a nonempty lattice. The bounded sets are the sets that are bo
unded both above
and below.
-/
def orderBornology : Bornology α := .ofBounded
  {s | BddBelow s ∧ BddAbove s}
  (by simp)
  (fun _ hs _ hst ↦ ⟨hs.1.mono hst, hs.2.mono hst⟩)
  (fun _ hs _ ht ↦ ⟨hs.1.union ht.1, hs.2.union ht.2⟩)
  (by simp)

set_option backward.isDefEq.respectTransparency false in
/-
**orderBornology_isBounded** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} {s : Set α} [inst : Lattice α] [inst_1 : Nonempty α], Bor
nology.IsBounded s ↔ BddBelow s ∧ BddAbove s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma orderBornology_isBounded : orderBornology.IsBounded s ↔ BddBelow s ∧ BddAbove s := by
  simp [IsBounded, IsCobounded, -isCobounded_compl_iff]

end Lattice

variable [Bornology α]

variable (α) [Preorder α] in
/-- Predicate for a preorder to be equipped with its order-bornology, namely for its bounded sets
to be the ones that are bounded both above and below. -/
/-
**IsOrderBornology** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_1) → [Bornology α] → [Preorder α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Predicate for a preorder to be equipped with its order-bornology, namely for its
 bounded sets
to be the ones that are bounded both above and below.
-/
class IsOrderBornology : Prop where
  protected isBounded_iff_bddBelow_bddAbove (s : Set α) : IsBounded s ↔ BddBelow s ∧ BddAbove s
/-
**isOrderBornology_iff_eq_orderBornology** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isOrderBornology_iff_eq_orderBornology [Lattice α] [Nonempty α] : IsOrderB
ornology α ↔ ‹Bornology α› = orderBornology
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Bornology.ext`：Bornology.ext (t t' : Bornology α) (h_cobounded : @Bornol
ogy.cobounded α t = @Bornology.cobounded α t') : t = t'
· 使用定理 `Filter.ext`：∀ {α : Type u_1} {f g : Filter α}, (∀ (s : Set α), s ∈ f ↔ s
 ∈ g) → f = g
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Bornology.isBounded_compl_iff`：isBounded_compl_iff : IsBounded sᶜ ↔ IsCo
bounded s
· 使用定理 `IsOrderBornology.isBounded_iff_bddBelow_bddAbove`：∀ {α : Type u_1} {inst
 : Bornology α} {inst_1 : Preorder α} [self : IsOrderBornology α] (s : Set α),  
 Bornology.IsBounded s ↔ BddBelow s ∧ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `orderBornology_isBounded`：∀ {α : Type u_1} {s : Set α} [inst : Lattice α
] [inst_1 : Nonempty α], Bornology.IsBounded s ↔ BddBelow s ∧ BddAbove s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isOrderBornology_iff_eq_orderBornology [Lattice α] [Nonempty α] :
    IsOrderBornology α ↔ ‹Bornology α› = orderBornology := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨fun s ↦ by rw [h, orderBornology_isBounded]⟩⟩
  ext s
  exact isBounded_compl_iff.symm.trans (h.1 _)

section Preorder
variable [Preorder α] [IsOrderBornology α]

/-
**isBounded_iff_bddBelow_bddAbove** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isBounded_iff_bddBelow_bddAbove : IsBounded s ↔ BddBelow s ∧ BddAbove s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderBornology.isBounded_iff_bddBelow_bddAbove`：∀ {α : Type u_1} {inst
 : Bornology α} {inst_1 : Preorder α} [self : IsOrderBornology α] (s : Set α),  
 Bornology.IsBounded s ↔ BddBelow s ∧ …
-/
lemma isBounded_iff_bddBelow_bddAbove : IsBounded s ↔ BddBelow s ∧ BddAbove s :=
  IsOrderBornology.isBounded_iff_bddBelow_bddAbove _
/-
**Bornology.IsBounded.bddBelow** 是 Mathlib 中的一个定理，位于命名空间 `Bornology.IsBounded`。
形式化陈述：∀ {α : Type u_1} {s : Set α} [inst : Bornology α] [inst_1 : Preorder α] [I
sOrderBornology α],   Bornology.IsBounded s → BddBelow s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `isBounded_iff_bddBelow_bddAbove`：isBounded_iff_bddBelow_bddAbove : IsBou
nded s ↔ BddBelow s ∧ BddAbove s
-/
protected lemma Bornology.IsBounded.bddBelow (hs : IsBounded s) : BddBelow s :=
  (isBounded_iff_bddBelow_bddAbove.1 hs).1
/-
**Bornology.IsBounded.bddAbove** 是 Mathlib 中的一个定理，位于命名空间 `Bornology.IsBounded`。
形式化陈述：∀ {α : Type u_1} {s : Set α} [inst : Bornology α] [inst_1 : Preorder α] [I
sOrderBornology α],   Bornology.IsBounded s → BddAbove s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `isBounded_iff_bddBelow_bddAbove`：isBounded_iff_bddBelow_bddAbove : IsBou
nded s ↔ BddBelow s ∧ BddAbove s
-/
protected lemma Bornology.IsBounded.bddAbove (hs : IsBounded s) : BddAbove s :=
  (isBounded_iff_bddBelow_bddAbove.1 hs).2
/-
**BddBelow.isBounded** 是 Mathlib 中的一个定理，位于命名空间 `BddBelow`。
形式化陈述：∀ {α : Type u_1} {s : Set α} [inst : Bornology α] [inst_1 : Preorder α] [I
sOrderBornology α],   BddBelow s → BddAbove s → Bornology.IsBounded s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `isBounded_iff_bddBelow_bddAbove`：isBounded_iff_bddBelow_bddAbove : IsBou
nded s ↔ BddBelow s ∧ BddAbove s
-/
protected lemma BddBelow.isBounded (hs₀ : BddBelow s) (hs₁ : BddAbove s) : IsBounded s :=
  isBounded_iff_bddBelow_bddAbove.2 ⟨hs₀, hs₁⟩
/-
**BddAbove.isBounded** 是 Mathlib 中的一个定理，位于命名空间 `BddAbove`。
形式化陈述：∀ {α : Type u_1} {s : Set α} [inst : Bornology α] [inst_1 : Preorder α] [I
sOrderBornology α],   BddAbove s → BddBelow s → Bornology.IsBounded s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `isBounded_iff_bddBelow_bddAbove`：isBounded_iff_bddBelow_bddAbove : IsBou
nded s ↔ BddBelow s ∧ BddAbove s
-/
protected lemma BddAbove.isBounded (hs₀ : BddAbove s) (hs₁ : BddBelow s) : IsBounded s :=
  isBounded_iff_bddBelow_bddAbove.2 ⟨hs₁, hs₀⟩
/-
**BddBelow.isBounded_inter** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：BddBelow.isBounded_inter (hs : BddBelow s) (ht : BddAbove t) : IsBounded (
s inter t)
参数：hs : BddBelow s；ht : BddAbove t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BddBelow.isBounded`：∀ {α : Type u_1} {s : Set α} [inst : Bornology α] [i
nst_1 : Preorder α] [IsOrderBornology α],   BddBelow s → BddAbove s → Bornology.
IsBounde…
· 使用定理 `BddBelow.mono`：∀ {α : Type u_1} [inst : Preorder α] ⦃s t : Set α⦄, s ⊆ t
 → BddBelow t → BddBelow s
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `BddAbove.mono`：BddAbove.mono ⦃s t : Set α⦄ (h : s subseteq t) : BddAbove
 t -> BddAbove s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
lemma BddBelow.isBounded_inter (hs : BddBelow s) (ht : BddAbove t) : IsBounded (s ∩ t) :=
  (hs.mono inter_subset_left).isBounded <| ht.mono inter_subset_right
/-
**BddAbove.isBounded_inter** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：BddAbove.isBounded_inter (hs : BddAbove s) (ht : BddBelow t) : IsBounded (
s inter t)
参数：hs : BddAbove s；ht : BddBelow t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BddAbove.isBounded`：∀ {α : Type u_1} {s : Set α} [inst : Bornology α] [i
nst_1 : Preorder α] [IsOrderBornology α],   BddAbove s → BddBelow s → Bornology.
IsBounde…
· 使用定理 `BddAbove.mono`：BddAbove.mono ⦃s t : Set α⦄ (h : s subseteq t) : BddAbove
 t -> BddAbove s
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `BddBelow.mono`：∀ {α : Type u_1} [inst : Preorder α] ⦃s t : Set α⦄, s ⊆ t
 → BddBelow t → BddBelow s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
lemma BddAbove.isBounded_inter (hs : BddAbove s) (ht : BddBelow t) : IsBounded (s ∩ t) :=
  (hs.mono inter_subset_left).isBounded <| ht.mono inter_subset_right
/-
**OrderDual.instIsOrderBornology** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：OrderDual.instIsOrderBornology : IsOrderBornology αᵒᵈ where isBounded_iff_
bddBelow_bddAbove s
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderDual.isBounded_preimage_toDual`：∀ {α : Type u_2} [inst : Bornology 
α] {s : Set αᵒᵈ},   Bornology.IsBounded (⇑OrderDual.toDual ⁻¹' s) ↔ Bornology.Is
Bounded s
· 使用定理 `bddBelow_preimage_toDual`：∀ {α : Type u_1} [inst : Preorder α] {s : Set 
αᵒᵈ}, BddBelow (⇑OrderDual.toDual ⁻¹' s) ↔ BddAbove s
· 使用引理 `bddAbove_preimage_toDual`：bddAbove_preimage_toDual {s : Set αᵒᵈ} : BddAb
ove (toDual ⁻¹' s) ↔ BddBelow s
· 使用引理 `isBounded_iff_bddBelow_bddAbove`：isBounded_iff_bddBelow_bddAbove : IsBou
nded s ↔ BddBelow s ∧ BddAbove s
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
instance OrderDual.instIsOrderBornology : IsOrderBornology αᵒᵈ where
  isBounded_iff_bddBelow_bddAbove s := by
    rw [← isBounded_preimage_toDual, ← bddBelow_preimage_toDual, ← bddAbove_preimage_toDual,
      isBounded_iff_bddBelow_bddAbove, and_comm]
/-
**Prod.instIsOrderBornology** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.instIsOrderBornology {β : Type*} [Preorder β] [Bornology β] [IsOrderB
ornology β] : IsOrderBornology (α × β) where isBounded_iff_bddBelow_bddAbove s
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Bornology.isBounded_image_fst_and_snd`：isBounded_image_fst_and_snd {s : 
Set (α × β)} : IsBounded (Prod.fst '' s) ∧ IsBounded (Prod.snd '' s) ↔ IsBounded
 s
· 使用定理 `bddBelow_prod`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst
_1 : Preorder β] {s : Set (α × β)},   BddBelow s ↔ BddBelow (Prod.fst '' s) ∧ Bd
dBe…
· 使用引理 `bddAbove_prod`：bddAbove_prod {s : Set (α × β)} : BddAbove s ↔ BddAbove (
Prod.fst '' s) ∧ BddAbove (Prod.snd '' s)
· 使用定理 `and_and_and_comm`：∀ {a b c d : Prop}, (a ∧ b) ∧ c ∧ d ↔ (a ∧ c) ∧ b ∧ d
· 使用引理 `isBounded_iff_bddBelow_bddAbove`：isBounded_iff_bddBelow_bddAbove : IsBou
nded s ↔ BddBelow s ∧ BddAbove s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
instance Prod.instIsOrderBornology {β : Type*} [Preorder β] [Bornology β] [IsOrderBornology β] :
    IsOrderBornology (α × β) where
  isBounded_iff_bddBelow_bddAbove s := by
    rw [← isBounded_image_fst_and_snd, bddBelow_prod, bddAbove_prod, and_and_and_comm,
      isBounded_iff_bddBelow_bddAbove, isBounded_iff_bddBelow_bddAbove]
/-
**Pi.instIsOrderBornology** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.instIsOrderBornology {ι : Type*} {α : ι -> Type*} [forall i, Preorder (
α i)] [forall i, Bornology (α i)] [forall i, IsOrderBornology (α i)] : IsOrderBo
rnology (forall i, α i) where isBounded_iff_bddBelow_bddAbove s
参数：α i；α i；α i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
instance Pi.instIsOrderBornology {ι : Type*} {α : ι → Type*} [∀ i, Preorder (α i)]
    [∀ i, Bornology (α i)] [∀ i, IsOrderBornology (α i)] : IsOrderBornology (∀ i, α i) where
  isBounded_iff_bddBelow_bddAbove s := by
    simp_rw [← forall_isBounded_image_eval_iff, bddBelow_pi, bddAbove_pi, ← forall_and,
      isBounded_iff_bddBelow_bddAbove]

variable (α) in
/-
**Nonempty.of_isOrderBornology** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Nonempty.of_isOrderBornology : Nonempty α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.nonempty`：∀ {α : Sort u_1} {p : α → Prop}, (∃ x, p x) → Nonempty 
α
· 使用定理 `Bornology.IsBounded.bddBelow`：∀ {α : Type u_1} {s : Set α} [inst : Borno
logy α] [inst_1 : Preorder α] [IsOrderBornology α],   Bornology.IsBounded s → Bd
dBelow s
· 使用定理 `Bornology.isBounded_empty`：isBounded_empty : IsBounded (∅ : Set α)
-/
lemma Nonempty.of_isOrderBornology : Nonempty α := Bornology.isBounded_empty.bddBelow.nonempty
/-
**IsOrderBornology.neBot_cobounded_of_noBotOrder** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsOrderBornology.neBot_cobounded_of_noBotOrder [NoBotOrder α] : (cobounded
 α).NeBot
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
instance IsOrderBornology.neBot_cobounded_of_noBotOrder [NoBotOrder α] : (cobounded α).NeBot := by
  simp [Filter.neBot_iff, cobounded_eq_bot_iff, ← isBounded_univ, isBounded_iff_bddBelow_bddAbove]
/-
**IsOrderBornology.neBot_cobounded_of_noTopOrder** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsOrderBornology.neBot_cobounded_of_noTopOrder [NoTopOrder α] : (cobounded
 α).NeBot
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance IsOrderBornology.neBot_cobounded_of_noTopOrder [NoTopOrder α] : (cobounded α).NeBot :=
  neBot_cobounded_of_noBotOrder (α := αᵒᵈ)
/-
**IsOrderBornology.atTop_le_cobounded** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsOrderBornology.atTop_le_cobounded [NoMaxOrder α] : .atTop <= Bornology.c
obounded α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `isBounded_iff_bddBelow_bddAbove`：isBounded_iff_bddBelow_bddAbove : IsBou
nded s ↔ BddBelow s ∧ BddAbove s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Bornology.isBounded_def`：isBounded_def {s : Set α} : IsBounded s ↔ sᶜ in
 cobounded α
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `NoMaxOrder.exists_gt`：∀ {α : Type u_3} {inst : LT α} [self : NoMaxOrder 
α] (a : α), ∃ b, a < b
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Filter.mem_atTop`：mem_atTop [Preorder α] (a : α) : { b : α | a <= b } in
 @atTop α _
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.mem_compl`：mem_compl {s : Set α} {x : α} (h : x ∉ s) : x in sᶜ
-/
lemma IsOrderBornology.atTop_le_cobounded [NoMaxOrder α] : .atTop ≤ Bornology.cobounded α := by
  intro s hs
  rw [← compl_compl s, ← isBounded_def, isBounded_iff_bddBelow_bddAbove] at hs
  obtain ⟨b, hb⟩ := hs.2
  obtain ⟨c, hbc⟩ := exists_gt b
  refine Filter.mem_of_superset (Filter.mem_atTop c) fun x hx ↦ ?_
  by_contra hx'
  exact hbc.not_ge <| hx.trans <| hb <| mem_compl hx'

-- TODO (khw): Generate this in the future with `to_dual`
-- See https://github.com/leanprover-community/mathlib4/pull/37738
/-
**IsOrderBornology.atBot_le_cobounded** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsOrderBornology.atBot_le_cobounded [NoMinOrder α] : .atBot <= Bornology.c
obounded α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsOrderBornology.atTop_le_cobounded`：IsOrderBornology.atTop_le_cobounded
 [NoMaxOrder α] : .atTop <= Bornology.cobounded α
· 使用定理 `OrderDual.noMaxOrder`：∀ {α : Type u_1} [inst : LT α] [NoMinOrder α], NoM
axOrder αᵒᵈ
-/
lemma IsOrderBornology.atBot_le_cobounded [NoMinOrder α] : .atBot ≤ Bornology.cobounded α :=
  atTop_le_cobounded (α := αᵒᵈ)

end Preorder

section LinearOrder

variable [LinearOrder α] [IsOrderBornology α]

/-
**IsOrderBornology.cobounded_le_atBot_sup_atTop** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsOrderBornology.cobounded_le_atBot_sup_atTop : cobounded α <= .atBot ⊔ .a
tTop
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nonempty.of_isOrderBornology`：Nonempty.of_isOrderBornology : Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.mem_sup`：mem_sup {f g : Filter α} {s : Set α} : s in f ⊔ g ↔ s in
 f ∧ s in g
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Filter.atTop_basis`：atTop_basis [Nonempty α] : (@atTop α _).HasBasis (fu
n _ => True) Ici
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用引理 `Filter.atBot_basis`：atBot_basis {α : Type*} [Preorder α] [IsCodirectedOr
der α] [Nonempty α] : (@atBot α _).HasBasis (fun _ => True) Iic
· 使用定理 `SemilatticeInf.instIsCodirectedOrder`：∀ {α : Type u_1} [inst : Semilatti
ceInf α], IsCodirectedOrder α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Bornology.isBounded_def`：isBounded_def {s : Set α} : IsBounded s ↔ sᶜ in
 cobounded α
· 使用引理 `isBounded_iff_bddBelow_bddAbove`：isBounded_iff_bddBelow_bddAbove : IsBou
nded s ↔ BddBelow s ∧ BddAbove s
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma IsOrderBornology.cobounded_le_atBot_sup_atTop : cobounded α ≤ .atBot ⊔ .atTop := by
  have := Nonempty.of_isOrderBornology α
  intro s
  rw [Filter.mem_sup, Filter.atTop_basis.mem_iff, Filter.atBot_basis.mem_iff,
    ← compl_compl s, ← isBounded_def, isBounded_iff_bddBelow_bddAbove, compl_compl s]
  intro ⟨⟨b, _, hb⟩, ⟨a, _, ha⟩⟩
  refine ⟨⟨b, fun x hx ↦ ?_⟩, ⟨a, fun x hx ↦ ?_⟩⟩ <;> by_contra! hx'
  · exact hx (hb hx'.le)
  · exact hx (ha hx'.le)

@[simp]
/-
**IsOrderBornology.cobounded_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsOrderBornology.cobounded_eq [NoMaxOrder α] [NoMinOrder α] : Bornology.co
bounded α = .atBot ⊔ .atTop
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用引理 `IsOrderBornology.cobounded_le_atBot_sup_atTop`：IsOrderBornology.cobounde
d_le_atBot_sup_atTop : cobounded α <= .atBot ⊔ .atTop
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用引理 `IsOrderBornology.atBot_le_cobounded`：IsOrderBornology.atBot_le_cobounded
 [NoMinOrder α] : .atBot <= Bornology.cobounded α
· 使用引理 `IsOrderBornology.atTop_le_cobounded`：IsOrderBornology.atTop_le_cobounded
 [NoMaxOrder α] : .atTop <= Bornology.cobounded α
-/
lemma IsOrderBornology.cobounded_eq [NoMaxOrder α] [NoMinOrder α] :
    Bornology.cobounded α = .atBot ⊔ .atTop :=
  cobounded_le_atBot_sup_atTop.antisymm <|
    sup_le IsOrderBornology.atBot_le_cobounded IsOrderBornology.atTop_le_cobounded
/-
**IsOrderBornology.cobounded_eq_atTop** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsOrderBornology.cobounded_eq_atTop [NoMaxOrder α] [OrderBot α] : Bornolog
y.cobounded α = .atTop
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用引理 `IsOrderBornology.atTop_le_cobounded`：IsOrderBornology.atTop_le_cobounded
 [NoMaxOrder α] : .atTop <= Bornology.cobounded α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Filter.atTop_basis`：atTop_basis [Nonempty α] : (@atTop α _).HasBasis (fu
n _ => True) Ici
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `bot_nonempty`：∀ (α : Type u_1) [Bot α], Nonempty α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Bornology.isBounded_def`：isBounded_def {s : Set α} : IsBounded s ↔ sᶜ in
 cobounded α
· 使用引理 `isBounded_iff_bddBelow_bddAbove`：isBounded_iff_bddBelow_bddAbove : IsBou
nded s ↔ BddBelow s ∧ BddAbove s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma IsOrderBornology.cobounded_eq_atTop [NoMaxOrder α] [OrderBot α] :
    Bornology.cobounded α = .atTop := by
  refine atTop_le_cobounded.antisymm' fun s ↦ ?_
  rw [Filter.atTop_basis.mem_iff,
    ← compl_compl s, ← isBounded_def, isBounded_iff_bddBelow_bddAbove, compl_compl s]
  refine fun ⟨b, _, hb⟩ ↦ ⟨⟨⊥, fun x hx ↦ by simp⟩, ⟨b, fun x hx ↦ ?_⟩⟩
  by_contra! hx'
  exact hx (hb hx'.le)

-- TODO (khw): Generate this in the future with `to_dual`
-- See https://github.com/leanprover-community/mathlib4/pull/37738
@[to_dual existing]
/-
**IsOrderBornology.cobounded_eq_atBot** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsOrderBornology.cobounded_eq_atBot [NoMinOrder α] [OrderTop α] : Bornolog
y.cobounded α = .atBot
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsOrderBornology.cobounded_eq_atTop`：IsOrderBornology.cobounded_eq_atTop
 [NoMaxOrder α] [OrderBot α] : Bornology.cobounded α = .atTop
· 使用定理 `OrderDual.noMaxOrder`：∀ {α : Type u_1} [inst : LT α] [NoMinOrder α], NoM
axOrder αᵒᵈ
-/
lemma IsOrderBornology.cobounded_eq_atBot [NoMinOrder α] [OrderTop α] :
    Bornology.cobounded α = .atBot := cobounded_eq_atTop (α := αᵒᵈ)

end LinearOrder

section ConditionallyCompleteLattice
variable [ConditionallyCompleteLattice α] [IsOrderBornology α] {s : Set α}

/-
**Bornology.IsBounded.subset_Icc_sInf_sSup** 是 Mathlib 中的一个定理，位于命名空间 `Bornology.
IsBounded`。
形式化陈述：∀ {α : Type u_1} [inst : Bornology α] [inst_1 : ConditionallyCompleteLatti
ce α] [IsOrderBornology α] {s : Set α},   Bornology.IsBounded s → s ⊆ Set.Icc (s
Inf s) (sSup s)
参数：sInf s；sSup s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_Icc_csInf_csSup`：subset_Icc_csInf_csSup (hb : BddBelow s) (ha : B
ddAbove s) : s subseteq Icc (sInf s) (sSup s)
· 使用定理 `Bornology.IsBounded.bddBelow`：∀ {α : Type u_1} {s : Set α} [inst : Borno
logy α] [inst_1 : Preorder α] [IsOrderBornology α],   Bornology.IsBounded s → Bd
dBelow s
· 使用定理 `Bornology.IsBounded.bddAbove`：∀ {α : Type u_1} {s : Set α} [inst : Borno
logy α] [inst_1 : Preorder α] [IsOrderBornology α],   Bornology.IsBounded s → Bd
dAbove s
-/
protected lemma Bornology.IsBounded.subset_Icc_sInf_sSup (hs : IsBounded s) :
    s ⊆ Icc (sInf s) (sSup s) := subset_Icc_csInf_csSup hs.bddBelow hs.bddAbove

end ConditionallyCompleteLattice

