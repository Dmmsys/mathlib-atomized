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
/--
Definition of `orderBornology` / `orderBornology` 的定义

English:
definition orderBornology
  signature: : Bornology α
  body: .ofBounded
  {s | BddBelow s ∧ BddAbove s}
  (by simp)
  (fun _ hs _ hst => ⟨hs.1.mono hst, hs.2.mono hst⟩)
  (fun _ hs _ ht => ⟨hs.1.union ht.1, hs.2.union ht.2⟩)
  (by simp)

中文:
定义 orderBornology
  签名: : Bornology α
  定义体: .ofBounded
  {s | BddBelow s ∧ BddAbove s}
  (by simp)
  (fun _ hs _ hst => ⟨hs.1.mono hst, hs.2.mono hst⟩)
  (fun _ hs _ ht => ⟨hs.1.union ht.1, hs.2.union ht.2⟩)
  (by simp)

Depends on / 依赖: ofBounded
-/
def orderBornology : Bornology α := .ofBounded
  {s | BddBelow s ∧ BddAbove s}
  (by simp)
  (fun _ hs _ hst => ⟨hs.1.mono hst, hs.2.mono hst⟩)
  (fun _ hs _ ht => ⟨hs.1.union ht.1, hs.2.union ht.2⟩)
  (by simp)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `orderBornology_isBounded` / 引理 `orderBornology_isBounded`

English:
lemma orderBornology_isBounded
  statement: orderBornology.IsBounded s ↔ BddBelow s ∧ BddAbove s
  proof: by
  simp [IsBounded, IsCobounded, -isCobounded_compl_iff]

中文:
引理 orderBornology_isBounded
  结论: orderBornology.IsBounded s ↔ BddBelow s ∧ BddAbove s
  证明: by
  simp [IsBounded, IsCobounded, -isCobounded_compl_iff]
-/
@[simp] lemma orderBornology_isBounded : orderBornology.IsBounded s ↔ BddBelow s ∧ BddAbove s := by
  simp [IsBounded, IsCobounded, -isCobounded_compl_iff]

end Lattice

variable [Bornology α]

variable (α) [Preorder α] in
/--
Definition of `IsOrderBornology` / `IsOrderBornology` 的定义

English:
class IsOrderBornology
  parameters: : Prop where
  axioms and operations (1):
    - isBounded_iff_bddBelow_bddAbove((s : Set α)) : IsBounded s ↔ BddBelow s ∧ BddAbove s

中文:
类 IsOrderBornology
  参数: : 命题 where
  公理与运算 (1 个):
    - isBounded_iff_bddBelow_bddAbove((s : Set α)) : IsBounded s ↔ BddBelow s ∧ BddAbove s
-/
class IsOrderBornology : Prop where
  protected isBounded_iff_bddBelow_bddAbove (s : Set α) : IsBounded s ↔ BddBelow s ∧ BddAbove s

/--
lemma `isOrderBornology_iff_eq_orderBornology` / 引理 `isOrderBornology_iff_eq_orderBornology`

English:
lemma isOrderBornology_iff_eq_orderBornology
  given: [Lattice α] [Nonempty α]
  proof: by
  refine ⟨fun h => ?_, fun h => ⟨fun s => by rw [h, orderBornology_isBounded]⟩⟩
  ext s
  exact isBounded_compl_iff.symm.trans (h.1 _)

中文:
引理 isOrderBornology_iff_eq_orderBornology
  条件: [Lattice α] [Nonempty α]
  证明: by
  refine ⟨fun h => ?_, fun h => ⟨fun s => by rw [h, orderBornology_isBounded]⟩⟩
  ext s
  exact isBounded_compl_iff.symm.trans (h.1 _)

Depends on / 依赖: isBounded_compl_iff, isBounded_compl_iff.symm.trans, orderBornology_isBounded
-/
lemma isOrderBornology_iff_eq_orderBornology [Lattice α] [Nonempty α] :
    IsOrderBornology α ↔ ‹Bornology α› = orderBornology := by
  refine ⟨fun h => ?_, fun h => ⟨fun s => by rw [h, orderBornology_isBounded]⟩⟩
  ext s
  exact isBounded_compl_iff.symm.trans (h.1 _)

section Preorder
variable [Preorder α] [IsOrderBornology α]

/--
lemma `isBounded_iff_bddBelow_bddAbove` / 引理 `isBounded_iff_bddBelow_bddAbove`

English:
lemma isBounded_iff_bddBelow_bddAbove
  statement: IsBounded s ↔ BddBelow s ∧ BddAbove s
  proof: IsOrderBornology.isBounded_iff_bddBelow_bddAbove _

中文:
引理 isBounded_iff_bddBelow_bddAbove
  结论: IsBounded s ↔ BddBelow s ∧ BddAbove s
  证明: IsOrderBornology.isBounded_iff_bddBelow_bddAbove _

Depends on / 依赖: IsOrderBornology, IsOrderBornology.isBounded_iff_bddBelow_bddAbove, isBounded_iff_bddBelow_bddAbove
-/
lemma isBounded_iff_bddBelow_bddAbove : IsBounded s ↔ BddBelow s ∧ BddAbove s :=
  IsOrderBornology.isBounded_iff_bddBelow_bddAbove _

/--
lemma `Bornology.IsBounded.bddBelow` / 引理 `Bornology.IsBounded.bddBelow`

English:
lemma Bornology.IsBounded.bddBelow
  given: (hs : IsBounded s)
  statement: BddBelow s
  proof: (isBounded_iff_bddBelow_bddAbove.1 hs).1

中文:
引理 Bornology.IsBounded.bddBelow
  条件: (hs : IsBounded s)
  结论: BddBelow s
  证明: (isBounded_iff_bddBelow_bddAbove.1 hs).1
-/
protected lemma Bornology.IsBounded.bddBelow (hs : IsBounded s) : BddBelow s :=
  (isBounded_iff_bddBelow_bddAbove.1 hs).1

/--
lemma `Bornology.IsBounded.bddAbove` / 引理 `Bornology.IsBounded.bddAbove`

English:
lemma Bornology.IsBounded.bddAbove
  given: (hs : IsBounded s)
  statement: BddAbove s
  proof: (isBounded_iff_bddBelow_bddAbove.1 hs).2

中文:
引理 Bornology.IsBounded.bddAbove
  条件: (hs : IsBounded s)
  结论: BddAbove s
  证明: (isBounded_iff_bddBelow_bddAbove.1 hs).2
-/
protected lemma Bornology.IsBounded.bddAbove (hs : IsBounded s) : BddAbove s :=
  (isBounded_iff_bddBelow_bddAbove.1 hs).2

/--
lemma `BddBelow.isBounded` / 引理 `BddBelow.isBounded`

English:
lemma BddBelow.isBounded
  given: (hs₀ : BddBelow s) (hs₁ : BddAbove s)
  statement: IsBounded s
  proof: isBounded_iff_bddBelow_bddAbove.2 ⟨hs₀, hs₁⟩

中文:
引理 BddBelow.isBounded
  条件: (hs₀ : BddBelow s) (hs₁ : BddAbove s)
  结论: IsBounded s
  证明: isBounded_iff_bddBelow_bddAbove.2 ⟨hs₀, hs₁⟩
-/
protected lemma BddBelow.isBounded (hs₀ : BddBelow s) (hs₁ : BddAbove s) : IsBounded s :=
  isBounded_iff_bddBelow_bddAbove.2 ⟨hs₀, hs₁⟩

/--
lemma `BddAbove.isBounded` / 引理 `BddAbove.isBounded`

English:
lemma BddAbove.isBounded
  given: (hs₀ : BddAbove s) (hs₁ : BddBelow s)
  statement: IsBounded s
  proof: isBounded_iff_bddBelow_bddAbove.2 ⟨hs₁, hs₀⟩

中文:
引理 BddAbove.isBounded
  条件: (hs₀ : BddAbove s) (hs₁ : BddBelow s)
  结论: IsBounded s
  证明: isBounded_iff_bddBelow_bddAbove.2 ⟨hs₁, hs₀⟩
-/
protected lemma BddAbove.isBounded (hs₀ : BddAbove s) (hs₁ : BddBelow s) : IsBounded s :=
  isBounded_iff_bddBelow_bddAbove.2 ⟨hs₁, hs₀⟩

/--
lemma `BddBelow.isBounded_inter` / 引理 `BddBelow.isBounded_inter`

English:
lemma BddBelow.isBounded_inter
  given: (hs : BddBelow s) (ht : BddAbove t)
  statement: IsBounded (s inter t)
  proof: (hs.mono inter_subset_left).isBounded ht.mono inter_subset_right

中文:
引理 BddBelow.isBounded_inter
  条件: (hs : BddBelow s) (ht : BddAbove t)
  结论: IsBounded (s inter t)
  证明: (hs.mono inter_subset_left).isBounded ht.mono inter_subset_right

Depends on / 依赖: hs.mono, ht.mono, inter_subset_left, inter_subset_right, isBounded
-/
lemma BddBelow.isBounded_inter (hs : BddBelow s) (ht : BddAbove t) : IsBounded (s inter t) :=
(hs.mono inter_subset_left).isBounded ht.mono inter_subset_right

/--
lemma `BddAbove.isBounded_inter` / 引理 `BddAbove.isBounded_inter`

English:
lemma BddAbove.isBounded_inter
  given: (hs : BddAbove s) (ht : BddBelow t)
  statement: IsBounded (s inter t)
  proof: (hs.mono inter_subset_left).isBounded ht.mono inter_subset_right

中文:
引理 BddAbove.isBounded_inter
  条件: (hs : BddAbove s) (ht : BddBelow t)
  结论: IsBounded (s inter t)
  证明: (hs.mono inter_subset_left).isBounded ht.mono inter_subset_right

Depends on / 依赖: hs.mono, ht.mono, inter_subset_left, inter_subset_right, isBounded
-/
lemma BddAbove.isBounded_inter (hs : BddAbove s) (ht : BddBelow t) : IsBounded (s inter t) :=
(hs.mono inter_subset_left).isBounded ht.mono inter_subset_right

/--
Instance `OrderDual.instIsOrderBornology` / 实例 `OrderDual.instIsOrderBornology`

English:
instance OrderDual.instIsOrderBornology
  signature: : IsOrderBornology αᵒᵈ where
  body: by
    rw [← isBounded_preimage_toDual]; rw [← bddBelow_preimage_toDual]; rw [← bddAbove_preimage_toDual]; rw [isBounded_iff_bddBelow_bddAbove]; rw [and_comm]

中文:
实例 OrderDual.instIsOrderBornology
  签名: : IsOrderBornology αᵒᵈ where
  定义体: by
    rw [← isBounded_preimage_toDual]; rw [← bddBelow_preimage_toDual]; rw [← bddAbove_preimage_toDual]; rw [isBounded_iff_bddBelow_bddAbove]; rw [and_comm]

Depends on / 依赖: and_comm, bddAbove_preimage_toDual, bddBelow_preimage_toDual, isBounded_iff_bddBelow_bddAbove, isBounded_preimage_toDual
-/
instance OrderDual.instIsOrderBornology : IsOrderBornology αᵒᵈ where
  isBounded_iff_bddBelow_bddAbove s := by
    rw [← isBounded_preimage_toDual]; rw [← bddBelow_preimage_toDual]; rw [← bddAbove_preimage_toDual]; rw [isBounded_iff_bddBelow_bddAbove]; rw [and_comm]

/--
Instance `Prod.instIsOrderBornology` / 实例 `Prod.instIsOrderBornology`

English:
instance Prod.instIsOrderBornology
  signature: {β : Type*} [Preorder β] [Bornology β] [IsOrderBornology β]
  body: by
    rw [← isBounded_image_fst_and_snd]; rw [bddBelow_prod]; rw [bddAbove_prod]; rw [and_and_and_comm]; rw [isBounded_iff_bddBelow_bddAbove]; rw [isBounded_iff_bddBelow_bddAbove]

中文:
实例 Prod.instIsOrderBornology
  签名: {β : 类型} [Preorder β] [Bornology β] [IsOrderBornology β]
  定义体: by
    rw [← isBounded_image_fst_and_snd]; rw [bddBelow_prod]; rw [bddAbove_prod]; rw [and_and_and_comm]; rw [isBounded_iff_bddBelow_bddAbove]; rw [isBounded_iff_bddBelow_bddAbove]

Depends on / 依赖: and_and_and_comm, bddAbove_prod, bddBelow_prod, isBounded_iff_bddBelow_bddAbove, isBounded_image_fst_and_snd
-/
instance Prod.instIsOrderBornology {β : Type*} [Preorder β] [Bornology β] [IsOrderBornology β] :
    IsOrderBornology (α × β) where
  isBounded_iff_bddBelow_bddAbove s := by
    rw [← isBounded_image_fst_and_snd]; rw [bddBelow_prod]; rw [bddAbove_prod]; rw [and_and_and_comm]; rw [isBounded_iff_bddBelow_bddAbove]; rw [isBounded_iff_bddBelow_bddAbove]

/--
Instance `Pi.instIsOrderBornology` / 实例 `Pi.instIsOrderBornology`

English:
instance Pi.instIsOrderBornology
  signature: {ι : Type*} {α : ι -> Type*} [forall i, Preorder (α i)]
  body: by
    simp_rw [← forall_isBounded_image_eval_iff, bddBelow_pi, bddAbove_pi, ← forall_and,
      isBounded_iff_bddBelow_bddAbove]

中文:
实例 Pi.instIsOrderBornology
  签名: {ι : 类型} {α : ι -> 类型} [对任意 i, Preorder (α i)]
  定义体: by
    simp_rw [← forall_isBounded_image_eval_iff, bddBelow_pi, bddAbove_pi, ← forall_and,
      isBounded_iff_bddBelow_bddAbove]

Depends on / 依赖: bddAbove_pi, bddBelow_pi, forall_and, forall_isBounded_image_eval_iff, isBounded_iff_bddBelow_bddAbove, simp_rw
-/
instance Pi.instIsOrderBornology {ι : Type*} {α : ι -> Type*} [forall i, Preorder (α i)]
    [forall i, Bornology (α i)] [forall i, IsOrderBornology (α i)] : IsOrderBornology (forall i, α i) where
  isBounded_iff_bddBelow_bddAbove s := by
    simp_rw [← forall_isBounded_image_eval_iff, bddBelow_pi, bddAbove_pi, ← forall_and,
      isBounded_iff_bddBelow_bddAbove]

variable (α) in
/--
lemma `Nonempty.of_isOrderBornology` / 引理 `Nonempty.of_isOrderBornology`

English:
lemma Nonempty.of_isOrderBornology
  statement: Nonempty α
  proof: Bornology.isBounded_empty.bddBelow.nonempty

中文:
引理 Nonempty.of_isOrderBornology
  结论: Nonempty α
  证明: Bornology.isBounded_empty.bddBelow.nonempty

Depends on / 依赖: Bornology, Bornology.isBounded_empty.bddBelow.nonempty, bddBelow, isBounded_empty, nonempty
-/
lemma Nonempty.of_isOrderBornology : Nonempty α := Bornology.isBounded_empty.bddBelow.nonempty

/--
Instance `IsOrderBornology.neBot_cobounded_of_noBotOrder` / 实例 `IsOrderBornology.neBot_cobounded_of_noBotOrder`

English:
instance IsOrderBornology.neBot_cobounded_of_noBotOrder
  signature: [NoBotOrder α]
  body: by
  simp [Filter.neBot_iff, cobounded_eq_bot_iff, ← isBounded_univ, isBounded_iff_bddBelow_bddAbove]

中文:
实例 IsOrderBornology.neBot_cobounded_of_noBotOrder
  签名: [NoBotOrder α]
  定义体: by
  simp [Filter.neBot_iff, cobounded_eq_bot_iff, ← isBounded_univ, isBounded_iff_bddBelow_bddAbove]

Depends on / 依赖: Filter, Filter.neBot_iff, cobounded_eq_bot_iff, isBounded_iff_bddBelow_bddAbove, isBounded_univ, neBot_iff
-/
instance IsOrderBornology.neBot_cobounded_of_noBotOrder [NoBotOrder α] : (cobounded α).NeBot := by
  simp [Filter.neBot_iff, cobounded_eq_bot_iff, ← isBounded_univ, isBounded_iff_bddBelow_bddAbove]

/--
Instance `IsOrderBornology.neBot_cobounded_of_noTopOrder` / 实例 `IsOrderBornology.neBot_cobounded_of_noTopOrder`

English:
instance IsOrderBornology.neBot_cobounded_of_noTopOrder
  signature: [NoTopOrder α]
  body: neBot_cobounded_of_noBotOrder (α := αᵒᵈ)

中文:
实例 IsOrderBornology.neBot_cobounded_of_noTopOrder
  签名: [NoTopOrder α]
  定义体: neBot_cobounded_of_noBotOrder (α := αᵒᵈ)

Depends on / 依赖: neBot_cobounded_of_noBotOrder
-/
instance IsOrderBornology.neBot_cobounded_of_noTopOrder [NoTopOrder α] : (cobounded α).NeBot :=
  neBot_cobounded_of_noBotOrder (α := αᵒᵈ)

/--
lemma `IsOrderBornology.atTop_le_cobounded` / 引理 `IsOrderBornology.atTop_le_cobounded`

English:
lemma IsOrderBornology.atTop_le_cobounded
  given: [NoMaxOrder α]
  statement: .atTop <= Bornology.cobounded α
  proof: by
  intro s hs
  rw [← compl_compl s]; rw [← isBounded_def]; rw [isBounded_iff_bddBelow_bddAbove] at hs
  obtain ⟨b, hb⟩ := hs.2
  obtain ⟨c, hbc⟩ := exists_gt b
  refine Filter.mem_of_superset (Filter.mem_atTop c) fun x hx => ?_
  by_contra hx'
exact hbc.not_ge hx.trans hb mem_compl hx'

中文:
引理 IsOrderBornology.atTop_le_cobounded
  条件: [NoMaxOrder α]
  结论: .atTop <= Bornology.cobounded α
  证明: by
  intro s hs
  rw [← compl_compl s]; rw [← isBounded_def]; rw [isBounded_iff_bddBelow_bddAbove] at hs
  obtain ⟨b, hb⟩ := hs.2
  obtain ⟨c, hbc⟩ := exists_gt b
  refine Filter.mem_of_superset (Filter.mem_atTop c) fun x hx => ?_
  by_contra hx'
exact hbc.not_ge hx.trans hb mem_compl hx'

Depends on / 依赖: Filter, Filter.mem_atTop, Filter.mem_of_superset, compl_compl, exists_gt, hbc.not_ge, hx.trans, isBounded_def, isBounded_iff_bddBelow_bddAbove, mem_atTop, mem_compl, mem_of_superset, not_ge
-/
lemma IsOrderBornology.atTop_le_cobounded [NoMaxOrder α] : .atTop <= Bornology.cobounded α := by
  intro s hs
  rw [← compl_compl s]; rw [← isBounded_def]; rw [isBounded_iff_bddBelow_bddAbove] at hs
  obtain ⟨b, hb⟩ := hs.2
  obtain ⟨c, hbc⟩ := exists_gt b
  refine Filter.mem_of_superset (Filter.mem_atTop c) fun x hx => ?_
  by_contra hx'
exact hbc.not_ge hx.trans hb mem_compl hx'

-- TODO (khw): Generate this in the future with `to_dual`
-- See https://github.com/leanprover-community/mathlib4/pull/37738
/--
lemma `IsOrderBornology.atBot_le_cobounded` / 引理 `IsOrderBornology.atBot_le_cobounded`

English:
lemma IsOrderBornology.atBot_le_cobounded
  given: [NoMinOrder α]
  statement: .atBot <= Bornology.cobounded α
  proof: atTop_le_cobounded (α := αᵒᵈ)

中文:
引理 IsOrderBornology.atBot_le_cobounded
  条件: [NoMinOrder α]
  结论: .atBot <= Bornology.cobounded α
  证明: atTop_le_cobounded (α := αᵒᵈ)

Depends on / 依赖: atTop_le_cobounded
-/
lemma IsOrderBornology.atBot_le_cobounded [NoMinOrder α] : .atBot <= Bornology.cobounded α :=
  atTop_le_cobounded (α := αᵒᵈ)

end Preorder

section LinearOrder

variable [LinearOrder α] [IsOrderBornology α]

/--
lemma `IsOrderBornology.cobounded_le_atBot_sup_atTop` / 引理 `IsOrderBornology.cobounded_le_atBot_sup_atTop`

English:
lemma IsOrderBornology.cobounded_le_atBot_sup_atTop
  statement: cobounded α <= .atBot ⊔ .atTop
  proof: by
  have := Nonempty.of_isOrderBornology α
  intro s
  rw [Filter.mem_sup]; rw [Filter.atTop_basis.mem_iff]; rw [Filter.atBot_basis.mem_iff]; rw [← compl_compl s]; rw [← isBounded_def]; rw [isBounded_iff_bddBelow_bddAbove]; rw [compl_compl s]
  intro ⟨⟨b, _, hb⟩, ⟨a, _, ha⟩⟩
  refine ⟨⟨b, fun x hx 

中文:
引理 IsOrderBornology.cobounded_le_atBot_sup_atTop
  结论: cobounded α <= .atBot ⊔ .atTop
  证明: by
  have := Nonempty.of_isOrderBornology α
  intro s
  rw [Filter.mem_sup]; rw [Filter.atTop_basis.mem_iff]; rw [Filter.atBot_basis.mem_iff]; rw [← compl_compl s]; rw [← isBounded_def]; rw [isBounded_iff_bddBelow_bddAbove]; rw [compl_compl s]
  intro ⟨⟨b, _, hb⟩, ⟨a, _, ha⟩⟩
  refine ⟨⟨b, fun x hx 

Depends on / 依赖: Filter, Filter.atBot_basis.mem_iff, Filter.atTop_basis.mem_iff, Filter.mem_sup, Nonempty, Nonempty.of_isOrderBornology, atBot_basis, atTop_basis, compl_compl, isBounded_def, isBounded_iff_bddBelow_bddAbove, mem_iff, mem_sup, of_isOrderBornology
-/
lemma IsOrderBornology.cobounded_le_atBot_sup_atTop : cobounded α <= .atBot ⊔ .atTop := by
  have := Nonempty.of_isOrderBornology α
  intro s
  rw [Filter.mem_sup]; rw [Filter.atTop_basis.mem_iff]; rw [Filter.atBot_basis.mem_iff]; rw [← compl_compl s]; rw [← isBounded_def]; rw [isBounded_iff_bddBelow_bddAbove]; rw [compl_compl s]
  intro ⟨⟨b, _, hb⟩, ⟨a, _, ha⟩⟩
  refine ⟨⟨b, fun x hx => ?_⟩, ⟨a, fun x hx => ?_⟩⟩ <;> by_contra! hx'
  · exact hx (hb hx'.le)
  · exact hx (ha hx'.le)

@[simp]
/--
lemma `IsOrderBornology.cobounded_eq` / 引理 `IsOrderBornology.cobounded_eq`

English:
lemma IsOrderBornology.cobounded_eq
  given: [NoMaxOrder α] [NoMinOrder α]
  proof: cobounded_le_atBot_sup_atTop.antisymm
    sup_le IsOrderBornology.atBot_le_cobounded IsOrderBornology.atTop_le_cobounded

中文:
引理 IsOrderBornology.cobounded_eq
  条件: [NoMaxOrder α] [NoMinOrder α]
  证明: cobounded_le_atBot_sup_atTop.antisymm
    sup_le IsOrderBornology.atBot_le_cobounded IsOrderBornology.atTop_le_cobounded

Depends on / 依赖: IsOrderBornology, IsOrderBornology.atBot_le_cobounded, IsOrderBornology.atTop_le_cobounded, antisymm, atBot_le_cobounded, atTop_le_cobounded, cobounded_le_atBot_sup_atTop, cobounded_le_atBot_sup_atTop.antisymm, sup_le
-/
lemma IsOrderBornology.cobounded_eq [NoMaxOrder α] [NoMinOrder α] :
    Bornology.cobounded α = .atBot ⊔ .atTop :=
cobounded_le_atBot_sup_atTop.antisymm
    sup_le IsOrderBornology.atBot_le_cobounded IsOrderBornology.atTop_le_cobounded

/--
lemma `IsOrderBornology.cobounded_eq_atTop` / 引理 `IsOrderBornology.cobounded_eq_atTop`

English:
lemma IsOrderBornology.cobounded_eq_atTop
  given: [NoMaxOrder α] [OrderBot α]
  proof: by
  refine atTop_le_cobounded.antisymm' fun s => ?_
  rw [Filter.atTop_basis.mem_iff]; rw [← compl_compl s]; rw [← isBounded_def]; rw [isBounded_iff_bddBelow_bddAbove]; rw [compl_compl s]
  refine fun ⟨b, _, hb⟩ => ⟨⟨⊥, fun x hx => by simp⟩, ⟨b, fun x hx => ?_⟩⟩
  by_contra! hx'
  exact hx (hb hx'.

中文:
引理 IsOrderBornology.cobounded_eq_atTop
  条件: [NoMaxOrder α] [OrderBot α]
  证明: by
  refine atTop_le_cobounded.antisymm' fun s => ?_
  rw [Filter.atTop_basis.mem_iff]; rw [← compl_compl s]; rw [← isBounded_def]; rw [isBounded_iff_bddBelow_bddAbove]; rw [compl_compl s]
  refine fun ⟨b, _, hb⟩ => ⟨⟨⊥, fun x hx => by simp⟩, ⟨b, fun x hx => ?_⟩⟩
  by_contra! hx'
  exact hx (hb hx'.

Depends on / 依赖: Filter, Filter.atTop_basis.mem_iff, antisymm, atTop_basis, atTop_le_cobounded, atTop_le_cobounded.antisymm, compl_compl, isBounded_def, isBounded_iff_bddBelow_bddAbove, mem_iff
-/
lemma IsOrderBornology.cobounded_eq_atTop [NoMaxOrder α] [OrderBot α] :
    Bornology.cobounded α = .atTop := by
  refine atTop_le_cobounded.antisymm' fun s => ?_
  rw [Filter.atTop_basis.mem_iff]; rw [← compl_compl s]; rw [← isBounded_def]; rw [isBounded_iff_bddBelow_bddAbove]; rw [compl_compl s]
  refine fun ⟨b, _, hb⟩ => ⟨⟨⊥, fun x hx => by simp⟩, ⟨b, fun x hx => ?_⟩⟩
  by_contra! hx'
  exact hx (hb hx'.le)

-- TODO (khw): Generate this in the future with `to_dual`
-- See https://github.com/leanprover-community/mathlib4/pull/37738
@[to_dual existing]
/--
lemma `IsOrderBornology.cobounded_eq_atBot` / 引理 `IsOrderBornology.cobounded_eq_atBot`

English:
lemma IsOrderBornology.cobounded_eq_atBot
  given: [NoMinOrder α] [OrderTop α]
  proof: cobounded_eq_atTop (α := αᵒᵈ)

中文:
引理 IsOrderBornology.cobounded_eq_atBot
  条件: [NoMinOrder α] [OrderTop α]
  证明: cobounded_eq_atTop (α := αᵒᵈ)

Depends on / 依赖: cobounded_eq_atTop
-/
lemma IsOrderBornology.cobounded_eq_atBot [NoMinOrder α] [OrderTop α] :
    Bornology.cobounded α = .atBot := cobounded_eq_atTop (α := αᵒᵈ)

end LinearOrder

section ConditionallyCompleteLattice
variable [ConditionallyCompleteLattice α] [IsOrderBornology α] {s : Set α}

/--
lemma `Bornology.IsBounded.subset_Icc_sInf_sSup` / 引理 `Bornology.IsBounded.subset_Icc_sInf_sSup`

English:
lemma Bornology.IsBounded.subset_Icc_sInf_sSup
  given: (hs : IsBounded s)
  proof: subset_Icc_csInf_csSup hs.bddBelow hs.bddAbove

中文:
引理 Bornology.IsBounded.subset_Icc_sInf_sSup
  条件: (hs : IsBounded s)
  证明: subset_Icc_csInf_csSup hs.bddBelow hs.bddAbove
-/
protected lemma Bornology.IsBounded.subset_Icc_sInf_sSup (hs : IsBounded s) :
    s subseteq Icc (sInf s) (sSup s) := subset_Icc_csInf_csSup hs.bddBelow hs.bddAbove

end ConditionallyCompleteLattice
