/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.SetTheory.Ordinal.Family

/-!
# Rank in a well-founded relation

For `r` a well-founded relation, `IsWellFounded.rank r a` is recursively defined as the least
ordinal greater than the ranks of all elements below `a`.
-/

@[expose] public section

universe u

variable {α : Type u} {a b : α}

/-! ### Rank of an accessible value -/

namespace Acc

variable {r : α -> α -> Prop}

/--
Definition of `rank` / `rank` 的定义

English:
definition rank
  signature: (h : Acc r a)
  body: Acc.recOn h fun a _h ih => ⨆ b : { b // r b a }, Order.succ (ih b b.2)

中文:
定义 rank
  签名: (h : Acc r a)
  定义体: Acc.recOn h fun a _h ih => ⨆ b : { b // r b a }, Order.succ (ih b b.2)

Depends on / 依赖: Acc.recOn, Order.succ
-/
noncomputable def rank (h : Acc r a) : Ordinal.{u} :=
  Acc.recOn h fun a _h ih => ⨆ b : { b // r b a }, Order.succ (ih b b.2)

/--
theorem `rank_eq` / 定理 `rank_eq`

English:
theorem rank_eq
  given: (h : Acc r a)
  proof: by
  change (Acc.intro a fun _ => h.inv).rank = _
  rfl

中文:
定理 rank_eq
  条件: (h : Acc r a)
  证明: by
  change (Acc.intro a fun _ => h.inv).rank = _
  rfl

Depends on / 依赖: Acc.intro, h.inv
-/
theorem rank_eq (h : Acc r a) :
    h.rank = ⨆ b : { b // r b a }, Order.succ (h.inv b.2).rank := by
  change (Acc.intro a fun _ => h.inv).rank = _
  rfl

/--
theorem `rank_lt_of_rel` / 定理 `rank_lt_of_rel`

English:
theorem rank_lt_of_rel
  given: (hb : Acc r b) (h : r a b)
  statement: (hb.inv h).rank < hb.rank
  proof: (Order.lt_succ _).trans_le by
    rw [hb.rank_eq]
    exact Ordinal.le_iSup _ (⟨a, h⟩ : {a // r a b})

中文:
定理 rank_lt_of_rel
  条件: (hb : Acc r b) (h : r a b)
  结论: (hb.inv h).rank < hb.rank
  证明: (Order.lt_succ _).trans_le by
    rw [hb.rank_eq]
    exact Ordinal.le_iSup _ (⟨a, h⟩ : {a // r a b})

Depends on / 依赖: Order.lt_succ, Ordinal, Ordinal.le_iSup, hb.rank_eq, le_iSup, lt_succ, rank_eq, trans_le
-/
theorem rank_lt_of_rel (hb : Acc r b) (h : r a b) : (hb.inv h).rank < hb.rank :=
(Order.lt_succ _).trans_le by
    rw [hb.rank_eq]
    exact Ordinal.le_iSup _ (⟨a, h⟩ : {a // r a b})

/--
theorem `mem_range_rank_of_le` / 定理 `mem_range_rank_of_le`

English:
theorem mem_range_rank_of_le
  given: {o : Ordinal} (ha : Acc r a) (ho : o <= ha.rank)
  proof: by
  obtain rfl | ho := ho.eq_or_lt
  · exact ⟨a, ha, rfl⟩
  · revert ho
    refine ha.recOn fun a ha IH ho => ?_
    rw [rank_eq]; rw [Ordinal.lt_iSup_iff] at ho
    obtain ⟨⟨b, hb⟩, ho⟩ := ho
    rw [Order.lt_succ_iff] at ho
    obtain rfl | ho := ho.eq_or_lt
    exacts [⟨b, ha b hb, rfl⟩, IH _ hb

中文:
定理 mem_range_rank_of_le
  条件: {o : 序数} (ha : Acc r a) (ho : o <= ha.rank)
  证明: by
  obtain rfl | ho := ho.eq_or_lt
  · exact ⟨a, ha, rfl⟩
  · revert ho
    refine ha.recOn fun a ha IH ho => ?_
    rw [rank_eq]; rw [Ordinal.lt_iSup_iff] at ho
    obtain ⟨⟨b, hb⟩, ho⟩ := ho
    rw [Order.lt_succ_iff] at ho
    obtain rfl | ho := ho.eq_or_lt
    exacts [⟨b, ha b hb, rfl⟩, IH _ hb

Depends on / 依赖: Order.lt_succ_iff, Ordinal, Ordinal.lt_iSup_iff, eq_or_lt, exacts, ha.recOn, ho.eq_or_lt, lt_iSup_iff, lt_succ_iff, rank_eq, revert
-/
theorem mem_range_rank_of_le {o : Ordinal} (ha : Acc r a) (ho : o <= ha.rank) :
    exists (b : α) (hb : Acc r b), hb.rank = o := by
  obtain rfl | ho := ho.eq_or_lt
  · exact ⟨a, ha, rfl⟩
  · revert ho
    refine ha.recOn fun a ha IH ho => ?_
    rw [rank_eq]; rw [Ordinal.lt_iSup_iff] at ho
    obtain ⟨⟨b, hb⟩, ho⟩ := ho
    rw [Order.lt_succ_iff] at ho
    obtain rfl | ho := ho.eq_or_lt
    exacts [⟨b, ha b hb, rfl⟩, IH _ hb ho]

end Acc

/-! ### Rank in a well-founded relation -/

namespace IsWellFounded

variable (r : α -> α -> Prop) [hwf : IsWellFounded α r]

/--
Definition of `rank` / `rank` 的定义

English:
definition rank
  signature: (a : α)
  body: (hwf.apply r a).rank

中文:
定义 rank
  签名: (a : α)
  定义体: (hwf.apply r a).rank

Depends on / 依赖: hwf.apply
-/
noncomputable def rank (a : α) : Ordinal.{u} :=
  (hwf.apply r a).rank

/--
theorem `rank_eq` / 定理 `rank_eq`

English:
theorem rank_eq
  given: (a : α)
  statement: rank r a = ⨆ b : { b // r b a }, Order.succ (rank r b)
  proof: (hwf.apply r a).rank_eq

中文:
定理 rank_eq
  条件: (a : α)
  结论: rank r a = ⨆ b : { b // r b a }, Order.succ (rank r b)
  证明: (hwf.apply r a).rank_eq

Depends on / 依赖: hwf.apply, rank_eq
-/
theorem rank_eq (a : α) : rank r a = ⨆ b : { b // r b a }, Order.succ (rank r b) :=
  (hwf.apply r a).rank_eq

variable {r : α -> α -> Prop} [hwf : IsWellFounded α r]

/--
theorem `rank_lt_of_rel` / 定理 `rank_lt_of_rel`

English:
theorem rank_lt_of_rel
  given: (h : r a b)
  statement: rank r a < rank r b
  proof: Acc.rank_lt_of_rel _ h

中文:
定理 rank_lt_of_rel
  条件: (h : r a b)
  结论: rank r a < rank r b
  证明: Acc.rank_lt_of_rel _ h

Depends on / 依赖: Acc.rank_lt_of_rel, isCompact_closedBall, isCompact_iff_compactSpace, isCompact_iff_compactSpace.mp, rank_lt_of_rel
-/
theorem rank_lt_of_rel (h : r a b) : rank r a < rank r b :=
  Acc.rank_lt_of_rel _ h

/--
theorem `mem_range_rank_of_le` / 定理 `mem_range_rank_of_le`

English:
theorem mem_range_rank_of_le
  given: {o : Ordinal} (h : o <= rank r a)
  statement: o in Set.range (rank r)
  proof: by
  obtain ⟨b, hb, rfl⟩ := Acc.mem_range_rank_of_le (hwf.apply r a) h
  exact ⟨b, rfl⟩

中文:
定理 mem_range_rank_of_le
  条件: {o : 序数} (h : o <= rank r a)
  结论: o in 集合.range (rank r)
  证明: by
  obtain ⟨b, hb, rfl⟩ := Acc.mem_range_rank_of_le (hwf.apply r a) h
  exact ⟨b, rfl⟩

Depends on / 依赖: Acc.mem_range_rank_of_le, hwf.apply, mem_range_rank_of_le
-/
theorem mem_range_rank_of_le {o : Ordinal} (h : o <= rank r a) : o in Set.range (rank r) := by
  obtain ⟨b, hb, rfl⟩ := Acc.mem_range_rank_of_le (hwf.apply r a) h
  exact ⟨b, rfl⟩

end IsWellFounded

/--
theorem `WellFoundedLT.rank_strictMono` / 定理 `WellFoundedLT.rank_strictMono`

English:
theorem WellFoundedLT.rank_strictMono
  given: [Preorder α] [WellFoundedLT α]
  proof: fun _ _ => IsWellFounded.rank_lt_of_rel

中文:
定理 WellFoundedLT.rank_strictMono
  条件: [预序 α] [WellFoundedLT α]
  证明: fun _ _ => IsWellFounded.rank_lt_of_rel

Depends on / 依赖: ProperSpace, secondCountable_of_proper
-/
theorem WellFoundedLT.rank_strictMono [Preorder α] [WellFoundedLT α] :
    StrictMono (IsWellFounded.rank (α := α) (· < ·)) :=
  fun _ _ => IsWellFounded.rank_lt_of_rel

/--
theorem `WellFoundedGT.rank_strictAnti` / 定理 `WellFoundedGT.rank_strictAnti`

English:
theorem WellFoundedGT.rank_strictAnti
  given: [Preorder α] [WellFoundedGT α]
  proof: fun _ _ a => IsWellFounded.rank_lt_of_rel a

@[simp]

中文:
定理 WellFoundedGT.rank_strictAnti
  条件: [预序 α] [WellFoundedGT α]
  证明: fun _ _ a => IsWellFounded.rank_lt_of_rel a

@[simp]
-/
theorem WellFoundedGT.rank_strictAnti [Preorder α] [WellFoundedGT α] :
    StrictAnti (IsWellFounded.rank (α := α) (· > ·)) :=
  fun _ _ a => IsWellFounded.rank_lt_of_rel a

@[simp]
/--
theorem `IsWellFounded.rank_eq_typein` / 定理 `IsWellFounded.rank_eq_typein`

English:
theorem IsWellFounded.rank_eq_typein
  given: (r) [IsWellOrder α r]
  statement: rank r = Ordinal.typein r
  proof: by
  classical
  let := linearOrderOfSTO r
  ext a
  exact InitialSeg.eq (⟨(OrderEmbedding.ofStrictMono _ WellFoundedLT.rank_strictMono).ltEmbedding,
    fun a b h => mem_range_rank_of_le h.le⟩) (Ordinal.typein r) a

中文:
定理 是良基.rank_eq_typein
  条件: (r) [是良序 α r]
  结论: rank r = 序数.typein r
  证明: by
  classical
  let := linearOrderOfSTO r
  ext a
  exact InitialSeg.eq (⟨(OrderEmbedding.ofStrictMono _ WellFoundedLT.rank_strictMono).ltEmbedding,
    fun a b h => mem_range_rank_of_le h.le⟩) (Ordinal.typein r) a

Depends on / 依赖: InitialSeg, InitialSeg.eq, OrderEmbedding, OrderEmbedding.ofStrictMono, Ordinal, Ordinal.typein, WellFoundedLT, WellFoundedLT.rank_strictMono, classical, h.le, linearOrderOfSTO, ltEmbedding, mem_range_rank_of_le, ofStrictMono, rank_strictMono, typein
-/
theorem IsWellFounded.rank_eq_typein (r) [IsWellOrder α r] : rank r = Ordinal.typein r := by
  classical
  let := linearOrderOfSTO r
  ext a
  exact InitialSeg.eq (⟨(OrderEmbedding.ofStrictMono _ WellFoundedLT.rank_strictMono).ltEmbedding,
    fun a b h => mem_range_rank_of_le h.le⟩) (Ordinal.typein r) a
