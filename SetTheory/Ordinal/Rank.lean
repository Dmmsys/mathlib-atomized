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

variable {r : α → α → Prop}

/-- The rank of an element `a` accessible under a relation `r` is defined recursively as the
smallest ordinal greater than the ranks of all elements below it (i.e. elements `b` such that
`r b a`). -/
/-
**Acc.rank** 是 Mathlib 中的一个定义，位于命名空间 `Acc`。
形式化陈述：rank (h : Acc r a) : Ordinal.{u}
参数：h : Acc r a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The rank of an element `a` accessible under a relation `r` is defined recursivel
y as the
smallest ordinal greater than the ranks of all elements below it (i.e. elements 
`b` such that
`r b a`).
-/
noncomputable def rank (h : Acc r a) : Ordinal.{u} :=
  Acc.recOn h fun a _h ih => ⨆ b : { b // r b a }, Order.succ (ih b b.2)
/-
**Acc.rank_eq** 是 Mathlib 中的一个定理，位于命名空间 `Acc`。
形式化陈述：rank_eq (h : Acc r a) : h.rank = ⨆ b : { b // r b a }, Order.succ (h.inv b
.2).rank
参数：h : Acc r a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Acc.inv`：∀ {α : Sort u} {r : α → α → Prop} {x y : α}, Acc r x → r y x → 
Acc r y
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem rank_eq (h : Acc r a) :
    h.rank = ⨆ b : { b // r b a }, Order.succ (h.inv b.2).rank := by
  change (Acc.intro a fun _ => h.inv).rank = _
  rfl

/-- if `r a b` then the rank of `a` is less than the rank of `b`. -/
/-
**Acc.rank_lt_of_rel** 是 Mathlib 中的一个定理，位于命名空间 `Acc`。
形式化陈述：rank_lt_of_rel (hb : Acc r b) (h : r a b) : (hb.inv h).rank < hb.rank
参数：hb : Acc r b；h : r a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Acc.inv`：∀ {α : Sort u} {r : α → α → Prop} {x y : α}, Acc r x → r y x → 
Acc r y
· 使用定理 `Order.lt_succ`：lt_succ (a : α) : a < succ a
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Acc.rank_eq`：rank_eq (h : Acc r a) : h.rank = ⨆ b : { b // r b a }, Orde
r.succ (h.inv b.2).rank
· 使用定理 `Ordinal.le_iSup`：∀ {ι : Type u_3} (f : ι → Ordinal.{u}) [Small.{u, u_3} 
ι] (i : ι), f i ≤ ⨆ i, f i
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α

--- 原说明 ---
if `r a b` then the rank of `a` is less than the rank of `b`.
-/
theorem rank_lt_of_rel (hb : Acc r b) (h : r a b) : (hb.inv h).rank < hb.rank :=
  (Order.lt_succ _).trans_le <| by
    rw [hb.rank_eq]
    exact Ordinal.le_iSup _ (⟨a, h⟩ : {a // r a b})
/-
**Acc.mem_range_rank_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Acc`。
形式化陈述：mem_range_rank_of_le {o : Ordinal} (ha : Acc r a) (ho : o <= ha.rank) : ex
ists (b : α) (hb : Acc r b), hb.rank = o
参数：ha : Acc r a；ho : o <= ha.rank。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Acc.inv`：∀ {α : Sort u} {r : α → α → Prop} {x y : α}, Acc r x → r y x → 
Acc r y
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.lt_iSup_iff`：∀ {ι : Type u_3} {f : ι → Ordinal.{u}} {a : Ordinal
.{u}} [Small.{u, u_3} ι], a < ⨆ i, f i ↔ ∃ i, a < f i
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Acc.rank_eq`：rank_eq (h : Acc r a) : h.rank = ⨆ b : { b // r b a }, Orde
r.succ (h.inv b.2).rank
· 使用定理 `Order.lt_succ_iff`：lt_succ_iff : a < succ b ↔ a <= b
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
-/
theorem mem_range_rank_of_le {o : Ordinal} (ha : Acc r a) (ho : o ≤ ha.rank) :
    ∃ (b : α) (hb : Acc r b), hb.rank = o := by
  obtain rfl | ho := ho.eq_or_lt
  · exact ⟨a, ha, rfl⟩
  · revert ho
    refine ha.recOn fun a ha IH ho ↦ ?_
    rw [rank_eq, Ordinal.lt_iSup_iff] at ho
    obtain ⟨⟨b, hb⟩, ho⟩ := ho
    rw [Order.lt_succ_iff] at ho
    obtain rfl | ho := ho.eq_or_lt
    exacts [⟨b, ha b hb, rfl⟩, IH _ hb ho]

end Acc

/-! ### Rank in a well-founded relation -/

namespace IsWellFounded

variable (r : α → α → Prop) [hwf : IsWellFounded α r]

/-- The rank of an element `a` under a well-founded relation `r` is defined recursively as the
smallest ordinal greater than the ranks of all elements below it (i.e. elements `b` such that
`r b a`). -/
/-
**IsWellFounded.rank** 是 Mathlib 中的一个定义，位于命名空间 `IsWellFounded`。
形式化陈述：rank (a : α) : Ordinal.{u}
参数：a : α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsWellFounded.apply`：apply : forall a, Acc r a

--- 原说明 ---
The rank of an element `a` under a well-founded relation `r` is defined recursiv
ely as the
smallest ordinal greater than the ranks of all elements below it (i.e. elements 
`b` such that
`r b a`).
-/
noncomputable def rank (a : α) : Ordinal.{u} :=
  (hwf.apply r a).rank
/-
**IsWellFounded.rank_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsWellFounded`。
形式化陈述：rank_eq (a : α) : rank r a = ⨆ b : { b // r b a }, Order.succ (rank r b)
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Acc.rank_eq`：rank_eq (h : Acc r a) : h.rank = ⨆ b : { b // r b a }, Orde
r.succ (h.inv b.2).rank
· 使用定理 `IsWellFounded.apply`：apply : forall a, Acc r a
-/
theorem rank_eq (a : α) : rank r a = ⨆ b : { b // r b a }, Order.succ (rank r b) :=
  (hwf.apply r a).rank_eq

variable {r : α → α → Prop} [hwf : IsWellFounded α r]
/-
**IsWellFounded.rank_lt_of_rel** 是 Mathlib 中的一个定理，位于命名空间 `IsWellFounded`。
形式化陈述：rank_lt_of_rel (h : r a b) : rank r a < rank r b
参数：h : r a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Acc.rank_lt_of_rel`：rank_lt_of_rel (hb : Acc r b) (h : r a b) : (hb.inv 
h).rank < hb.rank
· 使用定理 `IsWellFounded.apply`：apply : forall a, Acc r a
-/
theorem rank_lt_of_rel (h : r a b) : rank r a < rank r b :=
  Acc.rank_lt_of_rel _ h
/-
**IsWellFounded.mem_range_rank_of_le** 是 Mathlib 中的一个定理，位于命名空间 `IsWellFounded`。
形式化陈述：mem_range_rank_of_le {o : Ordinal} (h : o <= rank r a) : o in Set.range (r
ank r)
参数：h : o <= rank r a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Acc.mem_range_rank_of_le`：mem_range_rank_of_le {o : Ordinal} (ha : Acc r
 a) (ho : o <= ha.rank) : exists (b : α) (hb : Acc r b), hb.rank = o
· 使用定理 `IsWellFounded.apply`：apply : forall a, Acc r a
-/
theorem mem_range_rank_of_le {o : Ordinal} (h : o ≤ rank r a) : o ∈ Set.range (rank r) := by
  obtain ⟨b, hb, rfl⟩ := Acc.mem_range_rank_of_le (hwf.apply r a) h
  exact ⟨b, rfl⟩

end IsWellFounded

/-
**WellFoundedLT.rank_strictMono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WellFoundedLT.rank_strictMono [Preorder α] [WellFoundedLT α] : StrictMono 
(IsWellFounded.rank (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsWellFounded.rank_lt_of_rel`：rank_lt_of_rel (h : r a b) : rank r a < ra
nk r b
-/
theorem WellFoundedLT.rank_strictMono [Preorder α] [WellFoundedLT α] :
    StrictMono (IsWellFounded.rank (α := α) (· < ·)) :=
  fun _ _ => IsWellFounded.rank_lt_of_rel
/-
**WellFoundedGT.rank_strictAnti** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WellFoundedGT.rank_strictAnti [Preorder α] [WellFoundedGT α] : StrictAnti 
(IsWellFounded.rank (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsWellFounded.rank_lt_of_rel`：rank_lt_of_rel (h : r a b) : rank r a < ra
nk r b
-/
theorem WellFoundedGT.rank_strictAnti [Preorder α] [WellFoundedGT α] :
    StrictAnti (IsWellFounded.rank (α := α) (· > ·)) :=
  fun _ _ a => IsWellFounded.rank_lt_of_rel a

@[simp]
/-
**IsWellFounded.rank_eq_typein** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsWellFounded.rank_eq_typein (r) [IsWellOrder α r] : rank r = Ordinal.type
in r
参数：r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsStrictTotalOrderOfIsWellOrder`：∀ {α : Type u_1} (r : α → α → Prop)
 [IsWellOrder α r], IsStrictTotalOrder α r
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r
· 使用定理 `InitialSeg.eq`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β
 → β → Prop} [IsWellOrder β s] (f g : InitialSeg r s) (a : α),   f a = g a
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `WellFoundedLT.rank_strictMono`：WellFoundedLT.rank_strictMono [Preorder α
] [WellFoundedLT α] : StrictMono (IsWellFounded.rank (α
· 使用定理 `IsWellFounded.mem_range_rank_of_le`：mem_range_rank_of_le {o : Ordinal} (
h : o <= rank r a) : o in Set.range (rank r)
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `PrincipalSeg.mem_range_of_rel`：mem_range_of_rel [IsTrans β s] (f : r ≺i 
s) {a : α} {b : β} (h : s b (f a)) : b in Set.range f
· 使用定理 `instIsTransLt`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 < x2
-/
theorem IsWellFounded.rank_eq_typein (r) [IsWellOrder α r] : rank r = Ordinal.typein r := by
  classical
  let := linearOrderOfSTO r
  ext a
  exact InitialSeg.eq (⟨(OrderEmbedding.ofStrictMono _ WellFoundedLT.rank_strictMono).ltEmbedding,
    fun a b h ↦ mem_range_rank_of_le h.le⟩) (Ordinal.typein r) a
