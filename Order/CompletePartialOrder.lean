/-
Copyright (c) 2023 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
module

public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.OmegaCompletePartialOrder
public import Mathlib.Order.ConditionallyCompletePartialOrder.Defs

/-!
# Complete Partial Orders

This file considers complete partial orders (sometimes called directedly complete partial orders).
These are partial orders for which every directed set has a least upper bound.

## Main declarations

- `CompletePartialOrder`: Typeclass for (directly) complete partial orders.

## Main statements

- `CompletePartialOrder.toOmegaCompletePartialOrder`: A complete partial order is an ω-complete
  partial order.
- `CompleteLattice.toCompletePartialOrder`: A complete lattice is a complete partial order.

## References

- [B. A. Davey and H. A. Priestley, Introduction to lattices and order][davey_priestley]

## Tags

complete partial order, directedly complete partial order
-/

@[expose] public section

variable {ι : Sort*} {α β : Type*}

section CompletePartialOrder

/--
Definition of `CompletePartialOrder` / `CompletePartialOrder` 的定义

English:
class CompletePartialOrder
  parameters: (α : Type*)
  extends: PartialOrder α, SupSet α, OrderBot α
  axioms and operations (1):
    - lubOfDirected : forall d, DirectedOn (· <= ·) d -> IsLUB d (sSup d)

中文:
类 CompletePartialOrder
  参数: (α : 类型)
  继承: PartialOrder α, SupSet α, OrderBot α
  公理与运算 (1 个):
    - lubOfDirected : 对任意 d, DirectedOn (· <= ·) d -> IsLUB d (sSup d)
-/
class CompletePartialOrder (α : Type*) extends PartialOrder α, SupSet α, OrderBot α where
  /-- For each directed set `d`, `sSup d` is the least upper bound of `d`. -/
  lubOfDirected : forall d, DirectedOn (· <= ·) d -> IsLUB d (sSup d)

/-- Create a `CompletePartialOrder` from a `PartialOrder` and `SupSet`
such that for every directed set `d`, `sSup d` is the least upper bound of `d`.

The bottom element is defined as `sSup ∅`.
-/
@[reducible]
/--
Definition of `CompletePartialOrder.ofLubOfDirected` / `CompletePartialOrder.ofLubOfDirected` 的定义

English:
definition CompletePartialOrder.ofLubOfDirected
  signature: (α : Type*) [H1 : PartialOrder α] [H2 : SupSet α]
  body: H1; __ := H2
  bot := sSup ∅
bot_le := isLUB_empty_iff.mp lub_of_directed ∅ IsChain.empty.directedOn
  lubOfDirected := lub_of_directed

中文:
定义 CompletePartialOrder.ofLubOfDirected
  签名: (α : 类型) [H1 : PartialOrder α] [H2 : SupSet α]
  定义体: H1; __ := H2
  bot := sSup ∅
bot_le := isLUB_empty_iff.mp lub_of_directed ∅ IsChain.empty.directedOn
  lubOfDirected := lub_of_directed
-/
def CompletePartialOrder.ofLubOfDirected (α : Type*) [H1 : PartialOrder α] [H2 : SupSet α]
    (lub_of_directed : forall d : Set α, DirectedOn (· <= ·) d -> IsLUB d (sSup d)) :
    CompletePartialOrder α where
  __ := H1; __ := H2
  bot := sSup ∅
bot_le := isLUB_empty_iff.mp lub_of_directed ∅ IsChain.empty.directedOn
  lubOfDirected := lub_of_directed

variable [CompletePartialOrder α] [Preorder β] {f : ι -> α} {d : Set α} {a : α}

/--
lemma `DirectedOn.isLUB_sSup` / 引理 `DirectedOn.isLUB_sSup`

English:
lemma DirectedOn.isLUB_sSup
  statement: DirectedOn (· <= ·) d -> IsLUB d (sSup d)
  proof: CompletePartialOrder.lubOfDirected _

中文:
引理 DirectedOn.isLUB_sSup
  结论: DirectedOn (· <= ·) d -> IsLUB d (sSup d)
  证明: CompletePartialOrder.lubOfDirected _
-/
protected lemma DirectedOn.isLUB_sSup : DirectedOn (· <= ·) d -> IsLUB d (sSup d) :=
CompletePartialOrder.lubOfDirected _

/--
lemma `DirectedOn.le_sSup` / 引理 `DirectedOn.le_sSup`

English:
lemma DirectedOn.le_sSup
  given: (hd : DirectedOn (· <= ·) d) (ha : a in d)
  statement: a <= sSup d
  proof: hd.isLUB_sSup.1 ha

中文:
引理 DirectedOn.le_sSup
  条件: (hd : DirectedOn (· <= ·) d) (ha : a in d)
  结论: a <= sSup d
  证明: hd.isLUB_sSup.1 ha
-/
protected lemma DirectedOn.le_sSup (hd : DirectedOn (· <= ·) d) (ha : a in d) : a <= sSup d :=
hd.isLUB_sSup.1 ha

/--
lemma `DirectedOn.sSup_le` / 引理 `DirectedOn.sSup_le`

English:
lemma DirectedOn.sSup_le
  given: (hd : DirectedOn (· <= ·) d) (ha : forall b in d, b <= a)
  statement: sSup d <= a
  proof: hd.isLUB_sSup.2 ha

中文:
引理 DirectedOn.sSup_le
  条件: (hd : DirectedOn (· <= ·) d) (ha : 对任意 b in d, b <= a)
  结论: sSup d <= a
  证明: hd.isLUB_sSup.2 ha
-/
protected lemma DirectedOn.sSup_le (hd : DirectedOn (· <= ·) d) (ha : forall b in d, b <= a) : sSup d <= a :=
hd.isLUB_sSup.2 ha

/--
lemma `Directed.le_iSup` / 引理 `Directed.le_iSup`

English:
lemma Directed.le_iSup
  given: (hf : Directed (· <= ·) f) (i : ι)
  statement: f i <= ⨆ j, f j
  proof: hf.directedOn_range.le_sSup Set.mem_range_self _

中文:
引理 Directed.le_iSup
  条件: (hf : Directed (· <= ·) f) (i : ι)
  结论: f i <= ⨆ j, f j
  证明: hf.directedOn_range.le_sSup Set.mem_range_self _
-/
protected lemma Directed.le_iSup (hf : Directed (· <= ·) f) (i : ι) : f i <= ⨆ j, f j :=
hf.directedOn_range.le_sSup Set.mem_range_self _

/--
lemma `Directed.iSup_le` / 引理 `Directed.iSup_le`

English:
lemma Directed.iSup_le
  given: (hf : Directed (· <= ·) f) (ha : forall i, f i <= a)
  statement: ⨆ i, f i <= a
  proof: hf.directedOn_range.sSup_le Set.forall_mem_range.2 ha

中文:
引理 Directed.iSup_le
  条件: (hf : Directed (· <= ·) f) (ha : 对任意 i, f i <= a)
  结论: ⨆ i, f i <= a
  证明: hf.directedOn_range.sSup_le Set.forall_mem_range.2 ha
-/
protected lemma Directed.iSup_le (hf : Directed (· <= ·) f) (ha : forall i, f i <= a) : ⨆ i, f i <= a :=
hf.directedOn_range.sSup_le Set.forall_mem_range.2 ha

--TODO: We could mimic more `sSup`/`iSup` lemmas

/--
lemma `CompletePartialOrder.scottContinuous` / 引理 `CompletePartialOrder.scottContinuous`

English:
lemma CompletePartialOrder.scottContinuous
  given: {f : α -> β}
  proof: by
  refine ⟨fun h d hd₁ hd₂ => h hd₁ hd₂ hd₂.isLUB_sSup, fun h d hne hd a hda => ?_⟩
  rw [hda.unique hd.isLUB_sSup]
  exact h hne hd

中文:
引理 CompletePartialOrder.scottContinuous
  条件: {f : α -> β}
  证明: by
  refine ⟨fun h d hd₁ hd₂ => h hd₁ hd₂ hd₂.isLUB_sSup, fun h d hne hd a hda => ?_⟩
  rw [hda.unique hd.isLUB_sSup]
  exact h hne hd

Depends on / 依赖: hd.isLUB_sSup, hda.unique, isLUB_sSup, unique
-/
lemma CompletePartialOrder.scottContinuous {f : α -> β} :
    ScottContinuous f ↔
    forall ⦃d : Set α⦄, d.Nonempty -> DirectedOn (· <= ·) d -> IsLUB (f '' d) (f (sSup d)) := by
  refine ⟨fun h d hd₁ hd₂ => h hd₁ hd₂ hd₂.isLUB_sSup, fun h d hne hd a hda => ?_⟩
  rw [hda.unique hd.isLUB_sSup]
  exact h hne hd

open OmegaCompletePartialOrder

/-- A complete partial order is an ω-complete partial order. -/
instance (priority := 100) CompletePartialOrder.toOmegaCompletePartialOrder :
    OmegaCompletePartialOrder α where
  ωSup c := ⨆ n, c n
  le_ωSup c := c.directed.le_iSup
  ωSup_le c _ := c.directed.iSup_le

/-- A complete partial order is an conditionally complete partial order. -/
instance (priority := 100) : ConditionallyCompletePartialOrderSup α where
  isLUB_csSup_of_directed _ h_dir _ _ := h_dir.isLUB_sSup

end CompletePartialOrder

/-- A complete lattice is a complete partial order. -/
instance (priority := 100) CompleteLattice.toCompletePartialOrder [CompleteLattice α] :
    CompletePartialOrder α where
  sSup := sSup
  lubOfDirected _ _ := isLUB_sSup _
