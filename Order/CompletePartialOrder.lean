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
Complete partial orders are partial orders where every directed set has a least upper bound.
-/
/-
**CompletePartialOrder** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_4 → Type u_4
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Complete partial orders are partial orders where every directed set has a least 
upper bound.
-/
class CompletePartialOrder (α : Type*) extends PartialOrder α, SupSet α, OrderBot α where
  /-- For each directed set `d`, `sSup d` is the least upper bound of `d`. -/
  lubOfDirected : ∀ d, DirectedOn (· ≤ ·) d → IsLUB d (sSup d)

/-- Create a `CompletePartialOrder` from a `PartialOrder` and `SupSet`
such that for every directed set `d`, `sSup d` is the least upper bound of `d`.

The bottom element is defined as `sSup ∅`.
-/
@[reducible]
/-
**CompletePartialOrder.ofLubOfDirected** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：CompletePartialOrder.ofLubOfDirected (α : Type*) [H1 : PartialOrder α] [H2
 : SupSet α] (lub_of_directed : forall d : Set α, DirectedOn (· <= ·) d -> IsLUB
 d (sSup d)) : CompletePartialOrder α where __
参数：α : Type*；lub_of_directed : forall d : Set α, DirectedOn (· <= ·) d -> IsLUB 
d (sSup d)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Create a `CompletePartialOrder` from a `PartialOrder` and `SupSet`
such that for every directed set `d`, `sSup d` is the least upper bound of `d`.

The bottom element is defined as `sSup ∅`.
-/
def CompletePartialOrder.ofLubOfDirected (α : Type*) [H1 : PartialOrder α] [H2 : SupSet α]
    (lub_of_directed : ∀ d : Set α, DirectedOn (· ≤ ·) d → IsLUB d (sSup d)) :
    CompletePartialOrder α where
  __ := H1; __ := H2
  bot := sSup ∅
  bot_le := isLUB_empty_iff.mp <| lub_of_directed ∅ IsChain.empty.directedOn
  lubOfDirected := lub_of_directed

variable [CompletePartialOrder α] [Preorder β] {f : ι → α} {d : Set α} {a : α}
/-
**DirectedOn.isLUB_sSup** 是 Mathlib 中的一个定理，位于命名空间 `DirectedOn`。
形式化陈述：∀ {α : Type u_2} [inst : CompletePartialOrder α] {d : Set α}, DirectedOn (
fun x1 x2 => x1 ≤ x2) d → IsLUB d (sSup d)
参数：fun x1 x2 => x1 ≤ x2；sSup d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompletePartialOrder.lubOfDirected`：∀ {α : Type u_4} [self : CompletePar
tialOrder α] (d : Set α), DirectedOn (fun x1 x2 => x1 ≤ x2) d → IsLUB d (sSup d)
-/
protected lemma DirectedOn.isLUB_sSup : DirectedOn (· ≤ ·) d → IsLUB d (sSup d) :=
CompletePartialOrder.lubOfDirected _
/-
**DirectedOn.le_sSup** 是 Mathlib 中的一个定理，位于命名空间 `DirectedOn`。
形式化陈述：∀ {α : Type u_2} [inst : CompletePartialOrder α] {d : Set α} {a : α},   Di
rectedOn (fun x1 x2 => x1 ≤ x2) d → a ∈ d → a ≤ sSup d
参数：fun x1 x2 => x1 ≤ x2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `DirectedOn.isLUB_sSup`：∀ {α : Type u_2} [inst : CompletePartialOrder α] 
{d : Set α}, DirectedOn (fun x1 x2 => x1 ≤ x2) d → IsLUB d (sSup d)
-/
protected lemma DirectedOn.le_sSup (hd : DirectedOn (· ≤ ·) d) (ha : a ∈ d) : a ≤ sSup d :=
hd.isLUB_sSup.1 ha
/-
**DirectedOn.sSup_le** 是 Mathlib 中的一个定理，位于命名空间 `DirectedOn`。
形式化陈述：∀ {α : Type u_2} [inst : CompletePartialOrder α] {d : Set α} {a : α},   Di
rectedOn (fun x1 x2 => x1 ≤ x2) d → (∀ b ∈ d, b ≤ a) → sSup d ≤ a
参数：fun x1 x2 => x1 ≤ x2；∀ b ∈ d, b ≤ a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `DirectedOn.isLUB_sSup`：∀ {α : Type u_2} [inst : CompletePartialOrder α] 
{d : Set α}, DirectedOn (fun x1 x2 => x1 ≤ x2) d → IsLUB d (sSup d)
-/
protected lemma DirectedOn.sSup_le (hd : DirectedOn (· ≤ ·) d) (ha : ∀ b ∈ d, b ≤ a) : sSup d ≤ a :=
hd.isLUB_sSup.2 ha
/-
**Directed.le_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Directed`。
形式化陈述：∀ {ι : Sort u_1} {α : Type u_2} [inst : CompletePartialOrder α] {f : ι → α
},   Directed (fun x1 x2 => x1 ≤ x2) f → ∀ (i : ι), f i ≤ ⨆ j, f j
参数：fun x1 x2 => x1 ≤ x2；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectedOn.le_sSup`：∀ {α : Type u_2} [inst : CompletePartialOrder α] {d 
: Set α} {a : α},   DirectedOn (fun x1 x2 => x1 ≤ x2) d → a ∈ d → a ≤ sSup d
· 使用定理 `Directed.directedOn_range`：∀ {α : Type u_1} {ι : Sort u_3} {r : α → α → 
Prop} {f : ι → α}, Directed r f → DirectedOn r (Set.range f)
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
protected lemma Directed.le_iSup (hf : Directed (· ≤ ·) f) (i : ι) : f i ≤ ⨆ j, f j :=
hf.directedOn_range.le_sSup <| Set.mem_range_self _
/-
**Directed.iSup_le** 是 Mathlib 中的一个定理，位于命名空间 `Directed`。
形式化陈述：∀ {ι : Sort u_1} {α : Type u_2} [inst : CompletePartialOrder α] {f : ι → α
} {a : α},   Directed (fun x1 x2 => x1 ≤ x2) f → (∀ (i : ι), f i ≤ a) → ⨆ i, f i
 ≤ a
参数：fun x1 x2 => x1 ≤ x2；∀ (i : ι), f i ≤ a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectedOn.sSup_le`：∀ {α : Type u_2} [inst : CompletePartialOrder α] {d 
: Set α} {a : α},   DirectedOn (fun x1 x2 => x1 ≤ x2) d → (∀ b ∈ d, b ≤ a) → sSu
p d ≤ a
· 使用定理 `Directed.directedOn_range`：∀ {α : Type u_1} {ι : Sort u_3} {r : α → α → 
Prop} {f : ι → α}, Directed r f → DirectedOn r (Set.range f)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
-/
protected lemma Directed.iSup_le (hf : Directed (· ≤ ·) f) (ha : ∀ i, f i ≤ a) : ⨆ i, f i ≤ a :=
hf.directedOn_range.sSup_le <| Set.forall_mem_range.2 ha

--TODO: We could mimic more `sSup`/`iSup` lemmas

/-- Scott-continuity takes on a simpler form in complete partial orders. -/
/-
**CompletePartialOrder.scottContinuous** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CompletePartialOrder.scottContinuous {f : α -> β} : ScottContinuous f ↔ fo
rall ⦃d : Set α⦄, d.Nonempty -> DirectedOn (· <= ·) d -> IsLUB (f '' d) (f (sSup
 d))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectedOn.isLUB_sSup`：∀ {α : Type u_2} [inst : CompletePartialOrder α] 
{d : Set α}, DirectedOn (fun x1 x2 => x1 ≤ x2) d → IsLUB d (sSup d)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLUB.unique`：IsLUB.unique (Ha : IsLUB s a) (Hb : IsLUB s b) : a = b

--- 原说明 ---
Scott-continuity takes on a simpler form in complete partial orders.
-/
lemma CompletePartialOrder.scottContinuous {f : α → β} :
    ScottContinuous f ↔
    ∀ ⦃d : Set α⦄, d.Nonempty → DirectedOn (· ≤ ·) d → IsLUB (f '' d) (f (sSup d)) := by
  refine ⟨fun h d hd₁ hd₂ ↦ h hd₁ hd₂ hd₂.isLUB_sSup, fun h d hne hd a hda ↦ ?_⟩
  rw [hda.unique hd.isLUB_sSup]
  exact h hne hd

open OmegaCompletePartialOrder

/-- A complete partial order is an ω-complete partial order. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A complete partial order is an ω-complete partial order.
-/
instance (priority := 100) CompletePartialOrder.toOmegaCompletePartialOrder :
    OmegaCompletePartialOrder α where
  ωSup c := ⨆ n, c n
  le_ωSup c := c.directed.le_iSup
  ωSup_le c _ := c.directed.iSup_le

/-- A complete partial order is an conditionally complete partial order. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A complete partial order is an conditionally complete partial order.
-/
instance (priority := 100) : ConditionallyCompletePartialOrderSup α where
  isLUB_csSup_of_directed _ h_dir _ _ := h_dir.isLUB_sSup

end CompletePartialOrder

/-- A complete lattice is a complete partial order. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A complete lattice is a complete partial order.
-/
instance (priority := 100) CompleteLattice.toCompletePartialOrder [CompleteLattice α] :
    CompletePartialOrder α where
  sSup := sSup
  lubOfDirected _ _ := isLUB_sSup _
