/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Data.Set.Lattice
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.ConditionallyCompletePartialOrder.Basic

/-!
# Theory of conditionally complete lattices

A conditionally complete lattice is a lattice in which every non-empty bounded subset `s`
has a least upper bound and a greatest lower bound, denoted below by `sSup s` and `sInf s`.
Typical examples are `ℝ`, `ℕ`, and `ℤ` with their usual orders.

The theory is very comparable to the theory of complete lattices, except that suitable
boundedness and nonemptiness assumptions have to be added to most statements.
We express these using the `BddAbove` and `BddBelow` predicates, which we use to prove
most useful properties of `sSup` and `sInf` in conditionally complete lattices.

To differentiate the statements between complete lattices and conditionally complete
lattices, we prefix `sInf` and `sSup` in the statements by `c`, giving `csInf` and `csSup`.
For instance, `sInf_le` is a statement in complete lattices ensuring `sInf s ≤ x`,
while `csInf_le` is the same statement in conditionally complete lattices
with an additional assumption that `s` is bounded below.
-/

@[expose] public section

-- Guard against import creep
assert_not_exists Multiset

open Function OrderDual Set

variable {α β γ : Type*} {ι : Sort*}

section LE

namespace WithTop

/-!
Extension of `sSup` and `sInf` from a preorder `α` to `WithTop α` and `WithBot α`
-/

variable [LE α]

open scoped Classical in
@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SupSet
  signature: α] : SupSet (WithTop α)
  body: ⟨fun S =>
    if ⊤ in S then ⊤ else if BddAbove ((fun (a : α) => ↑a) ⁻¹' S : Set α) then
      ↑(sSup ((fun (a : α) => (a : WithTop α)) ⁻¹' S : Set α)) else ⊤⟩

中文:
实例 [上确界集
  签名: α] : 上确界集 (WithTop α)
  定义体: ⟨fun S =>
    if ⊤ in S then ⊤ else if BddAbove ((fun (a : α) => ↑a) ⁻¹' S : Set α) then
      ↑(sSup ((fun (a : α) => (a : WithTop α)) ⁻¹' S : Set α)) else ⊤⟩

Depends on / 依赖: BddAbove, WithTop
-/
noncomputable instance [SupSet α] : SupSet (WithTop α) :=
  ⟨fun S =>
    if ⊤ in S then ⊤ else if BddAbove ((fun (a : α) => ↑a) ⁻¹' S : Set α) then
      ↑(sSup ((fun (a : α) => (a : WithTop α)) ⁻¹' S : Set α)) else ⊤⟩

open scoped Classical in
@[to_dual]
/--
Instance `instInfSet` / 实例 `instInfSet`

English:
instance instInfSet
  signature: [InfSet α]
  body: ⟨fun S => if S subseteq {⊤} ∨ ¬BddBelow S then ⊤ else ↑(sInf ((fun (a : α) => ↑a) ⁻¹' S : Set α))⟩

@[to_dual]

中文:
实例 instInfSet
  签名: [下确界集 α]
  定义体: ⟨fun S => if S subseteq {⊤} ∨ ¬BddBelow S then ⊤ else ↑(sInf ((fun (a : α) => ↑a) ⁻¹' S : Set α))⟩

@[to_dual]

Depends on / 依赖: BddBelow, subseteq
-/
noncomputable instance instInfSet [InfSet α] : InfSet (WithTop α) :=
  ⟨fun S => if S subseteq {⊤} ∨ ¬BddBelow S then ⊤ else ↑(sInf ((fun (a : α) => ↑a) ⁻¹' S : Set α))⟩

@[to_dual]
/--
theorem `sSup_eq` / 定理 `sSup_eq`

English:
theorem sSup_eq
  statement: [SupSet α] {s : Set (WithTop α)} (hs : ⊤ ∉ s)
  proof: (if_neg hs).trans if_pos hs'

@[to_dual]

中文:
定理 sSup_eq
  结论: [上确界集 α] {s : 集合 (WithTop α)} (hs : ⊤ ∉ s)
  证明: (if_neg hs).trans if_pos hs'

@[to_dual]

Depends on / 依赖: if_neg, if_pos
-/
theorem sSup_eq [SupSet α] {s : Set (WithTop α)} (hs : ⊤ ∉ s)
    (hs' : BddAbove ((↑) ⁻¹' s : Set α)) : sSup s = ↑(sSup ((↑) ⁻¹' s) : α) :=
(if_neg hs).trans if_pos hs'

@[to_dual]
/--
theorem `sInf_eq` / 定理 `sInf_eq`

English:
theorem sInf_eq
  given: [InfSet α] {s : Set (WithTop α)} (hs : ¬s subseteq {⊤}) (h's : BddBelow s)
  proof: if_neg by simp [hs, h's]

@[to_dual (attr := simp)]

中文:
定理 sInf_eq
  条件: [下确界集 α] {s : 集合 (WithTop α)} (hs : ¬s subseteq {⊤}) (h's : BddBelow s)
  证明: if_neg by simp [hs, h's]

@[to_dual (attr := simp)]

Depends on / 依赖: if_neg
-/
theorem sInf_eq [InfSet α] {s : Set (WithTop α)} (hs : ¬s subseteq {⊤}) (h's : BddBelow s) :
    sInf s = ↑(sInf ((↑) ⁻¹' s) : α) :=
if_neg by simp [hs, h's]

@[to_dual (attr := simp)]
/--
theorem `sInf_empty` / 定理 `sInf_empty`

English:
theorem sInf_empty
  given: [InfSet α]
  statement: sInf (∅ : Set (WithTop α)) = ⊤
  proof: if_pos by simp

@[to_dual (attr := simp)]

中文:
定理 sInf_empty
  条件: [下确界集 α]
  结论: sInf (∅ : 集合 (WithTop α)) = ⊤
  证明: if_pos by simp

@[to_dual (attr := simp)]

Depends on / 依赖: if_pos
-/
theorem sInf_empty [InfSet α] : sInf (∅ : Set (WithTop α)) = ⊤ :=
if_pos by simp

@[to_dual (attr := simp)]
/--
theorem `sInf_singleton_top` / 定理 `sInf_singleton_top`

English:
theorem sInf_singleton_top
  given: [InfSet α]
  statement: sInf ({⊤} : Set (WithTop α)) = ⊤
  proof: if_pos .inl subset_rfl

@[to_dual (attr := simp)]

中文:
定理 sInf_singleton_top
  条件: [下确界集 α]
  结论: sInf ({⊤} : 集合 (WithTop α)) = ⊤
  证明: if_pos .inl subset_rfl

@[to_dual (attr := simp)]

Depends on / 依赖: if_pos, subset_rfl
-/
theorem sInf_singleton_top [InfSet α] : sInf ({⊤} : Set (WithTop α)) = ⊤ :=
if_pos .inl subset_rfl

@[to_dual (attr := simp)]
/--
theorem `sSup_of_top_mem` / 定理 `sSup_of_top_mem`

English:
theorem sSup_of_top_mem
  given: [SupSet α] {s : Set (WithTop α)} (h : ⊤ in s)
  statement: sSup s = ⊤
  proof: if_pos h

@[to_dual]

中文:
定理 sSup_of_top_mem
  条件: [上确界集 α] {s : 集合 (WithTop α)} (h : ⊤ in s)
  结论: sSup s = ⊤
  证明: if_pos h

@[to_dual]

Depends on / 依赖: if_pos
-/
theorem sSup_of_top_mem [SupSet α] {s : Set (WithTop α)} (h : ⊤ in s) : sSup s = ⊤ :=
  if_pos h

@[to_dual]
/--
theorem `sSup_singleton_top` / 定理 `sSup_singleton_top`

English:
theorem sSup_singleton_top
  given: [SupSet α]
  statement: sSup ({⊤} : Set (WithTop α)) = ⊤
  proof: by
  simp

@[to_dual]

中文:
定理 sSup_singleton_top
  条件: [上确界集 α]
  结论: sSup ({⊤} : 集合 (WithTop α)) = ⊤
  证明: by
  simp

@[to_dual]
-/
theorem sSup_singleton_top [SupSet α] : sSup ({⊤} : Set (WithTop α)) = ⊤ := by
  simp

@[to_dual]
/--
theorem `sSup_of_not_bddAbove` / 定理 `sSup_of_not_bddAbove`

English:
theorem sSup_of_not_bddAbove
  statement: [SupSet α] {s : Set (WithTop α)}
  proof: by
  by_cases hmem : ⊤ in s
  · exact sSup_of_top_mem hmem
.trans if_neg h · exact if_neg hmem

@[to_dual (attr := simp)]

中文:
定理 sSup_of_not_bddAbove
  结论: [上确界集 α] {s : 集合 (WithTop α)}
  证明: by
  by_cases hmem : ⊤ in s
  · exact sSup_of_top_mem hmem
.trans if_neg h · exact if_neg hmem

@[to_dual (attr := simp)]

Depends on / 依赖: if_neg, sSup_of_top_mem
-/
theorem sSup_of_not_bddAbove [SupSet α] {s : Set (WithTop α)}
    (h : ¬BddAbove ((↑) ⁻¹' s : Set α)) : sSup s = ⊤ := by
  by_cases hmem : ⊤ in s
  · exact sSup_of_top_mem hmem
.trans if_neg h · exact if_neg hmem

@[to_dual (attr := simp)]
/--
theorem `sInf_of_not_bddBelow` / 定理 `sInf_of_not_bddBelow`

English:
theorem sInf_of_not_bddBelow
  given: [InfSet α] {s : Set (WithTop α)} (h : ¬BddBelow s)
  proof: if_pos .inr h

@[to_dual (attr := norm_cast)]

中文:
定理 sInf_of_not_bddBelow
  条件: [下确界集 α] {s : 集合 (WithTop α)} (h : ¬BddBelow s)
  证明: if_pos .inr h

@[to_dual (attr := norm_cast)]

Depends on / 依赖: if_pos
-/
theorem sInf_of_not_bddBelow [InfSet α] {s : Set (WithTop α)} (h : ¬BddBelow s) :
    sInf s = ⊤ :=
if_pos .inr h

@[to_dual (attr := norm_cast)]
/--
theorem `coe_sSup'` / 定理 `coe_sSup'`

English:
theorem coe_sSup'
  given: [SupSet α] {s : Set α} (hs : BddAbove s)
  proof: by
  classical
  change _ = ite _ _ _
  rw [if_neg]; rw [preimage_image_eq]; rw [if_pos hs]
  · exact Option.some_injective _
  · rintro ⟨x, _, ⟨⟩⟩

@[to_dual]

中文:
定理 coe_sSup'
  条件: [上确界集 α] {s : 集合 α} (hs : BddAbove s)
  证明: by
  classical
  change _ = ite _ _ _
  rw [if_neg]; rw [preimage_image_eq]; rw [if_pos hs]
  · exact Option.some_injective _
  · rintro ⟨x, _, ⟨⟩⟩

@[to_dual]

Depends on / 依赖: Option.some_injective, classical, if_neg, if_pos, preimage_image_eq, some_injective
-/
theorem coe_sSup' [SupSet α] {s : Set α} (hs : BddAbove s) :
    ↑(sSup s) = (sSup ((fun (a : α) => ↑a) '' s) : WithTop α) := by
  classical
  change _ = ite _ _ _
  rw [if_neg]; rw [preimage_image_eq]; rw [if_pos hs]
  · exact Option.some_injective _
  · rintro ⟨x, _, ⟨⟩⟩

@[to_dual]
/--
theorem `sSup_empty` / 定理 `sSup_empty`

English:
theorem sSup_empty
  given: (α : Type*) [CompleteLattice α]
  statement: (sSup ∅ : WithTop α) = ⊥
  proof: by
  rw [sSup_eq (by simp) (OrderTop.bddAbove _)]; rw [Set.preimage_empty]; rw [_root_.sSup_empty]; rw [coe_bot]

中文:
定理 sSup_empty
  条件: (α : 类型) [完备格 α]
  结论: (sSup ∅ : WithTop α) = ⊥
  证明: by
  rw [sSup_eq (by simp) (OrderTop.bddAbove _)]; rw [Set.preimage_empty]; rw [_root_.sSup_empty]; rw [coe_bot]

Depends on / 依赖: OrderTop, OrderTop.bddAbove, Set.preimage_empty, _root_, _root_.sSup_empty, bddAbove, coe_bot, preimage_empty, sSup_empty, sSup_eq
-/
theorem sSup_empty (α : Type*) [CompleteLattice α] : (sSup ∅ : WithTop α) = ⊥ := by
  rw [sSup_eq (by simp) (OrderTop.bddAbove _)]; rw [Set.preimage_empty]; rw [_root_.sSup_empty]; rw [coe_bot]

end WithTop

end LE

section Preorder

variable [Preorder α]

@[to_dual (attr := norm_cast)]
/--
theorem `WithTop.coe_sInf'` / 定理 `WithTop.coe_sInf'`

English:
theorem WithTop.coe_sInf'
  statement: [InfSet α] {s : Set α} (hs : s.Nonempty)
  proof: by
  classical
  obtain ⟨x, hx⟩ := hs
  change _ = ite _ _ _
  split_ifs with h
  · rcases h with h1 | h2
    · cases h1 (mem_image_of_mem _ hx)
    · exact (h2 (Monotone.map_bddBelow coe_mono h's)).elim
  · rw [preimage_image_eq]
    exact Option.some_injective _

中文:
定理 WithTop.coe_sInf'
  结论: [下确界集 α] {s : 集合 α} (hs : s.非空)
  证明: by
  classical
  obtain ⟨x, hx⟩ := hs
  change _ = ite _ _ _
  split_ifs with h
  · rcases h with h1 | h2
    · cases h1 (mem_image_of_mem _ hx)
    · exact (h2 (Monotone.map_bddBelow coe_mono h's)).elim
  · rw [preimage_image_eq]
    exact Option.some_injective _

Depends on / 依赖: Monotone, Monotone.map_bddBelow, Option.some_injective, classical, coe_mono, map_bddBelow, mem_image_of_mem, preimage_image_eq, some_injective, split_ifs
-/
theorem WithTop.coe_sInf' [InfSet α] {s : Set α} (hs : s.Nonempty)
    (h's : BddBelow s) : ↑(sInf s) = (sInf ((fun (a : α) => ↑a) '' s) : WithTop α) := by
  classical
  obtain ⟨x, hx⟩ := hs
  change _ = ite _ _ _
  split_ifs with h
  · rcases h with h1 | h2
    · cases h1 (mem_image_of_mem _ hx)
    · exact (h2 (Monotone.map_bddBelow coe_mono h's)).elim
  · rw [preimage_image_eq]
    exact Option.some_injective _

end Preorder

/--
Instance `ConditionallyCompleteLinearOrder.toLinearOrder` / 实例 `ConditionallyCompleteLinearOrder.toLinearOrder`

English:
instance ConditionallyCompleteLinearOrder.toLinearOrder
  signature: [h : ConditionallyCompleteLinearOrder α]
  body: by
    by_cases hab : a = b
    · simp [hab]
    · rcases ConditionallyCompleteLinearOrder.le_total a b with (h₁ | h₂)
      · simp [h₁]
      · simp [show ¬(a <= b) from fun h => hab (le_antisymm h h₂), h₂]
  max_def a b := by
    by_cases hab : a = b
    · simp [hab]
    · rcases ConditionallyCompleteLinearOrder.le_total a b with (h₁ | h₂)
      · simp [h₁]
      · simp [show ¬(a <= b) from fun h => hab (le_antisymm h h₂), h₂]
  __ := h

中文:
实例 条件完备线性序.toLinearOrder
  签名: [h : 条件完备线性序 α]
  定义体: by
    by_cases hab : a = b
    · simp [hab]
    · rcases ConditionallyCompleteLinearOrder.le_total a b with (h₁ | h₂)
      · simp [h₁]
      · simp [show ¬(a <= b) from fun h => hab (le_antisymm h h₂), h₂]
  max_def a b := by
    by_cases hab : a = b
    · simp [hab]
    · rcases ConditionallyCompleteLinearOrder.le_total a b with (h₁ | h₂)
      · simp [h₁]
      · simp [show ¬(a <= b) from fun h => hab (le_antisymm h h₂), h₂]
  __ := h

Depends on / 依赖: ConditionallyCompleteLinearOrder, ConditionallyCompleteLinearOrder.le_total, le_antisymm, le_total, max_def
-/
instance ConditionallyCompleteLinearOrder.toLinearOrder [h : ConditionallyCompleteLinearOrder α] :
    LinearOrder α where
  min_def a b := by
    by_cases hab : a = b
    · simp [hab]
    · rcases ConditionallyCompleteLinearOrder.le_total a b with (h₁ | h₂)
      · simp [h₁]
      · simp [show ¬(a <= b) from fun h => hab (le_antisymm h h₂), h₂]
  max_def a b := by
    by_cases hab : a = b
    · simp [hab]
    · rcases ConditionallyCompleteLinearOrder.le_total a b with (h₁ | h₂)
      · simp [h₁]
      · simp [show ¬(a <= b) from fun h => hab (le_antisymm h h₂), h₂]
  __ := h

-- see Note [lower instance priority]
attribute [instance 100] ConditionallyCompleteLinearOrderBot.toOrderBot

-- see Note [lower instance priority]
/-- A complete lattice is a conditionally complete lattice, as there are no restrictions
on the properties of sInf and sSup in a complete lattice. -/
instance (priority := 100) CompleteLattice.toConditionallyCompleteLattice [CompleteLattice α] :
    ConditionallyCompleteLattice α where
  isLUB_csSup _ _ _ := isLUB_sSup _
  isGLB_csInf _ _ _ := isGLB_sInf _

-- see Note [lower instance priority]
instance (priority := 100) CompleteLinearOrder.toConditionallyCompleteLinearOrderBot {α : Type*}
    [h : CompleteLinearOrder α] : ConditionallyCompleteLinearOrderBot α where
  csSup_empty := sSup_empty
  csSup_of_not_bddAbove := fun s H => (H (OrderTop.bddAbove s)).elim
  csInf_of_not_bddBelow := fun s H => (H (OrderBot.bddBelow s)).elim
  __ := CompleteLattice.toConditionallyCompleteLattice
  __ := h

namespace OrderDual

/--
Instance `instConditionallyCompleteLattice` / 实例 `instConditionallyCompleteLattice`

English:
instance instConditionallyCompleteLattice
  signature: (α : Type*) [ConditionallyCompleteLattice α]
  body: ConditionallyCompleteLattice.isGLB_csInf (α := α)
  isGLB_csInf := ConditionallyCompleteLattice.isLUB_csSup (α := α)

中文:
实例 instConditionallyCompleteLattice
  签名: (α : 类型) [条件完备格 α]
  定义体: ConditionallyCompleteLattice.isGLB_csInf (α := α)
  isGLB_csInf := ConditionallyCompleteLattice.isLUB_csSup (α := α)

Depends on / 依赖: ConditionallyCompleteLattice, ConditionallyCompleteLattice.isGLB_csInf, isGLB_csInf
-/
instance instConditionallyCompleteLattice (α : Type*) [ConditionallyCompleteLattice α] :
    ConditionallyCompleteLattice αᵒᵈ where
  isLUB_csSup := ConditionallyCompleteLattice.isGLB_csInf (α := α)
  isGLB_csInf := ConditionallyCompleteLattice.isLUB_csSup (α := α)

instance (α : Type*) [ConditionallyCompleteLinearOrder α] :
    ConditionallyCompleteLinearOrder αᵒᵈ where
  csSup_of_not_bddAbove := ConditionallyCompleteLinearOrder.csInf_of_not_bddBelow (α := α)
  csInf_of_not_bddBelow := ConditionallyCompleteLinearOrder.csSup_of_not_bddAbove (α := α)
  __ := OrderDual.instConditionallyCompleteLattice α
  __ := OrderDual.instLinearOrder α

end OrderDual

section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice α] {s t : Set α} {a b : α}

@[to_dual]
/--
theorem `isLUB_csSup` / 定理 `isLUB_csSup`

English:
theorem isLUB_csSup
  given: (hn : s.Nonempty) (hb : BddAbove s := by bddDefault)
  statement: IsLUB s (sSup s)
  proof: ConditionallyCompleteLattice.isLUB_csSup _ hn hb

@[to_dual csInf_le]

中文:
定理 isLUB_csSup
  条件: (hn : s.非空) (hb : BddAbove s := by bddDefault)
  结论: IsLUB s (sSup s)
  证明: ConditionallyCompleteLattice.isLUB_csSup _ hn hb

@[to_dual csInf_le]

Depends on / 依赖: ConditionallyCompleteLattice, ConditionallyCompleteLattice.isLUB_csSup, bddDefault, isLUB_csSup
-/
theorem isLUB_csSup (hn : s.Nonempty) (hb : BddAbove s := by bddDefault) : IsLUB s (sSup s) :=
  ConditionallyCompleteLattice.isLUB_csSup _ hn hb

@[to_dual csInf_le]
/--
theorem `le_csSup` / 定理 `le_csSup`

English:
theorem le_csSup
  given: (h₁ : BddAbove s) (h₂ : a in s)
  statement: a <= sSup s
  proof: (isLUB_csSup (nonempty_of_mem h₂) h₁).1 h₂

@[to_dual le_csInf]

中文:
定理 le_csSup
  条件: (h₁ : BddAbove s) (h₂ : a in s)
  结论: a <= sSup s
  证明: (isLUB_csSup (nonempty_of_mem h₂) h₁).1 h₂

@[to_dual le_csInf]

Depends on / 依赖: isLUB_csSup, nonempty_of_mem
-/
theorem le_csSup (h₁ : BddAbove s) (h₂ : a in s) : a <= sSup s :=
  (isLUB_csSup (nonempty_of_mem h₂) h₁).1 h₂

@[to_dual le_csInf]
/--
theorem `csSup_le` / 定理 `csSup_le`

English:
theorem csSup_le
  given: (h₁ : s.Nonempty) (h₂ : forall b in s, b <= a)
  statement: sSup s <= a
  proof: (isLUB_csSup h₁ ⟨a, h₂⟩).2 h₂

@[to_dual csInf_le_of_le]

中文:
定理 csSup_le
  条件: (h₁ : s.非空) (h₂ : 对任意 b in s, b <= a)
  结论: sSup s <= a
  证明: (isLUB_csSup h₁ ⟨a, h₂⟩).2 h₂

@[to_dual csInf_le_of_le]

Depends on / 依赖: isLUB_csSup
-/
theorem csSup_le (h₁ : s.Nonempty) (h₂ : forall b in s, b <= a) : sSup s <= a :=
  (isLUB_csSup h₁ ⟨a, h₂⟩).2 h₂

@[to_dual csInf_le_of_le]
/--
theorem `le_csSup_of_le` / 定理 `le_csSup_of_le`

English:
theorem le_csSup_of_le
  given: (hs : BddAbove s) (hb : b in s) (h : a <= b)
  statement: a <= sSup s
  proof: le_trans h (le_csSup hs hb)

@[to_dual (attr := gcongr low)]

中文:
定理 le_csSup_of_le
  条件: (hs : BddAbove s) (hb : b in s) (h : a <= b)
  结论: a <= sSup s
  证明: le_trans h (le_csSup hs hb)

@[to_dual (attr := gcongr low)]

Depends on / 依赖: le_csSup, le_trans
-/
theorem le_csSup_of_le (hs : BddAbove s) (hb : b in s) (h : a <= b) : a <= sSup s :=
  le_trans h (le_csSup hs hb)

@[to_dual (attr := gcongr low)]
/--
theorem `csSup_le_csSup` / 定理 `csSup_le_csSup`

English:
theorem csSup_le_csSup
  given: (ht : BddAbove t) (hs : s.Nonempty) (h : s subseteq t)
  statement: sSup s <= sSup t
  proof: csSup_le hs fun _ ha => le_csSup ht (h ha)

@[to_dual csInf_le_iff]

中文:
定理 csSup_le_csSup
  条件: (ht : BddAbove t) (hs : s.非空) (h : s subseteq t)
  结论: sSup s <= sSup t
  证明: csSup_le hs fun _ ha => le_csSup ht (h ha)

@[to_dual csInf_le_iff]

Depends on / 依赖: csSup_le, le_csSup
-/
theorem csSup_le_csSup (ht : BddAbove t) (hs : s.Nonempty) (h : s subseteq t) : sSup s <= sSup t :=
  csSup_le hs fun _ ha => le_csSup ht (h ha)

@[to_dual csInf_le_iff]
/--
theorem `le_csSup_iff` / 定理 `le_csSup_iff`

English:
theorem le_csSup_iff
  given: (h : BddAbove s) (hs : s.Nonempty)
  statement: a <= sSup s ↔ forall b in upperBounds s, a <= b
  proof: ⟨fun h _ hb => le_trans h (csSup_le hs hb), fun hb => hb _ fun _ => le_csSup h⟩

@[to_dual]

中文:
定理 le_csSup_iff
  条件: (h : BddAbove s) (hs : s.非空)
  结论: a <= sSup s ↔ 对任意 b in upperBounds s, a <= b
  证明: ⟨fun h _ hb => le_trans h (csSup_le hs hb), fun hb => hb _ fun _ => le_csSup h⟩

@[to_dual]

Depends on / 依赖: csSup_le, le_csSup, le_trans
-/
theorem le_csSup_iff (h : BddAbove s) (hs : s.Nonempty) : a <= sSup s ↔ forall b in upperBounds s, a <= b :=
  ⟨fun h _ hb => le_trans h (csSup_le hs hb), fun hb => hb _ fun _ => le_csSup h⟩

@[to_dual]
/--
theorem `IsLUB.csSup_eq` / 定理 `IsLUB.csSup_eq`

English:
theorem IsLUB.csSup_eq
  given: (H : IsLUB s a) (ne : s.Nonempty)
  statement: sSup s = a
  proof: (isLUB_csSup ne ⟨a, H.1⟩).unique H

中文:
定理 IsLUB.csSup_eq
  条件: (H : IsLUB s a) (ne : s.非空)
  结论: sSup s = a
  证明: (isLUB_csSup ne ⟨a, H.1⟩).unique H

Depends on / 依赖: isLUB_csSup, unique
-/
theorem IsLUB.csSup_eq (H : IsLUB s a) (ne : s.Nonempty) : sSup s = a :=
  (isLUB_csSup ne ⟨a, H.1⟩).unique H

instance (priority := 100) ConditionallyCompleteLattice.toConditionallyCompletePartialOrder :
    ConditionallyCompletePartialOrder α where
  isGLB_csInf_of_directed _ _ := isGLB_csInf _
  isLUB_csSup_of_directed _ _ := isLUB_csSup _

/--
theorem `subset_Icc_csInf_csSup` / 定理 `subset_Icc_csInf_csSup`

English:
theorem subset_Icc_csInf_csSup
  given: (hb : BddBelow s) (ha : BddAbove s)
  statement: s subseteq Icc (sInf s) (sSup s)
  proof: fun _ hx => ⟨csInf_le hb hx, le_csSup ha hx⟩

@[to_dual le_csInf_iff]

中文:
定理 subset_Icc_csInf_csSup
  条件: (hb : BddBelow s) (ha : BddAbove s)
  结论: s subseteq 闭区间 (sInf s) (sSup s)
  证明: fun _ hx => ⟨csInf_le hb hx, le_csSup ha hx⟩

@[to_dual le_csInf_iff]

Depends on / 依赖: csInf_le, le_csSup
-/
theorem subset_Icc_csInf_csSup (hb : BddBelow s) (ha : BddAbove s) : s subseteq Icc (sInf s) (sSup s) :=
  fun _ hx => ⟨csInf_le hb hx, le_csSup ha hx⟩

@[to_dual le_csInf_iff]
/--
theorem `csSup_le_iff` / 定理 `csSup_le_iff`

English:
theorem csSup_le_iff
  given: (hb : BddAbove s) (hs : s.Nonempty)
  statement: sSup s <= a ↔ forall b in s, b <= a
  proof: isLUB_le_iff (isLUB_csSup hs hb)

@[to_dual]

中文:
定理 csSup_le_iff
  条件: (hb : BddAbove s) (hs : s.非空)
  结论: sSup s <= a ↔ 对任意 b in s, b <= a
  证明: isLUB_le_iff (isLUB_csSup hs hb)

@[to_dual]

Depends on / 依赖: isLUB_csSup, isLUB_le_iff
-/
theorem csSup_le_iff (hb : BddAbove s) (hs : s.Nonempty) : sSup s <= a ↔ forall b in s, b <= a :=
  isLUB_le_iff (isLUB_csSup hs hb)

@[to_dual]
/--
theorem `csSup_lowerBounds_eq_csInf` / 定理 `csSup_lowerBounds_eq_csInf`

English:
theorem csSup_lowerBounds_eq_csInf
  given: {s : Set α} (h : BddBelow s) (hs : s.Nonempty)
  proof: (isLUB_csSup h <| hs.mono fun _ hx _ hy => hy hx).unique (isGLB_csInf hs h).isLUB

@[to_dual]

中文:
定理 csSup_lowerBounds_eq_csInf
  条件: {s : 集合 α} (h : BddBelow s) (hs : s.非空)
  证明: (isLUB_csSup h <| hs.mono fun _ hx _ hy => hy hx).unique (isGLB_csInf hs h).isLUB

@[to_dual]

Depends on / 依赖: hs.mono, isGLB_csInf, isLUB_csSup, unique
-/
theorem csSup_lowerBounds_eq_csInf {s : Set α} (h : BddBelow s) (hs : s.Nonempty) :
    sSup (lowerBounds s) = sInf s :=
  (isLUB_csSup h <| hs.mono fun _ hx _ hy => hy hx).unique (isGLB_csInf hs h).isLUB

@[to_dual]
/--
theorem `csSup_lowerBounds_range` / 定理 `csSup_lowerBounds_range`

English:
theorem csSup_lowerBounds_range
  given: [Nonempty β] {f : β -> α} (hf : BddBelow (range f))
  proof: csSup_lowerBounds_eq_csInf hf range_nonempty _

@[to_dual notMem_of_csSup_lt]

中文:
定理 csSup_lowerBounds_range
  条件: [非空 β] {f : β -> α} (hf : BddBelow (range f))
  证明: csSup_lowerBounds_eq_csInf hf range_nonempty _

@[to_dual notMem_of_csSup_lt]

Depends on / 依赖: csSup_lowerBounds_eq_csInf, range_nonempty
-/
theorem csSup_lowerBounds_range [Nonempty β] {f : β -> α} (hf : BddBelow (range f)) :
    sSup (lowerBounds (range f)) = ⨅ i, f i :=
csSup_lowerBounds_eq_csInf hf range_nonempty _

@[to_dual notMem_of_csSup_lt]
/--
theorem `notMem_of_lt_csInf` / 定理 `notMem_of_lt_csInf`

English:
theorem notMem_of_lt_csInf
  given: {x : α} {s : Set α} (h : x < sInf s) (hs : BddBelow s)
  statement: x ∉ s
  proof: fun hx => lt_irrefl _ (h.trans_le (csInf_le hs hx))

中文:
定理 notMem_of_lt_csInf
  条件: {x : α} {s : 集合 α} (h : x < sInf s) (hs : BddBelow s)
  结论: x ∉ s
  证明: fun hx => lt_irrefl _ (h.trans_le (csInf_le hs hx))

Depends on / 依赖: csInf_le, h.trans_le, lt_irrefl, trans_le
-/
theorem notMem_of_lt_csInf {x : α} {s : Set α} (h : x < sInf s) (hs : BddBelow s) : x ∉ s :=
  fun hx => lt_irrefl _ (h.trans_le (csInf_le hs hx))

/-- Introduction rule to prove that `b` is the supremum of `s`: it suffices to check that `b`
is larger than all elements of `s`, and that this is not the case of any `w<b`.
See `sSup_eq_of_forall_le_of_forall_lt_exists_gt` for a version in complete lattices. -/
@[to_dual csInf_eq_of_forall_ge_of_forall_gt_exists_lt
/-- Introduction rule to prove that `b` is the infimum of `s`: it suffices to check that `b`
is smaller than all elements of `s`, and that this is not the case of any `w>b`.
See `sInf_eq_of_forall_ge_of_forall_gt_exists_lt` for a version in complete lattices. -/]
/--
theorem `csSup_eq_of_forall_le_of_forall_lt_exists_gt` / 定理 `csSup_eq_of_forall_le_of_forall_lt_exists_gt`

English:
theorem csSup_eq_of_forall_le_of_forall_lt_exists_gt
  statement: (hs : s.Nonempty) (H : forall a in s, a <= b)
  proof: (eq_of_le_of_not_lt (csSup_le hs H)) fun hb =>
    let ⟨_, ha, ha'⟩ := H' _ hb
lt_irrefl _ ha'.trans_le le_csSup ⟨b, H⟩ ha

中文:
定理 csSup_eq_of_对任意_le_of_对任意_lt_存在_gt
  结论: (hs : s.非空) (H : 对任意 a in s, a <= b)
  证明: (eq_of_le_of_not_lt (csSup_le hs H)) fun hb =>
    let ⟨_, ha, ha'⟩ := H' _ hb
lt_irrefl _ ha'.trans_le le_csSup ⟨b, H⟩ ha

Depends on / 依赖: csSup_le, eq_of_le_of_not_lt, le_csSup, lt_irrefl, trans_le
-/
theorem csSup_eq_of_forall_le_of_forall_lt_exists_gt (hs : s.Nonempty) (H : forall a in s, a <= b)
    (H' : forall w, w < b -> exists a in s, w < a) : sSup s = b :=
  (eq_of_le_of_not_lt (csSup_le hs H)) fun hb =>
    let ⟨_, ha, ha'⟩ := H' _ hb
lt_irrefl _ ha'.trans_le le_csSup ⟨b, H⟩ ha

/-- `b < sSup s` when there is an element `a` in `s` with `b < a`, when `s` is bounded above.
This is essentially an iff, except that the assumptions for the two implications are
slightly different (one needs boundedness above for one direction, nonemptiness and linear
order for the other one), so we formulate separately the two implications, contrary to
the `CompleteLattice` case. -/
@[to_dual csInf_lt_of_lt
/-- `sInf s < b` when there is an element `a` in `s` with `a < b`, when `s` is bounded below.
This is essentially an iff, except that the assumptions for the two implications are
slightly different (one needs boundedness below for one direction, nonemptiness and linear
order for the other one), so we formulate separately the two implications, contrary to
the `CompleteLattice` case. -/]
/--
theorem `lt_csSup_of_lt` / 定理 `lt_csSup_of_lt`

English:
theorem lt_csSup_of_lt
  given: (hs : BddAbove s) (ha : a in s) (h : b < a)
  statement: b < sSup s
  proof: lt_of_lt_of_le h (le_csSup hs ha)

中文:
定理 lt_csSup_of_lt
  条件: (hs : BddAbove s) (ha : a in s) (h : b < a)
  结论: b < sSup s
  证明: lt_of_lt_of_le h (le_csSup hs ha)

Depends on / 依赖: le_csSup, lt_of_lt_of_le
-/
theorem lt_csSup_of_lt (hs : BddAbove s) (ha : a in s) (h : b < a) : b < sSup s :=
  lt_of_lt_of_le h (le_csSup hs ha)

/-- If all elements of a nonempty set `s` are less than or equal to all elements
of a nonempty set `t`, then there exists an element between these sets. -/
@[to_dual none]
/--
theorem `exists_between_of_forall_le` / 定理 `exists_between_of_forall_le`

English:
theorem exists_between_of_forall_le
  statement: (sne : s.Nonempty) (tne : t.Nonempty)
  proof: ⟨sInf t, fun x hx => le_csInf tne hst x hx, fun _ hy => csInf_le (sne.mono hst) hy⟩

@[to_dual]

中文:
定理 存在_between_of_对任意_le
  结论: (sne : s.非空) (tne : t.非空)
  证明: ⟨sInf t, fun x hx => le_csInf tne hst x hx, fun _ hy => csInf_le (sne.mono hst) hy⟩

@[to_dual]

Depends on / 依赖: csInf_le, le_csInf, sne.mono
-/
theorem exists_between_of_forall_le (sne : s.Nonempty) (tne : t.Nonempty)
    (hst : forall x in s, forall y in t, x <= y) : (upperBounds s inter lowerBounds t).Nonempty :=
⟨sInf t, fun x hx => le_csInf tne hst x hx, fun _ hy => csInf_le (sne.mono hst) hy⟩

@[to_dual]
/--
theorem `csSup_pair` / 定理 `csSup_pair`

English:
theorem csSup_pair
  given: (a b : α)
  statement: sSup {a, b} = a ⊔ b
  proof: (@isLUB_pair _ _ a b).csSup_eq (insert_nonempty _ _)

中文:
定理 csSup_pair
  条件: (a b : α)
  结论: sSup {a, b} = a ⊔ b
  证明: (@isLUB_pair _ _ a b).csSup_eq (insert_nonempty _ _)

Depends on / 依赖: csSup_eq, insert_nonempty, isLUB_pair
-/
theorem csSup_pair (a b : α) : sSup {a, b} = a ⊔ b :=
  (@isLUB_pair _ _ a b).csSup_eq (insert_nonempty _ _)

/-- If a set is bounded below and above, and nonempty, its infimum is less than or equal to
its supremum. -/
@[to_dual self (reorder := hb ha)]
/--
theorem `csInf_le_csSup` / 定理 `csInf_le_csSup`

English:
theorem csInf_le_csSup
  statement: (ne : s.Nonempty) (hb : BddBelow s := by bddDefault)
  proof: isGLB_le_isLUB (isGLB_csInf ne hb) (isLUB_csSup ne ha) ne

中文:
定理 csInf_le_csSup
  结论: (ne : s.非空) (hb : BddBelow s := by bddDefault)
  证明: isGLB_le_isLUB (isGLB_csInf ne hb) (isLUB_csSup ne ha) ne

Depends on / 依赖: BddAbove, bddDefault, isGLB_csInf, isGLB_le_isLUB, isLUB_csSup
-/
theorem csInf_le_csSup (ne : s.Nonempty) (hb : BddBelow s := by bddDefault)
    (ha : BddAbove s := by bddDefault) : sInf s <= sSup s :=
  isGLB_le_isLUB (isGLB_csInf ne hb) (isLUB_csSup ne ha) ne

/--
theorem `csInf_le_csSup_of_nonempty_inter` / 定理 `csInf_le_csSup_of_nonempty_inter`

English:
theorem csInf_le_csSup_of_nonempty_inter
  statement: (h : (s inter t).Nonempty) (hs : BddBelow s := by bddDefault)
  proof: isGLB_le_isLUB_of_nonempty_inter h (isGLB_csInf h.left hs) (isLUB_csSup h.right ht)

中文:
定理 csInf_le_csSup_of_nonempty_inter
  结论: (h : (s inter t).非空) (hs : BddBelow s := by bddDefault)
  证明: isGLB_le_isLUB_of_nonempty_inter h (isGLB_csInf h.left hs) (isLUB_csSup h.right ht)

Depends on / 依赖: BddAbove, bddDefault, h.left, h.right, isGLB_csInf, isGLB_le_isLUB_of_nonempty_inter, isLUB_csSup
-/
theorem csInf_le_csSup_of_nonempty_inter (h : (s inter t).Nonempty) (hs : BddBelow s := by bddDefault)
    (ht : BddAbove t := by bddDefault) : sInf s <= sSup t :=
  isGLB_le_isLUB_of_nonempty_inter h (isGLB_csInf h.left hs) (isLUB_csSup h.right ht)

/-- The `sSup` of a union of two sets is the max of the suprema of each subset, under the
assumptions that all sets are bounded above and nonempty. -/
@[to_dual
/-- The `sInf` of a union of two sets is the min of the infima of each subset, under the assumptions
that all sets are bounded below and nonempty. -/]
/--
theorem `csSup_union` / 定理 `csSup_union`

English:
theorem csSup_union
  given: (hs : BddAbove s) (sne : s.Nonempty) (ht : BddAbove t) (tne : t.Nonempty)
  proof: ((isLUB_csSup sne hs).union (isLUB_csSup tne ht)).csSup_eq sne.inl

中文:
定理 csSup_union
  条件: (hs : BddAbove s) (sne : s.非空) (ht : BddAbove t) (tne : t.非空)
  证明: ((isLUB_csSup sne hs).union (isLUB_csSup tne ht)).csSup_eq sne.inl

Depends on / 依赖: csSup_eq, isLUB_csSup, sne.inl
-/
theorem csSup_union (hs : BddAbove s) (sne : s.Nonempty) (ht : BddAbove t) (tne : t.Nonempty) :
    sSup (s union t) = sSup s ⊔ sSup t :=
  ((isLUB_csSup sne hs).union (isLUB_csSup tne ht)).csSup_eq sne.inl

/-- The supremum of an intersection of two sets is bounded by the minimum of the suprema of each
set, if all sets are bounded above and nonempty. -/
@[to_dual le_csInf_inter
/-- The infimum of an intersection of two sets is bounded below by the maximum of the
infima of each set, if all sets are bounded below and nonempty. -/]
/--
theorem `csSup_inter_le` / 定理 `csSup_inter_le`

English:
theorem csSup_inter_le
  given: (hs : BddAbove s) (ht : BddAbove t) (hst : (s inter t).Nonempty)
  proof: (csSup_le hst) fun _ hx => le_inf (le_csSup hs hx.1) (le_csSup ht hx.2)

中文:
定理 csSup_inter_le
  条件: (hs : BddAbove s) (ht : BddAbove t) (hst : (s inter t).非空)
  证明: (csSup_le hst) fun _ hx => le_inf (le_csSup hs hx.1) (le_csSup ht hx.2)

Depends on / 依赖: csSup_le, le_csSup, le_inf
-/
theorem csSup_inter_le (hs : BddAbove s) (ht : BddAbove t) (hst : (s inter t).Nonempty) :
    sSup (s inter t) <= sSup s ⊓ sSup t :=
  (csSup_le hst) fun _ hx => le_inf (le_csSup hs hx.1) (le_csSup ht hx.2)

/-- The supremum of `insert a s` is the maximum of `a` and the supremum of `s`, if `s` is
nonempty and bounded above. -/
@[to_dual (attr := simp)
/-- The infimum of `insert a s` is the minimum of `a` and the infimum of `s`, if `s` is
nonempty and bounded below. -/]
/--
theorem `csSup_insert` / 定理 `csSup_insert`

English:
theorem csSup_insert
  given: (hs : BddAbove s) (sne : s.Nonempty)
  statement: sSup (insert a s) = a ⊔ sSup s
  proof: ((isLUB_csSup sne hs).insert a).csSup_eq (insert_nonempty a s)

@[to_dual (attr := simp)]

中文:
定理 csSup_insert
  条件: (hs : BddAbove s) (sne : s.非空)
  结论: sSup (insert a s) = a ⊔ sSup s
  证明: ((isLUB_csSup sne hs).insert a).csSup_eq (insert_nonempty a s)

@[to_dual (attr := simp)]

Depends on / 依赖: Representation, Representation.isTrivial_def, csSup_eq, insert, insert_nonempty, isLUB_csSup, isTrivial_def
-/
theorem csSup_insert (hs : BddAbove s) (sne : s.Nonempty) : sSup (insert a s) = a ⊔ sSup s :=
  ((isLUB_csSup sne hs).insert a).csSup_eq (insert_nonempty a s)

@[to_dual (attr := simp)]
/--
theorem `csSup_Ico` / 定理 `csSup_Ico`

English:
theorem csSup_Ico
  given: [DenselyOrdered α] (h : a < b)
  statement: sSup (Ico a b) = b
  proof: (isLUB_Ico h).csSup_eq (nonempty_Ico.2 h)

@[to_dual (attr := simp)]

中文:
定理 csSup_Ico
  条件: [稠密序 α] (h : a < b)
  结论: sSup (左闭右开区间 a b) = b
  证明: (isLUB_Ico h).csSup_eq (nonempty_Ico.2 h)

@[to_dual (attr := simp)]

Depends on / 依赖: csSup_eq, isLUB_Ico, nonempty_Ico
-/
theorem csSup_Ico [DenselyOrdered α] (h : a < b) : sSup (Ico a b) = b :=
  (isLUB_Ico h).csSup_eq (nonempty_Ico.2 h)

@[to_dual (attr := simp)]
/--
theorem `csSup_Iio` / 定理 `csSup_Iio`

English:
theorem csSup_Iio
  given: [NoMinOrder α] [DenselyOrdered α]
  statement: sSup (Iio a) = a
  proof: csSup_eq_of_forall_le_of_forall_lt_exists_gt nonempty_Iio (fun _ => le_of_lt) fun w hw => by
    simpa [and_comm] using exists_between hw

@[to_dual (attr := simp)]

中文:
定理 csSup_Iio
  条件: [NoMin序 α] [稠密序 α]
  结论: sSup (左无界右开区间 a) = a
  证明: csSup_eq_of_forall_le_of_forall_lt_exists_gt nonempty_Iio (fun _ => le_of_lt) fun w hw => by
    simpa [and_comm] using exists_between hw

@[to_dual (attr := simp)]

Depends on / 依赖: and_comm, csSup_eq_of_forall_le_of_forall_lt_exists_gt, exists_between, le_of_lt, nonempty_Iio
-/
theorem csSup_Iio [NoMinOrder α] [DenselyOrdered α] : sSup (Iio a) = a :=
  csSup_eq_of_forall_le_of_forall_lt_exists_gt nonempty_Iio (fun _ => le_of_lt) fun w hw => by
    simpa [and_comm] using exists_between hw

@[to_dual (attr := simp)]
/--
theorem `csSup_Ioo` / 定理 `csSup_Ioo`

English:
theorem csSup_Ioo
  given: [DenselyOrdered α] (h : a < b)
  statement: sSup (Ioo a b) = b
  proof: (isLUB_Ioo h).csSup_eq (nonempty_Ioo.2 h)

中文:
定理 csSup_Ioo
  条件: [稠密序 α] (h : a < b)
  结论: sSup (开区间 a b) = b
  证明: (isLUB_Ioo h).csSup_eq (nonempty_Ioo.2 h)

Depends on / 依赖: csSup_eq, isLUB_Ioo, nonempty_Ioo
-/
theorem csSup_Ioo [DenselyOrdered α] (h : a < b) : sSup (Ioo a b) = b :=
  (isLUB_Ioo h).csSup_eq (nonempty_Ioo.2 h)

/--
theorem `csSup_eq_of_is_forall_le_of_forall_le_imp_ge` / 定理 `csSup_eq_of_is_forall_le_of_forall_le_imp_ge`

English:
theorem csSup_eq_of_is_forall_le_of_forall_le_imp_ge
  statement: (hs : s.Nonempty) (h_is_ub : forall a in s, a <= b)
  proof: (csSup_le hs h_is_ub).antisymm ((h_b_le_ub _) fun _ => le_csSup ⟨b, h_is_ub⟩)

中文:
定理 csSup_eq_of_is_对任意_le_of_对任意_le_imp_ge
  结论: (hs : s.非空) (h_is_ub : 对任意 a in s, a <= b)
  证明: (csSup_le hs h_is_ub).antisymm ((h_b_le_ub _) fun _ => le_csSup ⟨b, h_is_ub⟩)

Depends on / 依赖: antisymm, csSup_le, h_b_le_ub, h_is_ub, le_csSup
-/
theorem csSup_eq_of_is_forall_le_of_forall_le_imp_ge (hs : s.Nonempty) (h_is_ub : forall a in s, a <= b)
    (h_b_le_ub : forall ub, (forall a in s, a <= ub) -> b <= ub) : sSup s = b :=
  (csSup_le hs h_is_ub).antisymm ((h_b_le_ub _) fun _ => le_csSup ⟨b, h_is_ub⟩)

end ConditionallyCompleteLattice

/--
Instance `Pi.conditionallyCompleteLattice` / 实例 `Pi.conditionallyCompleteLattice`

English:
instance Pi.conditionallyCompleteLattice
  signature: {ι : Type*} {α : ι -> Type*}
  body: isLUB_pi.mpr fun _ => by
    rw [sSup_apply_eq_sSup_image]
    exact isLUB_csSup (image_nonempty.mpr hn) ((monotone_eval _).map_bddAbove hb)
  isGLB_csInf _ hn hb := isGLB_pi.mpr fun _ => by
    rw [sInf_apply_eq_sInf_image]
    exact isGLB_csInf (image_nonempty.mpr hn) ((monotone_eval _).map_bddBelow hb)

中文:
实例 依赖函数类型.conditionallyCompleteLattice
  签名: {ι : 类型} {α : ι -> 类型}
  定义体: isLUB_pi.mpr fun _ => by
    rw [sSup_apply_eq_sSup_image]
    exact isLUB_csSup (image_nonempty.mpr hn) ((monotone_eval _).map_bddAbove hb)
  isGLB_csInf _ hn hb := isGLB_pi.mpr fun _ => by
    rw [sInf_apply_eq_sInf_image]
    exact isGLB_csInf (image_nonempty.mpr hn) ((monotone_eval _).map_bddBelow hb)

Depends on / 依赖: image_nonempty, image_nonempty.mpr, isGLB_csInf, isGLB_pi, isGLB_pi.mpr, isLUB_csSup, isLUB_pi, isLUB_pi.mpr, map_bddAbove, map_bddBelow, monotone_eval, sInf_apply_eq_sInf_image, sSup_apply_eq_sSup_image
-/
instance Pi.conditionallyCompleteLattice {ι : Type*} {α : ι -> Type*}
    [forall i, ConditionallyCompleteLattice (α i)] : ConditionallyCompleteLattice (forall i, α i) where
  isLUB_csSup _ hn hb := isLUB_pi.mpr fun _ => by
    rw [sSup_apply_eq_sSup_image]
    exact isLUB_csSup (image_nonempty.mpr hn) ((monotone_eval _).map_bddAbove hb)
  isGLB_csInf _ hn hb := isGLB_pi.mpr fun _ => by
    rw [sInf_apply_eq_sInf_image]
    exact isGLB_csInf (image_nonempty.mpr hn) ((monotone_eval _).map_bddBelow hb)

section ConditionallyCompleteLinearOrder

variable [ConditionallyCompleteLinearOrder α] {f : ι -> α} {s : Set α} {a b : α}

/-- When `b < sSup s`, there is an element `a` in `s` with `b < a`, if `s` is nonempty and the order
is a linear order. -/
@[to_dual exists_lt_of_csInf_lt
/-- When `sInf s < b`, there is an element `a` in `s` with `a < b`, if `s` is nonempty and the order
is a linear order. -/]
/--
theorem `exists_lt_of_lt_csSup` / 定理 `exists_lt_of_lt_csSup`

English:
theorem exists_lt_of_lt_csSup
  given: (hs : s.Nonempty) (hb : b < sSup s)
  statement: exists a in s, b < a
  proof: by
  contrapose! hb
  exact csSup_le hs hb

@[to_dual csInf_lt_iff]

中文:
定理 存在_lt_of_lt_csSup
  条件: (hs : s.非空) (hb : b < sSup s)
  结论: 存在 a in s, b < a
  证明: by
  contrapose! hb
  exact csSup_le hs hb

@[to_dual csInf_lt_iff]

Depends on / 依赖: contrapose, csSup_le
-/
theorem exists_lt_of_lt_csSup (hs : s.Nonempty) (hb : b < sSup s) : exists a in s, b < a := by
  contrapose! hb
  exact csSup_le hs hb

@[to_dual csInf_lt_iff]
/--
theorem `lt_csSup_iff` / 定理 `lt_csSup_iff`

English:
theorem lt_csSup_iff
  given: (hb : BddAbove s) (hs : s.Nonempty)
  statement: a < sSup s ↔ exists b in s, a < b
  proof: lt_isLUB_iff isLUB_csSup hs hb

@[to_dual (attr := simp)]

中文:
定理 lt_csSup_iff
  条件: (hb : BddAbove s) (hs : s.非空)
  结论: a < sSup s ↔ 存在 b in s, a < b
  证明: lt_isLUB_iff isLUB_csSup hs hb

@[to_dual (attr := simp)]

Depends on / 依赖: isLUB_csSup, lt_isLUB_iff
-/
theorem lt_csSup_iff (hb : BddAbove s) (hs : s.Nonempty) : a < sSup s ↔ exists b in s, a < b :=
lt_isLUB_iff isLUB_csSup hs hb

@[to_dual (attr := simp)]
/--
lemma `csSup_of_not_bddAbove` / 引理 `csSup_of_not_bddAbove`

English:
lemma csSup_of_not_bddAbove
  given: (hs : ¬BddAbove s)
  statement: sSup s = sSup ∅
  proof: ConditionallyCompleteLinearOrder.csSup_of_not_bddAbove s hs

@[to_dual (attr := simp)]

中文:
引理 csSup_of_not_bddAbove
  条件: (hs : ¬BddAbove s)
  结论: sSup s = sSup ∅
  证明: ConditionallyCompleteLinearOrder.csSup_of_not_bddAbove s hs

@[to_dual (attr := simp)]

Depends on / 依赖: ConditionallyCompleteLinearOrder, ConditionallyCompleteLinearOrder.csSup_of_not_bddAbove, csSup_of_not_bddAbove
-/
lemma csSup_of_not_bddAbove (hs : ¬BddAbove s) : sSup s = sSup ∅ :=
  ConditionallyCompleteLinearOrder.csSup_of_not_bddAbove s hs

@[to_dual (attr := simp)]
/--
lemma `ciSup_of_not_bddAbove` / 引理 `ciSup_of_not_bddAbove`

English:
lemma ciSup_of_not_bddAbove
  given: (hf : ¬BddAbove (range f))
  statement: ⨆ i, f i = sSup ∅
  proof: csSup_of_not_bddAbove hf

@[to_dual]

中文:
引理 ciSup_of_not_bddAbove
  条件: (hf : ¬BddAbove (range f))
  结论: ⨆ i, f i = sSup ∅
  证明: csSup_of_not_bddAbove hf

@[to_dual]

Depends on / 依赖: csSup_of_not_bddAbove
-/
lemma ciSup_of_not_bddAbove (hf : ¬BddAbove (range f)) : ⨆ i, f i = sSup ∅ :=
  csSup_of_not_bddAbove hf

@[to_dual]
/--
lemma `csSup_eq_univ_of_not_bddAbove` / 引理 `csSup_eq_univ_of_not_bddAbove`

English:
lemma csSup_eq_univ_of_not_bddAbove
  given: (hs : ¬BddAbove s)
  statement: sSup s = sSup univ
  proof: by
  rw [csSup_of_not_bddAbove hs]; rw [csSup_of_not_bddAbove (s := univ)]
  contrapose hs
  exact hs.mono (subset_univ _)

@[to_dual]

中文:
引理 csSup_eq_univ_of_not_bddAbove
  条件: (hs : ¬BddAbove s)
  结论: sSup s = sSup univ
  证明: by
  rw [csSup_of_not_bddAbove hs]; rw [csSup_of_not_bddAbove (s := univ)]
  contrapose hs
  exact hs.mono (subset_univ _)

@[to_dual]

Depends on / 依赖: contrapose, csSup_of_not_bddAbove, hs.mono, subset_univ
-/
lemma csSup_eq_univ_of_not_bddAbove (hs : ¬BddAbove s) : sSup s = sSup univ := by
  rw [csSup_of_not_bddAbove hs]; rw [csSup_of_not_bddAbove (s := univ)]
  contrapose hs
  exact hs.mono (subset_univ _)

@[to_dual]
/--
lemma `ciSup_eq_univ_of_not_bddAbove` / 引理 `ciSup_eq_univ_of_not_bddAbove`

English:
lemma ciSup_eq_univ_of_not_bddAbove
  given: (hf : ¬BddAbove (range f))
  statement: ⨆ i, f i = sSup univ
  proof: csSup_eq_univ_of_not_bddAbove hf

中文:
引理 ciSup_eq_univ_of_not_bddAbove
  条件: (hf : ¬BddAbove (range f))
  结论: ⨆ i, f i = sSup univ
  证明: csSup_eq_univ_of_not_bddAbove hf

Depends on / 依赖: csSup_eq_univ_of_not_bddAbove
-/
lemma ciSup_eq_univ_of_not_bddAbove (hf : ¬BddAbove (range f)) : ⨆ i, f i = sSup univ :=
  csSup_eq_univ_of_not_bddAbove hf

/-- When every element of a set `s` is bounded by an element of a set `t`, and conversely, then
`s` and `t` have the same supremum. This holds even when the sets may be empty or unbounded. -/
@[to_dual
/-- When every element of a set `s` is bounded by an element of a set `t`, and conversely, then
`s` and `t` have the same infimum. This holds even when the sets may be empty or unbounded. -/]
/--
theorem `csSup_eq_csSup_of_forall_exists_le` / 定理 `csSup_eq_csSup_of_forall_exists_le`

English:
theorem csSup_eq_csSup_of_forall_exists_le
  statement: {s t : Set α}
  proof: by
  rcases eq_empty_or_nonempty s with rfl | s_ne
  · have : t = ∅ := eq_empty_of_forall_notMem (fun y yt => by simpa using ht y yt)
    rw [this]
  rcases eq_empty_or_nonempty t with rfl | t_ne
  · have : s = ∅ := eq_empty_of_forall_notMem (fun x xs => by simpa using hs x xs)
    rw [this]
  by_cases B : BddAbove s ∨ BddAbove t
  · have Bs : BddAbove s := by
      rcases B with hB | ⟨b, hb⟩
      · exact hB
      · refine ⟨b, fun x hx => ?_⟩
        rcases hs x hx with ⟨y, hy, hxy⟩
        exact hxy.trans (hb hy)
    have Bt : BddAbove t := by
      rcases B with ⟨b, hb⟩ | hB
      · refine ⟨b, fun y hy => ?_⟩
        rcases ht y hy with ⟨x, hx, hyx⟩
        exact hyx.trans (hb hx)
      · exact hB
    apply le_antisymm
    · apply csSup_le s_ne (fun x hx => ?_)
      rcases hs x hx with ⟨y, yt, hxy⟩
      exact hxy.trans (le_csSup Bt yt)
    · apply csSup_le t_ne (fun y hy => ?_)
      rcases ht y hy with ⟨x, xs, hyx⟩
      exact hyx.trans (le_csSup Bs xs)
  · simp [csSup_of_not_bddAbove, (not_or.1 B).1, (not_or.1 B).2]

@[to_dual le_csInf_union]

中文:
定理 csSup_eq_csSup_of_对任意_存在_le
  结论: {s t : 集合 α}
  证明: by
  rcases eq_empty_or_nonempty s with rfl | s_ne
  · have : t = ∅ := eq_empty_of_forall_notMem (fun y yt => by simpa using ht y yt)
    rw [this]
  rcases eq_empty_or_nonempty t with rfl | t_ne
  · have : s = ∅ := eq_empty_of_forall_notMem (fun x xs => by simpa using hs x xs)
    rw [this]
  by_cases B : BddAbove s ∨ BddAbove t
  · have Bs : BddAbove s := by
      rcases B with hB | ⟨b, hb⟩
      · exact hB
      · refine ⟨b, fun x hx => ?_⟩
        rcases hs x hx with ⟨y, hy, hxy⟩
        exact hxy.trans (hb hy)
    have Bt : BddAbove t := by
      rcases B with ⟨b, hb⟩ | hB
      · refine ⟨b, fun y hy => ?_⟩
        rcases ht y hy with ⟨x, hx, hyx⟩
        exact hyx.trans (hb hx)
      · exact hB
    apply le_antisymm
    · apply csSup_le s_ne (fun x hx => ?_)
      rcases hs x hx with ⟨y, yt, hxy⟩
      exact hxy.trans (le_csSup Bt yt)
    · apply csSup_le t_ne (fun y hy => ?_)
      rcases ht y hy with ⟨x, xs, hyx⟩
      exact hyx.trans (le_csSup Bs xs)
  · simp [csSup_of_not_bddAbove, (not_or.1 B).1, (not_or.1 B).2]

@[to_dual le_csInf_union]

Depends on / 依赖: BddAbove, eq_empty_of_forall_notMem, eq_empty_or_nonempty, hxy.trans, s_ne, t_ne
-/
theorem csSup_eq_csSup_of_forall_exists_le {s t : Set α}
    (hs : forall x in s, exists y in t, x <= y) (ht : forall y in t, exists x in s, y <= x) :
    sSup s = sSup t := by
  rcases eq_empty_or_nonempty s with rfl | s_ne
  · have : t = ∅ := eq_empty_of_forall_notMem (fun y yt => by simpa using ht y yt)
    rw [this]
  rcases eq_empty_or_nonempty t with rfl | t_ne
  · have : s = ∅ := eq_empty_of_forall_notMem (fun x xs => by simpa using hs x xs)
    rw [this]
  by_cases B : BddAbove s ∨ BddAbove t
  · have Bs : BddAbove s := by
      rcases B with hB | ⟨b, hb⟩
      · exact hB
      · refine ⟨b, fun x hx => ?_⟩
        rcases hs x hx with ⟨y, hy, hxy⟩
        exact hxy.trans (hb hy)
    have Bt : BddAbove t := by
      rcases B with ⟨b, hb⟩ | hB
      · refine ⟨b, fun y hy => ?_⟩
        rcases ht y hy with ⟨x, hx, hyx⟩
        exact hyx.trans (hb hx)
      · exact hB
    apply le_antisymm
    · apply csSup_le s_ne (fun x hx => ?_)
      rcases hs x hx with ⟨y, yt, hxy⟩
      exact hxy.trans (le_csSup Bt yt)
    · apply csSup_le t_ne (fun y hy => ?_)
      rcases ht y hy with ⟨x, xs, hyx⟩
      exact hyx.trans (le_csSup Bs xs)
  · simp [csSup_of_not_bddAbove, (not_or.1 B).1, (not_or.1 B).2]

@[to_dual le_csInf_union]
/--
theorem `csSup_union_le` / 定理 `csSup_union_le`

English:
theorem csSup_union_le
  given: (s t : Set α)
  statement: sSup (s union t) <= sSup s ⊔ sSup t
  proof: by
  rcases s.eq_empty_or_nonempty with (rfl | hs)
  · simp
  rcases t.eq_empty_or_nonempty with (rfl | ht)
  · simp
  by_cases BddAbove (s union t) <;>
    grind [csSup_union, bddAbove_union, csSup_of_not_bddAbove]

@[to_dual]

中文:
定理 csSup_union_le
  条件: (s t : 集合 α)
  结论: sSup (s union t) <= sSup s ⊔ sSup t
  证明: by
  rcases s.eq_empty_or_nonempty with (rfl | hs)
  · simp
  rcases t.eq_empty_or_nonempty with (rfl | ht)
  · simp
  by_cases BddAbove (s union t) <;>
    grind [csSup_union, bddAbove_union, csSup_of_not_bddAbove]

@[to_dual]

Depends on / 依赖: BddAbove, bddAbove_union, csSup_of_not_bddAbove, csSup_union, eq_empty_or_nonempty, s.eq_empty_or_nonempty, t.eq_empty_or_nonempty
-/
theorem csSup_union_le (s t : Set α) : sSup (s union t) <= sSup s ⊔ sSup t := by
  rcases s.eq_empty_or_nonempty with (rfl | hs)
  · simp
  rcases t.eq_empty_or_nonempty with (rfl | ht)
  · simp
  by_cases BddAbove (s union t) <;>
    grind [csSup_union, bddAbove_union, csSup_of_not_bddAbove]

@[to_dual]
/--
lemma `sSup_iUnion_Iic` / 引理 `sSup_iUnion_Iic`

English:
lemma sSup_iUnion_Iic
  given: (f : ι -> α)
  statement: sSup (⋃ (i : ι), Iic (f i)) = ⨆ i, f i
  proof: by
  apply csSup_eq_csSup_of_forall_exists_le
  · rintro x ⟨-, ⟨i, rfl⟩, hi⟩
    exact ⟨f i, mem_range_self _, hi⟩
  · rintro x ⟨i, rfl⟩
    exact ⟨f i, mem_iUnion_of_mem i le_rfl, le_rfl⟩

@[to_dual]

中文:
引理 sSup_iUnion_Iic
  条件: (f : ι -> α)
  结论: sSup (⋃ (i : ι), 左无界右闭区间 (f i)) = ⨆ i, f i
  证明: by
  apply csSup_eq_csSup_of_forall_exists_le
  · rintro x ⟨-, ⟨i, rfl⟩, hi⟩
    exact ⟨f i, mem_range_self _, hi⟩
  · rintro x ⟨i, rfl⟩
    exact ⟨f i, mem_iUnion_of_mem i le_rfl, le_rfl⟩

@[to_dual]

Depends on / 依赖: csSup_eq_csSup_of_forall_exists_le, le_rfl, mem_iUnion_of_mem, mem_range_self
-/
lemma sSup_iUnion_Iic (f : ι -> α) : sSup (⋃ (i : ι), Iic (f i)) = ⨆ i, f i := by
  apply csSup_eq_csSup_of_forall_exists_le
  · rintro x ⟨-, ⟨i, rfl⟩, hi⟩
    exact ⟨f i, mem_range_self _, hi⟩
  · rintro x ⟨i, rfl⟩
    exact ⟨f i, mem_iUnion_of_mem i le_rfl, le_rfl⟩

@[to_dual]
/--
theorem `csSup_eq_top_of_top_mem` / 定理 `csSup_eq_top_of_top_mem`

English:
theorem csSup_eq_top_of_top_mem
  given: [OrderTop α] {s : Set α} (hs : ⊤ in s)
  statement: sSup s = ⊤
  proof: eq_top_iff.2 le_csSup (OrderTop.bddAbove s) hs

中文:
定理 csSup_eq_top_of_top_mem
  条件: [有顶序 α] {s : 集合 α} (hs : ⊤ in s)
  结论: sSup s = ⊤
  证明: eq_top_iff.2 le_csSup (OrderTop.bddAbove s) hs

Depends on / 依赖: OrderTop, OrderTop.bddAbove, bddAbove, eq_top_iff, le_csSup
-/
theorem csSup_eq_top_of_top_mem [OrderTop α] {s : Set α} (hs : ⊤ in s) : sSup s = ⊤ :=
eq_top_iff.2 le_csSup (OrderTop.bddAbove s) hs

open Function

variable [WellFoundedLT α]

/--
theorem `sInf_eq_argmin_on` / 定理 `sInf_eq_argmin_on`

English:
theorem sInf_eq_argmin_on
  given: (hs : s.Nonempty)
  statement: sInf s = argminOn id s hs
  proof: IsLeast.csInf_eq ⟨argminOn_mem _ _ _, fun _ ha => argminOn_le id _ ha⟩

中文:
定理 sInf_eq_argmin_on
  条件: (hs : s.非空)
  结论: sInf s = argminOn id s hs
  证明: IsLeast.csInf_eq ⟨argminOn_mem _ _ _, fun _ ha => argminOn_le id _ ha⟩

Depends on / 依赖: IsLeast, IsLeast.csInf_eq, argminOn_le, argminOn_mem, csInf_eq
-/
theorem sInf_eq_argmin_on (hs : s.Nonempty) : sInf s = argminOn id s hs :=
  IsLeast.csInf_eq ⟨argminOn_mem _ _ _, fun _ ha => argminOn_le id _ ha⟩

/--
theorem `isLeast_csInf` / 定理 `isLeast_csInf`

English:
theorem isLeast_csInf
  given: (hs : s.Nonempty)
  statement: IsLeast s (sInf s)
  proof: by
  rw [sInf_eq_argmin_on hs]
  exact ⟨argminOn_mem _ _ _, fun a ha => argminOn_le id _ ha⟩

中文:
定理 isLeast_csInf
  条件: (hs : s.非空)
  结论: IsLeast s (sInf s)
  证明: by
  rw [sInf_eq_argmin_on hs]
  exact ⟨argminOn_mem _ _ _, fun a ha => argminOn_le id _ ha⟩

Depends on / 依赖: argminOn_le, argminOn_mem, sInf_eq_argmin_on
-/
theorem isLeast_csInf (hs : s.Nonempty) : IsLeast s (sInf s) := by
  rw [sInf_eq_argmin_on hs]
  exact ⟨argminOn_mem _ _ _, fun a ha => argminOn_le id _ ha⟩

/--
theorem `le_csInf_iff'` / 定理 `le_csInf_iff'`

English:
theorem le_csInf_iff'
  given: (hs : s.Nonempty)
  statement: b <= sInf s ↔ b in lowerBounds s
  proof: le_isGLB_iff (isLeast_csInf hs).isGLB

中文:
定理 le_csInf_iff'
  条件: (hs : s.非空)
  结论: b <= sInf s ↔ b in lowerBounds s
  证明: le_isGLB_iff (isLeast_csInf hs).isGLB

Depends on / 依赖: isLeast_csInf, le_isGLB_iff
-/
theorem le_csInf_iff' (hs : s.Nonempty) : b <= sInf s ↔ b in lowerBounds s :=
  le_isGLB_iff (isLeast_csInf hs).isGLB

/--
theorem `csInf_mem` / 定理 `csInf_mem`

English:
theorem csInf_mem
  given: (hs : s.Nonempty)
  statement: sInf s in s
  proof: (isLeast_csInf hs).1

中文:
定理 csInf_mem
  条件: (hs : s.非空)
  结论: sInf s in s
  证明: (isLeast_csInf hs).1

Depends on / 依赖: isLeast_csInf
-/
theorem csInf_mem (hs : s.Nonempty) : sInf s in s :=
  (isLeast_csInf hs).1

/--
lemma `csInf_eq_iff` / 引理 `csInf_eq_iff`

English:
lemma csInf_eq_iff
  given: (hs : s.Nonempty) (n : α)
  proof: by
  have : OrderBot α := WellFoundedLT.toOrderBot α
  constructor
  · intro rfl
    exact ⟨csInf_mem hs, fun _ => csInf_le (OrderBot.bddBelow s)⟩
  · intro ⟨hn, hle⟩
    exact le_antisymm (csInf_le (OrderBot.bddBelow s) hn) (le_csInf hs hle)

中文:
引理 csInf_eq_iff
  条件: (hs : s.非空) (n : α)
  证明: by
  have : OrderBot α := WellFoundedLT.toOrderBot α
  constructor
  · intro rfl
    exact ⟨csInf_mem hs, fun _ => csInf_le (OrderBot.bddBelow s)⟩
  · intro ⟨hn, hle⟩
    exact le_antisymm (csInf_le (OrderBot.bddBelow s) hn) (le_csInf hs hle)

Depends on / 依赖: OrderBot, OrderBot.bddBelow, WellFoundedLT, WellFoundedLT.toOrderBot, bddBelow, csInf_le, csInf_mem, le_antisymm, le_csInf, toOrderBot
-/
lemma csInf_eq_iff (hs : s.Nonempty) (n : α) :
     sInf s = n ↔ n in s ∧ forall a in s, n <= a := by
  have : OrderBot α := WellFoundedLT.toOrderBot α
  constructor
  · intro rfl
    exact ⟨csInf_mem hs, fun _ => csInf_le (OrderBot.bddBelow s)⟩
  · intro ⟨hn, hle⟩
    exact le_antisymm (csInf_le (OrderBot.bddBelow s) hn) (le_csInf hs hle)

/--
theorem `MonotoneOn.map_csInf` / 定理 `MonotoneOn.map_csInf`

English:
theorem MonotoneOn.map_csInf
  statement: {β : Type*} [ConditionallyCompleteLattice β] {f : α -> β}
  proof: (hf.map_isLeast (isLeast_csInf hs)).csInf_eq.symm

中文:
定理 MonotoneOn.map_csInf
  结论: {β : 类型} [条件完备格 β] {f : α -> β}
  证明: (hf.map_isLeast (isLeast_csInf hs)).csInf_eq.symm

Depends on / 依赖: csInf_eq, csInf_eq.symm, hf.map_isLeast, isLeast_csInf, map_isLeast
-/
theorem MonotoneOn.map_csInf {β : Type*} [ConditionallyCompleteLattice β] {f : α -> β}
    (hf : MonotoneOn f s) (hs : s.Nonempty) : f (sInf s) = sInf (f '' s) :=
  (hf.map_isLeast (isLeast_csInf hs)).csInf_eq.symm

/--
theorem `Monotone.map_csInf` / 定理 `Monotone.map_csInf`

English:
theorem Monotone.map_csInf
  statement: {β : Type*} [ConditionallyCompleteLattice β] {f : α -> β}
  proof: (hf.map_isLeast (isLeast_csInf hs)).csInf_eq.symm

中文:
定理 递增.map_csInf
  结论: {β : 类型} [条件完备格 β] {f : α -> β}
  证明: (hf.map_isLeast (isLeast_csInf hs)).csInf_eq.symm

Depends on / 依赖: csInf_eq, csInf_eq.symm, hf.map_isLeast, isLeast_csInf, map_isLeast
-/
theorem Monotone.map_csInf {β : Type*} [ConditionallyCompleteLattice β] {f : α -> β}
    (hf : Monotone f) (hs : s.Nonempty) : f (sInf s) = sInf (f '' s) :=
  (hf.map_isLeast (isLeast_csInf hs)).csInf_eq.symm

end ConditionallyCompleteLinearOrder

/-!
### Lemmas about a conditionally complete linear order with bottom element

In this case we have `Sup ∅ = ⊥`, so we can drop some `Nonempty`/`Set.Nonempty` assumptions.
-/


section ConditionallyCompleteLinearOrderBot

@[simp]
/--
theorem `csInf_univ` / 定理 `csInf_univ`

English:
theorem csInf_univ
  given: [ConditionallyCompleteLattice α] [OrderBot α]
  statement: sInf (univ : Set α) = ⊥
  proof: isLeast_univ.csInf_eq

中文:
定理 csInf_univ
  条件: [条件完备格 α] [有底序 α]
  结论: sInf (univ : 集合 α) = ⊥
  证明: isLeast_univ.csInf_eq

Depends on / 依赖: csInf_eq, isLeast_univ, isLeast_univ.csInf_eq
-/
theorem csInf_univ [ConditionallyCompleteLattice α] [OrderBot α] : sInf (univ : Set α) = ⊥ :=
  isLeast_univ.csInf_eq

variable [ConditionallyCompleteLinearOrderBot α] {s : Set α} {a : α}

@[simp]
/--
theorem `csSup_empty` / 定理 `csSup_empty`

English:
theorem csSup_empty
  statement: (sSup ∅ : α) = ⊥
  proof: ConditionallyCompleteLinearOrderBot.csSup_empty

中文:
定理 csSup_empty
  结论: (sSup ∅ : α) = ⊥
  证明: ConditionallyCompleteLinearOrderBot.csSup_empty

Depends on / 依赖: ConditionallyCompleteLinearOrderBot, ConditionallyCompleteLinearOrderBot.csSup_empty, csSup_empty
-/
theorem csSup_empty : (sSup ∅ : α) = ⊥ :=
  ConditionallyCompleteLinearOrderBot.csSup_empty

/--
theorem `isLUB_csSup'` / 定理 `isLUB_csSup'`

English:
theorem isLUB_csSup'
  given: {s : Set α} (hs : BddAbove s)
  statement: IsLUB s (sSup s)
  proof: by
  rcases eq_empty_or_nonempty s with (rfl | hne)
  · simp only [csSup_empty, isLUB_empty]
  · exact isLUB_csSup hne hs

中文:
定理 isLUB_csSup'
  条件: {s : 集合 α} (hs : BddAbove s)
  结论: IsLUB s (sSup s)
  证明: by
  rcases eq_empty_or_nonempty s with (rfl | hne)
  · simp only [csSup_empty, isLUB_empty]
  · exact isLUB_csSup hne hs

Depends on / 依赖: csSup_empty, eq_empty_or_nonempty, isLUB_csSup, isLUB_empty
-/
theorem isLUB_csSup' {s : Set α} (hs : BddAbove s) : IsLUB s (sSup s) := by
  rcases eq_empty_or_nonempty s with (rfl | hne)
  · simp only [csSup_empty, isLUB_empty]
  · exact isLUB_csSup hne hs

/--
theorem `csSup_le_iff'` / 定理 `csSup_le_iff'`

English:
theorem csSup_le_iff'
  given: {s : Set α} (hs : BddAbove s) {a : α}
  statement: sSup s <= a ↔ forall x in s, x <= a
  proof: isLUB_le_iff (isLUB_csSup' hs)

中文:
定理 csSup_le_iff'
  条件: {s : 集合 α} (hs : BddAbove s) {a : α}
  结论: sSup s <= a ↔ 对任意 x in s, x <= a
  证明: isLUB_le_iff (isLUB_csSup' hs)

Depends on / 依赖: isLUB_csSup, isLUB_le_iff
-/
theorem csSup_le_iff' {s : Set α} (hs : BddAbove s) {a : α} : sSup s <= a ↔ forall x in s, x <= a :=
  isLUB_le_iff (isLUB_csSup' hs)

/--
theorem `csSup_le'` / 定理 `csSup_le'`

English:
theorem csSup_le'
  given: {s : Set α} {a : α} (h : a in upperBounds s)
  statement: sSup s <= a
  proof: (csSup_le_iff' ⟨a, h⟩).2 h

中文:
定理 csSup_le'
  条件: {s : 集合 α} {a : α} (h : a in upperBounds s)
  结论: sSup s <= a
  证明: (csSup_le_iff' ⟨a, h⟩).2 h

Depends on / 依赖: csSup_le_iff
-/
theorem csSup_le' {s : Set α} {a : α} (h : a in upperBounds s) : sSup s <= a :=
  (csSup_le_iff' ⟨a, h⟩).2 h

/--
theorem `lt_csSup_iff'` / 定理 `lt_csSup_iff'`

English:
theorem lt_csSup_iff'
  given: (hb : BddAbove s)
  statement: a < sSup s ↔ exists b in s, a < b
  proof: by
  simpa only [not_le, not_forall₂, exists_prop] using (csSup_le_iff' hb).not

中文:
定理 lt_csSup_iff'
  条件: (hb : BddAbove s)
  结论: a < sSup s ↔ 存在 b in s, a < b
  证明: by
  simpa only [not_le, not_forall₂, exists_prop] using (csSup_le_iff' hb).not

Depends on / 依赖: csSup_le_iff, exists_prop, not_le
-/
theorem lt_csSup_iff' (hb : BddAbove s) : a < sSup s ↔ exists b in s, a < b := by
  simpa only [not_le, not_forall₂, exists_prop] using (csSup_le_iff' hb).not

/--
theorem `le_csSup_iff'` / 定理 `le_csSup_iff'`

English:
theorem le_csSup_iff'
  given: {s : Set α} {a : α} (h : BddAbove s)
  proof: ⟨fun h _ hb => le_trans h (csSup_le' hb), fun hb => hb _ fun _ => le_csSup h⟩

中文:
定理 le_csSup_iff'
  条件: {s : 集合 α} {a : α} (h : BddAbove s)
  证明: ⟨fun h _ hb => le_trans h (csSup_le' hb), fun hb => hb _ fun _ => le_csSup h⟩

Depends on / 依赖: csSup_le, f.hom, le_csSup, le_trans
-/
theorem le_csSup_iff' {s : Set α} {a : α} (h : BddAbove s) :
    a <= sSup s ↔ forall b, b in upperBounds s -> a <= b :=
  ⟨fun h _ hb => le_trans h (csSup_le' hb), fun hb => hb _ fun _ => le_csSup h⟩

/--
theorem `le_csInf_iff''` / 定理 `le_csInf_iff''`

English:
theorem le_csInf_iff''
  given: {s : Set α} {a : α} (ne : s.Nonempty)
  proof: le_csInf_iff (OrderBot.bddBelow _) ne

中文:
定理 le_csInf_iff''
  条件: {s : 集合 α} {a : α} (ne : s.非空)
  证明: le_csInf_iff (OrderBot.bddBelow _) ne

Depends on / 依赖: OrderBot, OrderBot.bddBelow, bddBelow, le_csInf_iff
-/
theorem le_csInf_iff'' {s : Set α} {a : α} (ne : s.Nonempty) :
    a <= sInf s ↔ forall b : α, b in s -> a <= b :=
  le_csInf_iff (OrderBot.bddBelow _) ne

/--
theorem `csInf_le'` / 定理 `csInf_le'`

English:
theorem csInf_le'
  given: (h : a in s)
  statement: sInf s <= a
  proof: csInf_le (OrderBot.bddBelow _) h

中文:
定理 csInf_le'
  条件: (h : a in s)
  结论: sInf s <= a
  证明: csInf_le (OrderBot.bddBelow _) h

Depends on / 依赖: OrderBot, OrderBot.bddBelow, bddBelow, csInf_le
-/
theorem csInf_le' (h : a in s) : sInf s <= a := csInf_le (OrderBot.bddBelow _) h

/--
theorem `exists_lt_of_lt_csSup'` / 定理 `exists_lt_of_lt_csSup'`

English:
theorem exists_lt_of_lt_csSup'
  given: {s : Set α} {a : α} (h : a < sSup s)
  statement: exists b in s, a < b
  proof: by
  contrapose! h
  exact csSup_le' h

中文:
定理 存在_lt_of_lt_csSup'
  条件: {s : 集合 α} {a : α} (h : a < sSup s)
  结论: 存在 b in s, a < b
  证明: by
  contrapose! h
  exact csSup_le' h

Depends on / 依赖: contrapose, csSup_le
-/
theorem exists_lt_of_lt_csSup' {s : Set α} {a : α} (h : a < sSup s) : exists b in s, a < b := by
  contrapose! h
  exact csSup_le' h

/--
theorem `notMem_of_lt_csInf'` / 定理 `notMem_of_lt_csInf'`

English:
theorem notMem_of_lt_csInf'
  given: {x : α} {s : Set α} (h : x < sInf s)
  statement: x ∉ s
  proof: notMem_of_lt_csInf h (OrderBot.bddBelow s)

@[gcongr mid]

中文:
定理 notMem_of_lt_csInf'
  条件: {x : α} {s : 集合 α} (h : x < sInf s)
  结论: x ∉ s
  证明: notMem_of_lt_csInf h (OrderBot.bddBelow s)

@[gcongr mid]

Depends on / 依赖: OrderBot, OrderBot.bddBelow, bddBelow, notMem_of_lt_csInf
-/
theorem notMem_of_lt_csInf' {x : α} {s : Set α} (h : x < sInf s) : x ∉ s :=
  notMem_of_lt_csInf h (OrderBot.bddBelow s)

@[gcongr mid]
/--
theorem `csInf_le_csInf'` / 定理 `csInf_le_csInf'`

English:
theorem csInf_le_csInf'
  given: {s t : Set α} (h₁ : t.Nonempty) (h₂ : t subseteq s)
  statement: sInf s <= sInf t
  proof: csInf_le_csInf (OrderBot.bddBelow s) h₁ h₂

@[gcongr mid]

中文:
定理 csInf_le_csInf'
  条件: {s t : 集合 α} (h₁ : t.非空) (h₂ : t subseteq s)
  结论: sInf s <= sInf t
  证明: csInf_le_csInf (OrderBot.bddBelow s) h₁ h₂

@[gcongr mid]

Depends on / 依赖: OrderBot, OrderBot.bddBelow, bddBelow, csInf_le_csInf, fast_instance, hom_injective, hom_injective.module, module
-/
theorem csInf_le_csInf' {s t : Set α} (h₁ : t.Nonempty) (h₂ : t subseteq s) : sInf s <= sInf t :=
  csInf_le_csInf (OrderBot.bddBelow s) h₁ h₂

@[gcongr mid]
/--
theorem `csSup_le_csSup'` / 定理 `csSup_le_csSup'`

English:
theorem csSup_le_csSup'
  given: {s t : Set α} (h₁ : BddAbove t) (h₂ : s subseteq t)
  statement: sSup s <= sSup t
  proof: by
  rcases eq_empty_or_nonempty s with rfl | h
  · rw [csSup_empty]
    exact bot_le
  · exact csSup_le_csSup h₁ h h₂

中文:
定理 csSup_le_csSup'
  条件: {s t : 集合 α} (h₁ : BddAbove t) (h₂ : s subseteq t)
  结论: sSup s <= sSup t
  证明: by
  rcases eq_empty_or_nonempty s with rfl | h
  · rw [csSup_empty]
    exact bot_le
  · exact csSup_le_csSup h₁ h h₂

Depends on / 依赖: bot_le, csSup_empty, csSup_le_csSup, eq_empty_or_nonempty
-/
theorem csSup_le_csSup' {s t : Set α} (h₁ : BddAbove t) (h₂ : s subseteq t) : sSup s <= sSup t := by
  rcases eq_empty_or_nonempty s with rfl | h
  · rw [csSup_empty]
    exact bot_le
  · exact csSup_le_csSup h₁ h h₂

variable {t : Set α}

/--
theorem `csSup_union'` / 定理 `csSup_union'`

English:
theorem csSup_union'
  given: (hs : BddAbove s := by bddDefault) (ht : BddAbove t := by bddDefault)
  proof: by
  rcases s.eq_empty_or_nonempty with (rfl | hne)
  · simp
  exact (isLUB_csSup' hs |>.union <| isLUB_csSup' ht).csSup_eq hne.inl

中文:
定理 csSup_union'
  条件: (hs : BddAbove s := by bddDefault) (ht : BddAbove t := by bddDefault)
  证明: by
  rcases s.eq_empty_or_nonempty with (rfl | hne)
  · simp
  exact (isLUB_csSup' hs |>.union <| isLUB_csSup' ht).csSup_eq hne.inl

Depends on / 依赖: BddAbove, bddDefault, csSup_eq, eq_empty_or_nonempty, hne.inl, isLUB_csSup, s.eq_empty_or_nonempty
-/
theorem csSup_union' (hs : BddAbove s := by bddDefault) (ht : BddAbove t := by bddDefault) :
    sSup (s union t) = sSup s ⊔ sSup t := by
  rcases s.eq_empty_or_nonempty with (rfl | hne)
  · simp
  exact (isLUB_csSup' hs |>.union <| isLUB_csSup' ht).csSup_eq hne.inl

/--
theorem `csSup_inter_le'` / 定理 `csSup_inter_le'`

English:
theorem csSup_inter_le'
  given: (hs : BddAbove s := by bddDefault) (ht : BddAbove t := by bddDefault)
  proof: csSup_le' fun _ hx => le_inf (le_csSup hs hx.left) (le_csSup ht hx.right)

中文:
定理 csSup_inter_le'
  条件: (hs : BddAbove s := by bddDefault) (ht : BddAbove t := by bddDefault)
  证明: csSup_le' fun _ hx => le_inf (le_csSup hs hx.left) (le_csSup ht hx.right)

Depends on / 依赖: BddAbove, bddDefault, csSup_le, hx.left, hx.right, le_csSup, le_inf
-/
theorem csSup_inter_le' (hs : BddAbove s := by bddDefault) (ht : BddAbove t := by bddDefault) :
    sSup (s inter t) <= sSup s ⊓ sSup t :=
  csSup_le' fun _ hx => le_inf (le_csSup hs hx.left) (le_csSup ht hx.right)

/--
theorem `csSup_insert'` / 定理 `csSup_insert'`

English:
theorem csSup_insert'
  given: (hs : BddAbove s := by bddDefault)
  statement: sSup (insert a s) = a ⊔ sSup s
  proof: .csSup_eq insert_nonempty a s .insert a isLUB_csSup' hs

中文:
定理 csSup_insert'
  条件: (hs : BddAbove s := by bddDefault)
  结论: sSup (insert a s) = a ⊔ sSup s
  证明: .csSup_eq insert_nonempty a s .insert a isLUB_csSup' hs

Depends on / 依赖: bddDefault, csSup_eq, insert, insert_nonempty, isLUB_csSup
-/
theorem csSup_insert' (hs : BddAbove s := by bddDefault) : sSup (insert a s) = a ⊔ sSup s :=
.csSup_eq insert_nonempty a s .insert a isLUB_csSup' hs

end ConditionallyCompleteLinearOrderBot

namespace WithTop

variable [ConditionallyCompleteLinearOrderBot α]

/-- The `sSup` of a non-empty set is its least upper bound for a conditionally
complete lattice with a top. -/
@[to_dual]
/--
theorem `isLUB_sSup'` / 定理 `isLUB_sSup'`

English:
theorem isLUB_sSup'
  statement: {β : Type*} [ConditionallyCompleteLattice β] {s : Set (WithTop β)}
  proof: by
  classical
  constructor
  · change ite _ _ _ in _
    split_ifs with h₁ h₂
    · intro _ _
      exact le_top
    · rintro (⟨⟩ | a) ha
      · contradiction
      apply coe_le_coe.2
      exact le_csSup h₂ ha
    · intro _ _
      exact le_top
  · change ite _ _ _ in _
    split_ifs with h₁ h₂
    · rintro (⟨⟩ | a) ha
      · exact le_rfl
      · exact False.elim (not_top_le_coe a (ha h₁))
    · rintro (⟨⟩ | b) hb
      · exact le_top
      refine coe_le_coe.2 (csSup_le ?_ ?_)
      · rcases hs with ⟨⟨⟩ | b, hb⟩
        · exact absurd hb h₁
        · exact ⟨b, hb⟩
      · intro a ha
        exact coe_le_coe.1 (hb ha)
    · rintro (⟨⟩ | b) hb
      · exact le_rfl
      · exfalso
        apply h₂
        use b
        intro a ha
        exact coe_le_coe.1 (hb ha)

中文:
定理 isLUB_sSup'
  结论: {β : 类型} [条件完备格 β] {s : 集合 (WithTop β)}
  证明: by
  classical
  constructor
  · change ite _ _ _ in _
    split_ifs with h₁ h₂
    · intro _ _
      exact le_top
    · rintro (⟨⟩ | a) ha
      · contradiction
      apply coe_le_coe.2
      exact le_csSup h₂ ha
    · intro _ _
      exact le_top
  · change ite _ _ _ in _
    split_ifs with h₁ h₂
    · rintro (⟨⟩ | a) ha
      · exact le_rfl
      · exact False.elim (not_top_le_coe a (ha h₁))
    · rintro (⟨⟩ | b) hb
      · exact le_top
      refine coe_le_coe.2 (csSup_le ?_ ?_)
      · rcases hs with ⟨⟨⟩ | b, hb⟩
        · exact absurd hb h₁
        · exact ⟨b, hb⟩
      · intro a ha
        exact coe_le_coe.1 (hb ha)
    · rintro (⟨⟩ | b) hb
      · exact le_rfl
      · exfalso
        apply h₂
        use b
        intro a ha
        exact coe_le_coe.1 (hb ha)

Depends on / 依赖: False.elim, absurd, classical, coe_le_coe, csSup_le, le_csSup, le_rfl, le_top, not_top_le_coe, split_ifs
-/
theorem isLUB_sSup' {β : Type*} [ConditionallyCompleteLattice β] {s : Set (WithTop β)}
    (hs : s.Nonempty) : IsLUB s (sSup s) := by
  classical
  constructor
  · change ite _ _ _ in _
    split_ifs with h₁ h₂
    · intro _ _
      exact le_top
    · rintro (⟨⟩ | a) ha
      · contradiction
      apply coe_le_coe.2
      exact le_csSup h₂ ha
    · intro _ _
      exact le_top
  · change ite _ _ _ in _
    split_ifs with h₁ h₂
    · rintro (⟨⟩ | a) ha
      · exact le_rfl
      · exact False.elim (not_top_le_coe a (ha h₁))
    · rintro (⟨⟩ | b) hb
      · exact le_top
      refine coe_le_coe.2 (csSup_le ?_ ?_)
      · rcases hs with ⟨⟨⟩ | b, hb⟩
        · exact absurd hb h₁
        · exact ⟨b, hb⟩
      · intro a ha
        exact coe_le_coe.1 (hb ha)
    · rintro (⟨⟩ | b) hb
      · exact le_rfl
      · exfalso
        apply h₂
        use b
        intro a ha
        exact coe_le_coe.1 (hb ha)

/--
theorem `isLUB_sSup` / 定理 `isLUB_sSup`

English:
theorem isLUB_sSup
  given: (s : Set (WithTop α))
  statement: IsLUB s (sSup s)
  proof: by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp [sSup]
  · exact isLUB_sSup' hs

中文:
定理 isLUB_sSup
  条件: (s : 集合 (WithTop α))
  结论: IsLUB s (sSup s)
  证明: by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp [sSup]
  · exact isLUB_sSup' hs

Depends on / 依赖: eq_empty_or_nonempty, isLUB_sSup, s.eq_empty_or_nonempty
-/
theorem isLUB_sSup (s : Set (WithTop α)) : IsLUB s (sSup s) := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp [sSup]
  · exact isLUB_sSup' hs

/-- The `sInf` of a bounded-below set is its greatest lower bound for a conditionally
complete lattice with a top. -/
@[to_dual]
/--
theorem `isGLB_sInf'` / 定理 `isGLB_sInf'`

English:
theorem isGLB_sInf'
  statement: {β : Type*} [ConditionallyCompleteLattice β] {s : Set (WithTop β)}
  proof: by
  classical
  constructor
  · change ite _ _ _ in _
    simp only [hs, not_true_eq_false, or_false]
    split_ifs with h
    · intro a ha
      exact top_le_iff.2 (Set.mem_singleton_iff.1 (h ha))
    · rintro (⟨⟩ | a) ha
      · exact le_top
      refine coe_le_coe.2 (csInf_le ?_ ha)
      rcases hs with ⟨⟨⟩ | b, hb⟩
      · exfalso
        apply h
        intro c hc
        rw [mem_singleton_iff]; rw [← top_le_iff]
        exact hb hc
      use b
      intro c hc
      exact coe_le_coe.1 (hb hc)
  · change ite _ _ _ in _
    simp only [hs, not_true_eq_false, or_false]
    split_ifs with h
    · intro _ _
      exact le_top
    · rintro (⟨⟩ | a) ha
      · exfalso
        apply h
        intro b hb
        exact Set.mem_singleton_iff.2 (top_le_iff.1 (ha hb))
      · refine coe_le_coe.2 (le_csInf ?_ ?_)
        · classical
            contrapose! h
            rintro (⟨⟩ | a) ha
            · exact mem_singleton ⊤
            · exact (not_nonempty_iff_eq_empty.2 h ⟨a, ha⟩).elim
        · intro b hb
          rw [← coe_le_coe]
          exact ha hb

中文:
定理 isGLB_sInf'
  结论: {β : 类型} [条件完备格 β] {s : 集合 (WithTop β)}
  证明: by
  classical
  constructor
  · change ite _ _ _ in _
    simp only [hs, not_true_eq_false, or_false]
    split_ifs with h
    · intro a ha
      exact top_le_iff.2 (Set.mem_singleton_iff.1 (h ha))
    · rintro (⟨⟩ | a) ha
      · exact le_top
      refine coe_le_coe.2 (csInf_le ?_ ha)
      rcases hs with ⟨⟨⟩ | b, hb⟩
      · exfalso
        apply h
        intro c hc
        rw [mem_singleton_iff]; rw [← top_le_iff]
        exact hb hc
      use b
      intro c hc
      exact coe_le_coe.1 (hb hc)
  · change ite _ _ _ in _
    simp only [hs, not_true_eq_false, or_false]
    split_ifs with h
    · intro _ _
      exact le_top
    · rintro (⟨⟩ | a) ha
      · exfalso
        apply h
        intro b hb
        exact Set.mem_singleton_iff.2 (top_le_iff.1 (ha hb))
      · refine coe_le_coe.2 (le_csInf ?_ ?_)
        · classical
            contrapose! h
            rintro (⟨⟩ | a) ha
            · exact mem_singleton ⊤
            · exact (not_nonempty_iff_eq_empty.2 h ⟨a, ha⟩).elim
        · intro b hb
          rw [← coe_le_coe]
          exact ha hb

Depends on / 依赖: Set.mem_singleton_iff, classical, coe_le_coe, csInf_le, le_top, mem_singleton_iff, not_true_eq_false, or_false, split_ifs, top_le_iff
-/
theorem isGLB_sInf' {β : Type*} [ConditionallyCompleteLattice β] {s : Set (WithTop β)}
    (hs : BddBelow s) : IsGLB s (sInf s) := by
  classical
  constructor
  · change ite _ _ _ in _
    simp only [hs, not_true_eq_false, or_false]
    split_ifs with h
    · intro a ha
      exact top_le_iff.2 (Set.mem_singleton_iff.1 (h ha))
    · rintro (⟨⟩ | a) ha
      · exact le_top
      refine coe_le_coe.2 (csInf_le ?_ ha)
      rcases hs with ⟨⟨⟩ | b, hb⟩
      · exfalso
        apply h
        intro c hc
        rw [mem_singleton_iff]; rw [← top_le_iff]
        exact hb hc
      use b
      intro c hc
      exact coe_le_coe.1 (hb hc)
  · change ite _ _ _ in _
    simp only [hs, not_true_eq_false, or_false]
    split_ifs with h
    · intro _ _
      exact le_top
    · rintro (⟨⟩ | a) ha
      · exfalso
        apply h
        intro b hb
        exact Set.mem_singleton_iff.2 (top_le_iff.1 (ha hb))
      · refine coe_le_coe.2 (le_csInf ?_ ?_)
        · classical
            contrapose! h
            rintro (⟨⟩ | a) ha
            · exact mem_singleton ⊤
            · exact (not_nonempty_iff_eq_empty.2 h ⟨a, ha⟩).elim
        · intro b hb
          rw [← coe_le_coe]
          exact ha hb

/--
theorem `isGLB_sInf` / 定理 `isGLB_sInf`

English:
theorem isGLB_sInf
  given: (s : Set (WithTop α))
  statement: IsGLB s (sInf s)
  proof: by
  by_cases hs : BddBelow s
  · exact isGLB_sInf' hs
  · exact isGLB_sInf' (OrderBot.bddBelow _)

中文:
定理 isGLB_sInf
  条件: (s : 集合 (WithTop α))
  结论: IsGLB s (sInf s)
  证明: by
  by_cases hs : BddBelow s
  · exact isGLB_sInf' hs
  · exact isGLB_sInf' (OrderBot.bddBelow _)

Depends on / 依赖: BddBelow, OrderBot, OrderBot.bddBelow, bddBelow, isGLB_sInf
-/
theorem isGLB_sInf (s : Set (WithTop α)) : IsGLB s (sInf s) := by
  by_cases hs : BddBelow s
  · exact isGLB_sInf' hs
  · exact isGLB_sInf' (OrderBot.bddBelow _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteLinearOrder (WithTop α)
  body: linearOrder
  __ := linearOrder.toBiheytingAlgebra
  isLUB_sSup := isLUB_sSup
  isGLB_sInf := isGLB_sInf

中文:
实例 :
  签名: 完备线性序 (WithTop α)
  定义体: linearOrder
  __ := linearOrder.toBiheytingAlgebra
  isLUB_sSup := isLUB_sSup
  isGLB_sInf := isGLB_sInf

Depends on / 依赖: linearOrder
-/
noncomputable instance : CompleteLinearOrder (WithTop α) where
  __ := linearOrder
  __ := linearOrder.toBiheytingAlgebra
  isLUB_sSup := isLUB_sSup
  isGLB_sInf := isGLB_sInf

/-- A version of `WithTop.coe_sSup'` with a more convenient but less general statement. -/
@[norm_cast]
/--
theorem `coe_sSup` / 定理 `coe_sSup`

English:
theorem coe_sSup
  given: {s : Set α} (hb : BddAbove s)
  statement: ↑(sSup s) = (⨆ a in s, ↑a : WithTop α)
  proof: by
  rw [coe_sSup' hb]; rw [sSup_image]

中文:
定理 coe_sSup
  条件: {s : 集合 α} (hb : BddAbove s)
  结论: ↑(sSup s) = (⨆ a in s, ↑a : WithTop α)
  证明: by
  rw [coe_sSup' hb]; rw [sSup_image]

Depends on / 依赖: coe_sSup, sSup_image
-/
theorem coe_sSup {s : Set α} (hb : BddAbove s) : ↑(sSup s) = (⨆ a in s, ↑a : WithTop α) := by
  rw [coe_sSup' hb]; rw [sSup_image]

/-- A version of `WithTop.coe_sInf'` with a more convenient but less general statement. -/
@[norm_cast]
/--
theorem `coe_sInf` / 定理 `coe_sInf`

English:
theorem coe_sInf
  given: {s : Set α} (hs : s.Nonempty) (h's : BddBelow s)
  proof: by
  rw [coe_sInf' hs h's]; rw [sInf_image]

中文:
定理 coe_sInf
  条件: {s : 集合 α} (hs : s.非空) (h's : BddBelow s)
  证明: by
  rw [coe_sInf' hs h's]; rw [sInf_image]

Depends on / 依赖: coe_sInf, sInf_image
-/
theorem coe_sInf {s : Set α} (hs : s.Nonempty) (h's : BddBelow s) :
    ↑(sInf s) = (⨅ a in s, ↑a : WithTop α) := by
  rw [coe_sInf' hs h's]; rw [sInf_image]

end WithTop

namespace Monotone

variable [ConditionallyCompleteLattice β]

section Preorder

variable [Preorder α] {f : α -> β} (h_mono : Monotone f)
include h_mono

/-! A monotone function into a conditionally complete lattice preserves the ordering properties of
`sSup` and `sInf`. -/

@[to_dual csInf_image_le]
/--
theorem `le_csSup_image` / 定理 `le_csSup_image`

English:
theorem le_csSup_image
  given: {s : Set α} {c : α} (hcs : c in s) (h_bdd : BddAbove s)
  proof: le_csSup (map_bddAbove h_mono h_bdd) (mem_image_of_mem f hcs)

@[to_dual le_csInf_image]

中文:
定理 le_csSup_image
  条件: {s : 集合 α} {c : α} (hcs : c in s) (h_bdd : BddAbove s)
  证明: le_csSup (map_bddAbove h_mono h_bdd) (mem_image_of_mem f hcs)

@[to_dual le_csInf_image]

Depends on / 依赖: h_bdd, h_mono, le_csSup, map_bddAbove, mem_image_of_mem
-/
theorem le_csSup_image {s : Set α} {c : α} (hcs : c in s) (h_bdd : BddAbove s) :
    f c <= sSup (f '' s) :=
  le_csSup (map_bddAbove h_mono h_bdd) (mem_image_of_mem f hcs)

@[to_dual le_csInf_image]
/--
theorem `csSup_image_le` / 定理 `csSup_image_le`

English:
theorem csSup_image_le
  given: {s : Set α} (hs : s.Nonempty) {B : α} (hB : B in upperBounds s)
  proof: csSup_le (Nonempty.image f hs) (h_mono.mem_upperBounds_image hB)

中文:
定理 csSup_image_le
  条件: {s : 集合 α} (hs : s.非空) {B : α} (hB : B in upperBounds s)
  证明: csSup_le (Nonempty.image f hs) (h_mono.mem_upperBounds_image hB)

Depends on / 依赖: Nonempty, Nonempty.image, csSup_le, h_mono, h_mono.mem_upperBounds_image, mem_upperBounds_image
-/
theorem csSup_image_le {s : Set α} (hs : s.Nonempty) {B : α} (hB : B in upperBounds s) :
    sSup (f '' s) <= f B :=
  csSup_le (Nonempty.image f hs) (h_mono.mem_upperBounds_image hB)

end Preorder

section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice α]
variable {f : α -> β} {s : Set α} (hs : s.Nonempty) (hf : Monotone f)
include hs hf

@[to_dual map_csInf_le_csInf_image]
/--
theorem `csSup_image_le_map_csSup` / 定理 `csSup_image_le_map_csSup`

English:
theorem csSup_image_le_map_csSup
  given: (hbdd : BddAbove s := by bddDefault)
  proof: csSup_image_le hf hs .left isLUB_csSup hs hbdd

中文:
定理 csSup_image_le_map_csSup
  条件: (hbdd : BddAbove s := by bddDefault)
  证明: csSup_image_le hf hs .left isLUB_csSup hs hbdd

Depends on / 依赖: bddDefault, csSup_image_le, isLUB_csSup
-/
theorem csSup_image_le_map_csSup (hbdd : BddAbove s := by bddDefault) :
    sSup (f '' s) <= f (sSup s) :=
csSup_image_le hf hs .left isLUB_csSup hs hbdd

end ConditionallyCompleteLattice

end Monotone

@[to_dual]
/--
lemma `MonotoneOn.csInf_eq_of_subset_of_forall_exists_le` / 引理 `MonotoneOn.csInf_eq_of_subset_of_forall_exists_le`

English:
lemma MonotoneOn.csInf_eq_of_subset_of_forall_exists_le
  proof: by
  obtain rfl | hs := Set.eq_empty_or_nonempty s
  · obtain rfl : t = ∅ := by simpa [Set.eq_empty_iff_forall_notMem] using h
    rfl
  refine le_antisymm ?_ (by gcongr; exacts [ht, hs.image f])
  refine le_csInf ((hs.mono hst).image f) ?_
  simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  intro a ha
  obtain ⟨x, hxs, hxa⟩ := h a ha
  exact csInf_le_of_le (ht.mono (image_mono hst)) ⟨x, hxs, rfl⟩ (hf (hst hxs) ha hxa)

@[to_dual]

中文:
引理 MonotoneOn.csInf_eq_of_subset_of_对任意_存在_le
  证明: by
  obtain rfl | hs := Set.eq_empty_or_nonempty s
  · obtain rfl : t = ∅ := by simpa [Set.eq_empty_iff_forall_notMem] using h
    rfl
  refine le_antisymm ?_ (by gcongr; exacts [ht, hs.image f])
  refine le_csInf ((hs.mono hst).image f) ?_
  simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  intro a ha
  obtain ⟨x, hxs, hxa⟩ := h a ha
  exact csInf_le_of_le (ht.mono (image_mono hst)) ⟨x, hxs, rfl⟩ (hf (hst hxs) ha hxa)

@[to_dual]

Depends on / 依赖: Set.eq_empty_iff_forall_notMem, Set.eq_empty_or_nonempty, and_imp, csInf_le_of_le, eq_empty_iff_forall_notMem, eq_empty_or_nonempty, exacts, forall_exists_index, hs.image, hs.mono, ht.mono, image_mono, le_antisymm, le_csInf, mem_image
-/
lemma MonotoneOn.csInf_eq_of_subset_of_forall_exists_le
    [Preorder α] [ConditionallyCompleteLattice β] {f : α -> β}
    {s t : Set α} (ht : BddBelow (f '' t)) (hf : MonotoneOn f t)
    (hst : s subseteq t) (h : forall y in t, exists x in s, x <= y) :
    sInf (f '' s) = sInf (f '' t) := by
  obtain rfl | hs := Set.eq_empty_or_nonempty s
  · obtain rfl : t = ∅ := by simpa [Set.eq_empty_iff_forall_notMem] using h
    rfl
  refine le_antisymm ?_ (by gcongr; exacts [ht, hs.image f])
  refine le_csInf ((hs.mono hst).image f) ?_
  simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  intro a ha
  obtain ⟨x, hxs, hxa⟩ := h a ha
  exact csInf_le_of_le (ht.mono (image_mono hst)) ⟨x, hxs, rfl⟩ (hf (hst hxs) ha hxa)

@[to_dual]
/--
theorem `MonotoneOn.sInf_image_Icc` / 定理 `MonotoneOn.sInf_image_Icc`

English:
theorem MonotoneOn.sInf_image_Icc
  statement: [Preorder α] [ConditionallyCompleteLattice β]
  proof: by
  refine IsGLB.csInf_eq ?_ ((nonempty_Icc.mpr hab).image f)
  refine isGLB_iff_le_iff.mpr (fun b' => ⟨?_, ?_⟩)
  · intro hb'
    rintro _ ⟨x, hx, rfl⟩
exact hb'.trans h' (left_mem_Icc.mpr hab) hx hx.1
  · exact fun hb' => hb' ⟨a, by simp [hab]⟩

@[to_dual]

中文:
定理 MonotoneOn.sInf_image_Icc
  结论: [预序 α] [条件完备格 β]
  证明: by
  refine IsGLB.csInf_eq ?_ ((nonempty_Icc.mpr hab).image f)
  refine isGLB_iff_le_iff.mpr (fun b' => ⟨?_, ?_⟩)
  · intro hb'
    rintro _ ⟨x, hx, rfl⟩
exact hb'.trans h' (left_mem_Icc.mpr hab) hx hx.1
  · exact fun hb' => hb' ⟨a, by simp [hab]⟩

@[to_dual]

Depends on / 依赖: IsGLB.csInf_eq, csInf_eq, isGLB_iff_le_iff, isGLB_iff_le_iff.mpr, left_mem_Icc, left_mem_Icc.mpr, nonempty_Icc, nonempty_Icc.mpr
-/
theorem MonotoneOn.sInf_image_Icc [Preorder α] [ConditionallyCompleteLattice β]
    {f : α -> β} {a b : α} (hab : a <= b)
    (h' : MonotoneOn f (Icc a b)) : sInf (f '' Icc a b) = f a := by
  refine IsGLB.csInf_eq ?_ ((nonempty_Icc.mpr hab).image f)
  refine isGLB_iff_le_iff.mpr (fun b' => ⟨?_, ?_⟩)
  · intro hb'
    rintro _ ⟨x, hx, rfl⟩
exact hb'.trans h' (left_mem_Icc.mpr hab) hx hx.1
  · exact fun hb' => hb' ⟨a, by simp [hab]⟩

@[to_dual]
/--
theorem `AntitoneOn.sInf_image_Icc` / 定理 `AntitoneOn.sInf_image_Icc`

English:
theorem AntitoneOn.sInf_image_Icc
  statement: [Preorder α] [ConditionallyCompleteLattice β]
  proof: by
  have : Icc a b = Icc (α := αᵒᵈ) (toDual b) (toDual a) := by rw [Icc_toDual]; rfl
  rw [this] at h' ⊢
  exact h'.dual_left.sInf_image_Icc (α := αᵒᵈ) hab

中文:
定理 AntitoneOn.sInf_image_Icc
  结论: [预序 α] [条件完备格 β]
  证明: by
  have : Icc a b = Icc (α := αᵒᵈ) (toDual b) (toDual a) := by rw [Icc_toDual]; rfl
  rw [this] at h' ⊢
  exact h'.dual_left.sInf_image_Icc (α := αᵒᵈ) hab

Depends on / 依赖: Icc_toDual, dual_left, dual_left.sInf_image_Icc, sInf_image_Icc, toDual
-/
theorem AntitoneOn.sInf_image_Icc [Preorder α] [ConditionallyCompleteLattice β]
    {f : α -> β} {a b : α} (hab : a <= b)
    (h' : AntitoneOn f (Icc a b)) : sInf (f '' Icc a b) = f b := by
  have : Icc a b = Icc (α := αᵒᵈ) (toDual b) (toDual a) := by rw [Icc_toDual]; rfl
  rw [this] at h' ⊢
  exact h'.dual_left.sInf_image_Icc (α := αᵒᵈ) hab

/-!
### Supremum/infimum of `Set.image2`

A collection of lemmas showing what happens to the suprema/infima of `s` and `t` when mapped under
a binary function whose partial evaluations are lower/upper adjoints of Galois connections.
-/

section

variable [ConditionallyCompleteLattice α] [ConditionallyCompleteLattice β]
  [ConditionallyCompleteLattice γ] {s : Set α} {t : Set β}

variable {l u : α -> β -> γ} {l₁ u₁ : β -> γ -> α} {l₂ u₂ : α -> γ -> β}
to_dual_name_hint L U, L₁ U₁, L₂ U₂

@[to_dual]
/--
theorem `csSup_image2_eq_csSup_csSup` / 定理 `csSup_image2_eq_csSup_csSup`

English:
theorem csSup_image2_eq_csSup_csSup
  statement: (h₁ : forall b, GaloisConnection (swap l b) (u₁ b))
  proof: isLUB_image2_of_isLUB_isLUB h₁ h₂ (isLUB_csSup hs₀ hs₁) (isLUB_csSup ht₀ ht₁)
.csSup_eq (hs₀.image2 ht₀)

@[to_dual]

中文:
定理 csSup_image2_eq_csSup_csSup
  结论: (h₁ : 对任意 b, GaloisConnection (swap l b) (u₁ b))
  证明: isLUB_image2_of_isLUB_isLUB h₁ h₂ (isLUB_csSup hs₀ hs₁) (isLUB_csSup ht₀ ht₁)
.csSup_eq (hs₀.image2 ht₀)

@[to_dual]

Depends on / 依赖: csSup_eq, image2, isLUB_csSup, isLUB_image2_of_isLUB_isLUB
-/
theorem csSup_image2_eq_csSup_csSup (h₁ : forall b, GaloisConnection (swap l b) (u₁ b))
    (h₂ : forall a, GaloisConnection (l a) (u₂ a)) (hs₀ : s.Nonempty) (hs₁ : BddAbove s)
    (ht₀ : t.Nonempty) (ht₁ : BddAbove t) : sSup (image2 l s t) = l (sSup s) (sSup t) :=
  isLUB_image2_of_isLUB_isLUB h₁ h₂ (isLUB_csSup hs₀ hs₁) (isLUB_csSup ht₀ ht₁)
.csSup_eq (hs₀.image2 ht₀)

@[to_dual]
/--
theorem `csSup_image2_eq_csSup_csInf` / 定理 `csSup_image2_eq_csSup_csInf`

English:
theorem csSup_image2_eq_csSup_csInf
  statement: (h₁ : forall b, GaloisConnection (swap l b) (u₁ b))
  proof: csSup_image2_eq_csSup_csSup (β := βᵒᵈ) h₁ h₂

@[to_dual]

中文:
定理 csSup_image2_eq_csSup_csInf
  结论: (h₁ : 对任意 b, GaloisConnection (swap l b) (u₁ b))
  证明: csSup_image2_eq_csSup_csSup (β := βᵒᵈ) h₁ h₂

@[to_dual]

Depends on / 依赖: csSup_image2_eq_csSup_csSup
-/
theorem csSup_image2_eq_csSup_csInf (h₁ : forall b, GaloisConnection (swap l b) (u₁ b))
    (h₂ : forall a, GaloisConnection (l a ∘ ofDual) (toDual ∘ u₂ a)) :
    s.Nonempty -> BddAbove s -> t.Nonempty -> BddBelow t -> sSup (image2 l s t) = l (sSup s) (sInf t) :=
  csSup_image2_eq_csSup_csSup (β := βᵒᵈ) h₁ h₂

@[to_dual]
/--
theorem `csSup_image2_eq_csInf_csSup` / 定理 `csSup_image2_eq_csInf_csSup`

English:
theorem csSup_image2_eq_csInf_csSup
  statement: (h₁ : forall b, GaloisConnection (swap l b ∘ ofDual) (toDual ∘ u₁ b))
  proof: csSup_image2_eq_csSup_csSup (α := αᵒᵈ) h₁ h₂

@[to_dual]

中文:
定理 csSup_image2_eq_csInf_csSup
  结论: (h₁ : 对任意 b, GaloisConnection (swap l b ∘ ofDual) (toDual ∘ u₁ b))
  证明: csSup_image2_eq_csSup_csSup (α := αᵒᵈ) h₁ h₂

@[to_dual]

Depends on / 依赖: csSup_image2_eq_csSup_csSup
-/
theorem csSup_image2_eq_csInf_csSup (h₁ : forall b, GaloisConnection (swap l b ∘ ofDual) (toDual ∘ u₁ b))
    (h₂ : forall a, GaloisConnection (l a) (u₂ a)) :
    s.Nonempty -> BddBelow s -> t.Nonempty -> BddAbove t -> sSup (image2 l s t) = l (sInf s) (sSup t) :=
  csSup_image2_eq_csSup_csSup (α := αᵒᵈ) h₁ h₂

@[to_dual]
/--
theorem `csSup_image2_eq_csInf_csInf` / 定理 `csSup_image2_eq_csInf_csInf`

English:
theorem csSup_image2_eq_csInf_csInf
  statement: (h₁ : forall b, GaloisConnection (swap l b ∘ ofDual) (toDual ∘ u₁ b))
  proof: csSup_image2_eq_csSup_csSup (α := αᵒᵈ) (β := βᵒᵈ) h₁ h₂

中文:
定理 csSup_image2_eq_csInf_csInf
  结论: (h₁ : 对任意 b, GaloisConnection (swap l b ∘ ofDual) (toDual ∘ u₁ b))
  证明: csSup_image2_eq_csSup_csSup (α := αᵒᵈ) (β := βᵒᵈ) h₁ h₂

Depends on / 依赖: csSup_image2_eq_csSup_csSup
-/
theorem csSup_image2_eq_csInf_csInf (h₁ : forall b, GaloisConnection (swap l b ∘ ofDual) (toDual ∘ u₁ b))
    (h₂ : forall a, GaloisConnection (l a ∘ ofDual) (toDual ∘ u₂ a)) :
    s.Nonempty -> BddBelow s -> t.Nonempty -> BddBelow t -> sSup (image2 l s t) = l (sInf s) (sInf t) :=
  csSup_image2_eq_csSup_csSup (α := αᵒᵈ) (β := βᵒᵈ) h₁ h₂

end

section WithTopBot

/-!
### Complete lattice structure on `WithTop (WithBot α)`

If `α` is a `ConditionallyCompleteLattice`, then we show that `WithTop α` and `WithBot α`
also inherit the structure of conditionally complete lattices. Furthermore, we show
that `WithTop (WithBot α)` and `WithBot (WithTop α)` naturally inherit the structure of a
complete lattice. Note that for `α` a conditionally complete lattice, `sSup` and `sInf` both return
junk values for sets which are empty or unbounded. The extension of `sSup` to `WithTop α` fixes
the unboundedness problem and the extension to `WithBot α` fixes the problem with
the empty set.

This result can be used to show that the extended reals `[-∞, ∞]` are a complete linear order.
-/


/-- Adding a top element to a conditionally complete lattice
gives a conditionally complete lattice -/
@[to_dual
/-- Adding a bottom element to a conditionally complete lattice
gives a conditionally complete lattice -/]
/--
Instance `WithTop.conditionallyCompleteLattice` / 实例 `WithTop.conditionallyCompleteLattice`

English:
instance WithTop.conditionallyCompleteLattice
  signature: {α : Type*}
  body: WithTop.isLUB_sSup' hS
  isGLB_csInf _ _ hS := WithTop.isGLB_sInf' hS

@[to_dual]

中文:
实例 WithTop.conditionallyCompleteLattice
  签名: {α : 类型}
  定义体: WithTop.isLUB_sSup' hS
  isGLB_csInf _ _ hS := WithTop.isGLB_sInf' hS

@[to_dual]

Depends on / 依赖: WithTop, WithTop.isLUB_sSup, isLUB_sSup
-/
noncomputable instance WithTop.conditionallyCompleteLattice {α : Type*}
    [ConditionallyCompleteLattice α] : ConditionallyCompleteLattice (WithTop α) where
  isLUB_csSup _ hS _ := WithTop.isLUB_sSup' hS
  isGLB_csInf _ _ hS := WithTop.isGLB_sInf' hS

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CompleteLattice
  signature: α] : CompleteLattice (WithTop α) where
  body: ⟨fun _ => le_csSup (OrderTop.bddAbove _), fun _ has =>
    s.eq_empty_or_nonempty.elim (by simp [·, WithTop.sSup_empty]) (csSup_le · has)⟩
  isGLB_sInf s := ⟨fun _ => csInf_le (OrderBot.bddBelow _), fun _ hsa =>
    s.eq_empty_or_nonempty.elim (by simp [·]) (le_csInf · hsa)⟩

中文:
实例 [完备格
  签名: α] : 完备格 (WithTop α) where
  定义体: ⟨fun _ => le_csSup (OrderTop.bddAbove _), fun _ has =>
    s.eq_empty_or_nonempty.elim (by simp [·, WithTop.sSup_empty]) (csSup_le · has)⟩
  isGLB_sInf s := ⟨fun _ => csInf_le (OrderBot.bddBelow _), fun _ hsa =>
    s.eq_empty_or_nonempty.elim (by simp [·]) (le_csInf · hsa)⟩

Depends on / 依赖: OrderTop, OrderTop.bddAbove, bddAbove, le_csSup
-/
noncomputable instance [CompleteLattice α] : CompleteLattice (WithTop α) where
  isLUB_sSup s := ⟨fun _ => le_csSup (OrderTop.bddAbove _), fun _ has =>
    s.eq_empty_or_nonempty.elim (by simp [·, WithTop.sSup_empty]) (csSup_le · has)⟩
  isGLB_sInf s := ⟨fun _ => csInf_le (OrderBot.bddBelow _), fun _ hsa =>
    s.eq_empty_or_nonempty.elim (by simp [·]) (le_csInf · hsa)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CompleteLinearOrder
  signature: α] : CompleteLinearOrder (WithBot α) where
  body: WithBot.linearOrder
  __ := WithBot.linearOrder.toBiheytingAlgebra
  __ := show CompleteLattice (WithBot α) from inferInstance

中文:
实例 [完备线性序
  签名: α] : 完备线性序 (WithBot α) where
  定义体: WithBot.linearOrder
  __ := WithBot.linearOrder.toBiheytingAlgebra
  __ := show CompleteLattice (WithBot α) from inferInstance

Depends on / 依赖: WithBot, WithBot.linearOrder, linearOrder
-/
noncomputable instance [CompleteLinearOrder α] : CompleteLinearOrder (WithBot α) where
  __ := WithBot.linearOrder
  __ := WithBot.linearOrder.toBiheytingAlgebra
  __ := show CompleteLattice (WithBot α) from inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [ConditionallyCompleteLinearOrder
  signature: α] :
  body: inferInstance
  toDecidableEq := inferInstance
  toDecidableLT := inferInstance
csSup_of_not_bddAbove s := absurd OrderTop.bddAbove s
  csInf_of_not_bddBelow s h := by simp [h]

中文:
实例 [条件完备线性序
  签名: α] :
  定义体: inferInstance
  toDecidableEq := inferInstance
  toDecidableLT := inferInstance
csSup_of_not_bddAbove s := absurd OrderTop.bddAbove s
  csInf_of_not_bddBelow s h := by simp [h]
-/
noncomputable instance [ConditionallyCompleteLinearOrder α] :
    ConditionallyCompleteLinearOrder (WithTop α) where
  le_total
  toDecidableLE := inferInstance
  toDecidableEq := inferInstance
  toDecidableLT := inferInstance
csSup_of_not_bddAbove s := absurd OrderTop.bddAbove s
  csInf_of_not_bddBelow s h := by simp [h]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [ConditionallyCompleteLinearOrder
  signature: α] :
  body: inferInstance
  toDecidableEq := inferInstance
  toDecidableLT := inferInstance
  csSup_of_not_bddAbove s h := by simp [h]
csInf_of_not_bddBelow s := absurd OrderBot.bddBelow s
  csSup_empty := WithBot.sSup_empty

中文:
实例 [条件完备线性序
  签名: α] :
  定义体: inferInstance
  toDecidableEq := inferInstance
  toDecidableLT := inferInstance
  csSup_of_not_bddAbove s h := by simp [h]
csInf_of_not_bddBelow s := absurd OrderBot.bddBelow s
  csSup_empty := WithBot.sSup_empty
-/
noncomputable instance [ConditionallyCompleteLinearOrder α] :
    ConditionallyCompleteLinearOrderBot (WithBot α) where
  le_total
  toDecidableLE := inferInstance
  toDecidableEq := inferInstance
  toDecidableLT := inferInstance
  csSup_of_not_bddAbove s h := by simp [h]
csInf_of_not_bddBelow s := absurd OrderBot.bddBelow s
  csSup_empty := WithBot.sSup_empty

open scoped Classical in
@[to_dual WithBot.WithTop.completeLattice]
/--
Instance `WithTop.WithBot.completeLattice` / 实例 `WithTop.WithBot.completeLattice`

English:
instance WithTop.WithBot.completeLattice
  signature: {α : Type*}
  body: ⟨fun a haS => (WithTop.isLUB_sSup' ⟨a, haS⟩).1 haS, fun a ha => by
    rcases S.eq_empty_or_nonempty with h | h
    · change ite _ _ _ <= a
      simp [h]
    · exact (WithTop.isLUB_sSup' h).2 ha⟩
  isGLB_sInf S := ⟨fun a haS =>
    show ite _ _ _ <= a by
      simp only [OrderBot.bddBelow, not_true_eq_false, or_false]
      split_ifs with h₁
      · cases a
        · exact le_rfl
        cases h₁ haS
      · cases a
        · exact le_top
        · apply WithTop.coe_le_coe.2
          refine csInf_le ?_ haS
          use ⊥
          intro b _
          exact bot_le,
    fun a haS => (WithTop.isGLB_sInf' ⟨a, haS⟩).2 haS⟩

中文:
实例 WithTop.WithBot.completeLattice
  签名: {α : 类型}
  定义体: ⟨fun a haS => (WithTop.isLUB_sSup' ⟨a, haS⟩).1 haS, fun a ha => by
    rcases S.eq_empty_or_nonempty with h | h
    · change ite _ _ _ <= a
      simp [h]
    · exact (WithTop.isLUB_sSup' h).2 ha⟩
  isGLB_sInf S := ⟨fun a haS =>
    show ite _ _ _ <= a by
      simp only [OrderBot.bddBelow, not_true_eq_false, or_false]
      split_ifs with h₁
      · cases a
        · exact le_rfl
        cases h₁ haS
      · cases a
        · exact le_top
        · apply WithTop.coe_le_coe.2
          refine csInf_le ?_ haS
          use ⊥
          intro b _
          exact bot_le,
    fun a haS => (WithTop.isGLB_sInf' ⟨a, haS⟩).2 haS⟩

Depends on / 依赖: OrderBot, OrderBot.bddBelow, S.eq_empty_or_nonempty, WithTop, WithTop.coe_le_coe, WithTop.isGLB_sInf, WithTop.isLUB_sSup, bddBelow, bot_le, coe_le_coe, csInf_le, eq_empty_or_nonempty, isGLB_sInf, isLUB_sSup, le_rfl, le_top, not_true_eq_false, or_false, split_ifs
-/
noncomputable instance WithTop.WithBot.completeLattice {α : Type*}
    [ConditionallyCompleteLattice α] : CompleteLattice (WithTop (WithBot α)) where
  isLUB_sSup S := ⟨fun a haS => (WithTop.isLUB_sSup' ⟨a, haS⟩).1 haS, fun a ha => by
    rcases S.eq_empty_or_nonempty with h | h
    · change ite _ _ _ <= a
      simp [h]
    · exact (WithTop.isLUB_sSup' h).2 ha⟩
  isGLB_sInf S := ⟨fun a haS =>
    show ite _ _ _ <= a by
      simp only [OrderBot.bddBelow, not_true_eq_false, or_false]
      split_ifs with h₁
      · cases a
        · exact le_rfl
        cases h₁ haS
      · cases a
        · exact le_top
        · apply WithTop.coe_le_coe.2
          refine csInf_le ?_ haS
          use ⊥
          intro b _
          exact bot_le,
    fun a haS => (WithTop.isGLB_sInf' ⟨a, haS⟩).2 haS⟩

/--
Instance `WithBot.WithTop.completeLinearOrder` / 实例 `WithBot.WithTop.completeLinearOrder`

English:
instance WithBot.WithTop.completeLinearOrder
  signature: {α : Type*}
  body: completeLattice
  __ := linearOrder
  __ := linearOrder.toBiheytingAlgebra

中文:
实例 WithBot.WithTop.completeLinearOrder
  签名: {α : 类型}
  定义体: completeLattice
  __ := linearOrder
  __ := linearOrder.toBiheytingAlgebra

Depends on / 依赖: completeLattice
-/
noncomputable instance WithBot.WithTop.completeLinearOrder {α : Type*}
    [ConditionallyCompleteLinearOrder α] : CompleteLinearOrder (WithBot (WithTop α)) where
  __ := completeLattice
  __ := linearOrder
  __ := linearOrder.toBiheytingAlgebra

end WithTopBot
