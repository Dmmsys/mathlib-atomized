/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/
module

public import Mathlib.Data.Set.Order
public import Mathlib.Order.Bounds.Basic
public import Mathlib.Order.Interval.Set.Image
public import Mathlib.Order.Interval.Set.LinearOrder
public import Mathlib.Tactic.Common
public import Mathlib.Order.MinMax

/-!
# Intervals without endpoints ordering

In any lattice `α`, we define `uIcc a b` to be `Icc (a ⊓ b) (a ⊔ b)`, which in a linear order is
the set of elements lying between `a` and `b`.

`Icc a b` requires the assumption `a ≤ b` to be meaningful, which is sometimes inconvenient. The
interval as defined in this file is always the set of things lying between `a` and `b`, regardless
of the relative order of `a` and `b`.

For real numbers, `uIcc a b` is the same as `segment ℝ a b`.

In a product or pi type, `uIcc a b` is the smallest box containing `a` and `b`. For example,
`uIcc (1, -1) (-1, 1) = Icc (-1, -1) (1, 1)` is the square of vertices `(1, -1)`, `(-1, -1)`,
`(-1, 1)`, `(1, 1)`.

In `Finset α` (seen as a hypercube of dimension `Fintype.card α`), `uIcc a b` is the smallest
subcube containing both `a` and `b`.

## Notation

We use the localized notation `[[a, b]]` for `uIcc a b`. One can open the scope `Interval` to
make the notation available.

-/

@[expose] public section


open Function

open OrderDual (toDual ofDual)

variable {α β : Type*}

namespace Set

section Lattice

variable [Lattice α] [Lattice β] {a a₁ a₂ b b₁ b₂ x : α}

/--
Definition of `uIcc` / `uIcc` 的定义

English:
definition uIcc
  signature: (a b : α)
  body: Icc (a ⊓ b) (a ⊔ b)

中文:
定义 uIcc
  签名: (a b : α)
  定义体: Icc (a ⊓ b) (a ⊔ b)
-/
def uIcc (a b : α) : Set α := Icc (a ⊓ b) (a ⊔ b)

/-- `[[a, b]]` denotes the set of elements lying between `a` and `b`, inclusive. -/
scoped[Interval] notation "[[" a ", " b "]]" => Set.uIcc a b

open Interval

@[simp]
/--
lemma `uIcc_toDual` / 引理 `uIcc_toDual`

English:
lemma uIcc_toDual
  given: (a b : α)
  statement: [[toDual a, toDual b]] = ofDual ⁻¹' [[a, b]]
  proof: -- Note: needed to hint `(α := α)` after https://github.com/leanprover-community/mathlib4/pull/8386 (elaboration order?)
  Icc_toDual (α := α)

@[simp]

中文:
引理 uIcc_toDual
  条件: (a b : α)
  结论: [[toDual a, toDual b]] = ofDual ⁻¹' [[a, b]]
  证明: -- Note: needed to hint `(α := α)` after https://github.com/leanprover-community/mathlib4/pull/8386 (elaboration order?)
  Icc_toDual (α := α)

@[simp]
-/
lemma uIcc_toDual (a b : α) : [[toDual a, toDual b]] = ofDual ⁻¹' [[a, b]] :=
  -- Note: needed to hint `(α := α)` after https://github.com/leanprover-community/mathlib4/pull/8386 (elaboration order?)
  Icc_toDual (α := α)

@[simp]
/--
theorem `uIcc_ofDual` / 定理 `uIcc_ofDual`

English:
theorem uIcc_ofDual
  given: (a b : αᵒᵈ)
  statement: [[ofDual a, ofDual b]] = toDual ⁻¹' [[a, b]]
  proof: Icc_ofDual

@[simp]

中文:
定理 uIcc_ofDual
  条件: (a b : αᵒᵈ)
  结论: [[ofDual a, ofDual b]] = toDual ⁻¹' [[a, b]]
  证明: Icc_ofDual

@[simp]

Depends on / 依赖: Icc_ofDual
-/
theorem uIcc_ofDual (a b : αᵒᵈ) : [[ofDual a, ofDual b]] = toDual ⁻¹' [[a, b]] :=
  Icc_ofDual

@[simp]
/--
lemma `uIcc_of_le` / 引理 `uIcc_of_le`

English:
lemma uIcc_of_le
  given: (h : a <= b)
  statement: [[a, b]] = Icc a b
  proof: by rw [uIcc, inf_eq_left.2 h, sup_eq_right.2 h]

@[simp]

中文:
引理 uIcc_of_le
  条件: (h : a <= b)
  结论: [[a, b]] = 闭区间 a b
  证明: by rw [uIcc, inf_eq_left.2 h, sup_eq_right.2 h]

@[simp]

Depends on / 依赖: inf_eq_left, sup_eq_right
-/
lemma uIcc_of_le (h : a <= b) : [[a, b]] = Icc a b := by rw [uIcc, inf_eq_left.2 h, sup_eq_right.2 h]

@[simp]
/--
lemma `uIcc_of_ge` / 引理 `uIcc_of_ge`

English:
lemma uIcc_of_ge
  given: (h : b <= a)
  statement: [[a, b]] = Icc b a
  proof: by rw [uIcc, inf_eq_right.2 h, sup_eq_left.2 h]

中文:
引理 uIcc_of_ge
  条件: (h : b <= a)
  结论: [[a, b]] = 闭区间 b a
  证明: by rw [uIcc, inf_eq_right.2 h, sup_eq_left.2 h]

Depends on / 依赖: inf_eq_right, sup_eq_left
-/
lemma uIcc_of_ge (h : b <= a) : [[a, b]] = Icc b a := by rw [uIcc, inf_eq_right.2 h, sup_eq_left.2 h]

/--
lemma `uIcc_comm` / 引理 `uIcc_comm`

English:
lemma uIcc_comm
  given: (a b : α)
  statement: [[a, b]] = [[b, a]]
  proof: by simp_rw [uIcc, inf_comm, sup_comm]

中文:
引理 uIcc_comm
  条件: (a b : α)
  结论: [[a, b]] = [[b, a]]
  证明: by simp_rw [uIcc, inf_comm, sup_comm]

Depends on / 依赖: inf_comm, simp_rw, sup_comm
-/
lemma uIcc_comm (a b : α) : [[a, b]] = [[b, a]] := by simp_rw [uIcc, inf_comm, sup_comm]

/--
lemma `uIcc_of_lt` / 引理 `uIcc_of_lt`

English:
lemma uIcc_of_lt
  given: (h : a < b)
  statement: [[a, b]] = Icc a b
  proof: uIcc_of_le h.le

中文:
引理 uIcc_of_lt
  条件: (h : a < b)
  结论: [[a, b]] = 闭区间 a b
  证明: uIcc_of_le h.le

Depends on / 依赖: h.le, uIcc_of_le
-/
lemma uIcc_of_lt (h : a < b) : [[a, b]] = Icc a b := uIcc_of_le h.le
/--
lemma `uIcc_of_gt` / 引理 `uIcc_of_gt`

English:
lemma uIcc_of_gt
  given: (h : b < a)
  statement: [[a, b]] = Icc b a
  proof: uIcc_of_ge h.le

中文:
引理 uIcc_of_gt
  条件: (h : b < a)
  结论: [[a, b]] = 闭区间 b a
  证明: uIcc_of_ge h.le

Depends on / 依赖: h.le, uIcc_of_ge
-/
lemma uIcc_of_gt (h : b < a) : [[a, b]] = Icc b a := uIcc_of_ge h.le

/--
lemma `uIcc_self` / 引理 `uIcc_self`

English:
lemma uIcc_self
  statement: [[a, a]] = {a}
  proof: by simp [uIcc]

中文:
引理 uIcc_self
  结论: [[a, a]] = {a}
  证明: by simp [uIcc]
-/
lemma uIcc_self : [[a, a]] = {a} := by simp [uIcc]

/--
lemma `nonempty_uIcc` / 引理 `nonempty_uIcc`

English:
lemma nonempty_uIcc
  statement: [[a, b]].Nonempty
  proof: nonempty_Icc.2 inf_le_sup

中文:
引理 nonempty_uIcc
  结论: [[a, b]].非空
  证明: nonempty_Icc.2 inf_le_sup
-/
@[simp] lemma nonempty_uIcc : [[a, b]].Nonempty := nonempty_Icc.2 inf_le_sup

/--
lemma `Icc_subset_uIcc` / 引理 `Icc_subset_uIcc`

English:
lemma Icc_subset_uIcc
  statement: Icc a b subseteq [[a, b]]
  proof: Icc_subset_Icc inf_le_left le_sup_right

中文:
引理 Icc_subset_uIcc
  结论: 闭区间 a b subseteq [[a, b]]
  证明: Icc_subset_Icc inf_le_left le_sup_right

Depends on / 依赖: Icc_subset_Icc, inf_le_left, le_sup_right
-/
lemma Icc_subset_uIcc : Icc a b subseteq [[a, b]] := Icc_subset_Icc inf_le_left le_sup_right
/--
lemma `Icc_subset_uIcc'` / 引理 `Icc_subset_uIcc'`

English:
lemma Icc_subset_uIcc'
  statement: Icc b a subseteq [[a, b]]
  proof: Icc_subset_Icc inf_le_right le_sup_left

中文:
引理 Icc_subset_uIcc'
  结论: 闭区间 b a subseteq [[a, b]]
  证明: Icc_subset_Icc inf_le_right le_sup_left

Depends on / 依赖: Icc_subset_Icc, inf_le_right, le_sup_left
-/
lemma Icc_subset_uIcc' : Icc b a subseteq [[a, b]] := Icc_subset_Icc inf_le_right le_sup_left

/--
lemma `left_mem_uIcc` / 引理 `left_mem_uIcc`

English:
lemma left_mem_uIcc
  statement: a in [[a, b]]
  proof: ⟨inf_le_left, le_sup_left⟩

中文:
引理 left_mem_uIcc
  结论: a in [[a, b]]
  证明: ⟨inf_le_left, le_sup_left⟩
-/
@[simp] lemma left_mem_uIcc : a in [[a, b]] := ⟨inf_le_left, le_sup_left⟩
/--
lemma `right_mem_uIcc` / 引理 `right_mem_uIcc`

English:
lemma right_mem_uIcc
  statement: b in [[a, b]]
  proof: ⟨inf_le_right, le_sup_right⟩

中文:
引理 right_mem_uIcc
  结论: b in [[a, b]]
  证明: ⟨inf_le_right, le_sup_right⟩
-/
@[simp] lemma right_mem_uIcc : b in [[a, b]] := ⟨inf_le_right, le_sup_right⟩

/--
lemma `mem_uIcc_of_le` / 引理 `mem_uIcc_of_le`

English:
lemma mem_uIcc_of_le
  given: (ha : a <= x) (hb : x <= b)
  statement: x in [[a, b]]
  proof: Icc_subset_uIcc ⟨ha, hb⟩

中文:
引理 mem_uIcc_of_le
  条件: (ha : a <= x) (hb : x <= b)
  结论: x in [[a, b]]
  证明: Icc_subset_uIcc ⟨ha, hb⟩

Depends on / 依赖: Icc_subset_uIcc
-/
lemma mem_uIcc_of_le (ha : a <= x) (hb : x <= b) : x in [[a, b]] := Icc_subset_uIcc ⟨ha, hb⟩
/--
lemma `mem_uIcc_of_ge` / 引理 `mem_uIcc_of_ge`

English:
lemma mem_uIcc_of_ge
  given: (hb : b <= x) (ha : x <= a)
  statement: x in [[a, b]]
  proof: Icc_subset_uIcc' ⟨hb, ha⟩

中文:
引理 mem_uIcc_of_ge
  条件: (hb : b <= x) (ha : x <= a)
  结论: x in [[a, b]]
  证明: Icc_subset_uIcc' ⟨hb, ha⟩

Depends on / 依赖: Icc_subset_uIcc
-/
lemma mem_uIcc_of_ge (hb : b <= x) (ha : x <= a) : x in [[a, b]] := Icc_subset_uIcc' ⟨hb, ha⟩

/--
lemma `uIcc_subset_uIcc` / 引理 `uIcc_subset_uIcc`

English:
lemma uIcc_subset_uIcc
  given: (h₁ : a₁ in [[a₂, b₂]]) (h₂ : b₁ in [[a₂, b₂]])
  proof: Icc_subset_Icc (le_inf h₁.1 h₂.1) (sup_le h₁.2 h₂.2)

中文:
引理 uIcc_subset_uIcc
  条件: (h₁ : a₁ in [[a₂, b₂]]) (h₂ : b₁ in [[a₂, b₂]])
  证明: Icc_subset_Icc (le_inf h₁.1 h₂.1) (sup_le h₁.2 h₂.2)

Depends on / 依赖: Icc_subset_Icc, le_inf, sup_le
-/
lemma uIcc_subset_uIcc (h₁ : a₁ in [[a₂, b₂]]) (h₂ : b₁ in [[a₂, b₂]]) :
    [[a₁, b₁]] subseteq [[a₂, b₂]] :=
  Icc_subset_Icc (le_inf h₁.1 h₂.1) (sup_le h₁.2 h₂.2)

/--
lemma `uIcc_subset_Icc` / 引理 `uIcc_subset_Icc`

English:
lemma uIcc_subset_Icc
  given: (ha : a₁ in Icc a₂ b₂) (hb : b₁ in Icc a₂ b₂)
  proof: Icc_subset_Icc (le_inf ha.1 hb.1) (sup_le ha.2 hb.2)

中文:
引理 uIcc_subset_Icc
  条件: (ha : a₁ in 闭区间 a₂ b₂) (hb : b₁ in 闭区间 a₂ b₂)
  证明: Icc_subset_Icc (le_inf ha.1 hb.1) (sup_le ha.2 hb.2)

Depends on / 依赖: Icc_subset_Icc, le_inf, sup_le
-/
lemma uIcc_subset_Icc (ha : a₁ in Icc a₂ b₂) (hb : b₁ in Icc a₂ b₂) :
    [[a₁, b₁]] subseteq Icc a₂ b₂ :=
  Icc_subset_Icc (le_inf ha.1 hb.1) (sup_le ha.2 hb.2)

/--
lemma `uIcc_subset_uIcc_iff_mem` / 引理 `uIcc_subset_uIcc_iff_mem`

English:
lemma uIcc_subset_uIcc_iff_mem
  proof: Iff.intro (fun h => ⟨h left_mem_uIcc, h right_mem_uIcc⟩) fun h =>
    uIcc_subset_uIcc h.1 h.2

中文:
引理 uIcc_subset_uIcc_iff_mem
  证明: Iff.intro (fun h => ⟨h left_mem_uIcc, h right_mem_uIcc⟩) fun h =>
    uIcc_subset_uIcc h.1 h.2

Depends on / 依赖: Iff.intro, left_mem_uIcc, right_mem_uIcc, uIcc_subset_uIcc
-/
lemma uIcc_subset_uIcc_iff_mem :
    [[a₁, b₁]] subseteq [[a₂, b₂]] ↔ a₁ in [[a₂, b₂]] ∧ b₁ in [[a₂, b₂]] :=
  Iff.intro (fun h => ⟨h left_mem_uIcc, h right_mem_uIcc⟩) fun h =>
    uIcc_subset_uIcc h.1 h.2

/--
lemma `uIcc_subset_uIcc_iff_le'` / 引理 `uIcc_subset_uIcc_iff_le'`

English:
lemma uIcc_subset_uIcc_iff_le'
  proof: Icc_subset_Icc_iff inf_le_sup

中文:
引理 uIcc_subset_uIcc_iff_le'
  证明: Icc_subset_Icc_iff inf_le_sup

Depends on / 依赖: Icc_subset_Icc_iff, inf_le_sup
-/
lemma uIcc_subset_uIcc_iff_le' :
    [[a₁, b₁]] subseteq [[a₂, b₂]] ↔ a₂ ⊓ b₂ <= a₁ ⊓ b₁ ∧ a₁ ⊔ b₁ <= a₂ ⊔ b₂ :=
  Icc_subset_Icc_iff inf_le_sup

/--
lemma `uIcc_subset_uIcc_right` / 引理 `uIcc_subset_uIcc_right`

English:
lemma uIcc_subset_uIcc_right
  given: (h : x in [[a, b]])
  statement: [[x, b]] subseteq [[a, b]]
  proof: uIcc_subset_uIcc h right_mem_uIcc

中文:
引理 uIcc_subset_uIcc_right
  条件: (h : x in [[a, b]])
  结论: [[x, b]] subseteq [[a, b]]
  证明: uIcc_subset_uIcc h right_mem_uIcc

Depends on / 依赖: right_mem_uIcc, uIcc_subset_uIcc
-/
lemma uIcc_subset_uIcc_right (h : x in [[a, b]]) : [[x, b]] subseteq [[a, b]] :=
  uIcc_subset_uIcc h right_mem_uIcc

/--
lemma `uIcc_subset_uIcc_left` / 引理 `uIcc_subset_uIcc_left`

English:
lemma uIcc_subset_uIcc_left
  given: (h : x in [[a, b]])
  statement: [[a, x]] subseteq [[a, b]]
  proof: uIcc_subset_uIcc left_mem_uIcc h

中文:
引理 uIcc_subset_uIcc_left
  条件: (h : x in [[a, b]])
  结论: [[a, x]] subseteq [[a, b]]
  证明: uIcc_subset_uIcc left_mem_uIcc h

Depends on / 依赖: left_mem_uIcc, uIcc_subset_uIcc
-/
lemma uIcc_subset_uIcc_left (h : x in [[a, b]]) : [[a, x]] subseteq [[a, b]] :=
  uIcc_subset_uIcc left_mem_uIcc h

/--
lemma `bdd_below_bdd_above_iff_subset_uIcc` / 引理 `bdd_below_bdd_above_iff_subset_uIcc`

English:
lemma bdd_below_bdd_above_iff_subset_uIcc
  given: (s : Set α)
  proof: bddBelow_bddAbove_iff_subset_Icc.trans
    ⟨fun ⟨a, b, h⟩ => ⟨a, b, fun _ hx => Icc_subset_uIcc (h hx)⟩, fun ⟨_, _, h⟩ => ⟨_, _, h⟩⟩

中文:
引理 bdd_below_bdd_above_iff_subset_uIcc
  条件: (s : 集合 α)
  证明: bddBelow_bddAbove_iff_subset_Icc.trans
    ⟨fun ⟨a, b, h⟩ => ⟨a, b, fun _ hx => Icc_subset_uIcc (h hx)⟩, fun ⟨_, _, h⟩ => ⟨_, _, h⟩⟩

Depends on / 依赖: Icc_subset_uIcc, bddBelow_bddAbove_iff_subset_Icc, bddBelow_bddAbove_iff_subset_Icc.trans
-/
lemma bdd_below_bdd_above_iff_subset_uIcc (s : Set α) :
    BddBelow s ∧ BddAbove s ↔ exists a b, s subseteq [[a, b]] :=
  bddBelow_bddAbove_iff_subset_Icc.trans
    ⟨fun ⟨a, b, h⟩ => ⟨a, b, fun _ hx => Icc_subset_uIcc (h hx)⟩, fun ⟨_, _, h⟩ => ⟨_, _, h⟩⟩

section Prod

@[simp]
/--
theorem `uIcc_prod_uIcc` / 定理 `uIcc_prod_uIcc`

English:
theorem uIcc_prod_uIcc
  given: (a₁ a₂ : α) (b₁ b₂ : β)
  proof: Icc_prod_Icc _ _ _ _

中文:
定理 uIcc_prod_uIcc
  条件: (a₁ a₂ : α) (b₁ b₂ : β)
  证明: Icc_prod_Icc _ _ _ _

Depends on / 依赖: Icc_prod_Icc
-/
theorem uIcc_prod_uIcc (a₁ a₂ : α) (b₁ b₂ : β) :
    [[a₁, a₂]] ×ˢ [[b₁, b₂]] = [[(a₁, b₁), (a₂, b₂)]] :=
  Icc_prod_Icc _ _ _ _

/--
theorem `uIcc_prod_eq` / 定理 `uIcc_prod_eq`

English:
theorem uIcc_prod_eq
  given: (a b : α × β)
  statement: [[a, b]] = [[a.1, b.1]] ×ˢ [[a.2, b.2]]
  proof: by simp

中文:
定理 uIcc_prod_eq
  条件: (a b : α × β)
  结论: [[a, b]] = [[a.1, b.1]] ×ˢ [[a.2, b.2]]
  证明: by simp
-/
theorem uIcc_prod_eq (a b : α × β) : [[a, b]] = [[a.1, b.1]] ×ˢ [[a.2, b.2]] := by simp

end Prod

end Lattice

open Interval

section DistribLattice

variable [DistribLattice α] {a b c : α}

/--
lemma `eq_of_mem_uIcc_of_mem_uIcc` / 引理 `eq_of_mem_uIcc_of_mem_uIcc`

English:
lemma eq_of_mem_uIcc_of_mem_uIcc
  given: (ha : a in [[b, c]]) (hb : b in [[a, c]])
  statement: a = b
  proof: eq_of_inf_eq_sup_eq (inf_congr_right ha.1 hb.1) sup_congr_right ha.2 hb.2

中文:
引理 eq_of_mem_uIcc_of_mem_uIcc
  条件: (ha : a in [[b, c]]) (hb : b in [[a, c]])
  结论: a = b
  证明: eq_of_inf_eq_sup_eq (inf_congr_right ha.1 hb.1) sup_congr_right ha.2 hb.2

Depends on / 依赖: eq_of_inf_eq_sup_eq, inf_congr_right, sup_congr_right
-/
lemma eq_of_mem_uIcc_of_mem_uIcc (ha : a in [[b, c]]) (hb : b in [[a, c]]) : a = b :=
eq_of_inf_eq_sup_eq (inf_congr_right ha.1 hb.1) sup_congr_right ha.2 hb.2

/--
lemma `eq_of_mem_uIcc_of_mem_uIcc'` / 引理 `eq_of_mem_uIcc_of_mem_uIcc'`

English:
lemma eq_of_mem_uIcc_of_mem_uIcc'
  statement: b in [[a, c]] -> c in [[a, b]] -> b = c
  proof: by
  simpa only [uIcc_comm a] using eq_of_mem_uIcc_of_mem_uIcc

中文:
引理 eq_of_mem_uIcc_of_mem_uIcc'
  结论: b in [[a, c]] -> c in [[a, b]] -> b = c
  证明: by
  simpa only [uIcc_comm a] using eq_of_mem_uIcc_of_mem_uIcc

Depends on / 依赖: eq_of_mem_uIcc_of_mem_uIcc, uIcc_comm
-/
lemma eq_of_mem_uIcc_of_mem_uIcc' : b in [[a, c]] -> c in [[a, b]] -> b = c := by
  simpa only [uIcc_comm a] using eq_of_mem_uIcc_of_mem_uIcc

/--
lemma `uIcc_injective_right` / 引理 `uIcc_injective_right`

English:
lemma uIcc_injective_right
  given: (a : α)
  statement: Injective fun b => uIcc b a
  proof: fun b c h => by
  rw [Set.ext_iff] at h
  exact eq_of_mem_uIcc_of_mem_uIcc ((h _).1 left_mem_uIcc) ((h _).2 left_mem_uIcc)

中文:
引理 uIcc_injective_right
  条件: (a : α)
  结论: 单射 fun b => uIcc b a
  证明: fun b c h => by
  rw [Set.ext_iff] at h
  exact eq_of_mem_uIcc_of_mem_uIcc ((h _).1 left_mem_uIcc) ((h _).2 left_mem_uIcc)

Depends on / 依赖: Set.ext_iff, eq_of_mem_uIcc_of_mem_uIcc, ext_iff, left_mem_uIcc
-/
lemma uIcc_injective_right (a : α) : Injective fun b => uIcc b a := fun b c h => by
  rw [Set.ext_iff] at h
  exact eq_of_mem_uIcc_of_mem_uIcc ((h _).1 left_mem_uIcc) ((h _).2 left_mem_uIcc)

/--
lemma `uIcc_injective_left` / 引理 `uIcc_injective_left`

English:
lemma uIcc_injective_left
  given: (a : α)
  statement: Injective (uIcc a)
  proof: by
  simpa only [uIcc_comm] using uIcc_injective_right a

中文:
引理 uIcc_injective_left
  条件: (a : α)
  结论: 单射 (uIcc a)
  证明: by
  simpa only [uIcc_comm] using uIcc_injective_right a

Depends on / 依赖: uIcc_comm, uIcc_injective_right
-/
lemma uIcc_injective_left (a : α) : Injective (uIcc a) := by
  simpa only [uIcc_comm] using uIcc_injective_right a

end DistribLattice

section LinearOrder
variable [LinearOrder α]

section Lattice
variable [Lattice β] {f : α -> β} {a b : α}

/--
lemma `_root_.MonotoneOn.mapsTo_uIcc` / 引理 `_root_.MonotoneOn.mapsTo_uIcc`

English:
lemma _root_.MonotoneOn.mapsTo_uIcc
  given: (hf : MonotoneOn f (uIcc a b))
  proof: by
  rw [uIcc]; rw [uIcc]; rw [← hf.map_sup]; rw [← hf.map_inf] <;>
    apply_rules [left_mem_uIcc, right_mem_uIcc, hf.mapsTo_Icc]

中文:
引理 _root_.MonotoneOn.mapsTo_uIcc
  条件: (hf : MonotoneOn f (uIcc a b))
  证明: by
  rw [uIcc]; rw [uIcc]; rw [← hf.map_sup]; rw [← hf.map_inf] <;>
    apply_rules [left_mem_uIcc, right_mem_uIcc, hf.mapsTo_Icc]

Depends on / 依赖: apply_rules, hf.map_inf, hf.map_sup, hf.mapsTo_Icc, left_mem_uIcc, map_inf, map_sup, mapsTo_Icc, right_mem_uIcc
-/
lemma _root_.MonotoneOn.mapsTo_uIcc (hf : MonotoneOn f (uIcc a b)) :
    MapsTo f (uIcc a b) (uIcc (f a) (f b)) := by
  rw [uIcc]; rw [uIcc]; rw [← hf.map_sup]; rw [← hf.map_inf] <;>
    apply_rules [left_mem_uIcc, right_mem_uIcc, hf.mapsTo_Icc]

/--
lemma `_root_.AntitoneOn.mapsTo_uIcc` / 引理 `_root_.AntitoneOn.mapsTo_uIcc`

English:
lemma _root_.AntitoneOn.mapsTo_uIcc
  given: (hf : AntitoneOn f (uIcc a b))
  proof: by
  rw [uIcc]; rw [uIcc]; rw [← hf.map_sup]; rw [← hf.map_inf] <;>
    apply_rules [left_mem_uIcc, right_mem_uIcc, hf.mapsTo_Icc]

中文:
引理 _root_.AntitoneOn.mapsTo_uIcc
  条件: (hf : AntitoneOn f (uIcc a b))
  证明: by
  rw [uIcc]; rw [uIcc]; rw [← hf.map_sup]; rw [← hf.map_inf] <;>
    apply_rules [left_mem_uIcc, right_mem_uIcc, hf.mapsTo_Icc]

Depends on / 依赖: apply_rules, hf.map_inf, hf.map_sup, hf.mapsTo_Icc, left_mem_uIcc, map_inf, map_sup, mapsTo_Icc, right_mem_uIcc
-/
lemma _root_.AntitoneOn.mapsTo_uIcc (hf : AntitoneOn f (uIcc a b)) :
    MapsTo f (uIcc a b) (uIcc (f a) (f b)) := by
  rw [uIcc]; rw [uIcc]; rw [← hf.map_sup]; rw [← hf.map_inf] <;>
    apply_rules [left_mem_uIcc, right_mem_uIcc, hf.mapsTo_Icc]

/--
lemma `_root_.Monotone.mapsTo_uIcc` / 引理 `_root_.Monotone.mapsTo_uIcc`

English:
lemma _root_.Monotone.mapsTo_uIcc
  given: (hf : Monotone f)
  statement: MapsTo f (uIcc a b) (uIcc (f a) (f b))
  proof: (hf.monotoneOn _).mapsTo_uIcc

中文:
引理 _root_.递增.mapsTo_uIcc
  条件: (hf : 递增 f)
  结论: 映射到 f (uIcc a b) (uIcc (f a) (f b))
  证明: (hf.monotoneOn _).mapsTo_uIcc

Depends on / 依赖: hf.monotoneOn, mapsTo_uIcc, monotoneOn
-/
lemma _root_.Monotone.mapsTo_uIcc (hf : Monotone f) : MapsTo f (uIcc a b) (uIcc (f a) (f b)) :=
  (hf.monotoneOn _).mapsTo_uIcc

/--
lemma `_root_.Antitone.mapsTo_uIcc` / 引理 `_root_.Antitone.mapsTo_uIcc`

English:
lemma _root_.Antitone.mapsTo_uIcc
  given: (hf : Antitone f)
  statement: MapsTo f (uIcc a b) (uIcc (f a) (f b))
  proof: (hf.antitoneOn _).mapsTo_uIcc

中文:
引理 _root_.递减.mapsTo_uIcc
  条件: (hf : 递减 f)
  结论: 映射到 f (uIcc a b) (uIcc (f a) (f b))
  证明: (hf.antitoneOn _).mapsTo_uIcc

Depends on / 依赖: antitoneOn, hf.antitoneOn, mapsTo_uIcc
-/
lemma _root_.Antitone.mapsTo_uIcc (hf : Antitone f) : MapsTo f (uIcc a b) (uIcc (f a) (f b)) :=
  (hf.antitoneOn _).mapsTo_uIcc

/--
lemma `_root_.MonotoneOn.image_uIcc_subset` / 引理 `_root_.MonotoneOn.image_uIcc_subset`

English:
lemma _root_.MonotoneOn.image_uIcc_subset
  given: (hf : MonotoneOn f (uIcc a b))
  proof: hf.mapsTo_uIcc.image_subset

中文:
引理 _root_.MonotoneOn.image_uIcc_subset
  条件: (hf : MonotoneOn f (uIcc a b))
  证明: hf.mapsTo_uIcc.image_subset

Depends on / 依赖: hf.mapsTo_uIcc.image_subset, image_subset, mapsTo_uIcc
-/
lemma _root_.MonotoneOn.image_uIcc_subset (hf : MonotoneOn f (uIcc a b)) :
    f '' uIcc a b subseteq uIcc (f a) (f b) := hf.mapsTo_uIcc.image_subset

/--
lemma `_root_.AntitoneOn.image_uIcc_subset` / 引理 `_root_.AntitoneOn.image_uIcc_subset`

English:
lemma _root_.AntitoneOn.image_uIcc_subset
  given: (hf : AntitoneOn f (uIcc a b))
  proof: hf.mapsTo_uIcc.image_subset

中文:
引理 _root_.AntitoneOn.image_uIcc_subset
  条件: (hf : AntitoneOn f (uIcc a b))
  证明: hf.mapsTo_uIcc.image_subset

Depends on / 依赖: hf.mapsTo_uIcc.image_subset, image_subset, mapsTo_uIcc
-/
lemma _root_.AntitoneOn.image_uIcc_subset (hf : AntitoneOn f (uIcc a b)) :
    f '' uIcc a b subseteq uIcc (f a) (f b) := hf.mapsTo_uIcc.image_subset

/--
lemma `_root_.Monotone.image_uIcc_subset` / 引理 `_root_.Monotone.image_uIcc_subset`

English:
lemma _root_.Monotone.image_uIcc_subset
  given: (hf : Monotone f)
  statement: f '' uIcc a b subseteq uIcc (f a) (f b)
  proof: (hf.monotoneOn _).image_uIcc_subset

中文:
引理 _root_.递增.image_uIcc_subset
  条件: (hf : 递增 f)
  结论: f '' uIcc a b subseteq uIcc (f a) (f b)
  证明: (hf.monotoneOn _).image_uIcc_subset

Depends on / 依赖: hf.monotoneOn, image_uIcc_subset, monotoneOn
-/
lemma _root_.Monotone.image_uIcc_subset (hf : Monotone f) : f '' uIcc a b subseteq uIcc (f a) (f b) :=
  (hf.monotoneOn _).image_uIcc_subset

/--
lemma `_root_.Antitone.image_uIcc_subset` / 引理 `_root_.Antitone.image_uIcc_subset`

English:
lemma _root_.Antitone.image_uIcc_subset
  given: (hf : Antitone f)
  statement: f '' uIcc a b subseteq uIcc (f a) (f b)
  proof: (hf.antitoneOn _).image_uIcc_subset

中文:
引理 _root_.递减.image_uIcc_subset
  条件: (hf : 递减 f)
  结论: f '' uIcc a b subseteq uIcc (f a) (f b)
  证明: (hf.antitoneOn _).image_uIcc_subset

Depends on / 依赖: antitoneOn, hf.antitoneOn, image_uIcc_subset
-/
lemma _root_.Antitone.image_uIcc_subset (hf : Antitone f) : f '' uIcc a b subseteq uIcc (f a) (f b) :=
  (hf.antitoneOn _).image_uIcc_subset

end Lattice

variable [LinearOrder β] {f : α -> β} {s : Set α} {a a₁ a₂ b b₁ b₂ c : α}

/--
theorem `Icc_min_max` / 定理 `Icc_min_max`

English:
theorem Icc_min_max
  statement: Icc (min a b) (max a b) = [[a, b]]
  proof: rfl

中文:
定理 Icc_min_max
  结论: 闭区间 (最小值 a b) (最大值 a b) = [[a, b]]
  证明: rfl
-/
theorem Icc_min_max : Icc (min a b) (max a b) = [[a, b]] :=
  rfl

/--
lemma `uIcc_of_not_le` / 引理 `uIcc_of_not_le`

English:
lemma uIcc_of_not_le
  given: (h : ¬a <= b)
  statement: [[a, b]] = Icc b a
  proof: uIcc_of_gt lt_of_not_ge h

中文:
引理 uIcc_of_not_le
  条件: (h : ¬a <= b)
  结论: [[a, b]] = 闭区间 b a
  证明: uIcc_of_gt lt_of_not_ge h

Depends on / 依赖: lt_of_not_ge, uIcc_of_gt
-/
lemma uIcc_of_not_le (h : ¬a <= b) : [[a, b]] = Icc b a := uIcc_of_gt lt_of_not_ge h
/--
lemma `uIcc_of_not_ge` / 引理 `uIcc_of_not_ge`

English:
lemma uIcc_of_not_ge
  given: (h : ¬b <= a)
  statement: [[a, b]] = Icc a b
  proof: uIcc_of_lt lt_of_not_ge h

中文:
引理 uIcc_of_not_ge
  条件: (h : ¬b <= a)
  结论: [[a, b]] = 闭区间 a b
  证明: uIcc_of_lt lt_of_not_ge h

Depends on / 依赖: lt_of_not_ge, uIcc_of_lt
-/
lemma uIcc_of_not_ge (h : ¬b <= a) : [[a, b]] = Icc a b := uIcc_of_lt lt_of_not_ge h

/--
lemma `uIcc_eq_union` / 引理 `uIcc_eq_union`

English:
lemma uIcc_eq_union
  statement: [[a, b]] = Icc a b union Icc b a
  proof: by rw [Icc_union_Icc', max_comm] <;> rfl

中文:
引理 uIcc_eq_union
  结论: [[a, b]] = 闭区间 a b union 闭区间 b a
  证明: by rw [Icc_union_Icc', max_comm] <;> rfl

Depends on / 依赖: Icc_union_Icc, max_comm
-/
lemma uIcc_eq_union : [[a, b]] = Icc a b union Icc b a := by rw [Icc_union_Icc', max_comm] <;> rfl

/--
lemma `mem_uIcc` / 引理 `mem_uIcc`

English:
lemma mem_uIcc
  statement: a in [[b, c]] ↔ b <= a ∧ a <= c ∨ c <= a ∧ a <= b
  proof: by simp [uIcc_eq_union]

中文:
引理 mem_uIcc
  结论: a in [[b, c]] ↔ b <= a ∧ a <= c ∨ c <= a ∧ a <= b
  证明: by simp [uIcc_eq_union]

Depends on / 依赖: uIcc_eq_union
-/
lemma mem_uIcc : a in [[b, c]] ↔ b <= a ∧ a <= c ∨ c <= a ∧ a <= b := by simp [uIcc_eq_union]

/--
lemma `notMem_uIcc_of_lt` / 引理 `notMem_uIcc_of_lt`

English:
lemma notMem_uIcc_of_lt
  given: (ha : c < a) (hb : c < b)
  statement: c ∉ [[a, b]]
  proof: notMem_Icc_of_lt lt_min_iff.mpr ⟨ha, hb⟩

中文:
引理 notMem_uIcc_of_lt
  条件: (ha : c < a) (hb : c < b)
  结论: c ∉ [[a, b]]
  证明: notMem_Icc_of_lt lt_min_iff.mpr ⟨ha, hb⟩

Depends on / 依赖: lt_min_iff, lt_min_iff.mpr, notMem_Icc_of_lt
-/
lemma notMem_uIcc_of_lt (ha : c < a) (hb : c < b) : c ∉ [[a, b]] :=
notMem_Icc_of_lt lt_min_iff.mpr ⟨ha, hb⟩

/--
lemma `notMem_uIcc_of_gt` / 引理 `notMem_uIcc_of_gt`

English:
lemma notMem_uIcc_of_gt
  given: (ha : a < c) (hb : b < c)
  statement: c ∉ [[a, b]]
  proof: notMem_Icc_of_gt max_lt_iff.mpr ⟨ha, hb⟩

中文:
引理 notMem_uIcc_of_gt
  条件: (ha : a < c) (hb : b < c)
  结论: c ∉ [[a, b]]
  证明: notMem_Icc_of_gt max_lt_iff.mpr ⟨ha, hb⟩

Depends on / 依赖: max_lt_iff, max_lt_iff.mpr, notMem_Icc_of_gt
-/
lemma notMem_uIcc_of_gt (ha : a < c) (hb : b < c) : c ∉ [[a, b]] :=
notMem_Icc_of_gt max_lt_iff.mpr ⟨ha, hb⟩

/--
lemma `uIcc_subset_uIcc_iff_le` / 引理 `uIcc_subset_uIcc_iff_le`

English:
lemma uIcc_subset_uIcc_iff_le
  proof: uIcc_subset_uIcc_iff_le'

中文:
引理 uIcc_subset_uIcc_iff_le
  证明: uIcc_subset_uIcc_iff_le'

Depends on / 依赖: uIcc_subset_uIcc_iff_le
-/
lemma uIcc_subset_uIcc_iff_le :
    [[a₁, b₁]] subseteq [[a₂, b₂]] ↔ min a₂ b₂ <= min a₁ b₁ ∧ max a₁ b₁ <= max a₂ b₂ :=
  uIcc_subset_uIcc_iff_le'

/--
lemma `uIcc_subset_uIcc_union_uIcc` / 引理 `uIcc_subset_uIcc_union_uIcc`

English:
lemma uIcc_subset_uIcc_union_uIcc
  statement: [[a, c]] subseteq [[a, b]] union [[b, c]]
  proof: fun x => by
  simp only [mem_uIcc, mem_union]
  rcases le_total x b with h2 | h2 <;> tauto

中文:
引理 uIcc_subset_uIcc_union_uIcc
  结论: [[a, c]] subseteq [[a, b]] union [[b, c]]
  证明: fun x => by
  simp only [mem_uIcc, mem_union]
  rcases le_total x b with h2 | h2 <;> tauto

Depends on / 依赖: le_total, mem_uIcc, mem_union
-/
lemma uIcc_subset_uIcc_union_uIcc : [[a, c]] subseteq [[a, b]] union [[b, c]] := fun x => by
  simp only [mem_uIcc, mem_union]
  rcases le_total x b with h2 | h2 <;> tauto

/--
lemma `monotone_or_antitone_iff_uIcc` / 引理 `monotone_or_antitone_iff_uIcc`

English:
lemma monotone_or_antitone_iff_uIcc
  proof: by
  constructor
  · rintro (hf | hf) a b c <;> simp_rw [← Icc_min_max, ← hf.map_min, ← hf.map_max]
    exacts [fun hc => ⟨hf hc.1, hf hc.2⟩, fun hc => ⟨hf hc.2, hf hc.1⟩]
  contrapose!
  rw [not_monotone_not_antitone_iff_exists_le_le]
  rintro ⟨a, b, c, hab, hbc, ⟨hfab, hfcb⟩ | ⟨hfba, hfbc⟩⟩
· exact ⟨a, c, b, Icc_subset_uIcc ⟨hab, hbc⟩, fun h => h.2.not_gt max_lt hfab hfcb⟩
· exact ⟨a, c, b, Icc_subset_uIcc ⟨hab, hbc⟩, fun h => h.1.not_gt lt_min hfba hfbc⟩

中文:
引理 monotone_or_antitone_iff_uIcc
  证明: by
  constructor
  · rintro (hf | hf) a b c <;> simp_rw [← Icc_min_max, ← hf.map_min, ← hf.map_max]
    exacts [fun hc => ⟨hf hc.1, hf hc.2⟩, fun hc => ⟨hf hc.2, hf hc.1⟩]
  contrapose!
  rw [not_monotone_not_antitone_iff_exists_le_le]
  rintro ⟨a, b, c, hab, hbc, ⟨hfab, hfcb⟩ | ⟨hfba, hfbc⟩⟩
· exact ⟨a, c, b, Icc_subset_uIcc ⟨hab, hbc⟩, fun h => h.2.not_gt max_lt hfab hfcb⟩
· exact ⟨a, c, b, Icc_subset_uIcc ⟨hab, hbc⟩, fun h => h.1.not_gt lt_min hfba hfbc⟩

Depends on / 依赖: Icc_min_max, Icc_subset_uIcc, contrapose, exacts, hf.map_max, hf.map_min, lt_min, map_max, map_min, max_lt, not_gt, not_monotone_not_antitone_iff_exists_le_le, simp_rw
-/
lemma monotone_or_antitone_iff_uIcc :
    Monotone f ∨ Antitone f ↔ forall a b c, c in [[a, b]] -> f c in [[f a, f b]] := by
  constructor
  · rintro (hf | hf) a b c <;> simp_rw [← Icc_min_max, ← hf.map_min, ← hf.map_max]
    exacts [fun hc => ⟨hf hc.1, hf hc.2⟩, fun hc => ⟨hf hc.2, hf hc.1⟩]
  contrapose!
  rw [not_monotone_not_antitone_iff_exists_le_le]
  rintro ⟨a, b, c, hab, hbc, ⟨hfab, hfcb⟩ | ⟨hfba, hfbc⟩⟩
· exact ⟨a, c, b, Icc_subset_uIcc ⟨hab, hbc⟩, fun h => h.2.not_gt max_lt hfab hfcb⟩
· exact ⟨a, c, b, Icc_subset_uIcc ⟨hab, hbc⟩, fun h => h.1.not_gt lt_min hfba hfbc⟩

/--
lemma `monotoneOn_or_antitoneOn_iff_uIcc` / 引理 `monotoneOn_or_antitoneOn_iff_uIcc`

English:
lemma monotoneOn_or_antitoneOn_iff_uIcc
  proof: by
  simp [monotoneOn_iff_monotone, antitoneOn_iff_antitone, monotone_or_antitone_iff_uIcc,
    mem_uIcc]

中文:
引理 monotoneOn_or_antitoneOn_iff_uIcc
  证明: by
  simp [monotoneOn_iff_monotone, antitoneOn_iff_antitone, monotone_or_antitone_iff_uIcc,
    mem_uIcc]

Depends on / 依赖: antitoneOn_iff_antitone, mem_uIcc, monotoneOn_iff_monotone, monotone_or_antitone_iff_uIcc
-/
lemma monotoneOn_or_antitoneOn_iff_uIcc :
    MonotoneOn f s ∨ AntitoneOn f s ↔
      forallᵉ (a in s) (b in s) (c in s), c in [[a, b]] -> f c in [[f a, f b]] := by
  simp [monotoneOn_iff_monotone, antitoneOn_iff_antitone, monotone_or_antitone_iff_uIcc,
    mem_uIcc]

/--
Definition of `uIoc` / `uIoc` 的定义

English:
definition uIoc
  signature: : α -> α -> Set α
  body: fun a b => Ioc (min a b) (max a b)

中文:
定义 uIoc
  签名: : α -> α -> 集合 α
  定义体: fun a b => Ioc (min a b) (max a b)
-/
def uIoc : α -> α -> Set α := fun a b => Ioc (min a b) (max a b)

-- Below is a capital iota
/-- `Ι a b` denotes the open-closed interval with unordered bounds. Here, `Ι` is a capital iota,
distinguished from a capital `i`. -/
scoped[Interval] notation "Ι" => Set.uIoc

open scoped Interval

/--
lemma `uIoc_of_le` / 引理 `uIoc_of_le`

English:
lemma uIoc_of_le
  given: (h : a <= b)
  statement: Ι a b = Ioc a b
  proof: by simp [uIoc, h]

中文:
引理 uIoc_of_le
  条件: (h : a <= b)
  结论: Ι a b = 左开右闭区间 a b
  证明: by simp [uIoc, h]
-/
@[simp, grind =] lemma uIoc_of_le (h : a <= b) : Ι a b = Ioc a b := by simp [uIoc, h]
/--
lemma `uIoc_of_ge` / 引理 `uIoc_of_ge`

English:
lemma uIoc_of_ge
  given: (h : b <= a)
  statement: Ι a b = Ioc b a
  proof: by simp [uIoc, h]

中文:
引理 uIoc_of_ge
  条件: (h : b <= a)
  结论: Ι a b = 左开右闭区间 b a
  证明: by simp [uIoc, h]
-/
@[simp, grind =] lemma uIoc_of_ge (h : b <= a) : Ι a b = Ioc b a := by simp [uIoc, h]

/--
lemma `uIoc_eq_union` / 引理 `uIoc_eq_union`

English:
lemma uIoc_eq_union
  statement: Ι a b = Ioc a b union Ioc b a
  proof: by
  cases le_total a b <;> simp [uIoc, *]

中文:
引理 uIoc_eq_union
  结论: Ι a b = 左开右闭区间 a b union 左开右闭区间 b a
  证明: by
  cases le_total a b <;> simp [uIoc, *]

Depends on / 依赖: le_total
-/
lemma uIoc_eq_union : Ι a b = Ioc a b union Ioc b a := by
  cases le_total a b <;> simp [uIoc, *]

/--
lemma `mem_uIoc` / 引理 `mem_uIoc`

English:
lemma mem_uIoc
  statement: a in Ι b c ↔ b < a ∧ a <= c ∨ c < a ∧ a <= b
  proof: by
  rw [uIoc_eq_union]; rw [mem_union]; rw [mem_Ioc]; rw [mem_Ioc]

中文:
引理 mem_uIoc
  结论: a in Ι b c ↔ b < a ∧ a <= c ∨ c < a ∧ a <= b
  证明: by
  rw [uIoc_eq_union]; rw [mem_union]; rw [mem_Ioc]; rw [mem_Ioc]

Depends on / 依赖: mem_Ioc, mem_union, uIoc_eq_union
-/
lemma mem_uIoc : a in Ι b c ↔ b < a ∧ a <= c ∨ c < a ∧ a <= b := by
  rw [uIoc_eq_union]; rw [mem_union]; rw [mem_Ioc]; rw [mem_Ioc]

/--
lemma `notMem_uIoc` / 引理 `notMem_uIoc`

English:
lemma notMem_uIoc
  statement: a ∉ Ι b c ↔ a <= b ∧ a <= c ∨ c < a ∧ b < a
  proof: by
  simp only [uIoc_eq_union, mem_union, mem_Ioc, ← not_le]
  tauto

中文:
引理 notMem_uIoc
  结论: a ∉ Ι b c ↔ a <= b ∧ a <= c ∨ c < a ∧ b < a
  证明: by
  simp only [uIoc_eq_union, mem_union, mem_Ioc, ← not_le]
  tauto

Depends on / 依赖: mem_Ioc, mem_union, not_le, uIoc_eq_union
-/
lemma notMem_uIoc : a ∉ Ι b c ↔ a <= b ∧ a <= c ∨ c < a ∧ b < a := by
  simp only [uIoc_eq_union, mem_union, mem_Ioc, ← not_le]
  tauto

/--
lemma `left_mem_uIoc` / 引理 `left_mem_uIoc`

English:
lemma left_mem_uIoc
  statement: a in Ι a b ↔ b < a
  proof: by simp [mem_uIoc]

中文:
引理 left_mem_uIoc
  结论: a in Ι a b ↔ b < a
  证明: by simp [mem_uIoc]
-/
@[simp] lemma left_mem_uIoc : a in Ι a b ↔ b < a := by simp [mem_uIoc]
/--
lemma `right_mem_uIoc` / 引理 `right_mem_uIoc`

English:
lemma right_mem_uIoc
  statement: b in Ι a b ↔ a < b
  proof: by simp [mem_uIoc]

中文:
引理 right_mem_uIoc
  结论: b in Ι a b ↔ a < b
  证明: by simp [mem_uIoc]
-/
@[simp] lemma right_mem_uIoc : b in Ι a b ↔ a < b := by simp [mem_uIoc]

/--
lemma `forall_uIoc_iff` / 引理 `forall_uIoc_iff`

English:
lemma forall_uIoc_iff
  given: {P : α -> Prop}
  proof: by
  simp only [uIoc_eq_union, mem_union, or_imp, forall_and]

中文:
引理 对任意_uIoc_iff
  条件: {P : α -> 命题}
  证明: by
  simp only [uIoc_eq_union, mem_union, or_imp, forall_and]

Depends on / 依赖: forall_and, mem_union, or_imp, uIoc_eq_union
-/
lemma forall_uIoc_iff {P : α -> Prop} :
    (forall x in Ι a b, P x) ↔ (forall x in Ioc a b, P x) ∧ forall x in Ioc b a, P x := by
  simp only [uIoc_eq_union, mem_union, or_imp, forall_and]

/--
lemma `uIoc_subset_uIoc_of_uIcc_subset_uIcc` / 引理 `uIoc_subset_uIoc_of_uIcc_subset_uIcc`

English:
lemma uIoc_subset_uIoc_of_uIcc_subset_uIcc
  statement: {a b c d : α}
  proof: Ioc_subset_Ioc (uIcc_subset_uIcc_iff_le.1 h).1 (uIcc_subset_uIcc_iff_le.1 h).2

中文:
引理 uIoc_subset_uIoc_of_uIcc_subset_uIcc
  结论: {a b c d : α}
  证明: Ioc_subset_Ioc (uIcc_subset_uIcc_iff_le.1 h).1 (uIcc_subset_uIcc_iff_le.1 h).2

Depends on / 依赖: Ioc_subset_Ioc, uIcc_subset_uIcc_iff_le
-/
lemma uIoc_subset_uIoc_of_uIcc_subset_uIcc {a b c d : α}
    (h : [[a, b]] subseteq [[c, d]]) : Ι a b subseteq Ι c d :=
  Ioc_subset_Ioc (uIcc_subset_uIcc_iff_le.1 h).1 (uIcc_subset_uIcc_iff_le.1 h).2

/--
lemma `uIoc_comm` / 引理 `uIoc_comm`

English:
lemma uIoc_comm
  given: (a b : α)
  statement: Ι a b = Ι b a
  proof: by simp only [uIoc, min_comm a b, max_comm a b]

中文:
引理 uIoc_comm
  条件: (a b : α)
  结论: Ι a b = Ι b a
  证明: by simp only [uIoc, min_comm a b, max_comm a b]

Depends on / 依赖: max_comm, min_comm
-/
lemma uIoc_comm (a b : α) : Ι a b = Ι b a := by simp only [uIoc, min_comm a b, max_comm a b]

/--
lemma `Ioc_subset_uIoc` / 引理 `Ioc_subset_uIoc`

English:
lemma Ioc_subset_uIoc
  statement: Ioc a b subseteq Ι a b
  proof: Ioc_subset_Ioc (min_le_left _ _) (le_max_right _ _)

中文:
引理 Ioc_subset_uIoc
  结论: 左开右闭区间 a b subseteq Ι a b
  证明: Ioc_subset_Ioc (min_le_left _ _) (le_max_right _ _)

Depends on / 依赖: Ioc_subset_Ioc, le_max_right, min_le_left
-/
lemma Ioc_subset_uIoc : Ioc a b subseteq Ι a b := Ioc_subset_Ioc (min_le_left _ _) (le_max_right _ _)
/--
lemma `Ioc_subset_uIoc'` / 引理 `Ioc_subset_uIoc'`

English:
lemma Ioc_subset_uIoc'
  statement: Ioc a b subseteq Ι b a
  proof: Ioc_subset_Ioc (min_le_right _ _) (le_max_left _ _)

中文:
引理 Ioc_subset_uIoc'
  结论: 左开右闭区间 a b subseteq Ι b a
  证明: Ioc_subset_Ioc (min_le_right _ _) (le_max_left _ _)

Depends on / 依赖: Ioc_subset_Ioc, le_max_left, min_le_right
-/
lemma Ioc_subset_uIoc' : Ioc a b subseteq Ι b a := Ioc_subset_Ioc (min_le_right _ _) (le_max_left _ _)

/--
lemma `uIoc_subset_uIcc` / 引理 `uIoc_subset_uIcc`

English:
lemma uIoc_subset_uIcc
  statement: Ι a b subseteq uIcc a b
  proof: Ioc_subset_Icc_self

中文:
引理 uIoc_subset_uIcc
  结论: Ι a b subseteq uIcc a b
  证明: Ioc_subset_Icc_self

Depends on / 依赖: Ioc_subset_Icc_self
-/
lemma uIoc_subset_uIcc : Ι a b subseteq uIcc a b := Ioc_subset_Icc_self

/--
lemma `eq_of_mem_uIoc_of_mem_uIoc` / 引理 `eq_of_mem_uIoc_of_mem_uIoc`

English:
lemma eq_of_mem_uIoc_of_mem_uIoc
  statement: a in Ι b c -> b in Ι a c -> a = b
  proof: by
  simp_rw [mem_uIoc]; rintro (⟨_, _⟩ | ⟨_, _⟩) (⟨_, _⟩ | ⟨_, _⟩) <;> apply le_antisymm <;>
    first | assumption | exact le_of_lt ‹_› | exact le_trans ‹_› (le_of_lt ‹_›)

中文:
引理 eq_of_mem_uIoc_of_mem_uIoc
  结论: a in Ι b c -> b in Ι a c -> a = b
  证明: by
  simp_rw [mem_uIoc]; rintro (⟨_, _⟩ | ⟨_, _⟩) (⟨_, _⟩ | ⟨_, _⟩) <;> apply le_antisymm <;>
    first | assumption | exact le_of_lt ‹_› | exact le_trans ‹_› (le_of_lt ‹_›)

Depends on / 依赖: le_antisymm, le_of_lt, le_trans, mem_uIoc, simp_rw
-/
lemma eq_of_mem_uIoc_of_mem_uIoc : a in Ι b c -> b in Ι a c -> a = b := by
  simp_rw [mem_uIoc]; rintro (⟨_, _⟩ | ⟨_, _⟩) (⟨_, _⟩ | ⟨_, _⟩) <;> apply le_antisymm <;>
    first | assumption | exact le_of_lt ‹_› | exact le_trans ‹_› (le_of_lt ‹_›)

/--
lemma `eq_of_mem_uIoc_of_mem_uIoc'` / 引理 `eq_of_mem_uIoc_of_mem_uIoc'`

English:
lemma eq_of_mem_uIoc_of_mem_uIoc'
  statement: b in Ι a c -> c in Ι a b -> b = c
  proof: by
  simpa only [uIoc_comm a] using eq_of_mem_uIoc_of_mem_uIoc

中文:
引理 eq_of_mem_uIoc_of_mem_uIoc'
  结论: b in Ι a c -> c in Ι a b -> b = c
  证明: by
  simpa only [uIoc_comm a] using eq_of_mem_uIoc_of_mem_uIoc

Depends on / 依赖: eq_of_mem_uIoc_of_mem_uIoc, uIoc_comm
-/
lemma eq_of_mem_uIoc_of_mem_uIoc' : b in Ι a c -> c in Ι a b -> b = c := by
  simpa only [uIoc_comm a] using eq_of_mem_uIoc_of_mem_uIoc

/--
lemma `eq_of_notMem_uIoc_of_notMem_uIoc` / 引理 `eq_of_notMem_uIoc_of_notMem_uIoc`

English:
lemma eq_of_notMem_uIoc_of_notMem_uIoc
  given: (ha : a <= c) (hb : b <= c)
  proof: by
  grind

中文:
引理 eq_of_notMem_uIoc_of_notMem_uIoc
  条件: (ha : a <= c) (hb : b <= c)
  证明: by
  grind
-/
lemma eq_of_notMem_uIoc_of_notMem_uIoc (ha : a <= c) (hb : b <= c) :
    a ∉ Ι b c -> b ∉ Ι a c -> a = b := by
  grind

/--
lemma `uIoc_injective_right` / 引理 `uIoc_injective_right`

English:
lemma uIoc_injective_right
  given: (a : α)
  statement: Injective fun b => Ι b a
  proof: by
  rintro b c h
  rw [Set.ext_iff] at h
  obtain ha | ha := le_or_gt b a
  · have hb := (h b).not
    simp only [ha, left_mem_uIoc, true_iff, notMem_uIoc, ← not_le,
      and_true, not_true, false_and, not_false_iff, or_false] at hb
    refine hb.eq_of_not_lt fun hc => ?_
    simpa [ha, and_iff_right hc, ← @not_le _ _ _ a, iff_not_self, -not_le] using h c
  · refine
      eq_of_mem_uIoc_of_mem_uIoc ((h _).1 <| left_mem_uIoc.2 ha)
        ((h _).2 <| left_mem_uIoc.2 <| ha.trans_le ?_)
    simpa [ha, ha.not_ge, mem_uIoc] using h b

中文:
引理 uIoc_injective_right
  条件: (a : α)
  结论: 单射 fun b => Ι b a
  证明: by
  rintro b c h
  rw [Set.ext_iff] at h
  obtain ha | ha := le_or_gt b a
  · have hb := (h b).not
    simp only [ha, left_mem_uIoc, true_iff, notMem_uIoc, ← not_le,
      and_true, not_true, false_and, not_false_iff, or_false] at hb
    refine hb.eq_of_not_lt fun hc => ?_
    simpa [ha, and_iff_right hc, ← @not_le _ _ _ a, iff_not_self, -not_le] using h c
  · refine
      eq_of_mem_uIoc_of_mem_uIoc ((h _).1 <| left_mem_uIoc.2 ha)
        ((h _).2 <| left_mem_uIoc.2 <| ha.trans_le ?_)
    simpa [ha, ha.not_ge, mem_uIoc] using h b

Depends on / 依赖: Set.ext_iff, and_iff_right, and_true, eq_of_mem_uIoc_of_mem_uIoc, eq_of_not_lt, ext_iff, false_and, ha.not_ge, ha.trans_le, hb.eq_of_not_lt, iff_not_self, le_or_gt, left_mem_uIoc, mem_uIoc, notMem_uIoc, not_false_iff, not_ge, not_le, not_true, or_false
-/
lemma uIoc_injective_right (a : α) : Injective fun b => Ι b a := by
  rintro b c h
  rw [Set.ext_iff] at h
  obtain ha | ha := le_or_gt b a
  · have hb := (h b).not
    simp only [ha, left_mem_uIoc, true_iff, notMem_uIoc, ← not_le,
      and_true, not_true, false_and, not_false_iff, or_false] at hb
    refine hb.eq_of_not_lt fun hc => ?_
    simpa [ha, and_iff_right hc, ← @not_le _ _ _ a, iff_not_self, -not_le] using h c
  · refine
      eq_of_mem_uIoc_of_mem_uIoc ((h _).1 <| left_mem_uIoc.2 ha)
        ((h _).2 <| left_mem_uIoc.2 <| ha.trans_le ?_)
    simpa [ha, ha.not_ge, mem_uIoc] using h b

/--
lemma `uIoc_injective_left` / 引理 `uIoc_injective_left`

English:
lemma uIoc_injective_left
  given: (a : α)
  statement: Injective (Ι a)
  proof: by
  simpa only [uIoc_comm] using uIoc_injective_right a

中文:
引理 uIoc_injective_left
  条件: (a : α)
  结论: 单射 (Ι a)
  证明: by
  simpa only [uIoc_comm] using uIoc_injective_right a

Depends on / 依赖: uIoc_comm, uIoc_injective_right
-/
lemma uIoc_injective_left (a : α) : Injective (Ι a) := by
  simpa only [uIoc_comm] using uIoc_injective_right a

/--
lemma `uIoc_union_uIoc` / 引理 `uIoc_union_uIoc`

English:
lemma uIoc_union_uIoc
  given: (h : b in [[a, c]])
  statement: Ι a b union Ι b c = Ι a c
  proof: by
  wlog hac : a <= c generalizing a c
  · rw [uIoc_comm, union_comm, uIoc_comm, this _ (le_of_not_ge hac), uIoc_comm]
    rwa [uIcc_comm]
  rw [uIcc_of_le hac] at h
  rw [uIoc_of_le h.1]; rw [uIoc_of_le h.2]; rw [uIoc_of_le hac]; rw [Ioc_union_Ioc_eq_Ioc h.1 h.2]

中文:
引理 uIoc_union_uIoc
  条件: (h : b in [[a, c]])
  结论: Ι a b union Ι b c = Ι a c
  证明: by
  wlog hac : a <= c generalizing a c
  · rw [uIoc_comm, union_comm, uIoc_comm, this _ (le_of_not_ge hac), uIoc_comm]
    rwa [uIcc_comm]
  rw [uIcc_of_le hac] at h
  rw [uIoc_of_le h.1]; rw [uIoc_of_le h.2]; rw [uIoc_of_le hac]; rw [Ioc_union_Ioc_eq_Ioc h.1 h.2]

Depends on / 依赖: Ioc_union_Ioc_eq_Ioc, generalizing, le_of_not_ge, uIcc_comm, uIcc_of_le, uIoc_comm, uIoc_of_le, union_comm
-/
lemma uIoc_union_uIoc (h : b in [[a, c]]) : Ι a b union Ι b c = Ι a c := by
  wlog hac : a <= c generalizing a c
  · rw [uIoc_comm, union_comm, uIoc_comm, this _ (le_of_not_ge hac), uIoc_comm]
    rwa [uIcc_comm]
  rw [uIcc_of_le hac] at h
  rw [uIoc_of_le h.1]; rw [uIoc_of_le h.2]; rw [uIoc_of_le hac]; rw [Ioc_union_Ioc_eq_Ioc h.1 h.2]

section uIoo

/--
Definition of `uIoo` / `uIoo` 的定义

English:
definition uIoo
  signature: (a b : α)
  body: Ioo (a ⊓ b) (a ⊔ b)

@[simp]

中文:
定义 uIoo
  签名: (a b : α)
  定义体: Ioo (a ⊓ b) (a ⊔ b)

@[simp]
-/
def uIoo (a b : α) : Set α := Ioo (a ⊓ b) (a ⊔ b)

@[simp]
/--
lemma `uIoo_toDual` / 引理 `uIoo_toDual`

English:
lemma uIoo_toDual
  given: (a b : α)
  statement: uIoo (toDual a) (toDual b) = ofDual ⁻¹' uIoo a b
  proof: Ioo_toDual (α := α)

@[simp]

中文:
引理 uIoo_toDual
  条件: (a b : α)
  结论: uIoo (toDual a) (toDual b) = ofDual ⁻¹' uIoo a b
  证明: Ioo_toDual (α := α)

@[simp]

Depends on / 依赖: Ioo_toDual
-/
lemma uIoo_toDual (a b : α) : uIoo (toDual a) (toDual b) = ofDual ⁻¹' uIoo a b :=
  Ioo_toDual (α := α)

@[simp]
/--
theorem `uIoo_ofDual` / 定理 `uIoo_ofDual`

English:
theorem uIoo_ofDual
  given: (a b : αᵒᵈ)
  statement: uIoo (ofDual a) (ofDual b) = toDual ⁻¹' uIoo a b
  proof: Ioo_ofDual

中文:
定理 uIoo_ofDual
  条件: (a b : αᵒᵈ)
  结论: uIoo (ofDual a) (ofDual b) = toDual ⁻¹' uIoo a b
  证明: Ioo_ofDual

Depends on / 依赖: Ioo_ofDual
-/
theorem uIoo_ofDual (a b : αᵒᵈ) : uIoo (ofDual a) (ofDual b) = toDual ⁻¹' uIoo a b :=
  Ioo_ofDual

/--
lemma `uIoo_of_le` / 引理 `uIoo_of_le`

English:
lemma uIoo_of_le
  given: (h : a <= b)
  statement: uIoo a b = Ioo a b
  proof: by
  rw [uIoo]; rw [inf_eq_left.2 h]; rw [sup_eq_right.2 h]

中文:
引理 uIoo_of_le
  条件: (h : a <= b)
  结论: uIoo a b = 开区间 a b
  证明: by
  rw [uIoo]; rw [inf_eq_left.2 h]; rw [sup_eq_right.2 h]
-/
@[simp] lemma uIoo_of_le (h : a <= b) : uIoo a b = Ioo a b := by
  rw [uIoo]; rw [inf_eq_left.2 h]; rw [sup_eq_right.2 h]

/--
lemma `uIoo_of_ge` / 引理 `uIoo_of_ge`

English:
lemma uIoo_of_ge
  given: (h : b <= a)
  statement: uIoo a b = Ioo b a
  proof: by
  rw [uIoo]; rw [inf_eq_right.2 h]; rw [sup_eq_left.2 h]

中文:
引理 uIoo_of_ge
  条件: (h : b <= a)
  结论: uIoo a b = 开区间 b a
  证明: by
  rw [uIoo]; rw [inf_eq_right.2 h]; rw [sup_eq_left.2 h]
-/
@[simp] lemma uIoo_of_ge (h : b <= a) : uIoo a b = Ioo b a := by
  rw [uIoo]; rw [inf_eq_right.2 h]; rw [sup_eq_left.2 h]

/--
lemma `uIoo_comm` / 引理 `uIoo_comm`

English:
lemma uIoo_comm
  given: (a b : α)
  statement: uIoo a b = uIoo b a
  proof: by simp_rw [uIoo, inf_comm, sup_comm]

中文:
引理 uIoo_comm
  条件: (a b : α)
  结论: uIoo a b = uIoo b a
  证明: by simp_rw [uIoo, inf_comm, sup_comm]

Depends on / 依赖: inf_comm, simp_rw, sup_comm
-/
lemma uIoo_comm (a b : α) : uIoo a b = uIoo b a := by simp_rw [uIoo, inf_comm, sup_comm]

/--
lemma `uIoo_of_lt` / 引理 `uIoo_of_lt`

English:
lemma uIoo_of_lt
  given: (h : a < b)
  statement: uIoo a b = Ioo a b
  proof: uIoo_of_le h.le

中文:
引理 uIoo_of_lt
  条件: (h : a < b)
  结论: uIoo a b = 开区间 a b
  证明: uIoo_of_le h.le

Depends on / 依赖: h.le, uIoo_of_le
-/
lemma uIoo_of_lt (h : a < b) : uIoo a b = Ioo a b := uIoo_of_le h.le

/--
lemma `uIoo_of_gt` / 引理 `uIoo_of_gt`

English:
lemma uIoo_of_gt
  given: (h : b < a)
  statement: uIoo a b = Ioo b a
  proof: uIoo_of_ge h.le

中文:
引理 uIoo_of_gt
  条件: (h : b < a)
  结论: uIoo a b = 开区间 b a
  证明: uIoo_of_ge h.le

Depends on / 依赖: h.le, uIoo_of_ge
-/
lemma uIoo_of_gt (h : b < a) : uIoo a b = Ioo b a := uIoo_of_ge h.le

/--
lemma `uIoo_self` / 引理 `uIoo_self`

English:
lemma uIoo_self
  statement: uIoo a a = ∅
  proof: by simp [uIoo]

中文:
引理 uIoo_self
  结论: uIoo a a = ∅
  证明: by simp [uIoo]
-/
lemma uIoo_self : uIoo a a = ∅ := by simp [uIoo]

/--
lemma `left_notMem_uIoo` / 引理 `left_notMem_uIoo`

English:
lemma left_notMem_uIoo
  statement: a ∉ uIoo a b
  proof: by simp +contextual [uIoo, le_of_lt]

中文:
引理 left_notMem_uIoo
  结论: a ∉ uIoo a b
  证明: by simp +contextual [uIoo, le_of_lt]
-/
@[simp] lemma left_notMem_uIoo : a ∉ uIoo a b := by simp +contextual [uIoo, le_of_lt]
/--
lemma `right_notMem_uIoo` / 引理 `right_notMem_uIoo`

English:
lemma right_notMem_uIoo
  statement: b ∉ uIoo a b
  proof: by simp +contextual [uIoo, le_of_lt]

中文:
引理 right_notMem_uIoo
  结论: b ∉ uIoo a b
  证明: by simp +contextual [uIoo, le_of_lt]
-/
@[simp] lemma right_notMem_uIoo : b ∉ uIoo a b := by simp +contextual [uIoo, le_of_lt]

/--
lemma `Ioo_subset_uIoo` / 引理 `Ioo_subset_uIoo`

English:
lemma Ioo_subset_uIoo
  statement: Ioo a b subseteq uIoo a b
  proof: Ioo_subset_Ioo inf_le_left le_sup_right

中文:
引理 Ioo_subset_uIoo
  结论: 开区间 a b subseteq uIoo a b
  证明: Ioo_subset_Ioo inf_le_left le_sup_right

Depends on / 依赖: Ioo_subset_Ioo, inf_le_left, le_sup_right
-/
lemma Ioo_subset_uIoo : Ioo a b subseteq uIoo a b := Ioo_subset_Ioo inf_le_left le_sup_right

/--
lemma `Ioo_subset_uIoo'` / 引理 `Ioo_subset_uIoo'`

English:
lemma Ioo_subset_uIoo'
  statement: Ioo b a subseteq uIoo a b
  proof: Ioo_subset_Ioo inf_le_right le_sup_left

中文:
引理 Ioo_subset_uIoo'
  结论: 开区间 b a subseteq uIoo a b
  证明: Ioo_subset_Ioo inf_le_right le_sup_left

Depends on / 依赖: Ioo_subset_Ioo, inf_le_right, le_sup_left
-/
lemma Ioo_subset_uIoo' : Ioo b a subseteq uIoo a b := Ioo_subset_Ioo inf_le_right le_sup_left

variable {x : α}

/--
lemma `mem_uIoo_of_lt` / 引理 `mem_uIoo_of_lt`

English:
lemma mem_uIoo_of_lt
  given: (ha : a < x) (hb : x < b)
  statement: x in uIoo a b
  proof: Ioo_subset_uIoo ⟨ha, hb⟩

中文:
引理 mem_uIoo_of_lt
  条件: (ha : a < x) (hb : x < b)
  结论: x in uIoo a b
  证明: Ioo_subset_uIoo ⟨ha, hb⟩

Depends on / 依赖: Ioo_subset_uIoo
-/
lemma mem_uIoo_of_lt (ha : a < x) (hb : x < b) : x in uIoo a b := Ioo_subset_uIoo ⟨ha, hb⟩

/--
lemma `mem_uIoo_of_gt` / 引理 `mem_uIoo_of_gt`

English:
lemma mem_uIoo_of_gt
  given: (hb : b < x) (ha : x < a)
  statement: x in uIoo a b
  proof: Ioo_subset_uIoo' ⟨hb, ha⟩

中文:
引理 mem_uIoo_of_gt
  条件: (hb : b < x) (ha : x < a)
  结论: x in uIoo a b
  证明: Ioo_subset_uIoo' ⟨hb, ha⟩

Depends on / 依赖: Ioo_subset_uIoo
-/
lemma mem_uIoo_of_gt (hb : b < x) (ha : x < a) : x in uIoo a b := Ioo_subset_uIoo' ⟨hb, ha⟩

variable {a b : α}

/--
theorem `Ioo_min_max` / 定理 `Ioo_min_max`

English:
theorem Ioo_min_max
  statement: Ioo (min a b) (max a b) = uIoo a b
  proof: rfl

中文:
定理 Ioo_min_max
  结论: 开区间 (最小值 a b) (最大值 a b) = uIoo a b
  证明: rfl
-/
theorem Ioo_min_max : Ioo (min a b) (max a b) = uIoo a b := rfl

/--
lemma `uIoo_of_not_le` / 引理 `uIoo_of_not_le`

English:
lemma uIoo_of_not_le
  given: (h : ¬a <= b)
  statement: uIoo a b = Ioo b a
  proof: uIoo_of_gt lt_of_not_ge h

中文:
引理 uIoo_of_not_le
  条件: (h : ¬a <= b)
  结论: uIoo a b = 开区间 b a
  证明: uIoo_of_gt lt_of_not_ge h

Depends on / 依赖: lt_of_not_ge, uIoo_of_gt
-/
lemma uIoo_of_not_le (h : ¬a <= b) : uIoo a b = Ioo b a := uIoo_of_gt lt_of_not_ge h

/--
lemma `uIoo_of_not_ge` / 引理 `uIoo_of_not_ge`

English:
lemma uIoo_of_not_ge
  given: (h : ¬b <= a)
  statement: uIoo a b = Ioo a b
  proof: uIoo_of_lt lt_of_not_ge h

中文:
引理 uIoo_of_not_ge
  条件: (h : ¬b <= a)
  结论: uIoo a b = 开区间 a b
  证明: uIoo_of_lt lt_of_not_ge h

Depends on / 依赖: lt_of_not_ge, uIoo_of_lt
-/
lemma uIoo_of_not_ge (h : ¬b <= a) : uIoo a b = Ioo a b := uIoo_of_lt lt_of_not_ge h

/--
lemma `uIoo_subset_uIcc_self` / 引理 `uIoo_subset_uIcc_self`

English:
lemma uIoo_subset_uIcc_self
  statement: uIoo a b subseteq uIcc a b
  proof: by
  simp [uIoo, uIcc, Ioo_subset_Icc_self]

中文:
引理 uIoo_subset_uIcc_self
  结论: uIoo a b subseteq uIcc a b
  证明: by
  simp [uIoo, uIcc, Ioo_subset_Icc_self]

Depends on / 依赖: Ioo_subset_Icc_self
-/
lemma uIoo_subset_uIcc_self : uIoo a b subseteq uIcc a b := by
  simp [uIoo, uIcc, Ioo_subset_Icc_self]

/--
lemma `uIoo_subset_Ioo` / 引理 `uIoo_subset_Ioo`

English:
lemma uIoo_subset_Ioo
  given: (ha : a₁ in Icc a₂ b₂) (hb : b₁ in Icc a₂ b₂)
  statement: uIoo a₁ b₁ subseteq Ioo a₂ b₂
  proof: Ioo_subset_Ioo (le_inf ha.1 hb.1) (sup_le ha.2 hb.2)

中文:
引理 uIoo_subset_Ioo
  条件: (ha : a₁ in 闭区间 a₂ b₂) (hb : b₁ in 闭区间 a₂ b₂)
  结论: uIoo a₁ b₁ subseteq 开区间 a₂ b₂
  证明: Ioo_subset_Ioo (le_inf ha.1 hb.1) (sup_le ha.2 hb.2)

Depends on / 依赖: Ioo_subset_Ioo, le_inf, sup_le
-/
lemma uIoo_subset_Ioo (ha : a₁ in Icc a₂ b₂) (hb : b₁ in Icc a₂ b₂) : uIoo a₁ b₁ subseteq Ioo a₂ b₂ :=
  Ioo_subset_Ioo (le_inf ha.1 hb.1) (sup_le ha.2 hb.2)

/--
lemma `nonempty_uIoo` / 引理 `nonempty_uIoo`

English:
lemma nonempty_uIoo
  given: [DenselyOrdered α]
  statement: (uIoo a b).Nonempty ↔ a != b
  proof: by
  simp [uIoo, eq_comm]

中文:
引理 nonempty_uIoo
  条件: [稠密序 α]
  结论: (uIoo a b).非空 ↔ a != b
  证明: by
  simp [uIoo, eq_comm]
-/
@[simp] lemma nonempty_uIoo [DenselyOrdered α] : (uIoo a b).Nonempty ↔ a != b := by
  simp [uIoo, eq_comm]

/--
lemma `nonempty_uIoc` / 引理 `nonempty_uIoc`

English:
lemma nonempty_uIoc
  statement: (uIoc a b).Nonempty ↔ a != b
  proof: by
  simp [uIoc, eq_comm]

中文:
引理 nonempty_uIoc
  结论: (uIoc a b).非空 ↔ a != b
  证明: by
  simp [uIoc, eq_comm]
-/
@[simp] lemma nonempty_uIoc : (uIoc a b).Nonempty ↔ a != b := by
  simp [uIoc, eq_comm]

/--
lemma `uIoo_eq_union` / 引理 `uIoo_eq_union`

English:
lemma uIoo_eq_union
  statement: uIoo a b = Ioo a b union Ioo b a
  proof: by
  rcases lt_or_ge a b with h | h
  · simp [uIoo_of_lt, h, Ioo_eq_empty_of_le h.le]
  · simp [uIoo_of_ge, h]

中文:
引理 uIoo_eq_union
  结论: uIoo a b = 开区间 a b union 开区间 b a
  证明: by
  rcases lt_or_ge a b with h | h
  · simp [uIoo_of_lt, h, Ioo_eq_empty_of_le h.le]
  · simp [uIoo_of_ge, h]

Depends on / 依赖: Ioo_eq_empty_of_le, h.le, lt_or_ge, uIoo_of_ge, uIoo_of_lt
-/
lemma uIoo_eq_union : uIoo a b = Ioo a b union Ioo b a := by
  rcases lt_or_ge a b with h | h
  · simp [uIoo_of_lt, h, Ioo_eq_empty_of_le h.le]
  · simp [uIoo_of_ge, h]

end uIoo

end LinearOrder

end Set
