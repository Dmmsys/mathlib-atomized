/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Minchao Wu
-/
module

public import Mathlib.Data.Prod.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Lattice
public import Mathlib.Order.Lex
public import Mathlib.Tactic.Tauto
public import Mathlib.Tactic.FastInstance

/-!
# Lexicographic order

This file defines the lexicographic relation for pairs of orders, partial orders and linear orders.

## Main declarations

* `Prod.Lex.<pre/partial/linear>Order`: Instances lifting the orders on `α` and `β` to `α ×ₗ β`.

## Notation

* `α ×ₗ β`: `α × β` equipped with the lexicographic order

## See also

Related files are:
* `Data.Finset.CoLex`: Colexicographic order on finite sets.
* `Data.List.Lex`: Lexicographic order on lists.
* `Data.Pi.Lex`: Lexicographic order on `Πₗ i, α i`.
* `Data.PSigma.Order`: Lexicographic order on `Σ' i, α i`.
* `Data.Sigma.Order`: Lexicographic order on `Σ i, α i`.

# TODO

Some lemmas could be automatically generated with `to_dual`.
See [https://github.com/leanprover-community/mathlib4/pull/37939#discussion_r3367855484]

-/

@[expose] public section


variable {α β : Type*}

namespace Prod.Lex

@[inherit_doc] notation:35 α " ×ₗ " β:34 => Lex (Prod α β)

/--
Instance `instLE` / 实例 `instLE`

English:
instance instLE
  signature: (α β : Type*) [LT α] [LE β]
  body: Prod.Lex (· < ·) (· <= ·)

中文:
实例 instLE
  签名: (α β : 类型) [LT α] [LE β]
  定义体: Prod.Lex (· < ·) (· <= ·)

Depends on / 依赖: Prod.Lex
-/
instance instLE (α β : Type*) [LT α] [LE β] : LE (α ×ₗ β) where le := Prod.Lex (· < ·) (· <= ·)

/--
Instance `instLT` / 实例 `instLT`

English:
instance instLT
  signature: (α β : Type*) [LT α] [LT β]
  body: Prod.Lex (· < ·) (· < ·)

中文:
实例 instLT
  签名: (α β : 类型) [LT α] [LT β]
  定义体: Prod.Lex (· < ·) (· < ·)

Depends on / 依赖: Prod.Lex
-/
instance instLT (α β : Type*) [LT α] [LT β] : LT (α ×ₗ β) where lt := Prod.Lex (· < ·) (· < ·)

/--
theorem `toLex_le_toLex` / 定理 `toLex_le_toLex`

English:
theorem toLex_le_toLex
  given: [LT α] [LE β] {x y : α × β}
  proof: Prod.lex_def

@[to_dual existing toLex_le_toLex]

中文:
定理 toLex_le_toLex
  条件: [LT α] [LE β] {x y : α × β}
  证明: Prod.lex_def

@[to_dual existing toLex_le_toLex]

Depends on / 依赖: Prod.lex_def, lex_def
-/
theorem toLex_le_toLex [LT α] [LE β] {x y : α × β} :
    toLex x <= toLex y ↔ x.1 < y.1 ∨ x.1 = y.1 ∧ x.2 <= y.2 :=
  Prod.lex_def

@[to_dual existing toLex_le_toLex]
/--
theorem `toLex_ge_toLex` / 定理 `toLex_ge_toLex`

English:
theorem toLex_ge_toLex
  given: [LT α] [LE β] {x y : α × β}
  proof: by
  rw [eq_comm]; rw [toLex_le_toLex]

中文:
定理 toLex_ge_toLex
  条件: [LT α] [LE β] {x y : α × β}
  证明: by
  rw [eq_comm]; rw [toLex_le_toLex]

Depends on / 依赖: eq_comm, toLex_le_toLex
-/
theorem toLex_ge_toLex [LT α] [LE β] {x y : α × β} :
    toLex y <= toLex x ↔ y.1 < x.1 ∨ x.1 = y.1 ∧ y.2 <= x.2 := by
  rw [eq_comm]; rw [toLex_le_toLex]

/--
theorem `toLex_lt_toLex` / 定理 `toLex_lt_toLex`

English:
theorem toLex_lt_toLex
  given: [LT α] [LT β] {x y : α × β}
  proof: Prod.lex_def

@[to_dual existing toLex_lt_toLex]

中文:
定理 toLex_lt_toLex
  条件: [LT α] [LT β] {x y : α × β}
  证明: Prod.lex_def

@[to_dual existing toLex_lt_toLex]

Depends on / 依赖: Prod.lex_def, lex_def
-/
theorem toLex_lt_toLex [LT α] [LT β] {x y : α × β} :
    toLex x < toLex y ↔ x.1 < y.1 ∨ x.1 = y.1 ∧ x.2 < y.2 :=
  Prod.lex_def

@[to_dual existing toLex_lt_toLex]
/--
theorem `toLex_gt_toLex` / 定理 `toLex_gt_toLex`

English:
theorem toLex_gt_toLex
  given: [LT α] [LT β] {x y : α × β}
  proof: by
  rw [eq_comm]; rw [toLex_lt_toLex]

@[to_dual none]

中文:
定理 toLex_gt_toLex
  条件: [LT α] [LT β] {x y : α × β}
  证明: by
  rw [eq_comm]; rw [toLex_lt_toLex]

@[to_dual none]

Depends on / 依赖: eq_comm, toLex_lt_toLex
-/
theorem toLex_gt_toLex [LT α] [LT β] {x y : α × β} :
    toLex y < toLex x ↔ y.1 < x.1 ∨ x.1 = y.1 ∧ y.2 < x.2 := by
  rw [eq_comm]; rw [toLex_lt_toLex]

@[to_dual none]
/--
lemma `le_iff` / 引理 `le_iff`

English:
lemma le_iff
  given: [LT α] [LE β] {x y : α ×ₗ β}
  proof: toLex_le_toLex

@[to_dual none]

中文:
引理 le_iff
  条件: [LT α] [LE β] {x y : α ×ₗ β}
  证明: toLex_le_toLex

@[to_dual none]

Depends on / 依赖: toLex_le_toLex
-/
lemma le_iff [LT α] [LE β] {x y : α ×ₗ β} :
    x <= y ↔ (ofLex x).1 < (ofLex y).1 ∨ (ofLex x).1 = (ofLex y).1 ∧ (ofLex x).2 <= (ofLex y).2 :=
  toLex_le_toLex

@[to_dual none]
/--
lemma `lt_iff` / 引理 `lt_iff`

English:
lemma lt_iff
  given: [LT α] [LT β] {x y : α ×ₗ β}
  proof: toLex_lt_toLex

中文:
引理 lt_iff
  条件: [LT α] [LT β] {x y : α ×ₗ β}
  证明: toLex_lt_toLex

Depends on / 依赖: toLex_lt_toLex
-/
lemma lt_iff [LT α] [LT β] {x y : α ×ₗ β} :
    x < y ↔ (ofLex x).1 < (ofLex y).1 ∨ (ofLex x).1 = (ofLex y).1 ∧ (ofLex x).2 < (ofLex y).2 :=
  toLex_lt_toLex

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LT
  signature: α] [LT β] [WellFoundedLT α] [WellFoundedLT β] : WellFoundedLT (α ×ₗ β)
  body: instIsWellFounded

中文:
实例 [LT
  签名: α] [LT β] [WellFoundedLT α] [WellFoundedLT β] : WellFoundedLT (α ×ₗ β)
  定义体: instIsWellFounded

Depends on / 依赖: instIsWellFounded
-/
instance [LT α] [LT β] [WellFoundedLT α] [WellFoundedLT β] : WellFoundedLT (α ×ₗ β) :=
  instIsWellFounded

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LT
  signature: α] [LT β] [WellFoundedLT α] [WellFoundedLT β] : WellFoundedRelation (α ×ₗ β)
  body: ⟨(· < ·), wellFounded_lt⟩

中文:
实例 [LT
  签名: α] [LT β] [WellFoundedLT α] [WellFoundedLT β] : WellFoundedRelation (α ×ₗ β)
  定义体: ⟨(· < ·), wellFounded_lt⟩

Depends on / 依赖: wellFounded_lt
-/
instance [LT α] [LT β] [WellFoundedLT α] [WellFoundedLT β] : WellFoundedRelation (α ×ₗ β) :=
  ⟨(· < ·), wellFounded_lt⟩

/--
Instance `instPreorder` / 实例 `instPreorder`

English:
instance instPreorder
  signature: (α β : Type*) [Preorder α] [Preorder β]
  body: refl_of Prod.Lex _ _
le_trans _ _ _ := trans_of Prod.Lex _ _
  lt_iff_le_not_ge x₁ x₂ := by grind [le_iff, lt_iff, lt_iff_le_not_ge]

中文:
实例 instPreorder
  签名: (α β : 类型) [Preorder α] [Preorder β]
  定义体: refl_of Prod.Lex _ _
le_trans _ _ _ := trans_of Prod.Lex _ _
  lt_iff_le_not_ge x₁ x₂ := by grind [le_iff, lt_iff, lt_iff_le_not_ge]

Depends on / 依赖: Prod.Lex, refl_of
-/
instance instPreorder (α β : Type*) [Preorder α] [Preorder β] : Preorder (α ×ₗ β) where
le_refl := refl_of Prod.Lex _ _
le_trans _ _ _ := trans_of Prod.Lex _ _
  lt_iff_le_not_ge x₁ x₂ := by grind [le_iff, lt_iff, lt_iff_le_not_ge]

/--
theorem `monotone_fst` / 定理 `monotone_fst`

English:
theorem monotone_fst
  given: [Preorder α] [LE β] (t c : α ×ₗ β) (h : t <= c)
  proof: by
  cases toLex_le_toLex.mp h with
  | inl h' => exact h'.le
  | inr h' => exact h'.1.le

中文:
定理 monotone_fst
  条件: [Preorder α] [LE β] (t c : α ×ₗ β) (h : t <= c)
  证明: by
  cases toLex_le_toLex.mp h with
  | inl h' => exact h'.le
  | inr h' => exact h'.1.le

Depends on / 依赖: toLex_le_toLex, toLex_le_toLex.mp
-/
theorem monotone_fst [Preorder α] [LE β] (t c : α ×ₗ β) (h : t <= c) :
    (ofLex t).1 <= (ofLex c).1 := by
  cases toLex_le_toLex.mp h with
  | inl h' => exact h'.le
  | inr h' => exact h'.1.le

section Preorder

variable [Preorder α] [Preorder β]

/--
theorem `monotone_fst_ofLex` / 定理 `monotone_fst_ofLex`

English:
theorem monotone_fst_ofLex
  statement: Monotone fun x : α ×ₗ β => (ofLex x).1
  proof: monotone_fst

@[to_dual self]

中文:
定理 monotone_fst_ofLex
  结论: Monotone fun x : α ×ₗ β => (ofLex x).1
  证明: monotone_fst

@[to_dual self]

Depends on / 依赖: monotone_fst
-/
theorem monotone_fst_ofLex : Monotone fun x : α ×ₗ β => (ofLex x).1 := monotone_fst

@[to_dual self]
/--
theorem `_root_.WCovBy.fst_ofLex` / 定理 `_root_.WCovBy.fst_ofLex`

English:
theorem _root_.WCovBy.fst_ofLex
  given: {a b : α ×ₗ β} (h : a ⩿ b)
  statement: (ofLex a).1 ⩿ (ofLex b).1
  proof: ⟨monotone_fst _ _ h.1, fun c hac hcb => h.2 (c := toLex (c, a.2)) (.left _ _ hac) (.left _ _ hcb)⟩

@[to_dual none]

中文:
定理 _root_.WCovBy.fst_ofLex
  条件: {a b : α ×ₗ β} (h : a ⩿ b)
  结论: (ofLex a).1 ⩿ (ofLex b).1
  证明: ⟨monotone_fst _ _ h.1, fun c hac hcb => h.2 (c := toLex (c, a.2)) (.left _ _ hac) (.left _ _ hcb)⟩

@[to_dual none]

Depends on / 依赖: monotone_fst
-/
theorem _root_.WCovBy.fst_ofLex {a b : α ×ₗ β} (h : a ⩿ b) : (ofLex a).1 ⩿ (ofLex b).1 :=
  ⟨monotone_fst _ _ h.1, fun c hac hcb => h.2 (c := toLex (c, a.2)) (.left _ _ hac) (.left _ _ hcb)⟩

@[to_dual none]
/--
theorem `toLex_covBy_toLex_iff` / 定理 `toLex_covBy_toLex_iff`

English:
theorem toLex_covBy_toLex_iff
  given: {a₁ a₂ : α} {b₁ b₂ : β}
  proof: by
  simp only [CovBy, toLex_lt_toLex, toLex.surjective.forall, Prod.forall, isMax_iff_forall_not_lt,
    isMin_iff_forall_not_lt]
  grind

@[to_dual none]

中文:
定理 toLex_covBy_toLex_iff
  条件: {a₁ a₂ : α} {b₁ b₂ : β}
  证明: by
  simp only [CovBy, toLex_lt_toLex, toLex.surjective.forall, Prod.forall, isMax_iff_forall_not_lt,
    isMin_iff_forall_not_lt]
  grind

@[to_dual none]

Depends on / 依赖: Prod.forall, isMax_iff_forall_not_lt, isMin_iff_forall_not_lt, surjective, toLex.surjective.forall, toLex_lt_toLex
-/
theorem toLex_covBy_toLex_iff {a₁ a₂ : α} {b₁ b₂ : β} :
    toLex (a₁, b₁) ⋖ toLex (a₂, b₂) ↔ a₁ = a₂ ∧ b₁ ⋖ b₂ ∨ a₁ ⋖ a₂ ∧ IsMax b₁ ∧ IsMin b₂ := by
  simp only [CovBy, toLex_lt_toLex, toLex.surjective.forall, Prod.forall, isMax_iff_forall_not_lt,
    isMin_iff_forall_not_lt]
  grind

@[to_dual none]
/--
theorem `covBy_iff` / 定理 `covBy_iff`

English:
theorem covBy_iff
  given: {a b : α ×ₗ β}
  proof: toLex_covBy_toLex_iff

中文:
定理 covBy_iff
  条件: {a b : α ×ₗ β}
  证明: toLex_covBy_toLex_iff

Depends on / 依赖: toLex_covBy_toLex_iff
-/
theorem covBy_iff {a b : α ×ₗ β} :
    a ⋖ b ↔ (ofLex a).1 = (ofLex b).1 ∧ (ofLex a).2 ⋖ (ofLex b).2 ∨
      (ofLex a).1 ⋖ (ofLex b).1 ∧ IsMax (ofLex a).2 ∧ IsMin (ofLex b).2 :=
  toLex_covBy_toLex_iff

end Preorder

section PartialOrderPreorder

variable [PartialOrder α] [Preorder β] {x y : α × β}

/-- Variant of `Prod.Lex.toLex_le_toLex` for partial orders. -/
@[to_dual none]
/--
lemma `toLex_le_toLex'` / 引理 `toLex_le_toLex'`

English:
lemma toLex_le_toLex'
  statement: toLex x <= toLex y ↔ x.1 <= y.1 ∧ (x.1 = y.1 -> x.2 <= y.2)
  proof: by
  simp only [toLex_le_toLex, lt_iff_le_not_ge, le_antisymm_iff]
  tauto

中文:
引理 toLex_le_toLex'
  结论: toLex x <= toLex y ↔ x.1 <= y.1 ∧ (x.1 = y.1 -> x.2 <= y.2)
  证明: by
  simp only [toLex_le_toLex, lt_iff_le_not_ge, le_antisymm_iff]
  tauto

Depends on / 依赖: le_antisymm_iff, lt_iff_le_not_ge, toLex_le_toLex
-/
lemma toLex_le_toLex' : toLex x <= toLex y ↔ x.1 <= y.1 ∧ (x.1 = y.1 -> x.2 <= y.2) := by
  simp only [toLex_le_toLex, lt_iff_le_not_ge, le_antisymm_iff]
  tauto

/-- Variant of `Prod.Lex.toLex_lt_toLex` for partial orders. -/
@[to_dual none]
/--
lemma `toLex_lt_toLex'` / 引理 `toLex_lt_toLex'`

English:
lemma toLex_lt_toLex'
  statement: toLex x < toLex y ↔ x.1 <= y.1 ∧ (x.1 = y.1 -> x.2 < y.2)
  proof: by
  rw [toLex_lt_toLex]
  simp only [lt_iff_le_not_ge, le_antisymm_iff]
  tauto

中文:
引理 toLex_lt_toLex'
  结论: toLex x < toLex y ↔ x.1 <= y.1 ∧ (x.1 = y.1 -> x.2 < y.2)
  证明: by
  rw [toLex_lt_toLex]
  simp only [lt_iff_le_not_ge, le_antisymm_iff]
  tauto

Depends on / 依赖: le_antisymm_iff, lt_iff_le_not_ge, toLex_lt_toLex
-/
lemma toLex_lt_toLex' : toLex x < toLex y ↔ x.1 <= y.1 ∧ (x.1 = y.1 -> x.2 < y.2) := by
  rw [toLex_lt_toLex]
  simp only [lt_iff_le_not_ge, le_antisymm_iff]
  tauto

/-- Variant of `Prod.Lex.le_iff` for partial orders. -/
@[to_dual none]
/--
lemma `le_iff'` / 引理 `le_iff'`

English:
lemma le_iff'
  given: {x y : α ×ₗ β}
  proof: toLex_le_toLex'

中文:
引理 le_iff'
  条件: {x y : α ×ₗ β}
  证明: toLex_le_toLex'

Depends on / 依赖: toLex_le_toLex
-/
lemma le_iff' {x y : α ×ₗ β} :
    x <= y ↔ (ofLex x).1 <= (ofLex y).1 ∧ ((ofLex x).1 = (ofLex y).1 -> (ofLex x).2 <= (ofLex y).2) :=
  toLex_le_toLex'

/-- Variant of `Prod.Lex.lt_iff` for partial orders. -/
@[to_dual none]
/--
lemma `lt_iff'` / 引理 `lt_iff'`

English:
lemma lt_iff'
  given: {x y : α ×ₗ β}
  proof: toLex_lt_toLex'

中文:
引理 lt_iff'
  条件: {x y : α ×ₗ β}
  证明: toLex_lt_toLex'

Depends on / 依赖: toLex_lt_toLex
-/
lemma lt_iff' {x y : α ×ₗ β} :
    x < y ↔ (ofLex x).1 <= (ofLex y).1 ∧ ((ofLex x).1 = (ofLex y).1 -> (ofLex x).2 < (ofLex y).2) :=
  toLex_lt_toLex'

/--
theorem `toLex_mono` / 定理 `toLex_mono`

English:
theorem toLex_mono
  statement: Monotone (toLex : α × β -> α ×ₗ β)
  proof: fun _x _y hxy => toLex_le_toLex'.2 ⟨hxy.1, fun _ => hxy.2⟩

中文:
定理 toLex_mono
  结论: Monotone (toLex : α × β -> α ×ₗ β)
  证明: fun _x _y hxy => toLex_le_toLex'.2 ⟨hxy.1, fun _ => hxy.2⟩

Depends on / 依赖: toLex_le_toLex
-/
theorem toLex_mono : Monotone (toLex : α × β -> α ×ₗ β) :=
  fun _x _y hxy => toLex_le_toLex'.2 ⟨hxy.1, fun _ => hxy.2⟩

/--
theorem `toLex_strictMono` / 定理 `toLex_strictMono`

English:
theorem toLex_strictMono
  statement: StrictMono (toLex : α × β -> α ×ₗ β)
  proof: by
  rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
  obtain rfl | ha : a₁ = a₂ ∨ _ := h.le.1.eq_or_lt
  · exact right _ (Prod.mk_lt_mk_iff_right.1 h)
  · exact left _ _ ha

中文:
定理 toLex_strictMono
  结论: StrictMono (toLex : α × β -> α ×ₗ β)
  证明: by
  rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
  obtain rfl | ha : a₁ = a₂ ∨ _ := h.le.1.eq_or_lt
  · exact right _ (Prod.mk_lt_mk_iff_right.1 h)
  · exact left _ _ ha

Depends on / 依赖: Prod.mk_lt_mk_iff_right, eq_or_lt, h.le, mk_lt_mk_iff_right
-/
theorem toLex_strictMono : StrictMono (toLex : α × β -> α ×ₗ β) := by
  rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
  obtain rfl | ha : a₁ = a₂ ∨ _ := h.le.1.eq_or_lt
  · exact right _ (Prod.mk_lt_mk_iff_right.1 h)
  · exact left _ _ ha

end PartialOrderPreorder

/--
Instance `instPartialOrder` / 实例 `instPartialOrder`

English:
instance instPartialOrder
  signature: (α β : Type*) [PartialOrder α] [PartialOrder β]
  body: antisymm_of (Prod.Lex _ _)

中文:
实例 instPartialOrder
  签名: (α β : 类型) [PartialOrder α] [PartialOrder β]
  定义体: antisymm_of (Prod.Lex _ _)

Depends on / 依赖: Prod.Lex, antisymm_of
-/
instance instPartialOrder (α β : Type*) [PartialOrder α] [PartialOrder β] :
    PartialOrder (α ×ₗ β) where
  le_antisymm _ _ := antisymm_of (Prod.Lex _ _)

/--
Instance `instOrdLexProd` / 实例 `instOrdLexProd`

English:
instance instOrdLexProd
  signature: [Ord α] [Ord β]
  body: fast_instance% lexOrd

中文:
实例 instOrdLexProd
  签名: [Ord α] [Ord β]
  定义体: fast_instance% lexOrd

Depends on / 依赖: fast_instance, lexOrd
-/
instance instOrdLexProd [Ord α] [Ord β] : Ord (α ×ₗ β) := fast_instance% lexOrd

/--
theorem `compare_def` / 定理 `compare_def`

English:
theorem compare_def
  given: [Ord α] [Ord β]
  statement: @compare (α ×ₗ β) _ =
  proof: rfl

中文:
定理 compare_def
  条件: [Ord α] [Ord β]
  结论: @compare (α ×ₗ β) _ =
  证明: rfl
-/
theorem compare_def [Ord α] [Ord β] : @compare (α ×ₗ β) _ =
    compareLex (compareOn fun x => (ofLex x).1) (compareOn fun x => (ofLex x).2) := rfl

/--
theorem `_root_.lexOrd_eq` / 定理 `_root_.lexOrd_eq`

English:
theorem _root_.lexOrd_eq
  given: [Ord α] [Ord β]
  statement: @lexOrd α β _ _ = instOrdLexProd
  proof: rfl

中文:
定理 _root_.lexOrd_eq
  条件: [Ord α] [Ord β]
  结论: @lexOrd α β _ _ = instOrdLexProd
  证明: rfl
-/
theorem _root_.lexOrd_eq [Ord α] [Ord β] : @lexOrd α β _ _ = instOrdLexProd := rfl

/--
theorem `_root_.Ord.lex_eq` / 定理 `_root_.Ord.lex_eq`

English:
theorem _root_.Ord.lex_eq
  given: [oα : Ord α] [oβ : Ord β]
  statement: Ord.lex oα oβ = instOrdLexProd
  proof: rfl

中文:
定理 _root_.Ord.lex_eq
  条件: [oα : Ord α] [oβ : Ord β]
  结论: Ord.lex oα oβ = instOrdLexProd
  证明: rfl
-/
theorem _root_.Ord.lex_eq [oα : Ord α] [oβ : Ord β] : Ord.lex oα oβ = instOrdLexProd := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Ord
  signature: α] [Ord β] [Std.OrientedOrd α] [Std.OrientedOrd β] : Std.OrientedOrd (α ×ₗ β)
  body: inferInstanceAs (@Std.OrientedCmp (α × β) (compareLex _ _))

中文:
实例 [Ord
  签名: α] [Ord β] [Std.OrientedOrd α] [Std.OrientedOrd β] : Std.OrientedOrd (α ×ₗ β)
  定义体: inferInstanceAs (@Std.OrientedCmp (α × β) (compareLex _ _))

Depends on / 依赖: OrientedCmp, Std.OrientedCmp, compareLex
-/
instance [Ord α] [Ord β] [Std.OrientedOrd α] [Std.OrientedOrd β] : Std.OrientedOrd (α ×ₗ β) :=
  inferInstanceAs (@Std.OrientedCmp (α × β) (compareLex _ _))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Ord
  signature: α] [Ord β] [Std.TransOrd α] [Std.TransOrd β] : Std.TransOrd (α ×ₗ β)
  body: inferInstanceAs (@Std.TransCmp (α × β) (compareLex _ _))

中文:
实例 [Ord
  签名: α] [Ord β] [Std.TransOrd α] [Std.TransOrd β] : Std.TransOrd (α ×ₗ β)
  定义体: inferInstanceAs (@Std.TransCmp (α × β) (compareLex _ _))

Depends on / 依赖: Std.TransCmp, TransCmp, compareLex
-/
instance [Ord α] [Ord β] [Std.TransOrd α] [Std.TransOrd β] : Std.TransOrd (α ×ₗ β) :=
  inferInstanceAs (@Std.TransCmp (α × β) (compareLex _ _))

/--
Instance `instLinearOrder` / 实例 `instLinearOrder`

English:
instance instLinearOrder
  signature: (α β : Type*) [LinearOrder α] [LinearOrder β]
  body: total_of (Prod.Lex _ _)
  toDecidableLE := Prod.Lex.decidable _ _
  toDecidableLT := Prod.Lex.decidable _ _
  toDecidableEq := instDecidableEqLex _
  compare_eq_compareOfLessAndEq := fun a b => by
    have : DecidableLT (α ×ₗ β) := Prod.Lex.decidable _ _
    have : Std.LawfulBEqOrd (α ×ₗ β) := ⟨by
 

中文:
实例 instLinearOrder
  签名: (α β : 类型) [LinearOrder α] [LinearOrder β]
  定义体: total_of (Prod.Lex _ _)
  toDecidableLE := Prod.Lex.decidable _ _
  toDecidableLT := Prod.Lex.decidable _ _
  toDecidableEq := instDecidableEqLex _
  compare_eq_compareOfLessAndEq := fun a b => by
    have : DecidableLT (α ×ₗ β) := Prod.Lex.decidable _ _
    have : Std.LawfulBEqOrd (α ×ₗ β) := ⟨by
 

Depends on / 依赖: Prod.Lex, total_of
-/
instance instLinearOrder (α β : Type*) [LinearOrder α] [LinearOrder β] : LinearOrder (α ×ₗ β) where
  le_total := total_of (Prod.Lex _ _)
  toDecidableLE := Prod.Lex.decidable _ _
  toDecidableLT := Prod.Lex.decidable _ _
  toDecidableEq := instDecidableEqLex _
  compare_eq_compareOfLessAndEq := fun a b => by
    have : DecidableLT (α ×ₗ β) := Prod.Lex.decidable _ _
    have : Std.LawfulBEqOrd (α ×ₗ β) := ⟨by
      simp [compare_def, compareLex, compareOn, Ordering.then_eq_eq]⟩
    have : Std.LawfulLTOrd (α ×ₗ β) := ⟨by
      simp [compare_def, compareLex, compareOn, Ordering.then_eq_lt, toLex_lt_toLex,
        compare_lt_iff_lt]⟩
    convert! Std.LawfulLTCmp.eq_compareOfLessAndEq (cmp := compare) a b

@[to_dual]
/--
Instance `orderBot` / 实例 `orderBot`

English:
instance orderBot
  signature: [PartialOrder α] [Preorder β] [OrderBot α] [OrderBot β]
  body: toLex ⊥
  bot_le _ := toLex_mono bot_le

中文:
实例 orderBot
  签名: [PartialOrder α] [Preorder β] [OrderBot α] [OrderBot β]
  定义体: toLex ⊥
  bot_le _ := toLex_mono bot_le
-/
instance orderBot [PartialOrder α] [Preorder β] [OrderBot α] [OrderBot β] : OrderBot (α ×ₗ β) where
  bot := toLex ⊥
  bot_le _ := toLex_mono bot_le

/--
Instance `boundedOrder` / 实例 `boundedOrder`

English:
instance boundedOrder
  signature: [PartialOrder α] [Preorder β] [BoundedOrder α] [BoundedOrder β]

中文:
实例 boundedOrder
  签名: [PartialOrder α] [Preorder β] [BoundedOrder α] [BoundedOrder β]
-/
instance boundedOrder [PartialOrder α] [Preorder β] [BoundedOrder α] [BoundedOrder β] :
    BoundedOrder (α ×ₗ β) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preorder
  signature: α] [Preorder β] [DenselyOrdered α] [DenselyOrdered β] :
  body: by
    rintro _ _ (@⟨a₁, b₁, a₂, b₂, h⟩ | @⟨a, b₁, b₂, h⟩)
    · obtain ⟨c, h₁, h₂⟩ := exists_between h
      exact ⟨(c, b₁), left _ _ h₁, left _ _ h₂⟩
    · obtain ⟨c, h₁, h₂⟩ := exists_between h
      exact ⟨(a, c), right _ h₁, right _ h₂⟩

中文:
实例 [Preorder
  签名: α] [Preorder β] [DenselyOrdered α] [DenselyOrdered β] :
  定义体: by
    rintro _ _ (@⟨a₁, b₁, a₂, b₂, h⟩ | @⟨a, b₁, b₂, h⟩)
    · obtain ⟨c, h₁, h₂⟩ := exists_between h
      exact ⟨(c, b₁), left _ _ h₁, left _ _ h₂⟩
    · obtain ⟨c, h₁, h₂⟩ := exists_between h
      exact ⟨(a, c), right _ h₁, right _ h₂⟩

Depends on / 依赖: exists_between
-/
instance [Preorder α] [Preorder β] [DenselyOrdered α] [DenselyOrdered β] :
    DenselyOrdered (α ×ₗ β) where
  dense := by
    rintro _ _ (@⟨a₁, b₁, a₂, b₂, h⟩ | @⟨a, b₁, b₂, h⟩)
    · obtain ⟨c, h₁, h₂⟩ := exists_between h
      exact ⟨(c, b₁), left _ _ h₁, left _ _ h₂⟩
    · obtain ⟨c, h₁, h₂⟩ := exists_between h
      exact ⟨(a, c), right _ h₁, right _ h₂⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preorder
  signature: α] [Preorder β] [NoMinOrder β] [DenselyOrdered β] :
  body: by
    cases x with | h x
    cases y with | h y
    simp only [Prod.Lex.toLex_lt_toLex] at h
    rcases h with (h | h)
    · obtain ⟨v, hv⟩ := exists_lt y.2
      use toLex (y.1, v)
      simp [Prod.Lex.toLex_lt_toLex, h, hv]
    · obtain ⟨v, htv, hvu⟩ := DenselyOrdered.dense x.2 y.2 h.2
      use 

中文:
实例 [Preorder
  签名: α] [Preorder β] [NoMinOrder β] [DenselyOrdered β] :
  定义体: by
    cases x with | h x
    cases y with | h y
    simp only [Prod.Lex.toLex_lt_toLex] at h
    rcases h with (h | h)
    · obtain ⟨v, hv⟩ := exists_lt y.2
      use toLex (y.1, v)
      simp [Prod.Lex.toLex_lt_toLex, h, hv]
    · obtain ⟨v, htv, hvu⟩ := DenselyOrdered.dense x.2 y.2 h.2
      use 

Depends on / 依赖: DenselyOrdered, DenselyOrdered.dense, Prod.Lex.toLex_lt_toLex, exists_lt, toLex_lt_toLex
-/
instance [Preorder α] [Preorder β] [NoMinOrder β] [DenselyOrdered β] :
    DenselyOrdered (α ×ₗ β) where
  dense x y h := by
    cases x with | h x
    cases y with | h y
    simp only [Prod.Lex.toLex_lt_toLex] at h
    rcases h with (h | h)
    · obtain ⟨v, hv⟩ := exists_lt y.2
      use toLex (y.1, v)
      simp [Prod.Lex.toLex_lt_toLex, h, hv]
    · obtain ⟨v, htv, hvu⟩ := DenselyOrdered.dense x.2 y.2 h.2
      use toLex (x.1, v)
      simp [Prod.Lex.toLex_lt_toLex, h.1, htv, hvu]

@[to_dual existing]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preorder
  signature: α] [Preorder β] [NoMaxOrder β] [DenselyOrdered β] :
  body: by
    cases x with | h x
    cases y with | h y
    simp only [Prod.Lex.toLex_lt_toLex] at h
    rcases h with (h | h)
    · obtain ⟨v, hv⟩ := exists_gt x.2
      use toLex (x.1, v)
      simp [Prod.Lex.toLex_lt_toLex, h, hv]
    · obtain ⟨v, htv, hvu⟩ := DenselyOrdered.dense x.2 y.2 h.2
      use 

中文:
实例 [Preorder
  签名: α] [Preorder β] [NoMaxOrder β] [DenselyOrdered β] :
  定义体: by
    cases x with | h x
    cases y with | h y
    simp only [Prod.Lex.toLex_lt_toLex] at h
    rcases h with (h | h)
    · obtain ⟨v, hv⟩ := exists_gt x.2
      use toLex (x.1, v)
      simp [Prod.Lex.toLex_lt_toLex, h, hv]
    · obtain ⟨v, htv, hvu⟩ := DenselyOrdered.dense x.2 y.2 h.2
      use 

Depends on / 依赖: DenselyOrdered, DenselyOrdered.dense, Prod.Lex.toLex_lt_toLex, exists_gt, toLex_lt_toLex
-/
instance [Preorder α] [Preorder β] [NoMaxOrder β] [DenselyOrdered β] :
    DenselyOrdered (α ×ₗ β) where
  dense x y h := by
    cases x with | h x
    cases y with | h y
    simp only [Prod.Lex.toLex_lt_toLex] at h
    rcases h with (h | h)
    · obtain ⟨v, hv⟩ := exists_gt x.2
      use toLex (x.1, v)
      simp [Prod.Lex.toLex_lt_toLex, h, hv]
    · obtain ⟨v, htv, hvu⟩ := DenselyOrdered.dense x.2 y.2 h.2
      use toLex (x.1, v)
      simp [Prod.Lex.toLex_lt_toLex, h.1, htv, hvu]

@[to_dual]
/--
Instance `noMaxOrder_of_left` / 实例 `noMaxOrder_of_left`

English:
instance noMaxOrder_of_left
  signature: [Preorder α] [Preorder β] [NoMaxOrder α]
  body: by
    rw [Lex.forall]; rw [Prod.forall]
    intro a b
    obtain ⟨c, h⟩ := exists_gt a
    use toLex (c, b)
    simpa [lt_iff]

@[to_dual]

中文:
实例 noMaxOrder_of_left
  签名: [Preorder α] [Preorder β] [NoMaxOrder α]
  定义体: by
    rw [Lex.forall]; rw [Prod.forall]
    intro a b
    obtain ⟨c, h⟩ := exists_gt a
    use toLex (c, b)
    simpa [lt_iff]

@[to_dual]

Depends on / 依赖: Lex.forall, Prod.forall, exists_gt, lt_iff
-/
instance noMaxOrder_of_left [Preorder α] [Preorder β] [NoMaxOrder α] : NoMaxOrder (α ×ₗ β) where
  exists_gt := by
    rw [Lex.forall]; rw [Prod.forall]
    intro a b
    obtain ⟨c, h⟩ := exists_gt a
    use toLex (c, b)
    simpa [lt_iff]

@[to_dual]
/--
Instance `noMaxOrder_of_right` / 实例 `noMaxOrder_of_right`

English:
instance noMaxOrder_of_right
  signature: [Preorder α] [Preorder β] [NoMaxOrder β]
  body: by
    rw [Lex.forall]; rw [Prod.forall]
    intro a b
    obtain ⟨c, h⟩ := exists_gt b
    use toLex (a, c)
    simpa [lt_iff]

中文:
实例 noMaxOrder_of_right
  签名: [Preorder α] [Preorder β] [NoMaxOrder β]
  定义体: by
    rw [Lex.forall]; rw [Prod.forall]
    intro a b
    obtain ⟨c, h⟩ := exists_gt b
    use toLex (a, c)
    simpa [lt_iff]

Depends on / 依赖: Lex.forall, Prod.forall, exists_gt, lt_iff
-/
instance noMaxOrder_of_right [Preorder α] [Preorder β] [NoMaxOrder β] : NoMaxOrder (α ×ₗ β) where
  exists_gt := by
    rw [Lex.forall]; rw [Prod.forall]
    intro a b
    obtain ⟨c, h⟩ := exists_gt b
    use toLex (a, c)
    simpa [lt_iff]

end Prod.Lex
