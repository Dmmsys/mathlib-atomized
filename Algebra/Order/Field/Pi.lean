/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Basic

/-!
# Lemmas about (finite domain) functions into fields.

We split this from `Algebra.Order.Field.Basic` to avoid importing the finiteness hierarchy there.
-/

public section

variable {α ι : Type*} [AddCommMonoid α] [LinearOrder α] [IsOrderedCancelAddMonoid α]
  [Nontrivial α] [DenselyOrdered α]

/--
theorem `Pi.exists_forall_pos_add_lt` / 定理 `Pi.exists_forall_pos_add_lt`

English:
theorem Pi.exists_forall_pos_add_lt
  statement: [ExistsAddOfLE α] [Finite ι] {x y : ι -> α}
  proof: by
  cases nonempty_fintype ι
  cases isEmpty_or_nonempty ι
  · obtain ⟨a, ha⟩ := exists_ne (0 : α)
    obtain ha | ha := ha.lt_or_gt <;> obtain ⟨b, hb, -⟩ := exists_pos_add_of_lt' ha <;>
      exact ⟨b, hb, isEmptyElim⟩
  choose ε hε hxε using fun i => exists_pos_add_of_lt' (h i)
  obtain rfl : x + ε = y := funext hxε
  have hε : 0 < Finset.univ.inf' Finset.univ_nonempty ε := (Finset.lt_inf'_iff _).2 fun i _ => hε _
  obtain ⟨δ, hδ, hδε⟩ := exists_between hε
  exact ⟨δ, hδ, fun i => add_lt_add_right (hδε.trans_le <| Finset.inf'_le _ <| Finset.mem_univ _) _⟩

中文:
定理 依赖函数类型.存在_对任意_pos_add_lt
  结论: [ExistsAddOfLE α] [有限 ι] {x y : ι -> α}
  证明: by
  cases nonempty_fintype ι
  cases isEmpty_or_nonempty ι
  · obtain ⟨a, ha⟩ := exists_ne (0 : α)
    obtain ha | ha := ha.lt_or_gt <;> obtain ⟨b, hb, -⟩ := exists_pos_add_of_lt' ha <;>
      exact ⟨b, hb, isEmptyElim⟩
  choose ε hε hxε using fun i => exists_pos_add_of_lt' (h i)
  obtain rfl : x + ε = y := funext hxε
  have hε : 0 < Finset.univ.inf' Finset.univ_nonempty ε := (Finset.lt_inf'_iff _).2 fun i _ => hε _
  obtain ⟨δ, hδ, hδε⟩ := exists_between hε
  exact ⟨δ, hδ, fun i => add_lt_add_right (hδε.trans_le <| Finset.inf'_le _ <| Finset.mem_univ _) _⟩

Depends on / 依赖: Finset, Finset.lt_inf, Finset.univ.inf, Finset.univ_nonempty, _iff, add_lt_add_right, exists_between, exists_ne, exists_pos_add_of_lt, ha.lt_or_gt, isEmptyElim, isEmpty_or_nonempty, lt_inf, lt_or_gt, nonempty_fintype, trans_le, univ_nonempty
-/
theorem Pi.exists_forall_pos_add_lt [ExistsAddOfLE α] [Finite ι] {x y : ι -> α}
    (h : forall i, x i < y i) : exists ε, 0 < ε ∧ forall i, x i + ε < y i := by
  cases nonempty_fintype ι
  cases isEmpty_or_nonempty ι
  · obtain ⟨a, ha⟩ := exists_ne (0 : α)
    obtain ha | ha := ha.lt_or_gt <;> obtain ⟨b, hb, -⟩ := exists_pos_add_of_lt' ha <;>
      exact ⟨b, hb, isEmptyElim⟩
  choose ε hε hxε using fun i => exists_pos_add_of_lt' (h i)
  obtain rfl : x + ε = y := funext hxε
  have hε : 0 < Finset.univ.inf' Finset.univ_nonempty ε := (Finset.lt_inf'_iff _).2 fun i _ => hε _
  obtain ⟨δ, hδ, hδε⟩ := exists_between hε
  exact ⟨δ, hδ, fun i => add_lt_add_right (hδε.trans_le <| Finset.inf'_le _ <| Finset.mem_univ _) _⟩
