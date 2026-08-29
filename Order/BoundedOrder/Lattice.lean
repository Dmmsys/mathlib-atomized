/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Lattice

/-!
# Bounded lattices

This file contains miscellaneous lemmas about lattices with top or bottom elements.

## Common lattices

* Distributive lattices with a bottom element. Notated by `[DistribLattice α] [OrderBot α]`.
  It captures the properties of `Disjoint` that are common to `GeneralizedBooleanAlgebra` and
  `DistribLattice` when `OrderBot`.
* Bounded and distributive lattice. Notated by `[DistribLattice α] [BoundedOrder α]`.
  Typical examples include `Prop` and `Set α`.
-/

public section

open Function OrderDual

variable {α β : Type*}

/-! ### Top, bottom element -/

section SemilatticeSupTop

variable [SemilatticeSup α] [OrderTop α]

/--
theorem `top_sup_eq` / 定理 `top_sup_eq`

English:
theorem top_sup_eq
  given: (a : α)
  statement: ⊤ ⊔ a = ⊤
  proof: sup_of_le_left le_top

中文:
定理 top_sup_eq
  条件: (a : α)
  结论: ⊤ ⊔ a = ⊤
  证明: sup_of_le_left le_top
-/
@[to_dual] theorem top_sup_eq (a : α) : ⊤ ⊔ a = ⊤ := sup_of_le_left le_top
/--
theorem `sup_top_eq` / 定理 `sup_top_eq`

English:
theorem sup_top_eq
  given: (a : α)
  statement: a ⊔ ⊤ = ⊤
  proof: sup_of_le_right le_top

中文:
定理 sup_top_eq
  条件: (a : α)
  结论: a ⊔ ⊤ = ⊤
  证明: sup_of_le_right le_top
-/
@[to_dual] theorem sup_top_eq (a : α) : a ⊔ ⊤ = ⊤ := sup_of_le_right le_top

end SemilatticeSupTop

section SemilatticeSupBot

variable [SemilatticeSup α] [OrderBot α] {a b : α}

/--
theorem `bot_sup_eq` / 定理 `bot_sup_eq`

English:
theorem bot_sup_eq
  given: (a : α)
  statement: ⊥ ⊔ a = a
  proof: sup_of_le_right bot_le

中文:
定理 bot_sup_eq
  条件: (a : α)
  结论: ⊥ ⊔ a = a
  证明: sup_of_le_right bot_le
-/
@[to_dual] theorem bot_sup_eq (a : α) : ⊥ ⊔ a = a := sup_of_le_right bot_le
/--
theorem `sup_bot_eq` / 定理 `sup_bot_eq`

English:
theorem sup_bot_eq
  given: (a : α)
  statement: a ⊔ ⊥ = a
  proof: sup_of_le_left bot_le

@[to_dual (attr := simp, grind =)]

中文:
定理 sup_bot_eq
  条件: (a : α)
  结论: a ⊔ ⊥ = a
  证明: sup_of_le_left bot_le

@[to_dual (attr := simp, grind =)]
-/
@[to_dual] theorem sup_bot_eq (a : α) : a ⊔ ⊥ = a := sup_of_le_left bot_le

@[to_dual (attr := simp, grind =)]
/--
theorem `sup_eq_bot_iff` / 定理 `sup_eq_bot_iff`

English:
theorem sup_eq_bot_iff
  statement: a ⊔ b = ⊥ ↔ a = ⊥ ∧ b = ⊥
  proof: by rw [eq_bot_iff, sup_le_iff]; simp

中文:
定理 sup_eq_bot_iff
  结论: a ⊔ b = ⊥ ↔ a = ⊥ ∧ b = ⊥
  证明: by rw [eq_bot_iff, sup_le_iff]; simp

Depends on / 依赖: eq_bot_iff, sup_le_iff
-/
theorem sup_eq_bot_iff : a ⊔ b = ⊥ ↔ a = ⊥ ∧ b = ⊥ := by rw [eq_bot_iff, sup_le_iff]; simp

end SemilatticeSupBot

section LinearOrder

variable [LinearOrder α] [OrderBot α]

-- `simp` can prove these, so they shouldn't be simp-lemmas.

/--
theorem `min_bot_left` / 定理 `min_bot_left`

English:
theorem min_bot_left
  given: (a : α)
  statement: min ⊥ a = ⊥
  proof: bot_inf_eq _

中文:
定理 min_bot_left
  条件: (a : α)
  结论: min ⊥ a = ⊥
  证明: bot_inf_eq _
-/
@[to_dual] theorem min_bot_left (a : α) : min ⊥ a = ⊥ := bot_inf_eq _
/--
theorem `min_bot_right` / 定理 `min_bot_right`

English:
theorem min_bot_right
  given: (a : α)
  statement: min a ⊥ = ⊥
  proof: inf_bot_eq _

中文:
定理 min_bot_right
  条件: (a : α)
  结论: min a ⊥ = ⊥
  证明: inf_bot_eq _
-/
@[to_dual] theorem min_bot_right (a : α) : min a ⊥ = ⊥ := inf_bot_eq _

/--
theorem `max_bot_left` / 定理 `max_bot_left`

English:
theorem max_bot_left
  given: (a : α)
  statement: max ⊥ a = a
  proof: bot_sup_eq _

中文:
定理 max_bot_left
  条件: (a : α)
  结论: max ⊥ a = a
  证明: bot_sup_eq _
-/
@[to_dual] theorem max_bot_left (a : α) : max ⊥ a = a := bot_sup_eq _
/--
theorem `max_bot_right` / 定理 `max_bot_right`

English:
theorem max_bot_right
  given: (a : α)
  statement: max a ⊥ = a
  proof: sup_bot_eq _

中文:
定理 max_bot_right
  条件: (a : α)
  结论: max a ⊥ = a
  证明: sup_bot_eq _
-/
@[to_dual] theorem max_bot_right (a : α) : max a ⊥ = a := sup_bot_eq _

/--
theorem `max_eq_bot` / 定理 `max_eq_bot`

English:
theorem max_eq_bot
  given: {a b : α}
  statement: max a b = ⊥ ↔ a = ⊥ ∧ b = ⊥
  proof: sup_eq_bot_iff

@[to_dual (attr := simp)]

中文:
定理 max_eq_bot
  条件: {a b : α}
  结论: max a b = ⊥ ↔ a = ⊥ ∧ b = ⊥
  证明: sup_eq_bot_iff

@[to_dual (attr := simp)]
-/
@[to_dual] theorem max_eq_bot {a b : α} : max a b = ⊥ ↔ a = ⊥ ∧ b = ⊥ := sup_eq_bot_iff

@[to_dual (attr := simp)]
/--
theorem `min_eq_bot` / 定理 `min_eq_bot`

English:
theorem min_eq_bot
  given: {a b : α}
  statement: min a b = ⊥ ↔ a = ⊥ ∨ b = ⊥
  proof: by
  simp_rw [← le_bot_iff, inf_le_iff]

@[to_dual (attr := aesop (rule_sets := [finiteness]) safe apply)]

中文:
定理 min_eq_bot
  条件: {a b : α}
  结论: min a b = ⊥ ↔ a = ⊥ ∨ b = ⊥
  证明: by
  simp_rw [← le_bot_iff, inf_le_iff]

@[to_dual (attr := aesop (rule_sets := [finiteness]) safe apply)]

Depends on / 依赖: inf_le_iff, le_bot_iff, simp_rw
-/
theorem min_eq_bot {a b : α} : min a b = ⊥ ↔ a = ⊥ ∨ b = ⊥ := by
  simp_rw [← le_bot_iff, inf_le_iff]

@[to_dual (attr := aesop (rule_sets := [finiteness]) safe apply)]
/--
lemma `min_ne_bot` / 引理 `min_ne_bot`

English:
lemma min_ne_bot
  given: {a b : α} (ha : a != ⊥) (hb : b != ⊥)
  statement: min a b != ⊥
  proof: by
  grind

中文:
引理 min_ne_bot
  条件: {a b : α} (ha : a != ⊥) (hb : b != ⊥)
  结论: min a b != ⊥
  证明: by
  grind
-/
lemma min_ne_bot {a b : α} (ha : a != ⊥) (hb : b != ⊥) : min a b != ⊥ := by
  grind

end LinearOrder

/-! ### Induction on `WellFoundedGT` and `WellFoundedLT` -/

section WellFounded

@[to_dual (attr := elab_as_elim)]
/--
theorem `WellFoundedGT.induction_top` / 定理 `WellFoundedGT.induction_top`

English:
theorem WellFoundedGT.induction_top
  statement: [Preorder α] [WellFoundedGT α] [OrderTop α]
  proof: by
  contrapose! hexists
  intro M
  induction M using WellFoundedGT.induction with
  | ind x IH =>
    by_cases hx : x = ⊤
    · exact hx ▸ hexists
    · intro hx'
      obtain ⟨M, hM, hM'⟩ := hind x hx hx'
      exact IH _ hM hM'

中文:
定理 WellFoundedGT.induction_top
  结论: [Preorder α] [WellFoundedGT α] [OrderTop α]
  证明: by
  contrapose! hexists
  intro M
  induction M using WellFoundedGT.induction with
  | ind x IH =>
    by_cases hx : x = ⊤
    · exact hx ▸ hexists
    · intro hx'
      obtain ⟨M, hM, hM'⟩ := hind x hx hx'
      exact IH _ hM hM'

Depends on / 依赖: WellFoundedGT, WellFoundedGT.induction, contrapose, hexists
-/
theorem WellFoundedGT.induction_top [Preorder α] [WellFoundedGT α] [OrderTop α]
    {P : α -> Prop} (hexists : exists M, P M) (hind : forall N != ⊤, P N -> exists M > N, P M) : P ⊤ := by
  contrapose! hexists
  intro M
  induction M using WellFoundedGT.induction with
  | ind x IH =>
    by_cases hx : x = ⊤
    · exact hx ▸ hexists
    · intro hx'
      obtain ⟨M, hM, hM'⟩ := hind x hx hx'
      exact IH _ hM hM'

end WellFounded
