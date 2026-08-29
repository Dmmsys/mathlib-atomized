/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis
-/
module

public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Pow

/-!
# Lemmas about the interaction of power operations with order
-/

public section

-- We should need only a minimal development of sets in order to get here.
assert_not_exists Set.Subsingleton

open Function Int

variable {α : Type*}

section OrderedCommGroup
variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] {m n : Int} {a b : α}

@[to_additive zsmul_left_strictMono]
/--
lemma `zpow_right_strictMono` / 引理 `zpow_right_strictMono`

English:
lemma zpow_right_strictMono
  given: (ha : 1 < a)
  statement: StrictMono fun n : Int => a ^ n
  proof: by
  refine strictMono_int_of_lt_succ fun n => ?_
  rw [zpow_add_one]
  exact lt_mul_of_one_lt_right' (a ^ n) ha

@[to_additive zsmul_left_strictAnti]

中文:
引理 zpow_right_strictMono
  条件: (ha : 1 < a)
  结论: 严格递增 fun n : 整数 => a ^ n
  证明: by
  refine strictMono_int_of_lt_succ fun n => ?_
  rw [zpow_add_one]
  exact lt_mul_of_one_lt_right' (a ^ n) ha

@[to_additive zsmul_left_strictAnti]

Depends on / 依赖: lt_mul_of_one_lt_right, strictMono_int_of_lt_succ, zpow_add_one
-/
lemma zpow_right_strictMono (ha : 1 < a) : StrictMono fun n : Int => a ^ n := by
  refine strictMono_int_of_lt_succ fun n => ?_
  rw [zpow_add_one]
  exact lt_mul_of_one_lt_right' (a ^ n) ha

@[to_additive zsmul_left_strictAnti]
/--
lemma `zpow_right_strictAnti` / 引理 `zpow_right_strictAnti`

English:
lemma zpow_right_strictAnti
  given: (ha : a < 1)
  statement: StrictAnti fun n : Int => a ^ n
  proof: by
  refine strictAnti_int_of_succ_lt fun n => ?_
  rw [zpow_add_one]
  exact mul_lt_of_lt_one_right' (a ^ n) ha

@[to_additive zsmul_left_inj]

中文:
引理 zpow_right_strictAnti
  条件: (ha : a < 1)
  结论: 严格递减 fun n : 整数 => a ^ n
  证明: by
  refine strictAnti_int_of_succ_lt fun n => ?_
  rw [zpow_add_one]
  exact mul_lt_of_lt_one_right' (a ^ n) ha

@[to_additive zsmul_left_inj]

Depends on / 依赖: mul_lt_of_lt_one_right, strictAnti_int_of_succ_lt, zpow_add_one
-/
lemma zpow_right_strictAnti (ha : a < 1) : StrictAnti fun n : Int => a ^ n := by
  refine strictAnti_int_of_succ_lt fun n => ?_
  rw [zpow_add_one]
  exact mul_lt_of_lt_one_right' (a ^ n) ha

@[to_additive zsmul_left_inj]
/--
lemma `zpow_right_inj` / 引理 `zpow_right_inj`

English:
lemma zpow_right_inj
  given: (ha : 1 < a) {m n : Int}
  statement: a ^ m = a ^ n ↔ m = n
  proof: (zpow_right_strictMono ha).injective.eq_iff

@[to_additive zsmul_left_mono]

中文:
引理 zpow_right_inj
  条件: (ha : 1 < a) {m n : 整数}
  结论: a ^ m = a ^ n ↔ m = n
  证明: (zpow_right_strictMono ha).injective.eq_iff

@[to_additive zsmul_left_mono]

Depends on / 依赖: eq_iff, injective, injective.eq_iff, zpow_right_strictMono
-/
lemma zpow_right_inj (ha : 1 < a) {m n : Int} : a ^ m = a ^ n ↔ m = n :=
  (zpow_right_strictMono ha).injective.eq_iff

@[to_additive zsmul_left_mono]
/--
lemma `zpow_right_mono` / 引理 `zpow_right_mono`

English:
lemma zpow_right_mono
  given: (ha : 1 <= a)
  statement: Monotone fun n : Int => a ^ n
  proof: by
  refine monotone_int_of_le_succ fun n => ?_
  rw [zpow_add_one]
  exact le_mul_of_one_le_right' ha

@[to_additive (attr := gcongr) zsmul_le_zsmul_left]

中文:
引理 zpow_right_mono
  条件: (ha : 1 <= a)
  结论: 递增 fun n : 整数 => a ^ n
  证明: by
  refine monotone_int_of_le_succ fun n => ?_
  rw [zpow_add_one]
  exact le_mul_of_one_le_right' ha

@[to_additive (attr := gcongr) zsmul_le_zsmul_left]

Depends on / 依赖: le_mul_of_one_le_right, monotone_int_of_le_succ, zpow_add_one
-/
lemma zpow_right_mono (ha : 1 <= a) : Monotone fun n : Int => a ^ n := by
  refine monotone_int_of_le_succ fun n => ?_
  rw [zpow_add_one]
  exact le_mul_of_one_le_right' ha

@[to_additive (attr := gcongr) zsmul_le_zsmul_left]
/--
lemma `zpow_le_zpow_right` / 引理 `zpow_le_zpow_right`

English:
lemma zpow_le_zpow_right
  given: (ha : 1 <= a) (h : m <= n)
  statement: a ^ m <= a ^ n
  proof: zpow_right_mono ha h

@[to_additive (attr := gcongr) zsmul_lt_zsmul_left]

中文:
引理 zpow_le_zpow_right
  条件: (ha : 1 <= a) (h : m <= n)
  结论: a ^ m <= a ^ n
  证明: zpow_right_mono ha h

@[to_additive (attr := gcongr) zsmul_lt_zsmul_left]

Depends on / 依赖: zpow_right_mono
-/
lemma zpow_le_zpow_right (ha : 1 <= a) (h : m <= n) : a ^ m <= a ^ n := zpow_right_mono ha h

@[to_additive (attr := gcongr) zsmul_lt_zsmul_left]
/--
lemma `zpow_lt_zpow_right` / 引理 `zpow_lt_zpow_right`

English:
lemma zpow_lt_zpow_right
  given: (ha : 1 < a) (h : m < n)
  statement: a ^ m < a ^ n
  proof: zpow_right_strictMono ha h

@[to_additive zsmul_le_zsmul_iff_left]

中文:
引理 zpow_lt_zpow_right
  条件: (ha : 1 < a) (h : m < n)
  结论: a ^ m < a ^ n
  证明: zpow_right_strictMono ha h

@[to_additive zsmul_le_zsmul_iff_left]

Depends on / 依赖: zpow_right_strictMono
-/
lemma zpow_lt_zpow_right (ha : 1 < a) (h : m < n) : a ^ m < a ^ n := zpow_right_strictMono ha h

@[to_additive zsmul_le_zsmul_iff_left]
/--
lemma `zpow_le_zpow_iff_right` / 引理 `zpow_le_zpow_iff_right`

English:
lemma zpow_le_zpow_iff_right
  given: (ha : 1 < a)
  statement: a ^ m <= a ^ n ↔ m <= n
  proof: (zpow_right_strictMono ha).le_iff_le

@[to_additive zsmul_lt_zsmul_iff_left]

中文:
引理 zpow_le_zpow_iff_right
  条件: (ha : 1 < a)
  结论: a ^ m <= a ^ n ↔ m <= n
  证明: (zpow_right_strictMono ha).le_iff_le

@[to_additive zsmul_lt_zsmul_iff_left]

Depends on / 依赖: le_iff_le, zpow_right_strictMono
-/
lemma zpow_le_zpow_iff_right (ha : 1 < a) : a ^ m <= a ^ n ↔ m <= n :=
  (zpow_right_strictMono ha).le_iff_le

@[to_additive zsmul_lt_zsmul_iff_left]
/--
lemma `zpow_lt_zpow_iff_right` / 引理 `zpow_lt_zpow_iff_right`

English:
lemma zpow_lt_zpow_iff_right
  given: (ha : 1 < a)
  statement: a ^ m < a ^ n ↔ m < n
  proof: (zpow_right_strictMono ha).lt_iff_lt

中文:
引理 zpow_lt_zpow_iff_right
  条件: (ha : 1 < a)
  结论: a ^ m < a ^ n ↔ m < n
  证明: (zpow_right_strictMono ha).lt_iff_lt

Depends on / 依赖: lt_iff_lt, zpow_right_strictMono
-/
lemma zpow_lt_zpow_iff_right (ha : 1 < a) : a ^ m < a ^ n ↔ m < n :=
  (zpow_right_strictMono ha).lt_iff_lt

variable (α)

@[to_additive zsmul_strictMono_right]
/--
lemma `zpow_left_strictMono` / 引理 `zpow_left_strictMono`

English:
lemma zpow_left_strictMono
  given: (hn : 0 < n)
  statement: StrictMono ((· ^ n) : α -> α)
  proof: fun a b hab => by
  rw [← one_lt_div']; rw [← div_zpow]; exact one_lt_zpow (one_lt_div'.2 hab) hn

@[to_additive zsmul_mono_right]

中文:
引理 zpow_left_strictMono
  条件: (hn : 0 < n)
  结论: 严格递增 ((· ^ n) : α -> α)
  证明: fun a b hab => by
  rw [← one_lt_div']; rw [← div_zpow]; exact one_lt_zpow (one_lt_div'.2 hab) hn

@[to_additive zsmul_mono_right]

Depends on / 依赖: div_zpow, one_lt_div, one_lt_zpow
-/
lemma zpow_left_strictMono (hn : 0 < n) : StrictMono ((· ^ n) : α -> α) := fun a b hab => by
  rw [← one_lt_div']; rw [← div_zpow]; exact one_lt_zpow (one_lt_div'.2 hab) hn

@[to_additive zsmul_mono_right]
/--
lemma `zpow_left_mono` / 引理 `zpow_left_mono`

English:
lemma zpow_left_mono
  given: (hn : 0 <= n)
  statement: Monotone ((· ^ n) : α -> α)
  proof: fun a b hab => by
  rw [← one_le_div']; rw [← div_zpow]; exact one_le_zpow (one_le_div'.2 hab) hn

中文:
引理 zpow_left_mono
  条件: (hn : 0 <= n)
  结论: 递增 ((· ^ n) : α -> α)
  证明: fun a b hab => by
  rw [← one_le_div']; rw [← div_zpow]; exact one_le_zpow (one_le_div'.2 hab) hn

Depends on / 依赖: div_zpow, one_le_div, one_le_zpow
-/
lemma zpow_left_mono (hn : 0 <= n) : Monotone ((· ^ n) : α -> α) := fun a b hab => by
  rw [← one_le_div']; rw [← div_zpow]; exact one_le_zpow (one_le_div'.2 hab) hn

variable {α}

@[to_additive (attr := gcongr) zsmul_le_zsmul_right]
/--
lemma `zpow_le_zpow_left` / 引理 `zpow_le_zpow_left`

English:
lemma zpow_le_zpow_left
  given: (hn : 0 <= n) (h : a <= b)
  statement: a ^ n <= b ^ n
  proof: zpow_left_mono α hn h

@[to_additive (attr := gcongr) zsmul_lt_zsmul_right]

中文:
引理 zpow_le_zpow_left
  条件: (hn : 0 <= n) (h : a <= b)
  结论: a ^ n <= b ^ n
  证明: zpow_left_mono α hn h

@[to_additive (attr := gcongr) zsmul_lt_zsmul_right]

Depends on / 依赖: zpow_left_mono
-/
lemma zpow_le_zpow_left (hn : 0 <= n) (h : a <= b) : a ^ n <= b ^ n := zpow_left_mono α hn h

@[to_additive (attr := gcongr) zsmul_lt_zsmul_right]
/--
lemma `zpow_lt_zpow_left` / 引理 `zpow_lt_zpow_left`

English:
lemma zpow_lt_zpow_left
  given: (hn : 0 < n) (h : a < b)
  statement: a ^ n < b ^ n
  proof: zpow_left_strictMono α hn h

中文:
引理 zpow_lt_zpow_left
  条件: (hn : 0 < n) (h : a < b)
  结论: a ^ n < b ^ n
  证明: zpow_left_strictMono α hn h

Depends on / 依赖: zpow_left_strictMono
-/
lemma zpow_lt_zpow_left (hn : 0 < n) (h : a < b) : a ^ n < b ^ n := zpow_left_strictMono α hn h

end OrderedCommGroup

section LinearOrderedCommGroup

variable [CommGroup α] [LinearOrder α] [IsOrderedMonoid α] {n : Int} {a b : α}

@[to_additive zsmul_le_zsmul_iff_right]
/--
lemma `zpow_le_zpow_iff_left` / 引理 `zpow_le_zpow_iff_left`

English:
lemma zpow_le_zpow_iff_left
  given: (hn : 0 < n)
  statement: a ^ n <= b ^ n ↔ a <= b
  proof: (zpow_left_strictMono α hn).le_iff_le

@[to_additive zsmul_lt_zsmul_iff_right]

中文:
引理 zpow_le_zpow_iff_left
  条件: (hn : 0 < n)
  结论: a ^ n <= b ^ n ↔ a <= b
  证明: (zpow_left_strictMono α hn).le_iff_le

@[to_additive zsmul_lt_zsmul_iff_right]

Depends on / 依赖: le_iff_le, zpow_left_strictMono
-/
lemma zpow_le_zpow_iff_left (hn : 0 < n) : a ^ n <= b ^ n ↔ a <= b :=
  (zpow_left_strictMono α hn).le_iff_le

@[to_additive zsmul_lt_zsmul_iff_right]
/--
lemma `zpow_lt_zpow_iff_left` / 引理 `zpow_lt_zpow_iff_left`

English:
lemma zpow_lt_zpow_iff_left
  given: (hn : 0 < n)
  statement: a ^ n < b ^ n ↔ a < b
  proof: (zpow_left_strictMono α hn).lt_iff_lt

中文:
引理 zpow_lt_zpow_iff_left
  条件: (hn : 0 < n)
  结论: a ^ n < b ^ n ↔ a < b
  证明: (zpow_left_strictMono α hn).lt_iff_lt

Depends on / 依赖: lt_iff_lt, zpow_left_strictMono
-/
lemma zpow_lt_zpow_iff_left (hn : 0 < n) : a ^ n < b ^ n ↔ a < b :=
  (zpow_left_strictMono α hn).lt_iff_lt

variable (α) in
/-- A nontrivial densely linear ordered commutative group can't be a cyclic group. -/
@[to_additive
  /-- A nontrivial densely linear ordered additive commutative group can't be a cyclic group. -/]
/--
theorem `not_isCyclic_of_denselyOrdered` / 定理 `not_isCyclic_of_denselyOrdered`

English:
theorem not_isCyclic_of_denselyOrdered
  given: [DenselyOrdered α] [Nontrivial α]
  statement: ¬IsCyclic α
  proof: by
  intro h
  rcases exists_zpow_surjective α with ⟨a, ha⟩
  rcases lt_trichotomy a 1 with hlt | rfl | hlt
  · rcases exists_between hlt with ⟨b, hab, hb⟩
    rcases ha b with ⟨k, rfl⟩
    suffices 0 < k ∧ k < 1 by lia
    rw [← one_lt_inv'] at hlt
    simp_rw [← zpow_lt_zpow_iff_right hlt]
    simp_all
  · rcases exists_ne (1 : α) with ⟨b, hb⟩
    simpa [hb.symm] using ha b
  · rcases exists_between hlt with ⟨b, hb, hba⟩
    rcases ha b with ⟨k, rfl⟩
    suffices 0 < k ∧ k < 1 by lia
    simp_rw [← zpow_lt_zpow_iff_right hlt]
    simp_all

中文:
定理 not_isCyclic_of_denselyOrdered
  条件: [稠密序 α] [非平凡 α]
  结论: ¬是循环 α
  证明: by
  intro h
  rcases exists_zpow_surjective α with ⟨a, ha⟩
  rcases lt_trichotomy a 1 with hlt | rfl | hlt
  · rcases exists_between hlt with ⟨b, hab, hb⟩
    rcases ha b with ⟨k, rfl⟩
    suffices 0 < k ∧ k < 1 by lia
    rw [← one_lt_inv'] at hlt
    simp_rw [← zpow_lt_zpow_iff_right hlt]
    simp_all
  · rcases exists_ne (1 : α) with ⟨b, hb⟩
    simpa [hb.symm] using ha b
  · rcases exists_between hlt with ⟨b, hb, hba⟩
    rcases ha b with ⟨k, rfl⟩
    suffices 0 < k ∧ k < 1 by lia
    simp_rw [← zpow_lt_zpow_iff_right hlt]
    simp_all

Depends on / 依赖: exists_between, exists_ne, exists_zpow_surjective, hb.symm, lt_trichotomy, one_lt_inv, simp_rw, zpow_lt_zpow_iff_right
-/
theorem not_isCyclic_of_denselyOrdered [DenselyOrdered α] [Nontrivial α] : ¬IsCyclic α := by
  intro h
  rcases exists_zpow_surjective α with ⟨a, ha⟩
  rcases lt_trichotomy a 1 with hlt | rfl | hlt
  · rcases exists_between hlt with ⟨b, hab, hb⟩
    rcases ha b with ⟨k, rfl⟩
    suffices 0 < k ∧ k < 1 by lia
    rw [← one_lt_inv'] at hlt
    simp_rw [← zpow_lt_zpow_iff_right hlt]
    simp_all
  · rcases exists_ne (1 : α) with ⟨b, hb⟩
    simpa [hb.symm] using ha b
  · rcases exists_between hlt with ⟨b, hb, hba⟩
    rcases ha b with ⟨k, rfl⟩
    suffices 0 < k ∧ k < 1 by lia
    simp_rw [← zpow_lt_zpow_iff_right hlt]
    simp_all

end LinearOrderedCommGroup
