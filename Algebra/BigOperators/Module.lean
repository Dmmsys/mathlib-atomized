/-
Copyright (c) 2022 Dylan MacKenzie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dylan MacKenzie
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Tactic.Abel

/-!
# Summation by parts
-/

public section

namespace Finset
variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] (f : Nat -> R) (g : Nat -> M) {m n : Nat}

-- The partial sum of `g`, starting from zero
local notation "G " n:80 => ∑ i in range n, g i

/--
theorem `sum_Ico_by_parts` / 定理 `sum_Ico_by_parts`

English:
theorem sum_Ico_by_parts
  given: (hmn : m < n)
  proof: by
  have h₁ : (∑ i in Ico (m + 1) n, f i • G i) = ∑ i in Ico m (n - 1), f (i + 1) • G (i + 1) := by
    rw [← Nat.sub_add_cancel (Nat.one_le_of_lt hmn)]; rw [← sum_Ico_add']
    simp only [add_tsub_cancel_right]
  have h₂ :
    (∑ i in Ico (m + 1) n, f i • G (i + 1)) =
      (∑ i in Ico m (n - 1), 

中文:
定理 sum_Ico_by_parts
  条件: (hmn : m < n)
  证明: by
  have h₁ : (∑ i in Ico (m + 1) n, f i • G i) = ∑ i in Ico m (n - 1), f (i + 1) • G (i + 1) := by
    rw [← Nat.sub_add_cancel (Nat.one_le_of_lt hmn)]; rw [← sum_Ico_add']
    simp only [add_tsub_cancel_right]
  have h₂ :
    (∑ i in Ico (m + 1) n, f i • G (i + 1)) =
      (∑ i in Ico m (n - 1), 

Depends on / 依赖: Nat.le_sub_one_of_lt, Nat.one_le_of_lt, Nat.sub_add_cancel, add_tsub_cancel_right, le_sub_one_of_lt, one_le_of_lt, pos_of_gt, sub_add_cancel, sum_Ico_add, sum_Ico_sub_bot, sum_Ico_succ_sub_top, sum_eq_sum
-/
theorem sum_Ico_by_parts (hmn : m < n) :
    ∑ i in Ico m n, f i • g i =
      f (n - 1) • G n - f m • G m - ∑ i in Ico m (n - 1), (f (i + 1) - f i) • G (i + 1) := by
  have h₁ : (∑ i in Ico (m + 1) n, f i • G i) = ∑ i in Ico m (n - 1), f (i + 1) • G (i + 1) := by
    rw [← Nat.sub_add_cancel (Nat.one_le_of_lt hmn)]; rw [← sum_Ico_add']
    simp only [add_tsub_cancel_right]
  have h₂ :
    (∑ i in Ico (m + 1) n, f i • G (i + 1)) =
      (∑ i in Ico m (n - 1), f i • G (i + 1)) + f (n - 1) • G n - f m • G (m + 1) := by
    rw [← sum_Ico_sub_bot _ hmn]; rw [← sum_Ico_succ_sub_top _ (Nat.le_sub_one_of_lt hmn)]; rw [Nat.sub_add_cancel (pos_of_gt hmn)]; rw [sub_add_cancel]
  rw [sum_eq_sum_Ico_succ_bot hmn]
  conv in (occs := 3) (f _ • g _) => rw [← sum_range_succ_sub_sum g]
  simp_rw [smul_sub, sum_sub_distrib, h₂, h₁]
  conv_lhs => congr; rfl; rw [← add_sub, add_comm, ← add_sub, ← sum_sub_distrib]
  have : forall i, f i • G (i + 1) - f (i + 1) • G (i + 1) = -((f (i + 1) - f i) • G (i + 1)) := by
    intro i
    rw [sub_smul]
    abel
  simp_rw [this, sum_neg_distrib, sum_range_succ, smul_add]
  abel

/--
theorem `sum_Ioc_by_parts` / 定理 `sum_Ioc_by_parts`

English:
theorem sum_Ioc_by_parts
  given: (hmn : m < n)
  proof: by
  simpa only [← Ico_add_one_add_one_eq_Ioc, Nat.sub_add_cancel (Nat.one_le_of_lt hmn),
    add_tsub_cancel_right] using! sum_Ico_by_parts f g (Nat.succ_lt_succ hmn)

中文:
定理 sum_Ioc_by_parts
  条件: (hmn : m < n)
  证明: by
  simpa only [← Ico_add_one_add_one_eq_Ioc, Nat.sub_add_cancel (Nat.one_le_of_lt hmn),
    add_tsub_cancel_right] using! sum_Ico_by_parts f g (Nat.succ_lt_succ hmn)

Depends on / 依赖: Ico_add_one_add_one_eq_Ioc, Nat.one_le_of_lt, Nat.sub_add_cancel, Nat.succ_lt_succ, add_tsub_cancel_right, one_le_of_lt, sub_add_cancel, succ_lt_succ, sum_Ico_by_parts
-/
theorem sum_Ioc_by_parts (hmn : m < n) :
    ∑ i in Ioc m n, f i • g i =
      f n • G (n + 1) - f (m + 1) • G (m + 1)
        - ∑ i in Ioc m (n - 1), (f (i + 1) - f i) • G (i + 1) := by
  simpa only [← Ico_add_one_add_one_eq_Ioc, Nat.sub_add_cancel (Nat.one_le_of_lt hmn),
    add_tsub_cancel_right] using! sum_Ico_by_parts f g (Nat.succ_lt_succ hmn)

variable (n)

/--
theorem `sum_range_by_parts` / 定理 `sum_range_by_parts`

English:
theorem sum_range_by_parts
  proof: by
  by_cases hn : n = 0
  · simp [hn]
  · simp only [range_eq_Ico]
    rw [sum_Ico_by_parts f g (Nat.pos_of_ne_zero hn)]; rw [sum_range_zero]; rw [smul_zero]; rw [sub_zero]
    simp only [← range_eq_Ico]

中文:
定理 sum_range_by_parts
  证明: by
  by_cases hn : n = 0
  · simp [hn]
  · simp only [range_eq_Ico]
    rw [sum_Ico_by_parts f g (Nat.pos_of_ne_zero hn)]; rw [sum_range_zero]; rw [smul_zero]; rw [sub_zero]
    simp only [← range_eq_Ico]

Depends on / 依赖: Nat.pos_of_ne_zero, pos_of_ne_zero, range_eq_Ico, smul_zero, sub_zero, sum_Ico_by_parts, sum_range_zero
-/
theorem sum_range_by_parts :
    ∑ i in range n, f i • g i =
      f (n - 1) • G n - ∑ i in range (n - 1), (f (i + 1) - f i) • G (i + 1) := by
  by_cases hn : n = 0
  · simp [hn]
  · simp only [range_eq_Ico]
    rw [sum_Ico_by_parts f g (Nat.pos_of_ne_zero hn)]; rw [sum_range_zero]; rw [smul_zero]; rw [sub_zero]
    simp only [← range_eq_Ico]

end Finset
