/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Conditions for `Fin.insertNth` to be monotone or strictly monotone

-/

public section

namespace Fin

variable {n : Nat} {α : Type*} [Preorder α]

/--
lemma `insertNth_zero_monotone` / 引理 `insertNth_zero_monotone`

English:
lemma insertNth_zero_monotone
  proof: by
  rw [Fin.monotone_iff_le_succ]
  intro i
  obtain rfl | ⟨i, rfl⟩ := i.eq_zero_or_eq_succ
  · simpa
  · simpa using hf i.castSucc_le_succ

中文:
引理 insertNth_zero_monotone
  证明: by
  rw [Fin.monotone_iff_le_succ]
  intro i
  obtain rfl | ⟨i, rfl⟩ := i.eq_zero_or_eq_succ
  · simpa
  · simpa using hf i.castSucc_le_succ

Depends on / 依赖: Fin.monotone_iff_le_succ, castSucc_le_succ, eq_zero_or_eq_succ, i.castSucc_le_succ, i.eq_zero_or_eq_succ, monotone_iff_le_succ
-/
lemma insertNth_zero_monotone
    {f : Fin (n + 1) -> α} (hf : Monotone f) (x : α) (hx : x <= f 0) :
    Monotone (Fin.insertNth 0 (α := fun _ => α) x f) := by
  rw [Fin.monotone_iff_le_succ]
  intro i
  obtain rfl | ⟨i, rfl⟩ := i.eq_zero_or_eq_succ
  · simpa
  · simpa using hf i.castSucc_le_succ

/--
lemma `strictMono_insertNth_zero` / 引理 `strictMono_insertNth_zero`

English:
lemma strictMono_insertNth_zero
  proof: by
  rw [Fin.strictMono_iff_lt_succ] at hf ⊢
  intro i
  obtain rfl | ⟨i, rfl⟩ := i.eq_zero_or_eq_succ
  · simpa
  · simpa using hf i

中文:
引理 strictMono_insertNth_zero
  证明: by
  rw [Fin.strictMono_iff_lt_succ] at hf ⊢
  intro i
  obtain rfl | ⟨i, rfl⟩ := i.eq_zero_or_eq_succ
  · simpa
  · simpa using hf i

Depends on / 依赖: Fin.strictMono_iff_lt_succ, eq_zero_or_eq_succ, i.eq_zero_or_eq_succ, strictMono_iff_lt_succ
-/
lemma strictMono_insertNth_zero
    {f : Fin (n + 1) -> α} (hf : StrictMono f) (x : α) (hx : x < f 0) :
    StrictMono (Fin.insertNth 0 (α := fun _ => α) x f) := by
  rw [Fin.strictMono_iff_lt_succ] at hf ⊢
  intro i
  obtain rfl | ⟨i, rfl⟩ := i.eq_zero_or_eq_succ
  · simpa
  · simpa using hf i

/--
lemma `insertNth_monotone` / 引理 `insertNth_monotone`

English:
lemma insertNth_monotone
  proof: by
  rw [Fin.monotone_iff_le_succ]
  intro j
  obtain hj | rfl | hj := lt_trichotomy j i.castSucc
  · obtain ⟨j, rfl⟩ := j.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hj)
    grind [insertNth_apply_below, castPred_castSucc, hf j.castSucc_le_succ]
  · rwa [← succAbove_succ_self i.castSucc, insertNth_apply_succAbove, insertNth_apply_same]
  · obtain ⟨j, rfl⟩ := j.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hj)
    grind [insertNth_apply_same, insertNth_apply_above, hf j.castSucc_le_succ]

中文:
引理 insertNth_monotone
  证明: by
  rw [Fin.monotone_iff_le_succ]
  intro j
  obtain hj | rfl | hj := lt_trichotomy j i.castSucc
  · obtain ⟨j, rfl⟩ := j.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hj)
    grind [insertNth_apply_below, castPred_castSucc, hf j.castSucc_le_succ]
  · rwa [← succAbove_succ_self i.castSucc, insertNth_apply_succAbove, insertNth_apply_same]
  · obtain ⟨j, rfl⟩ := j.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hj)
    grind [insertNth_apply_same, insertNth_apply_above, hf j.castSucc_le_succ]

Depends on / 依赖: Fin.monotone_iff_le_succ, Fin.ne_last_of_lt, Fin.ne_zero_of_lt, castPred_castSucc, castSucc, castSucc_le_succ, eq_castSucc_of_ne_last, eq_succ_of_ne_zero, i.castSucc, insertNth_apply_above, insertNth_apply_below, insertNth_apply_same, insertNth_apply_succAbove, j.castSucc_le_succ, j.eq_castSucc_of_ne_last, j.eq_succ_of_ne_zero, lt_trichotomy, monotone_iff_le_succ, ne_last_of_lt, ne_zero_of_lt
-/
lemma insertNth_monotone
    {f : Fin (n + 1) -> α} (hf : Monotone f) (i : Fin n) (x : α)
    (hx₁ : f i.castSucc <= x) (hx₂ : x <= f i.succ) :
    Monotone (Fin.insertNth i.castSucc.succ (α := fun _ => α) x f) := by
  rw [Fin.monotone_iff_le_succ]
  intro j
  obtain hj | rfl | hj := lt_trichotomy j i.castSucc
  · obtain ⟨j, rfl⟩ := j.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hj)
    grind [insertNth_apply_below, castPred_castSucc, hf j.castSucc_le_succ]
  · rwa [← succAbove_succ_self i.castSucc, insertNth_apply_succAbove, insertNth_apply_same]
  · obtain ⟨j, rfl⟩ := j.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hj)
    grind [insertNth_apply_same, insertNth_apply_above, hf j.castSucc_le_succ]

/--
lemma `strictMono_insertNth` / 引理 `strictMono_insertNth`

English:
lemma strictMono_insertNth
  proof: by
  rw [Fin.strictMono_iff_lt_succ] at hf ⊢
  intro j
  obtain hj | rfl | hj := lt_trichotomy j i.castSucc
  · obtain ⟨j, rfl⟩ := j.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hj)
    grind [insertNth_apply_below, castPred_castSucc]
  · rwa [← succAbove_succ_self i.castSucc, insertNth_apply_succAbove, insertNth_apply_same]
  · obtain ⟨j, rfl⟩ := j.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hj)
    grind [insertNth_apply_same, insertNth_apply_above]

中文:
引理 strictMono_insertNth
  证明: by
  rw [Fin.strictMono_iff_lt_succ] at hf ⊢
  intro j
  obtain hj | rfl | hj := lt_trichotomy j i.castSucc
  · obtain ⟨j, rfl⟩ := j.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hj)
    grind [insertNth_apply_below, castPred_castSucc]
  · rwa [← succAbove_succ_self i.castSucc, insertNth_apply_succAbove, insertNth_apply_same]
  · obtain ⟨j, rfl⟩ := j.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hj)
    grind [insertNth_apply_same, insertNth_apply_above]

Depends on / 依赖: Fin.ne_last_of_lt, Fin.ne_zero_of_lt, Fin.strictMono_iff_lt_succ, castPred_castSucc, castSucc, eq_castSucc_of_ne_last, eq_succ_of_ne_zero, i.castSucc, insertNth_apply_above, insertNth_apply_below, insertNth_apply_same, insertNth_apply_succAbove, j.eq_castSucc_of_ne_last, j.eq_succ_of_ne_zero, lt_trichotomy, ne_last_of_lt, ne_zero_of_lt, strictMono_iff_lt_succ, succAbove_succ_self
-/
lemma strictMono_insertNth
    {f : Fin (n + 1) -> α} (hf : StrictMono f) (i : Fin n) (x : α)
    (hx₁ : f i.castSucc < x) (hx₂ : x < f i.succ) :
    StrictMono (Fin.insertNth i.castSucc.succ (α := fun _ => α) x f) := by
  rw [Fin.strictMono_iff_lt_succ] at hf ⊢
  intro j
  obtain hj | rfl | hj := lt_trichotomy j i.castSucc
  · obtain ⟨j, rfl⟩ := j.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hj)
    grind [insertNth_apply_below, castPred_castSucc]
  · rwa [← succAbove_succ_self i.castSucc, insertNth_apply_succAbove, insertNth_apply_same]
  · obtain ⟨j, rfl⟩ := j.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hj)
    grind [insertNth_apply_same, insertNth_apply_above]

/--
lemma `insertNth_last_monotone` / 引理 `insertNth_last_monotone`

English:
lemma insertNth_last_monotone
  proof: by
  rw [Fin.monotone_iff_le_succ]
  intro i
  obtain ⟨i, rfl⟩ | rfl := i.eq_castSucc_or_eq_last
  · simpa only [insertNth_last', snoc_castSucc, Fin.succ_castSucc]
      using hf i.castSucc_le_succ
  · simpa

中文:
引理 insertNth_last_monotone
  证明: by
  rw [Fin.monotone_iff_le_succ]
  intro i
  obtain ⟨i, rfl⟩ | rfl := i.eq_castSucc_or_eq_last
  · simpa only [insertNth_last', snoc_castSucc, Fin.succ_castSucc]
      using hf i.castSucc_le_succ
  · simpa

Depends on / 依赖: Fin.monotone_iff_le_succ, Fin.succ_castSucc, castSucc_le_succ, eq_castSucc_or_eq_last, i.castSucc_le_succ, i.eq_castSucc_or_eq_last, insertNth_last, monotone_iff_le_succ, snoc_castSucc, succ_castSucc
-/
lemma insertNth_last_monotone
    {f : Fin (n + 1) -> α} (hf : Monotone f) (x : α) (hx : f (Fin.last n) <= x) :
    Monotone (Fin.insertNth (Fin.last (n + 1)) (α := fun _ => α) x f) := by
  rw [Fin.monotone_iff_le_succ]
  intro i
  obtain ⟨i, rfl⟩ | rfl := i.eq_castSucc_or_eq_last
  · simpa only [insertNth_last', snoc_castSucc, Fin.succ_castSucc]
      using hf i.castSucc_le_succ
  · simpa

/--
lemma `strictMono_insertNth_last` / 引理 `strictMono_insertNth_last`

English:
lemma strictMono_insertNth_last
  proof: by
  rw [Fin.strictMono_iff_lt_succ] at hf ⊢
  intro i
  obtain ⟨i, rfl⟩ | rfl := i.eq_castSucc_or_eq_last
  · simpa only [insertNth_last', snoc_castSucc, Fin.succ_castSucc]
      using hf i
  · simpa

中文:
引理 strictMono_insertNth_last
  证明: by
  rw [Fin.strictMono_iff_lt_succ] at hf ⊢
  intro i
  obtain ⟨i, rfl⟩ | rfl := i.eq_castSucc_or_eq_last
  · simpa only [insertNth_last', snoc_castSucc, Fin.succ_castSucc]
      using hf i
  · simpa

Depends on / 依赖: Fin.strictMono_iff_lt_succ, Fin.succ_castSucc, eq_castSucc_or_eq_last, i.eq_castSucc_or_eq_last, insertNth_last, snoc_castSucc, strictMono_iff_lt_succ, succ_castSucc
-/
lemma strictMono_insertNth_last
    {f : Fin (n + 1) -> α} (hf : StrictMono f) (x : α) (hx : f (Fin.last n) < x) :
    StrictMono (Fin.insertNth (Fin.last (n + 1)) (α := fun _ => α) x f) := by
  rw [Fin.strictMono_iff_lt_succ] at hf ⊢
  intro i
  obtain ⟨i, rfl⟩ | rfl := i.eq_castSucc_or_eq_last
  · simpa only [insertNth_last', snoc_castSucc, Fin.succ_castSucc]
      using hf i
  · simpa

end Fin
