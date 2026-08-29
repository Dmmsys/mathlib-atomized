/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Algebra.Order.SuccPred.PartialSups
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Order.Disjointed

/-!
# `Disjointed` for functions on a `SuccAddOrder`

This file contains material excised from `Mathlib/Order/Disjointed.lean` to avoid import
dependencies from `Mathlib.Algebra.Order` into `Mathlib.Order`.

## TODO

Find a useful statement of `disjointedRec_succ`.
-/

@[expose] public section

open Order

variable {α ι : Type*} [GeneralizedBooleanAlgebra α]

section SuccAddOrder

variable [LinearOrder ι] [LocallyFiniteOrderBot ι] [Add ι] [One ι] [SuccAddOrder ι]

/--
theorem `disjointed_add_one` / 定理 `disjointed_add_one`

English:
theorem disjointed_add_one
  given: [NoMaxOrder ι] (f : ι -> α) (i : ι)
  proof: by
  simpa only [succ_eq_add_one] using disjointed_succ f (not_isMax i)

中文:
定理 disjointed_add_one
  条件: [NoMax序 ι] (f : ι -> α) (i : ι)
  证明: by
  simpa only [succ_eq_add_one] using disjointed_succ f (not_isMax i)

Depends on / 依赖: disjointed_succ, not_isMax, succ_eq_add_one
-/
theorem disjointed_add_one [NoMaxOrder ι] (f : ι -> α) (i : ι) :
    disjointed f (i + 1) = f (i + 1) \ partialSups f i := by
  simpa only [succ_eq_add_one] using disjointed_succ f (not_isMax i)

/--
lemma `partialSups_add_one_eq_sup_disjointed` / 引理 `partialSups_add_one_eq_sup_disjointed`

English:
lemma partialSups_add_one_eq_sup_disjointed
  given: (f : ι -> α) (i : ι)
  proof: by
  by_cases hi : IsMax i
  · have : i + 1 = i := by
      have h : i <= i + 1 := by
        rw [← Order.succ_eq_add_one]
        apply Order.le_succ
      exact le_antisymm (hi h) h
    simp only [this, left_eq_sup, ge_iff_le, disjointed, sdiff_le_iff]
    apply le_trans (le_partialSups _ _) le_sup_right
  · rw [← Order.succ_eq_add_one, disjointed_succ _ hi]
    simp

中文:
引理 partialSups_add_one_eq_sup_disjointed
  条件: (f : ι -> α) (i : ι)
  证明: by
  by_cases hi : IsMax i
  · have : i + 1 = i := by
      have h : i <= i + 1 := by
        rw [← Order.succ_eq_add_one]
        apply Order.le_succ
      exact le_antisymm (hi h) h
    simp only [this, left_eq_sup, ge_iff_le, disjointed, sdiff_le_iff]
    apply le_trans (le_partialSups _ _) le_sup_right
  · rw [← Order.succ_eq_add_one, disjointed_succ _ hi]
    simp

Depends on / 依赖: Order.le_succ, Order.succ_eq_add_one, disjointed, disjointed_succ, ge_iff_le, le_antisymm, le_partialSups, le_succ, le_sup_right, le_trans, left_eq_sup, sdiff_le_iff, succ_eq_add_one
-/
lemma partialSups_add_one_eq_sup_disjointed (f : ι -> α) (i : ι) :
    partialSups f (i + 1) = partialSups f i ⊔ disjointed f (i + 1) := by
  by_cases hi : IsMax i
  · have : i + 1 = i := by
      have h : i <= i + 1 := by
        rw [← Order.succ_eq_add_one]
        apply Order.le_succ
      exact le_antisymm (hi h) h
    simp only [this, left_eq_sup, ge_iff_le, disjointed, sdiff_le_iff]
    apply le_trans (le_partialSups _ _) le_sup_right
  · rw [← Order.succ_eq_add_one, disjointed_succ _ hi]
    simp

/--
lemma `Monotone.disjointed_add_one_sup` / 引理 `Monotone.disjointed_add_one_sup`

English:
lemma Monotone.disjointed_add_one_sup
  given: {f : ι -> α} (hf : Monotone f) (i : ι)
  proof: by
  simpa only [succ_eq_add_one i] using hf.disjointed_succ_sup i

中文:
引理 递增.disjointed_add_one_sup
  条件: {f : ι -> α} (hf : 递增 f) (i : ι)
  证明: by
  simpa only [succ_eq_add_one i] using hf.disjointed_succ_sup i
-/
protected lemma Monotone.disjointed_add_one_sup {f : ι -> α} (hf : Monotone f) (i : ι) :
    disjointed f (i + 1) ⊔ f i = f (i + 1) := by
  simpa only [succ_eq_add_one i] using hf.disjointed_succ_sup i

/--
lemma `Monotone.disjointed_add_one` / 引理 `Monotone.disjointed_add_one`

English:
lemma Monotone.disjointed_add_one
  given: [NoMaxOrder ι] {f : ι -> α} (hf : Monotone f) (i : ι)
  proof: by
  rw [← succ_eq_add_one]; rw [hf.disjointed_succ]
  exact not_isMax i

中文:
引理 递增.disjointed_add_one
  条件: [NoMax序 ι] {f : ι -> α} (hf : 递增 f) (i : ι)
  证明: by
  rw [← succ_eq_add_one]; rw [hf.disjointed_succ]
  exact not_isMax i
-/
protected lemma Monotone.disjointed_add_one [NoMaxOrder ι] {f : ι -> α} (hf : Monotone f) (i : ι) :
    disjointed f (i + 1) = f (i + 1) \ f i := by
  rw [← succ_eq_add_one]; rw [hf.disjointed_succ]
  exact not_isMax i

end SuccAddOrder

section Nat

/--
Definition of `Nat.disjointedRec` / `Nat.disjointedRec` 的定义

English:
definition Nat.disjointedRec
  signature: {f : Nat -> α} {p : α -> Sort*} (hdiff : forall ⦃t i⦄, p t -> p (t \ f i))

中文:
定义 自然数.disjointedRec
  签名: {f : 自然数 -> α} {p : α -> 类型层*} (hdiff : 对任意 ⦃t i⦄, p t -> p (t \ f i))
-/
def Nat.disjointedRec {f : Nat -> α} {p : α -> Sort*} (hdiff : forall ⦃t i⦄, p t -> p (t \ f i)) :
    forall ⦃n⦄, p (f n) -> p (disjointed f n)
  | 0 => fun h₀ => disjointed_zero f ▸ h₀
  | n + 1 => fun h => by
    suffices H : forall k, p (f (n + 1) \ partialSups f k) from disjointed_add_one f n ▸ H n
    intro k
    induction k with
    | zero => exact hdiff h
    | succ k ih => simpa only [partialSups_add_one, ← sdiff_sdiff_left] using hdiff ih

@[simp]
/--
theorem `disjointedRec_zero` / 定理 `disjointedRec_zero`

English:
theorem disjointedRec_zero
  statement: {f : Nat -> α} {p : α -> Sort*}
  proof: rfl

中文:
定理 disjointedRec_zero
  结论: {f : 自然数 -> α} {p : α -> 类型层*}
  证明: rfl
-/
theorem disjointedRec_zero {f : Nat -> α} {p : α -> Sort*}
    (hdiff : forall ⦃t i⦄, p t -> p (t \ f i)) (h₀ : p (f 0)) :
    Nat.disjointedRec hdiff h₀ = (disjointed_zero f ▸ h₀) :=
  rfl

-- TODO: Find a useful statement of `disjointedRec_succ`.

end Nat
