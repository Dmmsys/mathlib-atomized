/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Pi
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Star.Conjneg

/-!
# Order properties of conjugation-negation
-/

public section

open scoped ComplexConjugate

variable {G R : Type*} [AddGroup G]

section OrderedCommSemiring
variable [CommSemiring R] [PartialOrder R] [StarRing R] [StarOrderedRing R] {f : G -> R}

/--
lemma `conjneg_nonneg` / 引理 `conjneg_nonneg`

English:
lemma conjneg_nonneg
  statement: 0 <= conjneg f ↔ 0 <= f
  proof: (Equiv.neg _).forall_congr' by simp [starRingEnd_apply]

中文:
引理 conjneg_nonneg
  结论: 0 <= conjneg f ↔ 0 <= f
  证明: (Equiv.neg _).forall_congr' by simp [starRingEnd_apply]
-/
@[simp] lemma conjneg_nonneg : 0 <= conjneg f ↔ 0 <= f :=
(Equiv.neg _).forall_congr' by simp [starRingEnd_apply]

/--
lemma `conjneg_pos` / 引理 `conjneg_pos`

English:
lemma conjneg_pos
  statement: 0 < conjneg f ↔ 0 < f
  proof: by
  simp_rw [lt_iff_le_and_ne, ne_comm, conjneg_nonneg, conjneg_ne_zero]

中文:
引理 conjneg_pos
  结论: 0 < conjneg f ↔ 0 < f
  证明: by
  simp_rw [lt_iff_le_and_ne, ne_comm, conjneg_nonneg, conjneg_ne_zero]
-/
@[simp] lemma conjneg_pos : 0 < conjneg f ↔ 0 < f := by
  simp_rw [lt_iff_le_and_ne, ne_comm, conjneg_nonneg, conjneg_ne_zero]

end OrderedCommSemiring

section OrderedCommRing
variable [CommRing R] [PartialOrder R] [StarRing R] [StarOrderedRing R] {f : G -> R}

/--
lemma `conjneg_nonpos` / 引理 `conjneg_nonpos`

English:
lemma conjneg_nonpos
  statement: conjneg f <= 0 ↔ f <= 0
  proof: by
  simp_rw [← neg_nonneg, ← conjneg_neg, conjneg_nonneg]

中文:
引理 conjneg_nonpos
  结论: conjneg f <= 0 ↔ f <= 0
  证明: by
  simp_rw [← neg_nonneg, ← conjneg_neg, conjneg_nonneg]
-/
@[simp] lemma conjneg_nonpos : conjneg f <= 0 ↔ f <= 0 := by
  simp_rw [← neg_nonneg, ← conjneg_neg, conjneg_nonneg]

/--
lemma `conjneg_neg'` / 引理 `conjneg_neg'`

English:
lemma conjneg_neg'
  statement: conjneg f < 0 ↔ f < 0
  proof: by
  simp_rw [← neg_pos, ← conjneg_neg, conjneg_pos]

中文:
引理 conjneg_neg'
  结论: conjneg f < 0 ↔ f < 0
  证明: by
  simp_rw [← neg_pos, ← conjneg_neg, conjneg_pos]
-/
@[simp] lemma conjneg_neg' : conjneg f < 0 ↔ f < 0 := by
  simp_rw [← neg_pos, ← conjneg_neg, conjneg_pos]

end OrderedCommRing
