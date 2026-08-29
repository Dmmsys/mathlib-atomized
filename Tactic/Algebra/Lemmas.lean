/-
Copyright (c) 2025 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Tactic.Ring.RingNF

/-! # Lemmas for the `algebra` tactic.
-/

@[expose] public section

open Mathlib.Meta.NormNum

namespace Mathlib.Tactic.Algebra

section ring

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/--
theorem `isInt_negOfNat_eq` / 定理 `isInt_negOfNat_eq`

English:
theorem isInt_negOfNat_eq
  given: {a : A} {lit : Nat} (h : IsInt a (Int.negOfNat lit))
  proof: by
  simp [h.out]

中文:
定理 isInt_negOfNat_eq
  条件: {a : A} {lit : 自然数} (h : Is整数 a (整数.negOf自然数 lit))
  证明: by
  simp [h.out]

Depends on / 依赖: h.out
-/
theorem isInt_negOfNat_eq {a : A} {lit : Nat} (h : IsInt a (Int.negOfNat lit)) :
    a = algebraMap R A (Int.rawCast (Int.negOfNat lit) + 0 : R) + 0 := by
  simp [h.out]

end ring

section semifield

variable {R A : Type*} [Semifield R] [Semifield A] [Algebra R A]

/--
theorem `isNNRat_eq_rawCast` / 定理 `isNNRat_eq_rawCast`

English:
theorem isNNRat_eq_rawCast
  given: {a : A} {n d : Nat} (h : IsNNRat a n d)
  proof: by
  simp [Mathlib.Tactic.Ring.cast_nnrat h]

中文:
定理 isNNRat_eq_rawCast
  条件: {a : A} {n d : 自然数} (h : IsNNRat a n d)
  证明: by
  simp [Mathlib.Tactic.Ring.cast_nnrat h]

Depends on / 依赖: Mathlib, Mathlib.Tactic.Ring.cast_nnrat, Tactic, cast_nnrat
-/
theorem isNNRat_eq_rawCast {a : A} {n d : Nat} (h : IsNNRat a n d) :
    a = algebraMap R A (NNRat.rawCast n d + 0 : R) + 0 := by
  simp [Mathlib.Tactic.Ring.cast_nnrat h]

end semifield

section field

variable {R A : Type*} [Field R] [Field A] [Algebra R A]

/--
theorem `isRat_eq_rawCast` / 定理 `isRat_eq_rawCast`

English:
theorem isRat_eq_rawCast
  given: {a : A} {n d : Nat} (h : IsRat a (.negOfNat n) d)
  proof: by
  simp [Mathlib.Tactic.Ring.cast_rat h]

中文:
定理 isRat_eq_rawCast
  条件: {a : A} {n d : 自然数} (h : IsRat a (.negOf自然数 n) d)
  证明: by
  simp [Mathlib.Tactic.Ring.cast_rat h]

Depends on / 依赖: Mathlib, Mathlib.Tactic.Ring.cast_rat, Tactic, cast_rat
-/
theorem isRat_eq_rawCast {a : A} {n d : Nat} (h : IsRat a (.negOfNat n) d) :
    a = algebraMap R A (Rat.rawCast (.negOfNat n) d + 0 : R) + 0 := by
  simp [Mathlib.Tactic.Ring.cast_rat h]

end field

variable {R A : Type*} [sR : CommSemiring R] [sA : CommSemiring A] [sAlg : Algebra R A]

/--
theorem `isNat_zero_eq` / 定理 `isNat_zero_eq`

English:
theorem isNat_zero_eq
  given: {a : A} (h : IsNat a 0)
  statement: a = 0
  proof: by
  have := h.out
  simp [this]

中文:
定理 isNat_zero_eq
  条件: {a : A} (h : Is自然数 a 0)
  结论: a = 0
  证明: by
  have := h.out
  simp [this]

Depends on / 依赖: h.out
-/
theorem isNat_zero_eq {a : A} (h : IsNat a 0) : a = 0 := by
  have := h.out
  simp [this]

/--
theorem `isNat_eq_rawCast` / 定理 `isNat_eq_rawCast`

English:
theorem isNat_eq_rawCast
  given: {a : A} {lit : Nat} (h : IsNat a lit)
  proof: by
  simp [h.out]

中文:
定理 isNat_eq_rawCast
  条件: {a : A} {lit : 自然数} (h : Is自然数 a lit)
  证明: by
  simp [h.out]

Depends on / 依赖: h.out
-/
theorem isNat_eq_rawCast {a : A} {lit : Nat} (h : IsNat a lit) :
    a = algebraMap R A (lit + 0 : R) + 0 := by
  simp [h.out]

section cleanup

variable {n d : Nat}

section cleanupSMul

/--
theorem `add_assoc_rev` / 定理 `add_assoc_rev`

English:
theorem add_assoc_rev
  given: (a b c : R)
  statement: a + (b + c) = a + b + c
  proof: (add_assoc ..).symm

中文:
定理 add_assoc_rev
  条件: (a b c : R)
  结论: a + (b + c) = a + b + c
  证明: (add_assoc ..).symm

Depends on / 依赖: add_assoc
-/
theorem add_assoc_rev (a b c : R) : a + (b + c) = a + b + c := (add_assoc ..).symm
/--
theorem `mul_assoc_rev` / 定理 `mul_assoc_rev`

English:
theorem mul_assoc_rev
  given: (a b c : R)
  statement: a * (b * c) = a * b * c
  proof: (mul_assoc ..).symm

中文:
定理 mul_assoc_rev
  条件: (a b c : R)
  结论: a * (b * c) = a * b * c
  证明: (mul_assoc ..).symm

Depends on / 依赖: mul_assoc
-/
theorem mul_assoc_rev (a b c : R) : a * (b * c) = a * b * c := (mul_assoc ..).symm
/--
theorem `mul_neg` / 定理 `mul_neg`

English:
theorem mul_neg
  given: {R} [Ring R] (a b : R)
  statement: a * -b = -(a * b)
  proof: by simp

中文:
定理 mul_neg
  条件: {R} [Ring R] (a b : R)
  结论: a * -b = -(a * b)
  证明: by simp
-/
theorem mul_neg {R} [Ring R] (a b : R) : a * -b = -(a * b) := by simp
/--
theorem `add_neg` / 定理 `add_neg`

English:
theorem add_neg
  given: {R} [Ring R] (a b : R)
  statement: a + -b = a - b
  proof: (sub_eq_add_neg ..).symm

中文:
定理 add_neg
  条件: {R} [Ring R] (a b : R)
  结论: a + -b = a - b
  证明: (sub_eq_add_neg ..).symm

Depends on / 依赖: sub_eq_add_neg
-/
theorem add_neg {R} [Ring R] (a b : R) : a + -b = a - b := (sub_eq_add_neg ..).symm
/--
theorem `nat_rawCast_0` / 定理 `nat_rawCast_0`

English:
theorem nat_rawCast_0
  statement: (Nat.rawCast 0 : R) = 0
  proof: by simp

中文:
定理 nat_rawCast_0
  结论: (自然数.rawCast 0 : R) = 0
  证明: by simp
-/
theorem nat_rawCast_0 : (Nat.rawCast 0 : R) = 0 := by simp
/--
theorem `nat_rawCast_1` / 定理 `nat_rawCast_1`

English:
theorem nat_rawCast_1
  statement: (Nat.rawCast 1 : R) = 1
  proof: by simp

中文:
定理 nat_rawCast_1
  结论: (自然数.rawCast 1 : R) = 1
  证明: by simp
-/
theorem nat_rawCast_1 : (Nat.rawCast 1 : R) = 1 := by simp
/--
theorem `nat_rawCast_2` / 定理 `nat_rawCast_2`

English:
theorem nat_rawCast_2
  given: [Nat.AtLeastTwo n]
  statement: (Nat.rawCast n : R) = OfNat.ofNat n
  proof: rfl

中文:
定理 nat_rawCast_2
  条件: [自然数.AtLeastTwo n]
  结论: (自然数.rawCast n : R) = Of自然数.of自然数 n
  证明: rfl
-/
theorem nat_rawCast_2 [Nat.AtLeastTwo n] : (Nat.rawCast n : R) = OfNat.ofNat n := rfl
/--
theorem `int_rawCast_neg` / 定理 `int_rawCast_neg`

English:
theorem int_rawCast_neg
  given: {R} [Ring R]
  statement: (Int.rawCast (.negOfNat n) : R) = -Nat.rawCast n
  proof: by simp

中文:
定理 int_rawCast_neg
  条件: {R} [Ring R]
  结论: (整数.rawCast (.negOf自然数 n) : R) = -自然数.rawCast n
  证明: by simp
-/
theorem int_rawCast_neg {R} [Ring R] : (Int.rawCast (.negOfNat n) : R) = -Nat.rawCast n := by simp
/--
theorem `nnrat_rawCast` / 定理 `nnrat_rawCast`

English:
theorem nnrat_rawCast
  given: {R} [DivisionSemiring R]
  proof: by simp

中文:
定理 nnrat_rawCast
  条件: {R} [DivisionSemiring R]
  证明: by simp
-/
theorem nnrat_rawCast {R} [DivisionSemiring R] :
    (NNRat.rawCast n d : R) = Nat.rawCast n / Nat.rawCast d := by simp
/--
theorem `rat_rawCast_neg` / 定理 `rat_rawCast_neg`

English:
theorem rat_rawCast_neg
  given: {R} [DivisionRing R]
  proof: by simp

中文:
定理 rat_rawCast_neg
  条件: {R} [DivisionRing R]
  证明: by simp
-/
theorem rat_rawCast_neg {R} [DivisionRing R] :
    (Rat.rawCast (.negOfNat n) d : R) = Int.rawCast (.negOfNat n) / Nat.rawCast d := by simp

end cleanupSMul
section cleanupConsts

/--
theorem `ofNat_smul` / 定理 `ofNat_smul`

English:
theorem ofNat_smul
  statement: {R A} [CommSemiring R] [CommSemiring A] [Algebra R A]
  proof: by
  simp_rw [← nat_rawCast_2]
  simp [Nat.cast_smul_eq_nsmul]

中文:
定理 ofNat_smul
  结论: {R A} [CommSemiring R] [CommSemiring A] [Algebra R A]
  证明: by
  simp_rw [← nat_rawCast_2]
  simp [Nat.cast_smul_eq_nsmul]

Depends on / 依赖: Nat.cast_smul_eq_nsmul, cast_smul_eq_nsmul, nat_rawCast_2, simp_rw
-/
theorem ofNat_smul {R A} [CommSemiring R] [CommSemiring A] [Algebra R A]
    [n.AtLeastTwo] {a : A} :
    (ofNat(n) : R) • a = ofNat(n) * a := by
  simp_rw [← nat_rawCast_2]
  simp [Nat.cast_smul_eq_nsmul]

/--
theorem `neg_ofNat_smul` / 定理 `neg_ofNat_smul`

English:
theorem neg_ofNat_smul
  given: {R A} [CommRing R] [CommRing A] [Algebra R A] {a : A} [n.AtLeastTwo]
  proof: by
  simpa [← nat_rawCast_2] using! ofNat_smul

中文:
定理 neg_ofNat_smul
  条件: {R A} [CommRing R] [CommRing A] [Algebra R A] {a : A} [n.AtLeastTwo]
  证明: by
  simpa [← nat_rawCast_2] using! ofNat_smul

Depends on / 依赖: nat_rawCast_2, ofNat_smul
-/
theorem neg_ofNat_smul {R A} [CommRing R] [CommRing A] [Algebra R A] {a : A} [n.AtLeastTwo] :
    (- ofNat(n) : R) • a = - (ofNat(n)) * a := by
  simpa [← nat_rawCast_2] using! ofNat_smul

/--
theorem `neg_1_smul` / 定理 `neg_1_smul`

English:
theorem neg_1_smul
  given: {R A} [CommRing R] [CommRing A] [Algebra R A] {a : A}
  proof: by
  simp

中文:
定理 neg_1_smul
  条件: {R A} [CommRing R] [CommRing A] [Algebra R A] {a : A}
  证明: by
  simp
-/
theorem neg_1_smul {R A} [CommRing R] [CommRing A] [Algebra R A] {a : A} :
    (-1 : R) • a = - a := by
  simp

/--
theorem `nnRat_ofNat_smul_1` / 定理 `nnRat_ofNat_smul_1`

English:
theorem nnRat_ofNat_smul_1
  statement: {R A} [Semifield R] [Semifield A] [Algebra R A] {a : A}
  proof: by
  simp [Algebra.smul_def, ← nat_rawCast_2]

中文:
定理 nnRat_ofNat_smul_1
  结论: {R A} [Semifield R] [Semifield A] [Algebra R A] {a : A}
  证明: by
  simp [Algebra.smul_def, ← nat_rawCast_2]

Depends on / 依赖: Algebra, Algebra.smul_def, nat_rawCast_2, smul_def
-/
theorem nnRat_ofNat_smul_1 {R A} [Semifield R] [Semifield A] [Algebra R A] {a : A}
    [d.AtLeastTwo] :
    (1 / ofNat(d) : R) • a = (1 / ofNat(d)) * a := by
  simp [Algebra.smul_def, ← nat_rawCast_2]

/--
theorem `nnRat_ofNat_smul_2` / 定理 `nnRat_ofNat_smul_2`

English:
theorem nnRat_ofNat_smul_2
  statement: {R A} [Semifield R] [Semifield A] [Algebra R A] {a : A}
  proof: by
  simp [Algebra.smul_def, ← nat_rawCast_2]

中文:
定理 nnRat_ofNat_smul_2
  结论: {R A} [Semifield R] [Semifield A] [Algebra R A] {a : A}
  证明: by
  simp [Algebra.smul_def, ← nat_rawCast_2]

Depends on / 依赖: Algebra, Algebra.smul_def, foobar, nat_rawCast_2, smul_def
-/
theorem nnRat_ofNat_smul_2 {R A} [Semifield R] [Semifield A] [Algebra R A] {a : A}
    [n.AtLeastTwo] [d.AtLeastTwo] :
    (ofNat(n) / ofNat(d) : R) • a = (ofNat(n) / ofNat(d)) * a := by
  simp [Algebra.smul_def, ← nat_rawCast_2]

/--
theorem `rat_ofNat_smul_1` / 定理 `rat_ofNat_smul_1`

English:
theorem rat_ofNat_smul_1
  statement: {R A} [Field R] [Field A] [Algebra R A] {a : A}
  proof: by
  simp [Algebra.smul_def, ← nat_rawCast_2]

中文:
定理 rat_ofNat_smul_1
  结论: {R A} [Field R] [Field A] [Algebra R A] {a : A}
  证明: by
  simp [Algebra.smul_def, ← nat_rawCast_2]

Depends on / 依赖: Algebra, Algebra.smul_def, nat_rawCast_2, smul_def
-/
theorem rat_ofNat_smul_1 {R A} [Field R] [Field A] [Algebra R A] {a : A}
    [d.AtLeastTwo] :
    ((- 1) / ofNat(d) : R) • a = ((- 1) / ofNat(d)) * a := by
  simp [Algebra.smul_def, ← nat_rawCast_2]

/--
theorem `rat_ofNat_smul_2` / 定理 `rat_ofNat_smul_2`

English:
theorem rat_ofNat_smul_2
  statement: {R A} [Field R] [Field A] [Algebra R A] {a : A}
  proof: by
  simp [Algebra.smul_def, ← nat_rawCast_2]

中文:
定理 rat_ofNat_smul_2
  结论: {R A} [Field R] [Field A] [Algebra R A] {a : A}
  证明: by
  simp [Algebra.smul_def, ← nat_rawCast_2]

Depends on / 依赖: Algebra, Algebra.smul_def, nat_rawCast_2, smul_def
-/
theorem rat_ofNat_smul_2 {R A} [Field R] [Field A] [Algebra R A] {a : A}
    [n.AtLeastTwo] [d.AtLeastTwo] :
    ((- ofNat(n)) / ofNat(d) : R) • a = ((- ofNat(n)) / ofNat(d)) * a := by
  simp [Algebra.smul_def, ← nat_rawCast_2]

end cleanupConsts

end cleanup

section equateScalars

/--
theorem `smul_one_eq_zero` / 定理 `smul_one_eq_zero`

English:
theorem smul_one_eq_zero
  given: {r : R} (h : r = 0)
  proof: by
  simp [h]

中文:
定理 smul_one_eq_zero
  条件: {r : R} (h : r = 0)
  证明: by
  simp [h]
-/
theorem smul_one_eq_zero {r : R} (h : r = 0) :
    r • (1 : A) = 0 := by
  simp [h]

/--
theorem `add_eq_zero` / 定理 `add_eq_zero`

English:
theorem add_eq_zero
  given: {a b : A} (ha : a = 0) (hb : b = 0)
  proof: by
  simp [ha, hb]

中文:
定理 add_eq_zero
  条件: {a b : A} (ha : a = 0) (hb : b = 0)
  证明: by
  simp [ha, hb]
-/
theorem add_eq_zero {a b : A} (ha : a = 0) (hb : b = 0) :
    a + b = 0 := by
  simp [ha, hb]

/--
theorem `smul_one_eq_smul_one'` / 定理 `smul_one_eq_smul_one'`

English:
theorem smul_one_eq_smul_one'
  given: {r s : R} (h : r = s)
  proof: by
  simp [h]

中文:
定理 smul_one_eq_smul_one'
  条件: {r s : R} (h : r = s)
  证明: by
  simp [h]
-/
theorem smul_one_eq_smul_one' {r s : R} (h : r = s) :
    r • (1 : A) = s • 1 := by
  simp [h]

/--
theorem `add_eq_of_zero_add` / 定理 `add_eq_of_zero_add`

English:
theorem add_eq_of_zero_add
  statement: {a₁ a₂ b₁ b₂ : A}
  proof: by
  subst_vars
  simp

中文:
定理 add_eq_of_zero_add
  结论: {a₁ a₂ b₁ b₂ : A}
  证明: by
  subst_vars
  simp
-/
theorem add_eq_of_zero_add {a₁ a₂ b₁ b₂ : A}
    (ha₁ : a₁ = 0) (ha₂ : a₂ = b₁ + b₂) :
    a₁ + a₂ = b₁ + b₂ := by
  subst_vars
  simp

/--
theorem `add_eq_of_add_zero` / 定理 `add_eq_of_add_zero`

English:
theorem add_eq_of_add_zero
  statement: {a₁ a₂ b₁ b₂ : A}
  proof: by
  subst_vars
  simp

中文:
定理 add_eq_of_add_zero
  结论: {a₁ a₂ b₁ b₂ : A}
  证明: by
  subst_vars
  simp
-/
theorem add_eq_of_add_zero {a₁ a₂ b₁ b₂ : A}
    (hb₁ : b₁ = 0) (ha : a₁ + a₂ = b₂) :
    a₁ + a₂ = b₁ + b₂ := by
  subst_vars
  simp

/--
theorem `add_eq_of_eq_eq` / 定理 `add_eq_of_eq_eq`

English:
theorem add_eq_of_eq_eq
  statement: {a₁ a₂ b₁ b₂ : A}
  proof: by
  subst_vars
  rfl

中文:
定理 add_eq_of_eq_eq
  结论: {a₁ a₂ b₁ b₂ : A}
  证明: by
  subst_vars
  rfl
-/
theorem add_eq_of_eq_eq {a₁ a₂ b₁ b₂ : A}
    (ha : a₁ = b₁) (hb : a₂ = b₂) :
    a₁ + a₂ = b₁ + b₂ := by
  subst_vars
  rfl

/- matchScalarsAux -/
omit sA in
/--
theorem `eq_trans_trans` / 定理 `eq_trans_trans`

English:
theorem eq_trans_trans
  statement: {e₁ e₂ a b : A}
  proof: by
  subst_vars
  rfl

中文:
定理 eq_trans_trans
  结论: {e₁ e₂ a b : A}
  证明: by
  subst_vars
  rfl
-/
theorem eq_trans_trans {e₁ e₂ a b : A}
    (ha : e₁ = a) (hb : e₂ = b) (hab : a = b) :
    e₁ = e₂ := by
  subst_vars
  rfl

/--
theorem `mul_eq_mul_of_eq` / 定理 `mul_eq_mul_of_eq`

English:
theorem mul_eq_mul_of_eq
  statement: {c a b : A}
  proof: by
  simp [h]

中文:
定理 mul_eq_mul_of_eq
  结论: {c a b : A}
  证明: by
  simp [h]
-/
theorem mul_eq_mul_of_eq {c a b : A}
    (h : a = b) :
    c * a = c * b := by
  simp [h]

end equateScalars

section RingCompute

/--
theorem `add_algebraMap` / 定理 `add_algebraMap`

English:
theorem add_algebraMap
  given: {r s t : R} (h : r + s = t)
  proof: by
  rw [← map_add]; rw [h]

中文:
定理 add_algebraMap
  条件: {r s t : R} (h : r + s = t)
  证明: by
  rw [← map_add]; rw [h]

Depends on / 依赖: map_add
-/
theorem add_algebraMap {r s t : R} (h : r + s = t) :
    algebraMap R A r + algebraMap R A s = algebraMap R A t := by
  rw [← map_add]; rw [h]

/--
theorem `add_algebraMap_isNat_zero` / 定理 `add_algebraMap_isNat_zero`

English:
theorem add_algebraMap_isNat_zero
  given: {r s : R} (h : r + s = 0)
  proof: by
  rw [← map_add]; rw [h]; rw [map_zero]
  exact ⟨by simp⟩

中文:
定理 add_algebraMap_isNat_zero
  条件: {r s : R} (h : r + s = 0)
  证明: by
  rw [← map_add]; rw [h]; rw [map_zero]
  exact ⟨by simp⟩

Depends on / 依赖: map_add, map_zero
-/
theorem add_algebraMap_isNat_zero {r s : R} (h : r + s = 0) :
    IsNat (algebraMap R A r + algebraMap R A s) 0 := by
  rw [← map_add]; rw [h]; rw [map_zero]
  exact ⟨by simp⟩

/--
theorem `cast_zero_smul_eq_zero_mul` / 定理 `cast_zero_smul_eq_zero_mul`

English:
theorem cast_zero_smul_eq_zero_mul
  statement: {R' : Type*} [HSMul R' A A] {r' : R'} {r : R}
  proof: by
  simp [← h_smul, hr]

中文:
定理 cast_zero_smul_eq_zero_mul
  结论: {R' : 类型} [HSMul R' A A] {r' : R'} {r : R}
  证明: by
  simp [← h_smul, hr]

Depends on / 依赖: h_smul
-/
theorem cast_zero_smul_eq_zero_mul {R' : Type*} [HSMul R' A A] {r' : R'} {r : R}
    (hr : r = 0) (h_smul : forall (a : A), r • a = r' • a) (a : A) :
    r' • a = (0 : A) * a := by
  simp [← h_smul, hr]

/--
theorem `cast_smul_eq_mul` / 定理 `cast_smul_eq_mul`

English:
theorem cast_smul_eq_mul
  statement: {R' : Type*} [HSMul R' A A] {r' : R'} {r r'' : R}
  proof: by
  simp [← h_smul, ← hr, Algebra.smul_def r a]

中文:
定理 cast_smul_eq_mul
  结论: {R' : 类型} [HSMul R' A A] {r' : R'} {r r'' : R}
  证明: by
  simp [← h_smul, ← hr, Algebra.smul_def r a]

Depends on / 依赖: Algebra, Algebra.smul_def, h_smul, smul_def
-/
theorem cast_smul_eq_mul {R' : Type*} [HSMul R' A A] {r' : R'} {r r'' : R}
    (hr : r = r'') (h_smul : forall (a : A), r • a = r' • a) (a : A) :
    r' • a = (algebraMap R A r'' + 0) * a := by
  simp [← h_smul, ← hr, Algebra.smul_def r a]

/--
theorem `neg_algebraMap` / 定理 `neg_algebraMap`

English:
theorem neg_algebraMap
  statement: {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  proof: by
  rw [← map_neg]; rw [h]

中文:
定理 neg_algebraMap
  结论: {R A : 类型} [CommRing R] [CommRing A] [Algebra R A]
  证明: by
  rw [← map_neg]; rw [h]

Depends on / 依赖: map_neg
-/
theorem neg_algebraMap {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {r t : R} (h : -r = t) :
    -(algebraMap R A r) = algebraMap R A t := by
  rw [← map_neg]; rw [h]

/--
theorem `pow_algebraMap` / 定理 `pow_algebraMap`

English:
theorem pow_algebraMap
  given: {r s : R} {b : Nat} (h : r ^ b = s)
  proof: by
  rw [← map_pow]; rw [h]

中文:
定理 pow_algebraMap
  条件: {r s : R} {b : 自然数} (h : r ^ b = s)
  证明: by
  rw [← map_pow]; rw [h]

Depends on / 依赖: map_pow
-/
theorem pow_algebraMap {r s : R} {b : Nat} (h : r ^ b = s) :
    (algebraMap R A r) ^ b = algebraMap R A s := by
  rw [← map_pow]; rw [h]

/--
theorem `inv_algebraMap` / 定理 `inv_algebraMap`

English:
theorem inv_algebraMap
  statement: {R A : Type*} [Semifield R] [Semifield A] [Algebra R A]
  proof: by
  rw [← map_inv₀]; rw [h]

中文:
定理 inv_algebraMap
  结论: {R A : 类型} [Semifield R] [Semifield A] [Algebra R A]
  证明: by
  rw [← map_inv₀]; rw [h]
-/
theorem inv_algebraMap {R A : Type*} [Semifield R] [Semifield A] [Algebra R A]
    {r s : R} (h : r⁻¹ = s) :
    (algebraMap R A r)⁻¹ = algebraMap R A s := by
  rw [← map_inv₀]; rw [h]

/--
theorem `isOne_algebraMap` / 定理 `isOne_algebraMap`

English:
theorem isOne_algebraMap
  given: {r : R} (h : IsNat r 1)
  proof: by
  simp only [h.out, Nat.cast_one, add_zero, map_one]
  exact ⟨by simp⟩

中文:
定理 isOne_algebraMap
  条件: {r : R} (h : Is自然数 r 1)
  证明: by
  simp only [h.out, Nat.cast_one, add_zero, map_one]
  exact ⟨by simp⟩

Depends on / 依赖: Nat.cast_one, add_zero, cast_one, h.out, map_one
-/
theorem isOne_algebraMap {r : R} (h : IsNat r 1) :
    IsNat (algebraMap R A (r + 0)) 1 := by
  simp only [h.out, Nat.cast_one, add_zero, map_one]
  exact ⟨by simp⟩

end RingCompute

end Mathlib.Tactic.Algebra
