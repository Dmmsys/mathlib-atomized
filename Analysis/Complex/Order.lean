/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Analysis.Complex.Norm

/-!
# The partial order on the complex numbers

This order is defined by `z ≤ w ↔ z.re ≤ w.re ∧ z.im = w.im`.

This is a natural order on `ℂ` because, as is well-known, there does not exist an order on `ℂ`
making it into a linearly ordered field. However, the order described above is the canonical order
stemming from the structure of `ℂ` as a ⋆-ring (i.e., it becomes a `StarOrderedRing`). Moreover,
with this order `ℂ` satisfies `IsStrictOrderedRing` and the coercion `(↑) : ℝ → ℂ` is an order
embedding.

This file only provides `Complex.partialOrder` and lemmas about it. Further structural classes are
provided in `Mathlib/Analysis/RCLike/Basic.lean` as

* `RCLike.toStrictOrderedCommRing`
* `RCLike.toStarOrderedRing`
* `RCLike.toOrderedSMul`

These are all only available with `open scoped ComplexOrder`.
-/

@[expose] public section

namespace Complex

/-- We put a partial order on ℂ so that `z ≤ w` exactly if `w - z` is real and nonnegative.
Complex numbers with different imaginary parts are incomparable.
-/
@[instance_reducible]
/--
Definition of `partialOrder` / `partialOrder` 的定义

English:
definition partialOrder
  signature: : PartialOrder Complex where
  body: z.re <= w.re ∧ z.im = w.im
  lt z w := z.re < w.re ∧ z.im = w.im
  lt_iff_le_not_ge z w := by
    rw [lt_iff_le_not_ge]
    tauto
  le_refl _ := ⟨le_rfl, rfl⟩
  le_trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩
  le_antisymm _ _ h₁ h₂ := ext (h₁.1.antisymm h₂.1) h₁.2

中文:
定义 partialOrder
  签名: : PartialOrder Complex where
  定义体: z.re <= w.re ∧ z.im = w.im
  lt z w := z.re < w.re ∧ z.im = w.im
  lt_iff_le_not_ge z w := by
    rw [lt_iff_le_not_ge]
    tauto
  le_refl _ := ⟨le_rfl, rfl⟩
  le_trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩
  le_antisymm _ _ h₁ h₂ := ext (h₁.1.antisymm h₂.1) h₁.2
-/
protected def partialOrder : PartialOrder Complex where
  le z w := z.re <= w.re ∧ z.im = w.im
  lt z w := z.re < w.re ∧ z.im = w.im
  lt_iff_le_not_ge z w := by
    rw [lt_iff_le_not_ge]
    tauto
  le_refl _ := ⟨le_rfl, rfl⟩
  le_trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩
  le_antisymm _ _ h₁ h₂ := ext (h₁.1.antisymm h₂.1) h₁.2

namespace _root_.ComplexOrder

scoped[ComplexOrder] attribute [instance] Complex.partialOrder

end _root_.ComplexOrder

open ComplexOrder

/--
theorem `le_def` / 定理 `le_def`

English:
theorem le_def
  given: {z w : Complex}
  statement: z <= w ↔ z.re <= w.re ∧ z.im = w.im
  proof: Iff.rfl

中文:
定理 le_def
  条件: {z w : Complex}
  结论: z <= w ↔ z.re <= w.re ∧ z.im = w.im
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem le_def {z w : Complex} : z <= w ↔ z.re <= w.re ∧ z.im = w.im :=
  Iff.rfl

/--
theorem `lt_def` / 定理 `lt_def`

English:
theorem lt_def
  given: {z w : Complex}
  statement: z < w ↔ z.re < w.re ∧ z.im = w.im
  proof: Iff.rfl

中文:
定理 lt_def
  条件: {z w : Complex}
  结论: z < w ↔ z.re < w.re ∧ z.im = w.im
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem lt_def {z w : Complex} : z < w ↔ z.re < w.re ∧ z.im = w.im :=
  Iff.rfl

/--
theorem `nonneg_iff` / 定理 `nonneg_iff`

English:
theorem nonneg_iff
  given: {z : Complex}
  statement: 0 <= z ↔ 0 <= z.re ∧ 0 = z.im
  proof: le_def

中文:
定理 nonneg_iff
  条件: {z : Complex}
  结论: 0 <= z ↔ 0 <= z.re ∧ 0 = z.im
  证明: le_def

Depends on / 依赖: le_def
-/
theorem nonneg_iff {z : Complex} : 0 <= z ↔ 0 <= z.re ∧ 0 = z.im :=
  le_def

/--
theorem `pos_iff` / 定理 `pos_iff`

English:
theorem pos_iff
  given: {z : Complex}
  statement: 0 < z ↔ 0 < z.re ∧ 0 = z.im
  proof: lt_def

中文:
定理 pos_iff
  条件: {z : Complex}
  结论: 0 < z ↔ 0 < z.re ∧ 0 = z.im
  证明: lt_def

Depends on / 依赖: lt_def
-/
theorem pos_iff {z : Complex} : 0 < z ↔ 0 < z.re ∧ 0 = z.im :=
  lt_def

/--
theorem `nonpos_iff` / 定理 `nonpos_iff`

English:
theorem nonpos_iff
  given: {z : Complex}
  statement: z <= 0 ↔ z.re <= 0 ∧ z.im = 0
  proof: le_def

中文:
定理 nonpos_iff
  条件: {z : Complex}
  结论: z <= 0 ↔ z.re <= 0 ∧ z.im = 0
  证明: le_def

Depends on / 依赖: le_def
-/
theorem nonpos_iff {z : Complex} : z <= 0 ↔ z.re <= 0 ∧ z.im = 0 :=
  le_def

/--
theorem `neg_iff` / 定理 `neg_iff`

English:
theorem neg_iff
  given: {z : Complex}
  statement: z < 0 ↔ z.re < 0 ∧ z.im = 0
  proof: lt_def

中文:
定理 neg_iff
  条件: {z : Complex}
  结论: z < 0 ↔ z.re < 0 ∧ z.im = 0
  证明: lt_def

Depends on / 依赖: lt_def
-/
theorem neg_iff {z : Complex} : z < 0 ↔ z.re < 0 ∧ z.im = 0 :=
  lt_def

/--
theorem `sq_nonneg_iff` / 定理 `sq_nonneg_iff`

English:
theorem sq_nonneg_iff
  given: {z : Complex}
  statement: 0 <= z ^ 2 ↔ z.im = 0
  proof: by
  rw [nonneg_iff]; rw [pow_two]; rw [mul_re]; rw [mul_im]; rw [mul_comm z.im z.re]; rw [← mul_two]; rw [eq_comm]; rw [mul_eq_zero_iff_right two_ne_zero]; rw [← pow_two]; rw [← pow_two]; rw [mul_eq_zero]
  exact ⟨by aesop, fun h => by simpa [h] using sq_nonneg z.re⟩

中文:
定理 sq_nonneg_iff
  条件: {z : Complex}
  结论: 0 <= z ^ 2 ↔ z.im = 0
  证明: by
  rw [nonneg_iff]; rw [pow_two]; rw [mul_re]; rw [mul_im]; rw [mul_comm z.im z.re]; rw [← mul_two]; rw [eq_comm]; rw [mul_eq_zero_iff_right two_ne_zero]; rw [← pow_two]; rw [← pow_two]; rw [mul_eq_zero]
  exact ⟨by aesop, fun h => by simpa [h] using sq_nonneg z.re⟩

Depends on / 依赖: eq_comm, mul_comm, mul_eq_zero, mul_eq_zero_iff_right, mul_im, mul_re, mul_two, nonneg_iff, pow_two, sq_nonneg, two_ne_zero, z.im, z.re
-/
theorem sq_nonneg_iff {z : Complex} : 0 <= z ^ 2 ↔ z.im = 0 := by
  rw [nonneg_iff]; rw [pow_two]; rw [mul_re]; rw [mul_im]; rw [mul_comm z.im z.re]; rw [← mul_two]; rw [eq_comm]; rw [mul_eq_zero_iff_right two_ne_zero]; rw [← pow_two]; rw [← pow_two]; rw [mul_eq_zero]
  exact ⟨by aesop, fun h => by simpa [h] using sq_nonneg z.re⟩

/--
theorem `sq_nonpos_iff` / 定理 `sq_nonpos_iff`

English:
theorem sq_nonpos_iff
  given: {z : Complex}
  statement: z ^ 2 <= 0 ↔ z.re = 0
  proof: by
  rw [nonpos_iff]; rw [pow_two]; rw [mul_re]; rw [mul_im]; rw [mul_comm z.im z.re]; rw [← mul_two]; rw [mul_eq_zero_iff_right
    two_ne_zero]; rw [← pow_two]; rw [← pow_two]; rw [mul_eq_zero]
  exact ⟨by aesop, fun h => by simpa [h] using sq_nonneg z.im⟩

@[simp, norm_cast]

中文:
定理 sq_nonpos_iff
  条件: {z : Complex}
  结论: z ^ 2 <= 0 ↔ z.re = 0
  证明: by
  rw [nonpos_iff]; rw [pow_two]; rw [mul_re]; rw [mul_im]; rw [mul_comm z.im z.re]; rw [← mul_two]; rw [mul_eq_zero_iff_right
    two_ne_zero]; rw [← pow_two]; rw [← pow_two]; rw [mul_eq_zero]
  exact ⟨by aesop, fun h => by simpa [h] using sq_nonneg z.im⟩

@[simp, norm_cast]

Depends on / 依赖: mul_comm, mul_eq_zero, mul_eq_zero_iff_right, mul_im, mul_re, mul_two, nonpos_iff, pow_two, sq_nonneg, two_ne_zero, z.im, z.re
-/
theorem sq_nonpos_iff {z : Complex} : z ^ 2 <= 0 ↔ z.re = 0 := by
  rw [nonpos_iff]; rw [pow_two]; rw [mul_re]; rw [mul_im]; rw [mul_comm z.im z.re]; rw [← mul_two]; rw [mul_eq_zero_iff_right
    two_ne_zero]; rw [← pow_two]; rw [← pow_two]; rw [mul_eq_zero]
  exact ⟨by aesop, fun h => by simpa [h] using sq_nonneg z.im⟩

@[simp, norm_cast]
/--
theorem `real_le_real` / 定理 `real_le_real`

English:
theorem real_le_real
  given: {x y : Real}
  statement: (x : Complex) <= (y : Complex) ↔ x <= y
  proof: by simp [le_def, ofReal]

@[simp, norm_cast]

中文:
定理 real_le_real
  条件: {x y : 实数}
  结论: (x : Complex) <= (y : Complex) ↔ x <= y
  证明: by simp [le_def, ofReal]

@[simp, norm_cast]

Depends on / 依赖: le_def, ofReal
-/
theorem real_le_real {x y : Real} : (x : Complex) <= (y : Complex) ↔ x <= y := by simp [le_def, ofReal]

@[simp, norm_cast]
/--
theorem `real_lt_real` / 定理 `real_lt_real`

English:
theorem real_lt_real
  given: {x y : Real}
  statement: (x : Complex) < (y : Complex) ↔ x < y
  proof: by simp [lt_def, ofReal]

@[simp, norm_cast]

中文:
定理 real_lt_real
  条件: {x y : 实数}
  结论: (x : Complex) < (y : Complex) ↔ x < y
  证明: by simp [lt_def, ofReal]

@[simp, norm_cast]

Depends on / 依赖: lt_def, ofReal
-/
theorem real_lt_real {x y : Real} : (x : Complex) < (y : Complex) ↔ x < y := by simp [lt_def, ofReal]

@[simp, norm_cast]
/--
theorem `zero_le_real` / 定理 `zero_le_real`

English:
theorem zero_le_real
  given: {x : Real}
  statement: (0 : Complex) <= (x : Complex) ↔ 0 <= x
  proof: real_le_real

@[simp, norm_cast]

中文:
定理 zero_le_real
  条件: {x : 实数}
  结论: (0 : Complex) <= (x : Complex) ↔ 0 <= x
  证明: real_le_real

@[simp, norm_cast]

Depends on / 依赖: real_le_real
-/
theorem zero_le_real {x : Real} : (0 : Complex) <= (x : Complex) ↔ 0 <= x :=
  real_le_real

@[simp, norm_cast]
/--
theorem `zero_lt_real` / 定理 `zero_lt_real`

English:
theorem zero_lt_real
  given: {x : Real}
  statement: (0 : Complex) < (x : Complex) ↔ 0 < x
  proof: real_lt_real

中文:
定理 zero_lt_real
  条件: {x : 实数}
  结论: (0 : Complex) < (x : Complex) ↔ 0 < x
  证明: real_lt_real

Depends on / 依赖: real_lt_real
-/
theorem zero_lt_real {x : Real} : (0 : Complex) < (x : Complex) ↔ 0 < x :=
  real_lt_real

/--
theorem `not_le_iff` / 定理 `not_le_iff`

English:
theorem not_le_iff
  given: {z w : Complex}
  statement: ¬z <= w ↔ w.re < z.re ∨ z.im != w.im
  proof: by
  rw [le_def]; rw [not_and_or]; rw [not_le]

中文:
定理 not_le_iff
  条件: {z w : Complex}
  结论: ¬z <= w ↔ w.re < z.re ∨ z.im != w.im
  证明: by
  rw [le_def]; rw [not_and_or]; rw [not_le]

Depends on / 依赖: le_def, not_and_or, not_le
-/
theorem not_le_iff {z w : Complex} : ¬z <= w ↔ w.re < z.re ∨ z.im != w.im := by
  rw [le_def]; rw [not_and_or]; rw [not_le]

/--
theorem `not_lt_iff` / 定理 `not_lt_iff`

English:
theorem not_lt_iff
  given: {z w : Complex}
  statement: ¬z < w ↔ w.re <= z.re ∨ z.im != w.im
  proof: by
  rw [lt_def]; rw [not_and_or]; rw [not_lt]

中文:
定理 not_lt_iff
  条件: {z w : Complex}
  结论: ¬z < w ↔ w.re <= z.re ∨ z.im != w.im
  证明: by
  rw [lt_def]; rw [not_and_or]; rw [not_lt]

Depends on / 依赖: lt_def, not_and_or, not_lt
-/
theorem not_lt_iff {z w : Complex} : ¬z < w ↔ w.re <= z.re ∨ z.im != w.im := by
  rw [lt_def]; rw [not_and_or]; rw [not_lt]

/--
theorem `not_le_zero_iff` / 定理 `not_le_zero_iff`

English:
theorem not_le_zero_iff
  given: {z : Complex}
  statement: ¬z <= 0 ↔ 0 < z.re ∨ z.im != 0
  proof: not_le_iff

中文:
定理 not_le_zero_iff
  条件: {z : Complex}
  结论: ¬z <= 0 ↔ 0 < z.re ∨ z.im != 0
  证明: not_le_iff

Depends on / 依赖: not_le_iff
-/
theorem not_le_zero_iff {z : Complex} : ¬z <= 0 ↔ 0 < z.re ∨ z.im != 0 :=
  not_le_iff

/--
theorem `not_lt_zero_iff` / 定理 `not_lt_zero_iff`

English:
theorem not_lt_zero_iff
  given: {z : Complex}
  statement: ¬z < 0 ↔ 0 <= z.re ∨ z.im != 0
  proof: not_lt_iff

中文:
定理 not_lt_zero_iff
  条件: {z : Complex}
  结论: ¬z < 0 ↔ 0 <= z.re ∨ z.im != 0
  证明: not_lt_iff

Depends on / 依赖: not_lt_iff
-/
theorem not_lt_zero_iff {z : Complex} : ¬z < 0 ↔ 0 <= z.re ∨ z.im != 0 :=
  not_lt_iff

/--
theorem `eq_re_of_ofReal_le` / 定理 `eq_re_of_ofReal_le`

English:
theorem eq_re_of_ofReal_le
  given: {r : Real} {z : Complex} (hz : (r : Complex) <= z)
  statement: z = z.re
  proof: by
  rw [eq_comm]; rw [← conj_eq_iff_re]; rw [conj_eq_iff_im]; rw [← (Complex.le_def.1 hz).2]; rw [Complex.ofReal_im]

@[simp]

中文:
定理 eq_re_of_ofReal_le
  条件: {r : 实数} {z : Complex} (hz : (r : Complex) <= z)
  结论: z = z.re
  证明: by
  rw [eq_comm]; rw [← conj_eq_iff_re]; rw [conj_eq_iff_im]; rw [← (Complex.le_def.1 hz).2]; rw [Complex.ofReal_im]

@[simp]

Depends on / 依赖: Complex.le_def, Complex.ofReal_im, conj_eq_iff_im, conj_eq_iff_re, eq_comm, le_def, ofReal_im
-/
theorem eq_re_of_ofReal_le {r : Real} {z : Complex} (hz : (r : Complex) <= z) : z = z.re := by
  rw [eq_comm]; rw [← conj_eq_iff_re]; rw [conj_eq_iff_im]; rw [← (Complex.le_def.1 hz).2]; rw [Complex.ofReal_im]

@[simp]
/--
lemma `re_eq_norm` / 引理 `re_eq_norm`

English:
lemma re_eq_norm
  given: {z : Complex}
  statement: z.re = ‖z‖ ↔ 0 <= z
  proof: have : 0 <= ‖z‖ := norm_nonneg z
  ⟨fun h => ⟨h.symm ▸ this, (abs_re_eq_norm.1 <| h.symm ▸ abs_of_nonneg this).symm⟩,
    fun ⟨h₁, h₂⟩ => by rw [← abs_re_eq_norm.2 h₂.symm, abs_of_nonneg h₁]⟩

@[simp]

中文:
引理 re_eq_norm
  条件: {z : Complex}
  结论: z.re = ‖z‖ ↔ 0 <= z
  证明: have : 0 <= ‖z‖ := norm_nonneg z
  ⟨fun h => ⟨h.symm ▸ this, (abs_re_eq_norm.1 <| h.symm ▸ abs_of_nonneg this).symm⟩,
    fun ⟨h₁, h₂⟩ => by rw [← abs_re_eq_norm.2 h₂.symm, abs_of_nonneg h₁]⟩

@[simp]

Depends on / 依赖: abs_of_nonneg, abs_re_eq_norm, h.symm, norm_nonneg
-/
lemma re_eq_norm {z : Complex} : z.re = ‖z‖ ↔ 0 <= z :=
  have : 0 <= ‖z‖ := norm_nonneg z
  ⟨fun h => ⟨h.symm ▸ this, (abs_re_eq_norm.1 <| h.symm ▸ abs_of_nonneg this).symm⟩,
    fun ⟨h₁, h₂⟩ => by rw [← abs_re_eq_norm.2 h₂.symm, abs_of_nonneg h₁]⟩

@[simp]
/--
lemma `neg_re_eq_norm` / 引理 `neg_re_eq_norm`

English:
lemma neg_re_eq_norm
  given: {z : Complex}
  statement: -z.re = ‖z‖ ↔ z <= 0
  proof: by
  rw [← neg_re]; rw [← norm_neg z]; rw [re_eq_norm]
exact neg_nonneg.and eq_comm.trans neg_eq_zero

@[simp]

中文:
引理 neg_re_eq_norm
  条件: {z : Complex}
  结论: -z.re = ‖z‖ ↔ z <= 0
  证明: by
  rw [← neg_re]; rw [← norm_neg z]; rw [re_eq_norm]
exact neg_nonneg.and eq_comm.trans neg_eq_zero

@[simp]

Depends on / 依赖: eq_comm, eq_comm.trans, neg_eq_zero, neg_nonneg, neg_nonneg.and, neg_re, norm_neg, re_eq_norm
-/
lemma neg_re_eq_norm {z : Complex} : -z.re = ‖z‖ ↔ z <= 0 := by
  rw [← neg_re]; rw [← norm_neg z]; rw [re_eq_norm]
exact neg_nonneg.and eq_comm.trans neg_eq_zero

@[simp]
/--
lemma `re_eq_neg_norm` / 引理 `re_eq_neg_norm`

English:
lemma re_eq_neg_norm
  given: {z : Complex}
  statement: z.re = -‖z‖ ↔ z <= 0
  proof: by rw [← neg_eq_iff_eq_neg, neg_re_eq_norm]

中文:
引理 re_eq_neg_norm
  条件: {z : Complex}
  结论: z.re = -‖z‖ ↔ z <= 0
  证明: by rw [← neg_eq_iff_eq_neg, neg_re_eq_norm]

Depends on / 依赖: neg_eq_iff_eq_neg, neg_re_eq_norm
-/
lemma re_eq_neg_norm {z : Complex} : z.re = -‖z‖ ↔ z <= 0 := by rw [← neg_eq_iff_eq_neg, neg_re_eq_norm]

/--
lemma `monotone_ofReal` / 引理 `monotone_ofReal`

English:
lemma monotone_ofReal
  statement: Monotone ofReal
  proof: by
  intro x y hxy
  simp only [real_le_real, hxy]

中文:
引理 monotone_ofReal
  结论: Monotone of实数
  证明: by
  intro x y hxy
  simp only [real_le_real, hxy]

Depends on / 依赖: real_le_real
-/
lemma monotone_ofReal : Monotone ofReal := by
  intro x y hxy
  simp only [real_le_real, hxy]

end Complex

namespace Mathlib.Meta.Positivity
open Lean Meta Qq Complex
open scoped ComplexOrder

alias ⟨_, ofReal_pos⟩ := zero_lt_real
alias ⟨_, ofReal_nonneg⟩ := zero_le_real
alias ⟨_, ofReal_ne_zero_of_ne_zero⟩ := ofReal_ne_zero

/-- Extension for the `positivity` tactic: `Complex.ofReal` is positive/nonnegative/nonzero if its
input is. -/
@[positivity Complex.ofReal _, Complex.ofReal _]
meta def evalComplexOfReal : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(Complex), ~q(Complex.ofReal $a) =>
    assumeInstancesCommute
    match ← core q(inferInstance) (some q(inferInstance)) a with
    | .positive pa => return .positive q(ofReal_pos $pa)
    | .nonnegative pa => return .nonnegative q(ofReal_nonneg $pa)
    | .nonzero pa => return .nonzero q(ofReal_ne_zero_of_ne_zero $pa)
    | _ => return .none
  | _, _ => throwError "not Complex.ofReal"

example (x : Real) (hx : 0 < x) : 0 < (x : Complex) := by positivity
example (x : Real) (hx : 0 <= x) : 0 <= (x : Complex) := by positivity
example (x : Real) (hx : x != 0) : (x : Complex) != 0 := by positivity

end Mathlib.Meta.Positivity
