/-
Copyright (c) 2025 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Analysis.Real.Sqrt

/-! # `norm_num` extension for `Real.sqrt`

This module defines a `norm_num` extension for `Real.sqrt` and `NNReal.sqrt`.
-/

public meta section

namespace Mathlib.Meta.NormNum

open Qq Lean Lean.Meta Elab.Tactic Mathlib.Meta.NormNum NNReal

/--
lemma `isNat_realSqrt` / 引理 `isNat_realSqrt`

English:
lemma isNat_realSqrt
  given: {x : Real} {nx ny : Nat} (h : IsNat x nx) (hy : ny * ny = nx)
  proof: ⟨by simp [h.out, ← hy]⟩

中文:
引理 is自然数_realSqrt
  条件: {x : 实数} {nx ny : 自然数} (h : 是自然数 x nx) (hy : ny * ny = nx)
  证明: ⟨by simp [h.out, ← hy]⟩

Depends on / 依赖: h.out
-/
lemma isNat_realSqrt {x : Real} {nx ny : Nat} (h : IsNat x nx) (hy : ny * ny = nx) :
    IsNat √x ny := ⟨by simp [h.out, ← hy]⟩

/--
lemma `isNat_nnrealSqrt` / 引理 `isNat_nnrealSqrt`

English:
lemma isNat_nnrealSqrt
  given: {x : Real>=0} {nx ny : Nat} (h : IsNat x nx) (hy : ny * ny = nx)
  proof: ⟨by simp [h.out, ← hy]⟩

中文:
引理 is自然数_nnrealSqrt
  条件: {x : 实数>=0} {nx ny : 自然数} (h : 是自然数 x nx) (hy : ny * ny = nx)
  证明: ⟨by simp [h.out, ← hy]⟩

Depends on / 依赖: h.out
-/
lemma isNat_nnrealSqrt {x : Real>=0} {nx ny : Nat} (h : IsNat x nx) (hy : ny * ny = nx) :
    IsNat (NNReal.sqrt x) ny := ⟨by simp [h.out, ← hy]⟩

/--
lemma `isNNRat_nnrealSqrt_of_isNNRat` / 引理 `isNNRat_nnrealSqrt_of_isNNRat`

English:
lemma isNNRat_nnrealSqrt_of_isNNRat
  statement: {x : Real>=0} {n sn : Nat} {d sd : Nat} (hn : sn * sn = n)
  proof: by
  obtain ⟨_, rfl⟩ := h
  refine ⟨?_, ?out⟩
  · apply invertibleOfNonzero
    rw [← mul_self_ne_zero]; rw [← Nat.cast_mul]; rw [hd]
    exact Invertible.ne_zero _
  · simp [← hn, ← hd, NNReal.sqrt_mul]

中文:
引理 isNNRat_nnrealSqrt_of_isNNRat
  结论: {x : 实数>=0} {n sn : 自然数} {d sd : 自然数} (hn : sn * sn = n)
  证明: by
  obtain ⟨_, rfl⟩ := h
  refine ⟨?_, ?out⟩
  · apply invertibleOfNonzero
    rw [← mul_self_ne_zero]; rw [← Nat.cast_mul]; rw [hd]
    exact Invertible.ne_zero _
  · simp [← hn, ← hd, NNReal.sqrt_mul]

Depends on / 依赖: Invertible, Invertible.ne_zero, NNReal, NNReal.sqrt_mul, Nat.cast_mul, cast_mul, invertibleOfNonzero, mul_self_ne_zero, ne_zero, sqrt_mul
-/
lemma isNNRat_nnrealSqrt_of_isNNRat {x : Real>=0} {n sn : Nat} {d sd : Nat} (hn : sn * sn = n)
    (hd : sd * sd = d) (h : IsNNRat x n d) :
    IsNNRat (NNReal.sqrt x) sn sd := by
  obtain ⟨_, rfl⟩ := h
  refine ⟨?_, ?out⟩
  · apply invertibleOfNonzero
    rw [← mul_self_ne_zero]; rw [← Nat.cast_mul]; rw [hd]
    exact Invertible.ne_zero _
  · simp [← hn, ← hd, NNReal.sqrt_mul]

/--
lemma `isNat_realSqrt_neg` / 引理 `isNat_realSqrt_neg`

English:
lemma isNat_realSqrt_neg
  given: {x : Real} {nx : Nat} (h : IsInt x (Int.negOfNat nx))
  proof: ⟨by simp [Real.sqrt_eq_zero', h.out]⟩

中文:
引理 is自然数_realSqrt_neg
  条件: {x : 实数} {nx : 自然数} (h : 是整数 x (整数.negOf自然数 nx))
  证明: ⟨by simp [Real.sqrt_eq_zero', h.out]⟩

Depends on / 依赖: Real.sqrt_eq_zero, h.out, sqrt_eq_zero
-/
lemma isNat_realSqrt_neg {x : Real} {nx : Nat} (h : IsInt x (Int.negOfNat nx)) :
    IsNat √x (nat_lit 0) := ⟨by simp [Real.sqrt_eq_zero', h.out]⟩

/--
lemma `isNat_realSqrt_of_isRat_negOfNat` / 引理 `isNat_realSqrt_of_isRat_negOfNat`

English:
lemma isNat_realSqrt_of_isRat_negOfNat
  statement: {x : Real} {num : Nat} {denom : Nat}
  proof: by
  refine ⟨?_⟩
  obtain ⟨inv, rfl⟩ := h
  have h₁ : 0 <= (num : Rat) * ⅟(denom : Real) :=
    mul_nonneg (Nat.cast_nonneg' _) (invOf_nonneg.2 <| Nat.cast_nonneg' _)
  simpa [Nat.cast_zero, Real.sqrt_eq_zero', Int.cast_negOfNat, neg_mul, neg_nonpos] using h₁

中文:
引理 is自然数_realSqrt_of_isRat_negOf自然数
  结论: {x : 实数} {num : 自然数} {denom : 自然数}
  证明: by
  refine ⟨?_⟩
  obtain ⟨inv, rfl⟩ := h
  have h₁ : 0 <= (num : Rat) * ⅟(denom : Real) :=
    mul_nonneg (Nat.cast_nonneg' _) (invOf_nonneg.2 <| Nat.cast_nonneg' _)
  simpa [Nat.cast_zero, Real.sqrt_eq_zero', Int.cast_negOfNat, neg_mul, neg_nonpos] using h₁

Depends on / 依赖: Int.cast_negOfNat, Nat.cast_nonneg, Nat.cast_zero, Real.sqrt_eq_zero, cast_negOfNat, cast_nonneg, cast_zero, invOf_nonneg, mul_nonneg, neg_mul, neg_nonpos, sqrt_eq_zero
-/
lemma isNat_realSqrt_of_isRat_negOfNat {x : Real} {num : Nat} {denom : Nat}
    (h : IsRat x (.negOfNat num) denom) : IsNat √x (nat_lit 0) := by
  refine ⟨?_⟩
  obtain ⟨inv, rfl⟩ := h
  have h₁ : 0 <= (num : Rat) * ⅟(denom : Real) :=
    mul_nonneg (Nat.cast_nonneg' _) (invOf_nonneg.2 <| Nat.cast_nonneg' _)
  simpa [Nat.cast_zero, Real.sqrt_eq_zero', Int.cast_negOfNat, neg_mul, neg_nonpos] using h₁

/--
lemma `isNNRat_realSqrt_of_isNNRat` / 引理 `isNNRat_realSqrt_of_isNNRat`

English:
lemma isNNRat_realSqrt_of_isNNRat
  statement: {x : Real} {n sn : Nat} {d sd : Nat} (hn : sn * sn = n)
  proof: by
  obtain ⟨_, rfl⟩ := h
  refine ⟨?_, ?out⟩
  · apply invertibleOfNonzero
    rw [← mul_self_ne_zero]; rw [← Nat.cast_mul]; rw [hd]
    exact Invertible.ne_zero _
  · simp [← hn, ← hd, Real.sqrt_mul (mul_self_nonneg ↑sn)]

中文:
引理 isNNRat_realSqrt_of_isNNRat
  结论: {x : 实数} {n sn : 自然数} {d sd : 自然数} (hn : sn * sn = n)
  证明: by
  obtain ⟨_, rfl⟩ := h
  refine ⟨?_, ?out⟩
  · apply invertibleOfNonzero
    rw [← mul_self_ne_zero]; rw [← Nat.cast_mul]; rw [hd]
    exact Invertible.ne_zero _
  · simp [← hn, ← hd, Real.sqrt_mul (mul_self_nonneg ↑sn)]

Depends on / 依赖: Invertible, Invertible.ne_zero, Nat.cast_mul, Real.sqrt_mul, cast_mul, invertibleOfNonzero, mul_self_ne_zero, mul_self_nonneg, ne_zero, sqrt_mul
-/
lemma isNNRat_realSqrt_of_isNNRat {x : Real} {n sn : Nat} {d sd : Nat} (hn : sn * sn = n)
    (hd : sd * sd = d) (h : IsNNRat x n d) :
    IsNNRat √x sn sd := by
  obtain ⟨_, rfl⟩ := h
  refine ⟨?_, ?out⟩
  · apply invertibleOfNonzero
    rw [← mul_self_ne_zero]; rw [← Nat.cast_mul]; rw [hd]
    exact Invertible.ne_zero _
  · simp [← hn, ← hd, Real.sqrt_mul (mul_self_nonneg ↑sn)]

/-- `norm_num` extension that evaluates the function `Real.sqrt`. -/
@[norm_num √_]
/--
Definition of `evalRealSqrt` / `evalRealSqrt` 的定义

English:
definition evalRealSqrt
  signature: : NormNumExt where eval {u α} e
  body: do
  match u, α, e with
  | 0, ~q(Real), ~q(√$x) =>
    match ← derive x with
    | .isBool _ _ => failure
    | .isNat sReal ex pf =>
        let x := ex.natLit!
        let y := Nat.sqrt x
        unless y * y = x do failure
        have ey : Q(Nat) := mkRawNatLit y
        have pf₁ : Q($ey * $ey 

中文:
定义 eval实数Sqrt
  签名: : NormNumExt where eval {u α} e
  定义体: do
  match u, α, e with
  | 0, ~q(Real), ~q(√$x) =>
    match ← derive x with
    | .isBool _ _ => failure
    | .isNat sReal ex pf =>
        let x := ex.natLit!
        let y := Nat.sqrt x
        unless y * y = x do failure
        have ey : Q(Nat) := mkRawNatLit y
        have pf₁ : Q($ey * $ey 
-/
def evalRealSqrt : NormNumExt where eval {u α} e := do
  match u, α, e with
  | 0, ~q(Real), ~q(√$x) =>
    match ← derive x with
    | .isBool _ _ => failure
    | .isNat sReal ex pf =>
        let x := ex.natLit!
        let y := Nat.sqrt x
        unless y * y = x do failure
        have ey : Q(Nat) := mkRawNatLit y
        have pf₁ : Q($ey * $ey = $ex) := (q(Eq.refl $ex) : Expr)
        assumeInstancesCommute
        return .isNat q($sReal) q($ey) q(isNat_realSqrt $pf $pf₁)
    | .isNegNat _ ex pf =>
        -- Recall that `Real.sqrt` returns 0 for negative inputs
        assumeInstancesCommute
        return .isNat q(inferInstance) q(nat_lit 0) q(isNat_realSqrt_neg $pf)
    | .isNegNNRat sReal eq n ed pf =>
        assumeInstancesCommute
        return .isNat q(inferInstance) q(nat_lit 0) q(isNat_realSqrt_of_isRat_negOfNat $pf)
    | .isNNRat sReal eq n' ed pf =>
          let n : Nat := n'.natLit!
          let d : Nat := ed.natLit!
          let sn := Nat.sqrt n
          let sd := Nat.sqrt d
          unless sn * sn = n ∧ sd * sd = d do failure
          have esn : Q(Nat) := mkRawNatLit sn
          have esd : Q(Nat) := mkRawNatLit sd
          have hn : Q($esn * $esn = $n') := (q(Eq.refl $n') : Expr)
          have hd : Q($esd * $esd = $ed) := (q(Eq.refl $ed) : Expr)
          assumeInstancesCommute
          -- will never be an integer
          return .isNNRat q($sReal) (sn / sd) _ q($esd) q(isNNRat_realSqrt_of_isNNRat $hn $hd $pf)
  | _ => failure

/-- `norm_num` extension that evaluates the function `NNReal.sqrt`. -/
@[norm_num NNReal.sqrt _]
/--
Definition of `evalNNRealSqrt` / `evalNNRealSqrt` 的定义

English:
definition evalNNRealSqrt
  signature: : NormNumExt where eval {u α} e
  body: do
  match u, α, e with
  | 0, ~q(NNReal), ~q(NNReal.sqrt $x) =>
    match ← derive x with
    | .isBool _ _ => failure
    | .isNat sReal ex pf =>
        let x := ex.natLit!
        let y := Nat.sqrt x
        unless y * y = x do failure
        have ey : Q(Nat) := mkRawNatLit y
        have pf₁ :

中文:
定义 evalNN实数Sqrt
  签名: : NormNumExt where eval {u α} e
  定义体: do
  match u, α, e with
  | 0, ~q(NNReal), ~q(NNReal.sqrt $x) =>
    match ← derive x with
    | .isBool _ _ => failure
    | .isNat sReal ex pf =>
        let x := ex.natLit!
        let y := Nat.sqrt x
        unless y * y = x do failure
        have ey : Q(Nat) := mkRawNatLit y
        have pf₁ :
-/
def evalNNRealSqrt : NormNumExt where eval {u α} e := do
  match u, α, e with
  | 0, ~q(NNReal), ~q(NNReal.sqrt $x) =>
    match ← derive x with
    | .isBool _ _ => failure
    | .isNat sReal ex pf =>
        let x := ex.natLit!
        let y := Nat.sqrt x
        unless y * y = x do failure
        have ey : Q(Nat) := mkRawNatLit y
        have pf₁ : Q($ey * $ey = $ex) := (q(Eq.refl $ex) : Expr)
        assumeInstancesCommute
        return .isNat sReal ey q(isNat_nnrealSqrt $pf $pf₁)
    | .isNegNat _ ex pf => failure
    | .isNNRat sReal eq n' ed pf =>
        let n : Nat := n'.natLit!
        let d : Nat := ed.natLit!
        let sn := Nat.sqrt n
        let sd := Nat.sqrt d
        unless sn * sn = n ∧ sd * sd = d do failure
        have esn : Q(Nat) := mkRawNatLit sn
        have esd : Q(Nat) := mkRawNatLit sd
        have hn : Q($esn * $esn = $n') := (q(Eq.refl $n') : Expr)
        have hd : Q($esd * $esd = $ed) := (q(Eq.refl $ed) : Expr)
        assumeInstancesCommute
        -- will never be an integer
        return .isNNRat q($sReal) (sn / sd) _ q($esd) q(isNNRat_nnrealSqrt_of_isNNRat $hn $hd $pf)
    | .isNegNNRat sReal eq en ed pf => failure
  | _ => failure

end Mathlib.Meta.NormNum
