/-
Copyright (c) 2025 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/
module

public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Tactic.NormNum.Basic


/-!
# `norm_num` plugin for `abs`

TODO: plugins for `mabs`, `norm`, `nnorm`, and `enorm`.
-/

public meta section

namespace Mathlib.Meta.NormNum

open Lean.Meta Qq

/--
theorem `isNat_abs_nonneg` / 定理 `isNat_abs_nonneg`

English:
theorem isNat_abs_nonneg
  statement: {α : Type*} [Ring α] [Lattice α] [IsOrderedRing α]
  proof: by
  rw [pa.out]; rw [Nat.abs_cast]
  constructor
  rfl

中文:
定理 is自然数_abs_nonneg
  结论: {α : 类型} [环 α] [格 α] [是Ordered环 α]
  证明: by
  rw [pa.out]; rw [Nat.abs_cast]
  constructor
  rfl

Depends on / 依赖: Nat.abs_cast, abs_cast, pa.out
-/
theorem isNat_abs_nonneg {α : Type*} [Ring α] [Lattice α] [IsOrderedRing α]
    {a : α} {na : Nat} (pa : IsNat a na) : IsNat |a| na := by
  rw [pa.out]; rw [Nat.abs_cast]
  constructor
  rfl

/--
theorem `isNat_abs_neg` / 定理 `isNat_abs_neg`

English:
theorem isNat_abs_neg
  statement: {α : Type*} [Ring α] [Lattice α] [IsOrderedRing α]
  proof: by
  rw [pa.out]
  constructor
  simp

中文:
定理 is自然数_abs_neg
  结论: {α : 类型} [环 α] [格 α] [是Ordered环 α]
  证明: by
  rw [pa.out]
  constructor
  simp

Depends on / 依赖: pa.out
-/
theorem isNat_abs_neg {α : Type*} [Ring α] [Lattice α] [IsOrderedRing α]
    {a : α} {na : Nat} (pa : IsInt a (.negOfNat na)) : IsNat |a| na := by
  rw [pa.out]
  constructor
  simp

/--
theorem `isNNRat_abs_nonneg` / 定理 `isNNRat_abs_nonneg`

English:
theorem isNNRat_abs_nonneg
  statement: {α : Type*} [DivisionRing α] [LinearOrder α]
  proof: by
  obtain ⟨ha1, rfl⟩ := ra
  refine ⟨ha1, abs_of_nonneg ?_⟩
  apply mul_nonneg
  · exact Nat.cast_nonneg' num
  · simp only [invOf_eq_inv, inv_nonneg, Nat.cast_nonneg]

中文:
定理 isNNRat_abs_nonneg
  结论: {α : 类型} [除环 α] [线性序 α]
  证明: by
  obtain ⟨ha1, rfl⟩ := ra
  refine ⟨ha1, abs_of_nonneg ?_⟩
  apply mul_nonneg
  · exact Nat.cast_nonneg' num
  · simp only [invOf_eq_inv, inv_nonneg, Nat.cast_nonneg]

Depends on / 依赖: Nat.cast_nonneg, abs_of_nonneg, cast_nonneg, invOf_eq_inv, inv_nonneg, mul_nonneg
-/
theorem isNNRat_abs_nonneg {α : Type*} [DivisionRing α] [LinearOrder α]
    [IsStrictOrderedRing α] {a : α} {num den : Nat} (ra : IsNNRat a num den) :
    IsNNRat |a| num den := by
  obtain ⟨ha1, rfl⟩ := ra
  refine ⟨ha1, abs_of_nonneg ?_⟩
  apply mul_nonneg
  · exact Nat.cast_nonneg' num
  · simp only [invOf_eq_inv, inv_nonneg, Nat.cast_nonneg]

/--
theorem `isNNRat_abs_neg` / 定理 `isNNRat_abs_neg`

English:
theorem isNNRat_abs_neg
  statement: {α : Type*} [DivisionRing α] [LinearOrder α] [IsStrictOrderedRing α]
  proof: by
  obtain ⟨ha1, rfl⟩ := ra
  simp only [Int.cast_negOfNat, neg_mul, abs_neg]
  refine ⟨ha1, abs_of_nonneg ?_⟩
  apply mul_nonneg
  · exact Nat.cast_nonneg' num
  · simp only [invOf_eq_inv, inv_nonneg, Nat.cast_nonneg]

中文:
定理 isNNRat_abs_neg
  结论: {α : 类型} [除环 α] [线性序 α] [是StrictOrdered环 α]
  证明: by
  obtain ⟨ha1, rfl⟩ := ra
  simp only [Int.cast_negOfNat, neg_mul, abs_neg]
  refine ⟨ha1, abs_of_nonneg ?_⟩
  apply mul_nonneg
  · exact Nat.cast_nonneg' num
  · simp only [invOf_eq_inv, inv_nonneg, Nat.cast_nonneg]

Depends on / 依赖: Int.cast_negOfNat, Nat.cast_nonneg, abs_neg, abs_of_nonneg, cast_negOfNat, cast_nonneg, invOf_eq_inv, inv_nonneg, mul_nonneg, neg_mul
-/
theorem isNNRat_abs_neg {α : Type*} [DivisionRing α] [LinearOrder α] [IsStrictOrderedRing α]
    {a : α} {num den : Nat} (ra : IsRat a (.negOfNat num) den) : IsNNRat |a| num den := by
  obtain ⟨ha1, rfl⟩ := ra
  simp only [Int.cast_negOfNat, neg_mul, abs_neg]
  refine ⟨ha1, abs_of_nonneg ?_⟩
  apply mul_nonneg
  · exact Nat.cast_nonneg' num
  · simp only [invOf_eq_inv, inv_nonneg, Nat.cast_nonneg]

/--
Definition of `evalAbs` / `evalAbs` 的定义

English:
definition evalAbs
  signature: : NormNumExt where eval {u α}

中文:
定义 evalAbs
  签名: : NormNumExt where eval {u α}
-/
@[norm_num |_|] def evalAbs : NormNumExt where eval {u α}
  | ~q(@abs _ $instLattice $instAddGroup $a) => do
    match ← derive a with
    | .isBool .. => failure
    | .isNat sα na pa =>
      let rα : Q(Ring $α) ← synthInstanceQ q(Ring $α)
      let iorα : Q(IsOrderedRing $α) ← synthInstanceQ q(IsOrderedRing $α)
      assumeInstancesCommute
      return .isNat sα na q(isNat_abs_nonneg $pa)
    | .isNegNat sα na pa =>
      let rα : Q(Ring $α) ← synthInstanceQ q(Ring $α)
      let iorα : Q(IsOrderedRing $α) ← synthInstanceQ q(IsOrderedRing $α)
      assumeInstancesCommute
      return .isNat _ _ q(isNat_abs_neg $pa)
    | .isNNRat dsα' qe' nume' dene' pe' =>
      let rα : Q(DivisionRing $α) ← synthInstanceQ q(DivisionRing $α)
      let loα : Q(LinearOrder $α) ← synthInstanceQ q(LinearOrder $α)
      let isorα : Q(IsStrictOrderedRing $α) ← synthInstanceQ q(IsStrictOrderedRing $α)
      assumeInstancesCommute
      return .isNNRat _ qe' _ _ q(isNNRat_abs_nonneg $pe')
    | .isNegNNRat dα' qe' nume' dene' pe' =>
      let loα : Q(LinearOrder $α) ← synthInstanceQ q(LinearOrder $α)
      let isorα : Q(IsStrictOrderedRing $α) ← synthInstanceQ q(IsStrictOrderedRing $α)
      assumeInstancesCommute
      return .isNNRat _ (-qe') _ _ q(isNNRat_abs_neg $pe')

end Mathlib.Meta.NormNum
