/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Gabriel Ebner
-/
module

public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Data.Nat.Basic

/-!
# Cast of integers (additional theorems)

This file proves additional properties about the *canonical* homomorphism from
the integers into an additive group with a one (`Int.cast`).

There is also `Mathlib.Data.Int.Cast.Lemmas`,
which includes lemmas stated in terms of algebraic homomorphisms,
and results involving the order structure of `ℤ`.

By contrast, this file's only import beyond `Mathlib.Data.Int.Cast.Defs` is
`Mathlib.Algebra.Group.Basic`.
-/

public section


universe u

namespace Nat

variable {R : Type u} [AddGroupWithOne R]

@[simp, norm_cast]
/--
theorem `cast_sub` / 定理 `cast_sub`

English:
theorem cast_sub
  given: {m n} (h : m <= n)
  statement: ((n - m : Nat) : R) = n - m
  proof: eq_sub_of_add_eq by rw [← cast_add, Nat.sub_add_cancel h]

@[simp, norm_cast]

中文:
定理 cast_sub
  条件: {m n} (h : m <= n)
  结论: ((n - m : 自然数) : R) = n - m
  证明: eq_sub_of_add_eq by rw [← cast_add, Nat.sub_add_cancel h]

@[simp, norm_cast]

Depends on / 依赖: Nat.sub_add_cancel, cast_add, eq_sub_of_add_eq, sub_add_cancel
-/
theorem cast_sub {m n} (h : m <= n) : ((n - m : Nat) : R) = n - m :=
eq_sub_of_add_eq by rw [← cast_add, Nat.sub_add_cancel h]

@[simp, norm_cast]
/--
theorem `cast_pred` / 定理 `cast_pred`

English:
theorem cast_pred
  statement: forall {n}, 0 < n -> ((n - 1 : Nat) : R) = n - 1

中文:
定理 cast_pred
  结论: 对任意 {n}, 0 < n -> ((n - 1 : 自然数) : R) = n - 1
-/
theorem cast_pred : forall {n}, 0 < n -> ((n - 1 : Nat) : R) = n - 1
  | 0, h => by cases h
  | n + 1, _ => by rw [cast_succ, add_sub_cancel_right, Nat.add_sub_cancel_right]

end Nat

open Nat

namespace Int

variable {R : Type u}

@[simp, norm_cast]
/--
theorem `cast_ite` / 定理 `cast_ite`

English:
theorem cast_ite
  given: [IntCast R] (P : Prop) [Decidable P] (m n : Int)
  proof: apply_ite _ _ _ _

中文:
定理 cast_ite
  条件: [整数嵌入 R] (P : 命题) [可判定 P] (m n : 整数)
  证明: apply_ite _ _ _ _

Depends on / 依赖: apply_ite
-/
theorem cast_ite [IntCast R] (P : Prop) [Decidable P] (m n : Int) :
    ((ite P m n : Int) : R) = ite P (m : R) (n : R) :=
  apply_ite _ _ _ _

variable [AddGroupWithOne R]

-- TODO: I don't like that `norm_cast` is used here, because it results in `norm_cast`
-- introducing the "implementation detail" `Int.negSucc`.
@[simp, norm_cast squash]
/--
theorem `cast_negSucc` / 定理 `cast_negSucc`

English:
theorem cast_negSucc
  given: (n : Nat)
  statement: (-[n+1] : R) = -(n + 1 : Nat)
  proof: AddGroupWithOne.intCast_negSucc n

@[simp, norm_cast]

中文:
定理 cast_negSucc
  条件: (n : 自然数)
  结论: (-[n+1] : R) = -(n + 1 : 自然数)
  证明: AddGroupWithOne.intCast_negSucc n

@[simp, norm_cast]

Depends on / 依赖: AddGroupWithOne, AddGroupWithOne.intCast_negSucc, intCast_negSucc
-/
theorem cast_negSucc (n : Nat) : (-[n+1] : R) = -(n + 1 : Nat) :=
  AddGroupWithOne.intCast_negSucc n

@[simp, norm_cast]
/--
theorem `cast_zero` / 定理 `cast_zero`

English:
theorem cast_zero
  statement: ((0 : Int) : R) = 0
  proof: (AddGroupWithOne.intCast_ofNat 0).trans Nat.cast_zero

中文:
定理 cast_zero
  结论: ((0 : 整数) : R) = 0
  证明: (AddGroupWithOne.intCast_ofNat 0).trans Nat.cast_zero

Depends on / 依赖: AddGroupWithOne, AddGroupWithOne.intCast_ofNat, Nat.cast_zero, cast_zero, intCast_ofNat
-/
theorem cast_zero : ((0 : Int) : R) = 0 :=
  (AddGroupWithOne.intCast_ofNat 0).trans Nat.cast_zero

-- This lemma competes with `Int.ofNat_eq_natCast` to come later
@[simp high, norm_cast]
/--
theorem `cast_natCast` / 定理 `cast_natCast`

English:
theorem cast_natCast
  given: (n : Nat)
  statement: ((n : Int) : R) = n
  proof: AddGroupWithOne.intCast_ofNat _

@[simp, norm_cast]

中文:
定理 cast_natCast
  条件: (n : 自然数)
  结论: ((n : 整数) : R) = n
  证明: AddGroupWithOne.intCast_ofNat _

@[simp, norm_cast]

Depends on / 依赖: AddGroupWithOne, AddGroupWithOne.intCast_ofNat, intCast_ofNat
-/
theorem cast_natCast (n : Nat) : ((n : Int) : R) = n :=
  AddGroupWithOne.intCast_ofNat _

@[simp, norm_cast]
/--
theorem `cast_ofNat` / 定理 `cast_ofNat`

English:
theorem cast_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  proof: by
  simpa only [OfNat.ofNat] using! AddGroupWithOne.intCast_ofNat (R := R) n

@[simp, norm_cast]

中文:
定理 cast_of自然数
  条件: (n : 自然数) [n.AtLeastTwo]
  证明: by
  simpa only [OfNat.ofNat] using! AddGroupWithOne.intCast_ofNat (R := R) n

@[simp, norm_cast]

Depends on / 依赖: AddGroupWithOne, AddGroupWithOne.intCast_ofNat, OfNat.ofNat, intCast_ofNat
-/
theorem cast_ofNat (n : Nat) [n.AtLeastTwo] :
    ((ofNat(n) : Int) : R) = ofNat(n) := by
  simpa only [OfNat.ofNat] using! AddGroupWithOne.intCast_ofNat (R := R) n

@[simp, norm_cast]
/--
theorem `cast_one` / 定理 `cast_one`

English:
theorem cast_one
  statement: ((1 : Int) : R) = 1
  proof: by
  rw [← Int.natCast_one]; rw [cast_natCast]; rw [Nat.cast_one]

@[simp, norm_cast]

中文:
定理 cast_one
  结论: ((1 : 整数) : R) = 1
  证明: by
  rw [← Int.natCast_one]; rw [cast_natCast]; rw [Nat.cast_one]

@[simp, norm_cast]

Depends on / 依赖: Int.natCast_one, Nat.cast_one, cast_natCast, cast_one, natCast_one
-/
theorem cast_one : ((1 : Int) : R) = 1 := by
  rw [← Int.natCast_one]; rw [cast_natCast]; rw [Nat.cast_one]

@[simp, norm_cast]
/--
theorem `cast_neg` / 定理 `cast_neg`

English:
theorem cast_neg
  statement: forall n, ((-n : Int) : R) = -n

中文:
定理 cast_neg
  结论: 对任意 n, ((-n : 整数) : R) = -n
-/
theorem cast_neg : forall n, ((-n : Int) : R) = -n
  | (0 : Nat) => by simp
  | (n + 1 : Nat) => by rw [cast_natCast, neg_ofNat_succ]; simp
  | -[n+1] => by rw [Int.neg_negSucc, cast_natCast]; simp

@[simp, norm_cast]
/--
theorem `cast_subNatNat` / 定理 `cast_subNatNat`

English:
theorem cast_subNatNat
  given: (m n)
  statement: ((Int.subNatNat m n : Int) : R) = m - n
  proof: by
  unfold subNatNat
  cases e : n - m
  · simp [Nat.le_of_sub_eq_zero e]
  · rw [cast_negSucc, ← e, Nat.cast_sub <| _root_.le_of_lt <| Nat.lt_of_sub_eq_succ e, neg_sub]

@[simp]

中文:
定理 cast_sub自然数自然数
  条件: (m n)
  结论: ((整数.sub自然数自然数 m n : 整数) : R) = m - n
  证明: by
  unfold subNatNat
  cases e : n - m
  · simp [Nat.le_of_sub_eq_zero e]
  · rw [cast_negSucc, ← e, Nat.cast_sub <| _root_.le_of_lt <| Nat.lt_of_sub_eq_succ e, neg_sub]

@[simp]

Depends on / 依赖: Nat.cast_sub, Nat.le_of_sub_eq_zero, Nat.lt_of_sub_eq_succ, _root_, _root_.le_of_lt, cast_negSucc, cast_sub, le_of_lt, le_of_sub_eq_zero, lt_of_sub_eq_succ, neg_sub, subNatNat
-/
theorem cast_subNatNat (m n) : ((Int.subNatNat m n : Int) : R) = m - n := by
  unfold subNatNat
  cases e : n - m
  · simp [Nat.le_of_sub_eq_zero e]
  · rw [cast_negSucc, ← e, Nat.cast_sub <| _root_.le_of_lt <| Nat.lt_of_sub_eq_succ e, neg_sub]

@[simp]
/--
theorem `cast_negOfNat` / 定理 `cast_negOfNat`

English:
theorem cast_negOfNat
  given: (n : Nat)
  statement: ((negOfNat n : Int) : R) = -n
  proof: by simp [Int.cast_neg, negOfNat_eq]

@[simp, norm_cast]

中文:
定理 cast_negOf自然数
  条件: (n : 自然数)
  结论: ((negOf自然数 n : 整数) : R) = -n
  证明: by simp [Int.cast_neg, negOfNat_eq]

@[simp, norm_cast]

Depends on / 依赖: Int.cast_neg, cast_neg, negOfNat_eq
-/
theorem cast_negOfNat (n : Nat) : ((negOfNat n : Int) : R) = -n := by simp [Int.cast_neg, negOfNat_eq]

@[simp, norm_cast]
/--
theorem `cast_add` / 定理 `cast_add`

English:
theorem cast_add
  statement: forall m n, ((m + n : Int) : R) = m + n

中文:
定理 cast_add
  结论: 对任意 m n, ((m + n : 整数) : R) = m + n
-/
theorem cast_add : forall m n, ((m + n : Int) : R) = m + n
  | (m : Nat), (n : Nat) => by simp [← Int.natCast_add]
  | (m : Nat), -[n+1] => by
    rw [Int.ofNat_add_negSucc]; rw [cast_subNatNat]; rw [cast_natCast]; rw [cast_negSucc]; rw [sub_eq_add_neg]
  | -[m+1], (n : Nat) => by
    rw [Int.negSucc_add_ofNat]; rw [cast_subNatNat]; rw [cast_natCast]; rw [cast_negSucc]; rw [sub_eq_iff_eq_add]; rw [add_assoc]; rw [eq_neg_add_iff_add_eq]; rw [← Nat.cast_add]; rw [← Nat.cast_add]; rw [Nat.add_comm]
  | -[m+1], -[n+1] => by
    rw [Int.negSucc_add_negSucc]; rw [succ_eq_add_one]; rw [cast_negSucc]; rw [cast_negSucc]; rw [cast_negSucc]; rw [← neg_add_rev]; rw [← Nat.cast_add]; rw [Nat.add_right_comm m n 1]; rw [Nat.add_assoc]; rw [Nat.add_comm]

@[simp, norm_cast]
/--
theorem `cast_sub` / 定理 `cast_sub`

English:
theorem cast_sub
  given: (m n)
  statement: ((m - n : Int) : R) = m - n
  proof: by
  simp [Int.sub_eq_add_neg, sub_eq_add_neg, Int.cast_neg, Int.cast_add]

中文:
定理 cast_sub
  条件: (m n)
  结论: ((m - n : 整数) : R) = m - n
  证明: by
  simp [Int.sub_eq_add_neg, sub_eq_add_neg, Int.cast_neg, Int.cast_add]

Depends on / 依赖: Int.cast_add, Int.cast_neg, Int.sub_eq_add_neg, cast_add, cast_neg, sub_eq_add_neg
-/
theorem cast_sub (m n) : ((m - n : Int) : R) = m - n := by
  simp [Int.sub_eq_add_neg, sub_eq_add_neg, Int.cast_neg, Int.cast_add]

/--
theorem `cast_two` / 定理 `cast_two`

English:
theorem cast_two
  statement: ((2 : Int) : R) = 2
  proof: cast_ofNat _

中文:
定理 cast_two
  结论: ((2 : 整数) : R) = 2
  证明: cast_ofNat _

Depends on / 依赖: cast_ofNat
-/
theorem cast_two : ((2 : Int) : R) = 2 := cast_ofNat _

/--
theorem `cast_three` / 定理 `cast_three`

English:
theorem cast_three
  statement: ((3 : Int) : R) = 3
  proof: cast_ofNat _

中文:
定理 cast_three
  结论: ((3 : 整数) : R) = 3
  证明: cast_ofNat _

Depends on / 依赖: cast_ofNat
-/
theorem cast_three : ((3 : Int) : R) = 3 := cast_ofNat _

/--
theorem `cast_four` / 定理 `cast_four`

English:
theorem cast_four
  statement: ((4 : Int) : R) = 4
  proof: cast_ofNat _

中文:
定理 cast_four
  结论: ((4 : 整数) : R) = 4
  证明: cast_ofNat _

Depends on / 依赖: cast_ofNat
-/
theorem cast_four : ((4 : Int) : R) = 4 := cast_ofNat _

end Int

section zsmul

variable {R : Type*}

/--
lemma `zsmul_one` / 引理 `zsmul_one`

English:
lemma zsmul_one
  given: [AddGroupWithOne R] (n : Int)
  statement: n • (1 : R) = n
  proof: by cases n <;> simp

中文:
引理 zsmul_one
  条件: [加法带幺群 R] (n : 整数)
  结论: n • (1 : R) = n
  证明: by cases n <;> simp
-/
@[simp] lemma zsmul_one [AddGroupWithOne R] (n : Int) : n • (1 : R) = n := by cases n <;> simp

end zsmul
