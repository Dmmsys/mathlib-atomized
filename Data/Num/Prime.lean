/-
Copyright (c) 2020 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Num.ZNum
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow

/-!
# Primality for binary natural numbers

This file defines versions of `Nat.minFac` and `Nat.Prime` for `Num` and `PosNum`. As with other
`Num` definitions, they are not intended for general use (`Nat` should be used instead of `Num` in
most cases) but they can be used in contexts where kernel computation is required, such as proofs
by `rfl` and `decide`, as well as in `#reduce`.

The default decidable instance for `Nat.Prime` is optimized for VM evaluation, so it should be
preferred within `#eval` or in tactic execution, while for proofs the `norm_num` tactic can be used
to construct primality and non-primality proofs more efficiently than kernel computation.

Nevertheless, sometimes proof by computational reflection requires natural number computations, and
`Num` implements algorithms directly on binary natural numbers for this purpose.
-/

@[expose] public section


namespace PosNum

/--
Definition of `minFacAux` / `minFacAux` 的定义

English:
definition minFacAux
  signature: (n : PosNum)

中文:
定义 minFacAux
  签名: (n : PosNum)
-/
def minFacAux (n : PosNum) : Nat -> PosNum -> PosNum
  | 0, _ => n
  | fuel + 1, k =>
    if n < k.bit1 * k.bit1 then n else if k.bit1 ∣ n then k.bit1 else minFacAux n fuel k.succ

/--
theorem `minFacAux_to_nat` / 定理 `minFacAux_to_nat`

English:
theorem minFacAux_to_nat
  given: {fuel : Nat} {n k : PosNum} (h : Nat.sqrt n < fuel + k.bit1)
  proof: by
  induction fuel generalizing k <;> rw [minFacAux, Nat.minFacAux]
  case zero =>
    rw [Nat.zero_add]; rw [Nat.sqrt_lt] at h
    simp only [h, ite_true]
  case succ fuel ih =>
    simp_rw [← mul_to_nat]
    simp only [cast_lt, dvd_to_nat]
    split_ifs <;> try rfl
    rw [ih] <;> [congr; convert! Nat.lt_succ_of_lt h using 1] <;>
      simp only [cast_bit1, cast_succ, Nat.succ_eq_add_one, add_assoc,
        add_left_comm, ← one_add_one_eq_two]

中文:
定理 minFacAux_to_nat
  条件: {fuel : 自然数} {n k : PosNum} (h : 自然数.sqrt n < fuel + k.bit1)
  证明: by
  induction fuel generalizing k <;> rw [minFacAux, Nat.minFacAux]
  case zero =>
    rw [Nat.zero_add]; rw [Nat.sqrt_lt] at h
    simp only [h, ite_true]
  case succ fuel ih =>
    simp_rw [← mul_to_nat]
    simp only [cast_lt, dvd_to_nat]
    split_ifs <;> try rfl
    rw [ih] <;> [congr; convert! Nat.lt_succ_of_lt h using 1] <;>
      simp only [cast_bit1, cast_succ, Nat.succ_eq_add_one, add_assoc,
        add_left_comm, ← one_add_one_eq_two]

Depends on / 依赖: Nat.lt_succ_of_lt, Nat.minFacAux, Nat.sqrt_lt, Nat.succ_eq_add_one, Nat.zero_add, add_assoc, add_left_comm, cast_bit1, cast_lt, cast_succ, convert, dvd_to_nat, generalizing, ite_true, lt_succ_of_lt, minFacAux, mul_to_nat, one_add_one_eq_two, simp_rw, split_ifs
-/
theorem minFacAux_to_nat {fuel : Nat} {n k : PosNum} (h : Nat.sqrt n < fuel + k.bit1) :
    (minFacAux n fuel k : Nat) = Nat.minFacAux n k.bit1 := by
  induction fuel generalizing k <;> rw [minFacAux, Nat.minFacAux]
  case zero =>
    rw [Nat.zero_add]; rw [Nat.sqrt_lt] at h
    simp only [h, ite_true]
  case succ fuel ih =>
    simp_rw [← mul_to_nat]
    simp only [cast_lt, dvd_to_nat]
    split_ifs <;> try rfl
    rw [ih] <;> [congr; convert! Nat.lt_succ_of_lt h using 1] <;>
      simp only [cast_bit1, cast_succ, Nat.succ_eq_add_one, add_assoc,
        add_left_comm, ← one_add_one_eq_two]

/--
Definition of `minFac` / `minFac` 的定义

English:
definition minFac
  signature: : PosNum -> PosNum

中文:
定义 minFac
  签名: : PosNum -> PosNum
-/
def minFac : PosNum -> PosNum
  | 1 => 1
  | bit0 _ => 2
  | bit1 n => minFacAux (bit1 n) n 1

@[simp]
/--
theorem `minFac_to_nat` / 定理 `minFac_to_nat`

English:
theorem minFac_to_nat
  given: (n : PosNum)
  statement: (minFac n : Nat) = Nat.minFac n
  proof: by
  obtain - | n := n
  · simp [minFac]
  · rw [minFac, Nat.minFac_eq, if_neg]
    swap
    · simp [← two_mul]
    rw [minFacAux_to_nat]
    · rfl
    simp only [cast_one, cast_bit1]
    rw [Nat.sqrt_lt]
    calc
      (n : Nat) + (n : Nat) + 1 <= (n : Nat) + (n : Nat) + (n : Nat) := by simp
      _ = (n : Nat) * (1 + 1 + 1) := by simp only [mul_add, mul_one]
      _ < _ := by simp [mul_lt_mul]
  · rw [minFac, Nat.minFac_eq, if_pos]
    · rfl
    simp [← two_mul]

中文:
定理 minFac_to_nat
  条件: (n : PosNum)
  结论: (minFac n : 自然数) = 自然数.minFac n
  证明: by
  obtain - | n := n
  · simp [minFac]
  · rw [minFac, Nat.minFac_eq, if_neg]
    swap
    · simp [← two_mul]
    rw [minFacAux_to_nat]
    · rfl
    simp only [cast_one, cast_bit1]
    rw [Nat.sqrt_lt]
    calc
      (n : Nat) + (n : Nat) + 1 <= (n : Nat) + (n : Nat) + (n : Nat) := by simp
      _ = (n : Nat) * (1 + 1 + 1) := by simp only [mul_add, mul_one]
      _ < _ := by simp [mul_lt_mul]
  · rw [minFac, Nat.minFac_eq, if_pos]
    · rfl
    simp [← two_mul]

Depends on / 依赖: Nat.minFac_eq, Nat.sqrt_lt, cast_bit1, cast_one, if_neg, if_pos, minFac, minFacAux_to_nat, minFac_eq, mul_add, mul_lt_mul, mul_one, sqrt_lt, two_mul
-/
theorem minFac_to_nat (n : PosNum) : (minFac n : Nat) = Nat.minFac n := by
  obtain - | n := n
  · simp [minFac]
  · rw [minFac, Nat.minFac_eq, if_neg]
    swap
    · simp [← two_mul]
    rw [minFacAux_to_nat]
    · rfl
    simp only [cast_one, cast_bit1]
    rw [Nat.sqrt_lt]
    calc
      (n : Nat) + (n : Nat) + 1 <= (n : Nat) + (n : Nat) + (n : Nat) := by simp
      _ = (n : Nat) * (1 + 1 + 1) := by simp only [mul_add, mul_one]
      _ < _ := by simp [mul_lt_mul]
  · rw [minFac, Nat.minFac_eq, if_pos]
    · rfl
    simp [← two_mul]

/-- Primality predicate for a `PosNum`. -/
@[simp]
/--
Definition of `Prime` / `Prime` 的定义

English:
definition Prime
  signature: (n : PosNum)
  body: Nat.Prime n

中文:
定义 素
  签名: (n : PosNum)
  定义体: Nat.Prime n

Depends on / 依赖: Nat.Prime
-/
def Prime (n : PosNum) : Prop :=
  Nat.Prime n

/--
Instance `decidablePrime` / 实例 `decidablePrime`

English:
instance decidablePrime
  signature: : DecidablePred PosNum.Prime
  body: to_nat_pos n
          lia
        rw [← minFac_to_nat]; rw [to_nat_inj]; rfl

中文:
实例 decidablePrime
  签名: : DecidablePred PosNum.素
  定义体: to_nat_pos n
          lia
        rw [← minFac_to_nat]; rw [to_nat_inj]; rfl

Depends on / 依赖: to_nat_pos
-/
instance decidablePrime : DecidablePred PosNum.Prime
  | 1 => Decidable.isFalse Nat.not_prime_one
  | bit0 n =>
    decidable_of_iff' (n = 1)
      (by
        refine Nat.prime_def_minFac.trans ((and_iff_right ?_).trans <| eq_comm.trans ?_)
        · exact add_le_add (Nat.succ_le_of_lt (to_nat_pos _)) (Nat.succ_le_of_lt (to_nat_pos _))
        rw [← minFac_to_nat]; rw [to_nat_inj]
        exact ⟨bit0.inj, congr_arg _⟩)
  | bit1 n =>
decidable_of_iff' (minFacAux (bit1 n) n 1 = bit1 n) by
        refine Nat.prime_def_minFac.trans ((and_iff_right ?_).trans ?_)
        · simp only [cast_bit1]
          have := to_nat_pos n
          lia
        rw [← minFac_to_nat]; rw [to_nat_inj]; rfl

end PosNum

namespace Num

/--
Definition of `minFac` / `minFac` 的定义

English:
definition minFac
  signature: : Num -> PosNum

中文:
定义 minFac
  签名: : Num -> PosNum
-/
def minFac : Num -> PosNum
  | 0 => 2
  | pos n => n.minFac

@[simp]
/--
theorem `minFac_to_nat` / 定理 `minFac_to_nat`

English:
theorem minFac_to_nat
  statement: forall n : Num, (minFac n : Nat) = Nat.minFac n

中文:
定理 minFac_to_nat
  结论: 对任意 n : Num, (minFac n : 自然数) = 自然数.minFac n
-/
theorem minFac_to_nat : forall n : Num, (minFac n : Nat) = Nat.minFac n
  | 0 => rfl
  | pos _ => PosNum.minFac_to_nat _

/-- Primality predicate for a `Num`. -/
@[simp]
/--
Definition of `Prime` / `Prime` 的定义

English:
definition Prime
  signature: (n : Num)
  body: Nat.Prime n

中文:
定义 素
  签名: (n : Num)
  定义体: Nat.Prime n

Depends on / 依赖: Nat.Prime
-/
def Prime (n : Num) : Prop :=
  Nat.Prime n

/--
Instance `decidablePrime` / 实例 `decidablePrime`

English:
instance decidablePrime
  signature: : DecidablePred Num.Prime

中文:
实例 decidablePrime
  签名: : DecidablePred Num.素
-/
instance decidablePrime : DecidablePred Num.Prime
  | 0 => Decidable.isFalse Nat.not_prime_zero
  | pos n => PosNum.decidablePrime n

end Num
