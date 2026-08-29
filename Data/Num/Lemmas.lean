/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.PSub
public import Mathlib.Data.Nat.Size
public import Mathlib.Data.Num.Bitwise
import all Init.Data.Nat.Bitwise.Basic -- for unfolding `bitwise`

/-!
# Properties of the binary representation of integers
-/

@[expose] public section

open Int

attribute [local simp] add_assoc

namespace PosNum

variable {α : Type*}

@[simp, norm_cast]
/--
theorem `cast_one` / 定理 `cast_one`

English:
theorem cast_one
  given: [One α] [Add α]
  statement: ((1 : PosNum) : α) = 1
  proof: rfl

@[simp]

中文:
定理 cast_one
  条件: [幺 α] [加法 α]
  结论: ((1 : PosNum) : α) = 1
  证明: rfl

@[simp]
-/
theorem cast_one [One α] [Add α] : ((1 : PosNum) : α) = 1 :=
  rfl

@[simp]
/--
theorem `cast_one'` / 定理 `cast_one'`

English:
theorem cast_one'
  given: [One α] [Add α]
  statement: (PosNum.one : α) = 1
  proof: rfl

@[simp, norm_cast]

中文:
定理 cast_one'
  条件: [幺 α] [加法 α]
  结论: (PosNum.one : α) = 1
  证明: rfl

@[simp, norm_cast]
-/
theorem cast_one' [One α] [Add α] : (PosNum.one : α) = 1 :=
  rfl

@[simp, norm_cast]
/--
theorem `cast_bit0` / 定理 `cast_bit0`

English:
theorem cast_bit0
  given: [One α] [Add α] (n : PosNum)
  statement: (n.bit0 : α) = (n : α) + n
  proof: rfl

@[simp, norm_cast]

中文:
定理 cast_bit0
  条件: [幺 α] [加法 α] (n : PosNum)
  结论: (n.bit0 : α) = (n : α) + n
  证明: rfl

@[simp, norm_cast]
-/
theorem cast_bit0 [One α] [Add α] (n : PosNum) : (n.bit0 : α) = (n : α) + n :=
  rfl

@[simp, norm_cast]
/--
theorem `cast_bit1` / 定理 `cast_bit1`

English:
theorem cast_bit1
  given: [One α] [Add α] (n : PosNum)
  statement: (n.bit1 : α) = ((n : α) + n) + 1
  proof: rfl

@[simp, norm_cast]

中文:
定理 cast_bit1
  条件: [幺 α] [加法 α] (n : PosNum)
  结论: (n.bit1 : α) = ((n : α) + n) + 1
  证明: rfl

@[simp, norm_cast]
-/
theorem cast_bit1 [One α] [Add α] (n : PosNum) : (n.bit1 : α) = ((n : α) + n) + 1 :=
  rfl

@[simp, norm_cast]
/--
theorem `cast_to_nat` / 定理 `cast_to_nat`

English:
theorem cast_to_nat
  given: [AddMonoidWithOne α]
  statement: forall n : PosNum, ((n : Nat) : α) = n

中文:
定理 cast_to_nat
  条件: [加法带幺幺半群 α]
  结论: 对任意 n : PosNum, ((n : 自然数) : α) = n
-/
theorem cast_to_nat [AddMonoidWithOne α] : forall n : PosNum, ((n : Nat) : α) = n
  | 1 => Nat.cast_one
  | bit0 p => by dsimp; rw [Nat.cast_add, p.cast_to_nat]
  | bit1 p => by dsimp; rw [Nat.cast_add, Nat.cast_add, Nat.cast_one, p.cast_to_nat]

@[norm_cast]
/--
theorem `to_nat_to_int` / 定理 `to_nat_to_int`

English:
theorem to_nat_to_int
  given: (n : PosNum)
  statement: ((n : Nat) : Int) = n
  proof: cast_to_nat _

@[simp, norm_cast]

中文:
定理 to_nat_to_int
  条件: (n : PosNum)
  结论: ((n : 自然数) : 整数) = n
  证明: cast_to_nat _

@[simp, norm_cast]

Depends on / 依赖: cast_to_nat
-/
theorem to_nat_to_int (n : PosNum) : ((n : Nat) : Int) = n :=
  cast_to_nat _

@[simp, norm_cast]
/--
theorem `cast_to_int` / 定理 `cast_to_int`

English:
theorem cast_to_int
  given: [AddGroupWithOne α] (n : PosNum)
  statement: ((n : Int) : α) = n
  proof: by
  rw [← to_nat_to_int]; rw [Int.cast_natCast]; rw [cast_to_nat]

中文:
定理 cast_to_int
  条件: [加法带幺群 α] (n : PosNum)
  结论: ((n : 整数) : α) = n
  证明: by
  rw [← to_nat_to_int]; rw [Int.cast_natCast]; rw [cast_to_nat]

Depends on / 依赖: Int.cast_natCast, cast_natCast, cast_to_nat, to_nat_to_int
-/
theorem cast_to_int [AddGroupWithOne α] (n : PosNum) : ((n : Int) : α) = n := by
  rw [← to_nat_to_int]; rw [Int.cast_natCast]; rw [cast_to_nat]

/--
theorem `succ_to_nat` / 定理 `succ_to_nat`

English:
theorem succ_to_nat
  statement: forall n, (succ n : Nat) = n + 1

中文:
定理 succ_to_nat
  结论: 对任意 n, (succ n : 自然数) = n + 1
-/
theorem succ_to_nat : forall n, (succ n : Nat) = n + 1
  | 1 => rfl
  | bit0 _ => rfl
  | bit1 p =>
(congr_arg (fun n => n + n) (succ_to_nat p)).trans
      show ↑p + 1 + ↑p + 1 = ↑p + ↑p + 1 + 1 by simp [add_left_comm]

/--
theorem `one_add` / 定理 `one_add`

English:
theorem one_add
  given: (n : PosNum)
  statement: 1 + n = succ n
  proof: by cases n <;> rfl

中文:
定理 one_add
  条件: (n : PosNum)
  结论: 1 + n = succ n
  证明: by cases n <;> rfl
-/
theorem one_add (n : PosNum) : 1 + n = succ n := by cases n <;> rfl

/--
theorem `add_one` / 定理 `add_one`

English:
theorem add_one
  given: (n : PosNum)
  statement: n + 1 = succ n
  proof: by cases n <;> rfl

@[norm_cast]

中文:
定理 add_one
  条件: (n : PosNum)
  结论: n + 1 = succ n
  证明: by cases n <;> rfl

@[norm_cast]
-/
theorem add_one (n : PosNum) : n + 1 = succ n := by cases n <;> rfl

@[norm_cast]
/--
theorem `add_to_nat` / 定理 `add_to_nat`

English:
theorem add_to_nat
  statement: forall m n, ((m + n : PosNum) : Nat) = m + n

中文:
定理 add_to_nat
  结论: 对任意 m n, ((m + n : PosNum) : 自然数) = m + n
-/
theorem add_to_nat : forall m n, ((m + n : PosNum) : Nat) = m + n
  | 1, b => by rw [one_add b, succ_to_nat, add_comm, cast_one]
  | a, 1 => by rw [add_one a, succ_to_nat, cast_one]
| bit0 a, bit0 b => (congr_arg (fun n => n + n) (add_to_nat a b)).trans add_add_add_comm _ _ _ _
  | bit0 a, bit1 b =>
(congr_arg (fun n => (n + n) + 1) (add_to_nat a b)).trans
      show (a + b + (a + b) + 1 : Nat) = a + a + (b + b + 1) by simp [add_left_comm]
  | bit1 a, bit0 b =>
(congr_arg (fun n => (n + n) + 1) (add_to_nat a b)).trans
      show (a + b + (a + b) + 1 : Nat) = a + a + 1 + (b + b) by simp [add_comm, add_left_comm]
  | bit1 a, bit1 b =>
    show (succ (a + b) + succ (a + b) : Nat) = a + a + 1 + (b + b + 1) by
      rw [succ_to_nat]; rw [add_to_nat a b]; simp [add_left_comm]

/--
theorem `add_succ` / 定理 `add_succ`

English:
theorem add_succ
  statement: forall m n : PosNum, m + succ n = succ (m + n)

中文:
定理 add_succ
  结论: 对任意 m n : PosNum, m + succ n = succ (m + n)
-/
theorem add_succ : forall m n : PosNum, m + succ n = succ (m + n)
  | 1, b => by simp [one_add]
  | bit0 a, 1 => congr_arg bit0 (add_one a)
  | bit1 a, 1 => congr_arg bit1 (add_one a)
  | bit0 _, bit0 _ => rfl
  | bit0 a, bit1 b => congr_arg bit0 (add_succ a b)
  | bit1 _, bit0 _ => rfl
  | bit1 a, bit1 b => congr_arg bit1 (add_succ a b)

/--
theorem `bit0_of_bit0` / 定理 `bit0_of_bit0`

English:
theorem bit0_of_bit0
  statement: forall n, n + n = bit0 n

中文:
定理 bit0_of_bit0
  结论: 对任意 n, n + n = bit0 n
-/
theorem bit0_of_bit0 : forall n, n + n = bit0 n
  | 1 => rfl
  | bit0 p => congr_arg bit0 (bit0_of_bit0 p)
  | bit1 p => show bit0 (succ (p + p)) = _ by rw [bit0_of_bit0 p, succ]

/--
theorem `bit1_of_bit1` / 定理 `bit1_of_bit1`

English:
theorem bit1_of_bit1
  given: (n : PosNum)
  statement: (n + n) + 1 = bit1 n
  proof: show (n + n) + 1 = bit1 n by rw [add_one, bit0_of_bit0, succ]

@[norm_cast]

中文:
定理 bit1_of_bit1
  条件: (n : PosNum)
  结论: (n + n) + 1 = bit1 n
  证明: show (n + n) + 1 = bit1 n by rw [add_one, bit0_of_bit0, succ]

@[norm_cast]

Depends on / 依赖: add_one, bit0_of_bit0
-/
theorem bit1_of_bit1 (n : PosNum) : (n + n) + 1 = bit1 n :=
  show (n + n) + 1 = bit1 n by rw [add_one, bit0_of_bit0, succ]

@[norm_cast]
/--
theorem `mul_to_nat` / 定理 `mul_to_nat`

English:
theorem mul_to_nat
  given: (m)
  statement: forall n, ((m * n : PosNum) : Nat) = m * n

中文:
定理 mul_to_nat
  条件: (m)
  结论: 对任意 n, ((m * n : PosNum) : 自然数) = m * n
-/
theorem mul_to_nat (m) : forall n, ((m * n : PosNum) : Nat) = m * n
  | 1 => (mul_one _).symm
  | bit0 p => show (↑(m * p) + ↑(m * p) : Nat) = ↑m * (p + p) by rw [mul_to_nat m p, left_distrib]
  | bit1 p =>
(add_to_nat (bit0 (m * p)) m).trans
      show (↑(m * p) + ↑(m * p) + ↑m : Nat) = ↑m * (p + p) + m by rw [mul_to_nat m p, left_distrib]

/--
theorem `to_nat_pos` / 定理 `to_nat_pos`

English:
theorem to_nat_pos
  statement: forall n : PosNum, 0 < (n : Nat)
  proof: to_nat_pos p
    add_pos h h
  | bit1 _p => Nat.succ_pos _

中文:
定理 to_nat_pos
  结论: 对任意 n : PosNum, 0 < (n : 自然数)
  证明: to_nat_pos p
    add_pos h h
  | bit1 _p => Nat.succ_pos _

Depends on / 依赖: to_nat_pos
-/
theorem to_nat_pos : forall n : PosNum, 0 < (n : Nat)
  | 1 => Nat.zero_lt_one
  | bit0 p =>
    let h := to_nat_pos p
    add_pos h h
  | bit1 _p => Nat.succ_pos _

/--
theorem `cmp_to_nat_lemma` / 定理 `cmp_to_nat_lemma`

English:
theorem cmp_to_nat_lemma
  given: {m n : PosNum}
  statement: (m : Nat) < n -> (bit1 m : Nat) < bit0 n
  proof: show (m : Nat) < n -> (m + m + 1 + 1 : Nat) <= n + n by
    intro h; rw [Nat.add_right_comm m m 1, add_assoc]; exact Nat.add_le_add h h

中文:
定理 cmp_to_nat_lemma
  条件: {m n : PosNum}
  结论: (m : 自然数) < n -> (bit1 m : 自然数) < bit0 n
  证明: show (m : Nat) < n -> (m + m + 1 + 1 : Nat) <= n + n by
    intro h; rw [Nat.add_right_comm m m 1, add_assoc]; exact Nat.add_le_add h h

Depends on / 依赖: Nat.add_le_add, Nat.add_right_comm, add_assoc, add_le_add, add_right_comm
-/
theorem cmp_to_nat_lemma {m n : PosNum} : (m : Nat) < n -> (bit1 m : Nat) < bit0 n :=
  show (m : Nat) < n -> (m + m + 1 + 1 : Nat) <= n + n by
    intro h; rw [Nat.add_right_comm m m 1, add_assoc]; exact Nat.add_le_add h h

/--
theorem `cmp_swap` / 定理 `cmp_swap`

English:
theorem cmp_swap
  given: (m)
  statement: forall n, (cmp m n).swap = cmp n m
  proof: by
  induction m with | one => ?_ | bit1 m IH => ?_ | bit0 m IH => ?_ <;>
    intro n <;> obtain - | n | n := n <;> unfold cmp <;>
      try { rfl } <;> rw [← IH] <;> cases cmp m n <;> rfl

中文:
定理 cmp_swap
  条件: (m)
  结论: 对任意 n, (cmp m n).swap = cmp n m
  证明: by
  induction m with | one => ?_ | bit1 m IH => ?_ | bit0 m IH => ?_ <;>
    intro n <;> obtain - | n | n := n <;> unfold cmp <;>
      try { rfl } <;> rw [← IH] <;> cases cmp m n <;> rfl
-/
theorem cmp_swap (m) : forall n, (cmp m n).swap = cmp n m := by
  induction m with | one => ?_ | bit1 m IH => ?_ | bit0 m IH => ?_ <;>
    intro n <;> obtain - | n | n := n <;> unfold cmp <;>
      try { rfl } <;> rw [← IH] <;> cases cmp m n <;> rfl

/--
theorem `cmp_to_nat` / 定理 `cmp_to_nat`

English:
theorem cmp_to_nat
  statement: forall m n, (Ordering.casesOn (cmp m n) ((m : Nat) < n) (m = n) ((n : Nat) < m) : Prop)
  proof: to_nat_pos a
    Nat.add_le_add h h
| bit1 a, 1 => Nat.succ_lt_succ to_nat_pos bit0 a
  | 1, bit0 b =>
    let h : (1 : Nat) <= b := to_nat_pos b
    Nat.add_le_add h h
| 1, bit1 b => Nat.succ_lt_succ to_nat_pos bit0 b
  | bit0 a, bit0 b => by
    dsimp [cmp]
    have := cmp_to_nat a b; revert this;

中文:
定理 cmp_to_nat
  结论: 对任意 m n, (Ordering.casesOn (cmp m n) ((m : 自然数) < n) (m = n) ((n : 自然数) < m) : 命题)
  证明: to_nat_pos a
    Nat.add_le_add h h
| bit1 a, 1 => Nat.succ_lt_succ to_nat_pos bit0 a
  | 1, bit0 b =>
    let h : (1 : Nat) <= b := to_nat_pos b
    Nat.add_le_add h h
| 1, bit1 b => Nat.succ_lt_succ to_nat_pos bit0 b
  | bit0 a, bit0 b => by
    dsimp [cmp]
    have := cmp_to_nat a b; revert this;

Depends on / 依赖: to_nat_pos
-/
theorem cmp_to_nat : forall m n, (Ordering.casesOn (cmp m n) ((m : Nat) < n) (m = n) ((n : Nat) < m) : Prop)
  | 1, 1 => rfl
  | bit0 a, 1 =>
    let h : (1 : Nat) <= a := to_nat_pos a
    Nat.add_le_add h h
| bit1 a, 1 => Nat.succ_lt_succ to_nat_pos bit0 a
  | 1, bit0 b =>
    let h : (1 : Nat) <= b := to_nat_pos b
    Nat.add_le_add h h
| 1, bit1 b => Nat.succ_lt_succ to_nat_pos bit0 b
  | bit0 a, bit0 b => by
    dsimp [cmp]
    have := cmp_to_nat a b; revert this; cases cmp a b <;> dsimp <;> intro this
    · exact Nat.add_lt_add this this
    · rw [this]
    · exact Nat.add_lt_add this this
  | bit0 a, bit1 b => by
    dsimp [cmp]
    have := cmp_to_nat a b; revert this; cases cmp a b <;> dsimp <;> intro this
    · exact Nat.le_succ_of_le (Nat.add_lt_add this this)
    · rw [this]
      apply Nat.lt_succ_self
    · exact cmp_to_nat_lemma this
  | bit1 a, bit0 b => by
    dsimp [cmp]
    have := cmp_to_nat a b; revert this; cases cmp a b <;> dsimp <;> intro this
    · exact cmp_to_nat_lemma this
    · rw [this]
      apply Nat.lt_succ_self
    · exact Nat.le_succ_of_le (Nat.add_lt_add this this)
  | bit1 a, bit1 b => by
    dsimp [cmp]
    have := cmp_to_nat a b; revert this; cases cmp a b <;> dsimp <;> intro this
    · exact Nat.succ_lt_succ (Nat.add_lt_add this this)
    · rw [this]
    · exact Nat.succ_lt_succ (Nat.add_lt_add this this)

@[norm_cast]
/--
theorem `lt_to_nat` / 定理 `lt_to_nat`

English:
theorem lt_to_nat
  given: {m n : PosNum}
  statement: (m : Nat) < n ↔ m < n
  proof: show (m : Nat) < n ↔ cmp m n = Ordering.lt from
    match cmp m n, cmp_to_nat m n with
    | Ordering.lt, h => by simp [h]
    | Ordering.eq, h => by simp [h]
    | Ordering.gt, h => by simp [not_lt_of_gt h]

@[norm_cast]

中文:
定理 lt_to_nat
  条件: {m n : PosNum}
  结论: (m : 自然数) < n ↔ m < n
  证明: show (m : Nat) < n ↔ cmp m n = Ordering.lt from
    match cmp m n, cmp_to_nat m n with
    | Ordering.lt, h => by simp [h]
    | Ordering.eq, h => by simp [h]
    | Ordering.gt, h => by simp [not_lt_of_gt h]

@[norm_cast]

Depends on / 依赖: Ordering, Ordering.eq, Ordering.gt, Ordering.lt, cmp_to_nat, not_lt_of_gt
-/
theorem lt_to_nat {m n : PosNum} : (m : Nat) < n ↔ m < n :=
  show (m : Nat) < n ↔ cmp m n = Ordering.lt from
    match cmp m n, cmp_to_nat m n with
    | Ordering.lt, h => by simp [h]
    | Ordering.eq, h => by simp [h]
    | Ordering.gt, h => by simp [not_lt_of_gt h]

@[norm_cast]
/--
theorem `le_to_nat` / 定理 `le_to_nat`

English:
theorem le_to_nat
  given: {m n : PosNum}
  statement: (m : Nat) <= n ↔ m <= n
  proof: by
  rw [← not_lt]; exact not_congr lt_to_nat

中文:
定理 le_to_nat
  条件: {m n : PosNum}
  结论: (m : 自然数) <= n ↔ m <= n
  证明: by
  rw [← not_lt]; exact not_congr lt_to_nat

Depends on / 依赖: lt_to_nat, not_congr, not_lt
-/
theorem le_to_nat {m n : PosNum} : (m : Nat) <= n ↔ m <= n := by
  rw [← not_lt]; exact not_congr lt_to_nat

end PosNum

namespace Num

variable {α : Type*}

open PosNum

/--
theorem `add_zero` / 定理 `add_zero`

English:
theorem add_zero
  given: (n : Num)
  statement: n + 0 = n
  proof: by cases n <;> rfl

中文:
定理 add_zero
  条件: (n : Num)
  结论: n + 0 = n
  证明: by cases n <;> rfl
-/
theorem add_zero (n : Num) : n + 0 = n := by cases n <;> rfl

/--
theorem `zero_add` / 定理 `zero_add`

English:
theorem zero_add
  given: (n : Num)
  statement: 0 + n = n
  proof: by cases n <;> rfl

中文:
定理 zero_add
  条件: (n : Num)
  结论: 0 + n = n
  证明: by cases n <;> rfl
-/
theorem zero_add (n : Num) : 0 + n = n := by cases n <;> rfl

/--
theorem `add_one` / 定理 `add_one`

English:
theorem add_one
  statement: forall n : Num, n + 1 = succ n

中文:
定理 add_one
  结论: 对任意 n : Num, n + 1 = succ n
-/
theorem add_one : forall n : Num, n + 1 = succ n
  | 0 => rfl
  | pos p => by cases p <;> rfl

/--
theorem `add_succ` / 定理 `add_succ`

English:
theorem add_succ
  statement: forall m n : Num, m + succ n = succ (m + n)

中文:
定理 add_succ
  结论: 对任意 m n : Num, m + succ n = succ (m + n)
-/
theorem add_succ : forall m n : Num, m + succ n = succ (m + n)
  | 0, n => by simp [zero_add]
  | pos p, 0 => show pos (p + 1) = succ (pos p + 0) by rw [PosNum.add_one, add_zero, succ, succ']
  | pos _, pos _ => congr_arg pos (PosNum.add_succ _ _)

/--
theorem `bit0_of_bit0` / 定理 `bit0_of_bit0`

English:
theorem bit0_of_bit0
  statement: forall n : Num, n + n = n.bit0

中文:
定理 bit0_of_bit0
  结论: 对任意 n : Num, n + n = n.bit0
-/
theorem bit0_of_bit0 : forall n : Num, n + n = n.bit0
  | 0 => rfl
  | pos p => congr_arg pos p.bit0_of_bit0

/--
theorem `bit1_of_bit1` / 定理 `bit1_of_bit1`

English:
theorem bit1_of_bit1
  statement: forall n : Num, (n + n) + 1 = n.bit1

中文:
定理 bit1_of_bit1
  结论: 对任意 n : Num, (n + n) + 1 = n.bit1
-/
theorem bit1_of_bit1 : forall n : Num, (n + n) + 1 = n.bit1
  | 0 => rfl
  | pos p => congr_arg pos p.bit1_of_bit1

@[simp]
/--
theorem `ofNat'_zero` / 定理 `ofNat'_zero`

English:
theorem ofNat'_zero
  statement: Num.ofNat' 0 = 0
  proof: by simp [Num.ofNat']

中文:
定理 of自然数'_zero
  结论: Num.of自然数' 0 = 0
  证明: by simp [Num.ofNat']
-/
theorem ofNat'_zero : Num.ofNat' 0 = 0 := by simp [Num.ofNat']

/--
theorem `ofNat'_bit` / 定理 `ofNat'_bit`

English:
theorem ofNat'_bit
  given: (b n)
  statement: ofNat' (Nat.bit b n) = cond b Num.bit1 Num.bit0 (ofNat' n)
  proof: Nat.binaryRec_eq _ _ (.inl rfl)

@[simp]

中文:
定理 of自然数'_bit
  条件: (b n)
  结论: of自然数' (自然数.bit b n) = cond b Num.bit1 Num.bit0 (of自然数' n)
  证明: Nat.binaryRec_eq _ _ (.inl rfl)

@[simp]
-/
theorem ofNat'_bit (b n) : ofNat' (Nat.bit b n) = cond b Num.bit1 Num.bit0 (ofNat' n) :=
  Nat.binaryRec_eq _ _ (.inl rfl)

@[simp]
/--
theorem `ofNat'_one` / 定理 `ofNat'_one`

English:
theorem ofNat'_one
  statement: Num.ofNat' 1 = 1
  proof: by simp [Num.ofNat', Num.bit1]

中文:
定理 of自然数'_one
  结论: Num.of自然数' 1 = 1
  证明: by simp [Num.ofNat', Num.bit1]
-/
theorem ofNat'_one : Num.ofNat' 1 = 1 := by simp [Num.ofNat', Num.bit1]

/--
theorem `bit1_succ` / 定理 `bit1_succ`

English:
theorem bit1_succ
  statement: forall n : Num, n.bit1.succ = n.succ.bit0

中文:
定理 bit1_succ
  结论: 对任意 n : Num, n.bit1.succ = n.succ.bit0
-/
theorem bit1_succ : forall n : Num, n.bit1.succ = n.succ.bit0
  | 0 => rfl
  | pos _n => rfl

/--
theorem `ofNat'_succ` / 定理 `ofNat'_succ`

English:
theorem ofNat'_succ
  statement: forall {n}, ofNat' (n + 1) = ofNat' n + 1
  proof: @(Nat.binaryRec (by simp [zero_add]) fun b n ih => by
    cases b
    · erw [ofNat'_bit true n, ofNat'_bit]
      simp only [← bit1_of_bit1, ← bit0_of_bit0, cond]
    · rw [show n.bit true + 1 = (n + 1).bit false by simp [Nat.bit, mul_add],
        ofNat'_bit, ofNat'_bit, ih]
      simp only [cond, 

中文:
定理 of自然数'_succ
  结论: 对任意 {n}, of自然数' (n + 1) = of自然数' n + 1
  证明: @(Nat.binaryRec (by simp [zero_add]) fun b n ih => by
    cases b
    · erw [ofNat'_bit true n, ofNat'_bit]
      simp only [← bit1_of_bit1, ← bit0_of_bit0, cond]
    · rw [show n.bit true + 1 = (n + 1).bit false by simp [Nat.bit, mul_add],
        ofNat'_bit, ofNat'_bit, ih]
      simp only [cond, 
-/
theorem ofNat'_succ : forall {n}, ofNat' (n + 1) = ofNat' n + 1 :=
  @(Nat.binaryRec (by simp [zero_add]) fun b n ih => by
    cases b
    · erw [ofNat'_bit true n, ofNat'_bit]
      simp only [← bit1_of_bit1, ← bit0_of_bit0, cond]
    · rw [show n.bit true + 1 = (n + 1).bit false by simp [Nat.bit, mul_add],
        ofNat'_bit, ofNat'_bit, ih]
      simp only [cond, add_one, bit1_succ])

@[simp]
/--
theorem `add_ofNat'` / 定理 `add_ofNat'`

English:
theorem add_ofNat'
  given: (m n)
  statement: Num.ofNat' (m + n) = Num.ofNat' m + Num.ofNat' n
  proof: by
  induction n
  · simp only [Nat.add_zero, ofNat'_zero, add_zero]
  · simp only [Nat.add_succ, Nat.add_zero, ofNat'_succ, add_one, add_succ, *]

@[simp, norm_cast]

中文:
定理 add_of自然数'
  条件: (m n)
  结论: Num.of自然数' (m + n) = Num.of自然数' m + Num.of自然数' n
  证明: by
  induction n
  · simp only [Nat.add_zero, ofNat'_zero, add_zero]
  · simp only [Nat.add_succ, Nat.add_zero, ofNat'_succ, add_one, add_succ, *]

@[simp, norm_cast]

Depends on / 依赖: Nat.add_succ, Nat.add_zero, _succ, _zero, add_one, add_succ, add_zero
-/
theorem add_ofNat' (m n) : Num.ofNat' (m + n) = Num.ofNat' m + Num.ofNat' n := by
  induction n
  · simp only [Nat.add_zero, ofNat'_zero, add_zero]
  · simp only [Nat.add_succ, Nat.add_zero, ofNat'_succ, add_one, add_succ, *]

@[simp, norm_cast]
/--
theorem `cast_zero` / 定理 `cast_zero`

English:
theorem cast_zero
  given: [Zero α] [One α] [Add α]
  statement: ((0 : Num) : α) = 0
  proof: rfl

@[simp]

中文:
定理 cast_zero
  条件: [零 α] [幺 α] [加法 α]
  结论: ((0 : Num) : α) = 0
  证明: rfl

@[simp]
-/
theorem cast_zero [Zero α] [One α] [Add α] : ((0 : Num) : α) = 0 :=
  rfl

@[simp]
/--
theorem `cast_zero'` / 定理 `cast_zero'`

English:
theorem cast_zero'
  given: [Zero α] [One α] [Add α]
  statement: (Num.zero : α) = 0
  proof: rfl

@[simp, norm_cast]

中文:
定理 cast_zero'
  条件: [零 α] [幺 α] [加法 α]
  结论: (Num.zero : α) = 0
  证明: rfl

@[simp, norm_cast]
-/
theorem cast_zero' [Zero α] [One α] [Add α] : (Num.zero : α) = 0 :=
  rfl

@[simp, norm_cast]
/--
theorem `cast_one` / 定理 `cast_one`

English:
theorem cast_one
  given: [Zero α] [One α] [Add α]
  statement: ((1 : Num) : α) = 1
  proof: rfl

@[simp]

中文:
定理 cast_one
  条件: [零 α] [幺 α] [加法 α]
  结论: ((1 : Num) : α) = 1
  证明: rfl

@[simp]
-/
theorem cast_one [Zero α] [One α] [Add α] : ((1 : Num) : α) = 1 :=
  rfl

@[simp]
/--
theorem `cast_pos` / 定理 `cast_pos`

English:
theorem cast_pos
  given: [Zero α] [One α] [Add α] (n : PosNum)
  statement: (Num.pos n : α) = n
  proof: rfl

中文:
定理 cast_pos
  条件: [零 α] [幺 α] [加法 α] (n : PosNum)
  结论: (Num.pos n : α) = n
  证明: rfl
-/
theorem cast_pos [Zero α] [One α] [Add α] (n : PosNum) : (Num.pos n : α) = n :=
  rfl

/--
theorem `succ'_to_nat` / 定理 `succ'_to_nat`

English:
theorem succ'_to_nat
  statement: forall n, (succ' n : Nat) = n + 1

中文:
定理 succ'_to_nat
  结论: 对任意 n, (succ' n : 自然数) = n + 1
-/
theorem succ'_to_nat : forall n, (succ' n : Nat) = n + 1
  | 0 => (Nat.zero_add _).symm
  | pos _p => PosNum.succ_to_nat _

/--
theorem `succ_to_nat` / 定理 `succ_to_nat`

English:
theorem succ_to_nat
  given: (n)
  statement: (succ n : Nat) = n + 1
  proof: succ'_to_nat n

@[simp, norm_cast]

中文:
定理 succ_to_nat
  条件: (n)
  结论: (succ n : 自然数) = n + 1
  证明: succ'_to_nat n

@[simp, norm_cast]

Depends on / 依赖: _to_nat
-/
theorem succ_to_nat (n) : (succ n : Nat) = n + 1 :=
  succ'_to_nat n

@[simp, norm_cast]
/--
theorem `cast_to_nat` / 定理 `cast_to_nat`

English:
theorem cast_to_nat
  given: [AddMonoidWithOne α]
  statement: forall n : Num, ((n : Nat) : α) = n

中文:
定理 cast_to_nat
  条件: [加法带幺幺半群 α]
  结论: 对任意 n : Num, ((n : 自然数) : α) = n
-/
theorem cast_to_nat [AddMonoidWithOne α] : forall n : Num, ((n : Nat) : α) = n
  | 0 => Nat.cast_zero
  | pos p => p.cast_to_nat

@[norm_cast]
/--
theorem `add_to_nat` / 定理 `add_to_nat`

English:
theorem add_to_nat
  statement: forall m n, ((m + n : Num) : Nat) = m + n

中文:
定理 add_to_nat
  结论: 对任意 m n, ((m + n : Num) : 自然数) = m + n
-/
theorem add_to_nat : forall m n, ((m + n : Num) : Nat) = m + n
  | 0, 0 => rfl
  | 0, pos _q => (Nat.zero_add _).symm
  | pos _p, 0 => rfl
  | pos _p, pos _q => PosNum.add_to_nat _ _

@[norm_cast]
/--
theorem `mul_to_nat` / 定理 `mul_to_nat`

English:
theorem mul_to_nat
  statement: forall m n, ((m * n : Num) : Nat) = m * n

中文:
定理 mul_to_nat
  结论: 对任意 m n, ((m * n : Num) : 自然数) = m * n
-/
theorem mul_to_nat : forall m n, ((m * n : Num) : Nat) = m * n
  | 0, 0 => rfl
  | 0, pos _q => (zero_mul _).symm
  | pos _p, 0 => rfl
  | pos _p, pos _q => PosNum.mul_to_nat _ _

/--
theorem `cmp_to_nat` / 定理 `cmp_to_nat`

English:
theorem cmp_to_nat
  statement: forall m n, (Ordering.casesOn (cmp m n) ((m : Nat) < n) (m = n) ((n : Nat) < m) : Prop)
  proof: PosNum.cmp_to_nat a b; revert this; dsimp [cmp]; cases PosNum.cmp a b
    exacts [id, congr_arg pos, id]

@[norm_cast]

中文:
定理 cmp_to_nat
  结论: 对任意 m n, (Ordering.casesOn (cmp m n) ((m : 自然数) < n) (m = n) ((n : 自然数) < m) : 命题)
  证明: PosNum.cmp_to_nat a b; revert this; dsimp [cmp]; cases PosNum.cmp a b
    exacts [id, congr_arg pos, id]

@[norm_cast]

Depends on / 依赖: PosNum, PosNum.cmp, PosNum.cmp_to_nat, cmp_to_nat, revert
-/
theorem cmp_to_nat : forall m n, (Ordering.casesOn (cmp m n) ((m : Nat) < n) (m = n) ((n : Nat) < m) : Prop)
  | 0, 0 => rfl
  | 0, pos _ => to_nat_pos _
  | pos _, 0 => to_nat_pos _
  | pos a, pos b => by
    have := PosNum.cmp_to_nat a b; revert this; dsimp [cmp]; cases PosNum.cmp a b
    exacts [id, congr_arg pos, id]

@[norm_cast]
/--
theorem `lt_to_nat` / 定理 `lt_to_nat`

English:
theorem lt_to_nat
  given: {m n : Num}
  statement: (m : Nat) < n ↔ m < n
  proof: show (m : Nat) < n ↔ cmp m n = Ordering.lt from
    match cmp m n, cmp_to_nat m n with
    | Ordering.lt, h => by simp [h]
    | Ordering.eq, h => by simp [h]
    | Ordering.gt, h => by simp [not_lt_of_gt h]

@[norm_cast]

中文:
定理 lt_to_nat
  条件: {m n : Num}
  结论: (m : 自然数) < n ↔ m < n
  证明: show (m : Nat) < n ↔ cmp m n = Ordering.lt from
    match cmp m n, cmp_to_nat m n with
    | Ordering.lt, h => by simp [h]
    | Ordering.eq, h => by simp [h]
    | Ordering.gt, h => by simp [not_lt_of_gt h]

@[norm_cast]

Depends on / 依赖: Ordering, Ordering.eq, Ordering.gt, Ordering.lt, cmp_to_nat, not_lt_of_gt
-/
theorem lt_to_nat {m n : Num} : (m : Nat) < n ↔ m < n :=
  show (m : Nat) < n ↔ cmp m n = Ordering.lt from
    match cmp m n, cmp_to_nat m n with
    | Ordering.lt, h => by simp [h]
    | Ordering.eq, h => by simp [h]
    | Ordering.gt, h => by simp [not_lt_of_gt h]

@[norm_cast]
/--
theorem `le_to_nat` / 定理 `le_to_nat`

English:
theorem le_to_nat
  given: {m n : Num}
  statement: (m : Nat) <= n ↔ m <= n
  proof: by
  rw [← not_lt]; exact not_congr lt_to_nat

中文:
定理 le_to_nat
  条件: {m n : Num}
  结论: (m : 自然数) <= n ↔ m <= n
  证明: by
  rw [← not_lt]; exact not_congr lt_to_nat

Depends on / 依赖: lt_to_nat, not_congr, not_lt
-/
theorem le_to_nat {m n : Num} : (m : Nat) <= n ↔ m <= n := by
  rw [← not_lt]; exact not_congr lt_to_nat

end Num

namespace PosNum

@[simp]
/--
theorem `of_to_nat'` / 定理 `of_to_nat'`

English:
theorem of_to_nat'
  statement: forall n : PosNum, Num.ofNat' (n : Nat) = Num.pos n

中文:
定理 of_to_nat'
  结论: 对任意 n : PosNum, Num.of自然数' (n : 自然数) = Num.pos n
-/
theorem of_to_nat' : forall n : PosNum, Num.ofNat' (n : Nat) = Num.pos n
  | 1 => by
      simp only [cast_one, Num.ofNat'_one]
      norm_cast
  | bit0 p => by
      simpa only [Nat.bit_false, cond_false, two_mul, of_to_nat' p] using! Num.ofNat'_bit false p
  | bit1 p => by
      simpa only [Nat.bit_true, cond_true, two_mul, of_to_nat' p] using! Num.ofNat'_bit true p

end PosNum

namespace Num

@[simp, norm_cast]
/--
theorem `of_to_nat'` / 定理 `of_to_nat'`

English:
theorem of_to_nat'
  statement: forall n : Num, Num.ofNat' (n : Nat) = n

中文:
定理 of_to_nat'
  结论: 对任意 n : Num, Num.of自然数' (n : 自然数) = n
-/
theorem of_to_nat' : forall n : Num, Num.ofNat' (n : Nat) = n
  | 0 => ofNat'_zero
  | pos p => p.of_to_nat'

/--
lemma `toNat_injective` / 引理 `toNat_injective`

English:
lemma toNat_injective
  statement: Function.Injective (castNum : Num -> Nat)
  proof: Function.LeftInverse.injective of_to_nat'

@[norm_cast]

中文:
引理 to自然数_injective
  结论: 函数.单射 (castNum : Num -> 自然数)
  证明: Function.LeftInverse.injective of_to_nat'

@[norm_cast]

Depends on / 依赖: Function, Function.LeftInverse.injective, LeftInverse, injective, of_to_nat
-/
lemma toNat_injective : Function.Injective (castNum : Num -> Nat) :=
  Function.LeftInverse.injective of_to_nat'

@[norm_cast]
/--
theorem `to_nat_inj` / 定理 `to_nat_inj`

English:
theorem to_nat_inj
  given: {m n : Num}
  statement: (m : Nat) = n ↔ m = n
  proof: toNat_injective.eq_iff

中文:
定理 to_nat_inj
  条件: {m n : Num}
  结论: (m : 自然数) = n ↔ m = n
  证明: toNat_injective.eq_iff

Depends on / 依赖: eq_iff, toNat_injective, toNat_injective.eq_iff
-/
theorem to_nat_inj {m n : Num} : (m : Nat) = n ↔ m = n := toNat_injective.eq_iff

/-- This tactic tries to turn an (in)equality about `Num`s to one about `Nat`s by rewriting.
```lean
example (n : Num) (m : Num) : n ≤ n + m := by
  transfer_rw
  exact Nat.le_add_right _ _
```
-/
scoped macro (name := transfer_rw) "transfer_rw" : tactic => `(tactic|
    (repeat first | rw [← to_nat_inj] | rw [← lt_to_nat] | rw [← le_to_nat]
     repeat first | rw [add_to_nat] | rw [mul_to_nat] | rw [cast_one] | rw [cast_zero]))

/--
This tactic tries to prove (in)equalities about `Num`s by transferring them to the `Nat` world and
then trying to call `simp`.
```lean
example (n : Num) (m : Num) : n ≤ n + m := by transfer
```
-/
scoped macro (name := transfer) "transfer" : tactic => `(tactic|
    (intros; transfer_rw; try simp))

/--
Instance `addMonoid` / 实例 `addMonoid`

English:
instance addMonoid
  signature: : AddMonoid Num where
  body: zero_add
  add_zero := add_zero
  add_assoc := by transfer
  nsmul := nsmulRec

中文:
实例 addMonoid
  签名: : 加法幺半群 Num where
  定义体: zero_add
  add_zero := add_zero
  add_assoc := by transfer
  nsmul := nsmulRec

Depends on / 依赖: zero_add
-/
instance addMonoid : AddMonoid Num where
  zero_add := zero_add
  add_zero := add_zero
  add_assoc := by transfer
  nsmul := nsmulRec

/--
Instance `addMonoidWithOne` / 实例 `addMonoidWithOne`

English:
instance addMonoidWithOne
  signature: : AddMonoidWithOne Num
  body: { Num.addMonoid with
    natCast := Num.ofNat'
    natCast_zero := ofNat'_zero
    natCast_succ := fun _ => ofNat'_succ }

中文:
实例 addMonoidWithOne
  签名: : 加法带幺幺半群 Num
  定义体: { Num.addMonoid with
    natCast := Num.ofNat'
    natCast_zero := ofNat'_zero
    natCast_succ := fun _ => ofNat'_succ }

Depends on / 依赖: Num.addMonoid, Num.ofNat, _succ, _zero, addMonoid, natCast, natCast_succ, natCast_zero
-/
instance addMonoidWithOne : AddMonoidWithOne Num :=
  { Num.addMonoid with
    natCast := Num.ofNat'
    natCast_zero := ofNat'_zero
    natCast_succ := fun _ => ofNat'_succ }

/--
Instance `commSemiring` / 实例 `commSemiring`

English:
instance commSemiring
  signature: : CommSemiring Num where
  body: Num.addMonoid
  __ := Num.addMonoidWithOne
  npow := @npowRec Num ⟨1⟩ ⟨(· * ·)⟩
  mul_zero _ := by rw [← to_nat_inj, mul_to_nat, cast_zero, mul_zero]
  zero_mul _ := by rw [← to_nat_inj, mul_to_nat, cast_zero, zero_mul]
  mul_one _ := by rw [← to_nat_inj, mul_to_nat, cast_one, mul_one]
  one_mul _ :

中文:
实例 commSemiring
  签名: : 交换半环 Num where
  定义体: Num.addMonoid
  __ := Num.addMonoidWithOne
  npow := @npowRec Num ⟨1⟩ ⟨(· * ·)⟩
  mul_zero _ := by rw [← to_nat_inj, mul_to_nat, cast_zero, mul_zero]
  zero_mul _ := by rw [← to_nat_inj, mul_to_nat, cast_zero, zero_mul]
  mul_one _ := by rw [← to_nat_inj, mul_to_nat, cast_one, mul_one]
  one_mul _ :

Depends on / 依赖: Num.addMonoid, addMonoid
-/
instance commSemiring : CommSemiring Num where
  __ := Num.addMonoid
  __ := Num.addMonoidWithOne
  npow := @npowRec Num ⟨1⟩ ⟨(· * ·)⟩
  mul_zero _ := by rw [← to_nat_inj, mul_to_nat, cast_zero, mul_zero]
  zero_mul _ := by rw [← to_nat_inj, mul_to_nat, cast_zero, zero_mul]
  mul_one _ := by rw [← to_nat_inj, mul_to_nat, cast_one, mul_one]
  one_mul _ := by rw [← to_nat_inj, mul_to_nat, cast_one, one_mul]
  add_comm _ _ := by simp_rw [← to_nat_inj, add_to_nat, add_comm]
  mul_comm _ _ := by simp_rw [← to_nat_inj, mul_to_nat, mul_comm]
  mul_assoc _ _ _ := by simp_rw [← to_nat_inj, mul_to_nat, mul_assoc]
  left_distrib _ _ _ := by simp only [← to_nat_inj, mul_to_nat, add_to_nat, mul_add]
  right_distrib _ _ _ := by simp only [← to_nat_inj, mul_to_nat, add_to_nat, add_mul]

/--
Instance `partialOrder` / 实例 `partialOrder`

English:
instance partialOrder
  signature: : PartialOrder Num where
  body: by simp only [← lt_to_nat, ← le_to_nat, lt_iff_le_not_ge]
  le_refl := by transfer
  le_trans a b c := by transfer_rw; apply le_trans
  le_antisymm a b := by transfer_rw; apply le_antisymm

中文:
实例 partialOrder
  签名: : 偏序 Num where
  定义体: by simp only [← lt_to_nat, ← le_to_nat, lt_iff_le_not_ge]
  le_refl := by transfer
  le_trans a b c := by transfer_rw; apply le_trans
  le_antisymm a b := by transfer_rw; apply le_antisymm

Depends on / 依赖: le_antisymm, le_refl, le_to_nat, le_trans, lt_iff_le_not_ge, lt_to_nat, transfer, transfer_rw
-/
instance partialOrder : PartialOrder Num where
  lt_iff_le_not_ge a b := by simp only [← lt_to_nat, ← le_to_nat, lt_iff_le_not_ge]
  le_refl := by transfer
  le_trans a b c := by transfer_rw; apply le_trans
  le_antisymm a b := by transfer_rw; apply le_antisymm

/--
Instance `isOrderedCancelAddMonoid` / 实例 `isOrderedCancelAddMonoid`

English:
instance isOrderedCancelAddMonoid
  signature: : IsOrderedCancelAddMonoid Num where
  body: by revert h; transfer_rw; exact fun h => add_le_add_left h c
  le_of_add_le_add_left a b c := by transfer_rw; apply le_of_add_le_add_left

中文:
实例 isOrderedCancelAddMonoid
  签名: : 是OrderedCancelAdd幺半群 Num where
  定义体: by revert h; transfer_rw; exact fun h => add_le_add_left h c
  le_of_add_le_add_left a b c := by transfer_rw; apply le_of_add_le_add_left

Depends on / 依赖: add_le_add_left, le_of_add_le_add_left, revert, transfer_rw
-/
instance isOrderedCancelAddMonoid : IsOrderedCancelAddMonoid Num where
  add_le_add_left a b h c := by revert h; transfer_rw; exact fun h => add_le_add_left h c
  le_of_add_le_add_left a b c := by transfer_rw; apply le_of_add_le_add_left

/--
Instance `linearOrder` / 实例 `linearOrder`

English:
instance linearOrder
  signature: : LinearOrder Num
  body: { le_total := by
      intro a b
      transfer_rw
      apply le_total
    toDecidableLT := Num.decidableLT
    toDecidableLE := Num.decidableLE
    -- This is relying on an automatically generated instance name,
    -- generated in a `deriving` handler.
    -- See https://github.com/leanprover/lea

中文:
实例 linearOrder
  签名: : 线性序 Num
  定义体: { le_total := by
      intro a b
      transfer_rw
      apply le_total
    toDecidableLT := Num.decidableLT
    toDecidableLE := Num.decidableLE
    -- This is relying on an automatically generated instance name,
    -- generated in a `deriving` handler.
    -- See https://github.com/leanprover/lea

Depends on / 依赖: Num.decidableLE, Num.decidableLT, decidableLE, decidableLT, le_total, toDecidableLE, toDecidableLT, transfer_rw
-/
instance linearOrder : LinearOrder Num :=
  { le_total := by
      intro a b
      transfer_rw
      apply le_total
    toDecidableLT := Num.decidableLT
    toDecidableLE := Num.decidableLE
    -- This is relying on an automatically generated instance name,
    -- generated in a `deriving` handler.
    -- See https://github.com/leanprover/lean4/issues/2343
    toDecidableEq := instDecidableEqNum }

/--
Instance `isStrictOrderedRing` / 实例 `isStrictOrderedRing`

English:
instance isStrictOrderedRing
  signature: : IsStrictOrderedRing Num where
  body: by decide
  exists_pair_ne := ⟨0, 1, by decide⟩
  mul_lt_mul_of_pos_left a ha b c := by
    revert ha
    transfer_rw
    apply flip mul_lt_mul_of_pos_left
  mul_lt_mul_of_pos_right a ha b c := by
    revert ha
    transfer_rw
    apply flip mul_lt_mul_of_pos_right

@[norm_cast]

中文:
实例 isStrictOrderedRing
  签名: : 是StrictOrdered环 Num where
  定义体: by decide
  exists_pair_ne := ⟨0, 1, by decide⟩
  mul_lt_mul_of_pos_left a ha b c := by
    revert ha
    transfer_rw
    apply flip mul_lt_mul_of_pos_left
  mul_lt_mul_of_pos_right a ha b c := by
    revert ha
    transfer_rw
    apply flip mul_lt_mul_of_pos_right

@[norm_cast]

Depends on / 依赖: exists_pair_ne, mul_lt_mul_of_pos_left, mul_lt_mul_of_pos_right, revert, transfer_rw
-/
instance isStrictOrderedRing : IsStrictOrderedRing Num where
  zero_le_one := by decide
  exists_pair_ne := ⟨0, 1, by decide⟩
  mul_lt_mul_of_pos_left a ha b c := by
    revert ha
    transfer_rw
    apply flip mul_lt_mul_of_pos_left
  mul_lt_mul_of_pos_right a ha b c := by
    revert ha
    transfer_rw
    apply flip mul_lt_mul_of_pos_right

@[norm_cast]
/--
theorem `add_of_nat` / 定理 `add_of_nat`

English:
theorem add_of_nat
  given: (m n)
  statement: ((m + n : Nat) : Num) = m + n
  proof: add_ofNat' _ _

@[norm_cast]

中文:
定理 add_of_nat
  条件: (m n)
  结论: ((m + n : 自然数) : Num) = m + n
  证明: add_ofNat' _ _

@[norm_cast]

Depends on / 依赖: add_ofNat
-/
theorem add_of_nat (m n) : ((m + n : Nat) : Num) = m + n :=
  add_ofNat' _ _

@[norm_cast]
/--
theorem `to_nat_to_int` / 定理 `to_nat_to_int`

English:
theorem to_nat_to_int
  given: (n : Num)
  statement: ((n : Nat) : Int) = n
  proof: cast_to_nat _

@[simp, norm_cast]

中文:
定理 to_nat_to_int
  条件: (n : Num)
  结论: ((n : 自然数) : 整数) = n
  证明: cast_to_nat _

@[simp, norm_cast]

Depends on / 依赖: cast_to_nat
-/
theorem to_nat_to_int (n : Num) : ((n : Nat) : Int) = n :=
  cast_to_nat _

@[simp, norm_cast]
/--
theorem `cast_to_int` / 定理 `cast_to_int`

English:
theorem cast_to_int
  given: {α} [AddGroupWithOne α] (n : Num)
  statement: ((n : Int) : α) = n
  proof: by
  rw [← to_nat_to_int]; rw [Int.cast_natCast]; rw [cast_to_nat]

中文:
定理 cast_to_int
  条件: {α} [加法带幺群 α] (n : Num)
  结论: ((n : 整数) : α) = n
  证明: by
  rw [← to_nat_to_int]; rw [Int.cast_natCast]; rw [cast_to_nat]

Depends on / 依赖: Int.cast_natCast, cast_natCast, cast_to_nat, to_nat_to_int
-/
theorem cast_to_int {α} [AddGroupWithOne α] (n : Num) : ((n : Int) : α) = n := by
  rw [← to_nat_to_int]; rw [Int.cast_natCast]; rw [cast_to_nat]

/--
theorem `to_of_nat` / 定理 `to_of_nat`

English:
theorem to_of_nat
  statement: forall n : Nat, ((n : Num) : Nat) = n

中文:
定理 to_of_nat
  结论: 对任意 n : 自然数, ((n : Num) : 自然数) = n
-/
theorem to_of_nat : forall n : Nat, ((n : Num) : Nat) = n
  | 0 => by rw [Nat.cast_zero, cast_zero]
  | n + 1 => by rw [Nat.cast_succ, add_one, succ_to_nat, to_of_nat n]

@[simp, norm_cast]
/--
theorem `of_natCast` / 定理 `of_natCast`

English:
theorem of_natCast
  given: {α} [AddMonoidWithOne α] (n : Nat)
  statement: ((n : Num) : α) = n
  proof: by
  rw [← cast_to_nat]; rw [to_of_nat]

@[norm_cast]

中文:
定理 of_natCast
  条件: {α} [加法带幺幺半群 α] (n : 自然数)
  结论: ((n : Num) : α) = n
  证明: by
  rw [← cast_to_nat]; rw [to_of_nat]

@[norm_cast]

Depends on / 依赖: cast_to_nat, to_of_nat
-/
theorem of_natCast {α} [AddMonoidWithOne α] (n : Nat) : ((n : Num) : α) = n := by
  rw [← cast_to_nat]; rw [to_of_nat]

@[norm_cast]
/--
theorem `of_nat_inj` / 定理 `of_nat_inj`

English:
theorem of_nat_inj
  given: {m n : Nat}
  statement: (m : Num) = n ↔ m = n
  proof: ⟨fun h => Function.LeftInverse.injective to_of_nat h, congr_arg _⟩

中文:
定理 of_nat_inj
  条件: {m n : 自然数}
  结论: (m : Num) = n ↔ m = n
  证明: ⟨fun h => Function.LeftInverse.injective to_of_nat h, congr_arg _⟩

Depends on / 依赖: Function, Function.LeftInverse.injective, LeftInverse, congr_arg, injective, to_of_nat
-/
theorem of_nat_inj {m n : Nat} : (m : Num) = n ↔ m = n :=
  ⟨fun h => Function.LeftInverse.injective to_of_nat h, congr_arg _⟩

-- The priority should be `high`er than `cast_to_nat`.
@[simp high, norm_cast]
/--
theorem `of_to_nat` / 定理 `of_to_nat`

English:
theorem of_to_nat
  statement: forall n : Num, ((n : Nat) : Num) = n
  proof: of_to_nat'

@[norm_cast]

中文:
定理 of_to_nat
  结论: 对任意 n : Num, ((n : 自然数) : Num) = n
  证明: of_to_nat'

@[norm_cast]

Depends on / 依赖: of_to_nat
-/
theorem of_to_nat : forall n : Num, ((n : Nat) : Num) = n :=
  of_to_nat'

@[norm_cast]
/--
theorem `dvd_to_nat` / 定理 `dvd_to_nat`

English:
theorem dvd_to_nat
  given: (m n : Num)
  statement: (m : Nat) ∣ n ↔ m ∣ n
  proof: ⟨fun ⟨k, e⟩ => ⟨k, by rw [← of_to_nat n, e]; simp⟩, fun ⟨k, e⟩ => ⟨k, by simp [e, mul_to_nat]⟩⟩

中文:
定理 dvd_to_nat
  条件: (m n : Num)
  结论: (m : 自然数) ∣ n ↔ m ∣ n
  证明: ⟨fun ⟨k, e⟩ => ⟨k, by rw [← of_to_nat n, e]; simp⟩, fun ⟨k, e⟩ => ⟨k, by simp [e, mul_to_nat]⟩⟩

Depends on / 依赖: mul_to_nat, of_to_nat
-/
theorem dvd_to_nat (m n : Num) : (m : Nat) ∣ n ↔ m ∣ n :=
  ⟨fun ⟨k, e⟩ => ⟨k, by rw [← of_to_nat n, e]; simp⟩, fun ⟨k, e⟩ => ⟨k, by simp [e, mul_to_nat]⟩⟩

end Num

namespace PosNum

variable {α : Type*}

open Num

-- The priority should be `high`er than `cast_to_nat`.
@[simp high, norm_cast]
/--
theorem `of_to_nat` / 定理 `of_to_nat`

English:
theorem of_to_nat
  statement: forall n : PosNum, ((n : Nat) : Num) = Num.pos n
  proof: of_to_nat'

@[norm_cast]

中文:
定理 of_to_nat
  结论: 对任意 n : PosNum, ((n : 自然数) : Num) = Num.pos n
  证明: of_to_nat'

@[norm_cast]

Depends on / 依赖: of_to_nat
-/
theorem of_to_nat : forall n : PosNum, ((n : Nat) : Num) = Num.pos n :=
  of_to_nat'

@[norm_cast]
/--
theorem `to_nat_inj` / 定理 `to_nat_inj`

English:
theorem to_nat_inj
  given: {m n : PosNum}
  statement: (m : Nat) = n ↔ m = n
  proof: ⟨fun h => Num.pos.inj by rw [← PosNum.of_to_nat, ← PosNum.of_to_nat, h], congr_arg _⟩

中文:
定理 to_nat_inj
  条件: {m n : PosNum}
  结论: (m : 自然数) = n ↔ m = n
  证明: ⟨fun h => Num.pos.inj by rw [← PosNum.of_to_nat, ← PosNum.of_to_nat, h], congr_arg _⟩

Depends on / 依赖: Num.pos.inj, PosNum, PosNum.of_to_nat, congr_arg, of_to_nat
-/
theorem to_nat_inj {m n : PosNum} : (m : Nat) = n ↔ m = n :=
⟨fun h => Num.pos.inj by rw [← PosNum.of_to_nat, ← PosNum.of_to_nat, h], congr_arg _⟩

/--
theorem `pred'_to_nat` / 定理 `pred'_to_nat`

English:
theorem pred'_to_nat
  statement: forall n, (pred' n : Nat) = Nat.pred n
  proof: by
      rw [pred'_to_nat n]; rw [Nat.succ_pred_eq_of_pos (to_nat_pos n)]
    match (motive :=
        forall k : Num, Nat.succ ↑k = ↑n -> ↑(Num.casesOn k 1 bit1 : PosNum) = Nat.pred (n + n))
      pred' n, this with
    | 0, (h : ((1 : Num) : Nat) = n) => by rw [← to_nat_inj.1 h]; rfl
    | Num.pos

中文:
定理 pred'_to_nat
  结论: 对任意 n, (pred' n : 自然数) = 自然数.pred n
  证明: by
      rw [pred'_to_nat n]; rw [Nat.succ_pred_eq_of_pos (to_nat_pos n)]
    match (motive :=
        forall k : Num, Nat.succ ↑k = ↑n -> ↑(Num.casesOn k 1 bit1 : PosNum) = Nat.pred (n + n))
      pred' n, this with
    | 0, (h : ((1 : Num) : Nat) = n) => by rw [← to_nat_inj.1 h]; rfl
    | Num.pos

Depends on / 依赖: Nat.pred, Nat.succ, Nat.succ_add, Nat.succ_pred_eq_of_pos, Num.casesOn, Num.pos, PosNum, _to_nat, casesOn, motive, succ_add, succ_pred_eq_of_pos, to_nat_inj, to_nat_pos
-/
theorem pred'_to_nat : forall n, (pred' n : Nat) = Nat.pred n
  | 1 => rfl
  | bit0 n =>
    have : Nat.succ ↑(pred' n) = ↑n := by
      rw [pred'_to_nat n]; rw [Nat.succ_pred_eq_of_pos (to_nat_pos n)]
    match (motive :=
        forall k : Num, Nat.succ ↑k = ↑n -> ↑(Num.casesOn k 1 bit1 : PosNum) = Nat.pred (n + n))
      pred' n, this with
    | 0, (h : ((1 : Num) : Nat) = n) => by rw [← to_nat_inj.1 h]; rfl
    | Num.pos p, (h : Nat.succ ↑p = n) => by rw [← h]; exact (Nat.succ_add p p).symm
  | bit1 _ => rfl

@[simp]
/--
theorem `pred'_succ'` / 定理 `pred'_succ'`

English:
theorem pred'_succ'
  given: (n)
  statement: pred' (succ' n) = n
  proof: Num.to_nat_inj.1 by rw [pred'_to_nat, succ'_to_nat, Nat.add_one, Nat.pred_succ]

@[simp]

中文:
定理 pred'_succ'
  条件: (n)
  结论: pred' (succ' n) = n
  证明: Num.to_nat_inj.1 by rw [pred'_to_nat, succ'_to_nat, Nat.add_one, Nat.pred_succ]

@[simp]
-/
theorem pred'_succ' (n) : pred' (succ' n) = n :=
Num.to_nat_inj.1 by rw [pred'_to_nat, succ'_to_nat, Nat.add_one, Nat.pred_succ]

@[simp]
/--
theorem `succ'_pred'` / 定理 `succ'_pred'`

English:
theorem succ'_pred'
  given: (n)
  statement: succ' (pred' n) = n
  proof: to_nat_inj.1 by
    rw [succ'_to_nat]; rw [pred'_to_nat]; rw [Nat.add_one]; rw [Nat.succ_pred_eq_of_pos (to_nat_pos _)]

中文:
定理 succ'_pred'
  条件: (n)
  结论: succ' (pred' n) = n
  证明: to_nat_inj.1 by
    rw [succ'_to_nat]; rw [pred'_to_nat]; rw [Nat.add_one]; rw [Nat.succ_pred_eq_of_pos (to_nat_pos _)]

Depends on / 依赖: Nat.add_one, Nat.succ_pred_eq_of_pos, _to_nat, add_one, succ_pred_eq_of_pos, to_nat_inj, to_nat_pos
-/
theorem succ'_pred' (n) : succ' (pred' n) = n :=
to_nat_inj.1 by
    rw [succ'_to_nat]; rw [pred'_to_nat]; rw [Nat.add_one]; rw [Nat.succ_pred_eq_of_pos (to_nat_pos _)]

/--
Instance `dvd` / 实例 `dvd`

English:
instance dvd
  signature: : Dvd PosNum
  body: ⟨fun m n => pos m ∣ pos n⟩

@[norm_cast]

中文:
实例 dvd
  签名: : Dvd PosNum
  定义体: ⟨fun m n => pos m ∣ pos n⟩

@[norm_cast]
-/
instance dvd : Dvd PosNum :=
  ⟨fun m n => pos m ∣ pos n⟩

@[norm_cast]
/--
theorem `dvd_to_nat` / 定理 `dvd_to_nat`

English:
theorem dvd_to_nat
  given: {m n : PosNum}
  statement: (m : Nat) ∣ n ↔ m ∣ n
  proof: Num.dvd_to_nat (pos m) (pos n)

中文:
定理 dvd_to_nat
  条件: {m n : PosNum}
  结论: (m : 自然数) ∣ n ↔ m ∣ n
  证明: Num.dvd_to_nat (pos m) (pos n)

Depends on / 依赖: Num.dvd_to_nat, dvd_to_nat
-/
theorem dvd_to_nat {m n : PosNum} : (m : Nat) ∣ n ↔ m ∣ n :=
  Num.dvd_to_nat (pos m) (pos n)

/--
theorem `size_to_nat` / 定理 `size_to_nat`

English:
theorem size_to_nat
  statement: forall n, (size n : Nat) = Nat.size n
  proof: to_nat_pos n
      dsimp [Nat.bit]; lia
  | bit1 n => by
      rw [size]; rw [succ_to_nat]; rw [size_to_nat n]; rw [cast_bit1]; rw [← two_mul]; rw [← Nat.bit_true_apply]; rw [Nat.size_bit]
      dsimp [Nat.bit]; lia

中文:
定理 size_to_nat
  结论: 对任意 n, (size n : 自然数) = 自然数.size n
  证明: to_nat_pos n
      dsimp [Nat.bit]; lia
  | bit1 n => by
      rw [size]; rw [succ_to_nat]; rw [size_to_nat n]; rw [cast_bit1]; rw [← two_mul]; rw [← Nat.bit_true_apply]; rw [Nat.size_bit]
      dsimp [Nat.bit]; lia

Depends on / 依赖: to_nat_pos
-/
theorem size_to_nat : forall n, (size n : Nat) = Nat.size n
  | 1 => Nat.size_one.symm
  | bit0 n => by
      rw [size]; rw [succ_to_nat]; rw [size_to_nat n]; rw [cast_bit0]; rw [← two_mul]; rw [← Nat.bit_false_apply]; rw [Nat.size_bit]
      have := to_nat_pos n
      dsimp [Nat.bit]; lia
  | bit1 n => by
      rw [size]; rw [succ_to_nat]; rw [size_to_nat n]; rw [cast_bit1]; rw [← two_mul]; rw [← Nat.bit_true_apply]; rw [Nat.size_bit]
      dsimp [Nat.bit]; lia

/--
theorem `size_eq_natSize` / 定理 `size_eq_natSize`

English:
theorem size_eq_natSize
  statement: forall n, (size n : Nat) = natSize n

中文:
定理 size_eq_natSize
  结论: 对任意 n, (size n : 自然数) = natSize n
-/
theorem size_eq_natSize : forall n, (size n : Nat) = natSize n
  | 1 => rfl
  | bit0 n => by rw [size, succ_to_nat, natSize, size_eq_natSize n]
  | bit1 n => by rw [size, succ_to_nat, natSize, size_eq_natSize n]

/--
theorem `natSize_to_nat` / 定理 `natSize_to_nat`

English:
theorem natSize_to_nat
  given: (n)
  statement: natSize n = Nat.size n
  proof: by rw [← size_eq_natSize, size_to_nat]

中文:
定理 natSize_to_nat
  条件: (n)
  结论: natSize n = 自然数.size n
  证明: by rw [← size_eq_natSize, size_to_nat]

Depends on / 依赖: size_eq_natSize, size_to_nat
-/
theorem natSize_to_nat (n) : natSize n = Nat.size n := by rw [← size_eq_natSize, size_to_nat]

/--
theorem `natSize_pos` / 定理 `natSize_pos`

English:
theorem natSize_pos
  given: (n)
  statement: 0 < natSize n
  proof: by cases n <;> apply Nat.succ_pos

中文:
定理 natSize_pos
  条件: (n)
  结论: 0 < natSize n
  证明: by cases n <;> apply Nat.succ_pos

Depends on / 依赖: Nat.succ_pos, succ_pos
-/
theorem natSize_pos (n) : 0 < natSize n := by cases n <;> apply Nat.succ_pos

/-- This tactic tries to turn an (in)equality about `PosNum`s to one about `Nat`s by rewriting.
```lean
example (n : PosNum) (m : PosNum) : n ≤ n + m := by
  transfer_rw
  exact Nat.le_add_right _ _
```
-/
scoped macro (name := transfer_rw) "transfer_rw" : tactic => `(tactic|
    (repeat first | rw [← to_nat_inj] | rw [← lt_to_nat] | rw [← le_to_nat]
     repeat first | rw [add_to_nat] | rw [mul_to_nat] | rw [cast_one] | rw [cast_zero]))

/--
This tactic tries to prove (in)equalities about `PosNum`s by transferring them to the `Nat` world
and then trying to call `simp`.
```lean
example (n : PosNum) (m : PosNum) : n ≤ n + m := by transfer
```
-/
scoped macro (name := transfer) "transfer" : tactic => `(tactic|
    (intros; transfer_rw; try simp [add_comm, add_left_comm, mul_comm, mul_left_comm]))

/--
Instance `addCommSemigroup` / 实例 `addCommSemigroup`

English:
instance addCommSemigroup
  signature: : AddCommSemigroup PosNum where
  body: by transfer
  add_comm := by transfer

中文:
实例 addCommSemigroup
  签名: : 加法交换半群 PosNum where
  定义体: by transfer
  add_comm := by transfer

Depends on / 依赖: add_comm, transfer
-/
instance addCommSemigroup : AddCommSemigroup PosNum where
  add_assoc := by transfer
  add_comm := by transfer

/--
Instance `commMonoid` / 实例 `commMonoid`

English:
instance commMonoid
  signature: : CommMonoid PosNum where
  body: @npowRec PosNum ⟨1⟩ ⟨(· * ·)⟩
  mul_assoc := by transfer
  one_mul := by transfer
  mul_one := by transfer
  mul_comm := by transfer

中文:
实例 commMonoid
  签名: : 交换幺半群 PosNum where
  定义体: @npowRec PosNum ⟨1⟩ ⟨(· * ·)⟩
  mul_assoc := by transfer
  one_mul := by transfer
  mul_one := by transfer
  mul_comm := by transfer

Depends on / 依赖: PosNum, npowRec
-/
instance commMonoid : CommMonoid PosNum where
  npow := @npowRec PosNum ⟨1⟩ ⟨(· * ·)⟩
  mul_assoc := by transfer
  one_mul := by transfer
  mul_one := by transfer
  mul_comm := by transfer

/--
Instance `distrib` / 实例 `distrib`

English:
instance distrib
  signature: : Distrib PosNum where
  body: by transfer; simp [mul_add]
  right_distrib := by transfer; simp [mul_add, mul_comm]

中文:
实例 distrib
  签名: : Distrib PosNum where
  定义体: by transfer; simp [mul_add]
  right_distrib := by transfer; simp [mul_add, mul_comm]

Depends on / 依赖: mul_add, mul_comm, right_distrib, transfer
-/
instance distrib : Distrib PosNum where
  left_distrib := by transfer; simp [mul_add]
  right_distrib := by transfer; simp [mul_add, mul_comm]

/--
Instance `linearOrder` / 实例 `linearOrder`

English:
instance linearOrder
  signature: : LinearOrder PosNum where
  body: by
    intro a b
    transfer_rw
    apply lt_iff_le_not_ge
  le_refl := by transfer
  le_trans := by
    intro a b c
    transfer_rw
    apply le_trans
  le_antisymm := by
    intro a b
    transfer_rw
    apply le_antisymm
  le_total := by
    intro a b
    transfer_rw
    apply le_total
  toDecid

中文:
实例 linearOrder
  签名: : 线性序 PosNum where
  定义体: by
    intro a b
    transfer_rw
    apply lt_iff_le_not_ge
  le_refl := by transfer
  le_trans := by
    intro a b c
    transfer_rw
    apply le_trans
  le_antisymm := by
    intro a b
    transfer_rw
    apply le_antisymm
  le_total := by
    intro a b
    transfer_rw
    apply le_total
  toDecid

Depends on / 依赖: infer_instance, le_antisymm, le_refl, le_total, le_trans, lt_iff_le_not_ge, toDecidableEq, toDecidableLE, toDecidableLT, transfer, transfer_rw
-/
instance linearOrder : LinearOrder PosNum where
  lt_iff_le_not_ge := by
    intro a b
    transfer_rw
    apply lt_iff_le_not_ge
  le_refl := by transfer
  le_trans := by
    intro a b c
    transfer_rw
    apply le_trans
  le_antisymm := by
    intro a b
    transfer_rw
    apply le_antisymm
  le_total := by
    intro a b
    transfer_rw
    apply le_total
  toDecidableLT := by infer_instance
  toDecidableLE := by infer_instance
  toDecidableEq := by infer_instance

@[simp]
/--
theorem `cast_to_num` / 定理 `cast_to_num`

English:
theorem cast_to_num
  given: (n : PosNum)
  statement: ↑n = Num.pos n
  proof: by rw [← cast_to_nat, ← of_to_nat n]

@[simp, norm_cast]

中文:
定理 cast_to_num
  条件: (n : PosNum)
  结论: ↑n = Num.pos n
  证明: by rw [← cast_to_nat, ← of_to_nat n]

@[simp, norm_cast]

Depends on / 依赖: cast_to_nat, of_to_nat
-/
theorem cast_to_num (n : PosNum) : ↑n = Num.pos n := by rw [← cast_to_nat, ← of_to_nat n]

@[simp, norm_cast]
/--
theorem `bit_to_nat` / 定理 `bit_to_nat`

English:
theorem bit_to_nat
  given: (b n)
  statement: (bit b n : Nat) = Nat.bit b n
  proof: by cases b <;> simp [bit, two_mul]

@[simp, norm_cast]

中文:
定理 bit_to_nat
  条件: (b n)
  结论: (bit b n : 自然数) = 自然数.bit b n
  证明: by cases b <;> simp [bit, two_mul]

@[simp, norm_cast]

Depends on / 依赖: two_mul
-/
theorem bit_to_nat (b n) : (bit b n : Nat) = Nat.bit b n := by cases b <;> simp [bit, two_mul]

@[simp, norm_cast]
/--
theorem `cast_add` / 定理 `cast_add`

English:
theorem cast_add
  given: [AddMonoidWithOne α] (m n)
  statement: ((m + n : PosNum) : α) = m + n
  proof: by
  rw [← cast_to_nat]; rw [add_to_nat]; rw [Nat.cast_add]; rw [cast_to_nat]; rw [cast_to_nat]

@[simp 500, norm_cast]

中文:
定理 cast_add
  条件: [加法带幺幺半群 α] (m n)
  结论: ((m + n : PosNum) : α) = m + n
  证明: by
  rw [← cast_to_nat]; rw [add_to_nat]; rw [Nat.cast_add]; rw [cast_to_nat]; rw [cast_to_nat]

@[simp 500, norm_cast]

Depends on / 依赖: Nat.cast_add, add_to_nat, cast_add, cast_to_nat
-/
theorem cast_add [AddMonoidWithOne α] (m n) : ((m + n : PosNum) : α) = m + n := by
  rw [← cast_to_nat]; rw [add_to_nat]; rw [Nat.cast_add]; rw [cast_to_nat]; rw [cast_to_nat]

@[simp 500, norm_cast]
/--
theorem `cast_succ` / 定理 `cast_succ`

English:
theorem cast_succ
  given: [AddMonoidWithOne α] (n : PosNum)
  statement: (succ n : α) = n + 1
  proof: by
  rw [← add_one]; rw [cast_add]; rw [cast_one]

@[simp, norm_cast]

中文:
定理 cast_succ
  条件: [加法带幺幺半群 α] (n : PosNum)
  结论: (succ n : α) = n + 1
  证明: by
  rw [← add_one]; rw [cast_add]; rw [cast_one]

@[simp, norm_cast]

Depends on / 依赖: add_one, cast_add, cast_one
-/
theorem cast_succ [AddMonoidWithOne α] (n : PosNum) : (succ n : α) = n + 1 := by
  rw [← add_one]; rw [cast_add]; rw [cast_one]

@[simp, norm_cast]
/--
theorem `cast_inj` / 定理 `cast_inj`

English:
theorem cast_inj
  given: [AddMonoidWithOne α] [CharZero α] {m n : PosNum}
  statement: (m : α) = n ↔ m = n
  proof: by
  rw [← cast_to_nat m]; rw [← cast_to_nat n]; rw [Nat.cast_inj]; rw [to_nat_inj]

@[simp]

中文:
定理 cast_inj
  条件: [加法带幺幺半群 α] [特征零 α] {m n : PosNum}
  结论: (m : α) = n ↔ m = n
  证明: by
  rw [← cast_to_nat m]; rw [← cast_to_nat n]; rw [Nat.cast_inj]; rw [to_nat_inj]

@[simp]

Depends on / 依赖: Nat.cast_inj, cast_inj, cast_to_nat, to_nat_inj
-/
theorem cast_inj [AddMonoidWithOne α] [CharZero α] {m n : PosNum} : (m : α) = n ↔ m = n := by
  rw [← cast_to_nat m]; rw [← cast_to_nat n]; rw [Nat.cast_inj]; rw [to_nat_inj]

@[simp]
/--
theorem `one_le_cast` / 定理 `one_le_cast`

English:
theorem one_le_cast
  given: [Semiring α] [PartialOrder α] [IsStrictOrderedRing α] (n : PosNum)
  proof: by
  rw [← cast_to_nat]; rw [← Nat.cast_one]; rw [Nat.cast_le (α := α)]; apply to_nat_pos

@[simp]

中文:
定理 one_le_cast
  条件: [半环 α] [偏序 α] [是StrictOrdered环 α] (n : PosNum)
  证明: by
  rw [← cast_to_nat]; rw [← Nat.cast_one]; rw [Nat.cast_le (α := α)]; apply to_nat_pos

@[simp]

Depends on / 依赖: Nat.cast_le, Nat.cast_one, cast_le, cast_one, cast_to_nat, to_nat_pos
-/
theorem one_le_cast [Semiring α] [PartialOrder α] [IsStrictOrderedRing α] (n : PosNum) :
    (1 : α) <= n := by
  rw [← cast_to_nat]; rw [← Nat.cast_one]; rw [Nat.cast_le (α := α)]; apply to_nat_pos

@[simp]
/--
theorem `cast_pos` / 定理 `cast_pos`

English:
theorem cast_pos
  given: [Semiring α] [PartialOrder α] [IsStrictOrderedRing α] (n : PosNum)
  statement: 0 < (n : α)
  proof: lt_of_lt_of_le zero_lt_one (one_le_cast n)

@[simp, norm_cast]

中文:
定理 cast_pos
  条件: [半环 α] [偏序 α] [是StrictOrdered环 α] (n : PosNum)
  结论: 0 < (n : α)
  证明: lt_of_lt_of_le zero_lt_one (one_le_cast n)

@[simp, norm_cast]

Depends on / 依赖: lt_of_lt_of_le, one_le_cast, zero_lt_one
-/
theorem cast_pos [Semiring α] [PartialOrder α] [IsStrictOrderedRing α] (n : PosNum) : 0 < (n : α) :=
  lt_of_lt_of_le zero_lt_one (one_le_cast n)

@[simp, norm_cast]
/--
theorem `cast_mul` / 定理 `cast_mul`

English:
theorem cast_mul
  given: [NonAssocSemiring α] (m n)
  statement: ((m * n : PosNum) : α) = m * n
  proof: by
  rw [← cast_to_nat]; rw [mul_to_nat]; rw [Nat.cast_mul]; rw [cast_to_nat]; rw [cast_to_nat]

@[simp]

中文:
定理 cast_mul
  条件: [非结合半环 α] (m n)
  结论: ((m * n : PosNum) : α) = m * n
  证明: by
  rw [← cast_to_nat]; rw [mul_to_nat]; rw [Nat.cast_mul]; rw [cast_to_nat]; rw [cast_to_nat]

@[simp]

Depends on / 依赖: Nat.cast_mul, cast_mul, cast_to_nat, mul_to_nat
-/
theorem cast_mul [NonAssocSemiring α] (m n) : ((m * n : PosNum) : α) = m * n := by
  rw [← cast_to_nat]; rw [mul_to_nat]; rw [Nat.cast_mul]; rw [cast_to_nat]; rw [cast_to_nat]

@[simp]
/--
theorem `cmp_eq` / 定理 `cmp_eq`

English:
theorem cmp_eq
  given: (m n)
  statement: cmp m n = Ordering.eq ↔ m = n
  proof: by
  have := cmp_to_nat m n
  norm_cast at this
  -- Porting note: `cases` didn't rewrite at `this`, so `revert` is required.
  revert this; cases cmp m n <;> simp_all [LT.lt.ne, LT.lt.ne']

@[simp, norm_cast]

中文:
定理 cmp_eq
  条件: (m n)
  结论: cmp m n = Ordering.eq ↔ m = n
  证明: by
  have := cmp_to_nat m n
  norm_cast at this
  -- Porting note: `cases` didn't rewrite at `this`, so `revert` is required.
  revert this; cases cmp m n <;> simp_all [LT.lt.ne, LT.lt.ne']

@[simp, norm_cast]

Depends on / 依赖: cmp_to_nat
-/
theorem cmp_eq (m n) : cmp m n = Ordering.eq ↔ m = n := by
  have := cmp_to_nat m n
  norm_cast at this
  -- Porting note: `cases` didn't rewrite at `this`, so `revert` is required.
  revert this; cases cmp m n <;> simp_all [LT.lt.ne, LT.lt.ne']

@[simp, norm_cast]
/--
theorem `cast_lt` / 定理 `cast_lt`

English:
theorem cast_lt
  given: [Semiring α] [PartialOrder α] [IsStrictOrderedRing α] {m n : PosNum}
  proof: by
  rw [← cast_to_nat m]; rw [← cast_to_nat n]; rw [Nat.cast_lt (α := α)]; rw [lt_to_nat]

@[simp, norm_cast]

中文:
定理 cast_lt
  条件: [半环 α] [偏序 α] [是StrictOrdered环 α] {m n : PosNum}
  证明: by
  rw [← cast_to_nat m]; rw [← cast_to_nat n]; rw [Nat.cast_lt (α := α)]; rw [lt_to_nat]

@[simp, norm_cast]

Depends on / 依赖: Nat.cast_lt, cast_lt, cast_to_nat, lt_to_nat
-/
theorem cast_lt [Semiring α] [PartialOrder α] [IsStrictOrderedRing α] {m n : PosNum} :
    (m : α) < n ↔ m < n := by
  rw [← cast_to_nat m]; rw [← cast_to_nat n]; rw [Nat.cast_lt (α := α)]; rw [lt_to_nat]

@[simp, norm_cast]
/--
theorem `cast_le` / 定理 `cast_le`

English:
theorem cast_le
  given: [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] {m n : PosNum}
  proof: by
  rw [← not_lt]; exact not_congr cast_lt

中文:
定理 cast_le
  条件: [半环 α] [线性序 α] [是StrictOrdered环 α] {m n : PosNum}
  证明: by
  rw [← not_lt]; exact not_congr cast_lt

Depends on / 依赖: cast_lt, not_congr, not_lt
-/
theorem cast_le [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] {m n : PosNum} :
    (m : α) <= n ↔ m <= n := by
  rw [← not_lt]; exact not_congr cast_lt

end PosNum

namespace Num

variable {α : Type*}

open PosNum

/--
theorem `bit_to_nat` / 定理 `bit_to_nat`

English:
theorem bit_to_nat
  given: (b n)
  statement: (bit b n : Nat) = Nat.bit b n
  proof: by
  cases b <;> cases n <;> simp [bit, two_mul] <;> rfl

中文:
定理 bit_to_nat
  条件: (b n)
  结论: (bit b n : 自然数) = 自然数.bit b n
  证明: by
  cases b <;> cases n <;> simp [bit, two_mul] <;> rfl

Depends on / 依赖: two_mul
-/
theorem bit_to_nat (b n) : (bit b n : Nat) = Nat.bit b n := by
  cases b <;> cases n <;> simp [bit, two_mul] <;> rfl

/--
theorem `cast_succ'` / 定理 `cast_succ'`

English:
theorem cast_succ'
  given: [AddMonoidWithOne α] (n)
  statement: (succ' n : α) = n + 1
  proof: by
  rw [← PosNum.cast_to_nat]; rw [succ'_to_nat]; rw [Nat.cast_add_one]; rw [cast_to_nat]

中文:
定理 cast_succ'
  条件: [加法带幺幺半群 α] (n)
  结论: (succ' n : α) = n + 1
  证明: by
  rw [← PosNum.cast_to_nat]; rw [succ'_to_nat]; rw [Nat.cast_add_one]; rw [cast_to_nat]

Depends on / 依赖: Nat.cast_add_one, PosNum, PosNum.cast_to_nat, _to_nat, cast_add_one, cast_to_nat
-/
theorem cast_succ' [AddMonoidWithOne α] (n) : (succ' n : α) = n + 1 := by
  rw [← PosNum.cast_to_nat]; rw [succ'_to_nat]; rw [Nat.cast_add_one]; rw [cast_to_nat]

/--
theorem `cast_succ` / 定理 `cast_succ`

English:
theorem cast_succ
  given: [AddMonoidWithOne α] (n)
  statement: (succ n : α) = n + 1
  proof: cast_succ' n

@[simp, norm_cast]

中文:
定理 cast_succ
  条件: [加法带幺幺半群 α] (n)
  结论: (succ n : α) = n + 1
  证明: cast_succ' n

@[simp, norm_cast]

Depends on / 依赖: cast_succ
-/
theorem cast_succ [AddMonoidWithOne α] (n) : (succ n : α) = n + 1 :=
  cast_succ' n

@[simp, norm_cast]
/--
theorem `cast_add` / 定理 `cast_add`

English:
theorem cast_add
  given: [AddMonoidWithOne α] (m n)
  statement: ((m + n : Num) : α) = m + n
  proof: by
  rw [← cast_to_nat]; rw [add_to_nat]; rw [Nat.cast_add]; rw [cast_to_nat]; rw [cast_to_nat]

@[simp, norm_cast]

中文:
定理 cast_add
  条件: [加法带幺幺半群 α] (m n)
  结论: ((m + n : Num) : α) = m + n
  证明: by
  rw [← cast_to_nat]; rw [add_to_nat]; rw [Nat.cast_add]; rw [cast_to_nat]; rw [cast_to_nat]

@[simp, norm_cast]

Depends on / 依赖: Nat.cast_add, add_to_nat, cast_add, cast_to_nat
-/
theorem cast_add [AddMonoidWithOne α] (m n) : ((m + n : Num) : α) = m + n := by
  rw [← cast_to_nat]; rw [add_to_nat]; rw [Nat.cast_add]; rw [cast_to_nat]; rw [cast_to_nat]

@[simp, norm_cast]
/--
theorem `cast_bit0` / 定理 `cast_bit0`

English:
theorem cast_bit0
  given: [NonAssocSemiring α] (n : Num)
  statement: (n.bit0 : α) = 2 * (n : α)
  proof: by
  rw [← bit0_of_bit0]; rw [two_mul]; rw [cast_add]

@[simp, norm_cast]

中文:
定理 cast_bit0
  条件: [非结合半环 α] (n : Num)
  结论: (n.bit0 : α) = 2 * (n : α)
  证明: by
  rw [← bit0_of_bit0]; rw [two_mul]; rw [cast_add]

@[simp, norm_cast]

Depends on / 依赖: bit0_of_bit0, cast_add, two_mul
-/
theorem cast_bit0 [NonAssocSemiring α] (n : Num) : (n.bit0 : α) = 2 * (n : α) := by
  rw [← bit0_of_bit0]; rw [two_mul]; rw [cast_add]

@[simp, norm_cast]
/--
theorem `cast_bit1` / 定理 `cast_bit1`

English:
theorem cast_bit1
  given: [NonAssocSemiring α] (n : Num)
  statement: (n.bit1 : α) = 2 * (n : α) + 1
  proof: by
  rw [← bit1_of_bit1]; rw [bit0_of_bit0]; rw [cast_add]; rw [cast_bit0]; rfl

@[simp, norm_cast]

中文:
定理 cast_bit1
  条件: [非结合半环 α] (n : Num)
  结论: (n.bit1 : α) = 2 * (n : α) + 1
  证明: by
  rw [← bit1_of_bit1]; rw [bit0_of_bit0]; rw [cast_add]; rw [cast_bit0]; rfl

@[simp, norm_cast]

Depends on / 依赖: bit0_of_bit0, bit1_of_bit1, cast_add, cast_bit0
-/
theorem cast_bit1 [NonAssocSemiring α] (n : Num) : (n.bit1 : α) = 2 * (n : α) + 1 := by
  rw [← bit1_of_bit1]; rw [bit0_of_bit0]; rw [cast_add]; rw [cast_bit0]; rfl

@[simp, norm_cast]
/--
theorem `cast_mul` / 定理 `cast_mul`

English:
theorem cast_mul
  given: [NonAssocSemiring α]
  statement: forall m n, ((m * n : Num) : α) = m * n

中文:
定理 cast_mul
  条件: [非结合半环 α]
  结论: 对任意 m n, ((m * n : Num) : α) = m * n
-/
theorem cast_mul [NonAssocSemiring α] : forall m n, ((m * n : Num) : α) = m * n
  | 0, 0 => (zero_mul _).symm
  | 0, pos _q => (zero_mul _).symm
  | pos _p, 0 => (mul_zero _).symm
  | pos _p, pos _q => PosNum.cast_mul _ _

/--
theorem `size_to_nat` / 定理 `size_to_nat`

English:
theorem size_to_nat
  statement: forall n, (size n : Nat) = Nat.size n

中文:
定理 size_to_nat
  结论: 对任意 n, (size n : 自然数) = 自然数.size n
-/
theorem size_to_nat : forall n, (size n : Nat) = Nat.size n
  | 0 => Nat.size_zero.symm
  | pos p => p.size_to_nat

/--
theorem `size_eq_natSize` / 定理 `size_eq_natSize`

English:
theorem size_eq_natSize
  statement: forall n, (size n : Nat) = natSize n

中文:
定理 size_eq_natSize
  结论: 对任意 n, (size n : 自然数) = natSize n
-/
theorem size_eq_natSize : forall n, (size n : Nat) = natSize n
  | 0 => rfl
  | pos p => p.size_eq_natSize

/--
theorem `natSize_to_nat` / 定理 `natSize_to_nat`

English:
theorem natSize_to_nat
  given: (n)
  statement: natSize n = Nat.size n
  proof: by rw [← size_eq_natSize, size_to_nat]

@[simp 999]

中文:
定理 natSize_to_nat
  条件: (n)
  结论: natSize n = 自然数.size n
  证明: by rw [← size_eq_natSize, size_to_nat]

@[simp 999]

Depends on / 依赖: size_eq_natSize, size_to_nat
-/
theorem natSize_to_nat (n) : natSize n = Nat.size n := by rw [← size_eq_natSize, size_to_nat]

@[simp 999]
/--
theorem `ofNat'_eq` / 定理 `ofNat'_eq`

English:
theorem ofNat'_eq
  statement: forall n, Num.ofNat' n = n
  proof: Nat.binaryRec (by simp) fun b n IH => by tauto

中文:
定理 of自然数'_eq
  结论: 对任意 n, Num.of自然数' n = n
  证明: Nat.binaryRec (by simp) fun b n IH => by tauto
-/
theorem ofNat'_eq : forall n, Num.ofNat' n = n :=
  Nat.binaryRec (by simp) fun b n IH => by tauto

/--
theorem `zneg_toZNum` / 定理 `zneg_toZNum`

English:
theorem zneg_toZNum
  given: (n : Num)
  statement: -n.toZNum = n.toZNumNeg
  proof: by cases n <;> rfl

中文:
定理 zneg_toZNum
  条件: (n : Num)
  结论: -n.toZNum = n.toZNumNeg
  证明: by cases n <;> rfl
-/
theorem zneg_toZNum (n : Num) : -n.toZNum = n.toZNumNeg := by cases n <;> rfl

/--
theorem `zneg_toZNumNeg` / 定理 `zneg_toZNumNeg`

English:
theorem zneg_toZNumNeg
  given: (n : Num)
  statement: -n.toZNumNeg = n.toZNum
  proof: by cases n <;> rfl

中文:
定理 zneg_toZNumNeg
  条件: (n : Num)
  结论: -n.toZNumNeg = n.toZNum
  证明: by cases n <;> rfl
-/
theorem zneg_toZNumNeg (n : Num) : -n.toZNumNeg = n.toZNum := by cases n <;> rfl

/--
theorem `toZNum_inj` / 定理 `toZNum_inj`

English:
theorem toZNum_inj
  given: {m n : Num}
  statement: m.toZNum = n.toZNum ↔ m = n
  proof: ⟨fun h => by cases m <;> cases n <;> cases h <;> rfl, congr_arg _⟩

@[simp]

中文:
定理 toZNum_inj
  条件: {m n : Num}
  结论: m.toZNum = n.toZNum ↔ m = n
  证明: ⟨fun h => by cases m <;> cases n <;> cases h <;> rfl, congr_arg _⟩

@[simp]

Depends on / 依赖: congr_arg
-/
theorem toZNum_inj {m n : Num} : m.toZNum = n.toZNum ↔ m = n :=
  ⟨fun h => by cases m <;> cases n <;> cases h <;> rfl, congr_arg _⟩

@[simp]
/--
theorem `cast_toZNum` / 定理 `cast_toZNum`

English:
theorem cast_toZNum
  given: [Zero α] [One α] [Add α] [Neg α]
  statement: forall n : Num, (n.toZNum : α) = n

中文:
定理 cast_toZNum
  条件: [零 α] [幺 α] [加法 α] [取负 α]
  结论: 对任意 n : Num, (n.toZNum : α) = n
-/
theorem cast_toZNum [Zero α] [One α] [Add α] [Neg α] : forall n : Num, (n.toZNum : α) = n
  | 0 => rfl
  | Num.pos _p => rfl

@[simp]
/--
theorem `cast_toZNumNeg` / 定理 `cast_toZNumNeg`

English:
theorem cast_toZNumNeg
  given: [SubtractionMonoid α] [One α]
  statement: forall n : Num, (n.toZNumNeg : α) = -n

中文:
定理 cast_toZNumNeg
  条件: [Subtraction幺半群 α] [幺 α]
  结论: 对任意 n : Num, (n.toZNumNeg : α) = -n
-/
theorem cast_toZNumNeg [SubtractionMonoid α] [One α] : forall n : Num, (n.toZNumNeg : α) = -n
  | 0 => neg_zero.symm
  | Num.pos _p => rfl

@[simp]
/--
theorem `add_toZNum` / 定理 `add_toZNum`

English:
theorem add_toZNum
  given: (m n : Num)
  statement: Num.toZNum (m + n) = m.toZNum + n.toZNum
  proof: by
  cases m <;> cases n <;> rfl

中文:
定理 add_toZNum
  条件: (m n : Num)
  结论: Num.toZNum (m + n) = m.toZNum + n.toZNum
  证明: by
  cases m <;> cases n <;> rfl
-/
theorem add_toZNum (m n : Num) : Num.toZNum (m + n) = m.toZNum + n.toZNum := by
  cases m <;> cases n <;> rfl

end Num

namespace PosNum

open Num

/--
theorem `pred_to_nat` / 定理 `pred_to_nat`

English:
theorem pred_to_nat
  given: {n : PosNum} (h : 1 < n)
  statement: (pred n : Nat) = Nat.pred n
  proof: by
  unfold pred
  cases e : pred' n
  · have : (1 : Nat) <= Nat.pred n := Nat.pred_le_pred ((@cast_lt Nat _ _ _).2 h)
    rw [← pred'_to_nat]; rw [e] at this
    exact absurd this (by decide)
  · rw [← pred'_to_nat, e]
    rfl

中文:
定理 pred_to_nat
  条件: {n : PosNum} (h : 1 < n)
  结论: (pred n : 自然数) = 自然数.pred n
  证明: by
  unfold pred
  cases e : pred' n
  · have : (1 : Nat) <= Nat.pred n := Nat.pred_le_pred ((@cast_lt Nat _ _ _).2 h)
    rw [← pred'_to_nat]; rw [e] at this
    exact absurd this (by decide)
  · rw [← pred'_to_nat, e]
    rfl

Depends on / 依赖: Nat.pred, Nat.pred_le_pred, _to_nat, absurd, cast_lt, pred_le_pred
-/
theorem pred_to_nat {n : PosNum} (h : 1 < n) : (pred n : Nat) = Nat.pred n := by
  unfold pred
  cases e : pred' n
  · have : (1 : Nat) <= Nat.pred n := Nat.pred_le_pred ((@cast_lt Nat _ _ _).2 h)
    rw [← pred'_to_nat]; rw [e] at this
    exact absurd this (by decide)
  · rw [← pred'_to_nat, e]
    rfl

/--
theorem `sub'_one` / 定理 `sub'_one`

English:
theorem sub'_one
  given: (a : PosNum)
  statement: sub' a 1 = (pred' a).toZNum
  proof: by cases a <;> rfl

中文:
定理 sub'_one
  条件: (a : PosNum)
  结论: sub' a 1 = (pred' a).toZNum
  证明: by cases a <;> rfl
-/
theorem sub'_one (a : PosNum) : sub' a 1 = (pred' a).toZNum := by cases a <;> rfl

/--
theorem `one_sub'` / 定理 `one_sub'`

English:
theorem one_sub'
  given: (a : PosNum)
  statement: sub' 1 a = (pred' a).toZNumNeg
  proof: by cases a <;> rfl

中文:
定理 one_sub'
  条件: (a : PosNum)
  结论: sub' 1 a = (pred' a).toZNumNeg
  证明: by cases a <;> rfl
-/
theorem one_sub' (a : PosNum) : sub' 1 a = (pred' a).toZNumNeg := by cases a <;> rfl

/--
theorem `lt_iff_cmp` / 定理 `lt_iff_cmp`

English:
theorem lt_iff_cmp
  given: {m n}
  statement: m < n ↔ cmp m n = Ordering.lt
  proof: Iff.rfl

中文:
定理 lt_iff_cmp
  条件: {m n}
  结论: m < n ↔ cmp m n = Ordering.lt
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem lt_iff_cmp {m n} : m < n ↔ cmp m n = Ordering.lt :=
  Iff.rfl

/--
theorem `le_iff_cmp` / 定理 `le_iff_cmp`

English:
theorem le_iff_cmp
  given: {m n}
  statement: m <= n ↔ cmp m n != Ordering.gt
  proof: not_congr lt_iff_cmp.trans by rw [← cmp_swap]; cases cmp m n <;> decide

中文:
定理 le_iff_cmp
  条件: {m n}
  结论: m <= n ↔ cmp m n != Ordering.gt
  证明: not_congr lt_iff_cmp.trans by rw [← cmp_swap]; cases cmp m n <;> decide

Depends on / 依赖: IsScalarTower, cmp_swap, lt_iff_cmp, lt_iff_cmp.trans, not_congr
-/
theorem le_iff_cmp {m n} : m <= n ↔ cmp m n != Ordering.gt :=
not_congr lt_iff_cmp.trans by rw [← cmp_swap]; cases cmp m n <;> decide

end PosNum

namespace Num

variable {α : Type*}

open PosNum

/--
theorem `pred_to_nat` / 定理 `pred_to_nat`

English:
theorem pred_to_nat
  statement: forall n : Num, (pred n : Nat) = Nat.pred n

中文:
定理 pred_to_nat
  结论: 对任意 n : Num, (pred n : 自然数) = 自然数.pred n
-/
theorem pred_to_nat : forall n : Num, (pred n : Nat) = Nat.pred n
  | 0 => rfl
  | pos p => by rw [pred, PosNum.pred'_to_nat]; rfl

/--
theorem `ppred_to_nat` / 定理 `ppred_to_nat`

English:
theorem ppred_to_nat
  statement: forall n : Num, (↑) < > ppred n = Nat.ppred n

中文:
定理 ppred_to_nat
  结论: 对任意 n : Num, (↑) < > ppred n = 自然数.ppred n
-/
theorem ppred_to_nat : forall n : Num, (↑) < > ppred n = Nat.ppred n
  | 0 => rfl
  | pos p => by
    rw [ppred]; rw [Option.map_eq_map]; rw [Option.map_some]; rw [Nat.ppred_eq_some.2]
    rw [PosNum.pred'_to_nat]; rw [Nat.succ_pred_eq_of_pos (PosNum.to_nat_pos _)]
    rfl

/--
theorem `cmp_swap` / 定理 `cmp_swap`

English:
theorem cmp_swap
  given: (m n)
  statement: (cmp m n).swap = cmp n m
  proof: by
  cases m <;> cases n <;> try { rfl }; apply PosNum.cmp_swap

中文:
定理 cmp_swap
  条件: (m n)
  结论: (cmp m n).swap = cmp n m
  证明: by
  cases m <;> cases n <;> try { rfl }; apply PosNum.cmp_swap

Depends on / 依赖: PosNum, PosNum.cmp_swap, cmp_swap
-/
theorem cmp_swap (m n) : (cmp m n).swap = cmp n m := by
  cases m <;> cases n <;> try { rfl }; apply PosNum.cmp_swap

/--
theorem `cmp_eq` / 定理 `cmp_eq`

English:
theorem cmp_eq
  given: (m n)
  statement: cmp m n = Ordering.eq ↔ m = n
  proof: by
  have := cmp_to_nat m n
  norm_cast at this
  -- Porting note: `cases` didn't rewrite at `this`, so `revert` is required.
  revert this; cases cmp m n <;> simp_all [LT.lt.ne, LT.lt.ne']

@[simp, norm_cast]

中文:
定理 cmp_eq
  条件: (m n)
  结论: cmp m n = Ordering.eq ↔ m = n
  证明: by
  have := cmp_to_nat m n
  norm_cast at this
  -- Porting note: `cases` didn't rewrite at `this`, so `revert` is required.
  revert this; cases cmp m n <;> simp_all [LT.lt.ne, LT.lt.ne']

@[simp, norm_cast]

Depends on / 依赖: cmp_to_nat
-/
theorem cmp_eq (m n) : cmp m n = Ordering.eq ↔ m = n := by
  have := cmp_to_nat m n
  norm_cast at this
  -- Porting note: `cases` didn't rewrite at `this`, so `revert` is required.
  revert this; cases cmp m n <;> simp_all [LT.lt.ne, LT.lt.ne']

@[simp, norm_cast]
/--
theorem `cast_lt` / 定理 `cast_lt`

English:
theorem cast_lt
  given: [Semiring α] [PartialOrder α] [IsStrictOrderedRing α] {m n : Num}
  proof: by
  rw [← cast_to_nat m]; rw [← cast_to_nat n]; rw [Nat.cast_lt (α := α)]; rw [lt_to_nat]

@[simp, norm_cast]

中文:
定理 cast_lt
  条件: [半环 α] [偏序 α] [是StrictOrdered环 α] {m n : Num}
  证明: by
  rw [← cast_to_nat m]; rw [← cast_to_nat n]; rw [Nat.cast_lt (α := α)]; rw [lt_to_nat]

@[simp, norm_cast]

Depends on / 依赖: Nat.cast_lt, cast_lt, cast_to_nat, lt_to_nat
-/
theorem cast_lt [Semiring α] [PartialOrder α] [IsStrictOrderedRing α] {m n : Num} :
    (m : α) < n ↔ m < n := by
  rw [← cast_to_nat m]; rw [← cast_to_nat n]; rw [Nat.cast_lt (α := α)]; rw [lt_to_nat]

@[simp, norm_cast]
/--
theorem `cast_le` / 定理 `cast_le`

English:
theorem cast_le
  given: [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] {m n : Num}
  proof: by
  rw [← not_lt]; exact not_congr cast_lt

@[simp, norm_cast]

中文:
定理 cast_le
  条件: [半环 α] [线性序 α] [是StrictOrdered环 α] {m n : Num}
  证明: by
  rw [← not_lt]; exact not_congr cast_lt

@[simp, norm_cast]

Depends on / 依赖: cast_lt, not_congr, not_lt
-/
theorem cast_le [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] {m n : Num} :
    (m : α) <= n ↔ m <= n := by
  rw [← not_lt]; exact not_congr cast_lt

@[simp, norm_cast]
/--
theorem `cast_inj` / 定理 `cast_inj`

English:
theorem cast_inj
  given: [Semiring α] [PartialOrder α] [IsStrictOrderedRing α] {m n : Num}
  proof: by
  rw [← cast_to_nat m]; rw [← cast_to_nat n]; rw [Nat.cast_inj]; rw [to_nat_inj]

中文:
定理 cast_inj
  条件: [半环 α] [偏序 α] [是StrictOrdered环 α] {m n : Num}
  证明: by
  rw [← cast_to_nat m]; rw [← cast_to_nat n]; rw [Nat.cast_inj]; rw [to_nat_inj]

Depends on / 依赖: Nat.cast_inj, cast_inj, cast_to_nat, to_nat_inj
-/
theorem cast_inj [Semiring α] [PartialOrder α] [IsStrictOrderedRing α] {m n : Num} :
    (m : α) = n ↔ m = n := by
  rw [← cast_to_nat m]; rw [← cast_to_nat n]; rw [Nat.cast_inj]; rw [to_nat_inj]

/--
theorem `lt_iff_cmp` / 定理 `lt_iff_cmp`

English:
theorem lt_iff_cmp
  given: {m n}
  statement: m < n ↔ cmp m n = Ordering.lt
  proof: Iff.rfl

中文:
定理 lt_iff_cmp
  条件: {m n}
  结论: m < n ↔ cmp m n = Ordering.lt
  证明: Iff.rfl

Depends on / 依赖: AlgebraicClosure, Iff.rfl, RingHom, RingHom.injective, algebraMap, charP_of_injective_algebraMap, injective
-/
theorem lt_iff_cmp {m n} : m < n ↔ cmp m n = Ordering.lt :=
  Iff.rfl

/--
theorem `le_iff_cmp` / 定理 `le_iff_cmp`

English:
theorem le_iff_cmp
  given: {m n}
  statement: m <= n ↔ cmp m n != Ordering.gt
  proof: not_congr lt_iff_cmp.trans by rw [← cmp_swap]; cases cmp m n <;> decide

中文:
定理 le_iff_cmp
  条件: {m n}
  结论: m <= n ↔ cmp m n != Ordering.gt
  证明: not_congr lt_iff_cmp.trans by rw [← cmp_swap]; cases cmp m n <;> decide

Depends on / 依赖: cmp_swap, lt_iff_cmp, lt_iff_cmp.trans, not_congr
-/
theorem le_iff_cmp {m n} : m <= n ↔ cmp m n != Ordering.gt :=
not_congr lt_iff_cmp.trans by rw [← cmp_swap]; cases cmp m n <;> decide

/--
theorem `castNum_eq_bitwise` / 定理 `castNum_eq_bitwise`

English:
theorem castNum_eq_bitwise
  statement: {f : Num -> Num -> Num} {g : Bool -> Bool -> Bool}
  proof: by
  intro m n
  obtain - | m := m <;> obtain - | n := n <;>
      try simp only [show zero = 0 from rfl, show ((0 : Num) : Nat) = 0 from rfl]
  · rw [f00, Nat.bitwise_zero]; rfl
  · rw [f0n, Nat.bitwise_zero_left]
    cases g false true <;> rfl
  · rw [fn0, Nat.bitwise_zero_right]
    cases g true 

中文:
定理 castNum_eq_bitwise
  结论: {f : Num -> Num -> Num} {g : 布尔值 -> 布尔值 -> 布尔值}
  证明: by
  intro m n
  obtain - | m := m <;> obtain - | n := n <;>
      try simp only [show zero = 0 from rfl, show ((0 : Num) : Nat) = 0 from rfl]
  · rw [f00, Nat.bitwise_zero]; rfl
  · rw [f0n, Nat.bitwise_zero_left]
    cases g false true <;> rfl
  · rw [fn0, Nat.bitwise_zero_right]
    cases g true 

Depends on / 依赖: Nat.bit, Nat.bitwise_zero, Nat.bitwise_zero_left, Nat.bitwise_zero_right, PosNum, PosNum.bit, bitwise_zero, bitwise_zero_left, bitwise_zero_right
-/
theorem castNum_eq_bitwise {f : Num -> Num -> Num} {g : Bool -> Bool -> Bool}
    (p : PosNum -> PosNum -> Num)
    (gff : g false false = false) (f00 : f 0 0 = 0)
    (f0n : forall n, f 0 (pos n) = cond (g false true) (pos n) 0)
    (fn0 : forall n, f (pos n) 0 = cond (g true false) (pos n) 0)
    (fnn : forall m n, f (pos m) (pos n) = p m n) (p11 : p 1 1 = cond (g true true) 1 0)
    (p1b : forall b n, p 1 (PosNum.bit b n) = bit (g true b) (cond (g false true) (pos n) 0))
    (pb1 : forall a m, p (PosNum.bit a m) 1 = bit (g a true) (cond (g true false) (pos m) 0))
    (pbb : forall a b m n, p (PosNum.bit a m) (PosNum.bit b n) = bit (g a b) (p m n)) :
    forall m n : Num, (f m n : Nat) = Nat.bitwise g m n := by
  intro m n
  obtain - | m := m <;> obtain - | n := n <;>
      try simp only [show zero = 0 from rfl, show ((0 : Num) : Nat) = 0 from rfl]
  · rw [f00, Nat.bitwise_zero]; rfl
  · rw [f0n, Nat.bitwise_zero_left]
    cases g false true <;> rfl
  · rw [fn0, Nat.bitwise_zero_right]
    cases g true false <;> rfl
  · rw [fnn]
    have this b (n : PosNum) : (cond b (↑n) 0 : Nat) = ↑(cond b (pos n) 0 : Num) := by
      cases b <;> rfl
    have this' b (n : PosNum) : ↑(pos (PosNum.bit b n)) = Nat.bit b ↑n := by
      cases b <;> simp
    induction m generalizing n with | one => ?_ | bit1 m IH => ?_ | bit0 m IH => ?_ <;>
    obtain - | n | n := n
    any_goals simp only [show one = 1 from rfl, show pos 1 = 1 from rfl,
      show PosNum.bit0 = PosNum.bit false from rfl, show PosNum.bit1 = PosNum.bit true from rfl,
      show ((1 : Num) : Nat) = Nat.bit true 0 from rfl]
    all_goals
      repeat rw [this']
      rw [Nat.bitwise_bit gff]
    any_goals rw [Nat.bitwise_zero, p11]; cases g true true <;> rfl
    any_goals rw [Nat.bitwise_zero_left, ← Bool.cond_eq_ite, this, ← bit_to_nat, p1b]
    any_goals rw [Nat.bitwise_zero_right, ← Bool.cond_eq_ite, this, ← bit_to_nat, pb1]
    all_goals
      rw [← show forall n : PosNum]; rw [↑(p m n) = Nat.bitwise g ↑m ↑n from IH]
      rw [← bit_to_nat]; rw [pbb]

@[simp, norm_cast]
/--
theorem `castNum_or` / 定理 `castNum_or`

English:
theorem castNum_or
  statement: forall m n : Num, ↑(m ||| n) = (↑m ||| ↑n : Nat)
  proof: by
  apply castNum_eq_bitwise fun x y => pos (PosNum.lor x y) <;>
    (try rintro (_ | _)) <;> (try rintro (_ | _)) <;> intros <;> rfl

@[simp, norm_cast]

中文:
定理 castNum_or
  结论: 对任意 m n : Num, ↑(m ||| n) = (↑m ||| ↑n : 自然数)
  证明: by
  apply castNum_eq_bitwise fun x y => pos (PosNum.lor x y) <;>
    (try rintro (_ | _)) <;> (try rintro (_ | _)) <;> intros <;> rfl

@[simp, norm_cast]

Depends on / 依赖: PosNum, PosNum.lor, castNum_eq_bitwise, intros
-/
theorem castNum_or : forall m n : Num, ↑(m ||| n) = (↑m ||| ↑n : Nat) := by
  apply castNum_eq_bitwise fun x y => pos (PosNum.lor x y) <;>
    (try rintro (_ | _)) <;> (try rintro (_ | _)) <;> intros <;> rfl

@[simp, norm_cast]
/--
theorem `castNum_and` / 定理 `castNum_and`

English:
theorem castNum_and
  statement: forall m n : Num, ↑(m &&& n) = (↑m &&& ↑n : Nat)
  proof: by
  apply castNum_eq_bitwise PosNum.land <;> intros <;> (try cases_type* Bool) <;> rfl

@[simp, norm_cast]

中文:
定理 castNum_and
  结论: 对任意 m n : Num, ↑(m &&& n) = (↑m &&& ↑n : 自然数)
  证明: by
  apply castNum_eq_bitwise PosNum.land <;> intros <;> (try cases_type* Bool) <;> rfl

@[simp, norm_cast]

Depends on / 依赖: PosNum, PosNum.land, cases_type, castNum_eq_bitwise, intros
-/
theorem castNum_and : forall m n : Num, ↑(m &&& n) = (↑m &&& ↑n : Nat) := by
  apply castNum_eq_bitwise PosNum.land <;> intros <;> (try cases_type* Bool) <;> rfl

@[simp, norm_cast]
/--
theorem `castNum_ldiff` / 定理 `castNum_ldiff`

English:
theorem castNum_ldiff
  statement: forall m n : Num, (ldiff m n : Nat) = Nat.ldiff m n
  proof: by
  apply castNum_eq_bitwise PosNum.ldiff <;> intros <;> (try cases_type* Bool) <;> rfl

@[simp, norm_cast]

中文:
定理 castNum_ldiff
  结论: 对任意 m n : Num, (ldiff m n : 自然数) = 自然数.ldiff m n
  证明: by
  apply castNum_eq_bitwise PosNum.ldiff <;> intros <;> (try cases_type* Bool) <;> rfl

@[simp, norm_cast]

Depends on / 依赖: PosNum, PosNum.ldiff, cases_type, castNum_eq_bitwise, intros
-/
theorem castNum_ldiff : forall m n : Num, (ldiff m n : Nat) = Nat.ldiff m n := by
  apply castNum_eq_bitwise PosNum.ldiff <;> intros <;> (try cases_type* Bool) <;> rfl

@[simp, norm_cast]
/--
theorem `castNum_xor` / 定理 `castNum_xor`

English:
theorem castNum_xor
  statement: forall m n : Num, ↑(m ^^^ n) = (↑m ^^^ ↑n : Nat)
  proof: by
  apply castNum_eq_bitwise PosNum.lxor <;> intros <;> (try cases_type* Bool) <;> rfl

@[simp, norm_cast]

中文:
定理 castNum_xor
  结论: 对任意 m n : Num, ↑(m ^^^ n) = (↑m ^^^ ↑n : 自然数)
  证明: by
  apply castNum_eq_bitwise PosNum.lxor <;> intros <;> (try cases_type* Bool) <;> rfl

@[simp, norm_cast]

Depends on / 依赖: PosNum, PosNum.lxor, cases_type, castNum_eq_bitwise, intros
-/
theorem castNum_xor : forall m n : Num, ↑(m ^^^ n) = (↑m ^^^ ↑n : Nat) := by
  apply castNum_eq_bitwise PosNum.lxor <;> intros <;> (try cases_type* Bool) <;> rfl

@[simp, norm_cast]
/--
theorem `castNum_shiftLeft` / 定理 `castNum_shiftLeft`

English:
theorem castNum_shiftLeft
  given: (m : Num) (n : Nat)
  statement: ↑(m <<< n) = (m : Nat) <<< (n : Nat)
  proof: by
  cases m <;> dsimp only [← shiftl_eq_shiftLeft, shiftl]
  · symm
    apply Nat.zero_shiftLeft
  simp only [cast_pos]
  induction n with
  | zero => rfl
  | succ n IH =>
    simp [PosNum.shiftl_succ_eq_bit0_shiftl, Nat.shiftLeft_succ, IH, mul_comm,
      -shiftl_eq_shiftLeft, -PosNum.shiftl_eq_sh

中文:
定理 castNum_shiftLeft
  条件: (m : Num) (n : 自然数)
  结论: ↑(m <<< n) = (m : 自然数) <<< (n : 自然数)
  证明: by
  cases m <;> dsimp only [← shiftl_eq_shiftLeft, shiftl]
  · symm
    apply Nat.zero_shiftLeft
  simp only [cast_pos]
  induction n with
  | zero => rfl
  | succ n IH =>
    simp [PosNum.shiftl_succ_eq_bit0_shiftl, Nat.shiftLeft_succ, IH, mul_comm,
      -shiftl_eq_shiftLeft, -PosNum.shiftl_eq_sh

Depends on / 依赖: Nat.shiftLeft_succ, Nat.zero_shiftLeft, PosNum, PosNum.shiftl_eq_shiftLeft, PosNum.shiftl_succ_eq_bit0_shiftl, cast_pos, mul_comm, mul_two, shiftLeft_succ, shiftl, shiftl_eq_shiftLeft, shiftl_succ_eq_bit0_shiftl, zero_shiftLeft
-/
theorem castNum_shiftLeft (m : Num) (n : Nat) : ↑(m <<< n) = (m : Nat) <<< (n : Nat) := by
  cases m <;> dsimp only [← shiftl_eq_shiftLeft, shiftl]
  · symm
    apply Nat.zero_shiftLeft
  simp only [cast_pos]
  induction n with
  | zero => rfl
  | succ n IH =>
    simp [PosNum.shiftl_succ_eq_bit0_shiftl, Nat.shiftLeft_succ, IH, mul_comm,
      -shiftl_eq_shiftLeft, -PosNum.shiftl_eq_shiftLeft, mul_two]

@[simp, norm_cast]
/--
theorem `castNum_shiftRight` / 定理 `castNum_shiftRight`

English:
theorem castNum_shiftRight
  given: (m : Num) (n : Nat)
  statement: ↑(m >>> n) = (m : Nat) >>> (n : Nat)
  proof: by
  obtain - | m := m <;> dsimp only [← shiftr_eq_shiftRight, shiftr]
  · symm
    apply Nat.zero_shiftRight
  induction n generalizing m with
  | zero => cases m <;> rfl
  | succ n IH => ?_
  have hdiv2 : forall m, Nat.div2 (m + m) = m := by intro; rw [Nat.div2_val]; lia
  obtain - | m | m := m <;

中文:
定理 castNum_shiftRight
  条件: (m : Num) (n : 自然数)
  结论: ↑(m >>> n) = (m : 自然数) >>> (n : 自然数)
  证明: by
  obtain - | m := m <;> dsimp only [← shiftr_eq_shiftRight, shiftr]
  · symm
    apply Nat.zero_shiftRight
  induction n generalizing m with
  | zero => cases m <;> rfl
  | succ n IH => ?_
  have hdiv2 : forall m, Nat.div2 (m + m) = m := by intro; rw [Nat.div2_val]; lia
  obtain - | m | m := m <;

Depends on / 依赖: Nat.div2, Nat.div2_val, Nat.div_eq_of_lt, Nat.shiftRight, Nat.shiftRight_eq_div_pow, Nat.zero_shiftRight, PosNum, PosNum.shiftr, PosNum.shiftr_eq_shiftRight, add_co, div2_val, div_eq_of_lt, generalizing, shiftRight, shiftRight_eq_div_pow, shiftr, shiftr_eq_shiftRight, zero_shiftRight
-/
theorem castNum_shiftRight (m : Num) (n : Nat) : ↑(m >>> n) = (m : Nat) >>> (n : Nat) := by
  obtain - | m := m <;> dsimp only [← shiftr_eq_shiftRight, shiftr]
  · symm
    apply Nat.zero_shiftRight
  induction n generalizing m with
  | zero => cases m <;> rfl
  | succ n IH => ?_
  have hdiv2 : forall m, Nat.div2 (m + m) = m := by intro; rw [Nat.div2_val]; lia
  obtain - | m | m := m <;> dsimp only [PosNum.shiftr, ← PosNum.shiftr_eq_shiftRight]
  · rw [Nat.shiftRight_eq_div_pow]
    symm
    apply Nat.div_eq_of_lt
    simp
  · trans
    · apply IH
    change Nat.shiftRight m n = Nat.shiftRight (m + m + 1) (n + 1)
    rw [add_comm n 1]; rw [@Nat.shiftRight_eq _ (1 + n)]; rw [Nat.shiftRight_add]
    apply congr_arg fun x => Nat.shiftRight x n
    simp [-add_assoc, Nat.shiftRight_succ, Nat.shiftRight_zero, ← Nat.div2_val, hdiv2]
  · trans
    · apply IH
    change Nat.shiftRight m n = Nat.shiftRight (m + m) (n + 1)
    rw [add_comm n 1]; rw [@Nat.shiftRight_eq _ (1 + n)]; rw [Nat.shiftRight_add]
    apply congr_arg fun x => Nat.shiftRight x n
    simp [-add_assoc, Nat.shiftRight_succ, Nat.shiftRight_zero, ← Nat.div2_val, hdiv2]

@[simp]
/--
theorem `castNum_testBit` / 定理 `castNum_testBit`

English:
theorem castNum_testBit
  given: (m n)
  statement: testBit m n = Nat.testBit m n
  proof: by
  cases m with dsimp only [testBit]
  | zero =>
    rw [show (Num.zero : Nat) = 0 from rfl]; rw [Nat.zero_testBit]
  | pos m =>
    rw [cast_pos]
    induction n generalizing m <;> obtain - | m | m := m
        <;> simp only [PosNum.testBit]
    · rfl
    · rw [PosNum.cast_bit1, ← two_mul, ← cong

中文:
定理 castNum_testBit
  条件: (m n)
  结论: testBit m n = 自然数.testBit m n
  证明: by
  cases m with dsimp only [testBit]
  | zero =>
    rw [show (Num.zero : Nat) = 0 from rfl]; rw [Nat.zero_testBit]
  | pos m =>
    rw [cast_pos]
    induction n generalizing m <;> obtain - | m | m := m
        <;> simp only [PosNum.testBit]
    · rfl
    · rw [PosNum.cast_bit1, ← two_mul, ← cong

Depends on / 依赖: Nat.bit_false, Nat.bit_true, Nat.testBit_add_one, Nat.testBit_bit_zero, Nat.zero_testBit, Num.zero, PosNum, PosNum.cast_bit0, PosNum.cast_bit1, PosNum.testBit, bit_false, bit_true, cast_bit0, cast_bit1, cast_pos, congr_fun, generalizing, succ.bit1, testBit, testBit_add_one
-/
theorem castNum_testBit (m n) : testBit m n = Nat.testBit m n := by
  cases m with dsimp only [testBit]
  | zero =>
    rw [show (Num.zero : Nat) = 0 from rfl]; rw [Nat.zero_testBit]
  | pos m =>
    rw [cast_pos]
    induction n generalizing m <;> obtain - | m | m := m
        <;> simp only [PosNum.testBit]
    · rfl
    · rw [PosNum.cast_bit1, ← two_mul, ← congr_fun Nat.bit_true, Nat.testBit_bit_zero]
    · rw [PosNum.cast_bit0, ← two_mul, ← congr_fun Nat.bit_false, Nat.testBit_bit_zero]
    · simp [Nat.testBit_add_one]
    case succ.bit1 n IH =>
      rw [PosNum.cast_bit1]; rw [← two_mul]; rw [← congr_fun Nat.bit_true]; rw [Nat.testBit_bit_succ]; rw [IH]
    case succ.bit0 n IH =>
      rw [PosNum.cast_bit0]; rw [← two_mul]; rw [← congr_fun Nat.bit_false]; rw [Nat.testBit_bit_succ]; rw [IH]

end Num

namespace Int

/--
Definition of `ofSnum` / `ofSnum` 的定义

English:
definition ofSnum
  signature: : SNum -> Int
  body: SNum.rec' (fun a => cond a (-1) 0) fun a _p IH => cond a (2 * IH + 1) (2 * IH)

中文:
定义 ofSnum
  签名: : SNum -> 整数
  定义体: SNum.rec' (fun a => cond a (-1) 0) fun a _p IH => cond a (2 * IH + 1) (2 * IH)

Depends on / 依赖: SNum.rec
-/
def ofSnum : SNum -> Int :=
  SNum.rec' (fun a => cond a (-1) 0) fun a _p IH => cond a (2 * IH + 1) (2 * IH)

/--
Instance `snumCoe` / 实例 `snumCoe`

English:
instance snumCoe
  signature: : Coe SNum Int
  body: ⟨ofSnum⟩

中文:
实例 snumCoe
  签名: : Coe SNum 整数
  定义体: ⟨ofSnum⟩

Depends on / 依赖: ofSnum
-/
instance snumCoe : Coe SNum Int :=
  ⟨ofSnum⟩

end Int

/--
Instance `SNum.lt` / 实例 `SNum.lt`

English:
instance SNum.lt
  signature: : LT SNum
  body: ⟨fun a b => (a : Int) < b⟩

中文:
实例 SNum.lt
  签名: : LT SNum
  定义体: ⟨fun a b => (a : Int) < b⟩
-/
instance SNum.lt : LT SNum :=
  ⟨fun a b => (a : Int) < b⟩

/--
Instance `SNum.le` / 实例 `SNum.le`

English:
instance SNum.le
  signature: : LE SNum
  body: ⟨fun a b => (a : Int) <= b⟩

中文:
实例 SNum.le
  签名: : LE SNum
  定义体: ⟨fun a b => (a : Int) <= b⟩
-/
instance SNum.le : LE SNum :=
  ⟨fun a b => (a : Int) <= b⟩
