/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Order.Ring.Cast
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Num.Lemmas

/-!
# Properties of the `ZNum` representation of integers

This file was split from `Mathlib/Data/Num/Lemmas.lean` to keep the former under 1500 lines.
-/

public section

open Int

attribute [local simp] add_assoc

namespace ZNum

variable {α : Type*}

open PosNum

@[simp, norm_cast]
/--
theorem `cast_zero` / 定理 `cast_zero`

English:
theorem cast_zero
  given: [Zero α] [One α] [Add α] [Neg α]
  statement: ((0 : ZNum) : α) = 0
  proof: rfl

@[simp]

中文:
定理 cast_zero
  条件: [零 α] [幺 α] [加法 α] [取负 α]
  结论: ((0 : ZNum) : α) = 0
  证明: rfl

@[simp]
-/
theorem cast_zero [Zero α] [One α] [Add α] [Neg α] : ((0 : ZNum) : α) = 0 :=
  rfl

@[simp]
/--
theorem `cast_zero'` / 定理 `cast_zero'`

English:
theorem cast_zero'
  given: [Zero α] [One α] [Add α] [Neg α]
  statement: (ZNum.zero : α) = 0
  proof: rfl

@[simp, norm_cast]

中文:
定理 cast_zero'
  条件: [零 α] [幺 α] [加法 α] [取负 α]
  结论: (ZNum.zero : α) = 0
  证明: rfl

@[simp, norm_cast]
-/
theorem cast_zero' [Zero α] [One α] [Add α] [Neg α] : (ZNum.zero : α) = 0 :=
  rfl

@[simp, norm_cast]
/--
theorem `cast_one` / 定理 `cast_one`

English:
theorem cast_one
  given: [Zero α] [One α] [Add α] [Neg α]
  statement: ((1 : ZNum) : α) = 1
  proof: rfl

@[simp]

中文:
定理 cast_one
  条件: [零 α] [幺 α] [加法 α] [取负 α]
  结论: ((1 : ZNum) : α) = 1
  证明: rfl

@[simp]
-/
theorem cast_one [Zero α] [One α] [Add α] [Neg α] : ((1 : ZNum) : α) = 1 :=
  rfl

@[simp]
/--
theorem `cast_pos` / 定理 `cast_pos`

English:
theorem cast_pos
  given: [Zero α] [One α] [Add α] [Neg α] (n : PosNum)
  statement: (pos n : α) = n
  proof: rfl

@[simp]

中文:
定理 cast_pos
  条件: [零 α] [幺 α] [加法 α] [取负 α] (n : PosNum)
  结论: (pos n : α) = n
  证明: rfl

@[simp]
-/
theorem cast_pos [Zero α] [One α] [Add α] [Neg α] (n : PosNum) : (pos n : α) = n :=
  rfl

@[simp]
/--
theorem `cast_neg` / 定理 `cast_neg`

English:
theorem cast_neg
  given: [Zero α] [One α] [Add α] [Neg α] (n : PosNum)
  statement: (neg n : α) = -n
  proof: rfl

@[simp, norm_cast]

中文:
定理 cast_neg
  条件: [零 α] [幺 α] [加法 α] [取负 α] (n : PosNum)
  结论: (neg n : α) = -n
  证明: rfl

@[simp, norm_cast]
-/
theorem cast_neg [Zero α] [One α] [Add α] [Neg α] (n : PosNum) : (neg n : α) = -n :=
  rfl

@[simp, norm_cast]
/--
theorem `cast_zneg` / 定理 `cast_zneg`

English:
theorem cast_zneg
  given: [SubtractionMonoid α] [One α]
  statement: forall n, ((-n : ZNum) : α) = -n

中文:
定理 cast_zneg
  条件: [Subtraction幺半群 α] [幺 α]
  结论: 对任意 n, ((-n : ZNum) : α) = -n
-/
theorem cast_zneg [SubtractionMonoid α] [One α] : forall n, ((-n : ZNum) : α) = -n
  | 0 => neg_zero.symm
  | pos _p => rfl
  | neg _p => (neg_neg _).symm

/--
theorem `neg_zero` / 定理 `neg_zero`

English:
theorem neg_zero
  statement: (-0 : ZNum) = 0
  proof: rfl

中文:
定理 neg_zero
  结论: (-0 : ZNum) = 0
  证明: rfl
-/
theorem neg_zero : (-0 : ZNum) = 0 :=
  rfl

/--
theorem `zneg_pos` / 定理 `zneg_pos`

English:
theorem zneg_pos
  given: (n : PosNum)
  statement: -pos n = neg n
  proof: rfl

中文:
定理 zneg_pos
  条件: (n : PosNum)
  结论: -pos n = neg n
  证明: rfl
-/
theorem zneg_pos (n : PosNum) : -pos n = neg n :=
  rfl

/--
theorem `zneg_neg` / 定理 `zneg_neg`

English:
theorem zneg_neg
  given: (n : PosNum)
  statement: -neg n = pos n
  proof: rfl

中文:
定理 zneg_neg
  条件: (n : PosNum)
  结论: -neg n = pos n
  证明: rfl
-/
theorem zneg_neg (n : PosNum) : -neg n = pos n :=
  rfl

/--
theorem `zneg_zneg` / 定理 `zneg_zneg`

English:
theorem zneg_zneg
  given: (n : ZNum)
  statement: - -n = n
  proof: by cases n <;> rfl

中文:
定理 zneg_zneg
  条件: (n : ZNum)
  结论: - -n = n
  证明: by cases n <;> rfl
-/
theorem zneg_zneg (n : ZNum) : - -n = n := by cases n <;> rfl

/--
theorem `zneg_bit1` / 定理 `zneg_bit1`

English:
theorem zneg_bit1
  given: (n : ZNum)
  statement: -n.bit1 = (-n).bitm1
  proof: by cases n <;> rfl

中文:
定理 zneg_bit1
  条件: (n : ZNum)
  结论: -n.bit1 = (-n).bitm1
  证明: by cases n <;> rfl

Depends on / 依赖: Algebra, IsAlgClosure, IsAlgClosure.normal, normal
-/
theorem zneg_bit1 (n : ZNum) : -n.bit1 = (-n).bitm1 := by cases n <;> rfl

/--
theorem `zneg_bitm1` / 定理 `zneg_bitm1`

English:
theorem zneg_bitm1
  given: (n : ZNum)
  statement: -n.bitm1 = (-n).bit1
  proof: by cases n <;> rfl

中文:
定理 zneg_bitm1
  条件: (n : ZNum)
  结论: -n.bitm1 = (-n).bit1
  证明: by cases n <;> rfl

Depends on / 依赖: Algebra, IsAlgClosure, IsAlgClosure.separable, separable
-/
theorem zneg_bitm1 (n : ZNum) : -n.bitm1 = (-n).bit1 := by cases n <;> rfl

/--
theorem `zneg_succ` / 定理 `zneg_succ`

English:
theorem zneg_succ
  given: (n : ZNum)
  statement: -n.succ = (-n).pred
  proof: by
  cases n <;> try { rfl }; rw [succ, Num.zneg_toZNumNeg]; rfl

中文:
定理 zneg_succ
  条件: (n : ZNum)
  结论: -n.succ = (-n).pred
  证明: by
  cases n <;> try { rfl }; rw [succ, Num.zneg_toZNumNeg]; rfl

Depends on / 依赖: Num.zneg_toZNumNeg, zneg_toZNumNeg
-/
theorem zneg_succ (n : ZNum) : -n.succ = (-n).pred := by
  cases n <;> try { rfl }; rw [succ, Num.zneg_toZNumNeg]; rfl

/--
theorem `zneg_pred` / 定理 `zneg_pred`

English:
theorem zneg_pred
  given: (n : ZNum)
  statement: -n.pred = (-n).succ
  proof: by
  rw [← zneg_zneg (succ (-n))]; rw [zneg_succ]; rw [zneg_zneg]

@[simp]

中文:
定理 zneg_pred
  条件: (n : ZNum)
  结论: -n.pred = (-n).succ
  证明: by
  rw [← zneg_zneg (succ (-n))]; rw [zneg_succ]; rw [zneg_zneg]

@[simp]

Depends on / 依赖: zneg_succ, zneg_zneg
-/
theorem zneg_pred (n : ZNum) : -n.pred = (-n).succ := by
  rw [← zneg_zneg (succ (-n))]; rw [zneg_succ]; rw [zneg_zneg]

@[simp]
/--
theorem `abs_to_nat` / 定理 `abs_to_nat`

English:
theorem abs_to_nat
  statement: forall n, (abs n : Nat) = Int.natAbs n

中文:
定理 abs_to_nat
  结论: 对任意 n, (abs n : 自然数) = 整数.natAbs n
-/
theorem abs_to_nat : forall n, (abs n : Nat) = Int.natAbs n
  | 0 => rfl
  | pos p => congr_arg Int.natAbs p.to_nat_to_int
  | neg p => show Int.natAbs ((p : Nat) : Int) = Int.natAbs (-p) by rw [p.to_nat_to_int, Int.natAbs_neg]

@[simp]
/--
theorem `abs_toZNum` / 定理 `abs_toZNum`

English:
theorem abs_toZNum
  statement: forall n : Num, abs n.toZNum = n

中文:
定理 abs_toZNum
  结论: 对任意 n : Num, abs n.toZNum = n
-/
theorem abs_toZNum : forall n : Num, abs n.toZNum = n
  | 0 => rfl
  | Num.pos _p => rfl

@[simp, norm_cast]
/--
theorem `cast_to_int` / 定理 `cast_to_int`

English:
theorem cast_to_int
  given: [AddGroupWithOne α]
  statement: forall n : ZNum, ((n : Int) : α) = n

中文:
定理 cast_to_int
  条件: [加法带幺群 α]
  结论: 对任意 n : ZNum, ((n : 整数) : α) = n
-/
theorem cast_to_int [AddGroupWithOne α] : forall n : ZNum, ((n : Int) : α) = n
  | 0 => by rw [cast_zero, cast_zero, Int.cast_zero]
  | pos p => by rw [cast_pos, cast_pos, PosNum.cast_to_int]
  | neg p => by rw [cast_neg, cast_neg, Int.cast_neg, PosNum.cast_to_int]

/--
theorem `bit0_of_bit0` / 定理 `bit0_of_bit0`

English:
theorem bit0_of_bit0
  statement: forall n : ZNum, n + n = n.bit0

中文:
定理 bit0_of_bit0
  结论: 对任意 n : ZNum, n + n = n.bit0
-/
theorem bit0_of_bit0 : forall n : ZNum, n + n = n.bit0
  | 0 => rfl
  | pos a => congr_arg pos a.bit0_of_bit0
  | neg a => congr_arg neg a.bit0_of_bit0

/--
theorem `bit1_of_bit1` / 定理 `bit1_of_bit1`

English:
theorem bit1_of_bit1
  statement: forall n : ZNum, n + n + 1 = n.bit1

中文:
定理 bit1_of_bit1
  结论: 对任意 n : ZNum, n + n + 1 = n.bit1

Depends on / 依赖: p.Prime, perfectRing
-/
theorem bit1_of_bit1 : forall n : ZNum, n + n + 1 = n.bit1
  | 0 => rfl
  | pos a => congr_arg pos a.bit1_of_bit1
  | neg a => show PosNum.sub' 1 (a + a) = _ by rw [PosNum.one_sub', a.bit0_of_bit0]; rfl

@[simp, norm_cast]
/--
theorem `cast_bit0` / 定理 `cast_bit0`

English:
theorem cast_bit0
  given: [AddGroupWithOne α]
  statement: forall n : ZNum, (n.bit0 : α) = (n : α) + n

中文:
定理 cast_bit0
  条件: [加法带幺群 α]
  结论: 对任意 n : ZNum, (n.bit0 : α) = (n : α) + n

Depends on / 依赖: CharP.exists, IsAlgClosed, PerfectField, PerfectRing, PerfectRing.toPerfectField, exacts, ofCharZero, perfectField, toPerfectField
-/
theorem cast_bit0 [AddGroupWithOne α] : forall n : ZNum, (n.bit0 : α) = (n : α) + n
  | 0 => (add_zero _).symm
  | pos p => by rw [ZNum.bit0, cast_pos, cast_pos]; rfl
  | neg p => by
    rw [ZNum.bit0]; rw [cast_neg]; rw [cast_neg]; rw [PosNum.cast_bit0]; rw [neg_add_rev]

@[simp, norm_cast]
/--
theorem `cast_bit1` / 定理 `cast_bit1`

English:
theorem cast_bit1
  given: [AddGroupWithOne α]
  statement: forall n : ZNum, (n.bit1 : α) = ((n : α) + n) + 1
  proof: (succ'_pred' p).symm.trans (congr_arg Num.succ' e)
    · conv at ep => change p = 1
      subst p
      simp
    · dsimp only [Num.succ'] at ep
      subst p
      have : (↑(-↑a : Int) : α) = -1 + ↑(-↑a + 1 : Int) := by simp [add_comm (-↑a : Int) 1]
      simpa using this

@[simp]

中文:
定理 cast_bit1
  条件: [加法带幺群 α]
  结论: 对任意 n : ZNum, (n.bit1 : α) = ((n : α) + n) + 1
  证明: (succ'_pred' p).symm.trans (congr_arg Num.succ' e)
    · conv at ep => change p = 1
      subst p
      simp
    · dsimp only [Num.succ'] at ep
      subst p
      have : (↑(-↑a : Int) : α) = -1 + ↑(-↑a + 1 : Int) := by simp [add_comm (-↑a : Int) 1]
      simpa using this

@[simp]

Depends on / 依赖: Fintype, Fintype.card, Fintype.card_le_of_injective, Infinite, Infinite.of_not_fintype, IsAlgClosed, IsAlgClosed.splits_domain, Nat.not_succ_le_self, Num.succ, Separable, _pred, card_le_of_injective, card_rootSet_eq_natDegree, congr_arg, f.rootSet, n.succ, natDegree_X_pow_sub_C, not_succ_le_self, of_not_fintype, one_ne_zero
-/
theorem cast_bit1 [AddGroupWithOne α] : forall n : ZNum, (n.bit1 : α) = ((n : α) + n) + 1
  | 0 => by simp [ZNum.bit1]
  | pos p => by rw [ZNum.bit1, cast_pos, cast_pos]; rfl
  | neg p => by
    rw [ZNum.bit1]; rw [cast_neg]; rw [cast_neg]
    rcases e : pred' p with - | a <;>
      have ep : p = _ := (succ'_pred' p).symm.trans (congr_arg Num.succ' e)
    · conv at ep => change p = 1
      subst p
      simp
    · dsimp only [Num.succ'] at ep
      subst p
      have : (↑(-↑a : Int) : α) = -1 + ↑(-↑a + 1 : Int) := by simp [add_comm (-↑a : Int) 1]
      simpa using this

@[simp]
/--
theorem `cast_bitm1` / 定理 `cast_bitm1`

English:
theorem cast_bitm1
  given: [AddGroupWithOne α] (n : ZNum)
  statement: (n.bitm1 : α) = (n : α) + n - 1
  proof: by
  conv =>
    lhs
    rw [← zneg_zneg n]
  rw [← zneg_bit1]; rw [cast_zneg]; rw [cast_bit1]
  have : ((-1 + n + n : Int) : α) = (n + n + -1 : Int) := by simp [add_comm]
  simpa [sub_eq_add_neg] using this

中文:
定理 cast_bitm1
  条件: [加法带幺群 α] (n : ZNum)
  结论: (n.bitm1 : α) = (n : α) + n - 1
  证明: by
  conv =>
    lhs
    rw [← zneg_zneg n]
  rw [← zneg_bit1]; rw [cast_zneg]; rw [cast_bit1]
  have : ((-1 + n + n : Int) : α) = (n + n + -1 : Int) := by simp [add_comm]
  simpa [sub_eq_add_neg] using this

Depends on / 依赖: add_comm, cast_bit1, cast_zneg, sub_eq_add_neg, zneg_bit1, zneg_zneg
-/
theorem cast_bitm1 [AddGroupWithOne α] (n : ZNum) : (n.bitm1 : α) = (n : α) + n - 1 := by
  conv =>
    lhs
    rw [← zneg_zneg n]
  rw [← zneg_bit1]; rw [cast_zneg]; rw [cast_bit1]
  have : ((-1 + n + n : Int) : α) = (n + n + -1 : Int) := by simp [add_comm]
  simpa [sub_eq_add_neg] using this

/--
theorem `add_zero` / 定理 `add_zero`

English:
theorem add_zero
  given: (n : ZNum)
  statement: n + 0 = n
  proof: by cases n <;> rfl

中文:
定理 add_zero
  条件: (n : ZNum)
  结论: n + 0 = n
  证明: by cases n <;> rfl
-/
theorem add_zero (n : ZNum) : n + 0 = n := by cases n <;> rfl

/--
theorem `zero_add` / 定理 `zero_add`

English:
theorem zero_add
  given: (n : ZNum)
  statement: 0 + n = n
  proof: by cases n <;> rfl

中文:
定理 zero_add
  条件: (n : ZNum)
  结论: 0 + n = n
  证明: by cases n <;> rfl
-/
theorem zero_add (n : ZNum) : 0 + n = n := by cases n <;> rfl

/--
theorem `add_one` / 定理 `add_one`

English:
theorem add_one
  statement: forall n : ZNum, n + 1 = succ n

中文:
定理 add_one
  结论: 对任意 n : ZNum, n + 1 = succ n
-/
theorem add_one : forall n : ZNum, n + 1 = succ n
  | 0 => rfl
  | pos p => congr_arg pos p.add_one
  | neg p => by cases p <;> rfl

end ZNum

namespace PosNum

variable {α : Type*}

/--
theorem `cast_to_znum` / 定理 `cast_to_znum`

English:
theorem cast_to_znum
  statement: forall n : PosNum, (n : ZNum) = ZNum.pos n
  proof: congr_arg ZNum.bit0 (cast_to_znum p)
      rwa [← ZNum.bit0_of_bit0] at this
  | bit1 p => by
      have := congr_arg ZNum.bit1 (cast_to_znum p)
      rwa [← ZNum.bit1_of_bit1] at this

中文:
定理 cast_to_znum
  结论: 对任意 n : PosNum, (n : ZNum) = ZNum.pos n
  证明: congr_arg ZNum.bit0 (cast_to_znum p)
      rwa [← ZNum.bit0_of_bit0] at this
  | bit1 p => by
      have := congr_arg ZNum.bit1 (cast_to_znum p)
      rwa [← ZNum.bit1_of_bit1] at this

Depends on / 依赖: ZNum.bit0, cast_to_znum, congr_arg
-/
theorem cast_to_znum : forall n : PosNum, (n : ZNum) = ZNum.pos n
  | 1 => rfl
  | bit0 p => by
      have := congr_arg ZNum.bit0 (cast_to_znum p)
      rwa [← ZNum.bit0_of_bit0] at this
  | bit1 p => by
      have := congr_arg ZNum.bit1 (cast_to_znum p)
      rwa [← ZNum.bit1_of_bit1] at this

/--
theorem `cast_sub'` / 定理 `cast_sub'`

English:
theorem cast_sub'
  given: [AddGroupWithOne α]
  statement: forall m n : PosNum, (sub' m n : α) = m - n
  proof: by simp [add_left_comm]
    simpa [sub_eq_add_neg] using this
  | bit0 a, bit1 b => by
    rw [sub']; rw [ZNum.cast_bitm1]; rw [cast_sub' a b]
    have : ((-b + (a + (-b + -1)) : Int) : α) = (a + -1 + (-b + -b) : Int) := by
      simp [add_comm, add_left_comm]
    simpa [sub_eq_add_neg] using this
  | bit1 a, bit0 b => by
    rw [sub']; rw [ZNum.cast_bit1]; rw [cast_sub' a b]
    have : ((-b + (a + (-b + 1)) : Int) : α) = (a + 1 + (-b + -b) : Int) := by
      simp [add_comm, add_left_comm]
    simpa [sub_eq_add_neg] using this
  | bit1 a, bit1 b => by
    rw [sub']; rw [ZNum.cast_bit0]; rw [cast_sub' a b]
    have : ((-b + (a + -b) : Int) : α) = a + (-b + -b) := by simp [add_left_comm]
    simpa [sub_eq_add_neg] using this

中文:
定理 cast_sub'
  条件: [加法带幺群 α]
  结论: 对任意 m n : PosNum, (sub' m n : α) = m - n
  证明: by simp [add_left_comm]
    simpa [sub_eq_add_neg] using this
  | bit0 a, bit1 b => by
    rw [sub']; rw [ZNum.cast_bitm1]; rw [cast_sub' a b]
    have : ((-b + (a + (-b + -1)) : Int) : α) = (a + -1 + (-b + -b) : Int) := by
      simp [add_comm, add_left_comm]
    simpa [sub_eq_add_neg] using this
  | bit1 a, bit0 b => by
    rw [sub']; rw [ZNum.cast_bit1]; rw [cast_sub' a b]
    have : ((-b + (a + (-b + 1)) : Int) : α) = (a + 1 + (-b + -b) : Int) := by
      simp [add_comm, add_left_comm]
    simpa [sub_eq_add_neg] using this
  | bit1 a, bit1 b => by
    rw [sub']; rw [ZNum.cast_bit0]; rw [cast_sub' a b]
    have : ((-b + (a + -b) : Int) : α) = a + (-b + -b) := by simp [add_left_comm]
    simpa [sub_eq_add_neg] using this

Depends on / 依赖: ZNum.cast_bit1, ZNum.cast_bitm1, add_comm, add_left_comm, cast_bit1, cast_bitm1, cast_sub, sub_eq_add_neg
-/
theorem cast_sub' [AddGroupWithOne α] : forall m n : PosNum, (sub' m n : α) = m - n
  | a, 1 => by
    rw [sub'_one]; rw [Num.cast_toZNum]; rw [← Num.cast_to_nat]; rw [pred'_to_nat]; rw [← Nat.sub_one]
    simp
  | 1, b => by
    rw [one_sub']; rw [Num.cast_toZNumNeg]; rw [← neg_sub]; rw [neg_inj]; rw [← Num.cast_to_nat]; rw [pred'_to_nat]; rw [← Nat.sub_one]
    simp
  | bit0 a, bit0 b => by
    rw [sub']; rw [ZNum.cast_bit0]; rw [cast_sub' a b]
    have : ((a + -b + (a + -b) : Int) : α) = a + a + (-b + -b) := by simp [add_left_comm]
    simpa [sub_eq_add_neg] using this
  | bit0 a, bit1 b => by
    rw [sub']; rw [ZNum.cast_bitm1]; rw [cast_sub' a b]
    have : ((-b + (a + (-b + -1)) : Int) : α) = (a + -1 + (-b + -b) : Int) := by
      simp [add_comm, add_left_comm]
    simpa [sub_eq_add_neg] using this
  | bit1 a, bit0 b => by
    rw [sub']; rw [ZNum.cast_bit1]; rw [cast_sub' a b]
    have : ((-b + (a + (-b + 1)) : Int) : α) = (a + 1 + (-b + -b) : Int) := by
      simp [add_comm, add_left_comm]
    simpa [sub_eq_add_neg] using this
  | bit1 a, bit1 b => by
    rw [sub']; rw [ZNum.cast_bit0]; rw [cast_sub' a b]
    have : ((-b + (a + -b) : Int) : α) = a + (-b + -b) := by simp [add_left_comm]
    simpa [sub_eq_add_neg] using this

/--
theorem `to_nat_eq_succ_pred` / 定理 `to_nat_eq_succ_pred`

English:
theorem to_nat_eq_succ_pred
  given: (n : PosNum)
  statement: (n : Nat) = n.pred' + 1
  proof: by
  rw [← Num.succ'_to_nat]; rw [n.succ'_pred']

中文:
定理 to_nat_eq_succ_pred
  条件: (n : PosNum)
  结论: (n : 自然数) = n.pred' + 1
  证明: by
  rw [← Num.succ'_to_nat]; rw [n.succ'_pred']

Depends on / 依赖: Num.succ, _pred, _to_nat, n.succ
-/
theorem to_nat_eq_succ_pred (n : PosNum) : (n : Nat) = n.pred' + 1 := by
  rw [← Num.succ'_to_nat]; rw [n.succ'_pred']

/--
theorem `to_int_eq_succ_pred` / 定理 `to_int_eq_succ_pred`

English:
theorem to_int_eq_succ_pred
  given: (n : PosNum)
  statement: (n : Int) = (n.pred' : Nat) + 1
  proof: by
  rw [← n.to_nat_to_int]; rw [to_nat_eq_succ_pred]; rfl

中文:
定理 to_int_eq_succ_pred
  条件: (n : PosNum)
  结论: (n : 整数) = (n.pred' : 自然数) + 1
  证明: by
  rw [← n.to_nat_to_int]; rw [to_nat_eq_succ_pred]; rfl

Depends on / 依赖: n.to_nat_to_int, to_nat_eq_succ_pred, to_nat_to_int
-/
theorem to_int_eq_succ_pred (n : PosNum) : (n : Int) = (n.pred' : Nat) + 1 := by
  rw [← n.to_nat_to_int]; rw [to_nat_eq_succ_pred]; rfl

end PosNum

namespace Num

variable {α : Type*}

@[simp]
/--
theorem `cast_sub'` / 定理 `cast_sub'`

English:
theorem cast_sub'
  given: [AddGroupWithOne α]
  statement: forall m n : Num, (sub' m n : α) = m - n

中文:
定理 cast_sub'
  条件: [加法带幺群 α]
  结论: 对任意 m n : Num, (sub' m n : α) = m - n
-/
theorem cast_sub' [AddGroupWithOne α] : forall m n : Num, (sub' m n : α) = m - n
  | 0, 0 => (sub_zero _).symm
  | pos _a, 0 => (sub_zero _).symm
  | 0, pos _b => (zero_sub _).symm
  | pos _a, pos _b => PosNum.cast_sub' _ _

/--
theorem `toZNum_succ` / 定理 `toZNum_succ`

English:
theorem toZNum_succ
  statement: forall n : Num, n.succ.toZNum = n.toZNum.succ

中文:
定理 toZNum_succ
  结论: 对任意 n : Num, n.succ.toZNum = n.toZNum.succ
-/
theorem toZNum_succ : forall n : Num, n.succ.toZNum = n.toZNum.succ
  | 0 => rfl
  | pos _n => rfl

/--
theorem `toZNumNeg_succ` / 定理 `toZNumNeg_succ`

English:
theorem toZNumNeg_succ
  statement: forall n : Num, n.succ.toZNumNeg = n.toZNumNeg.pred

中文:
定理 toZNumNeg_succ
  结论: 对任意 n : Num, n.succ.toZNumNeg = n.toZNumNeg.pred
-/
theorem toZNumNeg_succ : forall n : Num, n.succ.toZNumNeg = n.toZNumNeg.pred
  | 0 => rfl
  | pos _n => rfl

@[simp]
/--
theorem `pred_succ` / 定理 `pred_succ`

English:
theorem pred_succ
  statement: forall n : ZNum, n.pred.succ = n

中文:
定理 pred_succ
  结论: 对任意 n : ZNum, n.pred.succ = n
-/
theorem pred_succ : forall n : ZNum, n.pred.succ = n
  | 0 => rfl
  | ZNum.neg p => show toZNumNeg (pos p).succ'.pred' = _ by rw [PosNum.pred'_succ']; rfl
  | ZNum.pos p => by rw [ZNum.pred, ← toZNum_succ, Num.succ, PosNum.succ'_pred', toZNum]

/--
theorem `succ_ofInt'` / 定理 `succ_ofInt'`

English:
theorem succ_ofInt'
  statement: forall n, ZNum.ofInt' (n + 1) = ZNum.ofInt' n + 1

中文:
定理 succ_of整数'
  结论: 对任意 n, ZNum.of整数' (n + 1) = ZNum.of整数' n + 1
-/
theorem succ_ofInt' : forall n, ZNum.ofInt' (n + 1) = ZNum.ofInt' n + 1
  | (n : Nat) => by
    change ZNum.ofInt' (n + 1 : Nat) = ZNum.ofInt' (n : Nat) + 1
    dsimp only [ZNum.ofInt', ZNum.ofInt']
    rw [Num.ofNat'_succ]; rw [Num.add_one]; rw [toZNum_succ]; rw [ZNum.add_one]
  | -[0+1] => by
    change ZNum.ofInt' 0 = ZNum.ofInt' (-[0+1]) + 1
    dsimp only [ZNum.ofInt', ZNum.ofInt']
    rw [ofNat'_succ]; rw [ofNat'_zero]; rfl
  | -[(n + 1)+1] => by
    change ZNum.ofInt' -[n+1] = ZNum.ofInt' -[(n + 1)+1] + 1
    dsimp only [ZNum.ofInt', ZNum.ofInt']
    rw [@Num.ofNat'_succ (n + 1)]; rw [Num.add_one]; rw [toZNumNeg_succ]; rw [@ofNat'_succ n]; rw [Num.add_one]; rw [ZNum.add_one]; rw [pred_succ]

/--
theorem `ofInt'_toZNum` / 定理 `ofInt'_toZNum`

English:
theorem ofInt'_toZNum
  statement: forall n : Nat, toZNum n = ZNum.ofInt' n

中文:
定理 of整数'_toZNum
  结论: 对任意 n : 自然数, toZNum n = ZNum.of整数' n
-/
theorem ofInt'_toZNum : forall n : Nat, toZNum n = ZNum.ofInt' n
  | 0 => rfl
  | n + 1 => by
    rw [Nat.cast_succ]; rw [Num.add_one]; rw [toZNum_succ]; rw [ofInt'_toZNum n]; rw [Nat.cast_succ]; rw [succ_ofInt']; rw [ZNum.add_one]

/--
theorem `mem_ofZNum'` / 定理 `mem_ofZNum'`

English:
theorem mem_ofZNum'
  statement: forall {m : Num} {n : ZNum}, m in ofZNum' n ↔ n = toZNum m

中文:
定理 mem_ofZNum'
  结论: 对任意 {m : Num} {n : ZNum}, m in ofZNum' n ↔ n = toZNum m
-/
theorem mem_ofZNum' : forall {m : Num} {n : ZNum}, m in ofZNum' n ↔ n = toZNum m
  | 0, 0 => ⟨fun _ => rfl, fun _ => rfl⟩
  | pos _, 0 => ⟨nofun, nofun⟩
  | m, ZNum.pos p =>
Option.some_inj.trans by cases m <;> constructor <;> intro h <;> try cases h <;> rfl
  | m, ZNum.neg p => ⟨nofun, fun h => by cases m <;> cases h⟩

/--
theorem `ofZNum'_toNat` / 定理 `ofZNum'_toNat`

English:
theorem ofZNum'_toNat
  statement: forall n : ZNum, (↑) < > ofZNum' n = Int.toNat? n

中文:
定理 ofZNum'_to自然数
  结论: 对任意 n : ZNum, (↑) < > ofZNum' n = 整数.to自然数? n
-/
theorem ofZNum'_toNat : forall n : ZNum, (↑) < > ofZNum' n = Int.toNat? n
  | 0 => rfl
  | ZNum.pos p => show _ = Int.toNat? p by rw [← PosNum.to_nat_to_int p]; rfl
  | ZNum.neg p =>
(congr_arg fun x => Int.toNat? (-x))
      show ((p.pred' + 1 : Nat) : Int) = p by rw [← succ'_to_nat]; simp

/--
theorem `ofZNum_toNat` / 定理 `ofZNum_toNat`

English:
theorem ofZNum_toNat
  statement: forall n : ZNum, (ofZNum n : Nat) = Int.toNat n

中文:
定理 ofZNum_to自然数
  结论: 对任意 n : ZNum, (ofZNum n : 自然数) = 整数.to自然数 n
-/
theorem ofZNum_toNat : forall n : ZNum, (ofZNum n : Nat) = Int.toNat n
  | 0 => rfl
  | ZNum.pos p => show _ = Int.toNat p by rw [← PosNum.to_nat_to_int p]; rfl
  | ZNum.neg p =>
(congr_arg fun x => Int.toNat (-x))
      show ((p.pred' + 1 : Nat) : Int) = p by rw [← succ'_to_nat]; simp

@[simp]
/--
theorem `cast_ofZNum` / 定理 `cast_ofZNum`

English:
theorem cast_ofZNum
  given: [AddMonoidWithOne α] (n : ZNum)
  statement: (ofZNum n : α) = Int.toNat n
  proof: by
  rw [← cast_to_nat]; rw [ofZNum_toNat]

@[simp, norm_cast]

中文:
定理 cast_ofZNum
  条件: [加法带幺幺半群 α] (n : ZNum)
  结论: (ofZNum n : α) = 整数.to自然数 n
  证明: by
  rw [← cast_to_nat]; rw [ofZNum_toNat]

@[simp, norm_cast]

Depends on / 依赖: cast_to_nat, ofZNum_toNat
-/
theorem cast_ofZNum [AddMonoidWithOne α] (n : ZNum) : (ofZNum n : α) = Int.toNat n := by
  rw [← cast_to_nat]; rw [ofZNum_toNat]

@[simp, norm_cast]
/--
theorem `sub_to_nat` / 定理 `sub_to_nat`

English:
theorem sub_to_nat
  given: (m n)
  statement: ((m - n : Num) : Nat) = m - n
  proof: show (ofZNum _ : Nat) = _ by
    rw [ofZNum_toNat]; rw [cast_sub']; rw [← to_nat_to_int]; rw [← to_nat_to_int]; rw [Int.toNat_sub]

中文:
定理 sub_to_nat
  条件: (m n)
  结论: ((m - n : Num) : 自然数) = m - n
  证明: show (ofZNum _ : Nat) = _ by
    rw [ofZNum_toNat]; rw [cast_sub']; rw [← to_nat_to_int]; rw [← to_nat_to_int]; rw [Int.toNat_sub]

Depends on / 依赖: Int.toNat_sub, cast_sub, ofZNum, ofZNum_toNat, toNat_sub, to_nat_to_int
-/
theorem sub_to_nat (m n) : ((m - n : Num) : Nat) = m - n :=
  show (ofZNum _ : Nat) = _ by
    rw [ofZNum_toNat]; rw [cast_sub']; rw [← to_nat_to_int]; rw [← to_nat_to_int]; rw [Int.toNat_sub]

end Num

namespace ZNum

variable {α : Type*}

@[simp, norm_cast]
/--
theorem `cast_add` / 定理 `cast_add`

English:
theorem cast_add
  given: [AddGroupWithOne α]
  statement: forall m n, ((m + n : ZNum) : α) = m + n
  proof: by
      rw [← PosNum.cast_to_int a]; rw [← PosNum.cast_to_int b]; rw [← Int.cast_neg]; rw [← Int.cast_add (-a)]
      simp [add_comm]
(PosNum.cast_sub' _ _).trans (sub_eq_add_neg _ _).trans this
  | neg a, neg b =>
    show -(↑(a + b) : α) = -a + -b by
      rw [PosNum.cast_add]; rw [neg_eq_iff_eq_neg]; rw [neg_add_rev]; rw [neg_neg]; rw [neg_neg]; rw [← PosNum.cast_to_int a]; rw [← PosNum.cast_to_int b]; rw [← Int.cast_add]; rw [← Int.cast_add]; rw [add_comm]

@[simp]

中文:
定理 cast_add
  条件: [加法带幺群 α]
  结论: 对任意 m n, ((m + n : ZNum) : α) = m + n
  证明: by
      rw [← PosNum.cast_to_int a]; rw [← PosNum.cast_to_int b]; rw [← Int.cast_neg]; rw [← Int.cast_add (-a)]
      simp [add_comm]
(PosNum.cast_sub' _ _).trans (sub_eq_add_neg _ _).trans this
  | neg a, neg b =>
    show -(↑(a + b) : α) = -a + -b by
      rw [PosNum.cast_add]; rw [neg_eq_iff_eq_neg]; rw [neg_add_rev]; rw [neg_neg]; rw [neg_neg]; rw [← PosNum.cast_to_int a]; rw [← PosNum.cast_to_int b]; rw [← Int.cast_add]; rw [← Int.cast_add]; rw [add_comm]

@[simp]
-/
theorem cast_add [AddGroupWithOne α] : forall m n, ((m + n : ZNum) : α) = m + n
  | 0, a => by cases a <;> exact (_root_.zero_add _).symm
  | b, 0 => by cases b <;> exact (_root_.add_zero _).symm
  | pos _, pos _ => PosNum.cast_add _ _
  | pos a, neg b => by simpa only [sub_eq_add_neg] using! PosNum.cast_sub' (α := α) _ _
  | neg a, pos b =>
    have : (↑b + -↑a : α) = -↑a + ↑b := by
      rw [← PosNum.cast_to_int a]; rw [← PosNum.cast_to_int b]; rw [← Int.cast_neg]; rw [← Int.cast_add (-a)]
      simp [add_comm]
(PosNum.cast_sub' _ _).trans (sub_eq_add_neg _ _).trans this
  | neg a, neg b =>
    show -(↑(a + b) : α) = -a + -b by
      rw [PosNum.cast_add]; rw [neg_eq_iff_eq_neg]; rw [neg_add_rev]; rw [neg_neg]; rw [neg_neg]; rw [← PosNum.cast_to_int a]; rw [← PosNum.cast_to_int b]; rw [← Int.cast_add]; rw [← Int.cast_add]; rw [add_comm]

@[simp]
/--
theorem `cast_succ` / 定理 `cast_succ`

English:
theorem cast_succ
  given: [AddGroupWithOne α] (n)
  statement: ((succ n : ZNum) : α) = n + 1
  proof: by
  rw [← add_one]; rw [cast_add]; rw [cast_one]

@[simp, norm_cast]

中文:
定理 cast_succ
  条件: [加法带幺群 α] (n)
  结论: ((succ n : ZNum) : α) = n + 1
  证明: by
  rw [← add_one]; rw [cast_add]; rw [cast_one]

@[simp, norm_cast]

Depends on / 依赖: add_one, cast_add, cast_one
-/
theorem cast_succ [AddGroupWithOne α] (n) : ((succ n : ZNum) : α) = n + 1 := by
  rw [← add_one]; rw [cast_add]; rw [cast_one]

@[simp, norm_cast]
/--
theorem `mul_to_int` / 定理 `mul_to_int`

English:
theorem mul_to_int
  statement: forall m n, ((m * n : ZNum) : Int) = m * n

中文:
定理 mul_to_int
  结论: 对任意 m n, ((m * n : ZNum) : 整数) = m * n
-/
theorem mul_to_int : forall m n, ((m * n : ZNum) : Int) = m * n
  | 0, a => by cases a <;> exact (zero_mul _).symm
  | b, 0 => by cases b <;> exact (mul_zero _).symm
  | pos a, pos b => PosNum.cast_mul a b
  | pos a, neg b => show -↑(a * b) = ↑a * -↑b by rw [PosNum.cast_mul, neg_mul_eq_mul_neg]
  | neg a, pos b => show -↑(a * b) = -↑a * ↑b by rw [PosNum.cast_mul, neg_mul_eq_neg_mul]
  | neg a, neg b => show ↑(a * b) = -↑a * -↑b by rw [PosNum.cast_mul, neg_mul_neg]

/--
theorem `cast_mul` / 定理 `cast_mul`

English:
theorem cast_mul
  given: [NonAssocRing α] (m n)
  statement: ((m * n : ZNum) : α) = m * n
  proof: by
  rw [← cast_to_int]; rw [mul_to_int]; rw [Int.cast_mul]; rw [cast_to_int]; rw [cast_to_int]

中文:
定理 cast_mul
  条件: [非结合环 α] (m n)
  结论: ((m * n : ZNum) : α) = m * n
  证明: by
  rw [← cast_to_int]; rw [mul_to_int]; rw [Int.cast_mul]; rw [cast_to_int]; rw [cast_to_int]

Depends on / 依赖: Int.cast_mul, cast_mul, cast_to_int, mul_to_int
-/
theorem cast_mul [NonAssocRing α] (m n) : ((m * n : ZNum) : α) = m * n := by
  rw [← cast_to_int]; rw [mul_to_int]; rw [Int.cast_mul]; rw [cast_to_int]; rw [cast_to_int]

/--
theorem `ofInt'_neg` / 定理 `ofInt'_neg`

English:
theorem ofInt'_neg
  statement: forall n : Int, ofInt' (-n) = -ofInt' n

中文:
定理 of整数'_neg
  结论: 对任意 n : 整数, of整数' (-n) = -of整数' n
-/
theorem ofInt'_neg : forall n : Int, ofInt' (-n) = -ofInt' n
  | -[n+1] => show ofInt' (n + 1 : Nat) = _ by simp only [ofInt', Num.zneg_toZNumNeg]
  | 0 => show Num.toZNum (Num.ofNat' 0) = -Num.toZNum (Num.ofNat' 0) by rw [Num.ofNat'_zero]; rfl
  | (n + 1 : Nat) => show Num.toZNumNeg _ = -Num.toZNum _ by rw [Num.zneg_toZNum]

/--
theorem `of_to_int'` / 定理 `of_to_int'`

English:
theorem of_to_int'
  statement: forall n : ZNum, ZNum.ofInt' n = n

中文:
定理 of_to_int'
  结论: 对任意 n : ZNum, ZNum.of整数' n = n
-/
theorem of_to_int' : forall n : ZNum, ZNum.ofInt' n = n
  | 0 => by
    dsimp [ofInt', cast_zero]
    simp only [Num.ofNat'_zero, Num.toZNum]
  | pos a => by rw [cast_pos, ← PosNum.cast_to_nat, ← Num.ofInt'_toZNum, PosNum.of_to_nat]; rfl
  | neg a => by
    rw [cast_neg]; rw [ofInt'_neg]; rw [← PosNum.cast_to_nat]; rw [← Num.ofInt'_toZNum]; rw [PosNum.of_to_nat]; rfl

/--
theorem `to_int_inj` / 定理 `to_int_inj`

English:
theorem to_int_inj
  given: {m n : ZNum}
  statement: (m : Int) = n ↔ m = n
  proof: ⟨fun h => Function.LeftInverse.injective of_to_int' h, congr_arg _⟩

中文:
定理 to_int_inj
  条件: {m n : ZNum}
  结论: (m : 整数) = n ↔ m = n
  证明: ⟨fun h => Function.LeftInverse.injective of_to_int' h, congr_arg _⟩

Depends on / 依赖: Function, Function.LeftInverse.injective, LeftInverse, congr_arg, injective, of_to_int
-/
theorem to_int_inj {m n : ZNum} : (m : Int) = n ↔ m = n :=
  ⟨fun h => Function.LeftInverse.injective of_to_int' h, congr_arg _⟩

/--
theorem `cmp_to_int` / 定理 `cmp_to_int`

English:
theorem cmp_to_int
  statement: forall m n, (Ordering.casesOn (cmp m n) ((m : Int) < n) (m = n) ((n : Int) < m) : Prop)
  proof: PosNum.cmp_to_nat b a; revert this; dsimp [cmp]
    cases PosNum.cmp b a <;> [simp; simp +contextual; simp]
  | pos _, 0 => PosNum.cast_pos _
  | pos _, neg _ => lt_trans (neg_lt_zero.2 <| PosNum.cast_pos _) (PosNum.cast_pos _)
| 0, neg _ => neg_lt_zero.2 PosNum.cast_pos _
| neg _, 0 => neg_lt_zero.2 PosNum.cast_pos _
  | neg _, pos _ => lt_trans (neg_lt_zero.2 <| PosNum.cast_pos _) (PosNum.cast_pos _)
  | 0, pos _ => PosNum.cast_pos _

@[norm_cast]

中文:
定理 cmp_to_int
  结论: 对任意 m n, (Ordering.casesOn (cmp m n) ((m : 整数) < n) (m = n) ((n : 整数) < m) : 命题)
  证明: PosNum.cmp_to_nat b a; revert this; dsimp [cmp]
    cases PosNum.cmp b a <;> [simp; simp +contextual; simp]
  | pos _, 0 => PosNum.cast_pos _
  | pos _, neg _ => lt_trans (neg_lt_zero.2 <| PosNum.cast_pos _) (PosNum.cast_pos _)
| 0, neg _ => neg_lt_zero.2 PosNum.cast_pos _
| neg _, 0 => neg_lt_zero.2 PosNum.cast_pos _
  | neg _, pos _ => lt_trans (neg_lt_zero.2 <| PosNum.cast_pos _) (PosNum.cast_pos _)
  | 0, pos _ => PosNum.cast_pos _

@[norm_cast]

Depends on / 依赖: PosNum, PosNum.cmp_to_nat, cmp_to_nat, revert
-/
theorem cmp_to_int : forall m n, (Ordering.casesOn (cmp m n) ((m : Int) < n) (m = n) ((n : Int) < m) : Prop)
  | 0, 0 => rfl
  | pos a, pos b => by simpa using! PosNum.cmp_to_nat a b
  | neg a, neg b => by
    have := PosNum.cmp_to_nat b a; revert this; dsimp [cmp]
    cases PosNum.cmp b a <;> [simp; simp +contextual; simp]
  | pos _, 0 => PosNum.cast_pos _
  | pos _, neg _ => lt_trans (neg_lt_zero.2 <| PosNum.cast_pos _) (PosNum.cast_pos _)
| 0, neg _ => neg_lt_zero.2 PosNum.cast_pos _
| neg _, 0 => neg_lt_zero.2 PosNum.cast_pos _
  | neg _, pos _ => lt_trans (neg_lt_zero.2 <| PosNum.cast_pos _) (PosNum.cast_pos _)
  | 0, pos _ => PosNum.cast_pos _

@[norm_cast]
/--
theorem `lt_to_int` / 定理 `lt_to_int`

English:
theorem lt_to_int
  given: {m n : ZNum}
  statement: (m : Int) < n ↔ m < n
  proof: show (m : Int) < n ↔ cmp m n = Ordering.lt from
    match cmp m n, cmp_to_int m n with
    | Ordering.lt, h => by simp only at h; simp [h]
    | Ordering.eq, h => by simp only at h; simp [h]
    | Ordering.gt, h => by simp [not_lt_of_gt h]

中文:
定理 lt_to_int
  条件: {m n : ZNum}
  结论: (m : 整数) < n ↔ m < n
  证明: show (m : Int) < n ↔ cmp m n = Ordering.lt from
    match cmp m n, cmp_to_int m n with
    | Ordering.lt, h => by simp only at h; simp [h]
    | Ordering.eq, h => by simp only at h; simp [h]
    | Ordering.gt, h => by simp [not_lt_of_gt h]

Depends on / 依赖: Ordering, Ordering.eq, Ordering.gt, Ordering.lt, cmp_to_int, not_lt_of_gt
-/
theorem lt_to_int {m n : ZNum} : (m : Int) < n ↔ m < n :=
  show (m : Int) < n ↔ cmp m n = Ordering.lt from
    match cmp m n, cmp_to_int m n with
    | Ordering.lt, h => by simp only at h; simp [h]
    | Ordering.eq, h => by simp only at h; simp [h]
    | Ordering.gt, h => by simp [not_lt_of_gt h]

/--
theorem `le_to_int` / 定理 `le_to_int`

English:
theorem le_to_int
  given: {m n : ZNum}
  statement: (m : Int) <= n ↔ m <= n
  proof: by
  rw [← not_lt]; exact not_congr lt_to_int

@[simp, norm_cast]

中文:
定理 le_to_int
  条件: {m n : ZNum}
  结论: (m : 整数) <= n ↔ m <= n
  证明: by
  rw [← not_lt]; exact not_congr lt_to_int

@[simp, norm_cast]

Depends on / 依赖: lt_to_int, not_congr, not_lt
-/
theorem le_to_int {m n : ZNum} : (m : Int) <= n ↔ m <= n := by
  rw [← not_lt]; exact not_congr lt_to_int

@[simp, norm_cast]
/--
theorem `cast_lt` / 定理 `cast_lt`

English:
theorem cast_lt
  given: [Ring α] [PartialOrder α] [IsStrictOrderedRing α] {m n : ZNum}
  proof: by
  rw [← cast_to_int m]; rw [← cast_to_int n]; rw [Int.cast_lt]; rw [lt_to_int]

@[simp, norm_cast]

中文:
定理 cast_lt
  条件: [环 α] [偏序 α] [是StrictOrdered环 α] {m n : ZNum}
  证明: by
  rw [← cast_to_int m]; rw [← cast_to_int n]; rw [Int.cast_lt]; rw [lt_to_int]

@[simp, norm_cast]

Depends on / 依赖: Int.cast_lt, cast_lt, cast_to_int, lt_to_int
-/
theorem cast_lt [Ring α] [PartialOrder α] [IsStrictOrderedRing α] {m n : ZNum} :
    (m : α) < n ↔ m < n := by
  rw [← cast_to_int m]; rw [← cast_to_int n]; rw [Int.cast_lt]; rw [lt_to_int]

@[simp, norm_cast]
/--
theorem `cast_le` / 定理 `cast_le`

English:
theorem cast_le
  given: [Ring α] [LinearOrder α] [IsStrictOrderedRing α] {m n : ZNum}
  proof: by
  rw [← not_lt]; exact not_congr cast_lt

@[simp, norm_cast]

中文:
定理 cast_le
  条件: [环 α] [线性序 α] [是StrictOrdered环 α] {m n : ZNum}
  证明: by
  rw [← not_lt]; exact not_congr cast_lt

@[simp, norm_cast]

Depends on / 依赖: cast_lt, not_congr, not_lt
-/
theorem cast_le [Ring α] [LinearOrder α] [IsStrictOrderedRing α] {m n : ZNum} :
    (m : α) <= n ↔ m <= n := by
  rw [← not_lt]; exact not_congr cast_lt

@[simp, norm_cast]
/--
theorem `cast_inj` / 定理 `cast_inj`

English:
theorem cast_inj
  given: [Ring α] [PartialOrder α] [IsStrictOrderedRing α] {m n : ZNum}
  proof: by
  rw [← cast_to_int m]; rw [← cast_to_int n]; rw [Int.cast_inj (α := α)]; rw [to_int_inj]

中文:
定理 cast_inj
  条件: [环 α] [偏序 α] [是StrictOrdered环 α] {m n : ZNum}
  证明: by
  rw [← cast_to_int m]; rw [← cast_to_int n]; rw [Int.cast_inj (α := α)]; rw [to_int_inj]

Depends on / 依赖: Int.cast_inj, cast_inj, cast_to_int, to_int_inj
-/
theorem cast_inj [Ring α] [PartialOrder α] [IsStrictOrderedRing α] {m n : ZNum} :
    (m : α) = n ↔ m = n := by
  rw [← cast_to_int m]; rw [← cast_to_int n]; rw [Int.cast_inj (α := α)]; rw [to_int_inj]

/-- This tactic tries to turn an (in)equality about `ZNum`s to one about `Int`s by rewriting.
```lean
example (n : ZNum) (m : ZNum) : n ≤ n + m * m := by
  transfer_rw
  exact le_add_of_nonneg_right (mul_self_nonneg _)
```
-/
scoped macro (name := transfer_rw) "transfer_rw" : tactic => `(tactic|
    (repeat first | rw [← to_int_inj] | rw [← lt_to_int] | rw [← le_to_int]
     repeat first | rw [cast_add] | rw [mul_to_int] | rw [cast_one] | rw [cast_zero]))

/--
This tactic tries to prove (in)equalities about `ZNum`s by transferring them to the `Int` world and
then trying to call `simp`.
```lean
example (n : ZNum) (m : ZNum) : n ≤ n + m * m := by
  transfer
  exact mul_self_nonneg _
```
-/
scoped macro (name := transfer) "transfer" : tactic => `(tactic|
    (intros; transfer_rw; try simp [add_comm, add_left_comm, mul_comm, mul_left_comm]))

/--
Instance `linearOrder` / 实例 `linearOrder`

English:
instance linearOrder
  signature: : LinearOrder ZNum where
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
  -- This is relying on an automatically generated instance name, generated in a `deriving` handler.
  -- See https://github.com/leanprover/lean4/issues/2343
  toDecidableEq := instDecidableEqZNum
  toDecidableLE := ZNum.decidableLE
  toDecidableLT := ZNum.decidableLT

中文:
实例 linearOrder
  签名: : 线性序 ZNum where
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
  -- This is relying on an automatically generated instance name, generated in a `deriving` handler.
  -- See https://github.com/leanprover/lean4/issues/2343
  toDecidableEq := instDecidableEqZNum
  toDecidableLE := ZNum.decidableLE
  toDecidableLT := ZNum.decidableLT

Depends on / 依赖: le_antisymm, le_refl, le_total, le_trans, lt_iff_le_not_ge, transfer, transfer_rw
-/
instance linearOrder : LinearOrder ZNum where
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
  -- This is relying on an automatically generated instance name, generated in a `deriving` handler.
  -- See https://github.com/leanprover/lean4/issues/2343
  toDecidableEq := instDecidableEqZNum
  toDecidableLE := ZNum.decidableLE
  toDecidableLT := ZNum.decidableLT

/--
Instance `addMonoid` / 实例 `addMonoid`

English:
instance addMonoid
  signature: : AddMonoid ZNum where
  body: by transfer
  zero_add := zero_add
  add_zero := add_zero
  nsmul := nsmulRec

中文:
实例 addMonoid
  签名: : 加法幺半群 ZNum where
  定义体: by transfer
  zero_add := zero_add
  add_zero := add_zero
  nsmul := nsmulRec

Depends on / 依赖: add_zero, nsmulRec, transfer, zero_add
-/
instance addMonoid : AddMonoid ZNum where
  add_assoc := by transfer
  zero_add := zero_add
  add_zero := add_zero
  nsmul := nsmulRec

/--
Instance `addCommGroup` / 实例 `addCommGroup`

English:
instance addCommGroup
  signature: : AddCommGroup ZNum
  body: { ZNum.addMonoid with
    add_comm := by transfer
    zsmul := zsmulRec
    neg_add_cancel := by transfer }

中文:
实例 addCommGroup
  签名: : 加法交换群 ZNum
  定义体: { ZNum.addMonoid with
    add_comm := by transfer
    zsmul := zsmulRec
    neg_add_cancel := by transfer }

Depends on / 依赖: ZNum.addMonoid, addMonoid, add_comm, neg_add_cancel, transfer, zsmulRec
-/
instance addCommGroup : AddCommGroup ZNum :=
  { ZNum.addMonoid with
    add_comm := by transfer
    zsmul := zsmulRec
    neg_add_cancel := by transfer }

/--
Instance `addMonoidWithOne` / 实例 `addMonoidWithOne`

English:
instance addMonoidWithOne
  signature: : AddMonoidWithOne ZNum
  body: { ZNum.addMonoid with
    natCast := fun n => ZNum.ofInt' n
    natCast_zero := show (Num.ofNat' 0).toZNum = 0 by rw [Num.ofNat'_zero]; rfl
    natCast_succ := fun n =>
      show (Num.ofNat' (n + 1)).toZNum = (Num.ofNat' n).toZNum + 1 by
        rw [Num.ofNat'_succ]; rw [Num.add_one]; rw [Num.toZNum_succ]; rw [ZNum.add_one] }

中文:
实例 addMonoidWithOne
  签名: : 加法带幺幺半群 ZNum
  定义体: { ZNum.addMonoid with
    natCast := fun n => ZNum.ofInt' n
    natCast_zero := show (Num.ofNat' 0).toZNum = 0 by rw [Num.ofNat'_zero]; rfl
    natCast_succ := fun n =>
      show (Num.ofNat' (n + 1)).toZNum = (Num.ofNat' n).toZNum + 1 by
        rw [Num.ofNat'_succ]; rw [Num.add_one]; rw [Num.toZNum_succ]; rw [ZNum.add_one] }

Depends on / 依赖: Num.add_one, Num.ofNat, Num.toZNum_succ, ZNum.addMonoid, ZNum.add_one, ZNum.ofInt, _succ, _zero, addMonoid, add_one, natCast, natCast_succ, natCast_zero, toZNum, toZNum_succ
-/
instance addMonoidWithOne : AddMonoidWithOne ZNum :=
  { ZNum.addMonoid with
    natCast := fun n => ZNum.ofInt' n
    natCast_zero := show (Num.ofNat' 0).toZNum = 0 by rw [Num.ofNat'_zero]; rfl
    natCast_succ := fun n =>
      show (Num.ofNat' (n + 1)).toZNum = (Num.ofNat' n).toZNum + 1 by
        rw [Num.ofNat'_succ]; rw [Num.add_one]; rw [Num.toZNum_succ]; rw [ZNum.add_one] }

-- The next theorems are declared outside of the instance to prevent timeouts.

set_option backward.privateInPublic true in
/--
theorem `mul_comm` / 定理 `mul_comm`

English:
theorem mul_comm
  statement: forall (a b : ZNum), a * b = b * a
  proof: by transfer

中文:
定理 mul_comm
  结论: 对任意 (a b : ZNum), a * b = b * a
  证明: by transfer
-/
private theorem mul_comm : forall (a b : ZNum), a * b = b * a := by transfer

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `commRing` / 实例 `commRing`

English:
instance commRing
  signature: : CommRing ZNum
  body: { ZNum.addCommGroup, ZNum.addMonoidWithOne with
    mul_assoc a b c := by transfer
    zero_mul := by transfer
    mul_zero := by transfer
    one_mul := by transfer
    mul_one := by transfer
    left_distrib := by
      transfer
      simp [mul_add]
    right_distrib := by
      transfer
      simp [mul_add, _root_.mul_comm]
    mul_comm := mul_comm }

中文:
实例 commRing
  签名: : 交换环 ZNum
  定义体: { ZNum.addCommGroup, ZNum.addMonoidWithOne with
    mul_assoc a b c := by transfer
    zero_mul := by transfer
    mul_zero := by transfer
    one_mul := by transfer
    mul_one := by transfer
    left_distrib := by
      transfer
      simp [mul_add]
    right_distrib := by
      transfer
      simp [mul_add, _root_.mul_comm]
    mul_comm := mul_comm }

Depends on / 依赖: ZNum.addCommGroup, ZNum.addMonoidWithOne, _root_, _root_.mul_comm, addCommGroup, addMonoidWithOne, left_distrib, mul_add, mul_assoc, mul_comm, mul_one, mul_zero, one_mul, right_distrib, transfer, zero_mul
-/
instance commRing : CommRing ZNum :=
  { ZNum.addCommGroup, ZNum.addMonoidWithOne with
    mul_assoc a b c := by transfer
    zero_mul := by transfer
    mul_zero := by transfer
    one_mul := by transfer
    mul_one := by transfer
    left_distrib := by
      transfer
      simp [mul_add]
    right_distrib := by
      transfer
      simp [mul_add, _root_.mul_comm]
    mul_comm := mul_comm }

/--
Instance `nontrivial` / 实例 `nontrivial`

English:
instance nontrivial
  signature: : Nontrivial ZNum
  body: { exists_pair_ne := ⟨0, 1, by decide⟩ }

中文:
实例 nontrivial
  签名: : 非平凡 ZNum
  定义体: { exists_pair_ne := ⟨0, 1, by decide⟩ }

Depends on / 依赖: exists_pair_ne
-/
instance nontrivial : Nontrivial ZNum :=
  { exists_pair_ne := ⟨0, 1, by decide⟩ }

/--
Instance `zeroLEOneClass` / 实例 `zeroLEOneClass`

English:
instance zeroLEOneClass
  signature: : ZeroLEOneClass ZNum
  body: { zero_le_one := by decide }

中文:
实例 zeroLEOneClass
  签名: : ZeroLEOne类 ZNum
  定义体: { zero_le_one := by decide }

Depends on / 依赖: zero_le_one
-/
instance zeroLEOneClass : ZeroLEOneClass ZNum :=
  { zero_le_one := by decide }

/--
Instance `isOrderedAddMonoid` / 实例 `isOrderedAddMonoid`

English:
instance isOrderedAddMonoid
  signature: : IsOrderedAddMonoid ZNum where
  body: by revert h; transfer_rw; intro h; gcongr

中文:
实例 isOrderedAddMonoid
  签名: : 是OrderedAdd幺半群 ZNum where
  定义体: by revert h; transfer_rw; intro h; gcongr

Depends on / 依赖: revert, transfer_rw
-/
instance isOrderedAddMonoid : IsOrderedAddMonoid ZNum where
  add_le_add_left a b h c := by revert h; transfer_rw; intro h; gcongr

/--
Instance `isStrictOrderedRing` / 实例 `isStrictOrderedRing`

English:
instance isStrictOrderedRing
  signature: : IsStrictOrderedRing ZNum
  body: .of_mul_pos fun a b => by
    transfer_rw
    apply mul_pos

@[simp, norm_cast]

中文:
实例 isStrictOrderedRing
  签名: : 是StrictOrdered环 ZNum
  定义体: .of_mul_pos fun a b => by
    transfer_rw
    apply mul_pos

@[simp, norm_cast]

Depends on / 依赖: mul_pos, of_mul_pos, transfer_rw
-/
instance isStrictOrderedRing : IsStrictOrderedRing ZNum :=
  .of_mul_pos fun a b => by
    transfer_rw
    apply mul_pos

@[simp, norm_cast]
/--
theorem `cast_sub` / 定理 `cast_sub`

English:
theorem cast_sub
  given: [AddCommGroupWithOne α] (m n)
  statement: ((m - n : ZNum) : α) = m - n
  proof: by
  simp [sub_eq_neg_add]

@[norm_cast]

中文:
定理 cast_sub
  条件: [加法交换带幺群 α] (m n)
  结论: ((m - n : ZNum) : α) = m - n
  证明: by
  simp [sub_eq_neg_add]

@[norm_cast]

Depends on / 依赖: sub_eq_neg_add
-/
theorem cast_sub [AddCommGroupWithOne α] (m n) : ((m - n : ZNum) : α) = m - n := by
  simp [sub_eq_neg_add]

@[norm_cast]
/--
theorem `neg_of_int` / 定理 `neg_of_int`

English:
theorem neg_of_int
  statement: forall n, ((-n : Int) : ZNum) = -n

中文:
定理 neg_of_int
  结论: 对任意 n, ((-n : 整数) : ZNum) = -n
-/
theorem neg_of_int : forall n, ((-n : Int) : ZNum) = -n
  | (_ + 1 : Nat) => rfl
  | 0 => by rw [Int.cast_neg]
  | -[_+1] => (zneg_zneg _).symm

@[simp]
/--
theorem `ofInt'_eq` / 定理 `ofInt'_eq`

English:
theorem ofInt'_eq
  statement: forall n : Int, ZNum.ofInt' n = n

中文:
定理 of整数'_eq
  结论: 对任意 n : 整数, ZNum.of整数' n = n
-/
theorem ofInt'_eq : forall n : Int, ZNum.ofInt' n = n
  | (n : Nat) => rfl
  | -[n+1] => by
    change Num.toZNumNeg (n + 1 : Nat) = -(n + 1 : Nat)
    rw [← neg_inj]; rw [neg_neg]; rw [Nat.cast_succ]; rw [Num.add_one]; rw [Num.zneg_toZNumNeg]; rw [Num.toZNum_succ]; rw [Nat.cast_succ]; rw [ZNum.add_one]
    rfl

@[simp]
/--
theorem `of_nat_toZNum` / 定理 `of_nat_toZNum`

English:
theorem of_nat_toZNum
  given: (n : Nat)
  statement: Num.toZNum n = n
  proof: rfl

中文:
定理 of_nat_toZNum
  条件: (n : 自然数)
  结论: Num.toZNum n = n
  证明: rfl
-/
theorem of_nat_toZNum (n : Nat) : Num.toZNum n = n :=
  rfl

-- The priority should be `high`er than `cast_to_int`.
@[simp high, norm_cast]
/--
theorem `of_to_int` / 定理 `of_to_int`

English:
theorem of_to_int
  given: (n : ZNum)
  statement: ((n : Int) : ZNum) = n
  proof: by rw [← ofInt'_eq, of_to_int']

中文:
定理 of_to_int
  条件: (n : ZNum)
  结论: ((n : 整数) : ZNum) = n
  证明: by rw [← ofInt'_eq, of_to_int']

Depends on / 依赖: of_to_int
-/
theorem of_to_int (n : ZNum) : ((n : Int) : ZNum) = n := by rw [← ofInt'_eq, of_to_int']

/--
theorem `to_of_int` / 定理 `to_of_int`

English:
theorem to_of_int
  given: (n : Int)
  statement: ((n : ZNum) : Int) = n
  proof: Int.inductionOn' n 0 (by simp) (by simp) (by simp)

@[simp]

中文:
定理 to_of_int
  条件: (n : 整数)
  结论: ((n : ZNum) : 整数) = n
  证明: Int.inductionOn' n 0 (by simp) (by simp) (by simp)

@[simp]

Depends on / 依赖: Int.inductionOn, inductionOn
-/
theorem to_of_int (n : Int) : ((n : ZNum) : Int) = n :=
  Int.inductionOn' n 0 (by simp) (by simp) (by simp)

@[simp]
/--
theorem `of_nat_toZNumNeg` / 定理 `of_nat_toZNumNeg`

English:
theorem of_nat_toZNumNeg
  given: (n : Nat)
  statement: Num.toZNumNeg n = -n
  proof: by rw [← of_nat_toZNum, Num.zneg_toZNum]

@[simp, norm_cast]

中文:
定理 of_nat_toZNumNeg
  条件: (n : 自然数)
  结论: Num.toZNumNeg n = -n
  证明: by rw [← of_nat_toZNum, Num.zneg_toZNum]

@[simp, norm_cast]

Depends on / 依赖: Num.zneg_toZNum, of_nat_toZNum, zneg_toZNum
-/
theorem of_nat_toZNumNeg (n : Nat) : Num.toZNumNeg n = -n := by rw [← of_nat_toZNum, Num.zneg_toZNum]

@[simp, norm_cast]
/--
theorem `of_intCast` / 定理 `of_intCast`

English:
theorem of_intCast
  given: [AddGroupWithOne α] (n : Int)
  statement: ((n : ZNum) : α) = n
  proof: by
  rw [← cast_to_int]; rw [to_of_int]

@[simp, norm_cast]

中文:
定理 of_intCast
  条件: [加法带幺群 α] (n : 整数)
  结论: ((n : ZNum) : α) = n
  证明: by
  rw [← cast_to_int]; rw [to_of_int]

@[simp, norm_cast]

Depends on / 依赖: cast_to_int, to_of_int
-/
theorem of_intCast [AddGroupWithOne α] (n : Int) : ((n : ZNum) : α) = n := by
  rw [← cast_to_int]; rw [to_of_int]

@[simp, norm_cast]
/--
theorem `of_natCast` / 定理 `of_natCast`

English:
theorem of_natCast
  given: [AddGroupWithOne α] (n : Nat)
  statement: ((n : ZNum) : α) = n
  proof: by
  rw [← Int.cast_natCast]; rw [of_intCast]; rw [Int.cast_natCast]

@[simp, norm_cast]

中文:
定理 of_natCast
  条件: [加法带幺群 α] (n : 自然数)
  结论: ((n : ZNum) : α) = n
  证明: by
  rw [← Int.cast_natCast]; rw [of_intCast]; rw [Int.cast_natCast]

@[simp, norm_cast]

Depends on / 依赖: Int.cast_natCast, cast_natCast, of_intCast
-/
theorem of_natCast [AddGroupWithOne α] (n : Nat) : ((n : ZNum) : α) = n := by
  rw [← Int.cast_natCast]; rw [of_intCast]; rw [Int.cast_natCast]

@[simp, norm_cast]
/--
theorem `dvd_to_int` / 定理 `dvd_to_int`

English:
theorem dvd_to_int
  given: (m n : ZNum)
  statement: (m : Int) ∣ n ↔ m ∣ n
  proof: ⟨fun ⟨k, e⟩ => ⟨k, by rw [← of_to_int n, e]; simp⟩, fun ⟨k, e⟩ => ⟨k, by simp [e]⟩⟩

中文:
定理 dvd_to_int
  条件: (m n : ZNum)
  结论: (m : 整数) ∣ n ↔ m ∣ n
  证明: ⟨fun ⟨k, e⟩ => ⟨k, by rw [← of_to_int n, e]; simp⟩, fun ⟨k, e⟩ => ⟨k, by simp [e]⟩⟩

Depends on / 依赖: of_to_int
-/
theorem dvd_to_int (m n : ZNum) : (m : Int) ∣ n ↔ m ∣ n :=
  ⟨fun ⟨k, e⟩ => ⟨k, by rw [← of_to_int n, e]; simp⟩, fun ⟨k, e⟩ => ⟨k, by simp [e]⟩⟩

end ZNum

namespace PosNum

/--
theorem `divMod_to_nat_aux` / 定理 `divMod_to_nat_aux`

English:
theorem divMod_to_nat_aux
  statement: {n d : PosNum} {q r : Num} (h₁ : (r : Nat) + d * ((q : Nat) + q) = n)
  proof: by
  unfold divModAux
  have : forall {r₂}, Num.ofZNum' (Num.sub' r (Num.pos d)) = some r₂ ↔ (r : Nat) = r₂ + d := by
    intro r₂
    apply Num.mem_ofZNum'.trans
    rw [← ZNum.to_int_inj]; rw [Num.cast_toZNum]; rw [Num.cast_sub']; rw [sub_eq_iff_eq_add]; rw [← Int.natCast_inj]
    simp
  rcases e : Num.ofZNum' (Num.sub' r (Num.pos d)) with - | r₂
  · rw [Num.cast_bit0, two_mul]
    refine ⟨h₁, lt_of_not_ge fun h => ?_⟩
    obtain ⟨r₂, e'⟩ := Nat.le.dest h
    rw [← Num.to_of_nat r₂]; rw [add_comm] at e'
    cases e.symm.trans (this.2 e'.symm)
  · have := this.1 e
    simp only [Num.cast_bit1]
    constructor
    · rwa [two_mul, add_comm _ 1, mul_add, mul_one, ← add_assoc, ← this]
    · rwa [this, two_mul, add_lt_add_iff_right] at h₂

中文:
定理 divMod_to_nat_aux
  结论: {n d : PosNum} {q r : Num} (h₁ : (r : 自然数) + d * ((q : 自然数) + q) = n)
  证明: by
  unfold divModAux
  have : forall {r₂}, Num.ofZNum' (Num.sub' r (Num.pos d)) = some r₂ ↔ (r : Nat) = r₂ + d := by
    intro r₂
    apply Num.mem_ofZNum'.trans
    rw [← ZNum.to_int_inj]; rw [Num.cast_toZNum]; rw [Num.cast_sub']; rw [sub_eq_iff_eq_add]; rw [← Int.natCast_inj]
    simp
  rcases e : Num.ofZNum' (Num.sub' r (Num.pos d)) with - | r₂
  · rw [Num.cast_bit0, two_mul]
    refine ⟨h₁, lt_of_not_ge fun h => ?_⟩
    obtain ⟨r₂, e'⟩ := Nat.le.dest h
    rw [← Num.to_of_nat r₂]; rw [add_comm] at e'
    cases e.symm.trans (this.2 e'.symm)
  · have := this.1 e
    simp only [Num.cast_bit1]
    constructor
    · rwa [two_mul, add_comm _ 1, mul_add, mul_one, ← add_assoc, ← this]
    · rwa [this, two_mul, add_lt_add_iff_right] at h₂

Depends on / 依赖: Int.natCast_inj, Nat.le.dest, Num.cast_bit0, Num.cast_sub, Num.cast_toZNum, Num.mem_ofZNum, Num.ofZNum, Num.pos, Num.sub, Num.to_of_nat, ZNum.to_int_inj, add_comm, cast_bit0, cast_sub, cast_toZNum, divModAux, e.symm.trans, lt_of_not_ge, mem_ofZNum, natCast_inj
-/
theorem divMod_to_nat_aux {n d : PosNum} {q r : Num} (h₁ : (r : Nat) + d * ((q : Nat) + q) = n)
    (h₂ : (r : Nat) < 2 * d) :
    ((divModAux d q r).2 + d * (divModAux d q r).1 : Nat) = ↑n ∧ ((divModAux d q r).2 : Nat) < d := by
  unfold divModAux
  have : forall {r₂}, Num.ofZNum' (Num.sub' r (Num.pos d)) = some r₂ ↔ (r : Nat) = r₂ + d := by
    intro r₂
    apply Num.mem_ofZNum'.trans
    rw [← ZNum.to_int_inj]; rw [Num.cast_toZNum]; rw [Num.cast_sub']; rw [sub_eq_iff_eq_add]; rw [← Int.natCast_inj]
    simp
  rcases e : Num.ofZNum' (Num.sub' r (Num.pos d)) with - | r₂
  · rw [Num.cast_bit0, two_mul]
    refine ⟨h₁, lt_of_not_ge fun h => ?_⟩
    obtain ⟨r₂, e'⟩ := Nat.le.dest h
    rw [← Num.to_of_nat r₂]; rw [add_comm] at e'
    cases e.symm.trans (this.2 e'.symm)
  · have := this.1 e
    simp only [Num.cast_bit1]
    constructor
    · rwa [two_mul, add_comm _ 1, mul_add, mul_one, ← add_assoc, ← this]
    · rwa [this, two_mul, add_lt_add_iff_right] at h₂

/--
theorem `divMod_to_nat` / 定理 `divMod_to_nat`

English:
theorem divMod_to_nat
  given: (d n : PosNum)
  proof: by
  rw [Nat.div_mod_unique (PosNum.cast_pos _)]
  induction n with
  | one =>
    exact divMod_to_nat_aux (by simp) (Nat.mul_le_mul_left 2 (PosNum.cast_pos d : (0 : Nat) < d))
  | bit1 n IH =>
    unfold divMod
    -- Porting note: `cases'` didn't rewrite at `this`, so `revert` & `intro` are required.
    revert IH; obtain ⟨q, r⟩ := divMod d n; intro IH
    simp only at IH ⊢
    apply divMod_to_nat_aux <;> simp only [Num.cast_bit1, cast_bit1]
    · rw [← two_mul, ← two_mul, add_right_comm, mul_left_comm, ← mul_add, IH.1]
    · lia
  | bit0 n IH =>
    unfold divMod
    -- Porting note: `cases'` didn't rewrite at `this`, so `revert` & `intro` are required.
    revert IH; obtain ⟨q, r⟩ := divMod d n; intro IH
    simp only at IH ⊢
    apply divMod_to_nat_aux
    · simp only [Num.cast_bit0, cast_bit0]
      rw [← two_mul]; rw [← two_mul]; rw [mul_left_comm]; rw [← mul_add]; rw [← IH.1]
    · simpa using IH.2

@[simp]

中文:
定理 divMod_to_nat
  条件: (d n : PosNum)
  证明: by
  rw [Nat.div_mod_unique (PosNum.cast_pos _)]
  induction n with
  | one =>
    exact divMod_to_nat_aux (by simp) (Nat.mul_le_mul_left 2 (PosNum.cast_pos d : (0 : Nat) < d))
  | bit1 n IH =>
    unfold divMod
    -- Porting note: `cases'` didn't rewrite at `this`, so `revert` & `intro` are required.
    revert IH; obtain ⟨q, r⟩ := divMod d n; intro IH
    simp only at IH ⊢
    apply divMod_to_nat_aux <;> simp only [Num.cast_bit1, cast_bit1]
    · rw [← two_mul, ← two_mul, add_right_comm, mul_left_comm, ← mul_add, IH.1]
    · lia
  | bit0 n IH =>
    unfold divMod
    -- Porting note: `cases'` didn't rewrite at `this`, so `revert` & `intro` are required.
    revert IH; obtain ⟨q, r⟩ := divMod d n; intro IH
    simp only at IH ⊢
    apply divMod_to_nat_aux
    · simp only [Num.cast_bit0, cast_bit0]
      rw [← two_mul]; rw [← two_mul]; rw [mul_left_comm]; rw [← mul_add]; rw [← IH.1]
    · simpa using IH.2

@[simp]

Depends on / 依赖: Nat.div_mod_unique, Nat.mul_le_mul_left, PosNum, PosNum.cast_pos, cast_pos, divMod, divMod_to_nat_aux, div_mod_unique, mul_le_mul_left
-/
theorem divMod_to_nat (d n : PosNum) :
    (n / d : Nat) = (divMod d n).1 ∧ (n % d : Nat) = (divMod d n).2 := by
  rw [Nat.div_mod_unique (PosNum.cast_pos _)]
  induction n with
  | one =>
    exact divMod_to_nat_aux (by simp) (Nat.mul_le_mul_left 2 (PosNum.cast_pos d : (0 : Nat) < d))
  | bit1 n IH =>
    unfold divMod
    -- Porting note: `cases'` didn't rewrite at `this`, so `revert` & `intro` are required.
    revert IH; obtain ⟨q, r⟩ := divMod d n; intro IH
    simp only at IH ⊢
    apply divMod_to_nat_aux <;> simp only [Num.cast_bit1, cast_bit1]
    · rw [← two_mul, ← two_mul, add_right_comm, mul_left_comm, ← mul_add, IH.1]
    · lia
  | bit0 n IH =>
    unfold divMod
    -- Porting note: `cases'` didn't rewrite at `this`, so `revert` & `intro` are required.
    revert IH; obtain ⟨q, r⟩ := divMod d n; intro IH
    simp only at IH ⊢
    apply divMod_to_nat_aux
    · simp only [Num.cast_bit0, cast_bit0]
      rw [← two_mul]; rw [← two_mul]; rw [mul_left_comm]; rw [← mul_add]; rw [← IH.1]
    · simpa using IH.2

@[simp]
/--
theorem `div'_to_nat` / 定理 `div'_to_nat`

English:
theorem div'_to_nat
  given: (n d)
  statement: (div' n d : Nat) = n / d
  proof: (divMod_to_nat _ _).1.symm

@[simp]

中文:
定理 div'_to_nat
  条件: (n d)
  结论: (div' n d : 自然数) = n / d
  证明: (divMod_to_nat _ _).1.symm

@[simp]
-/
theorem div'_to_nat (n d) : (div' n d : Nat) = n / d :=
  (divMod_to_nat _ _).1.symm

@[simp]
/--
theorem `mod'_to_nat` / 定理 `mod'_to_nat`

English:
theorem mod'_to_nat
  given: (n d)
  statement: (mod' n d : Nat) = n % d
  proof: (divMod_to_nat _ _).2.symm

中文:
定理 mod'_to_nat
  条件: (n d)
  结论: (mod' n d : 自然数) = n % d
  证明: (divMod_to_nat _ _).2.symm
-/
theorem mod'_to_nat (n d) : (mod' n d : Nat) = n % d :=
  (divMod_to_nat _ _).2.symm

end PosNum

namespace Num

@[simp]
/--
theorem `div_zero` / 定理 `div_zero`

English:
theorem div_zero
  given: (n : Num)
  statement: n / 0 = 0
  proof: show n.div 0 = 0 by
    cases n
    · rfl
    · simp [Num.div]

@[simp, norm_cast]

中文:
定理 div_zero
  条件: (n : Num)
  结论: n / 0 = 0
  证明: show n.div 0 = 0 by
    cases n
    · rfl
    · simp [Num.div]

@[simp, norm_cast]
-/
protected theorem div_zero (n : Num) : n / 0 = 0 :=
  show n.div 0 = 0 by
    cases n
    · rfl
    · simp [Num.div]

@[simp, norm_cast]
/--
theorem `div_to_nat` / 定理 `div_to_nat`

English:
theorem div_to_nat
  statement: forall n d, ((n / d : Num) : Nat) = n / d

中文:
定理 div_to_nat
  结论: 对任意 n d, ((n / d : Num) : 自然数) = n / d
-/
theorem div_to_nat : forall n d, ((n / d : Num) : Nat) = n / d
  | 0, 0 => by simp
  | 0, pos _ => (Nat.zero_div _).symm
  | pos _, 0 => (Nat.div_zero _).symm
  | pos _, pos _ => PosNum.div'_to_nat _ _

@[simp]
/--
theorem `mod_zero` / 定理 `mod_zero`

English:
theorem mod_zero
  given: (n : Num)
  statement: n % 0 = n
  proof: show n.mod 0 = n by
    cases n
    · rfl
    · simp [Num.mod]

@[simp, norm_cast]

中文:
定理 mod_zero
  条件: (n : Num)
  结论: n % 0 = n
  证明: show n.mod 0 = n by
    cases n
    · rfl
    · simp [Num.mod]

@[simp, norm_cast]
-/
protected theorem mod_zero (n : Num) : n % 0 = n :=
  show n.mod 0 = n by
    cases n
    · rfl
    · simp [Num.mod]

@[simp, norm_cast]
/--
theorem `mod_to_nat` / 定理 `mod_to_nat`

English:
theorem mod_to_nat
  statement: forall n d, ((n % d : Num) : Nat) = n % d

中文:
定理 mod_to_nat
  结论: 对任意 n d, ((n % d : Num) : 自然数) = n % d
-/
theorem mod_to_nat : forall n d, ((n % d : Num) : Nat) = n % d
  | 0, 0 => by simp
  | 0, pos _ => (Nat.zero_mod _).symm
  | pos _, 0 => (Nat.mod_zero _).symm
  | pos _, pos _ => PosNum.mod'_to_nat _ _

/--
theorem `gcd_to_nat_aux` / 定理 `gcd_to_nat_aux`

English:
theorem gcd_to_nat_aux

中文:
定理 gcd_to_nat_aux
-/
theorem gcd_to_nat_aux :
    forall {n} {a b : Num}, a <= b -> (a * b).natSize <= n -> (gcdAux n a b : Nat) = Nat.gcd a b
  | 0, 0, _, _ab, _h => (Nat.gcd_zero_left _).symm
  | 0, pos _, 0, ab, _h => (not_lt_of_ge ab).elim rfl
| 0, pos _, pos _, _ab, h => (not_lt_of_ge h).elim PosNum.natSize_pos _
  | Nat.succ _, 0, _, _ab, _h => (Nat.gcd_zero_left _).symm
  | Nat.succ n, pos a, b, ab, h => by
    simp only [gcdAux, cast_pos]
    rw [Nat.gcd_rec]; rw [gcd_to_nat_aux]; rw [mod_to_nat]
    · rfl
    · rw [← le_to_nat, mod_to_nat]
      exact le_of_lt (Nat.mod_lt _ (PosNum.cast_pos _))
    rw [natSize_to_nat]; rw [mul_to_nat]; rw [Nat.size_le] at h ⊢
    rw [mod_to_nat]; rw [mul_comm]
    rw [pow_succ]; rw [← Nat.mod_add_div b (pos a)] at h
    refine lt_of_mul_lt_mul_right (lt_of_le_of_lt ?_ h) (Nat.zero_le 2)
    rw [mul_two]; rw [mul_add]
    gcongr _ + _ * ?_
    grw [Nat.mod_lt, ← le_to_nat.2 ab]
    · simp
    · exact PosNum.cast_pos _

@[simp]
/--
theorem `gcd_to_nat` / 定理 `gcd_to_nat`

English:
theorem gcd_to_nat
  statement: forall a b, (gcd a b : Nat) = Nat.gcd a b
  proof: by
  have : forall a b : Num, (a * b).natSize <= a.natSize + b.natSize := by
    intros
    simp only [natSize_to_nat, cast_mul]
    rw [Nat.size_le]; rw [pow_add]
    exact mul_lt_mul'' (Nat.lt_size_self _) (Nat.lt_size_self _) (Nat.zero_le _) (Nat.zero_le _)
  intros
  unfold gcd
  split_ifs with h
  · exact gcd_to_nat_aux h (this _ _)
  · rw [Nat.gcd_comm]
    exact gcd_to_nat_aux (le_of_not_ge h) (this _ _)

中文:
定理 gcd_to_nat
  结论: 对任意 a b, (最大公约数 a b : 自然数) = 自然数.最大公约数 a b
  证明: by
  have : forall a b : Num, (a * b).natSize <= a.natSize + b.natSize := by
    intros
    simp only [natSize_to_nat, cast_mul]
    rw [Nat.size_le]; rw [pow_add]
    exact mul_lt_mul'' (Nat.lt_size_self _) (Nat.lt_size_self _) (Nat.zero_le _) (Nat.zero_le _)
  intros
  unfold gcd
  split_ifs with h
  · exact gcd_to_nat_aux h (this _ _)
  · rw [Nat.gcd_comm]
    exact gcd_to_nat_aux (le_of_not_ge h) (this _ _)

Depends on / 依赖: Nat.gcd_comm, Nat.lt_size_self, Nat.size_le, Nat.zero_le, a.natSize, b.natSize, cast_mul, gcd_comm, gcd_to_nat_aux, intros, le_of_not_ge, lt_size_self, mul_lt_mul, natSize, natSize_to_nat, pow_add, size_le, split_ifs, zero_le
-/
theorem gcd_to_nat : forall a b, (gcd a b : Nat) = Nat.gcd a b := by
  have : forall a b : Num, (a * b).natSize <= a.natSize + b.natSize := by
    intros
    simp only [natSize_to_nat, cast_mul]
    rw [Nat.size_le]; rw [pow_add]
    exact mul_lt_mul'' (Nat.lt_size_self _) (Nat.lt_size_self _) (Nat.zero_le _) (Nat.zero_le _)
  intros
  unfold gcd
  split_ifs with h
  · exact gcd_to_nat_aux h (this _ _)
  · rw [Nat.gcd_comm]
    exact gcd_to_nat_aux (le_of_not_ge h) (this _ _)

/--
theorem `dvd_iff_mod_eq_zero` / 定理 `dvd_iff_mod_eq_zero`

English:
theorem dvd_iff_mod_eq_zero
  given: {m n : Num}
  statement: m ∣ n ↔ n % m = 0
  proof: by
  rw [← dvd_to_nat]; rw [Nat.dvd_iff_mod_eq_zero]; rw [← to_nat_inj]; rw [mod_to_nat]; rfl

中文:
定理 dvd_iff_mod_eq_zero
  条件: {m n : Num}
  结论: m ∣ n ↔ n % m = 0
  证明: by
  rw [← dvd_to_nat]; rw [Nat.dvd_iff_mod_eq_zero]; rw [← to_nat_inj]; rw [mod_to_nat]; rfl

Depends on / 依赖: Nat.dvd_iff_mod_eq_zero, dvd_iff_mod_eq_zero, dvd_to_nat, mod_to_nat, to_nat_inj
-/
theorem dvd_iff_mod_eq_zero {m n : Num} : m ∣ n ↔ n % m = 0 := by
  rw [← dvd_to_nat]; rw [Nat.dvd_iff_mod_eq_zero]; rw [← to_nat_inj]; rw [mod_to_nat]; rfl

/--
Instance `decidableDvd` / 实例 `decidableDvd`

English:
instance decidableDvd
  signature: : DecidableRel ((· ∣ ·) : Num -> Num -> Prop)

中文:
实例 decidableDvd
  签名: : DecidableRel ((· ∣ ·) : Num -> Num -> 命题)
-/
instance decidableDvd : DecidableRel ((· ∣ ·) : Num -> Num -> Prop)
  | _a, _b => decidable_of_iff' _ dvd_iff_mod_eq_zero

end Num

/--
Instance `PosNum.decidableDvd` / 实例 `PosNum.decidableDvd`

English:
instance PosNum.decidableDvd
  signature: : DecidableRel ((· ∣ ·) : PosNum -> PosNum -> Prop)

中文:
实例 PosNum.decidableDvd
  签名: : DecidableRel ((· ∣ ·) : PosNum -> PosNum -> 命题)
-/
instance PosNum.decidableDvd : DecidableRel ((· ∣ ·) : PosNum -> PosNum -> Prop)
  | _a, _b => Num.decidableDvd _ _

namespace ZNum

@[simp]
/--
theorem `div_zero` / 定理 `div_zero`

English:
theorem div_zero
  given: (n : ZNum)
  statement: n / 0 = 0
  proof: show n.div 0 = 0 by cases n <;> rfl

@[simp, norm_cast]

中文:
定理 div_zero
  条件: (n : ZNum)
  结论: n / 0 = 0
  证明: show n.div 0 = 0 by cases n <;> rfl

@[simp, norm_cast]
-/
protected theorem div_zero (n : ZNum) : n / 0 = 0 :=
  show n.div 0 = 0 by cases n <;> rfl

@[simp, norm_cast]
/--
theorem `div_to_int` / 定理 `div_to_int`

English:
theorem div_to_int
  statement: forall n d, ((n / d : ZNum) : Int) = n / d

中文:
定理 div_to_int
  结论: 对任意 n d, ((n / d : ZNum) : 整数) = n / d
-/
theorem div_to_int : forall n d, ((n / d : ZNum) : Int) = n / d
  | 0, 0 => by simp [Int.ediv_zero]
  | 0, pos _ => (Int.zero_ediv _).symm
  | 0, neg _ => (Int.zero_ediv _).symm
  | pos _, 0 => (Int.ediv_zero _).symm
  | neg _, 0 => (Int.ediv_zero _).symm
| pos n, pos d => (Num.cast_toZNum _).trans by rw [← Num.to_nat_to_int]; simp
| pos n, neg d => (Num.cast_toZNumNeg _).trans by rw [← Num.to_nat_to_int]; simp
  | neg n, pos d =>
    show -_ = -_ / ↑d by
      rw [n.to_int_eq_succ_pred]; rw [d.to_int_eq_succ_pred]; rw [← PosNum.to_nat_to_int]; rw [Num.succ'_to_nat]; rw [Num.div_to_nat]
      change -[n.pred' / ↑d+1] = -[n.pred' / (d.pred' + 1)+1]
      rw [d.to_nat_eq_succ_pred]
  | neg n, neg d =>
    show ↑(PosNum.pred' n / Num.pos d).succ' = -_ / -↑d by
      rw [n.to_int_eq_succ_pred]; rw [d.to_int_eq_succ_pred]; rw [← PosNum.to_nat_to_int]; rw [Num.succ'_to_nat]; rw [Num.div_to_nat]
      change (Nat.succ (_ / d) : Int) = Nat.succ (n.pred' / (d.pred' + 1))
      rw [d.to_nat_eq_succ_pred]

@[simp, norm_cast]
/--
theorem `mod_to_int` / 定理 `mod_to_int`

English:
theorem mod_to_int
  statement: forall n d, ((n % d : ZNum) : Int) = n % d

中文:
定理 mod_to_int
  结论: 对任意 n d, ((n % d : ZNum) : 整数) = n % d
-/
theorem mod_to_int : forall n d, ((n % d : ZNum) : Int) = n % d
  | 0, _ => (Int.zero_emod _).symm
  | pos n, d =>
(Num.cast_toZNum _).trans by
      rw [← Num.to_nat_to_int]; rw [cast_pos]; rw [Num.mod_to_nat]; rw [← PosNum.to_nat_to_int]; rw [abs_to_nat]
      rfl
  | neg n, d =>
(Num.cast_sub' _ _).trans by
      rw [← Num.to_nat_to_int]; rw [cast_neg]; rw [← Num.to_nat_to_int]; rw [Num.succ_to_nat]; rw [Num.mod_to_nat]; rw [abs_to_nat]; rw [← Int.subNatNat_eq_coe]; rw [n.to_int_eq_succ_pred]
      rfl

@[simp]
/--
theorem `gcd_to_nat` / 定理 `gcd_to_nat`

English:
theorem gcd_to_nat
  given: (a b)
  statement: (gcd a b : Nat) = Int.gcd a b
  proof: (Num.gcd_to_nat _ _).trans by simp only [abs_to_nat]; rfl

中文:
定理 gcd_to_nat
  条件: (a b)
  结论: (最大公约数 a b : 自然数) = 整数.最大公约数 a b
  证明: (Num.gcd_to_nat _ _).trans by simp only [abs_to_nat]; rfl

Depends on / 依赖: Num.gcd_to_nat, abs_to_nat, gcd_to_nat
-/
theorem gcd_to_nat (a b) : (gcd a b : Nat) = Int.gcd a b :=
(Num.gcd_to_nat _ _).trans by simp only [abs_to_nat]; rfl

/--
theorem `dvd_iff_mod_eq_zero` / 定理 `dvd_iff_mod_eq_zero`

English:
theorem dvd_iff_mod_eq_zero
  given: {m n : ZNum}
  statement: m ∣ n ↔ n % m = 0
  proof: by
  rw [← dvd_to_int]; rw [Int.dvd_iff_emod_eq_zero]; rw [← to_int_inj]; rw [mod_to_int]; rfl

中文:
定理 dvd_iff_mod_eq_zero
  条件: {m n : ZNum}
  结论: m ∣ n ↔ n % m = 0
  证明: by
  rw [← dvd_to_int]; rw [Int.dvd_iff_emod_eq_zero]; rw [← to_int_inj]; rw [mod_to_int]; rfl

Depends on / 依赖: Int.dvd_iff_emod_eq_zero, dvd_iff_emod_eq_zero, dvd_to_int, mod_to_int, to_int_inj
-/
theorem dvd_iff_mod_eq_zero {m n : ZNum} : m ∣ n ↔ n % m = 0 := by
  rw [← dvd_to_int]; rw [Int.dvd_iff_emod_eq_zero]; rw [← to_int_inj]; rw [mod_to_int]; rfl

/--
Instance `decidableDvd` / 实例 `decidableDvd`

English:
instance decidableDvd
  signature: : DecidableRel ((· ∣ ·) : ZNum -> ZNum -> Prop)

中文:
实例 decidableDvd
  签名: : DecidableRel ((· ∣ ·) : ZNum -> ZNum -> 命题)
-/
instance decidableDvd : DecidableRel ((· ∣ ·) : ZNum -> ZNum -> Prop)
  | _a, _b => decidable_of_iff' _ dvd_iff_mod_eq_zero

end ZNum
