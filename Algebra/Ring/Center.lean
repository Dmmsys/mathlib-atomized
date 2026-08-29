/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Jireh Loreaux
-/
module

public import Mathlib.Algebra.Group.Center
public import Mathlib.Data.Int.Cast.Lemmas

/-!
# Centers of rings

-/

public section

assert_not_exists RelIso Finset Subsemigroup Field

variable {M : Type*}

namespace Set

variable (M)

@[simp]
/--
theorem `natCast_mem_center` / 定理 `natCast_mem_center`

English:
theorem natCast_mem_center
  given: [NonAssocSemiring M] (n : Nat)
  statement: (n : M) in Set.center M where
  proof: by rw [commute_iff_eq, Nat.commute_cast]
  left_assoc _ _ := by
    induction n with
    | zero => rw [Nat.cast_zero, zero_mul, zero_mul, zero_mul]
    | succ n ihn => rw [Nat.cast_succ, add_mul, one_mul, ihn, add_mul, add_mul, one_mul]
  right_assoc _ _ := by
    induction n with
    | zero => rw [Nat.cast_zero, mul_zero, mul_zero, mul_zero]
    | succ n ihn => rw [Nat.cast_succ, mul_add, ihn, mul_add, mul_add, mul_one, mul_one]

@[simp]

中文:
定理 natCast_mem_center
  条件: [非结合半环 M] (n : 自然数)
  结论: (n : M) in 集合.center M where
  证明: by rw [commute_iff_eq, Nat.commute_cast]
  left_assoc _ _ := by
    induction n with
    | zero => rw [Nat.cast_zero, zero_mul, zero_mul, zero_mul]
    | succ n ihn => rw [Nat.cast_succ, add_mul, one_mul, ihn, add_mul, add_mul, one_mul]
  right_assoc _ _ := by
    induction n with
    | zero => rw [Nat.cast_zero, mul_zero, mul_zero, mul_zero]
    | succ n ihn => rw [Nat.cast_succ, mul_add, ihn, mul_add, mul_add, mul_one, mul_one]

@[simp]

Depends on / 依赖: Nat.cast_succ, Nat.cast_zero, Nat.commute_cast, add_mul, cast_succ, cast_zero, commute_cast, commute_iff_eq, left_assoc, mul_add, mul_one, mul_zero, one_mul, right_assoc, zero_mul
-/
theorem natCast_mem_center [NonAssocSemiring M] (n : Nat) : (n : M) in Set.center M where
  comm _ := by rw [commute_iff_eq, Nat.commute_cast]
  left_assoc _ _ := by
    induction n with
    | zero => rw [Nat.cast_zero, zero_mul, zero_mul, zero_mul]
    | succ n ihn => rw [Nat.cast_succ, add_mul, one_mul, ihn, add_mul, add_mul, one_mul]
  right_assoc _ _ := by
    induction n with
    | zero => rw [Nat.cast_zero, mul_zero, mul_zero, mul_zero]
    | succ n ihn => rw [Nat.cast_succ, mul_add, ihn, mul_add, mul_add, mul_one, mul_one]

@[simp]
/--
theorem `ofNat_mem_center` / 定理 `ofNat_mem_center`

English:
theorem ofNat_mem_center
  given: [NonAssocSemiring M] (n : Nat) [n.AtLeastTwo]
  proof: natCast_mem_center M n

@[simp]

中文:
定理 of自然数_mem_center
  条件: [非结合半环 M] (n : 自然数) [n.AtLeastTwo]
  证明: natCast_mem_center M n

@[simp]

Depends on / 依赖: natCast_mem_center
-/
theorem ofNat_mem_center [NonAssocSemiring M] (n : Nat) [n.AtLeastTwo] :
    ofNat(n) in Set.center M :=
  natCast_mem_center M n

@[simp]
/--
theorem `intCast_mem_center` / 定理 `intCast_mem_center`

English:
theorem intCast_mem_center
  given: [NonAssocRing M] (n : Int)
  statement: (n : M) in Set.center M where
  proof: by rw [commute_iff_eq, Int.commute_cast]
  left_assoc _ _ := match n with
    | (n : Nat) => by rw [Int.cast_natCast, (natCast_mem_center _ n).left_assoc _ _]
    | Int.negSucc n => by
      rw [Int.cast_negSucc]; rw [Nat.cast_add]; rw [Nat.cast_one]; rw [neg_add_rev]; rw [add_mul]; rw [add_mul]; rw [add_mul]; rw [neg_mul]; rw [one_mul]; rw [neg_mul 1]; rw [one_mul]; rw [← neg_mul]; rw [add_right_inj]; rw [neg_mul]; rw [(natCast_mem_center _ n).left_assoc _ _]; rw [neg_mul]; rw [neg_mul]
  right_assoc _ _ := match n with
    | (n : Nat) => by rw [Int.cast_natCast, (natCast_mem_center _ n).right_assoc _ _]
    | Int.negSucc n => by
        simp only [Int.cast_negSucc, Nat.cast_add, Nat.cast_one, neg_add_rev]
        rw [mul_add]; rw [mul_add]; rw [mul_add]; rw [mul_neg]; rw [mul_one]; rw [mul_neg]; rw [mul_neg]; rw [mul_one]; rw [mul_neg]; rw [add_right_inj]; rw [(natCast_mem_center _ n).right_assoc _ _]; rw [mul_neg]; rw [mul_neg]

中文:
定理 intCast_mem_center
  条件: [非结合环 M] (n : 整数)
  结论: (n : M) in 集合.center M where
  证明: by rw [commute_iff_eq, Int.commute_cast]
  left_assoc _ _ := match n with
    | (n : Nat) => by rw [Int.cast_natCast, (natCast_mem_center _ n).left_assoc _ _]
    | Int.negSucc n => by
      rw [Int.cast_negSucc]; rw [Nat.cast_add]; rw [Nat.cast_one]; rw [neg_add_rev]; rw [add_mul]; rw [add_mul]; rw [add_mul]; rw [neg_mul]; rw [one_mul]; rw [neg_mul 1]; rw [one_mul]; rw [← neg_mul]; rw [add_right_inj]; rw [neg_mul]; rw [(natCast_mem_center _ n).left_assoc _ _]; rw [neg_mul]; rw [neg_mul]
  right_assoc _ _ := match n with
    | (n : Nat) => by rw [Int.cast_natCast, (natCast_mem_center _ n).right_assoc _ _]
    | Int.negSucc n => by
        simp only [Int.cast_negSucc, Nat.cast_add, Nat.cast_one, neg_add_rev]
        rw [mul_add]; rw [mul_add]; rw [mul_add]; rw [mul_neg]; rw [mul_one]; rw [mul_neg]; rw [mul_neg]; rw [mul_one]; rw [mul_neg]; rw [add_right_inj]; rw [(natCast_mem_center _ n).right_assoc _ _]; rw [mul_neg]; rw [mul_neg]

Depends on / 依赖: Int.cast_natCast, Int.cast_negSucc, Int.commute_cast, Int.negSucc, Nat.cast_add, Nat.cast_one, add_mul, add_right_inj, cast_add, cast_natCast, cast_negSucc, cast_one, commute_cast, commute_iff_eq, left_assoc, natCast_mem_center, negSucc, neg_add_rev, neg_mul, one_mul
-/
theorem intCast_mem_center [NonAssocRing M] (n : Int) : (n : M) in Set.center M where
  comm _ := by rw [commute_iff_eq, Int.commute_cast]
  left_assoc _ _ := match n with
    | (n : Nat) => by rw [Int.cast_natCast, (natCast_mem_center _ n).left_assoc _ _]
    | Int.negSucc n => by
      rw [Int.cast_negSucc]; rw [Nat.cast_add]; rw [Nat.cast_one]; rw [neg_add_rev]; rw [add_mul]; rw [add_mul]; rw [add_mul]; rw [neg_mul]; rw [one_mul]; rw [neg_mul 1]; rw [one_mul]; rw [← neg_mul]; rw [add_right_inj]; rw [neg_mul]; rw [(natCast_mem_center _ n).left_assoc _ _]; rw [neg_mul]; rw [neg_mul]
  right_assoc _ _ := match n with
    | (n : Nat) => by rw [Int.cast_natCast, (natCast_mem_center _ n).right_assoc _ _]
    | Int.negSucc n => by
        simp only [Int.cast_negSucc, Nat.cast_add, Nat.cast_one, neg_add_rev]
        rw [mul_add]; rw [mul_add]; rw [mul_add]; rw [mul_neg]; rw [mul_one]; rw [mul_neg]; rw [mul_neg]; rw [mul_one]; rw [mul_neg]; rw [add_right_inj]; rw [(natCast_mem_center _ n).right_assoc _ _]; rw [mul_neg]; rw [mul_neg]

variable {M}

@[simp]
/--
theorem `add_mem_center` / 定理 `add_mem_center`

English:
theorem add_mem_center
  given: [Distrib M] {a b : M} (ha : a in Set.center M) (hb : b in Set.center M)
  proof: by rw [commute_iff_eq, add_mul, mul_add, ha.comm, hb.comm]
  left_assoc _ _ := by rw [add_mul, ha.left_assoc, hb.left_assoc, ← add_mul, ← add_mul]
  right_assoc _ _ := by rw [mul_add, ha.right_assoc, hb.right_assoc, ← mul_add, ← mul_add]

@[simp]

中文:
定理 add_mem_center
  条件: [Distrib M] {a b : M} (ha : a in 集合.center M) (hb : b in 集合.center M)
  证明: by rw [commute_iff_eq, add_mul, mul_add, ha.comm, hb.comm]
  left_assoc _ _ := by rw [add_mul, ha.left_assoc, hb.left_assoc, ← add_mul, ← add_mul]
  right_assoc _ _ := by rw [mul_add, ha.right_assoc, hb.right_assoc, ← mul_add, ← mul_add]

@[simp]

Depends on / 依赖: add_mul, commute_iff_eq, ha.comm, ha.left_assoc, ha.right_assoc, hb.comm, hb.left_assoc, hb.right_assoc, left_assoc, mul_add, right_assoc
-/
theorem add_mem_center [Distrib M] {a b : M} (ha : a in Set.center M) (hb : b in Set.center M) :
    a + b in Set.center M where
  comm _ := by rw [commute_iff_eq, add_mul, mul_add, ha.comm, hb.comm]
  left_assoc _ _ := by rw [add_mul, ha.left_assoc, hb.left_assoc, ← add_mul, ← add_mul]
  right_assoc _ _ := by rw [mul_add, ha.right_assoc, hb.right_assoc, ← mul_add, ← mul_add]

@[simp]
/--
theorem `neg_mem_center` / 定理 `neg_mem_center`

English:
theorem neg_mem_center
  given: [NonUnitalNonAssocRing M] {a : M} (ha : a in Set.center M)
  proof: by rw [commute_iff_eq, ← neg_mul_comm, ← ha.comm, neg_mul_comm]
  left_assoc _ _ := by rw [neg_mul, ha.left_assoc, neg_mul, neg_mul]
  right_assoc _ _ := by rw [mul_neg, ha.right_assoc, mul_neg, mul_neg]

中文:
定理 neg_mem_center
  条件: [非幺非结合环 M] {a : M} (ha : a in 集合.center M)
  证明: by rw [commute_iff_eq, ← neg_mul_comm, ← ha.comm, neg_mul_comm]
  left_assoc _ _ := by rw [neg_mul, ha.left_assoc, neg_mul, neg_mul]
  right_assoc _ _ := by rw [mul_neg, ha.right_assoc, mul_neg, mul_neg]

Depends on / 依赖: commute_iff_eq, ha.comm, ha.left_assoc, ha.right_assoc, left_assoc, mul_neg, neg_mul, neg_mul_comm, right_assoc
-/
theorem neg_mem_center [NonUnitalNonAssocRing M] {a : M} (ha : a in Set.center M) :
    -a in Set.center M where
  comm _ := by rw [commute_iff_eq, ← neg_mul_comm, ← ha.comm, neg_mul_comm]
  left_assoc _ _ := by rw [neg_mul, ha.left_assoc, neg_mul, neg_mul]
  right_assoc _ _ := by rw [mul_neg, ha.right_assoc, mul_neg, mul_neg]

end Set
