/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.NeZero
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Fin.Rev

/-!
# Fin is a group

This file contains the additive and multiplicative monoid instances on `Fin n`.

See note [foundational algebra order theory].
-/

@[expose] public section

assert_not_exists IsOrderedMonoid MonoidWithZero

open Nat

namespace Fin
variable {n : Nat}


/--
Instance `addCommSemigroup` / 实例 `addCommSemigroup`

English:
instance addCommSemigroup
  signature: (n : Nat)
  body: by simp [add_def, Nat.add_assoc]
  add_comm := by simp [add_def, Nat.add_comm]

中文:
实例 addCommSemigroup
  签名: (n : 自然数)
  定义体: by simp [add_def, Nat.add_assoc]
  add_comm := by simp [add_def, Nat.add_comm]

Depends on / 依赖: Nat.add_assoc, Nat.add_comm, add_assoc, add_comm, add_def
-/
instance addCommSemigroup (n : Nat) : AddCommSemigroup (Fin n) where
  add_assoc := by simp [add_def, Nat.add_assoc]
  add_comm := by simp [add_def, Nat.add_comm]

/--
Instance `addCommMonoid` / 实例 `addCommMonoid`

English:
instance addCommMonoid
  signature: (n : Nat) [NeZero n]
  body: Fin.zero_add
  add_zero := Fin.add_zero
  nsmul := nsmulRec
  __ := Fin.addCommSemigroup n

中文:
实例 addCommMonoid
  签名: (n : 自然数) [NeZero n]
  定义体: Fin.zero_add
  add_zero := Fin.add_zero
  nsmul := nsmulRec
  __ := Fin.addCommSemigroup n

Depends on / 依赖: Fin.zero_add, zero_add
-/
instance addCommMonoid (n : Nat) [NeZero n] : AddCommMonoid (Fin n) where
  zero_add := Fin.zero_add
  add_zero := Fin.add_zero
  nsmul := nsmulRec
  __ := Fin.addCommSemigroup n

/--
This is not a global instance, but can introduced locally using `open Fin.NatCast in ...`.

This is not an instance because the `binop%` elaborator assumes that
there are no non-trivial coercion loops,
but this instance would introduce a coercion from `Nat` to `Fin n` and back.
Non-trivial loops lead to undesirable and counterintuitive elaboration behavior.

For example, for `x : Fin k` and `n : Nat`,
it causes `x < n` to be elaborated as `x < ↑n` rather than `↑x < n`,
silently introducing wraparound arithmetic.
-/
@[instance_reducible]
/--
Definition of `instAddMonoidWithOne` / `instAddMonoidWithOne` 的定义

English:
definition instAddMonoidWithOne
  signature: (n) [NeZero n]
  body: (inferInstance : AddCommMonoid (Fin n))
  natCast i := Fin.ofNat n i
  natCast_zero := rfl
  natCast_succ _ := Fin.ext (add_mod _ _ _)

中文:
定义 instAddMonoidWithOne
  签名: (n) [NeZero n]
  定义体: (inferInstance : AddCommMonoid (Fin n))
  natCast i := Fin.ofNat n i
  natCast_zero := rfl
  natCast_succ _ := Fin.ext (add_mod _ _ _)

Depends on / 依赖: AddCommMonoid
-/
def instAddMonoidWithOne (n) [NeZero n] : AddMonoidWithOne (Fin n) where
  __ := (inferInstance : AddCommMonoid (Fin n))
  natCast i := Fin.ofNat n i
  natCast_zero := rfl
  natCast_succ _ := Fin.ext (add_mod _ _ _)

namespace NatCast

attribute [scoped instance] Fin.instAddMonoidWithOne

end NatCast

/--
Instance `addCommGroup` / 实例 `addCommGroup`

English:
instance addCommGroup
  signature: (n : Nat) [NeZero n]
  body: addCommMonoid n
  __ := neg n
  neg_add_cancel := fun ⟨a, ha⟩ =>
Fin.ext (Nat.mod_add_mod _ _ _).trans by
      rw [Fin.val_zero]; rw [Nat.sub_add_cancel]; rw [Nat.mod_self]
      exact le_of_lt ha
  sub := Fin.sub
  sub_eq_add_neg := fun ⟨a, ha⟩ ⟨b, hb⟩ =>
Fin.ext by simp [Fin.sub_def, Fin.neg_def,

中文:
实例 addCommGroup
  签名: (n : 自然数) [NeZero n]
  定义体: addCommMonoid n
  __ := neg n
  neg_add_cancel := fun ⟨a, ha⟩ =>
Fin.ext (Nat.mod_add_mod _ _ _).trans by
      rw [Fin.val_zero]; rw [Nat.sub_add_cancel]; rw [Nat.mod_self]
      exact le_of_lt ha
  sub := Fin.sub
  sub_eq_add_neg := fun ⟨a, ha⟩ ⟨b, hb⟩ =>
Fin.ext by simp [Fin.sub_def, Fin.neg_def,

Depends on / 依赖: addCommMonoid
-/
instance addCommGroup (n : Nat) [NeZero n] : AddCommGroup (Fin n) where
  __ := addCommMonoid n
  __ := neg n
  neg_add_cancel := fun ⟨a, ha⟩ =>
Fin.ext (Nat.mod_add_mod _ _ _).trans by
      rw [Fin.val_zero]; rw [Nat.sub_add_cancel]; rw [Nat.mod_self]
      exact le_of_lt ha
  sub := Fin.sub
  sub_eq_add_neg := fun ⟨a, ha⟩ ⟨b, hb⟩ =>
Fin.ext by simp [Fin.sub_def, Fin.neg_def, Fin.add_def, Nat.add_comm]
  zsmul := zsmulRec

/--
Instance `instInvolutiveNeg` / 实例 `instInvolutiveNeg`

English:
instance instInvolutiveNeg
  signature: (n : Nat)
  body: Nat.casesOn n finZeroElim fun _i => neg_neg

中文:
实例 instInvolutiveNeg
  签名: (n : 自然数)
  定义体: Nat.casesOn n finZeroElim fun _i => neg_neg

Depends on / 依赖: Nat.casesOn, casesOn, finZeroElim, neg_neg
-/
instance instInvolutiveNeg (n : Nat) : InvolutiveNeg (Fin n) where
  neg_neg := Nat.casesOn n finZeroElim fun _i => neg_neg

/--
Instance `instIsCancelAdd` / 实例 `instIsCancelAdd`

English:
instance instIsCancelAdd
  signature: (n : Nat)
  body: Nat.casesOn n finZeroElim fun _i _ _ _ => add_left_cancel
  add_right_cancel := Nat.casesOn n finZeroElim fun _i _ _ _ => add_right_cancel

中文:
实例 instIsCancelAdd
  签名: (n : 自然数)
  定义体: Nat.casesOn n finZeroElim fun _i _ _ _ => add_left_cancel
  add_right_cancel := Nat.casesOn n finZeroElim fun _i _ _ _ => add_right_cancel

Depends on / 依赖: Nat.casesOn, add_left_cancel, casesOn, finZeroElim
-/
instance instIsCancelAdd (n : Nat) : IsCancelAdd (Fin n) where
  add_left_cancel := Nat.casesOn n finZeroElim fun _i _ _ _ => add_left_cancel
  add_right_cancel := Nat.casesOn n finZeroElim fun _i _ _ _ => add_right_cancel

/--
Instance `instAddLeftCancelSemigroup` / 实例 `instAddLeftCancelSemigroup`

English:
instance instAddLeftCancelSemigroup
  signature: (n : Nat)
  body: { Fin.addCommSemigroup n, Fin.instIsCancelAdd n with }

中文:
实例 instAddLeftCancelSemigroup
  签名: (n : 自然数)
  定义体: { Fin.addCommSemigroup n, Fin.instIsCancelAdd n with }

Depends on / 依赖: Fin.addCommSemigroup, Fin.instIsCancelAdd, addCommSemigroup, instIsCancelAdd
-/
instance instAddLeftCancelSemigroup (n : Nat) : AddLeftCancelSemigroup (Fin n) :=
  { Fin.addCommSemigroup n, Fin.instIsCancelAdd n with }

/--
Instance `instAddRightCancelSemigroup` / 实例 `instAddRightCancelSemigroup`

English:
instance instAddRightCancelSemigroup
  signature: (n : Nat)
  body: { Fin.addCommSemigroup n, Fin.instIsCancelAdd n with }

中文:
实例 instAddRightCancelSemigroup
  签名: (n : 自然数)
  定义体: { Fin.addCommSemigroup n, Fin.instIsCancelAdd n with }

Depends on / 依赖: Fin.addCommSemigroup, Fin.instIsCancelAdd, addCommSemigroup, instIsCancelAdd
-/
instance instAddRightCancelSemigroup (n : Nat) : AddRightCancelSemigroup (Fin n) :=
  { Fin.addCommSemigroup n, Fin.instIsCancelAdd n with }

/-! ### Miscellaneous lemmas -/

open scoped Fin.NatCast Fin.IntCast in
/--
theorem `intCast_def'` / 定理 `intCast_def'`

English:
theorem intCast_def'
  given: {n : Nat} [NeZero n] (x : Int)
  proof: Fin.intCast_def _

中文:
定理 intCast_def'
  条件: {n : 自然数} [NeZero n] (x : 整数)
  证明: Fin.intCast_def _

Depends on / 依赖: Fin.intCast_def, intCast_def
-/
theorem intCast_def' {n : Nat} [NeZero n] (x : Int) :
    (x : Fin n) = if 0 <= x then ↑x.natAbs else -↑x.natAbs :=
  Fin.intCast_def _

/--
lemma `coe_sub_one` / 引理 `coe_sub_one`

English:
lemma coe_sub_one
  given: (a : Fin (n + 1))
  statement: ↑(a - 1) = if a = 0 then n else a - 1
  proof: by
  cases n
  · simp
  split_ifs with h
  · simp [h]
  exact val_sub_one_of_ne_zero h

@[simp]

中文:
引理 coe_sub_one
  条件: (a : Fin (n + 1))
  结论: ↑(a - 1) = if a = 0 then n else a - 1
  证明: by
  cases n
  · simp
  split_ifs with h
  · simp [h]
  exact val_sub_one_of_ne_zero h

@[simp]

Depends on / 依赖: split_ifs, val_sub_one_of_ne_zero
-/
lemma coe_sub_one (a : Fin (n + 1)) : ↑(a - 1) = if a = 0 then n else a - 1 := by
  cases n
  · simp
  split_ifs with h
  · simp [h]
  exact val_sub_one_of_ne_zero h

@[simp]
/--
lemma `lt_sub_iff` / 引理 `lt_sub_iff`

English:
lemma lt_sub_iff
  given: {n : Nat} {a b : Fin n}
  statement: a < a - b ↔ a < b
  proof: by
  fin_omega

@[simp]

中文:
引理 lt_sub_iff
  条件: {n : 自然数} {a b : Fin n}
  结论: a < a - b ↔ a < b
  证明: by
  fin_omega

@[simp]

Depends on / 依赖: fin_omega
-/
lemma lt_sub_iff {n : Nat} {a b : Fin n} : a < a - b ↔ a < b := by
  fin_omega

@[simp]
/--
lemma `sub_le_iff` / 引理 `sub_le_iff`

English:
lemma sub_le_iff
  given: {n : Nat} {a b : Fin n}
  statement: a - b <= a ↔ b <= a
  proof: by
  rw [← not_iff_not]; rw [Fin.not_le]; rw [Fin.not_le]; rw [lt_sub_iff]

@[simp]

中文:
引理 sub_le_iff
  条件: {n : 自然数} {a b : Fin n}
  结论: a - b <= a ↔ b <= a
  证明: by
  rw [← not_iff_not]; rw [Fin.not_le]; rw [Fin.not_le]; rw [lt_sub_iff]

@[simp]

Depends on / 依赖: Fin.not_le, lt_sub_iff, not_iff_not, not_le
-/
lemma sub_le_iff {n : Nat} {a b : Fin n} : a - b <= a ↔ b <= a := by
  rw [← not_iff_not]; rw [Fin.not_le]; rw [Fin.not_le]; rw [lt_sub_iff]

@[simp]
/--
lemma `lt_one_iff` / 引理 `lt_one_iff`

English:
lemma lt_one_iff
  given: {n : Nat} (x : Fin (n + 2))
  statement: x < 1 ↔ x = 0
  proof: by
  simp [lt_def]

中文:
引理 lt_one_iff
  条件: {n : 自然数} (x : Fin (n + 2))
  结论: x < 1 ↔ x = 0
  证明: by
  simp [lt_def]

Depends on / 依赖: lt_def
-/
lemma lt_one_iff {n : Nat} (x : Fin (n + 2)) : x < 1 ↔ x = 0 := by
  simp [lt_def]

/--
lemma `lt_sub_one_iff` / 引理 `lt_sub_one_iff`

English:
lemma lt_sub_one_iff
  given: {k : Fin (n + 2)}
  statement: k < k - 1 ↔ k = 0
  proof: by
  simp

中文:
引理 lt_sub_one_iff
  条件: {k : Fin (n + 2)}
  结论: k < k - 1 ↔ k = 0
  证明: by
  simp
-/
lemma lt_sub_one_iff {k : Fin (n + 2)} : k < k - 1 ↔ k = 0 := by
  simp

/--
lemma `le_sub_one_iff` / 引理 `le_sub_one_iff`

English:
lemma le_sub_one_iff
  given: {k : Fin (n + 1)}
  statement: k <= k - 1 ↔ k = 0
  proof: by
  cases n
  · simp [fin_one_eq_zero k]
  simp only [le_def]
  rw [← lt_sub_one_iff]; rw [le_iff_lt_or_eq]; rw [val_fin_lt]; rw [val_inj]; rw [lt_sub_one_iff]; rw [or_iff_left_iff_imp]; rw [eq_comm]; rw [sub_eq_iff_eq_add]
  simp

中文:
引理 le_sub_one_iff
  条件: {k : Fin (n + 1)}
  结论: k <= k - 1 ↔ k = 0
  证明: by
  cases n
  · simp [fin_one_eq_zero k]
  simp only [le_def]
  rw [← lt_sub_one_iff]; rw [le_iff_lt_or_eq]; rw [val_fin_lt]; rw [val_inj]; rw [lt_sub_one_iff]; rw [or_iff_left_iff_imp]; rw [eq_comm]; rw [sub_eq_iff_eq_add]
  simp
-/
@[simp] lemma le_sub_one_iff {k : Fin (n + 1)} : k <= k - 1 ↔ k = 0 := by
  cases n
  · simp [fin_one_eq_zero k]
  simp only [le_def]
  rw [← lt_sub_one_iff]; rw [le_iff_lt_or_eq]; rw [val_fin_lt]; rw [val_inj]; rw [lt_sub_one_iff]; rw [or_iff_left_iff_imp]; rw [eq_comm]; rw [sub_eq_iff_eq_add]
  simp

/--
lemma `sub_one_lt_iff` / 引理 `sub_one_lt_iff`

English:
lemma sub_one_lt_iff
  given: {k : Fin (n + 1)}
  statement: k - 1 < k ↔ 0 < k
  proof: not_iff_not.1 by simp only [lt_def, not_lt, val_fin_le, le_sub_one_iff, le_zero_iff]

中文:
引理 sub_one_lt_iff
  条件: {k : Fin (n + 1)}
  结论: k - 1 < k ↔ 0 < k
  证明: not_iff_not.1 by simp only [lt_def, not_lt, val_fin_le, le_sub_one_iff, le_zero_iff]

Depends on / 依赖: le_sub_one_iff, le_zero_iff, lt_def, not_iff_not, not_lt, val_fin_le
-/
lemma sub_one_lt_iff {k : Fin (n + 1)} : k - 1 < k ↔ 0 < k :=
not_iff_not.1 by simp only [lt_def, not_lt, val_fin_le, le_sub_one_iff, le_zero_iff]

/--
lemma `neg_last` / 引理 `neg_last`

English:
lemma neg_last
  given: (n : Nat)
  statement: -Fin.last n = 1
  proof: by simp [neg_eq_iff_add_eq_zero]

中文:
引理 neg_last
  条件: (n : 自然数)
  结论: -Fin.last n = 1
  证明: by simp [neg_eq_iff_add_eq_zero]
-/
@[simp] lemma neg_last (n : Nat) : -Fin.last n = 1 := by simp [neg_eq_iff_add_eq_zero]

open Fin.NatCast in
/--
lemma `neg_natCast_eq_one` / 引理 `neg_natCast_eq_one`

English:
lemma neg_natCast_eq_one
  given: (n : Nat)
  statement: -(n : Fin (n + 1)) = 1
  proof: by
  simp only [natCast_eq_last, neg_last]

中文:
引理 neg_natCast_eq_one
  条件: (n : 自然数)
  结论: -(n : Fin (n + 1)) = 1
  证明: by
  simp only [natCast_eq_last, neg_last]

Depends on / 依赖: natCast_eq_last, neg_last
-/
lemma neg_natCast_eq_one (n : Nat) : -(n : Fin (n + 1)) = 1 := by
  simp only [natCast_eq_last, neg_last]

/--
lemma `rev_add` / 引理 `rev_add`

English:
lemma rev_add
  given: (a b : Fin n)
  statement: rev (a + b) = rev a - b
  proof: by
  cases n
  · exact a.elim0
  rw [← last_sub]; rw [← last_sub]; rw [sub_add_eq_sub_sub]

中文:
引理 rev_add
  条件: (a b : Fin n)
  结论: rev (a + b) = rev a - b
  证明: by
  cases n
  · exact a.elim0
  rw [← last_sub]; rw [← last_sub]; rw [sub_add_eq_sub_sub]

Depends on / 依赖: a.elim0, last_sub, sub_add_eq_sub_sub
-/
lemma rev_add (a b : Fin n) : rev (a + b) = rev a - b := by
  cases n
  · exact a.elim0
  rw [← last_sub]; rw [← last_sub]; rw [sub_add_eq_sub_sub]

/--
lemma `rev_sub` / 引理 `rev_sub`

English:
lemma rev_sub
  given: (a b : Fin n)
  statement: rev (a - b) = rev a + b
  proof: by
  rw [rev_eq_iff]; rw [rev_add]; rw [rev_rev]

中文:
引理 rev_sub
  条件: (a b : Fin n)
  结论: rev (a - b) = rev a + b
  证明: by
  rw [rev_eq_iff]; rw [rev_add]; rw [rev_rev]

Depends on / 依赖: rev_add, rev_eq_iff, rev_rev
-/
lemma rev_sub (a b : Fin n) : rev (a - b) = rev a + b := by
  rw [rev_eq_iff]; rw [rev_add]; rw [rev_rev]

/--
lemma `lt_add_one_of_succ_lt` / 引理 `lt_add_one_of_succ_lt`

English:
lemma lt_add_one_of_succ_lt
  given: {n : Nat} [NeZero n] {a : Fin n} (ha : a + 1 < n)
  statement: a < a + 1
  proof: by
  rw [lt_def]; rw [val_add]; rw [coe_ofNat_eq_mod]; rw [Nat.add_mod_mod]; rw [Nat.mod_eq_of_lt ha]
  lia

中文:
引理 lt_add_one_of_succ_lt
  条件: {n : 自然数} [NeZero n] {a : Fin n} (ha : a + 1 < n)
  结论: a < a + 1
  证明: by
  rw [lt_def]; rw [val_add]; rw [coe_ofNat_eq_mod]; rw [Nat.add_mod_mod]; rw [Nat.mod_eq_of_lt ha]
  lia

Depends on / 依赖: Nat.add_mod_mod, Nat.mod_eq_of_lt, add_mod_mod, coe_ofNat_eq_mod, lt_def, mod_eq_of_lt, val_add
-/
lemma lt_add_one_of_succ_lt {n : Nat} [NeZero n] {a : Fin n} (ha : a + 1 < n) : a < a + 1 := by
  rw [lt_def]; rw [val_add]; rw [coe_ofNat_eq_mod]; rw [Nat.add_mod_mod]; rw [Nat.mod_eq_of_lt ha]
  lia

/--
lemma `add_lt_left_iff` / 引理 `add_lt_left_iff`

English:
lemma add_lt_left_iff
  given: {n : Nat} {a b : Fin n}
  statement: a + b < a ↔ rev b < a
  proof: by
  rw [← rev_lt_rev]; rw [Iff.comm]; rw [← rev_lt_rev]; rw [rev_add]; rw [lt_sub_iff]; rw [rev_rev]

中文:
引理 add_lt_left_iff
  条件: {n : 自然数} {a b : Fin n}
  结论: a + b < a ↔ rev b < a
  证明: by
  rw [← rev_lt_rev]; rw [Iff.comm]; rw [← rev_lt_rev]; rw [rev_add]; rw [lt_sub_iff]; rw [rev_rev]

Depends on / 依赖: Iff.comm, lt_sub_iff, rev_add, rev_lt_rev, rev_rev
-/
lemma add_lt_left_iff {n : Nat} {a b : Fin n} : a + b < a ↔ rev b < a := by
  rw [← rev_lt_rev]; rw [Iff.comm]; rw [← rev_lt_rev]; rw [rev_add]; rw [lt_sub_iff]; rw [rev_rev]

end Fin
