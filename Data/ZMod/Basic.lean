/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Fintype
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases

/-!
# Integers mod `n`

Definition of the integers mod n, and the field structure on the integers mod p.


## Definitions

* `ZMod n`, which is for integers modulo a nat `n : ℕ`

* `val a` is defined as a natural number:
  - for `a : ZMod 0` it is the absolute value of `a`
  - for `a : ZMod n` with `0 < n` it is the least natural number in the equivalence class

* A coercion `cast` is defined from `ZMod n` into any ring.
  This is a ring hom if the ring has characteristic dividing `n`

-/

@[expose] public section

assert_not_exists Field Submodule TwoSidedIdeal

open Function ZMod

namespace ZMod

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsDomain (ZMod 0)
  body: inferInstanceAs (IsDomain Int)

中文:
实例 :
  签名: IsDomain (ZMod 0)
  定义体: inferInstanceAs (IsDomain Int)

Depends on / 依赖: IsDomain
-/
instance : IsDomain (ZMod 0) := inferInstanceAs (IsDomain Int)

/--
Definition of `finEquiv` / `finEquiv` 的定义

English:
definition finEquiv
  signature: : forall (n : Nat) [NeZero n], Fin n ≃+* ZMod n

中文:
定义 finEquiv
  签名: : 对任意 (n : 自然数) [NeZero n], Fin n ≃+* ZMod n
-/
def finEquiv : forall (n : Nat) [NeZero n], Fin n ≃+* ZMod n
  | 0, h => (h.ne _ rfl).elim
  | _ + 1, _ => .refl _

/--
Instance `charZero` / 实例 `charZero`

English:
instance charZero
  signature: : CharZero (ZMod 0)
  body: inferInstanceAs (CharZero Int)

中文:
实例 charZero
  签名: : CharZero (ZMod 0)
  定义体: inferInstanceAs (CharZero Int)

Depends on / 依赖: CharZero
-/
instance charZero : CharZero (ZMod 0) := inferInstanceAs (CharZero Int)

/--
Definition of `val` / `val` 的定义

English:
definition val
  signature: : forall {n : Nat}, ZMod n -> Nat

中文:
定义 val
  签名: : 对任意 {n : 自然数}, ZMod n -> 自然数
-/
def val : forall {n : Nat}, ZMod n -> Nat
  | 0 => Int.natAbs
  | n + 1 => ((↑) : Fin (n + 1) -> Nat)

/--
theorem `val_lt` / 定理 `val_lt`

English:
theorem val_lt
  given: {n : Nat} [NeZero n] (a : ZMod n)
  statement: a.val < n
  proof: by
  cases n
  · cases NeZero.ne 0 rfl
  exact Fin.is_lt a

grind_pattern val_lt => a.val

中文:
定理 val_lt
  条件: {n : 自然数} [NeZero n] (a : ZMod n)
  结论: a.val < n
  证明: by
  cases n
  · cases NeZero.ne 0 rfl
  exact Fin.is_lt a

grind_pattern val_lt => a.val

Depends on / 依赖: Fin.is_lt, NeZero, NeZero.ne, is_lt
-/
theorem val_lt {n : Nat} [NeZero n] (a : ZMod n) : a.val < n := by
  cases n
  · cases NeZero.ne 0 rfl
  exact Fin.is_lt a

grind_pattern val_lt => a.val

/--
theorem `val_le` / 定理 `val_le`

English:
theorem val_le
  given: {n : Nat} [NeZero n] (a : ZMod n)
  statement: a.val <= n
  proof: a.val_lt.le

@[simp]

中文:
定理 val_le
  条件: {n : 自然数} [NeZero n] (a : ZMod n)
  结论: a.val <= n
  证明: a.val_lt.le

@[simp]

Depends on / 依赖: a.val_lt.le, val_lt
-/
theorem val_le {n : Nat} [NeZero n] (a : ZMod n) : a.val <= n :=
  a.val_lt.le

@[simp]
/--
theorem `val_zero` / 定理 `val_zero`

English:
theorem val_zero
  statement: forall {n}, (0 : ZMod n).val = 0

中文:
定理 val_zero
  结论: 对任意 {n}, (0 : ZMod n).val = 0
-/
theorem val_zero : forall {n}, (0 : ZMod n).val = 0
  | 0 => rfl
  | _ + 1 => rfl

@[simp]
/--
theorem `val_one'` / 定理 `val_one'`

English:
theorem val_one'
  statement: (1 : ZMod 0).val = 1
  proof: rfl

@[simp]

中文:
定理 val_one'
  结论: (1 : ZMod 0).val = 1
  证明: rfl

@[simp]
-/
theorem val_one' : (1 : ZMod 0).val = 1 :=
  rfl

@[simp]
/--
theorem `val_neg'` / 定理 `val_neg'`

English:
theorem val_neg'
  given: {n : ZMod 0}
  statement: (-n).val = n.val
  proof: Int.natAbs_neg n

@[simp]

中文:
定理 val_neg'
  条件: {n : ZMod 0}
  结论: (-n).val = n.val
  证明: Int.natAbs_neg n

@[simp]

Depends on / 依赖: Int.natAbs_neg, natAbs_neg
-/
theorem val_neg' {n : ZMod 0} : (-n).val = n.val :=
  Int.natAbs_neg n

@[simp]
/--
theorem `val_mul'` / 定理 `val_mul'`

English:
theorem val_mul'
  given: {m n : ZMod 0}
  statement: (m * n).val = m.val * n.val
  proof: Int.natAbs_mul m n

@[simp]

中文:
定理 val_mul'
  条件: {m n : ZMod 0}
  结论: (m * n).val = m.val * n.val
  证明: Int.natAbs_mul m n

@[simp]

Depends on / 依赖: Int.natAbs_mul, natAbs_mul
-/
theorem val_mul' {m n : ZMod 0} : (m * n).val = m.val * n.val :=
  Int.natAbs_mul m n

@[simp]
/--
theorem `val_natCast` / 定理 `val_natCast`

English:
theorem val_natCast
  given: (n a : Nat)
  statement: (a : ZMod n).val = a % n
  proof: by
  cases n
  · rw [Nat.mod_zero]
    exact Int.natAbs_natCast a
  · apply Fin.val_natCast

中文:
定理 val_natCast
  条件: (n a : 自然数)
  结论: (a : ZMod n).val = a % n
  证明: by
  cases n
  · rw [Nat.mod_zero]
    exact Int.natAbs_natCast a
  · apply Fin.val_natCast

Depends on / 依赖: Fin.val_natCast, Int.natAbs_natCast, Nat.mod_zero, mod_zero, natAbs_natCast, val_natCast
-/
theorem val_natCast (n a : Nat) : (a : ZMod n).val = a % n := by
  cases n
  · rw [Nat.mod_zero]
    exact Int.natAbs_natCast a
  · apply Fin.val_natCast

/--
lemma `val_natCast_of_lt` / 引理 `val_natCast_of_lt`

English:
lemma val_natCast_of_lt
  given: {n a : Nat} (h : a < n)
  statement: (a : ZMod n).val = a
  proof: by
  rwa [val_natCast, Nat.mod_eq_of_lt]

中文:
引理 val_natCast_of_lt
  条件: {n a : 自然数} (h : a < n)
  结论: (a : ZMod n).val = a
  证明: by
  rwa [val_natCast, Nat.mod_eq_of_lt]

Depends on / 依赖: Nat.mod_eq_of_lt, mod_eq_of_lt, val_natCast
-/
lemma val_natCast_of_lt {n a : Nat} (h : a < n) : (a : ZMod n).val = a := by
  rwa [val_natCast, Nat.mod_eq_of_lt]

/--
lemma `val_ofNat` / 引理 `val_ofNat`

English:
lemma val_ofNat
  given: (n a : Nat) [a.AtLeastTwo]
  statement: (ofNat(a) : ZMod n).val = ofNat(a) % n
  proof: val_natCast ..

中文:
引理 val_ofNat
  条件: (n a : 自然数) [a.AtLeastTwo]
  结论: (of自然数(a) : ZMod n).val = of自然数(a) % n
  证明: val_natCast ..

Depends on / 依赖: val_natCast
-/
lemma val_ofNat (n a : Nat) [a.AtLeastTwo] : (ofNat(a) : ZMod n).val = ofNat(a) % n := val_natCast ..

/--
lemma `val_ofNat_of_lt` / 引理 `val_ofNat_of_lt`

English:
lemma val_ofNat_of_lt
  given: {n a : Nat} [a.AtLeastTwo] (han : a < n)
  statement: (ofNat(a) : ZMod n).val = ofNat(a)
  proof: val_natCast_of_lt han

中文:
引理 val_ofNat_of_lt
  条件: {n a : 自然数} [a.AtLeastTwo] (han : a < n)
  结论: (of自然数(a) : ZMod n).val = of自然数(a)
  证明: val_natCast_of_lt han

Depends on / 依赖: val_natCast_of_lt
-/
lemma val_ofNat_of_lt {n a : Nat} [a.AtLeastTwo] (han : a < n) : (ofNat(a) : ZMod n).val = ofNat(a) :=
  val_natCast_of_lt han

set_option backward.isDefEq.respectTransparency false in
/--
theorem `val_unit'` / 定理 `val_unit'`

English:
theorem val_unit'
  given: {n : ZMod 0}
  statement: IsUnit n ↔ n.val = 1
  proof: by
  simp only [val]
  rw [Int.isUnit_iff]; rw [Int.natAbs_eq_iff]; rw [Nat.cast_one]

中文:
定理 val_unit'
  条件: {n : ZMod 0}
  结论: IsUnit n ↔ n.val = 1
  证明: by
  simp only [val]
  rw [Int.isUnit_iff]; rw [Int.natAbs_eq_iff]; rw [Nat.cast_one]

Depends on / 依赖: Int.isUnit_iff, Int.natAbs_eq_iff, Nat.cast_one, cast_one, isUnit_iff, natAbs_eq_iff
-/
theorem val_unit' {n : ZMod 0} : IsUnit n ↔ n.val = 1 := by
  simp only [val]
  rw [Int.isUnit_iff]; rw [Int.natAbs_eq_iff]; rw [Nat.cast_one]

/--
lemma `eq_one_of_isUnit_natCast` / 引理 `eq_one_of_isUnit_natCast`

English:
lemma eq_one_of_isUnit_natCast
  given: {n : Nat} (h : IsUnit (n : ZMod 0))
  statement: n = 1
  proof: by
  rw [← Nat.mod_zero n]; rw [← val_natCast]; rw [val_unit'.mp h]

中文:
引理 eq_one_of_isUnit_natCast
  条件: {n : 自然数} (h : IsUnit (n : ZMod 0))
  结论: n = 1
  证明: by
  rw [← Nat.mod_zero n]; rw [← val_natCast]; rw [val_unit'.mp h]

Depends on / 依赖: Nat.mod_zero, mod_zero, val_natCast, val_unit
-/
lemma eq_one_of_isUnit_natCast {n : Nat} (h : IsUnit (n : ZMod 0)) : n = 1 := by
  rw [← Nat.mod_zero n]; rw [← val_natCast]; rw [val_unit'.mp h]

/--
Instance `charP` / 实例 `charP`

English:
instance charP
  signature: (n : Nat)
  body: by
    intro k
    rcases n with - | n
    · simp
    · exact Fin.natCast_eq_zero

中文:
实例 charP
  签名: (n : 自然数)
  定义体: by
    intro k
    rcases n with - | n
    · simp
    · exact Fin.natCast_eq_zero

Depends on / 依赖: Fin.natCast_eq_zero, natCast_eq_zero
-/
instance charP (n : Nat) : CharP (ZMod n) n where
  cast_eq_zero_iff := by
    intro k
    rcases n with - | n
    · simp
    · exact Fin.natCast_eq_zero

-- Verify that `grind` can see that `ZMod n` has characteristic `n`.
example (n : Nat) : Lean.Grind.IsCharP (ZMod n) n := inferInstance

@[simp]
/--
theorem `addOrderOf_one` / 定理 `addOrderOf_one`

English:
theorem addOrderOf_one
  given: (n : Nat)
  statement: addOrderOf (1 : ZMod n) = n
  proof: CharP.eq _ (CharP.addOrderOf_one _) (ZMod.charP n)

中文:
定理 addOrderOf_one
  条件: (n : 自然数)
  结论: addOrderOf (1 : ZMod n) = n
  证明: CharP.eq _ (CharP.addOrderOf_one _) (ZMod.charP n)

Depends on / 依赖: CharP.addOrderOf_one, CharP.eq, ZMod.charP, addOrderOf_one
-/
theorem addOrderOf_one (n : Nat) : addOrderOf (1 : ZMod n) = n :=
  CharP.eq _ (CharP.addOrderOf_one _) (ZMod.charP n)

/-- This lemma works in the case in which `ZMod n` is not infinite, i.e. `n ≠ 0`. The version
where `a ≠ 0` is `addOrderOf_coe'`. -/
@[simp]
/--
theorem `addOrderOf_coe` / 定理 `addOrderOf_coe`

English:
theorem addOrderOf_coe
  given: (a : Nat) {n : Nat} (n0 : n != 0)
  statement: addOrderOf (a : ZMod n) = n / n.gcd a
  proof: by
  rcases a with - | a
  · simp only [Nat.cast_zero, addOrderOf_zero, Nat.gcd_zero_right,
      Nat.pos_of_ne_zero n0, Nat.div_self]
  rw [← Nat.smul_one_eq_cast]; rw [addOrderOf_nsmul' _ a.succ_ne_zero]; rw [ZMod.addOrderOf_one]

中文:
定理 addOrderOf_coe
  条件: (a : 自然数) {n : 自然数} (n0 : n != 0)
  结论: addOrderOf (a : ZMod n) = n / n.gcd a
  证明: by
  rcases a with - | a
  · simp only [Nat.cast_zero, addOrderOf_zero, Nat.gcd_zero_right,
      Nat.pos_of_ne_zero n0, Nat.div_self]
  rw [← Nat.smul_one_eq_cast]; rw [addOrderOf_nsmul' _ a.succ_ne_zero]; rw [ZMod.addOrderOf_one]

Depends on / 依赖: Nat.cast_zero, Nat.div_self, Nat.gcd_zero_right, Nat.pos_of_ne_zero, Nat.smul_one_eq_cast, ZMod.addOrderOf_one, a.succ_ne_zero, addOrderOf_nsmul, addOrderOf_one, addOrderOf_zero, cast_zero, div_self, gcd_zero_right, pos_of_ne_zero, smul_one_eq_cast, succ_ne_zero
-/
theorem addOrderOf_coe (a : Nat) {n : Nat} (n0 : n != 0) : addOrderOf (a : ZMod n) = n / n.gcd a := by
  rcases a with - | a
  · simp only [Nat.cast_zero, addOrderOf_zero, Nat.gcd_zero_right,
      Nat.pos_of_ne_zero n0, Nat.div_self]
  rw [← Nat.smul_one_eq_cast]; rw [addOrderOf_nsmul' _ a.succ_ne_zero]; rw [ZMod.addOrderOf_one]

/-- This lemma works in the case in which `a ≠ 0`. The version where
`ZMod n` is not infinite, i.e. `n ≠ 0`, is `addOrderOf_coe`. -/
@[simp]
/--
theorem `addOrderOf_coe'` / 定理 `addOrderOf_coe'`

English:
theorem addOrderOf_coe'
  given: {a : Nat} (n : Nat) (a0 : a != 0)
  statement: addOrderOf (a : ZMod n) = n / n.gcd a
  proof: by
  rw [← Nat.smul_one_eq_cast]; rw [addOrderOf_nsmul' _ a0]; rw [ZMod.addOrderOf_one]

中文:
定理 addOrderOf_coe'
  条件: {a : 自然数} (n : 自然数) (a0 : a != 0)
  结论: addOrderOf (a : ZMod n) = n / n.gcd a
  证明: by
  rw [← Nat.smul_one_eq_cast]; rw [addOrderOf_nsmul' _ a0]; rw [ZMod.addOrderOf_one]

Depends on / 依赖: Nat.smul_one_eq_cast, ZMod.addOrderOf_one, addOrderOf_nsmul, addOrderOf_one, smul_one_eq_cast
-/
theorem addOrderOf_coe' {a : Nat} (n : Nat) (a0 : a != 0) : addOrderOf (a : ZMod n) = n / n.gcd a := by
  rw [← Nat.smul_one_eq_cast]; rw [addOrderOf_nsmul' _ a0]; rw [ZMod.addOrderOf_one]

/--
theorem `ringChar_zmod_n` / 定理 `ringChar_zmod_n`

English:
theorem ringChar_zmod_n
  given: (n : Nat)
  statement: ringChar (ZMod n) = n
  proof: by
  rw [ringChar.eq_iff]
  exact ZMod.charP n

中文:
定理 ringChar_zmod_n
  条件: (n : 自然数)
  结论: ringChar (ZMod n) = n
  证明: by
  rw [ringChar.eq_iff]
  exact ZMod.charP n

Depends on / 依赖: ZMod.charP, eq_iff, ringChar, ringChar.eq_iff
-/
theorem ringChar_zmod_n (n : Nat) : ringChar (ZMod n) = n := by
  rw [ringChar.eq_iff]
  exact ZMod.charP n

/--
theorem `natCast_self` / 定理 `natCast_self`

English:
theorem natCast_self
  given: (n : Nat)
  statement: (n : ZMod n) = 0
  proof: CharP.cast_eq_zero (ZMod n) n

@[simp]

中文:
定理 natCast_self
  条件: (n : 自然数)
  结论: (n : ZMod n) = 0
  证明: CharP.cast_eq_zero (ZMod n) n

@[simp]

Depends on / 依赖: CharP.cast_eq_zero, cast_eq_zero
-/
theorem natCast_self (n : Nat) : (n : ZMod n) = 0 :=
  CharP.cast_eq_zero (ZMod n) n

@[simp]
/--
theorem `natCast_self'` / 定理 `natCast_self'`

English:
theorem natCast_self'
  given: (n : Nat)
  statement: (n + 1 : ZMod (n + 1)) = 0
  proof: by
  rw [← Nat.cast_add_one]; rw [natCast_self (n + 1)]

@[aesop unsafe 75%]

中文:
定理 natCast_self'
  条件: (n : 自然数)
  结论: (n + 1 : ZMod (n + 1)) = 0
  证明: by
  rw [← Nat.cast_add_one]; rw [natCast_self (n + 1)]

@[aesop unsafe 75%]

Depends on / 依赖: Nat.cast_add_one, cast_add_one, natCast_self
-/
theorem natCast_self' (n : Nat) : (n + 1 : ZMod (n + 1)) = 0 := by
  rw [← Nat.cast_add_one]; rw [natCast_self (n + 1)]

@[aesop unsafe 75%]
/--
lemma `natCast_pow_eq_zero_of_le` / 引理 `natCast_pow_eq_zero_of_le`

English:
lemma natCast_pow_eq_zero_of_le
  given: (p : Nat) {m n : Nat} (h : n <= m)
  proof: by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add]; rw [← Nat.cast_pow]
  simp

中文:
引理 natCast_pow_eq_zero_of_le
  条件: (p : 自然数) {m n : 自然数} (h : n <= m)
  证明: by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add]; rw [← Nat.cast_pow]
  simp

Depends on / 依赖: Nat.cast_pow, Nat.exists_eq_add_of_le, cast_pow, exists_eq_add_of_le, pow_add
-/
lemma natCast_pow_eq_zero_of_le (p : Nat) {m n : Nat} (h : n <= m) :
    (p ^ m : ZMod (p ^ n)) = 0 := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add]; rw [← Nat.cast_pow]
  simp

section UniversalProperty

variable {n : Nat} {R : Type*}

section

variable [AddGroupWithOne R]

/--
Definition of `cast` / `cast` 的定义

English:
definition cast
  signature: : forall {n : Nat}, ZMod n -> R

中文:
定义 cast
  签名: : 对任意 {n : 自然数}, ZMod n -> R
-/
def cast : forall {n : Nat}, ZMod n -> R
  | 0 => Int.cast
  | _ + 1 => fun i => i.val


@[simp]
/--
theorem `cast_zero` / 定理 `cast_zero`

English:
theorem cast_zero
  statement: (cast (0 : ZMod n) : R) = 0
  proof: by
  delta ZMod.cast
  cases n
  · exact Int.cast_zero
  · simp

中文:
定理 cast_zero
  结论: (cast (0 : ZMod n) : R) = 0
  证明: by
  delta ZMod.cast
  cases n
  · exact Int.cast_zero
  · simp

Depends on / 依赖: Int.cast_zero, ZMod.cast, cast_zero
-/
theorem cast_zero : (cast (0 : ZMod n) : R) = 0 := by
  delta ZMod.cast
  cases n
  · exact Int.cast_zero
  · simp

/--
theorem `cast_eq_val` / 定理 `cast_eq_val`

English:
theorem cast_eq_val
  given: [NeZero n] (a : ZMod n)
  statement: (cast a : R) = a.val
  proof: by
  cases n
  · cases NeZero.ne 0 rfl
  rfl

中文:
定理 cast_eq_val
  条件: [NeZero n] (a : ZMod n)
  结论: (cast a : R) = a.val
  证明: by
  cases n
  · cases NeZero.ne 0 rfl
  rfl

Depends on / 依赖: NeZero, NeZero.ne
-/
theorem cast_eq_val [NeZero n] (a : ZMod n) : (cast a : R) = a.val := by
  cases n
  · cases NeZero.ne 0 rfl
  rfl

variable {S : Type*} [AddGroupWithOne S]

@[simp]
/--
theorem `_root_.Prod.fst_zmod_cast` / 定理 `_root_.Prod.fst_zmod_cast`

English:
theorem _root_.Prod.fst_zmod_cast
  given: (a : ZMod n)
  statement: (cast a : R × S).fst = cast a
  proof: by
  cases n
  · rfl
  · simp [ZMod.cast]

@[simp]

中文:
定理 _root_.Prod.fst_zmod_cast
  条件: (a : ZMod n)
  结论: (cast a : R × S).fst = cast a
  证明: by
  cases n
  · rfl
  · simp [ZMod.cast]

@[simp]

Depends on / 依赖: Fintype, Fintype.subtype, List.mem_toFinset, List.toFinset, Red.enum, Red.enum.complete, Red.enum.sound, ZMod.cast, complete, mem_toFinset, subtype, toFinset
-/
theorem _root_.Prod.fst_zmod_cast (a : ZMod n) : (cast a : R × S).fst = cast a := by
  cases n
  · rfl
  · simp [ZMod.cast]

@[simp]
/--
theorem `_root_.Prod.snd_zmod_cast` / 定理 `_root_.Prod.snd_zmod_cast`

English:
theorem _root_.Prod.snd_zmod_cast
  given: (a : ZMod n)
  statement: (cast a : R × S).snd = cast a
  proof: by
  cases n
  · rfl
  · simp [ZMod.cast]

中文:
定理 _root_.Prod.snd_zmod_cast
  条件: (a : ZMod n)
  结论: (cast a : R × S).snd = cast a
  证明: by
  cases n
  · rfl
  · simp [ZMod.cast]

Depends on / 依赖: ZMod.cast
-/
theorem _root_.Prod.snd_zmod_cast (a : ZMod n) : (cast a : R × S).snd = cast a := by
  cases n
  · rfl
  · simp [ZMod.cast]

end

/--
theorem `natCast_zmod_val` / 定理 `natCast_zmod_val`

English:
theorem natCast_zmod_val
  given: {n : Nat} [NeZero n] (a : ZMod n)
  statement: (a.val : ZMod n) = a
  proof: by
  cases n
  · cases NeZero.ne 0 rfl
  · apply Fin.cast_val_eq_self

中文:
定理 natCast_zmod_val
  条件: {n : 自然数} [NeZero n] (a : ZMod n)
  结论: (a.val : ZMod n) = a
  证明: by
  cases n
  · cases NeZero.ne 0 rfl
  · apply Fin.cast_val_eq_self

Depends on / 依赖: Fin.cast_val_eq_self, NeZero, NeZero.ne, cast_val_eq_self
-/
theorem natCast_zmod_val {n : Nat} [NeZero n] (a : ZMod n) : (a.val : ZMod n) = a := by
  cases n
  · cases NeZero.ne 0 rfl
  · apply Fin.cast_val_eq_self

/--
theorem `natCast_rightInverse` / 定理 `natCast_rightInverse`

English:
theorem natCast_rightInverse
  given: [NeZero n]
  statement: Function.RightInverse val ((↑) : Nat -> ZMod n)
  proof: natCast_zmod_val

中文:
定理 natCast_rightInverse
  条件: [NeZero n]
  结论: Function.RightInverse val ((↑) : 自然数 -> ZMod n)
  证明: natCast_zmod_val

Depends on / 依赖: natCast_zmod_val
-/
theorem natCast_rightInverse [NeZero n] : Function.RightInverse val ((↑) : Nat -> ZMod n) :=
  natCast_zmod_val

/--
theorem `natCast_zmod_surjective` / 定理 `natCast_zmod_surjective`

English:
theorem natCast_zmod_surjective
  given: [NeZero n]
  statement: Function.Surjective ((↑) : Nat -> ZMod n)
  proof: natCast_rightInverse.surjective

中文:
定理 natCast_zmod_surjective
  条件: [NeZero n]
  结论: Function.Surjective ((↑) : 自然数 -> ZMod n)
  证明: natCast_rightInverse.surjective

Depends on / 依赖: natCast_rightInverse, natCast_rightInverse.surjective, surjective
-/
theorem natCast_zmod_surjective [NeZero n] : Function.Surjective ((↑) : Nat -> ZMod n) :=
  natCast_rightInverse.surjective

set_option backward.isDefEq.respectTransparency false in
/-- So-named because the outer coercion is `Int.cast` into `ZMod`. For `Int.cast` into an arbitrary
ring, see `ZMod.intCast_cast`. -/
@[norm_cast]
/--
theorem `intCast_zmod_cast` / 定理 `intCast_zmod_cast`

English:
theorem intCast_zmod_cast
  given: (a : ZMod n)
  statement: ((cast a : Int) : ZMod n) = a
  proof: by
  cases n
  · simp [ZMod.cast, ZMod]
  · dsimp [ZMod.cast]
    rw [Int.cast_natCast]; rw [natCast_zmod_val]

中文:
定理 intCast_zmod_cast
  条件: (a : ZMod n)
  结论: ((cast a : 整数) : ZMod n) = a
  证明: by
  cases n
  · simp [ZMod.cast, ZMod]
  · dsimp [ZMod.cast]
    rw [Int.cast_natCast]; rw [natCast_zmod_val]

Depends on / 依赖: Int.cast_natCast, ZMod.cast, cast_natCast, natCast_zmod_val
-/
theorem intCast_zmod_cast (a : ZMod n) : ((cast a : Int) : ZMod n) = a := by
  cases n
  · simp [ZMod.cast, ZMod]
  · dsimp [ZMod.cast]
    rw [Int.cast_natCast]; rw [natCast_zmod_val]

/--
theorem `intCast_rightInverse` / 定理 `intCast_rightInverse`

English:
theorem intCast_rightInverse
  statement: Function.RightInverse (cast : ZMod n -> Int) ((↑) : Int -> ZMod n)
  proof: intCast_zmod_cast

中文:
定理 intCast_rightInverse
  结论: Function.RightInverse (cast : ZMod n -> 整数) ((↑) : 整数 -> ZMod n)
  证明: intCast_zmod_cast

Depends on / 依赖: intCast_zmod_cast
-/
theorem intCast_rightInverse : Function.RightInverse (cast : ZMod n -> Int) ((↑) : Int -> ZMod n) :=
  intCast_zmod_cast

/--
theorem `intCast_surjective` / 定理 `intCast_surjective`

English:
theorem intCast_surjective
  statement: Function.Surjective ((↑) : Int -> ZMod n)
  proof: intCast_rightInverse.surjective

中文:
定理 intCast_surjective
  结论: Function.Surjective ((↑) : 整数 -> ZMod n)
  证明: intCast_rightInverse.surjective

Depends on / 依赖: intCast_rightInverse, intCast_rightInverse.surjective, surjective
-/
theorem intCast_surjective : Function.Surjective ((↑) : Int -> ZMod n) :=
  intCast_rightInverse.surjective

/--
lemma `«forall»` / 引理 `«forall»`

English:
lemma «forall»
  given: {P : ZMod n -> Prop}
  statement: (forall x, P x) ↔ forall x : Int, P x
  proof: intCast_surjective.forall

中文:
引理 «forall»
  条件: {P : ZMod n -> 命题}
  结论: (对任意 x, P x) ↔ 对任意 x : 整数, P x
  证明: intCast_surjective.forall
-/
lemma «forall» {P : ZMod n -> Prop} : (forall x, P x) ↔ forall x : Int, P x := intCast_surjective.forall
/--
lemma `«exists»` / 引理 `«exists»`

English:
lemma «exists»
  given: {P : ZMod n -> Prop}
  statement: (exists x, P x) ↔ exists x : Int, P x
  proof: intCast_surjective.exists

中文:
引理 «exists»
  条件: {P : ZMod n -> 命题}
  结论: (存在 x, P x) ↔ 存在 x : 整数, P x
  证明: intCast_surjective.exists
-/
lemma «exists» {P : ZMod n -> Prop} : (exists x, P x) ↔ exists x : Int, P x := intCast_surjective.exists

/--
theorem `cast_id` / 定理 `cast_id`

English:
theorem cast_id
  statement: forall (n) (i : ZMod n), (ZMod.cast i : ZMod n) = i

中文:
定理 cast_id
  结论: 对任意 (n) (i : ZMod n), (ZMod.cast i : ZMod n) = i
-/
theorem cast_id : forall (n) (i : ZMod n), (ZMod.cast i : ZMod n) = i
  | 0, _ => Int.cast_id
  | _ + 1, i => natCast_zmod_val i

@[simp]
/--
theorem `cast_id'` / 定理 `cast_id'`

English:
theorem cast_id'
  statement: (ZMod.cast : ZMod n -> ZMod n) = id
  proof: funext (cast_id n)

中文:
定理 cast_id'
  结论: (ZMod.cast : ZMod n -> ZMod n) = id
  证明: funext (cast_id n)

Depends on / 依赖: cast_id
-/
theorem cast_id' : (ZMod.cast : ZMod n -> ZMod n) = id :=
  funext (cast_id n)

variable (R) [Ring R]

/-- The coercions are respectively `Nat.cast` and `ZMod.cast`. -/
@[simp]
/--
theorem `natCast_comp_val` / 定理 `natCast_comp_val`

English:
theorem natCast_comp_val
  given: [NeZero n]
  statement: ((↑) : Nat -> R) ∘ (val : ZMod n -> Nat) = cast
  proof: by
  cases n
  · cases NeZero.ne 0 rfl
  rfl

中文:
定理 natCast_comp_val
  条件: [NeZero n]
  结论: ((↑) : 自然数 -> R) ∘ (val : ZMod n -> 自然数) = cast
  证明: by
  cases n
  · cases NeZero.ne 0 rfl
  rfl

Depends on / 依赖: NeZero, NeZero.ne
-/
theorem natCast_comp_val [NeZero n] : ((↑) : Nat -> R) ∘ (val : ZMod n -> Nat) = cast := by
  cases n
  · cases NeZero.ne 0 rfl
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The coercions are respectively `Int.cast`, `ZMod.cast`, and `ZMod.cast`. -/
@[simp]
/--
theorem `intCast_comp_cast` / 定理 `intCast_comp_cast`

English:
theorem intCast_comp_cast
  statement: ((↑) : Int -> R) ∘ (cast : ZMod n -> Int) = cast
  proof: by
  cases n
  · exact congr_arg (Int.cast ∘ ·) ZMod.cast_id'
  · ext
    simp [ZMod, ZMod.cast]

中文:
定理 intCast_comp_cast
  结论: ((↑) : 整数 -> R) ∘ (cast : ZMod n -> 整数) = cast
  证明: by
  cases n
  · exact congr_arg (Int.cast ∘ ·) ZMod.cast_id'
  · ext
    simp [ZMod, ZMod.cast]

Depends on / 依赖: Int.cast, ZMod.cast, ZMod.cast_id, cast_id, congr_arg
-/
theorem intCast_comp_cast : ((↑) : Int -> R) ∘ (cast : ZMod n -> Int) = cast := by
  cases n
  · exact congr_arg (Int.cast ∘ ·) ZMod.cast_id'
  · ext
    simp [ZMod, ZMod.cast]

variable {R}

@[simp]
/--
theorem `natCast_val` / 定理 `natCast_val`

English:
theorem natCast_val
  given: [NeZero n] (i : ZMod n)
  statement: (i.val : R) = cast i
  proof: congr_fun (natCast_comp_val R) i

@[simp]

中文:
定理 natCast_val
  条件: [NeZero n] (i : ZMod n)
  结论: (i.val : R) = cast i
  证明: congr_fun (natCast_comp_val R) i

@[simp]

Depends on / 依赖: congr_fun, natCast_comp_val
-/
theorem natCast_val [NeZero n] (i : ZMod n) : (i.val : R) = cast i :=
  congr_fun (natCast_comp_val R) i

@[simp]
/--
theorem `intCast_cast` / 定理 `intCast_cast`

English:
theorem intCast_cast
  given: (i : ZMod n)
  statement: ((cast i : Int) : R) = cast i
  proof: congr_fun (intCast_comp_cast R) i

中文:
定理 intCast_cast
  条件: (i : ZMod n)
  结论: ((cast i : 整数) : R) = cast i
  证明: congr_fun (intCast_comp_cast R) i

Depends on / 依赖: congr_fun, intCast_comp_cast
-/
theorem intCast_cast (i : ZMod n) : ((cast i : Int) : R) = cast i :=
  congr_fun (intCast_comp_cast R) i

/--
theorem `cast_add_eq_ite` / 定理 `cast_add_eq_ite`

English:
theorem cast_add_eq_ite
  given: {n : Nat} (a b : ZMod n)
  proof: by
  rcases n with - | n
  · simp; rfl
  change Fin (n + 1) at a b
  change ((((a + b) : Fin (n + 1)) : Nat) : Int) = if ((n + 1 : Nat) : Int) <= (a : Nat) + b then _ else _
  simp only [Fin.val_add_eq_ite, Int.natCast_succ]
  norm_cast
  split_ifs with h
  · rw [Nat.cast_sub h]
    congr
  · rfl

中文:
定理 cast_add_eq_ite
  条件: {n : 自然数} (a b : ZMod n)
  证明: by
  rcases n with - | n
  · simp; rfl
  change Fin (n + 1) at a b
  change ((((a + b) : Fin (n + 1)) : Nat) : Int) = if ((n + 1 : Nat) : Int) <= (a : Nat) + b then _ else _
  simp only [Fin.val_add_eq_ite, Int.natCast_succ]
  norm_cast
  split_ifs with h
  · rw [Nat.cast_sub h]
    congr
  · rfl

Depends on / 依赖: Fin.val_add_eq_ite, Int.natCast_succ, Nat.cast_sub, cast_sub, natCast_succ, split_ifs, val_add_eq_ite
-/
theorem cast_add_eq_ite {n : Nat} (a b : ZMod n) :
    (cast (a + b) : Int) =
      if (n : Int) <= cast a + cast b then (cast a + cast b - n : Int) else cast a + cast b := by
  rcases n with - | n
  · simp; rfl
  change Fin (n + 1) at a b
  change ((((a + b) : Fin (n + 1)) : Nat) : Int) = if ((n + 1 : Nat) : Int) <= (a : Nat) + b then _ else _
  simp only [Fin.val_add_eq_ite, Int.natCast_succ]
  norm_cast
  split_ifs with h
  · rw [Nat.cast_sub h]
    congr
  · rfl

section CharDvd

/-! If the characteristic of `R` divides `n`, then `cast` is a homomorphism. -/


variable {m : Nat} [CharP R m]

@[simp]
/--
theorem `cast_one` / 定理 `cast_one`

English:
theorem cast_one
  given: (h : m ∣ n)
  statement: (cast (1 : ZMod n) : R) = 1
  proof: by
  rcases n with - | n
  · exact Int.cast_one
  change ((1 % (n + 1) : Nat) : R) = 1
  cases n
  · rw [Nat.dvd_one] at h
    subst m
    subsingleton [CharP.CharOne.subsingleton]
  rw [Nat.mod_eq_of_lt]
  · exact Nat.cast_one
  exact Nat.lt_of_sub_eq_succ rfl

中文:
定理 cast_one
  条件: (h : m ∣ n)
  结论: (cast (1 : ZMod n) : R) = 1
  证明: by
  rcases n with - | n
  · exact Int.cast_one
  change ((1 % (n + 1) : Nat) : R) = 1
  cases n
  · rw [Nat.dvd_one] at h
    subst m
    subsingleton [CharP.CharOne.subsingleton]
  rw [Nat.mod_eq_of_lt]
  · exact Nat.cast_one
  exact Nat.lt_of_sub_eq_succ rfl

Depends on / 依赖: CharOne, CharP.CharOne.subsingleton, Int.cast_one, Nat.cast_one, Nat.dvd_one, Nat.lt_of_sub_eq_succ, Nat.mod_eq_of_lt, cast_one, dvd_one, lt_of_sub_eq_succ, mod_eq_of_lt, subsingleton
-/
theorem cast_one (h : m ∣ n) : (cast (1 : ZMod n) : R) = 1 := by
  rcases n with - | n
  · exact Int.cast_one
  change ((1 % (n + 1) : Nat) : R) = 1
  cases n
  · rw [Nat.dvd_one] at h
    subst m
    subsingleton [CharP.CharOne.subsingleton]
  rw [Nat.mod_eq_of_lt]
  · exact Nat.cast_one
  exact Nat.lt_of_sub_eq_succ rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `cast_add` / 定理 `cast_add`

English:
theorem cast_add
  given: (h : m ∣ n) (a b : ZMod n)
  statement: (cast (a + b : ZMod n) : R) = cast a + cast b
  proof: by
  cases n
  · apply Int.cast_add
  symm
  dsimp [ZMod, ZMod.cast, ZMod.val]
  rw [← Nat.cast_add]; rw [Fin.val_add]; rw [← sub_eq_zero]; rw [← Nat.cast_sub (Nat.mod_le _ _)]; rw [@CharP.cast_eq_zero_iff R _ m]
  exact h.trans (Nat.dvd_sub_mod _)

中文:
定理 cast_add
  条件: (h : m ∣ n) (a b : ZMod n)
  结论: (cast (a + b : ZMod n) : R) = cast a + cast b
  证明: by
  cases n
  · apply Int.cast_add
  symm
  dsimp [ZMod, ZMod.cast, ZMod.val]
  rw [← Nat.cast_add]; rw [Fin.val_add]; rw [← sub_eq_zero]; rw [← Nat.cast_sub (Nat.mod_le _ _)]; rw [@CharP.cast_eq_zero_iff R _ m]
  exact h.trans (Nat.dvd_sub_mod _)

Depends on / 依赖: CharP.cast_eq_zero_iff, Fin.val_add, Int.cast_add, Nat.cast_add, Nat.cast_sub, Nat.dvd_sub_mod, Nat.mod_le, ZMod.cast, ZMod.val, cast_add, cast_eq_zero_iff, cast_sub, dvd_sub_mod, h.trans, mod_le, sub_eq_zero, val_add
-/
theorem cast_add (h : m ∣ n) (a b : ZMod n) : (cast (a + b : ZMod n) : R) = cast a + cast b := by
  cases n
  · apply Int.cast_add
  symm
  dsimp [ZMod, ZMod.cast, ZMod.val]
  rw [← Nat.cast_add]; rw [Fin.val_add]; rw [← sub_eq_zero]; rw [← Nat.cast_sub (Nat.mod_le _ _)]; rw [@CharP.cast_eq_zero_iff R _ m]
  exact h.trans (Nat.dvd_sub_mod _)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `cast_mul` / 定理 `cast_mul`

English:
theorem cast_mul
  given: (h : m ∣ n) (a b : ZMod n)
  statement: (cast (a * b : ZMod n) : R) = cast a * cast b
  proof: by
  cases n
  · apply Int.cast_mul
  symm
  dsimp [ZMod, ZMod.cast, ZMod.val]
  rw [← Nat.cast_mul]; rw [Fin.val_mul]; rw [← sub_eq_zero]; rw [← Nat.cast_sub (Nat.mod_le _ _)]; rw [@CharP.cast_eq_zero_iff R _ m]
  exact h.trans (Nat.dvd_sub_mod _)

中文:
定理 cast_mul
  条件: (h : m ∣ n) (a b : ZMod n)
  结论: (cast (a * b : ZMod n) : R) = cast a * cast b
  证明: by
  cases n
  · apply Int.cast_mul
  symm
  dsimp [ZMod, ZMod.cast, ZMod.val]
  rw [← Nat.cast_mul]; rw [Fin.val_mul]; rw [← sub_eq_zero]; rw [← Nat.cast_sub (Nat.mod_le _ _)]; rw [@CharP.cast_eq_zero_iff R _ m]
  exact h.trans (Nat.dvd_sub_mod _)

Depends on / 依赖: CharP.cast_eq_zero_iff, Fin.val_mul, Int.cast_mul, Nat.cast_mul, Nat.cast_sub, Nat.dvd_sub_mod, Nat.mod_le, ZMod.cast, ZMod.val, cast_eq_zero_iff, cast_mul, cast_sub, dvd_sub_mod, h.trans, mod_le, sub_eq_zero, val_mul
-/
theorem cast_mul (h : m ∣ n) (a b : ZMod n) : (cast (a * b : ZMod n) : R) = cast a * cast b := by
  cases n
  · apply Int.cast_mul
  symm
  dsimp [ZMod, ZMod.cast, ZMod.val]
  rw [← Nat.cast_mul]; rw [Fin.val_mul]; rw [← sub_eq_zero]; rw [← Nat.cast_sub (Nat.mod_le _ _)]; rw [@CharP.cast_eq_zero_iff R _ m]
  exact h.trans (Nat.dvd_sub_mod _)

/--
Definition of `castHom` / `castHom` 的定义

English:
definition castHom
  signature: (h : m ∣ n) (R : Type*) [Ring R] [CharP R m]
  body: cast
  map_zero' := cast_zero
  map_one' := cast_one h
  map_add' := cast_add h
  map_mul' := cast_mul h

@[simp]

中文:
定义 castHom
  签名: (h : m ∣ n) (R : 类型) [Ring R] [CharP R m]
  定义体: cast
  map_zero' := cast_zero
  map_one' := cast_one h
  map_add' := cast_add h
  map_mul' := cast_mul h

@[simp]
-/
def castHom (h : m ∣ n) (R : Type*) [Ring R] [CharP R m] : ZMod n ->+* R where
  toFun := cast
  map_zero' := cast_zero
  map_one' := cast_one h
  map_add' := cast_add h
  map_mul' := cast_mul h

@[simp]
/--
theorem `castHom_apply` / 定理 `castHom_apply`

English:
theorem castHom_apply
  given: {h : m ∣ n} (i : ZMod n)
  statement: castHom h R i = cast i
  proof: rfl

@[simp]

中文:
定理 castHom_apply
  条件: {h : m ∣ n} (i : ZMod n)
  结论: castHom h R i = cast i
  证明: rfl

@[simp]
-/
theorem castHom_apply {h : m ∣ n} (i : ZMod n) : castHom h R i = cast i :=
  rfl

@[simp]
/--
theorem `cast_sub` / 定理 `cast_sub`

English:
theorem cast_sub
  given: (h : m ∣ n) (a b : ZMod n)
  statement: (cast (a - b : ZMod n) : R) = cast a - cast b
  proof: (castHom h R).map_sub a b

@[simp]

中文:
定理 cast_sub
  条件: (h : m ∣ n) (a b : ZMod n)
  结论: (cast (a - b : ZMod n) : R) = cast a - cast b
  证明: (castHom h R).map_sub a b

@[simp]

Depends on / 依赖: MulAction, MulAction.mem_fixedBy, castHom, infer_instance, map_sub, mem_fixedBy
-/
theorem cast_sub (h : m ∣ n) (a b : ZMod n) : (cast (a - b : ZMod n) : R) = cast a - cast b :=
  (castHom h R).map_sub a b

@[simp]
/--
theorem `cast_neg` / 定理 `cast_neg`

English:
theorem cast_neg
  given: (h : m ∣ n) (a : ZMod n)
  statement: (cast (-a : ZMod n) : R) = -(cast a)
  proof: (castHom h R).map_neg a

@[simp]

中文:
定理 cast_neg
  条件: (h : m ∣ n) (a : ZMod n)
  结论: (cast (-a : ZMod n) : R) = -(cast a)
  证明: (castHom h R).map_neg a

@[simp]

Depends on / 依赖: castHom, map_neg
-/
theorem cast_neg (h : m ∣ n) (a : ZMod n) : (cast (-a : ZMod n) : R) = -(cast a) :=
  (castHom h R).map_neg a

@[simp]
/--
theorem `cast_pow` / 定理 `cast_pow`

English:
theorem cast_pow
  given: (h : m ∣ n) (a : ZMod n) (k : Nat)
  statement: (cast (a ^ k : ZMod n) : R) = (cast a) ^ k
  proof: (castHom h R).map_pow a k

@[simp, norm_cast]

中文:
定理 cast_pow
  条件: (h : m ∣ n) (a : ZMod n) (k : 自然数)
  结论: (cast (a ^ k : ZMod n) : R) = (cast a) ^ k
  证明: (castHom h R).map_pow a k

@[simp, norm_cast]

Depends on / 依赖: castHom, map_pow
-/
theorem cast_pow (h : m ∣ n) (a : ZMod n) (k : Nat) : (cast (a ^ k : ZMod n) : R) = (cast a) ^ k :=
  (castHom h R).map_pow a k

@[simp, norm_cast]
/--
theorem `cast_natCast` / 定理 `cast_natCast`

English:
theorem cast_natCast
  given: (h : m ∣ n) (k : Nat)
  statement: (cast (k : ZMod n) : R) = k
  proof: map_natCast (castHom h R) k

@[simp, norm_cast]

中文:
定理 cast_natCast
  条件: (h : m ∣ n) (k : 自然数)
  结论: (cast (k : ZMod n) : R) = k
  证明: map_natCast (castHom h R) k

@[simp, norm_cast]

Depends on / 依赖: castHom, map_natCast
-/
theorem cast_natCast (h : m ∣ n) (k : Nat) : (cast (k : ZMod n) : R) = k :=
  map_natCast (castHom h R) k

@[simp, norm_cast]
/--
theorem `cast_intCast` / 定理 `cast_intCast`

English:
theorem cast_intCast
  given: (h : m ∣ n) (k : Int)
  statement: (cast (k : ZMod n) : R) = k
  proof: map_intCast (castHom h R) k

中文:
定理 cast_intCast
  条件: (h : m ∣ n) (k : 整数)
  结论: (cast (k : ZMod n) : R) = k
  证明: map_intCast (castHom h R) k

Depends on / 依赖: castHom, map_intCast, mul_smul
-/
theorem cast_intCast (h : m ∣ n) (k : Int) : (cast (k : ZMod n) : R) = k :=
  map_intCast (castHom h R) k

/--
theorem `castHom_surjective` / 定理 `castHom_surjective`

English:
theorem castHom_surjective
  given: (h : m ∣ n)
  statement: Function.Surjective (castHom h (ZMod m))
  proof: fun a => by obtain ⟨a, rfl⟩ := intCast_surjective a; exact ⟨a, map_intCast ..⟩

中文:
定理 castHom_surjective
  条件: (h : m ∣ n)
  结论: Function.Surjective (castHom h (ZMod m))
  证明: fun a => by obtain ⟨a, rfl⟩ := intCast_surjective a; exact ⟨a, map_intCast ..⟩

Depends on / 依赖: intCast_surjective, map_intCast
-/
theorem castHom_surjective (h : m ∣ n) : Function.Surjective (castHom h (ZMod m)) :=
  fun a => by obtain ⟨a, rfl⟩ := intCast_surjective a; exact ⟨a, map_intCast ..⟩

end CharDvd

section CharEq

/-! Some specialised simp lemmas which apply when `R` has characteristic `n`. -/


variable [CharP R n]

/--
theorem `cast_one'` / 定理 `cast_one'`

English:
theorem cast_one'
  statement: (cast (1 : ZMod n) : R) = 1
  proof: by simp

中文:
定理 cast_one'
  结论: (cast (1 : ZMod n) : R) = 1
  证明: by simp
-/
theorem cast_one' : (cast (1 : ZMod n) : R) = 1 := by simp

/--
theorem `cast_add'` / 定理 `cast_add'`

English:
theorem cast_add'
  given: (a b : ZMod n)
  statement: (cast (a + b : ZMod n) : R) = cast a + cast b
  proof: by simp

中文:
定理 cast_add'
  条件: (a b : ZMod n)
  结论: (cast (a + b : ZMod n) : R) = cast a + cast b
  证明: by simp
-/
theorem cast_add' (a b : ZMod n) : (cast (a + b : ZMod n) : R) = cast a + cast b := by simp

/--
theorem `cast_mul'` / 定理 `cast_mul'`

English:
theorem cast_mul'
  given: (a b : ZMod n)
  statement: (cast (a * b : ZMod n) : R) = cast a * cast b
  proof: by simp

中文:
定理 cast_mul'
  条件: (a b : ZMod n)
  结论: (cast (a * b : ZMod n) : R) = cast a * cast b
  证明: by simp
-/
theorem cast_mul' (a b : ZMod n) : (cast (a * b : ZMod n) : R) = cast a * cast b := by simp

/--
theorem `cast_sub'` / 定理 `cast_sub'`

English:
theorem cast_sub'
  given: (a b : ZMod n)
  statement: (cast (a - b : ZMod n) : R) = cast a - cast b
  proof: by simp

中文:
定理 cast_sub'
  条件: (a b : ZMod n)
  结论: (cast (a - b : ZMod n) : R) = cast a - cast b
  证明: by simp

Depends on / 依赖: Quotient, Quotient.eq, Quotient.inductionOn, inductionOn, mem_orbit, mul_smul, orbitRel, orbitRel.Quotient.mem_orbit
-/
theorem cast_sub' (a b : ZMod n) : (cast (a - b : ZMod n) : R) = cast a - cast b := by simp

/--
theorem `cast_pow'` / 定理 `cast_pow'`

English:
theorem cast_pow'
  given: (a : ZMod n) (k : Nat)
  statement: (cast (a ^ k : ZMod n) : R) = (cast a : R) ^ k
  proof: by simp

@[norm_cast]

中文:
定理 cast_pow'
  条件: (a : ZMod n) (k : 自然数)
  结论: (cast (a ^ k : ZMod n) : R) = (cast a : R) ^ k
  证明: by simp

@[norm_cast]
-/
theorem cast_pow' (a : ZMod n) (k : Nat) : (cast (a ^ k : ZMod n) : R) = (cast a : R) ^ k := by simp

@[norm_cast]
/--
theorem `cast_natCast'` / 定理 `cast_natCast'`

English:
theorem cast_natCast'
  given: (k : Nat)
  statement: (cast (k : ZMod n) : R) = k
  proof: by simp

@[norm_cast]

中文:
定理 cast_natCast'
  条件: (k : 自然数)
  结论: (cast (k : ZMod n) : R) = k
  证明: by simp

@[norm_cast]
-/
theorem cast_natCast' (k : Nat) : (cast (k : ZMod n) : R) = k := by simp

@[norm_cast]
/--
theorem `cast_intCast'` / 定理 `cast_intCast'`

English:
theorem cast_intCast'
  given: (k : Int)
  statement: (cast (k : ZMod n) : R) = k
  proof: by simp

中文:
定理 cast_intCast'
  条件: (k : 整数)
  结论: (cast (k : ZMod n) : R) = k
  证明: by simp
-/
theorem cast_intCast' (k : Int) : (cast (k : ZMod n) : R) = k := by simp

variable (R)

/--
theorem `castHom_injective` / 定理 `castHom_injective`

English:
theorem castHom_injective
  statement: Function.Injective (ZMod.castHom (dvd_refl n) R)
  proof: by
  rw [injective_iff_map_eq_zero]
  intro x
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective x
  rw [map_intCast]; rw [CharP.intCast_eq_zero_iff R n]; rw [CharP.intCast_eq_zero_iff (ZMod n) n]
  exact id

中文:
定理 castHom_injective
  结论: Function.Injective (ZMod.castHom (dvd_refl n) R)
  证明: by
  rw [injective_iff_map_eq_zero]
  intro x
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective x
  rw [map_intCast]; rw [CharP.intCast_eq_zero_iff R n]; rw [CharP.intCast_eq_zero_iff (ZMod n) n]
  exact id

Depends on / 依赖: CharP.intCast_eq_zero_iff, ZMod.intCast_surjective, injective_iff_map_eq_zero, intCast_eq_zero_iff, intCast_surjective, map_intCast
-/
theorem castHom_injective : Function.Injective (ZMod.castHom (dvd_refl n) R) := by
  rw [injective_iff_map_eq_zero]
  intro x
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective x
  rw [map_intCast]; rw [CharP.intCast_eq_zero_iff R n]; rw [CharP.intCast_eq_zero_iff (ZMod n) n]
  exact id

/--
theorem `castHom_bijective` / 定理 `castHom_bijective`

English:
theorem castHom_bijective
  given: [Fintype R] (h : Fintype.card R = n)
  proof: by
  have : NeZero n :=
    ⟨by
      intro hn
      rw [hn] at h
      exact (Fintype.card_eq_zero_iff.mp h).elim' 0⟩
  rw [Fintype.bijective_iff_injective_and_card]; rw [ZMod.card]; rw [h]; rw [eq_self_iff_true]; rw [and_true]
  apply ZMod.castHom_injective

中文:
定理 castHom_bijective
  条件: [Fintype R] (h : Fintype.card R = n)
  证明: by
  have : NeZero n :=
    ⟨by
      intro hn
      rw [hn] at h
      exact (Fintype.card_eq_zero_iff.mp h).elim' 0⟩
  rw [Fintype.bijective_iff_injective_and_card]; rw [ZMod.card]; rw [h]; rw [eq_self_iff_true]; rw [and_true]
  apply ZMod.castHom_injective

Depends on / 依赖: Fintype, Fintype.bijective_iff_injective_and_card, Fintype.card_eq_zero_iff.mp, NeZero, ZMod.card, ZMod.castHom_injective, and_true, bijective_iff_injective_and_card, card_eq_zero_iff, castHom_injective, eq_self_iff_true
-/
theorem castHom_bijective [Fintype R] (h : Fintype.card R = n) :
    Function.Bijective (ZMod.castHom (dvd_refl n) R) := by
  have : NeZero n :=
    ⟨by
      intro hn
      rw [hn] at h
      exact (Fintype.card_eq_zero_iff.mp h).elim' 0⟩
  rw [Fintype.bijective_iff_injective_and_card]; rw [ZMod.card]; rw [h]; rw [eq_self_iff_true]; rw [and_true]
  apply ZMod.castHom_injective

/--
Definition of `ringEquiv` / `ringEquiv` 的定义

English:
definition ringEquiv
  signature: [Fintype R] (h : Fintype.card R = n)
  body: RingEquiv.ofBijective _ (ZMod.castHom_bijective R h)

中文:
定义 ringEquiv
  签名: [Fintype R] (h : Fintype.card R = n)
  定义体: RingEquiv.ofBijective _ (ZMod.castHom_bijective R h)

Depends on / 依赖: RingEquiv, RingEquiv.ofBijective, ZMod.castHom_bijective, castHom_bijective, ofBijective
-/
noncomputable def ringEquiv [Fintype R] (h : Fintype.card R = n) : ZMod n ≃+* R :=
  RingEquiv.ofBijective _ (ZMod.castHom_bijective R h)

/--
Definition of `ringEquivOfPrime` / `ringEquivOfPrime` 的定义

English:
definition ringEquivOfPrime
  signature: [Fintype R] {p : Nat} (hp : p.Prime) (hR : Fintype.card R = p)
  body: have : Nontrivial R := Fintype.one_lt_card_iff_nontrivial.1 (hR ▸ hp.one_lt)
  -- The following line exists as `charP_of_card_eq_prime` in
  -- `Mathlib/Algebra/CharP/CharAndCard.lean`.
  have : CharP R p := (CharP.charP_iff_prime_eq_zero hp).2 (hR ▸ Nat.cast_card_eq_zero R)
  ZMod.ringEquiv R hR

@

中文:
定义 ringEquivOfPrime
  签名: [Fintype R] {p : 自然数} (hp : p.Prime) (hR : Fintype.card R = p)
  定义体: have : Nontrivial R := Fintype.one_lt_card_iff_nontrivial.1 (hR ▸ hp.one_lt)
  -- The following line exists as `charP_of_card_eq_prime` in
  -- `Mathlib/Algebra/CharP/CharAndCard.lean`.
  have : CharP R p := (CharP.charP_iff_prime_eq_zero hp).2 (hR ▸ Nat.cast_card_eq_zero R)
  ZMod.ringEquiv R hR

@

Depends on / 依赖: Fintype, Fintype.one_lt_card_iff_nontrivial, Nontrivial, hp.one_lt, one_lt, one_lt_card_iff_nontrivial
-/
noncomputable def ringEquivOfPrime [Fintype R] {p : Nat} (hp : p.Prime) (hR : Fintype.card R = p) :
    ZMod p ≃+* R :=
  have : Nontrivial R := Fintype.one_lt_card_iff_nontrivial.1 (hR ▸ hp.one_lt)
  -- The following line exists as `charP_of_card_eq_prime` in
  -- `Mathlib/Algebra/CharP/CharAndCard.lean`.
  have : CharP R p := (CharP.charP_iff_prime_eq_zero hp).2 (hR ▸ Nat.cast_card_eq_zero R)
  ZMod.ringEquiv R hR

@[simp]
/--
lemma `ringEquivOfPrime_eq_ringEquiv` / 引理 `ringEquivOfPrime_eq_ringEquiv`

English:
lemma ringEquivOfPrime_eq_ringEquiv
  statement: [Fintype R] {p : Nat} [CharP R p] (hp : p.Prime)
  proof: rfl

中文:
引理 ringEquivOfPrime_eq_ringEquiv
  结论: [Fintype R] {p : 自然数} [CharP R p] (hp : p.Prime)
  证明: rfl
-/
lemma ringEquivOfPrime_eq_ringEquiv [Fintype R] {p : Nat} [CharP R p] (hp : p.Prime)
    (hR : Fintype.card R = p) : ringEquivOfPrime R hp hR = ringEquiv R hR := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `ringEquivCongr` / `ringEquivCongr` 的定义

English:
definition ringEquivCongr
  signature: {m n : Nat} (h : m = n)
  body: by
  rcases m with - | m <;> rcases n with - | n
  · exact RingEquiv.refl _
  · exfalso
    exact n.succ_ne_zero h.symm
  · exfalso
    exact m.succ_ne_zero h
  · exact
      { finCongr h with
        map_mul' := fun a b => by
          dsimp [ZMod]
          ext
          rw [Fin.val_cast]; rw [Fin

中文:
定义 ringEquivCongr
  签名: {m n : 自然数} (h : m = n)
  定义体: by
  rcases m with - | m <;> rcases n with - | n
  · exact RingEquiv.refl _
  · exfalso
    exact n.succ_ne_zero h.symm
  · exfalso
    exact m.succ_ne_zero h
  · exact
      { finCongr h with
        map_mul' := fun a b => by
          dsimp [ZMod]
          ext
          rw [Fin.val_cast]; rw [Fin

Depends on / 依赖: Fin.val_add, Fin.val_cast, Fin.val_mul, RingEquiv, RingEquiv.refl, finCongr, h.symm, m.succ_ne_zero, map_add, map_mul, n.succ_ne_zero, succ_ne_zero, val_add, val_cast, val_mul
-/
def ringEquivCongr {m n : Nat} (h : m = n) : ZMod m ≃+* ZMod n := by
  rcases m with - | m <;> rcases n with - | n
  · exact RingEquiv.refl _
  · exfalso
    exact n.succ_ne_zero h.symm
  · exfalso
    exact m.succ_ne_zero h
  · exact
      { finCongr h with
        map_mul' := fun a b => by
          dsimp [ZMod]
          ext
          rw [Fin.val_cast]; rw [Fin.val_mul]; rw [Fin.val_mul]; rw [Fin.val_cast]; rw [Fin.val_cast]; rw [← h]
        map_add' := fun a b => by
          dsimp [ZMod]
          ext
          rw [Fin.val_cast]; rw [Fin.val_add]; rw [Fin.val_add]; rw [Fin.val_cast]; rw [Fin.val_cast]; rw [← h] }

/--
lemma `ringEquivCongr_refl` / 引理 `ringEquivCongr_refl`

English:
lemma ringEquivCongr_refl
  given: (a : Nat)
  statement: ringEquivCongr (rfl : a = a) = .refl _
  proof: by
  cases a <;> rfl

中文:
引理 ringEquivCongr_refl
  条件: (a : 自然数)
  结论: ringEquivCongr (rfl : a = a) = .refl _
  证明: by
  cases a <;> rfl
-/
@[simp] lemma ringEquivCongr_refl (a : Nat) : ringEquivCongr (rfl : a = a) = .refl _ := by
  cases a <;> rfl

/--
lemma `ringEquivCongr_refl_apply` / 引理 `ringEquivCongr_refl_apply`

English:
lemma ringEquivCongr_refl_apply
  given: {a : Nat} (x : ZMod a)
  statement: ringEquivCongr rfl x = x
  proof: by
  rw [ringEquivCongr_refl]
  rfl

中文:
引理 ringEquivCongr_refl_apply
  条件: {a : 自然数} (x : ZMod a)
  结论: ringEquivCongr rfl x = x
  证明: by
  rw [ringEquivCongr_refl]
  rfl

Depends on / 依赖: ringEquivCongr_refl
-/
lemma ringEquivCongr_refl_apply {a : Nat} (x : ZMod a) : ringEquivCongr rfl x = x := by
  rw [ringEquivCongr_refl]
  rfl

/--
lemma `ringEquivCongr_symm` / 引理 `ringEquivCongr_symm`

English:
lemma ringEquivCongr_symm
  given: {a b : Nat} (hab : a = b)
  proof: by
  subst hab
  cases a <;> rfl

中文:
引理 ringEquivCongr_symm
  条件: {a b : 自然数} (hab : a = b)
  证明: by
  subst hab
  cases a <;> rfl
-/
lemma ringEquivCongr_symm {a b : Nat} (hab : a = b) :
    (ringEquivCongr hab).symm = ringEquivCongr hab.symm := by
  subst hab
  cases a <;> rfl

/--
lemma `ringEquivCongr_trans` / 引理 `ringEquivCongr_trans`

English:
lemma ringEquivCongr_trans
  given: {a b c : Nat} (hab : a = b) (hbc : b = c)
  proof: by
  subst hab hbc
  cases a <;> rfl

中文:
引理 ringEquivCongr_trans
  条件: {a b c : 自然数} (hab : a = b) (hbc : b = c)
  证明: by
  subst hab hbc
  cases a <;> rfl
-/
lemma ringEquivCongr_trans {a b c : Nat} (hab : a = b) (hbc : b = c) :
    (ringEquivCongr hab).trans (ringEquivCongr hbc) = ringEquivCongr (hab.trans hbc) := by
  subst hab hbc
  cases a <;> rfl

/--
lemma `ringEquivCongr_ringEquivCongr_apply` / 引理 `ringEquivCongr_ringEquivCongr_apply`

English:
lemma ringEquivCongr_ringEquivCongr_apply
  given: {a b c : Nat} (hab : a = b) (hbc : b = c) (x : ZMod a)
  proof: by
  rw [← ringEquivCongr_trans hab hbc]
  rfl

中文:
引理 ringEquivCongr_ringEquivCongr_apply
  条件: {a b c : 自然数} (hab : a = b) (hbc : b = c) (x : ZMod a)
  证明: by
  rw [← ringEquivCongr_trans hab hbc]
  rfl

Depends on / 依赖: ringEquivCongr_trans
-/
lemma ringEquivCongr_ringEquivCongr_apply {a b c : Nat} (hab : a = b) (hbc : b = c) (x : ZMod a) :
    ringEquivCongr hbc (ringEquivCongr hab x) = ringEquivCongr (hab.trans hbc) x := by
  rw [← ringEquivCongr_trans hab hbc]
  rfl

/--
lemma `ringEquivCongr_val` / 引理 `ringEquivCongr_val`

English:
lemma ringEquivCongr_val
  given: {a b : Nat} (h : a = b) (x : ZMod a)
  proof: by
  subst h
  cases a <;> rfl

中文:
引理 ringEquivCongr_val
  条件: {a b : 自然数} (h : a = b) (x : ZMod a)
  证明: by
  subst h
  cases a <;> rfl
-/
lemma ringEquivCongr_val {a b : Nat} (h : a = b) (x : ZMod a) :
    ZMod.val ((ZMod.ringEquivCongr h) x) = ZMod.val x := by
  subst h
  cases a <;> rfl

/--
lemma `ringEquivCongr_intCast` / 引理 `ringEquivCongr_intCast`

English:
lemma ringEquivCongr_intCast
  given: {a b : Nat} (h : a = b) (z : Int)
  proof: map_intCast (ringEquivCongr h) z

中文:
引理 ringEquivCongr_intCast
  条件: {a b : 自然数} (h : a = b) (z : 整数)
  证明: map_intCast (ringEquivCongr h) z

Depends on / 依赖: map_intCast, ringEquivCongr
-/
lemma ringEquivCongr_intCast {a b : Nat} (h : a = b) (z : Int) :
    ZMod.ringEquivCongr h z = z := map_intCast (ringEquivCongr h) z

end CharEq

end UniversalProperty

variable {m n : Nat}

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `val_eq_zero` / 定理 `val_eq_zero`

English:
theorem val_eq_zero
  statement: forall {n : Nat} (a : ZMod n), a.val = 0 ↔ a = 0

中文:
定理 val_eq_zero
  结论: 对任意 {n : 自然数} (a : ZMod n), a.val = 0 ↔ a = 0
-/
theorem val_eq_zero : forall {n : Nat} (a : ZMod n), a.val = 0 ↔ a = 0
  | 0, _ => Int.natAbs_eq_zero
  | n + 1, a => by
    rw [Fin.ext_iff]
    exact Iff.rfl

/--
theorem `intCast_eq_intCast_iff` / 定理 `intCast_eq_intCast_iff`

English:
theorem intCast_eq_intCast_iff
  given: (a b : Int) (c : Nat)
  statement: (a : ZMod c) = (b : ZMod c) ↔ a ≡ b [ZMOD c]
  proof: CharP.intCast_eq_intCast (ZMod c) c

中文:
定理 intCast_eq_intCast_iff
  条件: (a b : 整数) (c : 自然数)
  结论: (a : ZMod c) = (b : ZMod c) ↔ a ≡ b [ZMOD c]
  证明: CharP.intCast_eq_intCast (ZMod c) c

Depends on / 依赖: CharP.intCast_eq_intCast, intCast_eq_intCast
-/
theorem intCast_eq_intCast_iff (a b : Int) (c : Nat) : (a : ZMod c) = (b : ZMod c) ↔ a ≡ b [ZMOD c] :=
  CharP.intCast_eq_intCast (ZMod c) c

/--
theorem `intCast_eq_intCast_iff'` / 定理 `intCast_eq_intCast_iff'`

English:
theorem intCast_eq_intCast_iff'
  given: (a b : Int) (c : Nat)
  statement: (a : ZMod c) = (b : ZMod c) ↔ a % c = b % c
  proof: ZMod.intCast_eq_intCast_iff a b c

中文:
定理 intCast_eq_intCast_iff'
  条件: (a b : 整数) (c : 自然数)
  结论: (a : ZMod c) = (b : ZMod c) ↔ a % c = b % c
  证明: ZMod.intCast_eq_intCast_iff a b c

Depends on / 依赖: ZMod.intCast_eq_intCast_iff, intCast_eq_intCast_iff
-/
theorem intCast_eq_intCast_iff' (a b : Int) (c : Nat) : (a : ZMod c) = (b : ZMod c) ↔ a % c = b % c :=
  ZMod.intCast_eq_intCast_iff a b c

/--
theorem `val_intCast` / 定理 `val_intCast`

English:
theorem val_intCast
  given: {n : Nat} (a : Int) [NeZero n]
  statement: ↑(a : ZMod n).val = a % n
  proof: by
  have hle : (0 : Int) <= ↑(a : ZMod n).val := Int.natCast_nonneg _
  have hlt : ↑(a : ZMod n).val < (n : Int) := Int.ofNat_lt.mpr (ZMod.val_lt a)
  refine (Int.emod_eq_of_lt hle hlt).symm.trans ?_
  rw [← ZMod.intCast_eq_intCast_iff']; rw [Int.cast_natCast]; rw [ZMod.natCast_val]; rw [ZMod.cast_

中文:
定理 val_intCast
  条件: {n : 自然数} (a : 整数) [NeZero n]
  结论: ↑(a : ZMod n).val = a % n
  证明: by
  have hle : (0 : Int) <= ↑(a : ZMod n).val := Int.natCast_nonneg _
  have hlt : ↑(a : ZMod n).val < (n : Int) := Int.ofNat_lt.mpr (ZMod.val_lt a)
  refine (Int.emod_eq_of_lt hle hlt).symm.trans ?_
  rw [← ZMod.intCast_eq_intCast_iff']; rw [Int.cast_natCast]; rw [ZMod.natCast_val]; rw [ZMod.cast_

Depends on / 依赖: Int.cast_natCast, Int.emod_eq_of_lt, Int.natCast_nonneg, Int.ofNat_lt.mpr, ZMod.cast_id, ZMod.intCast_eq_intCast_iff, ZMod.natCast_val, ZMod.val_lt, cast_id, cast_natCast, emod_eq_of_lt, intCast_eq_intCast_iff, natCast_nonneg, natCast_val, ofNat_lt, symm.trans, val_lt
-/
theorem val_intCast {n : Nat} (a : Int) [NeZero n] : ↑(a : ZMod n).val = a % n := by
  have hle : (0 : Int) <= ↑(a : ZMod n).val := Int.natCast_nonneg _
  have hlt : ↑(a : ZMod n).val < (n : Int) := Int.ofNat_lt.mpr (ZMod.val_lt a)
  refine (Int.emod_eq_of_lt hle hlt).symm.trans ?_
  rw [← ZMod.intCast_eq_intCast_iff']; rw [Int.cast_natCast]; rw [ZMod.natCast_val]; rw [ZMod.cast_id]

/--
theorem `natCast_eq_natCast_iff` / 定理 `natCast_eq_natCast_iff`

English:
theorem natCast_eq_natCast_iff
  given: (a b c : Nat)
  statement: (a : ZMod c) = (b : ZMod c) ↔ a ≡ b [MOD c]
  proof: by
  simpa [Int.natCast_modEq_iff] using ZMod.intCast_eq_intCast_iff a b c

中文:
定理 natCast_eq_natCast_iff
  条件: (a b c : 自然数)
  结论: (a : ZMod c) = (b : ZMod c) ↔ a ≡ b [MOD c]
  证明: by
  simpa [Int.natCast_modEq_iff] using ZMod.intCast_eq_intCast_iff a b c

Depends on / 依赖: Int.natCast_modEq_iff, ZMod.intCast_eq_intCast_iff, intCast_eq_intCast_iff, natCast_modEq_iff
-/
theorem natCast_eq_natCast_iff (a b c : Nat) : (a : ZMod c) = (b : ZMod c) ↔ a ≡ b [MOD c] := by
  simpa [Int.natCast_modEq_iff] using ZMod.intCast_eq_intCast_iff a b c

/--
theorem `natCast_eq_natCast_iff'` / 定理 `natCast_eq_natCast_iff'`

English:
theorem natCast_eq_natCast_iff'
  given: (a b c : Nat)
  statement: (a : ZMod c) = (b : ZMod c) ↔ a % c = b % c
  proof: ZMod.natCast_eq_natCast_iff a b c

中文:
定理 natCast_eq_natCast_iff'
  条件: (a b c : 自然数)
  结论: (a : ZMod c) = (b : ZMod c) ↔ a % c = b % c
  证明: ZMod.natCast_eq_natCast_iff a b c

Depends on / 依赖: ZMod.natCast_eq_natCast_iff, natCast_eq_natCast_iff
-/
theorem natCast_eq_natCast_iff' (a b c : Nat) : (a : ZMod c) = (b : ZMod c) ↔ a % c = b % c :=
  ZMod.natCast_eq_natCast_iff a b c

/--
theorem `intCast_zmod_eq_zero_iff_dvd` / 定理 `intCast_zmod_eq_zero_iff_dvd`

English:
theorem intCast_zmod_eq_zero_iff_dvd
  given: (a : Int) (b : Nat)
  statement: (a : ZMod b) = 0 ↔ (b : Int) ∣ a
  proof: by
  rw [← Int.cast_zero]; rw [ZMod.intCast_eq_intCast_iff]; rw [Int.modEq_zero_iff_dvd]

中文:
定理 intCast_zmod_eq_zero_iff_dvd
  条件: (a : 整数) (b : 自然数)
  结论: (a : ZMod b) = 0 ↔ (b : 整数) ∣ a
  证明: by
  rw [← Int.cast_zero]; rw [ZMod.intCast_eq_intCast_iff]; rw [Int.modEq_zero_iff_dvd]

Depends on / 依赖: Int.cast_zero, Int.modEq_zero_iff_dvd, ZMod.intCast_eq_intCast_iff, cast_zero, intCast_eq_intCast_iff, modEq_zero_iff_dvd
-/
theorem intCast_zmod_eq_zero_iff_dvd (a : Int) (b : Nat) : (a : ZMod b) = 0 ↔ (b : Int) ∣ a := by
  rw [← Int.cast_zero]; rw [ZMod.intCast_eq_intCast_iff]; rw [Int.modEq_zero_iff_dvd]

/--
theorem `intCast_eq_intCast_iff_dvd_sub` / 定理 `intCast_eq_intCast_iff_dvd_sub`

English:
theorem intCast_eq_intCast_iff_dvd_sub
  given: (a b : Int) (c : Nat)
  statement: (a : ZMod c) = ↑b ↔ ↑c ∣ b - a
  proof: by
  rw [ZMod.intCast_eq_intCast_iff]; rw [Int.modEq_iff_dvd]

中文:
定理 intCast_eq_intCast_iff_dvd_sub
  条件: (a b : 整数) (c : 自然数)
  结论: (a : ZMod c) = ↑b ↔ ↑c ∣ b - a
  证明: by
  rw [ZMod.intCast_eq_intCast_iff]; rw [Int.modEq_iff_dvd]

Depends on / 依赖: Int.modEq_iff_dvd, ZMod.intCast_eq_intCast_iff, intCast_eq_intCast_iff, modEq_iff_dvd
-/
theorem intCast_eq_intCast_iff_dvd_sub (a b : Int) (c : Nat) : (a : ZMod c) = ↑b ↔ ↑c ∣ b - a := by
  rw [ZMod.intCast_eq_intCast_iff]; rw [Int.modEq_iff_dvd]

/--
theorem `natCast_eq_zero_iff` / 定理 `natCast_eq_zero_iff`

English:
theorem natCast_eq_zero_iff
  given: (a b : Nat)
  statement: (a : ZMod b) = 0 ↔ b ∣ a
  proof: by
  rw [← Nat.cast_zero]; rw [ZMod.natCast_eq_natCast_iff]; rw [Nat.modEq_zero_iff_dvd]

中文:
定理 natCast_eq_zero_iff
  条件: (a b : 自然数)
  结论: (a : ZMod b) = 0 ↔ b ∣ a
  证明: by
  rw [← Nat.cast_zero]; rw [ZMod.natCast_eq_natCast_iff]; rw [Nat.modEq_zero_iff_dvd]

Depends on / 依赖: Nat.cast_zero, Nat.modEq_zero_iff_dvd, ZMod.natCast_eq_natCast_iff, cast_zero, modEq_zero_iff_dvd, natCast_eq_natCast_iff
-/
theorem natCast_eq_zero_iff (a b : Nat) : (a : ZMod b) = 0 ↔ b ∣ a := by
  rw [← Nat.cast_zero]; rw [ZMod.natCast_eq_natCast_iff]; rw [Nat.modEq_zero_iff_dvd]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `coe_intCast` / 定理 `coe_intCast`

English:
theorem coe_intCast
  given: (a : Int)
  statement: cast (a : ZMod n) = a % n
  proof: by
  cases n
  · rw [Int.ofNat_zero, Int.emod_zero, Int.cast_id]; rfl
  · rw [← val_intCast, val]; rfl

中文:
定理 coe_intCast
  条件: (a : 整数)
  结论: cast (a : ZMod n) = a % n
  证明: by
  cases n
  · rw [Int.ofNat_zero, Int.emod_zero, Int.cast_id]; rfl
  · rw [← val_intCast, val]; rfl

Depends on / 依赖: Int.cast_id, Int.emod_zero, Int.ofNat_zero, cast_id, emod_zero, ofNat_zero, val_intCast
-/
theorem coe_intCast (a : Int) : cast (a : ZMod n) = a % n := by
  cases n
  · rw [Int.ofNat_zero, Int.emod_zero, Int.cast_id]; rfl
  · rw [← val_intCast, val]; rfl

/--
lemma `intCast_cast_add` / 引理 `intCast_cast_add`

English:
lemma intCast_cast_add
  given: (x y : ZMod n)
  statement: (cast (x + y) : Int) = (cast x + cast y) % n
  proof: by
  rw [← ZMod.coe_intCast]; rw [Int.cast_add]; rw [ZMod.intCast_zmod_cast]; rw [ZMod.intCast_zmod_cast]

中文:
引理 intCast_cast_add
  条件: (x y : ZMod n)
  结论: (cast (x + y) : 整数) = (cast x + cast y) % n
  证明: by
  rw [← ZMod.coe_intCast]; rw [Int.cast_add]; rw [ZMod.intCast_zmod_cast]; rw [ZMod.intCast_zmod_cast]

Depends on / 依赖: Int.cast_add, ZMod.coe_intCast, ZMod.intCast_zmod_cast, cast_add, coe_intCast, intCast_zmod_cast
-/
lemma intCast_cast_add (x y : ZMod n) : (cast (x + y) : Int) = (cast x + cast y) % n := by
  rw [← ZMod.coe_intCast]; rw [Int.cast_add]; rw [ZMod.intCast_zmod_cast]; rw [ZMod.intCast_zmod_cast]

/--
lemma `intCast_cast_mul` / 引理 `intCast_cast_mul`

English:
lemma intCast_cast_mul
  given: (x y : ZMod n)
  statement: (cast (x * y) : Int) = cast x * cast y % n
  proof: by
  rw [← ZMod.coe_intCast]; rw [Int.cast_mul]; rw [ZMod.intCast_zmod_cast]; rw [ZMod.intCast_zmod_cast]

中文:
引理 intCast_cast_mul
  条件: (x y : ZMod n)
  结论: (cast (x * y) : 整数) = cast x * cast y % n
  证明: by
  rw [← ZMod.coe_intCast]; rw [Int.cast_mul]; rw [ZMod.intCast_zmod_cast]; rw [ZMod.intCast_zmod_cast]

Depends on / 依赖: Int.cast_mul, ZMod.coe_intCast, ZMod.intCast_zmod_cast, cast_mul, coe_intCast, intCast_zmod_cast
-/
lemma intCast_cast_mul (x y : ZMod n) : (cast (x * y) : Int) = cast x * cast y % n := by
  rw [← ZMod.coe_intCast]; rw [Int.cast_mul]; rw [ZMod.intCast_zmod_cast]; rw [ZMod.intCast_zmod_cast]

/--
lemma `intCast_cast_sub` / 引理 `intCast_cast_sub`

English:
lemma intCast_cast_sub
  given: (x y : ZMod n)
  statement: (cast (x - y) : Int) = (cast x - cast y) % n
  proof: by
  rw [← ZMod.coe_intCast]; rw [Int.cast_sub]; rw [ZMod.intCast_zmod_cast]; rw [ZMod.intCast_zmod_cast]

中文:
引理 intCast_cast_sub
  条件: (x y : ZMod n)
  结论: (cast (x - y) : 整数) = (cast x - cast y) % n
  证明: by
  rw [← ZMod.coe_intCast]; rw [Int.cast_sub]; rw [ZMod.intCast_zmod_cast]; rw [ZMod.intCast_zmod_cast]

Depends on / 依赖: Int.cast_sub, ZMod.coe_intCast, ZMod.intCast_zmod_cast, cast_sub, coe_intCast, intCast_zmod_cast
-/
lemma intCast_cast_sub (x y : ZMod n) : (cast (x - y) : Int) = (cast x - cast y) % n := by
  rw [← ZMod.coe_intCast]; rw [Int.cast_sub]; rw [ZMod.intCast_zmod_cast]; rw [ZMod.intCast_zmod_cast]

/--
lemma `intCast_cast_neg` / 引理 `intCast_cast_neg`

English:
lemma intCast_cast_neg
  given: (x : ZMod n)
  statement: (cast (-x) : Int) = -cast x % n
  proof: by
  rw [← ZMod.coe_intCast]; rw [Int.cast_neg]; rw [ZMod.intCast_zmod_cast]

中文:
引理 intCast_cast_neg
  条件: (x : ZMod n)
  结论: (cast (-x) : 整数) = -cast x % n
  证明: by
  rw [← ZMod.coe_intCast]; rw [Int.cast_neg]; rw [ZMod.intCast_zmod_cast]

Depends on / 依赖: Int.cast_neg, ZMod.coe_intCast, ZMod.intCast_zmod_cast, cast_neg, coe_intCast, intCast_zmod_cast
-/
lemma intCast_cast_neg (x : ZMod n) : (cast (-x) : Int) = -cast x % n := by
  rw [← ZMod.coe_intCast]; rw [Int.cast_neg]; rw [ZMod.intCast_zmod_cast]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `val_neg_one` / 定理 `val_neg_one`

English:
theorem val_neg_one
  given: (n : Nat)
  statement: (-1 : ZMod n.succ).val = n
  proof: by
  dsimp [val, Fin.val_neg']
  cases n
  · simp
  · dsimp [ZMod, ZMod.cast]
    rw [Fin.coe_neg_one]

中文:
定理 val_neg_one
  条件: (n : 自然数)
  结论: (-1 : ZMod n.succ).val = n
  证明: by
  dsimp [val, Fin.val_neg']
  cases n
  · simp
  · dsimp [ZMod, ZMod.cast]
    rw [Fin.coe_neg_one]

Depends on / 依赖: Fin.coe_neg_one, Fin.val_neg, ZMod.cast, coe_neg_one, val_neg
-/
theorem val_neg_one (n : Nat) : (-1 : ZMod n.succ).val = n := by
  dsimp [val, Fin.val_neg']
  cases n
  · simp
  · dsimp [ZMod, ZMod.cast]
    rw [Fin.coe_neg_one]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `cast_neg_one` / 定理 `cast_neg_one`

English:
theorem cast_neg_one
  given: {R : Type*} [Ring R] (n : Nat)
  statement: cast (-1 : ZMod n) = (n - 1 : R)
  proof: by
  rcases n with - | n
  · dsimp [ZMod, ZMod.cast]; simp
  · rw [← natCast_val, val_neg_one, Nat.cast_succ, add_sub_cancel_right]

中文:
定理 cast_neg_one
  条件: {R : 类型} [Ring R] (n : 自然数)
  结论: cast (-1 : ZMod n) = (n - 1 : R)
  证明: by
  rcases n with - | n
  · dsimp [ZMod, ZMod.cast]; simp
  · rw [← natCast_val, val_neg_one, Nat.cast_succ, add_sub_cancel_right]

Depends on / 依赖: Nat.cast_succ, ZMod.cast, add_sub_cancel_right, cast_succ, natCast_val, val_neg_one
-/
theorem cast_neg_one {R : Type*} [Ring R] (n : Nat) : cast (-1 : ZMod n) = (n - 1 : R) := by
  rcases n with - | n
  · dsimp [ZMod, ZMod.cast]; simp
  · rw [← natCast_val, val_neg_one, Nat.cast_succ, add_sub_cancel_right]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `cast_sub_one` / 定理 `cast_sub_one`

English:
theorem cast_sub_one
  given: {R : Type*} [Ring R] {n : Nat} (k : ZMod n)
  proof: by
  split_ifs with hk
  · rw [hk, zero_sub, ZMod.cast_neg_one]
  · cases n
    · dsimp [ZMod, ZMod.cast]
      rw [Int.cast_sub]; rw [Int.cast_one]
    · dsimp [ZMod, ZMod.cast, ZMod.val]
      rw [Fin.coe_sub_one]; rw [if_neg]
      · rw [Nat.cast_sub, Nat.cast_one]
        rwa [Fin.ext_iff, Fin.v

中文:
定理 cast_sub_one
  条件: {R : 类型} [Ring R] {n : 自然数} (k : ZMod n)
  证明: by
  split_ifs with hk
  · rw [hk, zero_sub, ZMod.cast_neg_one]
  · cases n
    · dsimp [ZMod, ZMod.cast]
      rw [Int.cast_sub]; rw [Int.cast_one]
    · dsimp [ZMod, ZMod.cast, ZMod.val]
      rw [Fin.coe_sub_one]; rw [if_neg]
      · rw [Nat.cast_sub, Nat.cast_one]
        rwa [Fin.ext_iff, Fin.v

Depends on / 依赖: Fin.coe_sub_one, Fin.ext_iff, Fin.val_zero, Int.cast_one, Int.cast_sub, Nat.cast_one, Nat.cast_sub, Nat.one_le_iff_ne_zero, ZMod.cast, ZMod.cast_neg_one, ZMod.val, cast_neg_one, cast_one, cast_sub, coe_sub_one, ext_iff, if_neg, one_le_iff_ne_zero, split_ifs, val_zero
-/
theorem cast_sub_one {R : Type*} [Ring R] {n : Nat} (k : ZMod n) :
    (cast (k - 1 : ZMod n) : R) = (if k = 0 then (n : R) else cast k) - 1 := by
  split_ifs with hk
  · rw [hk, zero_sub, ZMod.cast_neg_one]
  · cases n
    · dsimp [ZMod, ZMod.cast]
      rw [Int.cast_sub]; rw [Int.cast_one]
    · dsimp [ZMod, ZMod.cast, ZMod.val]
      rw [Fin.coe_sub_one]; rw [if_neg]
      · rw [Nat.cast_sub, Nat.cast_one]
        rwa [Fin.ext_iff, Fin.val_zero, ← Ne, ← Nat.one_le_iff_ne_zero] at hk
      · exact hk

/--
theorem `natCast_eq_iff` / 定理 `natCast_eq_iff`

English:
theorem natCast_eq_iff
  given: (p : Nat) (n : Nat) (z : ZMod p) [NeZero p]
  proof: by
  constructor
  · rintro rfl
    refine ⟨n / p, ?_⟩
    rw [val_natCast]; rw [Nat.mod_add_div]
  · rintro ⟨k, rfl⟩
    rw [Nat.cast_add]; rw [natCast_zmod_val]; rw [Nat.cast_mul]; rw [natCast_self]; rw [zero_mul]; rw [add_zero]

中文:
定理 natCast_eq_iff
  条件: (p : 自然数) (n : 自然数) (z : ZMod p) [NeZero p]
  证明: by
  constructor
  · rintro rfl
    refine ⟨n / p, ?_⟩
    rw [val_natCast]; rw [Nat.mod_add_div]
  · rintro ⟨k, rfl⟩
    rw [Nat.cast_add]; rw [natCast_zmod_val]; rw [Nat.cast_mul]; rw [natCast_self]; rw [zero_mul]; rw [add_zero]

Depends on / 依赖: Nat.cast_add, Nat.cast_mul, Nat.mod_add_div, add_zero, cast_add, cast_mul, mod_add_div, natCast_self, natCast_zmod_val, val_natCast, zero_mul
-/
theorem natCast_eq_iff (p : Nat) (n : Nat) (z : ZMod p) [NeZero p] :
    ↑n = z ↔ exists k, n = z.val + p * k := by
  constructor
  · rintro rfl
    refine ⟨n / p, ?_⟩
    rw [val_natCast]; rw [Nat.mod_add_div]
  · rintro ⟨k, rfl⟩
    rw [Nat.cast_add]; rw [natCast_zmod_val]; rw [Nat.cast_mul]; rw [natCast_self]; rw [zero_mul]; rw [add_zero]

/--
theorem `intCast_eq_iff` / 定理 `intCast_eq_iff`

English:
theorem intCast_eq_iff
  given: (p : Nat) (n : Int) (z : ZMod p) [NeZero p]
  proof: by
  constructor
  · rintro rfl
    refine ⟨n / p, ?_⟩
    rw [val_intCast]; rw [Int.emod_add_mul_ediv]
  · rintro ⟨k, rfl⟩
    rw [Int.cast_add]; rw [Int.cast_mul]; rw [Int.cast_natCast]; rw [Int.cast_natCast]; rw [natCast_val]; rw [ZMod.natCast_self]; rw [zero_mul]; rw [add_zero]; rw [cast_id]

@[

中文:
定理 intCast_eq_iff
  条件: (p : 自然数) (n : 整数) (z : ZMod p) [NeZero p]
  证明: by
  constructor
  · rintro rfl
    refine ⟨n / p, ?_⟩
    rw [val_intCast]; rw [Int.emod_add_mul_ediv]
  · rintro ⟨k, rfl⟩
    rw [Int.cast_add]; rw [Int.cast_mul]; rw [Int.cast_natCast]; rw [Int.cast_natCast]; rw [natCast_val]; rw [ZMod.natCast_self]; rw [zero_mul]; rw [add_zero]; rw [cast_id]

@[

Depends on / 依赖: Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.emod_add_mul_ediv, ZMod.natCast_self, add_zero, cast_add, cast_id, cast_mul, cast_natCast, emod_add_mul_ediv, natCast_self, natCast_val, val_intCast, zero_mul
-/
theorem intCast_eq_iff (p : Nat) (n : Int) (z : ZMod p) [NeZero p] :
    ↑n = z ↔ exists k, n = z.val + p * k := by
  constructor
  · rintro rfl
    refine ⟨n / p, ?_⟩
    rw [val_intCast]; rw [Int.emod_add_mul_ediv]
  · rintro ⟨k, rfl⟩
    rw [Int.cast_add]; rw [Int.cast_mul]; rw [Int.cast_natCast]; rw [Int.cast_natCast]; rw [natCast_val]; rw [ZMod.natCast_self]; rw [zero_mul]; rw [add_zero]; rw [cast_id]

@[push_cast, simp]
/--
theorem `intCast_mod` / 定理 `intCast_mod`

English:
theorem intCast_mod
  given: (a : Int) (b : Nat)
  statement: ((a % b : Int) : ZMod b) = (a : ZMod b)
  proof: by
  rw [ZMod.intCast_eq_intCast_iff]
  apply Int.mod_modEq

中文:
定理 intCast_mod
  条件: (a : 整数) (b : 自然数)
  结论: ((a % b : 整数) : ZMod b) = (a : ZMod b)
  证明: by
  rw [ZMod.intCast_eq_intCast_iff]
  apply Int.mod_modEq

Depends on / 依赖: Int.mod_modEq, ZMod.intCast_eq_intCast_iff, intCast_eq_intCast_iff, mod_modEq
-/
theorem intCast_mod (a : Int) (b : Nat) : ((a % b : Int) : ZMod b) = (a : ZMod b) := by
  rw [ZMod.intCast_eq_intCast_iff]
  apply Int.mod_modEq

/--
theorem `ker_intCastAddHom` / 定理 `ker_intCastAddHom`

English:
theorem ker_intCastAddHom
  given: (n : Nat)
  proof: by
  ext
  rw [Int.mem_zmultiples_iff]; rw [AddMonoidHom.mem_ker]; rw [Int.coe_castAddHom]; rw [intCast_zmod_eq_zero_iff_dvd]

中文:
定理 ker_intCastAddHom
  条件: (n : 自然数)
  证明: by
  ext
  rw [Int.mem_zmultiples_iff]; rw [AddMonoidHom.mem_ker]; rw [Int.coe_castAddHom]; rw [intCast_zmod_eq_zero_iff_dvd]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mem_ker, Int.coe_castAddHom, Int.mem_zmultiples_iff, coe_castAddHom, intCast_zmod_eq_zero_iff_dvd, mem_ker, mem_zmultiples_iff
-/
theorem ker_intCastAddHom (n : Nat) :
    (Int.castAddHom (ZMod n)).ker = AddSubgroup.zmultiples (n : Int) := by
  ext
  rw [Int.mem_zmultiples_iff]; rw [AddMonoidHom.mem_ker]; rw [Int.coe_castAddHom]; rw [intCast_zmod_eq_zero_iff_dvd]

/--
theorem `cast_injective_of_le` / 定理 `cast_injective_of_le`

English:
theorem cast_injective_of_le
  given: {m n : Nat} [nzm : NeZero m] (h : m <= n)
  proof: by
  cases m with
  | zero => cases nzm; simp_all
  | succ m =>
    rintro ⟨x, hx⟩ ⟨y, hy⟩ f
    simp only [cast, val, natCast_eq_natCast_iff',
      Nat.mod_eq_of_lt (hx.trans_le h), Nat.mod_eq_of_lt (hy.trans_le h)] at f
    apply Fin.ext
    exact f

中文:
定理 cast_injective_of_le
  条件: {m n : 自然数} [nzm : NeZero m] (h : m <= n)
  证明: by
  cases m with
  | zero => cases nzm; simp_all
  | succ m =>
    rintro ⟨x, hx⟩ ⟨y, hy⟩ f
    simp only [cast, val, natCast_eq_natCast_iff',
      Nat.mod_eq_of_lt (hx.trans_le h), Nat.mod_eq_of_lt (hy.trans_le h)] at f
    apply Fin.ext
    exact f

Depends on / 依赖: Fin.ext, Nat.mod_eq_of_lt, hx.trans_le, hy.trans_le, mod_eq_of_lt, natCast_eq_natCast_iff, trans_le
-/
theorem cast_injective_of_le {m n : Nat} [nzm : NeZero m] (h : m <= n) :
    Function.Injective (@cast (ZMod n) _ m) := by
  cases m with
  | zero => cases nzm; simp_all
  | succ m =>
    rintro ⟨x, hx⟩ ⟨y, hy⟩ f
    simp only [cast, val, natCast_eq_natCast_iff',
      Nat.mod_eq_of_lt (hx.trans_le h), Nat.mod_eq_of_lt (hy.trans_le h)] at f
    apply Fin.ext
    exact f

/--
theorem `cast_zmod_eq_zero_iff_of_le` / 定理 `cast_zmod_eq_zero_iff_of_le`

English:
theorem cast_zmod_eq_zero_iff_of_le
  given: {m n : Nat} [NeZero m] (h : m <= n) (a : ZMod m)
  proof: by
  rw [← ZMod.cast_zero (n := m)]
  exact Injective.eq_iff' (cast_injective_of_le h) rfl

@[simp]

中文:
定理 cast_zmod_eq_zero_iff_of_le
  条件: {m n : 自然数} [NeZero m] (h : m <= n) (a : ZMod m)
  证明: by
  rw [← ZMod.cast_zero (n := m)]
  exact Injective.eq_iff' (cast_injective_of_le h) rfl

@[simp]

Depends on / 依赖: Injective, Injective.eq_iff, ZMod.cast_zero, cast_injective_of_le, cast_zero, eq_iff
-/
theorem cast_zmod_eq_zero_iff_of_le {m n : Nat} [NeZero m] (h : m <= n) (a : ZMod m) :
    (cast a : ZMod n) = 0 ↔ a = 0 := by
  rw [← ZMod.cast_zero (n := m)]
  exact Injective.eq_iff' (cast_injective_of_le h) rfl

@[simp]
/--
theorem `natCast_toNat` / 定理 `natCast_toNat`

English:
theorem natCast_toNat
  given: (p : Nat)
  statement: forall {z : Int} (_h : 0 <= z), (z.toNat : ZMod p) = z

中文:
定理 natCast_toNat
  条件: (p : 自然数)
  结论: 对任意 {z : 整数} (_h : 0 <= z), (z.to自然数 : ZMod p) = z
-/
theorem natCast_toNat (p : Nat) : forall {z : Int} (_h : 0 <= z), (z.toNat : ZMod p) = z
  | (n : Nat), _h => by simp only [Int.cast_natCast, Int.toNat_natCast]
  | Int.negSucc n, h => by simp at h

/--
theorem `val_injective` / 定理 `val_injective`

English:
theorem val_injective
  given: (n : Nat) [NeZero n]
  statement: Function.Injective (val : ZMod n -> Nat)
  proof: by
  cases n
  · cases NeZero.ne 0 rfl
  intro a b h
  dsimp [ZMod]
  ext
  exact h

中文:
定理 val_injective
  条件: (n : 自然数) [NeZero n]
  结论: Function.Injective (val : ZMod n -> 自然数)
  证明: by
  cases n
  · cases NeZero.ne 0 rfl
  intro a b h
  dsimp [ZMod]
  ext
  exact h

Depends on / 依赖: NeZero, NeZero.ne
-/
theorem val_injective (n : Nat) [NeZero n] : Function.Injective (val : ZMod n -> Nat) := by
  cases n
  · cases NeZero.ne 0 rfl
  intro a b h
  dsimp [ZMod]
  ext
  exact h

/--
theorem `val_one_eq_one_mod` / 定理 `val_one_eq_one_mod`

English:
theorem val_one_eq_one_mod
  given: (n : Nat)
  statement: (1 : ZMod n).val = 1 % n
  proof: by
  rw [← Nat.cast_one]; rw [val_natCast]

中文:
定理 val_one_eq_one_mod
  条件: (n : 自然数)
  结论: (1 : ZMod n).val = 1 % n
  证明: by
  rw [← Nat.cast_one]; rw [val_natCast]

Depends on / 依赖: Nat.cast_one, cast_one, val_natCast
-/
theorem val_one_eq_one_mod (n : Nat) : (1 : ZMod n).val = 1 % n := by
  rw [← Nat.cast_one]; rw [val_natCast]

/--
theorem `val_two_eq_two_mod` / 定理 `val_two_eq_two_mod`

English:
theorem val_two_eq_two_mod
  given: (n : Nat)
  statement: (2 : ZMod n).val = 2 % n
  proof: by
  rw [← Nat.cast_two]; rw [val_natCast]

中文:
定理 val_two_eq_two_mod
  条件: (n : 自然数)
  结论: (2 : ZMod n).val = 2 % n
  证明: by
  rw [← Nat.cast_two]; rw [val_natCast]

Depends on / 依赖: Nat.cast_two, cast_two, val_natCast
-/
theorem val_two_eq_two_mod (n : Nat) : (2 : ZMod n).val = 2 % n := by
  rw [← Nat.cast_two]; rw [val_natCast]

/--
theorem `val_one` / 定理 `val_one`

English:
theorem val_one
  given: (n : Nat) [Fact (1 < n)]
  statement: (1 : ZMod n).val = 1
  proof: by
  rw [val_one_eq_one_mod]
  exact Nat.mod_eq_of_lt Fact.out

中文:
定理 val_one
  条件: (n : 自然数) [Fact (1 < n)]
  结论: (1 : ZMod n).val = 1
  证明: by
  rw [val_one_eq_one_mod]
  exact Nat.mod_eq_of_lt Fact.out

Depends on / 依赖: Fact.out, Nat.mod_eq_of_lt, mod_eq_of_lt, val_one_eq_one_mod
-/
theorem val_one (n : Nat) [Fact (1 < n)] : (1 : ZMod n).val = 1 := by
  rw [val_one_eq_one_mod]
  exact Nat.mod_eq_of_lt Fact.out

/--
lemma `val_one''` / 引理 `val_one''`

English:
lemma val_one''
  statement: forall {n}, n != 1 -> (1 : ZMod n).val = 1
  proof: ⟨by simp⟩
    ZMod.val_one _

中文:
引理 val_one''
  结论: 对任意 {n}, n != 1 -> (1 : ZMod n).val = 1
  证明: ⟨by simp⟩
    ZMod.val_one _
-/
lemma val_one'' : forall {n}, n != 1 -> (1 : ZMod n).val = 1
  | 0, _ => rfl
  | 1, hn => by cases hn rfl
  | n + 2, _ =>
    haveI : Fact (1 < n + 2) := ⟨by simp⟩
    ZMod.val_one _

/--
theorem `val_add` / 定理 `val_add`

English:
theorem val_add
  given: {n : Nat} [NeZero n] (a b : ZMod n)
  statement: (a + b).val = (a.val + b.val) % n
  proof: by
  cases n
  · cases NeZero.ne 0 rfl
  · apply Fin.val_add

中文:
定理 val_add
  条件: {n : 自然数} [NeZero n] (a b : ZMod n)
  结论: (a + b).val = (a.val + b.val) % n
  证明: by
  cases n
  · cases NeZero.ne 0 rfl
  · apply Fin.val_add

Depends on / 依赖: Fin.val_add, NeZero, NeZero.ne, val_add
-/
theorem val_add {n : Nat} [NeZero n] (a b : ZMod n) : (a + b).val = (a.val + b.val) % n := by
  cases n
  · cases NeZero.ne 0 rfl
  · apply Fin.val_add

/--
theorem `val_add_of_lt` / 定理 `val_add_of_lt`

English:
theorem val_add_of_lt
  given: {n : Nat} {a b : ZMod n} (h : a.val + b.val < n)
  proof: by
  have : NeZero n := by constructor; rintro rfl; simp at h
  rw [ZMod.val_add]; rw [Nat.mod_eq_of_lt h]

中文:
定理 val_add_of_lt
  条件: {n : 自然数} {a b : ZMod n} (h : a.val + b.val < n)
  证明: by
  have : NeZero n := by constructor; rintro rfl; simp at h
  rw [ZMod.val_add]; rw [Nat.mod_eq_of_lt h]

Depends on / 依赖: Nat.mod_eq_of_lt, NeZero, ZMod.val_add, mod_eq_of_lt, val_add
-/
theorem val_add_of_lt {n : Nat} {a b : ZMod n} (h : a.val + b.val < n) :
    (a + b).val = a.val + b.val := by
  have : NeZero n := by constructor; rintro rfl; simp at h
  rw [ZMod.val_add]; rw [Nat.mod_eq_of_lt h]

/--
theorem `val_add_val_of_le` / 定理 `val_add_val_of_le`

English:
theorem val_add_val_of_le
  given: {n : Nat} [NeZero n] {a b : ZMod n} (h : n <= a.val + b.val)
  proof: by
  rw [val_add]; rw [Nat.add_mod_add_of_le_add_mod]; rw [Nat.mod_eq_of_lt (val_lt _)]; rw [Nat.mod_eq_of_lt (val_lt _)]
  rwa [Nat.mod_eq_of_lt (val_lt _), Nat.mod_eq_of_lt (val_lt _)]

中文:
定理 val_add_val_of_le
  条件: {n : 自然数} [NeZero n] {a b : ZMod n} (h : n <= a.val + b.val)
  证明: by
  rw [val_add]; rw [Nat.add_mod_add_of_le_add_mod]; rw [Nat.mod_eq_of_lt (val_lt _)]; rw [Nat.mod_eq_of_lt (val_lt _)]
  rwa [Nat.mod_eq_of_lt (val_lt _), Nat.mod_eq_of_lt (val_lt _)]

Depends on / 依赖: Nat.add_mod_add_of_le_add_mod, Nat.mod_eq_of_lt, add_mod_add_of_le_add_mod, mod_eq_of_lt, val_add, val_lt
-/
theorem val_add_val_of_le {n : Nat} [NeZero n] {a b : ZMod n} (h : n <= a.val + b.val) :
    a.val + b.val = (a + b).val + n := by
  rw [val_add]; rw [Nat.add_mod_add_of_le_add_mod]; rw [Nat.mod_eq_of_lt (val_lt _)]; rw [Nat.mod_eq_of_lt (val_lt _)]
  rwa [Nat.mod_eq_of_lt (val_lt _), Nat.mod_eq_of_lt (val_lt _)]

/--
theorem `val_add_of_le` / 定理 `val_add_of_le`

English:
theorem val_add_of_le
  given: {n : Nat} [NeZero n] {a b : ZMod n} (h : n <= a.val + b.val)
  proof: by
  rw [val_add_val_of_le h]
  exact eq_tsub_of_add_eq rfl

中文:
定理 val_add_of_le
  条件: {n : 自然数} [NeZero n] {a b : ZMod n} (h : n <= a.val + b.val)
  证明: by
  rw [val_add_val_of_le h]
  exact eq_tsub_of_add_eq rfl

Depends on / 依赖: eq_tsub_of_add_eq, val_add_val_of_le
-/
theorem val_add_of_le {n : Nat} [NeZero n] {a b : ZMod n} (h : n <= a.val + b.val) :
    (a + b).val = a.val + b.val - n := by
  rw [val_add_val_of_le h]
  exact eq_tsub_of_add_eq rfl

/--
theorem `val_add_le` / 定理 `val_add_le`

English:
theorem val_add_le
  given: {n : Nat} (a b : ZMod n)
  statement: (a + b).val <= a.val + b.val
  proof: by
  cases n
  · simpa [ZMod.val] using! Int.natAbs_add_le _ _
  · simpa [ZMod.val_add] using! Nat.mod_le _ _

中文:
定理 val_add_le
  条件: {n : 自然数} (a b : ZMod n)
  结论: (a + b).val <= a.val + b.val
  证明: by
  cases n
  · simpa [ZMod.val] using! Int.natAbs_add_le _ _
  · simpa [ZMod.val_add] using! Nat.mod_le _ _

Depends on / 依赖: Int.natAbs_add_le, Nat.mod_le, ZMod.val, ZMod.val_add, mod_le, natAbs_add_le, val_add
-/
theorem val_add_le {n : Nat} (a b : ZMod n) : (a + b).val <= a.val + b.val := by
  cases n
  · simpa [ZMod.val] using! Int.natAbs_add_le _ _
  · simpa [ZMod.val_add] using! Nat.mod_le _ _

/--
theorem `val_mul` / 定理 `val_mul`

English:
theorem val_mul
  given: {n : Nat} (a b : ZMod n)
  statement: (a * b).val = a.val * b.val % n
  proof: by
  cases n
  · rw [Nat.mod_zero]
    apply Int.natAbs_mul
  · apply Fin.val_mul

中文:
定理 val_mul
  条件: {n : 自然数} (a b : ZMod n)
  结论: (a * b).val = a.val * b.val % n
  证明: by
  cases n
  · rw [Nat.mod_zero]
    apply Int.natAbs_mul
  · apply Fin.val_mul

Depends on / 依赖: Fin.val_mul, Int.natAbs_mul, Nat.mod_zero, mod_zero, natAbs_mul, val_mul
-/
theorem val_mul {n : Nat} (a b : ZMod n) : (a * b).val = a.val * b.val % n := by
  cases n
  · rw [Nat.mod_zero]
    apply Int.natAbs_mul
  · apply Fin.val_mul

/--
theorem `val_mul_le` / 定理 `val_mul_le`

English:
theorem val_mul_le
  given: {n : Nat} (a b : ZMod n)
  statement: (a * b).val <= a.val * b.val
  proof: by
  rw [val_mul]
  apply Nat.mod_le

中文:
定理 val_mul_le
  条件: {n : 自然数} (a b : ZMod n)
  结论: (a * b).val <= a.val * b.val
  证明: by
  rw [val_mul]
  apply Nat.mod_le

Depends on / 依赖: Nat.mod_le, mod_le, val_mul
-/
theorem val_mul_le {n : Nat} (a b : ZMod n) : (a * b).val <= a.val * b.val := by
  rw [val_mul]
  apply Nat.mod_le

/--
theorem `val_mul_of_lt` / 定理 `val_mul_of_lt`

English:
theorem val_mul_of_lt
  given: {n : Nat} {a b : ZMod n} (h : a.val * b.val < n)
  proof: by
  rw [val_mul]
  apply Nat.mod_eq_of_lt h

中文:
定理 val_mul_of_lt
  条件: {n : 自然数} {a b : ZMod n} (h : a.val * b.val < n)
  证明: by
  rw [val_mul]
  apply Nat.mod_eq_of_lt h

Depends on / 依赖: Nat.mod_eq_of_lt, mod_eq_of_lt, val_mul
-/
theorem val_mul_of_lt {n : Nat} {a b : ZMod n} (h : a.val * b.val < n) :
    (a * b).val = a.val * b.val := by
  rw [val_mul]
  apply Nat.mod_eq_of_lt h

/--
theorem `val_mul_iff_lt` / 定理 `val_mul_iff_lt`

English:
theorem val_mul_iff_lt
  given: {n : Nat} [NeZero n] (a b : ZMod n)
  proof: by
  constructor <;> intro h
  · rw [← h]; apply ZMod.val_lt
  · apply ZMod.val_mul_of_lt h

中文:
定理 val_mul_iff_lt
  条件: {n : 自然数} [NeZero n] (a b : ZMod n)
  证明: by
  constructor <;> intro h
  · rw [← h]; apply ZMod.val_lt
  · apply ZMod.val_mul_of_lt h

Depends on / 依赖: ZMod.val_lt, ZMod.val_mul_of_lt, val_lt, val_mul_of_lt
-/
theorem val_mul_iff_lt {n : Nat} [NeZero n] (a b : ZMod n) :
    (a * b).val = a.val * b.val ↔ a.val * b.val < n := by
  constructor <;> intro h
  · rw [← h]; apply ZMod.val_lt
  · apply ZMod.val_mul_of_lt h

/--
Instance `nontrivial` / 实例 `nontrivial`

English:
instance nontrivial
  signature: (n : Nat) [Fact (1 < n)]
  body: ⟨⟨0, 1, fun h =>
zero_ne_one
        calc
          0 = (0 : ZMod n).val := by rw [val_zero]
          _ = (1 : ZMod n).val := congr_arg ZMod.val h
          _ = 1 := val_one n
          ⟩⟩

中文:
实例 nontrivial
  签名: (n : 自然数) [Fact (1 < n)]
  定义体: ⟨⟨0, 1, fun h =>
zero_ne_one
        calc
          0 = (0 : ZMod n).val := by rw [val_zero]
          _ = (1 : ZMod n).val := congr_arg ZMod.val h
          _ = 1 := val_one n
          ⟩⟩

Depends on / 依赖: ZMod.val, congr_arg, val_one, val_zero, zero_ne_one
-/
instance nontrivial (n : Nat) [Fact (1 < n)] : Nontrivial (ZMod n) :=
  ⟨⟨0, 1, fun h =>
zero_ne_one
        calc
          0 = (0 : ZMod n).val := by rw [val_zero]
          _ = (1 : ZMod n).val := congr_arg ZMod.val h
          _ = 1 := val_one n
          ⟩⟩

/--
Instance `nontrivial'` / 实例 `nontrivial'`

English:
instance nontrivial'
  signature: : Nontrivial (ZMod 0)
  body: by
  delta ZMod; infer_instance

中文:
实例 nontrivial'
  签名: : Nontrivial (ZMod 0)
  定义体: by
  delta ZMod; infer_instance

Depends on / 依赖: infer_instance
-/
instance nontrivial' : Nontrivial (ZMod 0) := by
  delta ZMod; infer_instance

/--
lemma `one_eq_zero_iff` / 引理 `one_eq_zero_iff`

English:
lemma one_eq_zero_iff
  given: {n : Nat}
  statement: (1 : ZMod n) = 0 ↔ n = 1
  proof: by
  rw [← Nat.cast_one]; rw [natCast_eq_zero_iff]; rw [Nat.dvd_one]

中文:
引理 one_eq_zero_iff
  条件: {n : 自然数}
  结论: (1 : ZMod n) = 0 ↔ n = 1
  证明: by
  rw [← Nat.cast_one]; rw [natCast_eq_zero_iff]; rw [Nat.dvd_one]

Depends on / 依赖: Nat.cast_one, Nat.dvd_one, cast_one, dvd_one, natCast_eq_zero_iff
-/
lemma one_eq_zero_iff {n : Nat} : (1 : ZMod n) = 0 ↔ n = 1 := by
  rw [← Nat.cast_one]; rw [natCast_eq_zero_iff]; rw [Nat.dvd_one]

/--
Definition of `inv` / `inv` 的定义

English:
definition inv
  signature: : forall n : Nat, ZMod n -> ZMod n

中文:
定义 inv
  签名: : 对任意 n : 自然数, ZMod n -> ZMod n
-/
def inv : forall n : Nat, ZMod n -> ZMod n
  | 0, i => Int.sign i
  | n + 1, i => Nat.gcdA i.val (n + 1)

instance (n : Nat) : Inv (ZMod n) :=
  ⟨inv n⟩

/--
theorem `inv_zero` / 定理 `inv_zero`

English:
theorem inv_zero
  statement: forall n : Nat, (0 : ZMod n)⁻¹ = 0

中文:
定理 inv_zero
  结论: 对任意 n : 自然数, (0 : ZMod n)⁻¹ = 0
-/
theorem inv_zero : forall n : Nat, (0 : ZMod n)⁻¹ = 0
  | 0 => Int.sign_zero
  | n + 1 =>
    show (Nat.gcdA _ (n + 1) : ZMod (n + 1)) = 0 by
      simp [Nat.gcdA, Nat.xgcd, Nat.xgcdAux, Nat.strongRec_eq]

/--
theorem `mul_inv_eq_gcd` / 定理 `mul_inv_eq_gcd`

English:
theorem mul_inv_eq_gcd
  given: {n : Nat} (a : ZMod n)
  statement: a * a⁻¹ = Nat.gcd a.val n
  proof: by
  rcases n with - | n
  · dsimp [ZMod] at a ⊢
    calc
      _ = a * Int.sign a := rfl
      _ = a.natAbs := by rw [Int.mul_sign_self]
      _ = a.natAbs.gcd 0 := by rw [Nat.gcd_zero_right]
  · calc
      a * a⁻¹ = a * a⁻¹ + n.succ * Nat.gcdB (val a) n.succ := by
        rw [natCast_self]; rw [ze

中文:
定理 mul_inv_eq_gcd
  条件: {n : 自然数} (a : ZMod n)
  结论: a * a⁻¹ = 自然数.gcd a.val n
  证明: by
  rcases n with - | n
  · dsimp [ZMod] at a ⊢
    calc
      _ = a * Int.sign a := rfl
      _ = a.natAbs := by rw [Int.mul_sign_self]
      _ = a.natAbs.gcd 0 := by rw [Nat.gcd_zero_right]
  · calc
      a * a⁻¹ = a * a⁻¹ + n.succ * Nat.gcdB (val a) n.succ := by
        rw [natCast_self]; rw [ze

Depends on / 依赖: Int.mul_sign_self, Int.sign, Nat.gcd, Nat.gcdA, Nat.gcdB, Nat.gcd_eq_gcd_ab, Nat.gcd_zero_right, a.natAbs, a.natAbs.gcd, a.val, add_zero, gcd_eq_gcd_ab, gcd_zero_right, mul_sign_self, n.succ, natAbs, natCast_self, natCast_zmod_val, zero_mul
-/
theorem mul_inv_eq_gcd {n : Nat} (a : ZMod n) : a * a⁻¹ = Nat.gcd a.val n := by
  rcases n with - | n
  · dsimp [ZMod] at a ⊢
    calc
      _ = a * Int.sign a := rfl
      _ = a.natAbs := by rw [Int.mul_sign_self]
      _ = a.natAbs.gcd 0 := by rw [Nat.gcd_zero_right]
  · calc
      a * a⁻¹ = a * a⁻¹ + n.succ * Nat.gcdB (val a) n.succ := by
        rw [natCast_self]; rw [zero_mul]; rw [add_zero]
      _ = ↑(↑a.val * Nat.gcdA (val a) n.succ + n.succ * Nat.gcdB (val a) n.succ) := by
        push_cast
        rw [natCast_zmod_val]
        rfl
      _ = Nat.gcd a.val n.succ := by rw [← Nat.gcd_eq_gcd_ab a.val n.succ]; rfl

/--
lemma `inv_one` / 引理 `inv_one`

English:
lemma inv_one
  given: (n : Nat)
  statement: (1⁻¹ : ZMod n) = 1
  proof: by
  obtain rfl | hn := eq_or_ne n 1
  · exact Subsingleton.elim _ _
  · simpa [ZMod.val_one'' hn] using mul_inv_eq_gcd (1 : ZMod n)

@[simp, grind =]

中文:
引理 inv_one
  条件: (n : 自然数)
  结论: (1⁻¹ : ZMod n) = 1
  证明: by
  obtain rfl | hn := eq_or_ne n 1
  · exact Subsingleton.elim _ _
  · simpa [ZMod.val_one'' hn] using mul_inv_eq_gcd (1 : ZMod n)

@[simp, grind =]
-/
@[simp] protected lemma inv_one (n : Nat) : (1⁻¹ : ZMod n) = 1 := by
  obtain rfl | hn := eq_or_ne n 1
  · exact Subsingleton.elim _ _
  · simpa [ZMod.val_one'' hn] using mul_inv_eq_gcd (1 : ZMod n)

@[simp, grind =]
/--
theorem `natCast_mod` / 定理 `natCast_mod`

English:
theorem natCast_mod
  given: (a : Nat) (n : Nat)
  statement: ((a % n : Nat) : ZMod n) = a
  proof: (CharP.cast_eq_mod (ZMod n) n a).symm

中文:
定理 natCast_mod
  条件: (a : 自然数) (n : 自然数)
  结论: ((a % n : 自然数) : ZMod n) = a
  证明: (CharP.cast_eq_mod (ZMod n) n a).symm

Depends on / 依赖: CharP.cast_eq_mod, cast_eq_mod
-/
theorem natCast_mod (a : Nat) (n : Nat) : ((a % n : Nat) : ZMod n) = a :=
  (CharP.cast_eq_mod (ZMod n) n a).symm

/--
theorem `intCast_eq_zero_iff_even` / 定理 `intCast_eq_zero_iff_even`

English:
theorem intCast_eq_zero_iff_even
  given: {n : Int}
  statement: (n : ZMod 2) = 0 ↔ Even n
  proof: (CharP.intCast_eq_zero_iff (ZMod 2) 2 n).trans even_iff_two_dvd.symm

alias ⟨_, _root_.Even.intCast_zmod_two⟩ := intCast_eq_zero_iff_even

中文:
定理 intCast_eq_zero_iff_even
  条件: {n : 整数}
  结论: (n : ZMod 2) = 0 ↔ Even n
  证明: (CharP.intCast_eq_zero_iff (ZMod 2) 2 n).trans even_iff_two_dvd.symm

alias ⟨_, _root_.Even.intCast_zmod_two⟩ := intCast_eq_zero_iff_even

Depends on / 依赖: CharP.intCast_eq_zero_iff, even_iff_two_dvd, even_iff_two_dvd.symm, intCast_eq_zero_iff
-/
theorem intCast_eq_zero_iff_even {n : Int} : (n : ZMod 2) = 0 ↔ Even n :=
  (CharP.intCast_eq_zero_iff (ZMod 2) 2 n).trans even_iff_two_dvd.symm

alias ⟨_, _root_.Even.intCast_zmod_two⟩ := intCast_eq_zero_iff_even

/--
theorem `natCast_eq_zero_iff_even` / 定理 `natCast_eq_zero_iff_even`

English:
theorem natCast_eq_zero_iff_even
  given: {n : Nat}
  statement: (n : ZMod 2) = 0 ↔ Even n
  proof: mod_cast intCast_eq_zero_iff_even (n := n)

alias ⟨_, _root_.Even.natCast_zmod_two⟩ := natCast_eq_zero_iff_even

中文:
定理 natCast_eq_zero_iff_even
  条件: {n : 自然数}
  结论: (n : ZMod 2) = 0 ↔ Even n
  证明: mod_cast intCast_eq_zero_iff_even (n := n)

alias ⟨_, _root_.Even.natCast_zmod_two⟩ := natCast_eq_zero_iff_even

Depends on / 依赖: intCast_eq_zero_iff_even, mod_cast
-/
theorem natCast_eq_zero_iff_even {n : Nat} : (n : ZMod 2) = 0 ↔ Even n :=
  mod_cast intCast_eq_zero_iff_even (n := n)

alias ⟨_, _root_.Even.natCast_zmod_two⟩ := natCast_eq_zero_iff_even

/--
theorem `intCast_eq_one_iff_odd` / 定理 `intCast_eq_one_iff_odd`

English:
theorem intCast_eq_one_iff_odd
  given: {n : Int}
  statement: (n : ZMod 2) = 1 ↔ Odd n
  proof: by
  rw [← Int.cast_one]; rw [ZMod.intCast_eq_intCast_iff]; rw [Int.odd_iff]; rw [Int.ModEq]
  simp

alias ⟨_, _root_.Odd.intCast_zmod_two⟩ := intCast_eq_one_iff_odd

中文:
定理 intCast_eq_one_iff_odd
  条件: {n : 整数}
  结论: (n : ZMod 2) = 1 ↔ Odd n
  证明: by
  rw [← Int.cast_one]; rw [ZMod.intCast_eq_intCast_iff]; rw [Int.odd_iff]; rw [Int.ModEq]
  simp

alias ⟨_, _root_.Odd.intCast_zmod_two⟩ := intCast_eq_one_iff_odd

Depends on / 依赖: Int.ModEq, Int.cast_one, Int.odd_iff, ZMod.intCast_eq_intCast_iff, cast_one, intCast_eq_intCast_iff, odd_iff
-/
theorem intCast_eq_one_iff_odd {n : Int} : (n : ZMod 2) = 1 ↔ Odd n := by
  rw [← Int.cast_one]; rw [ZMod.intCast_eq_intCast_iff]; rw [Int.odd_iff]; rw [Int.ModEq]
  simp

alias ⟨_, _root_.Odd.intCast_zmod_two⟩ := intCast_eq_one_iff_odd

/--
theorem `natCast_eq_one_iff_odd` / 定理 `natCast_eq_one_iff_odd`

English:
theorem natCast_eq_one_iff_odd
  given: {n : Nat}
  statement: (n : ZMod 2) = 1 ↔ Odd n
  proof: mod_cast intCast_eq_one_iff_odd (n := n)

alias ⟨_, _root_.Odd.natCast_zmod_two⟩ := natCast_eq_one_iff_odd

中文:
定理 natCast_eq_one_iff_odd
  条件: {n : 自然数}
  结论: (n : ZMod 2) = 1 ↔ Odd n
  证明: mod_cast intCast_eq_one_iff_odd (n := n)

alias ⟨_, _root_.Odd.natCast_zmod_two⟩ := natCast_eq_one_iff_odd

Depends on / 依赖: intCast_eq_one_iff_odd, mod_cast
-/
theorem natCast_eq_one_iff_odd {n : Nat} : (n : ZMod 2) = 1 ↔ Odd n :=
  mod_cast intCast_eq_one_iff_odd (n := n)

alias ⟨_, _root_.Odd.natCast_zmod_two⟩ := natCast_eq_one_iff_odd

/--
theorem `natCast_ne_zero_iff_odd` / 定理 `natCast_ne_zero_iff_odd`

English:
theorem natCast_ne_zero_iff_odd
  given: {n : Nat}
  statement: (n : ZMod 2) != 0 ↔ Odd n
  proof: by
  simp [natCast_eq_zero_iff_even]

中文:
定理 natCast_ne_zero_iff_odd
  条件: {n : 自然数}
  结论: (n : ZMod 2) != 0 ↔ Odd n
  证明: by
  simp [natCast_eq_zero_iff_even]

Depends on / 依赖: natCast_eq_zero_iff_even
-/
theorem natCast_ne_zero_iff_odd {n : Nat} : (n : ZMod 2) != 0 ↔ Odd n := by
  simp [natCast_eq_zero_iff_even]

/--
theorem `coe_mul_inv_eq_one` / 定理 `coe_mul_inv_eq_one`

English:
theorem coe_mul_inv_eq_one
  given: {n : Nat} (x : Nat) (h : Nat.Coprime x n)
  proof: by
  rw [Nat.Coprime]; rw [Nat.gcd_comm]; rw [Nat.gcd_rec] at h
  rw [mul_inv_eq_gcd]; rw [val_natCast]; rw [h]; rw [Nat.cast_one]

中文:
定理 coe_mul_inv_eq_one
  条件: {n : 自然数} (x : 自然数) (h : 自然数.Coprime x n)
  证明: by
  rw [Nat.Coprime]; rw [Nat.gcd_comm]; rw [Nat.gcd_rec] at h
  rw [mul_inv_eq_gcd]; rw [val_natCast]; rw [h]; rw [Nat.cast_one]

Depends on / 依赖: Coprime, Nat.Coprime, Nat.cast_one, Nat.gcd_comm, Nat.gcd_rec, cast_one, gcd_comm, gcd_rec, mul_inv_eq_gcd, val_natCast
-/
theorem coe_mul_inv_eq_one {n : Nat} (x : Nat) (h : Nat.Coprime x n) :
    ((x : ZMod n) * (x : ZMod n)⁻¹) = 1 := by
  rw [Nat.Coprime]; rw [Nat.gcd_comm]; rw [Nat.gcd_rec] at h
  rw [mul_inv_eq_gcd]; rw [val_natCast]; rw [h]; rw [Nat.cast_one]

/--
lemma `mul_val_inv` / 引理 `mul_val_inv`

English:
lemma mul_val_inv
  given: (hmn : m.Coprime n)
  statement: (m * (m⁻¹ : ZMod n).val : ZMod n) = 1
  proof: by
  obtain rfl | hn := eq_or_ne n 0
  · simp [m.coprime_zero_right.1 hmn]
  have : NeZero n := ⟨hn⟩
  rw [ZMod.natCast_zmod_val]; rw [ZMod.coe_mul_inv_eq_one _ hmn]

中文:
引理 mul_val_inv
  条件: (hmn : m.Coprime n)
  结论: (m * (m⁻¹ : ZMod n).val : ZMod n) = 1
  证明: by
  obtain rfl | hn := eq_or_ne n 0
  · simp [m.coprime_zero_right.1 hmn]
  have : NeZero n := ⟨hn⟩
  rw [ZMod.natCast_zmod_val]; rw [ZMod.coe_mul_inv_eq_one _ hmn]

Depends on / 依赖: NeZero, ZMod.coe_mul_inv_eq_one, ZMod.natCast_zmod_val, coe_mul_inv_eq_one, coprime_zero_right, eq_or_ne, m.coprime_zero_right, natCast_zmod_val
-/
lemma mul_val_inv (hmn : m.Coprime n) : (m * (m⁻¹ : ZMod n).val : ZMod n) = 1 := by
  obtain rfl | hn := eq_or_ne n 0
  · simp [m.coprime_zero_right.1 hmn]
  have : NeZero n := ⟨hn⟩
  rw [ZMod.natCast_zmod_val]; rw [ZMod.coe_mul_inv_eq_one _ hmn]

/--
lemma `val_inv_mul` / 引理 `val_inv_mul`

English:
lemma val_inv_mul
  given: (hmn : m.Coprime n)
  statement: ((m⁻¹ : ZMod n).val * m : ZMod n) = 1
  proof: by
  rw [mul_comm]; rw [mul_val_inv hmn]

中文:
引理 val_inv_mul
  条件: (hmn : m.Coprime n)
  结论: ((m⁻¹ : ZMod n).val * m : ZMod n) = 1
  证明: by
  rw [mul_comm]; rw [mul_val_inv hmn]

Depends on / 依赖: mul_comm, mul_val_inv
-/
lemma val_inv_mul (hmn : m.Coprime n) : ((m⁻¹ : ZMod n).val * m : ZMod n) = 1 := by
  rw [mul_comm]; rw [mul_val_inv hmn]

/--
Definition of `unitOfCoprime` / `unitOfCoprime` 的定义

English:
definition unitOfCoprime
  signature: {n : Nat} (x : Nat) (h : Nat.Coprime x n)
  body: ⟨x, x⁻¹, coe_mul_inv_eq_one x h, by rw [mul_comm, coe_mul_inv_eq_one x h]⟩

@[simp]

中文:
定义 unitOfCoprime
  签名: {n : 自然数} (x : 自然数) (h : 自然数.Coprime x n)
  定义体: ⟨x, x⁻¹, coe_mul_inv_eq_one x h, by rw [mul_comm, coe_mul_inv_eq_one x h]⟩

@[simp]

Depends on / 依赖: coe_mul_inv_eq_one, mul_comm
-/
def unitOfCoprime {n : Nat} (x : Nat) (h : Nat.Coprime x n) : (ZMod n)ˣ :=
  ⟨x, x⁻¹, coe_mul_inv_eq_one x h, by rw [mul_comm, coe_mul_inv_eq_one x h]⟩

@[simp]
/--
theorem `coe_unitOfCoprime` / 定理 `coe_unitOfCoprime`

English:
theorem coe_unitOfCoprime
  given: {n : Nat} (x : Nat) (h : Nat.Coprime x n)
  proof: rfl

中文:
定理 coe_unitOfCoprime
  条件: {n : 自然数} (x : 自然数) (h : 自然数.Coprime x n)
  证明: rfl
-/
theorem coe_unitOfCoprime {n : Nat} (x : Nat) (h : Nat.Coprime x n) :
    (unitOfCoprime x h : ZMod n) = x :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `val_coe_unit_coprime` / 定理 `val_coe_unit_coprime`

English:
theorem val_coe_unit_coprime
  given: {n : Nat} (u : (ZMod n)ˣ)
  statement: Nat.Coprime (u : ZMod n).val n
  proof: by
  rcases n with - | n
  · rcases Int.units_eq_one_or u with (rfl | rfl) <;> simp
  apply Nat.coprime_of_mul_modEq_one ((u⁻¹ : Units (ZMod (n + 1))) : ZMod (n + 1)).val
  have := Units.ext_iff.1 (mul_inv_cancel u)
  rw [Units.val_one] at this
  rw [← natCast_eq_natCast_iff]; rw [Nat.cast_one]; rw 

中文:
定理 val_coe_unit_coprime
  条件: {n : 自然数} (u : (ZMod n)ˣ)
  结论: 自然数.Coprime (u : ZMod n).val n
  证明: by
  rcases n with - | n
  · rcases Int.units_eq_one_or u with (rfl | rfl) <;> simp
  apply Nat.coprime_of_mul_modEq_one ((u⁻¹ : Units (ZMod (n + 1))) : ZMod (n + 1)).val
  have := Units.ext_iff.1 (mul_inv_cancel u)
  rw [Units.val_one] at this
  rw [← natCast_eq_natCast_iff]; rw [Nat.cast_one]; rw 

Depends on / 依赖: Int.units_eq_one_or, Nat.cast_one, Nat.coprime_of_mul_modEq_one, Units.ext_iff, Units.val_mul, Units.val_one, cast_one, coprime_of_mul_modEq_one, ext_iff, mul_inv_cancel, natCast_eq_natCast_iff, natCast_mod, natCast_zmod_val, units_eq_one_or, val_mul, val_one
-/
theorem val_coe_unit_coprime {n : Nat} (u : (ZMod n)ˣ) : Nat.Coprime (u : ZMod n).val n := by
  rcases n with - | n
  · rcases Int.units_eq_one_or u with (rfl | rfl) <;> simp
  apply Nat.coprime_of_mul_modEq_one ((u⁻¹ : Units (ZMod (n + 1))) : ZMod (n + 1)).val
  have := Units.ext_iff.1 (mul_inv_cancel u)
  rw [Units.val_one] at this
  rw [← natCast_eq_natCast_iff]; rw [Nat.cast_one]; rw [← this]; clear this
  rw [← natCast_zmod_val ((u * u⁻¹ : Units (ZMod (n + 1))) : ZMod (n + 1))]
  rw [Units.val_mul]; rw [val_mul]; rw [natCast_mod]

/--
lemma `isUnit_iff_coprime` / 引理 `isUnit_iff_coprime`

English:
lemma isUnit_iff_coprime
  given: (m n : Nat)
  statement: IsUnit (m : ZMod n) ↔ m.Coprime n
  proof: by
  refine ⟨fun H => ?_, fun H => (unitOfCoprime m H).isUnit⟩
  have H' := val_coe_unit_coprime H.unit
  rw [IsUnit.unit_spec]; rw [val_natCast]; rw [Nat.coprime_iff_gcd_eq_one] at H'
  rw [Nat.coprime_iff_gcd_eq_one]; rw [Nat.gcd_comm]; rw [← H']
  exact Nat.gcd_rec n m

@[simp]

中文:
引理 isUnit_iff_coprime
  条件: (m n : 自然数)
  结论: IsUnit (m : ZMod n) ↔ m.Coprime n
  证明: by
  refine ⟨fun H => ?_, fun H => (unitOfCoprime m H).isUnit⟩
  have H' := val_coe_unit_coprime H.unit
  rw [IsUnit.unit_spec]; rw [val_natCast]; rw [Nat.coprime_iff_gcd_eq_one] at H'
  rw [Nat.coprime_iff_gcd_eq_one]; rw [Nat.gcd_comm]; rw [← H']
  exact Nat.gcd_rec n m

@[simp]

Depends on / 依赖: H.unit, IsUnit, IsUnit.unit_spec, Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm, Nat.gcd_rec, coprime_iff_gcd_eq_one, gcd_comm, gcd_rec, isUnit, unitOfCoprime, unit_spec, val_coe_unit_coprime, val_natCast
-/
lemma isUnit_iff_coprime (m n : Nat) : IsUnit (m : ZMod n) ↔ m.Coprime n := by
  refine ⟨fun H => ?_, fun H => (unitOfCoprime m H).isUnit⟩
  have H' := val_coe_unit_coprime H.unit
  rw [IsUnit.unit_spec]; rw [val_natCast]; rw [Nat.coprime_iff_gcd_eq_one] at H'
  rw [Nat.coprime_iff_gcd_eq_one]; rw [Nat.gcd_comm]; rw [← H']
  exact Nat.gcd_rec n m

@[simp]
/--
lemma `coprime_mod_iff_coprime` / 引理 `coprime_mod_iff_coprime`

English:
lemma coprime_mod_iff_coprime
  given: (m n : Nat)
  statement: (m % n).Coprime n ↔ m.Coprime n
  proof: by
  suffices (m % n).gcd n = m.gcd n by grind
  exact Nat.ModEq.gcd_eq (by simp [Nat.ModEq])

中文:
引理 coprime_mod_iff_coprime
  条件: (m n : 自然数)
  结论: (m % n).Coprime n ↔ m.Coprime n
  证明: by
  suffices (m % n).gcd n = m.gcd n by grind
  exact Nat.ModEq.gcd_eq (by simp [Nat.ModEq])

Depends on / 依赖: Nat.ModEq, Nat.ModEq.gcd_eq, Set.mem_univ, Set.univ, gcd_eq, m.gcd, mem_univ
-/
lemma coprime_mod_iff_coprime (m n : Nat) : (m % n).Coprime n ↔ m.Coprime n := by
  suffices (m % n).gcd n = m.gcd n by grind
  exact Nat.ModEq.gcd_eq (by simp [Nat.ModEq])

/--
lemma `isUnit_prime_iff_not_dvd` / 引理 `isUnit_prime_iff_not_dvd`

English:
lemma isUnit_prime_iff_not_dvd
  given: {n p : Nat} (hp : p.Prime)
  statement: IsUnit (p : ZMod n) ↔ ¬p ∣ n
  proof: by
  rw [isUnit_iff_coprime]; rw [Nat.Prime.coprime_iff_not_dvd hp]

中文:
引理 isUnit_prime_iff_not_dvd
  条件: {n p : 自然数} (hp : p.Prime)
  结论: IsUnit (p : ZMod n) ↔ ¬p ∣ n
  证明: by
  rw [isUnit_iff_coprime]; rw [Nat.Prime.coprime_iff_not_dvd hp]

Depends on / 依赖: Nat.Prime.coprime_iff_not_dvd, coprime_iff_not_dvd, isUnit_iff_coprime
-/
lemma isUnit_prime_iff_not_dvd {n p : Nat} (hp : p.Prime) : IsUnit (p : ZMod n) ↔ ¬p ∣ n := by
  rw [isUnit_iff_coprime]; rw [Nat.Prime.coprime_iff_not_dvd hp]

/--
lemma `isUnit_prime_of_not_dvd` / 引理 `isUnit_prime_of_not_dvd`

English:
lemma isUnit_prime_of_not_dvd
  given: {n p : Nat} (hp : p.Prime) (h : ¬ p ∣ n)
  statement: IsUnit (p : ZMod n)
  proof: (isUnit_prime_iff_not_dvd hp).mpr h

中文:
引理 isUnit_prime_of_not_dvd
  条件: {n p : 自然数} (hp : p.Prime) (h : ¬ p ∣ n)
  结论: IsUnit (p : ZMod n)
  证明: (isUnit_prime_iff_not_dvd hp).mpr h

Depends on / 依赖: isUnit_prime_iff_not_dvd
-/
lemma isUnit_prime_of_not_dvd {n p : Nat} (hp : p.Prime) (h : ¬ p ∣ n) : IsUnit (p : ZMod n) :=
  (isUnit_prime_iff_not_dvd hp).mpr h

/--
theorem `isUnit_natCast_iff_not_dvd_pow` / 定理 `isUnit_natCast_iff_not_dvd_pow`

English:
theorem isUnit_natCast_iff_not_dvd_pow
  given: {p d a : Nat} (hp : p.Prime) (hd : 0 < d)
  proof: by
  rw [isUnit_iff_coprime]; rw [Nat.coprime_pow_right_iff hd]; rw [Nat.coprime_comm]; rw [hp.coprime_iff_not_dvd]

中文:
定理 isUnit_natCast_iff_not_dvd_pow
  条件: {p d a : 自然数} (hp : p.Prime) (hd : 0 < d)
  证明: by
  rw [isUnit_iff_coprime]; rw [Nat.coprime_pow_right_iff hd]; rw [Nat.coprime_comm]; rw [hp.coprime_iff_not_dvd]

Depends on / 依赖: Nat.coprime_comm, Nat.coprime_pow_right_iff, coprime_comm, coprime_iff_not_dvd, coprime_pow_right_iff, hp.coprime_iff_not_dvd, isUnit_iff_coprime
-/
theorem isUnit_natCast_iff_not_dvd_pow {p d a : Nat} (hp : p.Prime) (hd : 0 < d) :
    IsUnit (a : ZMod (p ^ d)) ↔ ¬ p ∣ a := by
  rw [isUnit_iff_coprime]; rw [Nat.coprime_pow_right_iff hd]; rw [Nat.coprime_comm]; rw [hp.coprime_iff_not_dvd]

/--
theorem `prime_natCast_not_isUnit_pow` / 定理 `prime_natCast_not_isUnit_pow`

English:
theorem prime_natCast_not_isUnit_pow
  given: {p d : Nat} (hp : p.Prime) (hd : 0 < d)
  proof: by
  simp [isUnit_prime_iff_not_dvd hp]
  lia

@[simp]

中文:
定理 prime_natCast_not_isUnit_pow
  条件: {p d : 自然数} (hp : p.Prime) (hd : 0 < d)
  证明: by
  simp [isUnit_prime_iff_not_dvd hp]
  lia

@[simp]

Depends on / 依赖: isUnit_prime_iff_not_dvd
-/
theorem prime_natCast_not_isUnit_pow {p d : Nat} (hp : p.Prime) (hd : 0 < d) :
    ¬ IsUnit ((p : Nat) : ZMod (p ^ d)) := by
  simp [isUnit_prime_iff_not_dvd hp]
  lia

@[simp]
/--
theorem `inv_coe_unit` / 定理 `inv_coe_unit`

English:
theorem inv_coe_unit
  given: {n : Nat} (u : (ZMod n)ˣ)
  statement: (u : ZMod n)⁻¹ = (u⁻¹ : (ZMod n)ˣ)
  proof: by
  have := congr_arg ((↑) : Nat -> ZMod n) (val_coe_unit_coprime u)
  rw [← mul_inv_eq_gcd]; rw [Nat.cast_one] at this
  exact (Units.inv_eq_of_mul_eq_one_right this).symm

中文:
定理 inv_coe_unit
  条件: {n : 自然数} (u : (ZMod n)ˣ)
  结论: (u : ZMod n)⁻¹ = (u⁻¹ : (ZMod n)ˣ)
  证明: by
  have := congr_arg ((↑) : Nat -> ZMod n) (val_coe_unit_coprime u)
  rw [← mul_inv_eq_gcd]; rw [Nat.cast_one] at this
  exact (Units.inv_eq_of_mul_eq_one_right this).symm

Depends on / 依赖: Nat.cast_one, Units.inv_eq_of_mul_eq_one_right, cast_one, congr_arg, inv_eq_of_mul_eq_one_right, mul_inv_eq_gcd, val_coe_unit_coprime
-/
theorem inv_coe_unit {n : Nat} (u : (ZMod n)ˣ) : (u : ZMod n)⁻¹ = (u⁻¹ : (ZMod n)ˣ) := by
  have := congr_arg ((↑) : Nat -> ZMod n) (val_coe_unit_coprime u)
  rw [← mul_inv_eq_gcd]; rw [Nat.cast_one] at this
  exact (Units.inv_eq_of_mul_eq_one_right this).symm

/--
theorem `mul_inv_of_unit` / 定理 `mul_inv_of_unit`

English:
theorem mul_inv_of_unit
  given: {n : Nat} (a : ZMod n) (h : IsUnit a)
  statement: a * a⁻¹ = 1
  proof: by
  rcases h with ⟨u, rfl⟩
  rw [inv_coe_unit]; rw [u.mul_inv]

中文:
定理 mul_inv_of_unit
  条件: {n : 自然数} (a : ZMod n) (h : IsUnit a)
  结论: a * a⁻¹ = 1
  证明: by
  rcases h with ⟨u, rfl⟩
  rw [inv_coe_unit]; rw [u.mul_inv]

Depends on / 依赖: inv_coe_unit, mul_inv, u.mul_inv
-/
theorem mul_inv_of_unit {n : Nat} (a : ZMod n) (h : IsUnit a) : a * a⁻¹ = 1 := by
  rcases h with ⟨u, rfl⟩
  rw [inv_coe_unit]; rw [u.mul_inv]

/--
theorem `inv_mul_of_unit` / 定理 `inv_mul_of_unit`

English:
theorem inv_mul_of_unit
  given: {n : Nat} (a : ZMod n) (h : IsUnit a)
  statement: a⁻¹ * a = 1
  proof: by
  rw [mul_comm]; rw [mul_inv_of_unit a h]

中文:
定理 inv_mul_of_unit
  条件: {n : 自然数} (a : ZMod n) (h : IsUnit a)
  结论: a⁻¹ * a = 1
  证明: by
  rw [mul_comm]; rw [mul_inv_of_unit a h]

Depends on / 依赖: mul_comm, mul_inv_of_unit
-/
theorem inv_mul_of_unit {n : Nat} (a : ZMod n) (h : IsUnit a) : a⁻¹ * a = 1 := by
  rw [mul_comm]; rw [mul_inv_of_unit a h]

-- TODO: If we changed `⁻¹` so that `ZMod n` is always a `DivisionMonoid`,
-- then we could use the general lemma `inv_eq_of_mul_eq_one`
/--
theorem `inv_eq_of_mul_eq_one` / 定理 `inv_eq_of_mul_eq_one`

English:
theorem inv_eq_of_mul_eq_one
  given: (n : Nat) (a b : ZMod n) (h : a * b = 1)
  statement: a⁻¹ = b
  proof: left_inv_eq_right_inv (inv_mul_of_unit a ⟨⟨a, b, h, mul_comm a b ▸ h⟩, rfl⟩) h

@[simp]

中文:
定理 inv_eq_of_mul_eq_one
  条件: (n : 自然数) (a b : ZMod n) (h : a * b = 1)
  结论: a⁻¹ = b
  证明: left_inv_eq_right_inv (inv_mul_of_unit a ⟨⟨a, b, h, mul_comm a b ▸ h⟩, rfl⟩) h

@[simp]
-/
protected theorem inv_eq_of_mul_eq_one (n : Nat) (a b : ZMod n) (h : a * b = 1) : a⁻¹ = b :=
  left_inv_eq_right_inv (inv_mul_of_unit a ⟨⟨a, b, h, mul_comm a b ▸ h⟩, rfl⟩) h

@[simp]
/--
theorem `inv_neg_one` / 定理 `inv_neg_one`

English:
theorem inv_neg_one
  given: (n : Nat)
  statement: (-1 : ZMod n)⁻¹ = -1
  proof: ZMod.inv_eq_of_mul_eq_one n (-1) (-1) (by simp)

中文:
定理 inv_neg_one
  条件: (n : 自然数)
  结论: (-1 : ZMod n)⁻¹ = -1
  证明: ZMod.inv_eq_of_mul_eq_one n (-1) (-1) (by simp)

Depends on / 依赖: ZMod.inv_eq_of_mul_eq_one, inv_eq_of_mul_eq_one
-/
theorem inv_neg_one (n : Nat) : (-1 : ZMod n)⁻¹ = -1 :=
  ZMod.inv_eq_of_mul_eq_one n (-1) (-1) (by simp)

/--
lemma `inv_mul_eq_one_of_isUnit` / 引理 `inv_mul_eq_one_of_isUnit`

English:
lemma inv_mul_eq_one_of_isUnit
  given: {n : Nat} {a : ZMod n} (ha : IsUnit a) (b : ZMod n)
  proof: by
  -- ideally, this would be `ha.inv_mul_eq_one`, but `ZMod n` is not a `DivisionMonoid`...
  -- (see the "TODO" above)
  refine ⟨fun H => ?_, fun H => H ▸ a.inv_mul_of_unit ha⟩
  apply_fun (a * ·) at H
  rwa [← mul_assoc, a.mul_inv_of_unit ha, one_mul, mul_one, eq_comm] at H

中文:
引理 inv_mul_eq_one_of_isUnit
  条件: {n : 自然数} {a : ZMod n} (ha : IsUnit a) (b : ZMod n)
  证明: by
  -- ideally, this would be `ha.inv_mul_eq_one`, but `ZMod n` is not a `DivisionMonoid`...
  -- (see the "TODO" above)
  refine ⟨fun H => ?_, fun H => H ▸ a.inv_mul_of_unit ha⟩
  apply_fun (a * ·) at H
  rwa [← mul_assoc, a.mul_inv_of_unit ha, one_mul, mul_one, eq_comm] at H
-/
lemma inv_mul_eq_one_of_isUnit {n : Nat} {a : ZMod n} (ha : IsUnit a) (b : ZMod n) :
    a⁻¹ * b = 1 ↔ a = b := by
  -- ideally, this would be `ha.inv_mul_eq_one`, but `ZMod n` is not a `DivisionMonoid`...
  -- (see the "TODO" above)
  refine ⟨fun H => ?_, fun H => H ▸ a.inv_mul_of_unit ha⟩
  apply_fun (a * ·) at H
  rwa [← mul_assoc, a.mul_inv_of_unit ha, one_mul, mul_one, eq_comm] at H

-- TODO: this equivalence is true for `ZMod 0 = ℤ`, but needs to use different functions.
/--
Definition of `unitsEquivCoprime` / `unitsEquivCoprime` 的定义

English:
definition unitsEquivCoprime
  signature: {n : Nat} [NeZero n]
  body: ⟨x, val_coe_unit_coprime x⟩
  invFun x := unitOfCoprime x.1.val x.2
  left_inv := fun ⟨_, _, _, _⟩ => Units.ext (natCast_zmod_val _)
  right_inv := fun ⟨_, _⟩ => by simp

中文:
定义 unitsEquivCoprime
  签名: {n : 自然数} [NeZero n]
  定义体: ⟨x, val_coe_unit_coprime x⟩
  invFun x := unitOfCoprime x.1.val x.2
  left_inv := fun ⟨_, _, _, _⟩ => Units.ext (natCast_zmod_val _)
  right_inv := fun ⟨_, _⟩ => by simp

Depends on / 依赖: val_coe_unit_coprime
-/
def unitsEquivCoprime {n : Nat} [NeZero n] : (ZMod n)ˣ ≃ { x : ZMod n // Nat.Coprime x.val n } where
  toFun x := ⟨x, val_coe_unit_coprime x⟩
  invFun x := unitOfCoprime x.1.val x.2
  left_inv := fun ⟨_, _, _, _⟩ => Units.ext (natCast_zmod_val _)
  right_inv := fun ⟨_, _⟩ => by simp

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `chineseRemainder` / `chineseRemainder` 的定义

English:
definition chineseRemainder
  signature: {m n : Nat} (h : m.Coprime n)
  body: let to_fun : ZMod (m * n) -> ZMod m × ZMod n :=
    ZMod.castHom (show m.lcm n ∣ m * n by simp [Nat.lcm_dvd_iff]) (ZMod m × ZMod n)
  let inv_fun : ZMod m × ZMod n -> ZMod (m * n) := fun x =>
    if m * n = 0 then
      if m = 1 then cast (RingHom.snd _ (ZMod n) x) else cast (RingHom.fst (ZMod m) _ 

中文:
定义 chineseRemainder
  签名: {m n : 自然数} (h : m.Coprime n)
  定义体: let to_fun : ZMod (m * n) -> ZMod m × ZMod n :=
    ZMod.castHom (show m.lcm n ∣ m * n by simp [Nat.lcm_dvd_iff]) (ZMod m × ZMod n)
  let inv_fun : ZMod m × ZMod n -> ZMod (m * n) := fun x =>
    if m * n = 0 then
      if m = 1 then cast (RingHom.snd _ (ZMod n) x) else cast (RingHom.fst (ZMod m) _ 

Depends on / 依赖: Function, Function.LeftInverse, Function.RightInverse, LeftInverse, Nat.chineseRemainder, Nat.lcm_dvd_iff, RightInverse, RingHom, RingHom.fst, RingHom.snd, ZMod.castHom, castHom, chineseRemainder, eq_of_mul_eq_zero, h.eq_of_mul_eq_zero, inv_fun, lcm_dvd_iff, m.lcm, to_fun
-/
def chineseRemainder {m n : Nat} (h : m.Coprime n) : ZMod (m * n) ≃+* ZMod m × ZMod n :=
  let to_fun : ZMod (m * n) -> ZMod m × ZMod n :=
    ZMod.castHom (show m.lcm n ∣ m * n by simp [Nat.lcm_dvd_iff]) (ZMod m × ZMod n)
  let inv_fun : ZMod m × ZMod n -> ZMod (m * n) := fun x =>
    if m * n = 0 then
      if m = 1 then cast (RingHom.snd _ (ZMod n) x) else cast (RingHom.fst (ZMod m) _ x)
    else Nat.chineseRemainder h x.1.val x.2.val
  have inv : Function.LeftInverse inv_fun to_fun ∧ Function.RightInverse inv_fun to_fun :=
    if hmn0 : m * n = 0 then by
      rcases h.eq_of_mul_eq_zero hmn0 with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · constructor
        · intro x; rfl
        · rintro ⟨x, y⟩
          fin_cases y
          simp [to_fun, inv_fun, castHom, Prod.ext_iff, eq_iff_true_of_subsingleton]
      · constructor
        · intro x; rfl
        · rintro ⟨x, y⟩
          fin_cases x
          simp [to_fun, inv_fun, castHom, Prod.ext_iff, eq_iff_true_of_subsingleton]
    else by
      have : NeZero (m * n) := ⟨hmn0⟩
      have : NeZero m := ⟨left_ne_zero_of_mul hmn0⟩
      have : NeZero n := ⟨right_ne_zero_of_mul hmn0⟩
      have left_inv : Function.LeftInverse inv_fun to_fun := by
        intro x
        dsimp only [to_fun, inv_fun, ZMod.castHom_apply]
        conv_rhs => rw [← ZMod.natCast_zmod_val x]
        rw [if_neg hmn0]; rw [ZMod.natCast_eq_natCast_iff]; rw [← Nat.modEq_and_modEq_iff_modEq_mul h]; rw [Prod.fst_zmod_cast]; rw [Prod.snd_zmod_cast]
        refine
          ⟨(Nat.chineseRemainder h (cast x : ZMod m).val (cast x : ZMod n).val).2.left.trans ?_,
            (Nat.chineseRemainder h (cast x : ZMod m).val (cast x : ZMod n).val).2.right.trans ?_⟩
        · rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val, ZMod.natCast_val]
        · rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val, ZMod.natCast_val]
      exact ⟨left_inv, left_inv.rightInverse_of_card_le (by simp)⟩
  { toFun := to_fun,
    invFun := inv_fun,
    map_mul' := map_mul _
    map_add' := map_add _
    left_inv := inv.1
    right_inv := inv.2 }

/--
lemma `subsingleton_iff` / 引理 `subsingleton_iff`

English:
lemma subsingleton_iff
  given: {n : Nat}
  statement: Subsingleton (ZMod n) ↔ n = 1
  proof: by
  constructor
  · obtain (_ | _ | n) := n
    · simpa [ZMod] using not_subsingleton _
    · simp [ZMod]
    · simpa [ZMod] using not_subsingleton _
  · rintro rfl
    infer_instance

中文:
引理 subsingleton_iff
  条件: {n : 自然数}
  结论: Subsingleton (ZMod n) ↔ n = 1
  证明: by
  constructor
  · obtain (_ | _ | n) := n
    · simpa [ZMod] using not_subsingleton _
    · simp [ZMod]
    · simpa [ZMod] using not_subsingleton _
  · rintro rfl
    infer_instance

Depends on / 依赖: infer_instance, not_subsingleton
-/
lemma subsingleton_iff {n : Nat} : Subsingleton (ZMod n) ↔ n = 1 := by
  constructor
  · obtain (_ | _ | n) := n
    · simpa [ZMod] using not_subsingleton _
    · simp [ZMod]
    · simpa [ZMod] using not_subsingleton _
  · rintro rfl
    infer_instance

/--
lemma `nontrivial_iff` / 引理 `nontrivial_iff`

English:
lemma nontrivial_iff
  given: {n : Nat}
  statement: Nontrivial (ZMod n) ↔ n != 1
  proof: by
  rw [← not_subsingleton_iff_nontrivial]; rw [subsingleton_iff]

中文:
引理 nontrivial_iff
  条件: {n : 自然数}
  结论: Nontrivial (ZMod n) ↔ n != 1
  证明: by
  rw [← not_subsingleton_iff_nontrivial]; rw [subsingleton_iff]

Depends on / 依赖: not_subsingleton_iff_nontrivial, subsingleton_iff
-/
lemma nontrivial_iff {n : Nat} : Nontrivial (ZMod n) ↔ n != 1 := by
  rw [← not_subsingleton_iff_nontrivial]; rw [subsingleton_iff]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Unique (ZMod 2)ˣ
  body: 1
  uniq := by decide

@[simp]

中文:
实例 :
  签名: Unique (ZMod 2)ˣ
  定义体: 1
  uniq := by decide

@[simp]
-/
instance : Unique (ZMod 2)ˣ where
  default := 1
  uniq := by decide

@[simp]
/--
theorem `add_self_eq_zero_iff_eq_zero` / 定理 `add_self_eq_zero_iff_eq_zero`

English:
theorem add_self_eq_zero_iff_eq_zero
  given: {n : Nat} (hn : Odd n) {a : ZMod n}
  proof: by
  rw [Nat.odd_iff]; rw [← Nat.two_dvd_ne_zero]; rw [← Nat.prime_two.coprime_iff_not_dvd] at hn
  rw [← mul_two]; rw [← @Nat.cast_two (ZMod n)]; rw [← ZMod.coe_unitOfCoprime 2 hn]; rw [Units.mul_left_eq_zero]

中文:
定理 add_self_eq_zero_iff_eq_zero
  条件: {n : 自然数} (hn : Odd n) {a : ZMod n}
  证明: by
  rw [Nat.odd_iff]; rw [← Nat.two_dvd_ne_zero]; rw [← Nat.prime_two.coprime_iff_not_dvd] at hn
  rw [← mul_two]; rw [← @Nat.cast_two (ZMod n)]; rw [← ZMod.coe_unitOfCoprime 2 hn]; rw [Units.mul_left_eq_zero]

Depends on / 依赖: Nat.cast_two, Nat.odd_iff, Nat.prime_two.coprime_iff_not_dvd, Nat.two_dvd_ne_zero, Units.mul_left_eq_zero, ZMod.coe_unitOfCoprime, cast_two, coe_unitOfCoprime, coprime_iff_not_dvd, mul_left_eq_zero, mul_two, odd_iff, prime_two, two_dvd_ne_zero
-/
theorem add_self_eq_zero_iff_eq_zero {n : Nat} (hn : Odd n) {a : ZMod n} :
    a + a = 0 ↔ a = 0 := by
  rw [Nat.odd_iff]; rw [← Nat.two_dvd_ne_zero]; rw [← Nat.prime_two.coprime_iff_not_dvd] at hn
  rw [← mul_two]; rw [← @Nat.cast_two (ZMod n)]; rw [← ZMod.coe_unitOfCoprime 2 hn]; rw [Units.mul_left_eq_zero]

/--
theorem `ne_neg_self` / 定理 `ne_neg_self`

English:
theorem ne_neg_self
  given: {n : Nat} (hn : Odd n) {a : ZMod n} (ha : a != 0)
  statement: a != -a
  proof: by
  rwa [Ne, eq_neg_iff_add_eq_zero, add_self_eq_zero_iff_eq_zero hn]

中文:
定理 ne_neg_self
  条件: {n : 自然数} (hn : Odd n) {a : ZMod n} (ha : a != 0)
  结论: a != -a
  证明: by
  rwa [Ne, eq_neg_iff_add_eq_zero, add_self_eq_zero_iff_eq_zero hn]

Depends on / 依赖: add_self_eq_zero_iff_eq_zero, eq_neg_iff_add_eq_zero
-/
theorem ne_neg_self {n : Nat} (hn : Odd n) {a : ZMod n} (ha : a != 0) : a != -a := by
  rwa [Ne, eq_neg_iff_add_eq_zero, add_self_eq_zero_iff_eq_zero hn]

/--
theorem `neg_one_ne_one` / 定理 `neg_one_ne_one`

English:
theorem neg_one_ne_one
  given: {n : Nat} [Fact (2 < n)]
  statement: (-1 : ZMod n) != 1
  proof: CharP.neg_one_ne_one (ZMod n) n

中文:
定理 neg_one_ne_one
  条件: {n : 自然数} [Fact (2 < n)]
  结论: (-1 : ZMod n) != 1
  证明: CharP.neg_one_ne_one (ZMod n) n

Depends on / 依赖: CharP.neg_one_ne_one, neg_one_ne_one
-/
theorem neg_one_ne_one {n : Nat} [Fact (2 < n)] : (-1 : ZMod n) != 1 :=
  CharP.neg_one_ne_one (ZMod n) n

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `neg_eq_self_mod_two` / 定理 `neg_eq_self_mod_two`

English:
theorem neg_eq_self_mod_two
  given: (a : ZMod 2)
  statement: -a = a
  proof: by
  fin_cases a <;> apply Fin.ext <;> simp; rfl

@[simp]

中文:
定理 neg_eq_self_mod_two
  条件: (a : ZMod 2)
  结论: -a = a
  证明: by
  fin_cases a <;> apply Fin.ext <;> simp; rfl

@[simp]

Depends on / 依赖: Fin.ext, fin_cases
-/
theorem neg_eq_self_mod_two (a : ZMod 2) : -a = a := by
  fin_cases a <;> apply Fin.ext <;> simp; rfl

@[simp]
/--
theorem `intCast_abs_mod_two` / 定理 `intCast_abs_mod_two`

English:
theorem intCast_abs_mod_two
  given: (a : Int)
  statement: (↑|a| : ZMod 2) = a
  proof: by
  cases le_total a 0 <;> simp [abs_of_nonneg, abs_of_nonpos, *]

中文:
定理 intCast_abs_mod_two
  条件: (a : 整数)
  结论: (↑|a| : ZMod 2) = a
  证明: by
  cases le_total a 0 <;> simp [abs_of_nonneg, abs_of_nonpos, *]

Depends on / 依赖: abs_of_nonneg, abs_of_nonpos, le_total
-/
theorem intCast_abs_mod_two (a : Int) : (↑|a| : ZMod 2) = a := by
  cases le_total a 0 <;> simp [abs_of_nonneg, abs_of_nonpos, *]

/--
theorem `natAbs_mod_two` / 定理 `natAbs_mod_two`

English:
theorem natAbs_mod_two
  given: (a : Int)
  statement: (a.natAbs : ZMod 2) = a
  proof: by
  simp

中文:
定理 natAbs_mod_two
  条件: (a : 整数)
  结论: (a.natAbs : ZMod 2) = a
  证明: by
  simp
-/
theorem natAbs_mod_two (a : Int) : (a.natAbs : ZMod 2) = a := by
  simp

/--
theorem `val_ne_zero` / 定理 `val_ne_zero`

English:
theorem val_ne_zero
  given: {n : Nat} (a : ZMod n)
  statement: a.val != 0 ↔ a != 0
  proof: (val_eq_zero a).not

@[simp]

中文:
定理 val_ne_zero
  条件: {n : 自然数} (a : ZMod n)
  结论: a.val != 0 ↔ a != 0
  证明: (val_eq_zero a).not

@[simp]

Depends on / 依赖: val_eq_zero
-/
theorem val_ne_zero {n : Nat} (a : ZMod n) : a.val != 0 ↔ a != 0 :=
  (val_eq_zero a).not

@[simp]
/--
theorem `val_pos` / 定理 `val_pos`

English:
theorem val_pos
  given: {n : Nat} {a : ZMod n}
  statement: 0 < a.val ↔ a != 0
  proof: by
  simp [pos_iff_ne_zero]

中文:
定理 val_pos
  条件: {n : 自然数} {a : ZMod n}
  结论: 0 < a.val ↔ a != 0
  证明: by
  simp [pos_iff_ne_zero]

Depends on / 依赖: pos_iff_ne_zero
-/
theorem val_pos {n : Nat} {a : ZMod n} : 0 < a.val ↔ a != 0 := by
  simp [pos_iff_ne_zero]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `val_eq_one` / 定理 `val_eq_one`

English:
theorem val_eq_one
  statement: forall {n : Nat} (_ : 1 < n) (a : ZMod n), a.val = 1 ↔ a = 1

中文:
定理 val_eq_one
  结论: 对任意 {n : 自然数} (_ : 1 < n) (a : ZMod n), a.val = 1 ↔ a = 1
-/
theorem val_eq_one : forall {n : Nat} (_ : 1 < n) (a : ZMod n), a.val = 1 ↔ a = 1
  | 0, hn, _
  | 1, hn, _ => by simp at hn
  | n + 2, _, _ => by simp only [val, ZMod, Fin.ext_iff, Fin.val_one]

/--
theorem `neg_eq_self_iff` / 定理 `neg_eq_self_iff`

English:
theorem neg_eq_self_iff
  given: {n : Nat} (a : ZMod n)
  statement: -a = a ↔ a = 0 ∨ 2 * a.val = n
  proof: by
  rw [neg_eq_iff_add_eq_zero]; rw [← two_mul]
  cases n
  · simp
  conv_lhs =>
    rw [← a.natCast_zmod_val]; rw [← Nat.cast_two]; rw [← Nat.cast_mul]; rw [natCast_eq_zero_iff]
  constructor
  · rintro ⟨m, he⟩
    rcases m with - | m
    · rw [mul_zero, mul_eq_zero] at he
      rcases he with (⟨⟨

中文:
定理 neg_eq_self_iff
  条件: {n : 自然数} (a : ZMod n)
  结论: -a = a ↔ a = 0 ∨ 2 * a.val = n
  证明: by
  rw [neg_eq_iff_add_eq_zero]; rw [← two_mul]
  cases n
  · simp
  conv_lhs =>
    rw [← a.natCast_zmod_val]; rw [← Nat.cast_two]; rw [← Nat.cast_mul]; rw [natCast_eq_zero_iff]
  constructor
  · rintro ⟨m, he⟩
    rcases m with - | m
    · rw [mul_zero, mul_eq_zero] at he
      rcases he with (⟨⟨

Depends on / 依赖: Nat.cast_mul, Nat.cast_two, Nat.le_of_mul_le_mul_left, Nat.mul_le_mul_left, Or.inl, a.natCast_zmod_val, a.val_eq_zero, a.val_lt.not_ge, cast_mul, cast_two, conv_lhs, le_of_mul_le_mul_left, mul_comm, mul_eq_zero, mul_le_mul_left, mul_one, mul_zero, natCast_eq_zero_iff, natCast_zmod_val, neg_eq_iff_add_eq_zero
-/
theorem neg_eq_self_iff {n : Nat} (a : ZMod n) : -a = a ↔ a = 0 ∨ 2 * a.val = n := by
  rw [neg_eq_iff_add_eq_zero]; rw [← two_mul]
  cases n
  · simp
  conv_lhs =>
    rw [← a.natCast_zmod_val]; rw [← Nat.cast_two]; rw [← Nat.cast_mul]; rw [natCast_eq_zero_iff]
  constructor
  · rintro ⟨m, he⟩
    rcases m with - | m
    · rw [mul_zero, mul_eq_zero] at he
      rcases he with (⟨⟨⟩⟩ | he)
      exact Or.inl (a.val_eq_zero.1 he)
    cases m
    · right
      rwa [show 0 + 1 = 1 from rfl, mul_one] at he
    refine (a.val_lt.not_ge <| Nat.le_of_mul_le_mul_left ?_ zero_lt_two).elim
    rw [he]; rw [mul_comm]
    apply Nat.mul_le_mul_left
    simp
  · rintro (rfl | h)
    · rw [val_zero, mul_zero]
      apply dvd_zero
    · rw [h]

/--
theorem `val_cast_of_lt` / 定理 `val_cast_of_lt`

English:
theorem val_cast_of_lt
  given: {n : Nat} {a : Nat} (h : a < n)
  statement: (a : ZMod n).val = a
  proof: by
  rw [val_natCast]; rw [Nat.mod_eq_of_lt h]

中文:
定理 val_cast_of_lt
  条件: {n : 自然数} {a : 自然数} (h : a < n)
  结论: (a : ZMod n).val = a
  证明: by
  rw [val_natCast]; rw [Nat.mod_eq_of_lt h]

Depends on / 依赖: Nat.mod_eq_of_lt, mod_eq_of_lt, val_natCast
-/
theorem val_cast_of_lt {n : Nat} {a : Nat} (h : a < n) : (a : ZMod n).val = a := by
  rw [val_natCast]; rw [Nat.mod_eq_of_lt h]

/--
theorem `val_cast_zmod_lt` / 定理 `val_cast_zmod_lt`

English:
theorem val_cast_zmod_lt
  given: {m : Nat} [NeZero m] (n : Nat) [NeZero n] (a : ZMod m)
  proof: by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (NeZero.ne m)
  by_cases! h : m < n
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (NeZero.ne n)
    rw [← natCast_val]; rw [val_cast_of_lt]
    · apply a.val_lt
    apply lt_of_le_of_lt (Nat.le_of_lt_succ (ZMod.val_lt a)) h
  · apply

中文:
定理 val_cast_zmod_lt
  条件: {m : 自然数} [NeZero m] (n : 自然数) [NeZero n] (a : ZMod m)
  证明: by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (NeZero.ne m)
  by_cases! h : m < n
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (NeZero.ne n)
    rw [← natCast_val]; rw [val_cast_of_lt]
    · apply a.val_lt
    apply lt_of_le_of_lt (Nat.le_of_lt_succ (ZMod.val_lt a)) h
  · apply

Depends on / 依赖: Nat.exists_eq_add_one_of_ne_zero, Nat.le_of_lt_succ, Nat.le_succ, NeZero, NeZero.ne, ZMod.val_lt, a.val_lt, exists_eq_add_one_of_ne_zero, le_of_lt_succ, le_succ, le_trans, lt_of_le_of_lt, lt_of_lt_of_le, natCast_val, val_cast_of_lt, val_lt
-/
theorem val_cast_zmod_lt {m : Nat} [NeZero m] (n : Nat) [NeZero n] (a : ZMod m) :
    (a.cast : ZMod n).val < m := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (NeZero.ne m)
  by_cases! h : m < n
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (NeZero.ne n)
    rw [← natCast_val]; rw [val_cast_of_lt]
    · apply a.val_lt
    apply lt_of_le_of_lt (Nat.le_of_lt_succ (ZMod.val_lt a)) h
  · apply lt_of_lt_of_le (ZMod.val_lt _) (le_trans h (Nat.le_succ m))

/--
theorem `neg_val'` / 定理 `neg_val'`

English:
theorem neg_val'
  given: {n : Nat} [NeZero n] (a : ZMod n)
  statement: (-a).val = (n - a.val) % n
  proof: calc
    (-a).val = val (-a) % n := by rw [Nat.mod_eq_of_lt (-a).val_lt]
    _ = (n - val a) % n :=
      Nat.ModEq.add_right_cancel' (val a)
        (by
          rw [Nat.ModEq]; rw [← val_add]; rw [neg_add_cancel]; rw [tsub_add_cancel_of_le a.val_le]; rw [Nat.mod_self]; rw [val_zero])

中文:
定理 neg_val'
  条件: {n : 自然数} [NeZero n] (a : ZMod n)
  结论: (-a).val = (n - a.val) % n
  证明: calc
    (-a).val = val (-a) % n := by rw [Nat.mod_eq_of_lt (-a).val_lt]
    _ = (n - val a) % n :=
      Nat.ModEq.add_right_cancel' (val a)
        (by
          rw [Nat.ModEq]; rw [← val_add]; rw [neg_add_cancel]; rw [tsub_add_cancel_of_le a.val_le]; rw [Nat.mod_self]; rw [val_zero])

Depends on / 依赖: Nat.ModEq, Nat.ModEq.add_right_cancel, Nat.mod_eq_of_lt, Nat.mod_self, a.val_le, add_right_cancel, mod_eq_of_lt, mod_self, neg_add_cancel, tsub_add_cancel_of_le, val_add, val_le, val_lt, val_zero
-/
theorem neg_val' {n : Nat} [NeZero n] (a : ZMod n) : (-a).val = (n - a.val) % n :=
  calc
    (-a).val = val (-a) % n := by rw [Nat.mod_eq_of_lt (-a).val_lt]
    _ = (n - val a) % n :=
      Nat.ModEq.add_right_cancel' (val a)
        (by
          rw [Nat.ModEq]; rw [← val_add]; rw [neg_add_cancel]; rw [tsub_add_cancel_of_le a.val_le]; rw [Nat.mod_self]; rw [val_zero])

/--
theorem `neg_val` / 定理 `neg_val`

English:
theorem neg_val
  given: {n : Nat} [NeZero n] (a : ZMod n)
  statement: (-a).val = if a = 0 then 0 else n - a.val
  proof: by
  rw [neg_val']
  by_cases h : a = 0; · rw [if_pos h, h, val_zero, tsub_zero, Nat.mod_self]
  rw [if_neg h]
  apply Nat.mod_eq_of_lt
  exact Nat.sub_lt (NeZero.pos n) (val_pos.mpr h)

中文:
定理 neg_val
  条件: {n : 自然数} [NeZero n] (a : ZMod n)
  结论: (-a).val = if a = 0 then 0 else n - a.val
  证明: by
  rw [neg_val']
  by_cases h : a = 0; · rw [if_pos h, h, val_zero, tsub_zero, Nat.mod_self]
  rw [if_neg h]
  apply Nat.mod_eq_of_lt
  exact Nat.sub_lt (NeZero.pos n) (val_pos.mpr h)

Depends on / 依赖: Nat.mod_eq_of_lt, Nat.mod_self, Nat.sub_lt, NeZero, NeZero.pos, if_neg, if_pos, mod_eq_of_lt, mod_self, neg_val, sub_lt, tsub_zero, val_pos, val_pos.mpr, val_zero
-/
theorem neg_val {n : Nat} [NeZero n] (a : ZMod n) : (-a).val = if a = 0 then 0 else n - a.val := by
  rw [neg_val']
  by_cases h : a = 0; · rw [if_pos h, h, val_zero, tsub_zero, Nat.mod_self]
  rw [if_neg h]
  apply Nat.mod_eq_of_lt
  exact Nat.sub_lt (NeZero.pos n) (val_pos.mpr h)

/--
theorem `val_neg_of_ne_zero` / 定理 `val_neg_of_ne_zero`

English:
theorem val_neg_of_ne_zero
  given: {n : Nat} [nz : NeZero n] (a : ZMod n) [na : NeZero a]
  proof: by simp_all [neg_val a, na.out]

中文:
定理 val_neg_of_ne_zero
  条件: {n : 自然数} [nz : NeZero n] (a : ZMod n) [na : NeZero a]
  证明: by simp_all [neg_val a, na.out]

Depends on / 依赖: na.out, neg_val
-/
theorem val_neg_of_ne_zero {n : Nat} [nz : NeZero n] (a : ZMod n) [na : NeZero a] :
    (-a).val = n - a.val := by simp_all [neg_val a, na.out]

/--
theorem `val_sub` / 定理 `val_sub`

English:
theorem val_sub
  given: {n : Nat} [NeZero n] {a b : ZMod n} (h : b.val <= a.val)
  proof: by
  by_cases hb : b = 0
  · cases hb; simp
  · have : NeZero b := ⟨hb⟩
    rw [sub_eq_add_neg]; rw [val_add]; rw [val_neg_of_ne_zero]; rw [← Nat.add_sub_assoc (le_of_lt (val_lt _))]; rw [add_comm]; rw [Nat.add_sub_assoc h]; rw [Nat.add_mod_left]
    apply Nat.mod_eq_of_lt (tsub_lt_of_lt (val_lt _))

中文:
定理 val_sub
  条件: {n : 自然数} [NeZero n] {a b : ZMod n} (h : b.val <= a.val)
  证明: by
  by_cases hb : b = 0
  · cases hb; simp
  · have : NeZero b := ⟨hb⟩
    rw [sub_eq_add_neg]; rw [val_add]; rw [val_neg_of_ne_zero]; rw [← Nat.add_sub_assoc (le_of_lt (val_lt _))]; rw [add_comm]; rw [Nat.add_sub_assoc h]; rw [Nat.add_mod_left]
    apply Nat.mod_eq_of_lt (tsub_lt_of_lt (val_lt _))

Depends on / 依赖: Nat.add_mod_left, Nat.add_sub_assoc, Nat.mod_eq_of_lt, NeZero, add_comm, add_mod_left, add_sub_assoc, le_of_lt, mod_eq_of_lt, sub_eq_add_neg, tsub_lt_of_lt, val_add, val_lt, val_neg_of_ne_zero
-/
theorem val_sub {n : Nat} [NeZero n] {a b : ZMod n} (h : b.val <= a.val) :
    (a - b).val = a.val - b.val := by
  by_cases hb : b = 0
  · cases hb; simp
  · have : NeZero b := ⟨hb⟩
    rw [sub_eq_add_neg]; rw [val_add]; rw [val_neg_of_ne_zero]; rw [← Nat.add_sub_assoc (le_of_lt (val_lt _))]; rw [add_comm]; rw [Nat.add_sub_assoc h]; rw [Nat.add_mod_left]
    apply Nat.mod_eq_of_lt (tsub_lt_of_lt (val_lt _))

/--
theorem `val_cast_eq_val_of_lt` / 定理 `val_cast_eq_val_of_lt`

English:
theorem val_cast_eq_val_of_lt
  statement: {m n : Nat} [nzm : NeZero m] {a : ZMod m}
  proof: by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (NeZero.ne m)
obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero by rintro (rfl : n = 0); simp at h
  exact Fin.val_cast_of_lt h

中文:
定理 val_cast_eq_val_of_lt
  结论: {m n : 自然数} [nzm : NeZero m] {a : ZMod m}
  证明: by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (NeZero.ne m)
obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero by rintro (rfl : n = 0); simp at h
  exact Fin.val_cast_of_lt h

Depends on / 依赖: Fin.val_cast_of_lt, Nat.exists_eq_add_one_of_ne_zero, NeZero, NeZero.ne, exists_eq_add_one_of_ne_zero, val_cast_of_lt
-/
theorem val_cast_eq_val_of_lt {m n : Nat} [nzm : NeZero m] {a : ZMod m}
    (h : a.val < n) : (a.cast : ZMod n).val = a.val := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (NeZero.ne m)
obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero by rintro (rfl : n = 0); simp at h
  exact Fin.val_cast_of_lt h

/--
theorem `cast_cast_zmod_of_le` / 定理 `cast_cast_zmod_of_le`

English:
theorem cast_cast_zmod_of_le
  given: {m n : Nat} [hm : NeZero m] (h : m <= n) (a : ZMod m)
  proof: by
  have : NeZero n := ⟨((Nat.zero_lt_of_ne_zero hm.out).trans_le h).ne'⟩
  rw [cast_eq_val]; rw [val_cast_eq_val_of_lt (a.val_lt.trans_le h)]; rw [natCast_zmod_val]

中文:
定理 cast_cast_zmod_of_le
  条件: {m n : 自然数} [hm : NeZero m] (h : m <= n) (a : ZMod m)
  证明: by
  have : NeZero n := ⟨((Nat.zero_lt_of_ne_zero hm.out).trans_le h).ne'⟩
  rw [cast_eq_val]; rw [val_cast_eq_val_of_lt (a.val_lt.trans_le h)]; rw [natCast_zmod_val]

Depends on / 依赖: Nat.zero_lt_of_ne_zero, NeZero, a.val_lt.trans_le, cast_eq_val, hm.out, natCast_zmod_val, trans_le, val_cast_eq_val_of_lt, val_lt, zero_lt_of_ne_zero
-/
theorem cast_cast_zmod_of_le {m n : Nat} [hm : NeZero m] (h : m <= n) (a : ZMod m) :
    (cast (cast a : ZMod n) : ZMod m) = a := by
  have : NeZero n := ⟨((Nat.zero_lt_of_ne_zero hm.out).trans_le h).ne'⟩
  rw [cast_eq_val]; rw [val_cast_eq_val_of_lt (a.val_lt.trans_le h)]; rw [natCast_zmod_val]

/--
theorem `val_pow` / 定理 `val_pow`

English:
theorem val_pow
  given: {m n : Nat} {a : ZMod n} [ilt : Fact (1 < n)] (h : a.val ^ m < n)
  proof: by
  induction m with
  | zero => simp [ZMod.val_one]
  | succ m ih =>
    have : a.val ^ m < n := by
      obtain rfl | ha := eq_or_ne a 0
      · by_cases hm : m = 0
        · cases hm; simp [ilt.out]
        · simp only [val_zero, ne_eq, hm, not_false_eq_true, zero_pow, Nat.zero_lt_of_lt h]
     

中文:
定理 val_pow
  条件: {m n : 自然数} {a : ZMod n} [ilt : Fact (1 < n)] (h : a.val ^ m < n)
  证明: by
  induction m with
  | zero => simp [ZMod.val_one]
  | succ m ih =>
    have : a.val ^ m < n := by
      obtain rfl | ha := eq_or_ne a 0
      · by_cases hm : m = 0
        · cases hm; simp [ilt.out]
        · simp only [val_zero, ne_eq, hm, not_false_eq_true, zero_pow, Nat.zero_lt_of_lt h]
     

Depends on / 依赖: Nat.le_succ, Nat.mod_eq_of_lt, Nat.pow_le_pow_right, Nat.zero_lt_of_lt, ZMod.val_mul, ZMod.val_one, ZMod.val_pos, a.val, eq_or_ne, gt_iff_lt, ilt.out, le_succ, lt_of_le_of_lt, mod_eq_of_lt, ne_eq, not_false_eq_true, pow_le_pow_right, pow_succ, val_mul, val_one
-/
theorem val_pow {m n : Nat} {a : ZMod n} [ilt : Fact (1 < n)] (h : a.val ^ m < n) :
    (a ^ m).val = a.val ^ m := by
  induction m with
  | zero => simp [ZMod.val_one]
  | succ m ih =>
    have : a.val ^ m < n := by
      obtain rfl | ha := eq_or_ne a 0
      · by_cases hm : m = 0
        · cases hm; simp [ilt.out]
        · simp only [val_zero, ne_eq, hm, not_false_eq_true, zero_pow, Nat.zero_lt_of_lt h]
      · exact lt_of_le_of_lt
         (Nat.pow_le_pow_right (by rwa [gt_iff_lt, ZMod.val_pos]) (Nat.le_succ m)) h
    rw [pow_succ]; rw [ZMod.val_mul]; rw [ih this]; rw [← pow_succ]; rw [Nat.mod_eq_of_lt h]

/--
theorem `val_pow_le` / 定理 `val_pow_le`

English:
theorem val_pow_le
  given: {m n : Nat} [Fact (1 < n)] {a : ZMod n}
  statement: (a ^ m).val <= a.val ^ m
  proof: by
  induction m with
  | zero => simp [ZMod.val_one]
  | succ m ih =>
    rw [pow_succ]; rw [pow_succ]
    apply le_trans (ZMod.val_mul_le _ _)
    apply Nat.mul_le_mul_right _ ih

中文:
定理 val_pow_le
  条件: {m n : 自然数} [Fact (1 < n)] {a : ZMod n}
  结论: (a ^ m).val <= a.val ^ m
  证明: by
  induction m with
  | zero => simp [ZMod.val_one]
  | succ m ih =>
    rw [pow_succ]; rw [pow_succ]
    apply le_trans (ZMod.val_mul_le _ _)
    apply Nat.mul_le_mul_right _ ih

Depends on / 依赖: Nat.mul_le_mul_right, ZMod.val_mul_le, ZMod.val_one, le_trans, mul_le_mul_right, pow_succ, val_mul_le, val_one
-/
theorem val_pow_le {m n : Nat} [Fact (1 < n)] {a : ZMod n} : (a ^ m).val <= a.val ^ m := by
  induction m with
  | zero => simp [ZMod.val_one]
  | succ m ih =>
    rw [pow_succ]; rw [pow_succ]
    apply le_trans (ZMod.val_mul_le _ _)
    apply Nat.mul_le_mul_right _ ih

/--
theorem `natAbs_min_of_le_div_two` / 定理 `natAbs_min_of_le_div_two`

English:
theorem natAbs_min_of_le_div_two
  given: (n : Nat) (x y : Int) (he : (x : ZMod n) = y) (hl : x.natAbs <= n / 2)
  proof: by
  rw [intCast_eq_intCast_iff_dvd_sub] at he
  obtain ⟨m, he⟩ := he
  rw [sub_eq_iff_eq_add] at he
  subst he
  obtain rfl | hm := eq_or_ne m 0
  · rw [mul_zero, zero_add]
  apply hl.trans
  rw [← add_le_add_iff_right x.natAbs]
  refine le_trans (le_trans ((add_le_add_iff_left _).2 hl) ?_) (Int.na

中文:
定理 natAbs_min_of_le_div_two
  条件: (n : 自然数) (x y : 整数) (he : (x : ZMod n) = y) (hl : x.natAbs <= n / 2)
  证明: by
  rw [intCast_eq_intCast_iff_dvd_sub] at he
  obtain ⟨m, he⟩ := he
  rw [sub_eq_iff_eq_add] at he
  subst he
  obtain rfl | hm := eq_or_ne m 0
  · rw [mul_zero, zero_add]
  apply hl.trans
  rw [← add_le_add_iff_right x.natAbs]
  refine le_trans (le_trans ((add_le_add_iff_left _).2 hl) ?_) (Int.na

Depends on / 依赖: Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_pos, Int.natAbs_sub_le, Nat.div_mul_le_self, Nat.le_mul_of_pos_right, add_le_add_iff_left, add_le_add_iff_right, add_sub_cancel_right, div_mul_le_self, eq_or_ne, hl.trans, intCast_eq_intCast_iff_dvd_sub, le_mul_of_pos_right, le_trans, mul_two, mul_zero, natAbs, natAbs_mul, natAbs_natCast
-/
theorem natAbs_min_of_le_div_two (n : Nat) (x y : Int) (he : (x : ZMod n) = y) (hl : x.natAbs <= n / 2) :
    x.natAbs <= y.natAbs := by
  rw [intCast_eq_intCast_iff_dvd_sub] at he
  obtain ⟨m, he⟩ := he
  rw [sub_eq_iff_eq_add] at he
  subst he
  obtain rfl | hm := eq_or_ne m 0
  · rw [mul_zero, zero_add]
  apply hl.trans
  rw [← add_le_add_iff_right x.natAbs]
  refine le_trans (le_trans ((add_le_add_iff_left _).2 hl) ?_) (Int.natAbs_sub_le _ _)
  rw [add_sub_cancel_right]; rw [Int.natAbs_mul]; rw [Int.natAbs_natCast]
  refine le_trans ?_ (Nat.le_mul_of_pos_right _ <| Int.natAbs_pos.2 hm)
  rw [← mul_two]; apply Nat.div_mul_le_self

end ZMod

/--
theorem `RingHom.ext_zmod` / 定理 `RingHom.ext_zmod`

English:
theorem RingHom.ext_zmod
  given: {n : Nat} {R : Type*} [NonAssocSemiring R] (f g : ZMod n ->+* R)
  statement: f = g
  proof: by
  ext a
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective a
  let φ : Int ->+* R := f.comp (Int.castRingHom (ZMod n))
  let ψ : Int ->+* R := g.comp (Int.castRingHom (ZMod n))
  change φ k = ψ k
  rw [φ.ext_int ψ]

中文:
定理 RingHom.ext_zmod
  条件: {n : 自然数} {R : 类型} [NonAssocSemiring R] (f g : ZMod n ->+* R)
  结论: f = g
  证明: by
  ext a
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective a
  let φ : Int ->+* R := f.comp (Int.castRingHom (ZMod n))
  let ψ : Int ->+* R := g.comp (Int.castRingHom (ZMod n))
  change φ k = ψ k
  rw [φ.ext_int ψ]

Depends on / 依赖: Int.castRingHom, ZMod.intCast_surjective, castRingHom, ext_int, f.comp, g.comp, intCast_surjective
-/
theorem RingHom.ext_zmod {n : Nat} {R : Type*} [NonAssocSemiring R] (f g : ZMod n ->+* R) : f = g := by
  ext a
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective a
  let φ : Int ->+* R := f.comp (Int.castRingHom (ZMod n))
  let ψ : Int ->+* R := g.comp (Int.castRingHom (ZMod n))
  change φ k = ψ k
  rw [φ.ext_int ψ]

namespace ZMod

variable {n : Nat} {R : Type*}

/--
Instance `subsingleton_ringHom` / 实例 `subsingleton_ringHom`

English:
instance subsingleton_ringHom
  signature: [Semiring R]
  body: ⟨RingHom.ext_zmod⟩

中文:
实例 subsingleton_ringHom
  签名: [Semiring R]
  定义体: ⟨RingHom.ext_zmod⟩

Depends on / 依赖: RingHom, RingHom.ext_zmod, ext_zmod
-/
instance subsingleton_ringHom [Semiring R] : Subsingleton (ZMod n ->+* R) :=
  ⟨RingHom.ext_zmod⟩

/--
Instance `subsingleton_ringEquiv` / 实例 `subsingleton_ringEquiv`

English:
instance subsingleton_ringEquiv
  signature: [Semiring R]
  body: ⟨fun f g => by
    rw [RingEquiv.coe_ringHom_inj_iff]
    apply RingHom.ext_zmod _ _⟩

中文:
实例 subsingleton_ringEquiv
  签名: [Semiring R]
  定义体: ⟨fun f g => by
    rw [RingEquiv.coe_ringHom_inj_iff]
    apply RingHom.ext_zmod _ _⟩

Depends on / 依赖: RingEquiv, RingEquiv.coe_ringHom_inj_iff, RingHom, RingHom.ext_zmod, coe_ringHom_inj_iff, ext_zmod
-/
instance subsingleton_ringEquiv [Semiring R] : Subsingleton (ZMod n ≃+* R) :=
  ⟨fun f g => by
    rw [RingEquiv.coe_ringHom_inj_iff]
    apply RingHom.ext_zmod _ _⟩

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `ringHom_map_cast` / 定理 `ringHom_map_cast`

English:
theorem ringHom_map_cast
  given: [NonAssocRing R] (f : R ->+* ZMod n) (k : ZMod n)
  statement: f (cast k) = k
  proof: by
  cases n
  · dsimp +instances [ZMod, ZMod.cast] at f k ⊢
    simp
  · dsimp [ZMod.cast]
    rw [map_natCast]; rw [natCast_zmod_val]

中文:
定理 ringHom_map_cast
  条件: [NonAssocRing R] (f : R ->+* ZMod n) (k : ZMod n)
  结论: f (cast k) = k
  证明: by
  cases n
  · dsimp +instances [ZMod, ZMod.cast] at f k ⊢
    simp
  · dsimp [ZMod.cast]
    rw [map_natCast]; rw [natCast_zmod_val]

Depends on / 依赖: ZMod.cast, instances, map_natCast, natCast_zmod_val
-/
theorem ringHom_map_cast [NonAssocRing R] (f : R ->+* ZMod n) (k : ZMod n) : f (cast k) = k := by
  cases n
  · dsimp +instances [ZMod, ZMod.cast] at f k ⊢
    simp
  · dsimp [ZMod.cast]
    rw [map_natCast]; rw [natCast_zmod_val]

/--
theorem `ringHom_rightInverse` / 定理 `ringHom_rightInverse`

English:
theorem ringHom_rightInverse
  given: [NonAssocRing R] (f : R ->+* ZMod n)
  proof: ringHom_map_cast f

中文:
定理 ringHom_rightInverse
  条件: [NonAssocRing R] (f : R ->+* ZMod n)
  证明: ringHom_map_cast f

Depends on / 依赖: ringHom_map_cast
-/
theorem ringHom_rightInverse [NonAssocRing R] (f : R ->+* ZMod n) :
    Function.RightInverse (cast : ZMod n -> R) f :=
  ringHom_map_cast f

/--
theorem `ringHom_surjective` / 定理 `ringHom_surjective`

English:
theorem ringHom_surjective
  given: [NonAssocRing R] (f : R ->+* ZMod n)
  statement: Function.Surjective f
  proof: (ringHom_rightInverse f).surjective

@[simp]

中文:
定理 ringHom_surjective
  条件: [NonAssocRing R] (f : R ->+* ZMod n)
  结论: Function.Surjective f
  证明: (ringHom_rightInverse f).surjective

@[simp]

Depends on / 依赖: ringHom_rightInverse, surjective
-/
theorem ringHom_surjective [NonAssocRing R] (f : R ->+* ZMod n) : Function.Surjective f :=
  (ringHom_rightInverse f).surjective

@[simp]
/--
lemma `castHom_self` / 引理 `castHom_self`

English:
lemma castHom_self
  statement: ZMod.castHom dvd_rfl (ZMod n) = RingHom.id (ZMod n)
  proof: Subsingleton.elim _ _

@[simp]

中文:
引理 castHom_self
  结论: ZMod.castHom dvd_rfl (ZMod n) = RingHom.id (ZMod n)
  证明: Subsingleton.elim _ _

@[simp]

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
lemma castHom_self : ZMod.castHom dvd_rfl (ZMod n) = RingHom.id (ZMod n) :=
  Subsingleton.elim _ _

@[simp]
/--
lemma `castHom_comp` / 引理 `castHom_comp`

English:
lemma castHom_comp
  given: {m d : Nat} (hm : n ∣ m) (hd : m ∣ d)
  proof: RingHom.ext_zmod _ _

中文:
引理 castHom_comp
  条件: {m d : 自然数} (hm : n ∣ m) (hd : m ∣ d)
  证明: RingHom.ext_zmod _ _

Depends on / 依赖: RingHom, RingHom.ext_zmod, ext_zmod
-/
lemma castHom_comp {m d : Nat} (hm : n ∣ m) (hd : m ∣ d) :
    (castHom hm (ZMod n)).comp (castHom hd (ZMod m)) = castHom (dvd_trans hm hd) (ZMod n) :=
  RingHom.ext_zmod _ _

section lift

variable (n) {A : Type*} [AddGroup A]

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: : { f : Int ->+ A // f n = 0 } ≃ (ZMod n ->+ A)
  body: (Equiv.subtypeEquivRight <| by
        intro f
        rw [ker_intCastAddHom]
        constructor
        · rintro hf _ ⟨x, rfl⟩
          simp only [f.map_zsmul, zsmul_zero, f.mem_ker, hf]
        · intro h
          exact h (AddSubgroup.mem_zmultiples _)).trans <|
    (Int.castAddHom (ZMod n)).lif

中文:
定义 lift
  签名: : { f : 整数 ->+ A // f n = 0 } ≃ (ZMod n ->+ A)
  定义体: (Equiv.subtypeEquivRight <| by
        intro f
        rw [ker_intCastAddHom]
        constructor
        · rintro hf _ ⟨x, rfl⟩
          simp only [f.map_zsmul, zsmul_zero, f.mem_ker, hf]
        · intro h
          exact h (AddSubgroup.mem_zmultiples _)).trans <|
    (Int.castAddHom (ZMod n)).lif

Depends on / 依赖: AddSubgroup, AddSubgroup.mem_zmultiples, Equiv.subtypeEquivRight, Int.castAddHom, castAddHom, f.map_zsmul, f.mem_ker, intCast_zmod_cast, ker_intCastAddHom, liftOfRightInverse, map_zsmul, mem_ker, mem_zmultiples, subtypeEquivRight, zsmul_zero
-/
def lift : { f : Int ->+ A // f n = 0 } ≃ (ZMod n ->+ A) :=
  (Equiv.subtypeEquivRight <| by
        intro f
        rw [ker_intCastAddHom]
        constructor
        · rintro hf _ ⟨x, rfl⟩
          simp only [f.map_zsmul, zsmul_zero, f.mem_ker, hf]
        · intro h
          exact h (AddSubgroup.mem_zmultiples _)).trans <|
    (Int.castAddHom (ZMod n)).liftOfRightInverse cast intCast_zmod_cast

variable (f : { f : Int ->+ A // f n = 0 })

@[simp]
/--
theorem `lift_coe` / 定理 `lift_coe`

English:
theorem lift_coe
  given: (x : Int)
  statement: lift n f (x : ZMod n) = f.val x
  proof: AddMonoidHom.liftOfRightInverse_comp_apply _ _ (fun _ => intCast_zmod_cast _) _ _

中文:
定理 lift_coe
  条件: (x : 整数)
  结论: lift n f (x : ZMod n) = f.val x
  证明: AddMonoidHom.liftOfRightInverse_comp_apply _ _ (fun _ => intCast_zmod_cast _) _ _

Depends on / 依赖: AddMonoidHom, AddMonoidHom.liftOfRightInverse_comp_apply, intCast_zmod_cast, liftOfRightInverse_comp_apply
-/
theorem lift_coe (x : Int) : lift n f (x : ZMod n) = f.val x :=
  AddMonoidHom.liftOfRightInverse_comp_apply _ _ (fun _ => intCast_zmod_cast _) _ _

/--
theorem `lift_castAddHom` / 定理 `lift_castAddHom`

English:
theorem lift_castAddHom
  given: (x : Int)
  statement: lift n f (Int.castAddHom (ZMod n) x) = f.1 x
  proof: AddMonoidHom.liftOfRightInverse_comp_apply _ _ (fun _ => intCast_zmod_cast _) _ _

@[simp]

中文:
定理 lift_castAddHom
  条件: (x : 整数)
  结论: lift n f (整数.castAddHom (ZMod n) x) = f.1 x
  证明: AddMonoidHom.liftOfRightInverse_comp_apply _ _ (fun _ => intCast_zmod_cast _) _ _

@[simp]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.liftOfRightInverse_comp_apply, intCast_zmod_cast, liftOfRightInverse_comp_apply
-/
theorem lift_castAddHom (x : Int) : lift n f (Int.castAddHom (ZMod n) x) = f.1 x :=
  AddMonoidHom.liftOfRightInverse_comp_apply _ _ (fun _ => intCast_zmod_cast _) _ _

@[simp]
/--
theorem `lift_comp_coe` / 定理 `lift_comp_coe`

English:
theorem lift_comp_coe
  statement: ZMod.lift n f ∘ ((↑) : Int -> _) = f
  proof: funext lift_coe _ _

@[simp]

中文:
定理 lift_comp_coe
  结论: ZMod.lift n f ∘ ((↑) : 整数 -> _) = f
  证明: funext lift_coe _ _

@[simp]

Depends on / 依赖: lift_coe
-/
theorem lift_comp_coe : ZMod.lift n f ∘ ((↑) : Int -> _) = f :=
funext lift_coe _ _

@[simp]
/--
theorem `lift_comp_castAddHom` / 定理 `lift_comp_castAddHom`

English:
theorem lift_comp_castAddHom
  statement: (ZMod.lift n f).comp (Int.castAddHom (ZMod n)) = f
  proof: AddMonoidHom.ext lift_castAddHom _ _

中文:
定理 lift_comp_castAddHom
  结论: (ZMod.lift n f).comp (整数.castAddHom (ZMod n)) = f
  证明: AddMonoidHom.ext lift_castAddHom _ _

Depends on / 依赖: AddMonoidHom, AddMonoidHom.ext, lift_castAddHom
-/
theorem lift_comp_castAddHom : (ZMod.lift n f).comp (Int.castAddHom (ZMod n)) = f :=
AddMonoidHom.ext lift_castAddHom _ _

/--
lemma `lift_injective` / 引理 `lift_injective`

English:
lemma lift_injective
  given: {f : {f : Int ->+ A // f n = 0}}
  proof: by
  simp only [← AddMonoidHom.ker_eq_bot_iff, eq_bot_iff, SetLike.le_def,
    ZMod.intCast_surjective.forall, ZMod.lift_coe, AddMonoidHom.mem_ker, AddSubgroup.mem_bot]

中文:
引理 lift_injective
  条件: {f : {f : 整数 ->+ A // f n = 0}}
  证明: by
  simp only [← AddMonoidHom.ker_eq_bot_iff, eq_bot_iff, SetLike.le_def,
    ZMod.intCast_surjective.forall, ZMod.lift_coe, AddMonoidHom.mem_ker, AddSubgroup.mem_bot]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.ker_eq_bot_iff, AddMonoidHom.mem_ker, AddSubgroup, AddSubgroup.mem_bot, SetLike, SetLike.le_def, ZMod.intCast_surjective.forall, ZMod.lift_coe, eq_bot_iff, intCast_surjective, ker_eq_bot_iff, le_def, lift_coe, mem_bot, mem_ker
-/
lemma lift_injective {f : {f : Int ->+ A // f n = 0}} :
    Injective (lift n f) ↔ forall m, f.1 m = 0 -> (m : ZMod n) = 0 := by
  simp only [← AddMonoidHom.ker_eq_bot_iff, eq_bot_iff, SetLike.le_def,
    ZMod.intCast_surjective.forall, ZMod.lift_coe, AddMonoidHom.mem_ker, AddSubgroup.mem_bot]

end lift

end ZMod

/-!
### Groups of bounded torsion

For `G` a group and `n` a natural number, `G` having torsion dividing `n`
(`∀ x : G, n • x = 0`) can be derived from `Module R G` where `R` has characteristic dividing `n`.

It is however painful to have the API for such groups `G` stated in this generality, as `R` does not
appear anywhere in the lemmas' return type. Instead of writing the API in terms of a general `R`, we
therefore specialise to the canonical ring of order `n`, namely `ZMod n`.

This spelling `Module (ZMod n) G` has the extra advantage of providing the canonical action by
`ZMod n`. It is however Type-valued, so we might want to acquire a Prop-valued version in the
future.
-/

section Module
variable {n : Nat} {S G : Type*} [AddCommGroup G] [SetLike S G] [AddSubgroupClass S G] {K : S} {x : G}

section general
variable [Module (ZMod n) G] {x : G}

/--
lemma `zmod_smul_mem` / 引理 `zmod_smul_mem`

English:
lemma zmod_smul_mem
  given: (hx : x in K)
  statement: forall a : ZMod n, a • x in K
  proof: by
  simpa [ZMod.forall, Int.cast_smul_eq_zsmul] using zsmul_mem hx

中文:
引理 zmod_smul_mem
  条件: (hx : x in K)
  结论: 对任意 a : ZMod n, a • x in K
  证明: by
  simpa [ZMod.forall, Int.cast_smul_eq_zsmul] using zsmul_mem hx

Depends on / 依赖: Int.cast_smul_eq_zsmul, ZMod.forall, cast_smul_eq_zsmul, zsmul_mem
-/
lemma zmod_smul_mem (hx : x in K) : forall a : ZMod n, a • x in K := by
  simpa [ZMod.forall, Int.cast_smul_eq_zsmul] using zsmul_mem hx

/--
lemma `smulMemClass` / 引理 `smulMemClass`

English:
lemma smulMemClass
  statement: SMulMemClass S (ZMod n) G where smul_mem _ _ {_x} hx
  proof: zmod_smul_mem hx _

中文:
引理 smulMemClass
  结论: SMulMemClass S (ZMod n) G where smul_mem _ _ {_x} hx
  证明: zmod_smul_mem hx _

Depends on / 依赖: zmod_smul_mem
-/
lemma smulMemClass : SMulMemClass S (ZMod n) G where smul_mem _ _ {_x} hx := zmod_smul_mem hx _

namespace AddSubgroupClass

/--
Instance `instZModSMul` / 实例 `instZModSMul`

English:
instance instZModSMul
  signature: : SMul (ZMod n) K where smul a x
  body: ⟨a • x, zmod_smul_mem x.2 _⟩

中文:
实例 instZModSMul
  签名: : SMul (ZMod n) K where smul a x
  定义体: ⟨a • x, zmod_smul_mem x.2 _⟩

Depends on / 依赖: zmod_smul_mem
-/
instance instZModSMul : SMul (ZMod n) K where smul a x := ⟨a • x, zmod_smul_mem x.2 _⟩

/--
lemma `coe_zmod_smul` / 引理 `coe_zmod_smul`

English:
lemma coe_zmod_smul
  given: (a : ZMod n) (x : K)
  statement: ↑(a • x) = (a • x : G)
  proof: rfl

中文:
引理 coe_zmod_smul
  条件: (a : ZMod n) (x : K)
  结论: ↑(a • x) = (a • x : G)
  证明: rfl
-/
@[simp, norm_cast] lemma coe_zmod_smul (a : ZMod n) (x : K) : ↑(a • x) = (a • x : G) := rfl

/--
Instance `instZModModule` / 实例 `instZModModule`

English:
instance instZModModule
  signature: : Module (ZMod n) K
  body: fast_instance%
  Subtype.coe_injective.module _ (AddSubmonoidClass.subtype K) coe_zmod_smul

中文:
实例 instZModModule
  签名: : Module (ZMod n) K
  定义体: fast_instance%
  Subtype.coe_injective.module _ (AddSubmonoidClass.subtype K) coe_zmod_smul

Depends on / 依赖: fast_instance
-/
instance instZModModule : Module (ZMod n) K := fast_instance%
  Subtype.coe_injective.module _ (AddSubmonoidClass.subtype K) coe_zmod_smul

end AddSubgroupClass

variable (n)

/--
lemma `ZModModule.char_nsmul_eq_zero` / 引理 `ZModModule.char_nsmul_eq_zero`

English:
lemma ZModModule.char_nsmul_eq_zero
  given: (x : G)
  statement: n • x = 0
  proof: by
  simp [← Nat.cast_smul_eq_nsmul (ZMod n)]

中文:
引理 ZModModule.char_nsmul_eq_zero
  条件: (x : G)
  结论: n • x = 0
  证明: by
  simp [← Nat.cast_smul_eq_nsmul (ZMod n)]

Depends on / 依赖: Nat.cast_smul_eq_nsmul, cast_smul_eq_nsmul
-/
lemma ZModModule.char_nsmul_eq_zero (x : G) : n • x = 0 := by
  simp [← Nat.cast_smul_eq_nsmul (ZMod n)]

variable (G) in
/--
lemma `ZModModule.char_ne_one` / 引理 `ZModModule.char_ne_one`

English:
lemma ZModModule.char_ne_one
  given: [Nontrivial G]
  statement: n != 1
  proof: by
  rintro rfl
  obtain ⟨x, hx⟩ := exists_ne (0 : G)
exact hx by simpa using char_nsmul_eq_zero 1 x

中文:
引理 ZModModule.char_ne_one
  条件: [Nontrivial G]
  结论: n != 1
  证明: by
  rintro rfl
  obtain ⟨x, hx⟩ := exists_ne (0 : G)
exact hx by simpa using char_nsmul_eq_zero 1 x

Depends on / 依赖: char_nsmul_eq_zero, exists_ne
-/
lemma ZModModule.char_ne_one [Nontrivial G] : n != 1 := by
  rintro rfl
  obtain ⟨x, hx⟩ := exists_ne (0 : G)
exact hx by simpa using char_nsmul_eq_zero 1 x

variable (G) in
/--
lemma `ZModModule.two_le_char` / 引理 `ZModModule.two_le_char`

English:
lemma ZModModule.two_le_char
  given: [NeZero n] [Nontrivial G]
  statement: 2 <= n
  proof: by
  have := NeZero.ne n
  have := char_ne_one n G
  lia

中文:
引理 ZModModule.two_le_char
  条件: [NeZero n] [Nontrivial G]
  结论: 2 <= n
  证明: by
  have := NeZero.ne n
  have := char_ne_one n G
  lia

Depends on / 依赖: NeZero, NeZero.ne, char_ne_one
-/
lemma ZModModule.two_le_char [NeZero n] [Nontrivial G] : 2 <= n := by
  have := NeZero.ne n
  have := char_ne_one n G
  lia

/--
lemma `ZModModule.periodicPts_add_left` / 引理 `ZModModule.periodicPts_add_left`

English:
lemma ZModModule.periodicPts_add_left
  given: [NeZero n] (x : G)
  statement: periodicPts (x + ·) = .univ
  proof: Set.eq_univ_of_forall fun y => ⟨n, NeZero.pos n, by
    simpa [char_nsmul_eq_zero, IsPeriodicPt] using! isFixedPt_id _⟩

中文:
引理 ZModModule.periodicPts_add_left
  条件: [NeZero n] (x : G)
  结论: periodicPts (x + ·) = .univ
  证明: Set.eq_univ_of_forall fun y => ⟨n, NeZero.pos n, by
    simpa [char_nsmul_eq_zero, IsPeriodicPt] using! isFixedPt_id _⟩

Depends on / 依赖: IsPeriodicPt, NeZero, NeZero.pos, Set.eq_univ_of_forall, char_nsmul_eq_zero, eq_univ_of_forall, isFixedPt_id
-/
lemma ZModModule.periodicPts_add_left [NeZero n] (x : G) : periodicPts (x + ·) = .univ :=
  Set.eq_univ_of_forall fun y => ⟨n, NeZero.pos n, by
    simpa [char_nsmul_eq_zero, IsPeriodicPt] using! isFixedPt_id _⟩

end general

section two
variable [Module (ZMod 2) G]

/--
lemma `ZModModule.add_self` / 引理 `ZModModule.add_self`

English:
lemma ZModModule.add_self
  given: (x : G)
  statement: x + x = 0
  proof: by
  simpa [two_nsmul] using char_nsmul_eq_zero 2 x

中文:
引理 ZModModule.add_self
  条件: (x : G)
  结论: x + x = 0
  证明: by
  simpa [two_nsmul] using char_nsmul_eq_zero 2 x

Depends on / 依赖: char_nsmul_eq_zero, two_nsmul
-/
lemma ZModModule.add_self (x : G) : x + x = 0 := by
  simpa [two_nsmul] using char_nsmul_eq_zero 2 x

/--
lemma `ZModModule.neg_eq_self` / 引理 `ZModModule.neg_eq_self`

English:
lemma ZModModule.neg_eq_self
  given: (x : G)
  statement: -x = x
  proof: by simp [add_self, eq_comm, ← sub_eq_zero]

中文:
引理 ZModModule.neg_eq_self
  条件: (x : G)
  结论: -x = x
  证明: by simp [add_self, eq_comm, ← sub_eq_zero]

Depends on / 依赖: add_self, eq_comm, sub_eq_zero
-/
lemma ZModModule.neg_eq_self (x : G) : -x = x := by simp [add_self, eq_comm, ← sub_eq_zero]

/--
lemma `ZModModule.sub_eq_add` / 引理 `ZModModule.sub_eq_add`

English:
lemma ZModModule.sub_eq_add
  given: (x y : G)
  statement: x - y = x + y
  proof: by simp [neg_eq_self, sub_eq_add_neg]

中文:
引理 ZModModule.sub_eq_add
  条件: (x y : G)
  结论: x - y = x + y
  证明: by simp [neg_eq_self, sub_eq_add_neg]

Depends on / 依赖: neg_eq_self, sub_eq_add_neg
-/
lemma ZModModule.sub_eq_add (x y : G) : x - y = x + y := by simp [neg_eq_self, sub_eq_add_neg]

/--
lemma `ZModModule.add_add_add_cancel` / 引理 `ZModModule.add_add_add_cancel`

English:
lemma ZModModule.add_add_add_cancel
  given: (x y z : G)
  statement: (x + y) + (y + z) = x + z
  proof: by
  simpa [sub_eq_add] using sub_add_sub_cancel x y z

中文:
引理 ZModModule.add_add_add_cancel
  条件: (x y z : G)
  结论: (x + y) + (y + z) = x + z
  证明: by
  simpa [sub_eq_add] using sub_add_sub_cancel x y z

Depends on / 依赖: sub_add_sub_cancel, sub_eq_add
-/
lemma ZModModule.add_add_add_cancel (x y z : G) : (x + y) + (y + z) = x + z := by
  simpa [sub_eq_add] using sub_add_sub_cancel x y z

end two
end Module

section Group
variable {α : Type*} [Group α] {n : Nat}

@[to_additive (attr := simp) nsmul_zmod_val_inv_nsmul]
/--
lemma `pow_zmod_val_inv_pow` / 引理 `pow_zmod_val_inv_pow`

English:
lemma pow_zmod_val_inv_pow
  given: (hn : (Nat.card α).gcd n = 1) (a : α)
  proof: by
  replace hn : (Nat.card α).Coprime n := hn
  rw [← pow_mul']; rw [← pow_mod_natCard]; rw [← ZMod.val_natCast]; rw [Nat.cast_mul]; rw [ZMod.mul_val_inv hn.symm]; rw [ZMod.val_one_eq_one_mod]; rw [pow_mod_natCard]; rw [pow_one]

@[to_additive (attr := simp) zmod_val_inv_nsmul_nsmul]

中文:
引理 pow_zmod_val_inv_pow
  条件: (hn : (自然数.card α).gcd n = 1) (a : α)
  证明: by
  replace hn : (Nat.card α).Coprime n := hn
  rw [← pow_mul']; rw [← pow_mod_natCard]; rw [← ZMod.val_natCast]; rw [Nat.cast_mul]; rw [ZMod.mul_val_inv hn.symm]; rw [ZMod.val_one_eq_one_mod]; rw [pow_mod_natCard]; rw [pow_one]

@[to_additive (attr := simp) zmod_val_inv_nsmul_nsmul]

Depends on / 依赖: Coprime, Nat.card, Nat.cast_mul, ZMod.mul_val_inv, ZMod.val_natCast, ZMod.val_one_eq_one_mod, cast_mul, hn.symm, mul_val_inv, pow_mod_natCard, pow_mul, pow_one, replace, val_natCast, val_one_eq_one_mod
-/
lemma pow_zmod_val_inv_pow (hn : (Nat.card α).gcd n = 1) (a : α) :
    (a ^ (n⁻¹ : ZMod (Nat.card α)).val) ^ n = a := by
  replace hn : (Nat.card α).Coprime n := hn
  rw [← pow_mul']; rw [← pow_mod_natCard]; rw [← ZMod.val_natCast]; rw [Nat.cast_mul]; rw [ZMod.mul_val_inv hn.symm]; rw [ZMod.val_one_eq_one_mod]; rw [pow_mod_natCard]; rw [pow_one]

@[to_additive (attr := simp) zmod_val_inv_nsmul_nsmul]
/--
lemma `pow_pow_zmod_val_inv` / 引理 `pow_pow_zmod_val_inv`

English:
lemma pow_pow_zmod_val_inv
  given: (hn : (Nat.card α).gcd n = 1) (a : α)
  proof: by rw [pow_right_comm, pow_zmod_val_inv_pow hn]

中文:
引理 pow_pow_zmod_val_inv
  条件: (hn : (自然数.card α).gcd n = 1) (a : α)
  证明: by rw [pow_right_comm, pow_zmod_val_inv_pow hn]

Depends on / 依赖: pow_right_comm, pow_zmod_val_inv_pow
-/
lemma pow_pow_zmod_val_inv (hn : (Nat.card α).gcd n = 1) (a : α) :
    (a ^ n) ^ (n⁻¹ : ZMod (Nat.card α)).val = a := by rw [pow_right_comm, pow_zmod_val_inv_pow hn]

end Group

open ZMod

/--
lemma `Nat.range_mul_add` / 引理 `Nat.range_mul_add`

English:
lemma Nat.range_mul_add
  given: (m k : Nat)
  proof: by
  ext n
  simp only [Set.mem_range, Set.mem_ofPred_eq]
  conv => enter [1, 1, y]; rw [add_comm, eq_comm]
  refine ⟨fun ⟨a, ha⟩ => ⟨?_, le_iff_exists_add.mpr ⟨_, ha⟩⟩, fun ⟨H₁, H₂⟩ => ?_⟩
  · simpa using congr_arg ((↑) : Nat -> ZMod m) ha
  · obtain ⟨a, ha⟩ := le_iff_exists_add.mp H₂
    simp only

中文:
引理 Nat.range_mul_add
  条件: (m k : 自然数)
  证明: by
  ext n
  simp only [Set.mem_range, Set.mem_ofPred_eq]
  conv => enter [1, 1, y]; rw [add_comm, eq_comm]
  refine ⟨fun ⟨a, ha⟩ => ⟨?_, le_iff_exists_add.mpr ⟨_, ha⟩⟩, fun ⟨H₁, H₂⟩ => ?_⟩
  · simpa using congr_arg ((↑) : Nat -> ZMod m) ha
  · obtain ⟨a, ha⟩ := le_iff_exists_add.mp H₂
    simp only

Depends on / 依赖: Nat.cast_add, Set.mem_ofPred_eq, Set.mem_range, ZMod.natCast_eq_zero_iff, add_comm, add_eq_left, cast_add, congr_arg, eq_comm, le_iff_exists_add, le_iff_exists_add.mp, le_iff_exists_add.mpr, mem_ofPred_eq, mem_range, natCast_eq_zero_iff
-/
lemma Nat.range_mul_add (m k : Nat) :
    Set.range (fun n : Nat => m * n + k) = {n : Nat | (n : ZMod m) = k ∧ k <= n} := by
  ext n
  simp only [Set.mem_range, Set.mem_ofPred_eq]
  conv => enter [1, 1, y]; rw [add_comm, eq_comm]
  refine ⟨fun ⟨a, ha⟩ => ⟨?_, le_iff_exists_add.mpr ⟨_, ha⟩⟩, fun ⟨H₁, H₂⟩ => ?_⟩
  · simpa using congr_arg ((↑) : Nat -> ZMod m) ha
  · obtain ⟨a, ha⟩ := le_iff_exists_add.mp H₂
    simp only [ha, Nat.cast_add, add_eq_left, ZMod.natCast_eq_zero_iff] at H₁
    obtain ⟨b, rfl⟩ := H₁
    exact ⟨b, ha⟩

/--
Definition of `Nat.residueClassesEquiv` / `Nat.residueClassesEquiv` 的定义

English:
definition Nat.residueClassesEquiv
  signature: (N : Nat) [NeZero N]
  body: (↑n, n / N)
  invFun p := p.1.val + N * p.2
  left_inv n := by simpa only [val_natCast] using mod_add_div n N
  right_inv p := by
    ext1
    · simp only [add_comm p.1.val, cast_add, cast_mul, natCast_self, zero_mul, natCast_val,
        cast_id', id_eq, zero_add]
    · simp only [add_comm p.1.val,

中文:
定义 Nat.residueClassesEquiv
  签名: (N : 自然数) [NeZero N]
  定义体: (↑n, n / N)
  invFun p := p.1.val + N * p.2
  left_inv n := by simpa only [val_natCast] using mod_add_div n N
  right_inv p := by
    ext1
    · simp only [add_comm p.1.val, cast_add, cast_mul, natCast_self, zero_mul, natCast_val,
        cast_id', id_eq, zero_add]
    · simp only [add_comm p.1.val,
-/
def Nat.residueClassesEquiv (N : Nat) [NeZero N] : Nat ≃ ZMod N × Nat where
  toFun n := (↑n, n / N)
  invFun p := p.1.val + N * p.2
  left_inv n := by simpa only [val_natCast] using mod_add_div n N
  right_inv p := by
    ext1
    · simp only [add_comm p.1.val, cast_add, cast_mul, natCast_self, zero_mul, natCast_val,
        cast_id', id_eq, zero_add]
    · simp only [add_comm p.1.val, mul_add_div (NeZero.pos _),
(Nat.div_eq_zero_iff).2 .inr p.1.val_lt, add_zero]

-- there is a faster proof with Module.toAddMonoidEnd
/--
Instance `ZMod.instSubsingletonModule` / 实例 `ZMod.instSubsingletonModule`

English:
instance ZMod.instSubsingletonModule
  signature: (n : Nat) (M : Type*) [AddCommMonoid M]
  body: by
  obtain _ | n := n
  · exact inferInstanceAs (Subsingleton (Module Int M))
  refine ⟨fun m1 m2 => Module.ext' _ _ fun r m => ?_⟩
  obtain ⟨r, rfl⟩ := ZMod.natCast_zmod_surjective r
  rw [(letI := m1; Nat.cast_smul_eq_nsmul _ r m)]; rw [Nat.cast_smul_eq_nsmul _ r m]

中文:
实例 ZMod.instSubsingletonModule
  签名: (n : 自然数) (M : 类型) [AddCommMonoid M]
  定义体: by
  obtain _ | n := n
  · exact inferInstanceAs (Subsingleton (Module Int M))
  refine ⟨fun m1 m2 => Module.ext' _ _ fun r m => ?_⟩
  obtain ⟨r, rfl⟩ := ZMod.natCast_zmod_surjective r
  rw [(letI := m1; Nat.cast_smul_eq_nsmul _ r m)]; rw [Nat.cast_smul_eq_nsmul _ r m]

Depends on / 依赖: Module, Module.ext, Nat.cast_smul_eq_nsmul, Subsingleton, ZMod.natCast_zmod_surjective, cast_smul_eq_nsmul, natCast_zmod_surjective
-/
instance ZMod.instSubsingletonModule (n : Nat) (M : Type*) [AddCommMonoid M] :
    Subsingleton (Module (ZMod n) M) := by
  obtain _ | n := n
  · exact inferInstanceAs (Subsingleton (Module Int M))
  refine ⟨fun m1 m2 => Module.ext' _ _ fun r m => ?_⟩
  obtain ⟨r, rfl⟩ := ZMod.natCast_zmod_surjective r
  rw [(letI := m1; Nat.cast_smul_eq_nsmul _ r m)]; rw [Nat.cast_smul_eq_nsmul _ r m]
