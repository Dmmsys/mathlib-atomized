/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Logic.Basic

/-!

# Characteristic zero

A ring `R` is called of characteristic zero if every natural number `n` is non-zero when considered
as an element of `R`. Since this definition doesn't mention the multiplicative structure of `R`
except for the existence of `1` in this file characteristic zero is defined for additive monoids
with `1`.

## Main definition

`CharZero` is the typeclass of an additive monoid with one such that the natural homomorphism
from the natural numbers into it is injective.

## TODO

* Unify with `CharP` (possibly using an out-parameter)
-/

public section

/--
Definition of `CharZero` / `CharZero` 的定义

English:
class CharZero
  parameters: (R) [AddMonoidWithOne R]
  axioms and operations (1):
    - cast_injective : Function.Injective (Nat.cast : Nat -> R)

中文:
类 CharZero
  参数: (R) [AddMonoidWithOne R]
  公理与运算 (1 个):
    - cast_injective : Function.Injective (自然数.cast : 自然数 -> R)
-/
class CharZero (R) [AddMonoidWithOne R] : Prop where
  /-- An additive monoid with one has characteristic zero if the canonical map `ℕ → R` is
  injective. -/
  cast_injective : Function.Injective (Nat.cast : Nat -> R)

variable {R : Type*}

/--
theorem `charZero_of_inj_zero` / 定理 `charZero_of_inj_zero`

English:
theorem charZero_of_inj_zero
  given: [AddGroupWithOne R] (H : forall n : Nat, (n : R) = 0 -> n = 0)
  proof: ⟨@fun m n h => by
    induction m generalizing n with
    | zero => rw [H n]; rw [← h, Nat.cast_zero]
    | succ m ih =>
      cases n
      · apply H; rw [h, Nat.cast_zero]
      · simp only [Nat.cast_succ, add_right_cancel_iff] at h; rwa [ih]⟩

中文:
定理 charZero_of_inj_zero
  条件: [AddGroupWithOne R] (H : 对任意 n : 自然数, (n : R) = 0 -> n = 0)
  证明: ⟨@fun m n h => by
    induction m generalizing n with
    | zero => rw [H n]; rw [← h, Nat.cast_zero]
    | succ m ih =>
      cases n
      · apply H; rw [h, Nat.cast_zero]
      · simp only [Nat.cast_succ, add_right_cancel_iff] at h; rwa [ih]⟩

Depends on / 依赖: Nat.cast_succ, Nat.cast_zero, add_right_cancel_iff, cast_succ, cast_zero, generalizing
-/
theorem charZero_of_inj_zero [AddGroupWithOne R] (H : forall n : Nat, (n : R) = 0 -> n = 0) :
    CharZero R :=
  ⟨@fun m n h => by
    induction m generalizing n with
    | zero => rw [H n]; rw [← h, Nat.cast_zero]
    | succ m ih =>
      cases n
      · apply H; rw [h, Nat.cast_zero]
      · simp only [Nat.cast_succ, add_right_cancel_iff] at h; rwa [ih]⟩

namespace Nat

variable [AddMonoidWithOne R] [CharZero R]

/--
theorem `cast_injective` / 定理 `cast_injective`

English:
theorem cast_injective
  statement: Function.Injective (Nat.cast : Nat -> R)
  proof: CharZero.cast_injective

@[simp, norm_cast]

中文:
定理 cast_injective
  结论: Function.Injective (自然数.cast : 自然数 -> R)
  证明: CharZero.cast_injective

@[simp, norm_cast]

Depends on / 依赖: CharZero, CharZero.cast_injective, cast_injective
-/
theorem cast_injective : Function.Injective (Nat.cast : Nat -> R) :=
  CharZero.cast_injective

@[simp, norm_cast]
/--
theorem `cast_inj` / 定理 `cast_inj`

English:
theorem cast_inj
  given: {m n : Nat}
  statement: (m : R) = n ↔ m = n
  proof: cast_injective.eq_iff

@[simp, norm_cast]

中文:
定理 cast_inj
  条件: {m n : 自然数}
  结论: (m : R) = n ↔ m = n
  证明: cast_injective.eq_iff

@[simp, norm_cast]

Depends on / 依赖: cast_injective, cast_injective.eq_iff, eq_iff
-/
theorem cast_inj {m n : Nat} : (m : R) = n ↔ m = n :=
  cast_injective.eq_iff

@[simp, norm_cast]
/--
theorem `cast_eq_zero` / 定理 `cast_eq_zero`

English:
theorem cast_eq_zero
  given: {n : Nat}
  statement: (n : R) = 0 ↔ n = 0
  proof: by rw [← cast_zero, cast_inj]

@[norm_cast]

中文:
定理 cast_eq_zero
  条件: {n : 自然数}
  结论: (n : R) = 0 ↔ n = 0
  证明: by rw [← cast_zero, cast_inj]

@[norm_cast]

Depends on / 依赖: cast_inj, cast_zero
-/
theorem cast_eq_zero {n : Nat} : (n : R) = 0 ↔ n = 0 := by rw [← cast_zero, cast_inj]

@[norm_cast]
/--
theorem `cast_ne_zero` / 定理 `cast_ne_zero`

English:
theorem cast_ne_zero
  given: {n : Nat}
  statement: (n : R) != 0 ↔ n != 0
  proof: not_congr cast_eq_zero

中文:
定理 cast_ne_zero
  条件: {n : 自然数}
  结论: (n : R) != 0 ↔ n != 0
  证明: not_congr cast_eq_zero

Depends on / 依赖: cast_eq_zero, not_congr
-/
theorem cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0 :=
  not_congr cast_eq_zero

/--
theorem `cast_add_one_ne_zero` / 定理 `cast_add_one_ne_zero`

English:
theorem cast_add_one_ne_zero
  given: (n : Nat)
  statement: (n + 1 : R) != 0
  proof: mod_cast n.succ_ne_zero

@[simp, norm_cast]

中文:
定理 cast_add_one_ne_zero
  条件: (n : 自然数)
  结论: (n + 1 : R) != 0
  证明: mod_cast n.succ_ne_zero

@[simp, norm_cast]

Depends on / 依赖: mod_cast, n.succ_ne_zero, succ_ne_zero
-/
theorem cast_add_one_ne_zero (n : Nat) : (n + 1 : R) != 0 :=
  mod_cast n.succ_ne_zero

@[simp, norm_cast]
/--
theorem `cast_eq_one` / 定理 `cast_eq_one`

English:
theorem cast_eq_one
  given: {n : Nat}
  statement: (n : R) = 1 ↔ n = 1
  proof: by rw [← cast_one, cast_inj]

@[norm_cast]

中文:
定理 cast_eq_one
  条件: {n : 自然数}
  结论: (n : R) = 1 ↔ n = 1
  证明: by rw [← cast_one, cast_inj]

@[norm_cast]

Depends on / 依赖: cast_inj, cast_one
-/
theorem cast_eq_one {n : Nat} : (n : R) = 1 ↔ n = 1 := by rw [← cast_one, cast_inj]

@[norm_cast]
/--
theorem `cast_ne_one` / 定理 `cast_ne_one`

English:
theorem cast_ne_one
  given: {n : Nat}
  statement: (n : R) != 1 ↔ n != 1
  proof: cast_eq_one.not

中文:
定理 cast_ne_one
  条件: {n : 自然数}
  结论: (n : R) != 1 ↔ n != 1
  证明: cast_eq_one.not

Depends on / 依赖: cast_eq_one, cast_eq_one.not
-/
theorem cast_ne_one {n : Nat} : (n : R) != 1 ↔ n != 1 :=
  cast_eq_one.not

end Nat

namespace OfNat

variable [AddMonoidWithOne R] [CharZero R]

/--
lemma `ofNat_ne_zero` / 引理 `ofNat_ne_zero`

English:
lemma ofNat_ne_zero
  given: (n : Nat) [n.AtLeastTwo]
  statement: (ofNat(n) : R) != 0
  proof: Nat.cast_ne_zero.2 (NeZero.ne n)

中文:
引理 ofNat_ne_zero
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: (of自然数(n) : R) != 0
  证明: Nat.cast_ne_zero.2 (NeZero.ne n)
-/
@[simp] lemma ofNat_ne_zero (n : Nat) [n.AtLeastTwo] : (ofNat(n) : R) != 0 :=
  Nat.cast_ne_zero.2 (NeZero.ne n)

/--
lemma `zero_ne_ofNat` / 引理 `zero_ne_ofNat`

English:
lemma zero_ne_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  statement: 0 != (ofNat(n) : R)
  proof: (ofNat_ne_zero n).symm

中文:
引理 zero_ne_ofNat
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: 0 != (of自然数(n) : R)
  证明: (ofNat_ne_zero n).symm
-/
@[simp] lemma zero_ne_ofNat (n : Nat) [n.AtLeastTwo] : 0 != (ofNat(n) : R) :=
  (ofNat_ne_zero n).symm

/--
lemma `ofNat_ne_one` / 引理 `ofNat_ne_one`

English:
lemma ofNat_ne_one
  given: (n : Nat) [n.AtLeastTwo]
  statement: (ofNat(n) : R) != 1
  proof: Nat.cast_ne_one.2 (Nat.AtLeastTwo.ne_one)

中文:
引理 ofNat_ne_one
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: (of自然数(n) : R) != 1
  证明: Nat.cast_ne_one.2 (Nat.AtLeastTwo.ne_one)
-/
@[simp] lemma ofNat_ne_one (n : Nat) [n.AtLeastTwo] : (ofNat(n) : R) != 1 :=
  Nat.cast_ne_one.2 (Nat.AtLeastTwo.ne_one)

/--
lemma `one_ne_ofNat` / 引理 `one_ne_ofNat`

English:
lemma one_ne_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  statement: (1 : R) != ofNat(n)
  proof: (ofNat_ne_one n).symm

中文:
引理 one_ne_ofNat
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: (1 : R) != of自然数(n)
  证明: (ofNat_ne_one n).symm
-/
@[simp] lemma one_ne_ofNat (n : Nat) [n.AtLeastTwo] : (1 : R) != ofNat(n) :=
  (ofNat_ne_one n).symm

/--
lemma `ofNat_eq_ofNat` / 引理 `ofNat_eq_ofNat`

English:
lemma ofNat_eq_ofNat
  given: {m n : Nat} [m.AtLeastTwo] [n.AtLeastTwo]
  proof: Nat.cast_inj

中文:
引理 ofNat_eq_ofNat
  条件: {m n : 自然数} [m.AtLeastTwo] [n.AtLeastTwo]
  证明: Nat.cast_inj
-/
@[simp] lemma ofNat_eq_ofNat {m n : Nat} [m.AtLeastTwo] [n.AtLeastTwo] :
    (ofNat(m) : R) = ofNat(n) ↔ (ofNat m : Nat) = ofNat n :=
  Nat.cast_inj

end OfNat

namespace NeZero

/--
Instance `charZero` / 实例 `charZero`

English:
instance charZero
  signature: {M} {n : Nat} [NeZero n] [AddMonoidWithOne M] [CharZero M]
  body: ⟨Nat.cast_ne_zero.mpr out⟩

中文:
实例 charZero
  签名: {M} {n : 自然数} [NeZero n] [AddMonoidWithOne M] [CharZero M]
  定义体: ⟨Nat.cast_ne_zero.mpr out⟩

Depends on / 依赖: Nat.cast_ne_zero.mpr, cast_ne_zero
-/
instance charZero {M} {n : Nat} [NeZero n] [AddMonoidWithOne M] [CharZero M] : NeZero (n : M) :=
  ⟨Nat.cast_ne_zero.mpr out⟩

/--
Instance `charZero_one` / 实例 `charZero_one`

English:
instance charZero_one
  signature: {M} [AddMonoidWithOne M] [CharZero M]
  body: by
    rw [← Nat.cast_one]; rw [Nat.cast_ne_zero]
    trivial

中文:
实例 charZero_one
  签名: {M} [AddMonoidWithOne M] [CharZero M]
  定义体: by
    rw [← Nat.cast_one]; rw [Nat.cast_ne_zero]
    trivial

Depends on / 依赖: Nat.cast_ne_zero, Nat.cast_one, cast_ne_zero, cast_one
-/
instance charZero_one {M} [AddMonoidWithOne M] [CharZero M] : NeZero (1 : M) where
  out := by
    rw [← Nat.cast_one]; rw [Nat.cast_ne_zero]
    trivial

/--
Instance `charZero_ofNat` / 实例 `charZero_ofNat`

English:
instance charZero_ofNat
  signature: {M} {n : Nat} [n.AtLeastTwo] [AddMonoidWithOne M] [CharZero M]
  body: ⟨OfNat.ofNat_ne_zero n⟩

中文:
实例 charZero_ofNat
  签名: {M} {n : 自然数} [n.AtLeastTwo] [AddMonoidWithOne M] [CharZero M]
  定义体: ⟨OfNat.ofNat_ne_zero n⟩

Depends on / 依赖: OfNat.ofNat_ne_zero, ofNat_ne_zero
-/
instance charZero_ofNat {M} {n : Nat} [n.AtLeastTwo] [AddMonoidWithOne M] [CharZero M] :
    NeZero (OfNat.ofNat n : M) :=
  ⟨OfNat.ofNat_ne_zero n⟩

end NeZero
