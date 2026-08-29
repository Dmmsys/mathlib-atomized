/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Harun Khan, Alex Keizer
-/
module

public import Mathlib.Algebra.Ring.InjSurj
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Data.Int.Cast.Lemmas

/-!
# Basic Theorems About Bitvectors

This file contains theorems about bitvectors which can only be stated in Mathlib or downstream
because they refer to other notions defined in Mathlib.

Please do not extend this file further: material about BitVec needed in downstream projects
can either be PR'd to Lean, or kept downstream if it also relies on Mathlib.
-/

@[expose] public section

namespace BitVec

variable {w : Nat}

-- TODO: move to the Lean4 repository.
open Fin.CommRing in
/--
theorem `ofFin_intCast` / 定理 `ofFin_intCast`

English:
theorem ofFin_intCast
  given: (z : Int)
  statement: ofFin (z : Fin (2 ^ w)) = ↑z
  proof: by
  cases w
  case zero =>
    simp only [eq_nil]
  case succ w =>
    apply BitVec.eq_of_toInt_eq
    rw [toInt_ofFin]; rw [Fin.val_intCast]; rw [Int.natCast_pow]; rw [Nat.cast_ofNat]; rw [Int.ofNat_toNat]; rw [toInt_intCast]
    rw [Int.max_eq_left]
    · have h : (2 ^ (w + 1) : Int) = (2 ^ (w + 1) : Nat) := by simp
      rw [h]; rw [Int.emod_bmod]
    · omega

中文:
定理 ofFin_intCast
  条件: (z : 整数)
  结论: ofFin (z : 有限集 (2 ^ w)) = ↑z
  证明: by
  cases w
  case zero =>
    simp only [eq_nil]
  case succ w =>
    apply BitVec.eq_of_toInt_eq
    rw [toInt_ofFin]; rw [Fin.val_intCast]; rw [Int.natCast_pow]; rw [Nat.cast_ofNat]; rw [Int.ofNat_toNat]; rw [toInt_intCast]
    rw [Int.max_eq_left]
    · have h : (2 ^ (w + 1) : Int) = (2 ^ (w + 1) : Nat) := by simp
      rw [h]; rw [Int.emod_bmod]
    · omega

Depends on / 依赖: BitVec, BitVec.eq_of_toInt_eq, Fin.val_intCast, Int.emod_bmod, Int.max_eq_left, Int.natCast_pow, Int.ofNat_toNat, Nat.cast_ofNat, cast_ofNat, emod_bmod, eq_nil, eq_of_toInt_eq, max_eq_left, natCast_pow, ofNat_toNat, toInt_intCast, toInt_ofFin, val_intCast
-/
theorem ofFin_intCast (z : Int) : ofFin (z : Fin (2 ^ w)) = ↑z := by
  cases w
  case zero =>
    simp only [eq_nil]
  case succ w =>
    apply BitVec.eq_of_toInt_eq
    rw [toInt_ofFin]; rw [Fin.val_intCast]; rw [Int.natCast_pow]; rw [Nat.cast_ofNat]; rw [Int.ofNat_toNat]; rw [toInt_intCast]
    rw [Int.max_eq_left]
    · have h : (2 ^ (w + 1) : Int) = (2 ^ (w + 1) : Nat) := by simp
      rw [h]; rw [Int.emod_bmod]
    · omega

open Fin.CommRing in
/--
theorem `toFin_intCast` / 定理 `toFin_intCast`

English:
theorem toFin_intCast
  given: (z : Int)
  statement: (z : BitVec w).toFin = ↑z
  proof: by
  rw [← ofFin_intCast]

中文:
定理 toFin_intCast
  条件: (z : 整数)
  结论: (z : BitVec w).toFin = ↑z
  证明: by
  rw [← ofFin_intCast]
-/
@[simp] theorem toFin_intCast (z : Int) : (z : BitVec w).toFin = ↑z := by
  rw [← ofFin_intCast]


/--
theorem `toNat_injective` / 定理 `toNat_injective`

English:
theorem toNat_injective
  given: {n : Nat}
  statement: Function.Injective (BitVec.toNat : BitVec n -> _)

中文:
定理 to自然数_injective
  条件: {n : 自然数}
  结论: 函数.单射 (BitVec.to自然数 : BitVec n -> _)
-/
theorem toNat_injective {n : Nat} : Function.Injective (BitVec.toNat : BitVec n -> _)
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

/--
theorem `toFin_injective` / 定理 `toFin_injective`

English:
theorem toFin_injective
  given: {n : Nat}
  statement: Function.Injective (toFin : BitVec n -> _)

中文:
定理 toFin_injective
  条件: {n : 自然数}
  结论: 函数.单射 (toFin : BitVec n -> _)
-/
theorem toFin_injective {n : Nat} : Function.Injective (toFin : BitVec n -> _)
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

/-!
## Scalar Multiplication and Powers
-/

open Fin.NatCast

/--
lemma `toFin_nsmul` / 引理 `toFin_nsmul`

English:
lemma toFin_nsmul
  given: (n : Nat) (x : BitVec w)
  statement: toFin (n • x) = n • x.toFin
  proof: .trans by toFin_mul _ _
    open scoped Fin.CommRing in
    simp only [natCast_eq_ofNat, toFin_ofNat, Fin.ofNat_eq_cast, nsmul_eq_mul]

中文:
引理 toFin_nsmul
  条件: (n : 自然数) (x : BitVec w)
  结论: toFin (n • x) = n • x.toFin
  证明: .trans by toFin_mul _ _
    open scoped Fin.CommRing in
    simp only [natCast_eq_ofNat, toFin_ofNat, Fin.ofNat_eq_cast, nsmul_eq_mul]

Depends on / 依赖: CommRing, Fin.CommRing, Fin.ofNat_eq_cast, natCast_eq_ofNat, nsmul_eq_mul, ofNat_eq_cast, scoped, toFin_mul, toFin_ofNat
-/
lemma toFin_nsmul (n : Nat) (x : BitVec w) : toFin (n • x) = n • x.toFin :=
.trans by toFin_mul _ _
    open scoped Fin.CommRing in
    simp only [natCast_eq_ofNat, toFin_ofNat, Fin.ofNat_eq_cast, nsmul_eq_mul]

/--
lemma `toFin_zsmul` / 引理 `toFin_zsmul`

English:
lemma toFin_zsmul
  given: (z : Int) (x : BitVec w)
  statement: toFin (z • x) = z • x.toFin
  proof: .trans by toFin_mul _ _
    open scoped Fin.CommRing in
    simp only [zsmul_eq_mul, toFin_intCast]

中文:
引理 toFin_zsmul
  条件: (z : 整数) (x : BitVec w)
  结论: toFin (z • x) = z • x.toFin
  证明: .trans by toFin_mul _ _
    open scoped Fin.CommRing in
    simp only [zsmul_eq_mul, toFin_intCast]

Depends on / 依赖: CommRing, Fin.CommRing, scoped, toFin_intCast, toFin_mul, zsmul_eq_mul
-/
lemma toFin_zsmul (z : Int) (x : BitVec w) : toFin (z • x) = z • x.toFin :=
.trans by toFin_mul _ _
    open scoped Fin.CommRing in
    simp only [zsmul_eq_mul, toFin_intCast]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `toFin_pow` / 引理 `toFin_pow`

English:
lemma toFin_pow
  given: (x : BitVec w) (n : Nat)
  statement: toFin (x ^ n) = x.toFin ^ n
  proof: by
  induction n with
  | zero => simp
  | succ n ih => simp [ih, BitVec.pow_succ]

中文:
引理 toFin_pow
  条件: (x : BitVec w) (n : 自然数)
  结论: toFin (x ^ n) = x.toFin ^ n
  证明: by
  induction n with
  | zero => simp
  | succ n ih => simp [ih, BitVec.pow_succ]

Depends on / 依赖: BitVec, BitVec.pow_succ, pow_succ
-/
lemma toFin_pow (x : BitVec w) (n : Nat) : toFin (x ^ n) = x.toFin ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih, BitVec.pow_succ]

/-!
## Ring
-/

-- Verify that the `HPow` instance from Lean agrees definitionally with the instance via `Monoid`.
example : @instHPow (Fin (2 ^ w)) Nat NPow.toPow = Lean.Grind.Fin.instHPowFinNatOfNeZero := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommSemiring (BitVec w)
  body: open Fin.CommRing in
  toFin_injective.commSemiring _
    toFin_zero
    toFin_one
    toFin_add
    toFin_mul
    toFin_nsmul
    toFin_pow
    toFin_natCast

中文:
实例 :
  签名: 交换半环 (BitVec w)
  定义体: open Fin.CommRing in
  toFin_injective.commSemiring _
    toFin_zero
    toFin_one
    toFin_add
    toFin_mul
    toFin_nsmul
    toFin_pow
    toFin_natCast

Depends on / 依赖: CommRing, Fin.CommRing, commSemiring, toFin_add, toFin_injective, toFin_injective.commSemiring, toFin_mul, toFin_natCast, toFin_nsmul, toFin_one, toFin_pow, toFin_zero
-/
instance : CommSemiring (BitVec w) :=
  open Fin.CommRing in
  toFin_injective.commSemiring _
    toFin_zero
    toFin_one
    toFin_add
    toFin_mul
    toFin_nsmul
    toFin_pow
    toFin_natCast
-- The statement in the new API would be: `n#(k.succ) = ((n / 2)#k).concat (n % 2 != 0)`

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommRing (BitVec w)
  body: open Fin.CommRing in
  toFin_injective.commRing _
    toFin_zero toFin_one toFin_add toFin_mul toFin_neg toFin_sub
    toFin_nsmul toFin_zsmul toFin_pow toFin_natCast toFin_intCast

中文:
实例 :
  签名: 交换环 (BitVec w)
  定义体: open Fin.CommRing in
  toFin_injective.commRing _
    toFin_zero toFin_one toFin_add toFin_mul toFin_neg toFin_sub
    toFin_nsmul toFin_zsmul toFin_pow toFin_natCast toFin_intCast

Depends on / 依赖: CommRing, Fin.CommRing, commRing, toFin_add, toFin_injective, toFin_injective.commRing, toFin_intCast, toFin_mul, toFin_natCast, toFin_neg, toFin_nsmul, toFin_one, toFin_pow, toFin_sub, toFin_zero, toFin_zsmul
-/
instance : CommRing (BitVec w) :=
  open Fin.CommRing in
  toFin_injective.commRing _
    toFin_zero toFin_one toFin_add toFin_mul toFin_neg toFin_sub
    toFin_nsmul toFin_zsmul toFin_pow toFin_natCast toFin_intCast

/-- The ring `BitVec m` is isomorphic to `Fin (2 ^ m)`. -/
@[simps]
/--
Definition of `equivFin` / `equivFin` 的定义

English:
definition equivFin
  signature: {m : Nat}
  body: a.toFin
  invFun a := ofFin a
  map_mul' := toFin_mul
  map_add' := toFin_add

中文:
定义 equivFin
  签名: {m : 自然数}
  定义体: a.toFin
  invFun a := ofFin a
  map_mul' := toFin_mul
  map_add' := toFin_add

Depends on / 依赖: a.toFin
-/
def equivFin {m : Nat} : BitVec m ≃+* Fin (2 ^ m) where
  toFun a := a.toFin
  invFun a := ofFin a
  map_mul' := toFin_mul
  map_add' := toFin_add

end BitVec
