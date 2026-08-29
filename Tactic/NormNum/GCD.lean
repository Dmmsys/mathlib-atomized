/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kyle Miller, Eric Wieser
-/
module

public meta import Mathlib.Data.Int.GCD
public import Mathlib.Algebra.Ring.Divisibility.Basic
public import Mathlib.Tactic.NormNum

/-! # `norm_num` extensions for GCD-adjacent functions

This module defines some `norm_num` extensions for functions such as
`Nat.gcd`, `Nat.lcm`, `Int.gcd`, and `Int.lcm`.

Note that `Nat.coprime` is reducible and defined in terms of `Nat.gcd`, so the `Nat.gcd` extension
also indirectly provides a `Nat.coprime` extension.
-/

public meta section

namespace Mathlib.Meta

namespace NormNum

/--
theorem `int_gcd_helper'` / 定理 `int_gcd_helper'`

English:
theorem int_gcd_helper'
  statement: {d : Nat} {x y : Int} (a b : Int) (h₁ : (d : Int) ∣ x) (h₂ : (d : Int) ∣ y)
  proof: by
  refine Nat.dvd_antisymm ?_ (Int.natCast_dvd_natCast.1 (Int.dvd_coe_gcd h₁ h₂))
  rw [← Int.natCast_dvd_natCast]; rw [← h₃]
  apply dvd_add
  · exact (Int.gcd_dvd_left ..).mul_right _
  · exact (Int.gcd_dvd_right ..).mul_right _

中文:
定理 int_gcd_helper'
  结论: {d : 自然数} {x y : 整数} (a b : 整数) (h₁ : (d : 整数) ∣ x) (h₂ : (d : 整数) ∣ y)
  证明: by
  refine Nat.dvd_antisymm ?_ (Int.natCast_dvd_natCast.1 (Int.dvd_coe_gcd h₁ h₂))
  rw [← Int.natCast_dvd_natCast]; rw [← h₃]
  apply dvd_add
  · exact (Int.gcd_dvd_left ..).mul_right _
  · exact (Int.gcd_dvd_right ..).mul_right _

Depends on / 依赖: Int.dvd_coe_gcd, Int.gcd_dvd_left, Int.gcd_dvd_right, Int.natCast_dvd_natCast, Nat.dvd_antisymm, dvd_add, dvd_antisymm, dvd_coe_gcd, gcd_dvd_left, gcd_dvd_right, mul_right, natCast_dvd_natCast
-/
theorem int_gcd_helper' {d : Nat} {x y : Int} (a b : Int) (h₁ : (d : Int) ∣ x) (h₂ : (d : Int) ∣ y)
    (h₃ : x * a + y * b = d) : Int.gcd x y = d := by
  refine Nat.dvd_antisymm ?_ (Int.natCast_dvd_natCast.1 (Int.dvd_coe_gcd h₁ h₂))
  rw [← Int.natCast_dvd_natCast]; rw [← h₃]
  apply dvd_add
  · exact (Int.gcd_dvd_left ..).mul_right _
  · exact (Int.gcd_dvd_right ..).mul_right _

/--
theorem `nat_gcd_helper_dvd_left` / 定理 `nat_gcd_helper_dvd_left`

English:
theorem nat_gcd_helper_dvd_left
  given: (x y : Nat) (h : y % x = 0)
  statement: Nat.gcd x y = x
  proof: Nat.gcd_eq_left (Nat.dvd_of_mod_eq_zero h)

中文:
定理 nat_gcd_helper_dvd_left
  条件: (x y : 自然数) (h : y % x = 0)
  结论: 自然数.最大公约数 x y = x
  证明: Nat.gcd_eq_left (Nat.dvd_of_mod_eq_zero h)

Depends on / 依赖: Nat.dvd_of_mod_eq_zero, Nat.gcd_eq_left, dvd_of_mod_eq_zero, gcd_eq_left
-/
theorem nat_gcd_helper_dvd_left (x y : Nat) (h : y % x = 0) : Nat.gcd x y = x :=
  Nat.gcd_eq_left (Nat.dvd_of_mod_eq_zero h)

/--
theorem `nat_gcd_helper_dvd_right` / 定理 `nat_gcd_helper_dvd_right`

English:
theorem nat_gcd_helper_dvd_right
  given: (x y : Nat) (h : x % y = 0)
  statement: Nat.gcd x y = y
  proof: Nat.gcd_eq_right (Nat.dvd_of_mod_eq_zero h)

中文:
定理 nat_gcd_helper_dvd_right
  条件: (x y : 自然数) (h : x % y = 0)
  结论: 自然数.最大公约数 x y = y
  证明: Nat.gcd_eq_right (Nat.dvd_of_mod_eq_zero h)

Depends on / 依赖: Nat.dvd_of_mod_eq_zero, Nat.gcd_eq_right, dvd_of_mod_eq_zero, gcd_eq_right
-/
theorem nat_gcd_helper_dvd_right (x y : Nat) (h : x % y = 0) : Nat.gcd x y = y :=
  Nat.gcd_eq_right (Nat.dvd_of_mod_eq_zero h)

/--
theorem `nat_gcd_helper_2` / 定理 `nat_gcd_helper_2`

English:
theorem nat_gcd_helper_2
  statement: (d x y a b : Nat) (hu : x % d = 0) (hv : y % d = 0)
  proof: by
  rw [← Int.gcd_natCast_natCast]
  apply int_gcd_helper' a (-b)
    (Int.natCast_dvd_natCast.mpr (Nat.dvd_of_mod_eq_zero hu))
    (Int.natCast_dvd_natCast.mpr (Nat.dvd_of_mod_eq_zero hv))
  rw [mul_neg]; rw [← sub_eq_add_neg]; rw [sub_eq_iff_eq_add']
  exact mod_cast h

中文:
定理 nat_gcd_helper_2
  结论: (d x y a b : 自然数) (hu : x % d = 0) (hv : y % d = 0)
  证明: by
  rw [← Int.gcd_natCast_natCast]
  apply int_gcd_helper' a (-b)
    (Int.natCast_dvd_natCast.mpr (Nat.dvd_of_mod_eq_zero hu))
    (Int.natCast_dvd_natCast.mpr (Nat.dvd_of_mod_eq_zero hv))
  rw [mul_neg]; rw [← sub_eq_add_neg]; rw [sub_eq_iff_eq_add']
  exact mod_cast h

Depends on / 依赖: Int.gcd_natCast_natCast, Int.natCast_dvd_natCast.mpr, Nat.dvd_of_mod_eq_zero, dvd_of_mod_eq_zero, gcd_natCast_natCast, int_gcd_helper, mod_cast, mul_neg, natCast_dvd_natCast, sub_eq_add_neg, sub_eq_iff_eq_add
-/
theorem nat_gcd_helper_2 (d x y a b : Nat) (hu : x % d = 0) (hv : y % d = 0)
    (h : x * a = y * b + d) : Nat.gcd x y = d := by
  rw [← Int.gcd_natCast_natCast]
  apply int_gcd_helper' a (-b)
    (Int.natCast_dvd_natCast.mpr (Nat.dvd_of_mod_eq_zero hu))
    (Int.natCast_dvd_natCast.mpr (Nat.dvd_of_mod_eq_zero hv))
  rw [mul_neg]; rw [← sub_eq_add_neg]; rw [sub_eq_iff_eq_add']
  exact mod_cast h

/--
theorem `nat_gcd_helper_1` / 定理 `nat_gcd_helper_1`

English:
theorem nat_gcd_helper_1
  statement: (d x y a b : Nat) (hu : x % d = 0) (hv : y % d = 0)
  proof: (Nat.gcd_comm _ _).trans nat_gcd_helper_2 _ _ _ _ _ hv hu h

中文:
定理 nat_gcd_helper_1
  结论: (d x y a b : 自然数) (hu : x % d = 0) (hv : y % d = 0)
  证明: (Nat.gcd_comm _ _).trans nat_gcd_helper_2 _ _ _ _ _ hv hu h

Depends on / 依赖: Nat.gcd_comm, gcd_comm, nat_gcd_helper_2
-/
theorem nat_gcd_helper_1 (d x y a b : Nat) (hu : x % d = 0) (hv : y % d = 0)
    (h : y * b = x * a + d) : Nat.gcd x y = d :=
(Nat.gcd_comm _ _).trans nat_gcd_helper_2 _ _ _ _ _ hv hu h

/--
theorem `nat_gcd_helper_1'` / 定理 `nat_gcd_helper_1'`

English:
theorem nat_gcd_helper_1'
  given: (x y a b : Nat) (h : y * b = x * a + 1)
  proof: nat_gcd_helper_1 1 _ _ _ _ (Nat.mod_one _) (Nat.mod_one _) h

中文:
定理 nat_gcd_helper_1'
  条件: (x y a b : 自然数) (h : y * b = x * a + 1)
  证明: nat_gcd_helper_1 1 _ _ _ _ (Nat.mod_one _) (Nat.mod_one _) h

Depends on / 依赖: Nat.mod_one, mod_one, nat_gcd_helper_1
-/
theorem nat_gcd_helper_1' (x y a b : Nat) (h : y * b = x * a + 1) :
    Nat.gcd x y = 1 :=
  nat_gcd_helper_1 1 _ _ _ _ (Nat.mod_one _) (Nat.mod_one _) h

/--
theorem `nat_gcd_helper_2'` / 定理 `nat_gcd_helper_2'`

English:
theorem nat_gcd_helper_2'
  given: (x y a b : Nat) (h : x * a = y * b + 1)
  proof: nat_gcd_helper_2 1 _ _ _ _ (Nat.mod_one _) (Nat.mod_one _) h

中文:
定理 nat_gcd_helper_2'
  条件: (x y a b : 自然数) (h : x * a = y * b + 1)
  证明: nat_gcd_helper_2 1 _ _ _ _ (Nat.mod_one _) (Nat.mod_one _) h

Depends on / 依赖: Nat.mod_one, mod_one, nat_gcd_helper_2
-/
theorem nat_gcd_helper_2' (x y a b : Nat) (h : x * a = y * b + 1) :
    Nat.gcd x y = 1 :=
  nat_gcd_helper_2 1 _ _ _ _ (Nat.mod_one _) (Nat.mod_one _) h

/--
theorem `nat_lcm_helper` / 定理 `nat_lcm_helper`

English:
theorem nat_lcm_helper
  statement: (x y d m : Nat) (hd : Nat.gcd x y = d)
  proof: mul_right_injective₀ (Nat.ne_of_beq_eq_false d0) by
    dsimp only
    rw [← dm]; rw [← hd]; rw [Nat.gcd_mul_lcm]

中文:
定理 nat_lcm_helper
  结论: (x y d m : 自然数) (hd : 自然数.最大公约数 x y = d)
  证明: mul_right_injective₀ (Nat.ne_of_beq_eq_false d0) by
    dsimp only
    rw [← dm]; rw [← hd]; rw [Nat.gcd_mul_lcm]

Depends on / 依赖: Nat.gcd_mul_lcm, Nat.ne_of_beq_eq_false, gcd_mul_lcm, ne_of_beq_eq_false
-/
theorem nat_lcm_helper (x y d m : Nat) (hd : Nat.gcd x y = d)
    (d0 : Nat.beq d 0 = false)
    (dm : x * y = d * m) : Nat.lcm x y = m :=
mul_right_injective₀ (Nat.ne_of_beq_eq_false d0) by
    dsimp only
    rw [← dm]; rw [← hd]; rw [Nat.gcd_mul_lcm]

/--
theorem `int_gcd_helper` / 定理 `int_gcd_helper`

English:
theorem int_gcd_helper
  statement: {x y : Int} {x' y' d : Nat}
  proof: by subst_vars; rw [Int.gcd_def]

中文:
定理 int_gcd_helper
  结论: {x y : 整数} {x' y' d : 自然数}
  证明: by subst_vars; rw [Int.gcd_def]

Depends on / 依赖: Int.gcd_def, gcd_def
-/
theorem int_gcd_helper {x y : Int} {x' y' d : Nat}
    (hx : x.natAbs = x') (hy : y.natAbs = y') (h : Nat.gcd x' y' = d) :
    Int.gcd x y = d := by subst_vars; rw [Int.gcd_def]

/--
theorem `int_lcm_helper` / 定理 `int_lcm_helper`

English:
theorem int_lcm_helper
  statement: {x y : Int} {x' y' d : Nat}
  proof: by subst_vars; rw [Int.lcm_def]

中文:
定理 int_lcm_helper
  结论: {x y : 整数} {x' y' d : 自然数}
  证明: by subst_vars; rw [Int.lcm_def]

Depends on / 依赖: Int.lcm_def, lcm_def
-/
theorem int_lcm_helper {x y : Int} {x' y' d : Nat}
    (hx : x.natAbs = x') (hy : y.natAbs = y') (h : Nat.lcm x' y' = d) :
    Int.lcm x y = d := by subst_vars; rw [Int.lcm_def]

open Qq Lean Elab.Tactic Mathlib.Meta.NormNum

/--
theorem `isNat_gcd` / 定理 `isNat_gcd`

English:
theorem isNat_gcd
  statement: {x y nx ny z : Nat} ->

中文:
定理 is自然数_gcd
  结论: {x y nx ny z : 自然数} ->
-/
theorem isNat_gcd : {x y nx ny z : Nat} ->
    IsNat x nx -> IsNat y ny -> Nat.gcd nx ny = z -> IsNat (Nat.gcd x y) z
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨rfl⟩

/--
theorem `isNat_lcm` / 定理 `isNat_lcm`

English:
theorem isNat_lcm
  statement: {x y nx ny z : Nat} ->

中文:
定理 is自然数_lcm
  结论: {x y nx ny z : 自然数} ->
-/
theorem isNat_lcm : {x y nx ny z : Nat} ->
    IsNat x nx -> IsNat y ny -> Nat.lcm nx ny = z -> IsNat (Nat.lcm x y) z
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨rfl⟩

/--
theorem `isInt_gcd` / 定理 `isInt_gcd`

English:
theorem isInt_gcd
  statement: {x y nx ny : Int} -> {z : Nat} ->

中文:
定理 is整数_gcd
  结论: {x y nx ny : 整数} -> {z : 自然数} ->
-/
theorem isInt_gcd : {x y nx ny : Int} -> {z : Nat} ->
    IsInt x nx -> IsInt y ny -> Int.gcd nx ny = z -> IsNat (Int.gcd x y) z
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨rfl⟩

/--
theorem `isInt_lcm` / 定理 `isInt_lcm`

English:
theorem isInt_lcm
  statement: {x y nx ny : Int} -> {z : Nat} ->

中文:
定理 is整数_lcm
  结论: {x y nx ny : 整数} -> {z : 自然数} ->
-/
theorem isInt_lcm : {x y nx ny : Int} -> {z : Nat} ->
    IsInt x nx -> IsInt y ny -> Int.lcm nx ny = z -> IsNat (Int.lcm x y) z
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨rfl⟩

/--
Definition of `proveNatGCD` / `proveNatGCD` 的定义

English:
definition proveNatGCD
  signature: (ex ey : Q(Nat))
  body: match ex.natLit!, ey.natLit! with
| 0, _ => have : ex =Q nat_lit 0 := ⟨⟩; ⟨ey, q(Nat.gcd_zero_left $ey)⟩
| _, 0 => have : ey =Q nat_lit 0 := ⟨⟩; ⟨ex, q(Nat.gcd_zero_right $ex)⟩
| 1, _ => have : ex =Q nat_lit 1 := ⟨⟩; ⟨q(nat_lit 1), q(Nat.gcd_one_left $ey)⟩
| _, 1 => have : ey =Q nat_lit 1 := ⟨⟩; ⟨q(nat_lit 1), q(Nat.gcd_one_right $ex)⟩
  | x, y =>
    let (d, a, b) := Nat.xgcdAux x 1 0 y 0 1
    if d = x then
      have pq : Q(Nat.mod $ey $ex = 0) := (q(Eq.refl (nat_lit 0)) : Expr)
      ⟨ex, q(nat_gcd_helper_dvd_left $ex $ey $pq)⟩
    else if d = y then
      have pq : Q(Nat.mod $ex $ey = 0) := (q(Eq.refl (nat_lit 0)) : Expr)
      ⟨ey, q(nat_gcd_helper_dvd_right $ex $ey $pq)⟩
    else
      have ea' : Q(Nat) := mkRawNatLit a.natAbs
      have eb' : Q(Nat) := mkRawNatLit b.natAbs
      if d = 1 then
        if a >= 0 then
          have pt : Q($ex * $ea' = $ey * $eb' + 1) := (q(Eq.refl ($ex * $ea')) : Expr)
          ⟨q(nat_lit 1), q(nat_gcd_helper_2' $ex $ey $ea' $eb' $pt)⟩
        else
          have pt : Q($ey * $eb' = $ex * $ea' + 1) := (q(Eq.refl ($ey * $eb')) : Expr)
          ⟨q(nat_lit 1), q(nat_gcd_helper_1' $ex $ey $ea' $eb' $pt)⟩
      else
        have ed : Q(Nat) := mkRawNatLit d
        have pu : Q(Nat.mod $ex $ed = 0) := (q(Eq.refl (nat_lit 0)) : Expr)
        have pv : Q(Nat.mod $ey $ed = 0) := (q(Eq.refl (nat_lit 0)) : Expr)
        if a >= 0 then
          have pt : Q($ex * $ea' = $ey * $eb' + $ed) := (q(Eq.refl ($ex * $ea')) : Expr)
          ⟨ed, q(nat_gcd_helper_2 $ed $ex $ey $ea' $eb' $pu $pv $pt)⟩
        else
          have pt : Q($ey * $eb' = $ex * $ea' + $ed) := (q(Eq.refl ($ey * $eb')) : Expr)
          ⟨ed, q(nat_gcd_helper_1 $ed $ex $ey $ea' $eb' $pu $pv $pt)⟩

中文:
定义 prove自然数GCD
  签名: (ex ey : Q(自然数))
  定义体: match ex.natLit!, ey.natLit! with
| 0, _ => have : ex =Q nat_lit 0 := ⟨⟩; ⟨ey, q(Nat.gcd_zero_left $ey)⟩
| _, 0 => have : ey =Q nat_lit 0 := ⟨⟩; ⟨ex, q(Nat.gcd_zero_right $ex)⟩
| 1, _ => have : ex =Q nat_lit 1 := ⟨⟩; ⟨q(nat_lit 1), q(Nat.gcd_one_left $ey)⟩
| _, 1 => have : ey =Q nat_lit 1 := ⟨⟩; ⟨q(nat_lit 1), q(Nat.gcd_one_right $ex)⟩
  | x, y =>
    let (d, a, b) := Nat.xgcdAux x 1 0 y 0 1
    if d = x then
      have pq : Q(Nat.mod $ey $ex = 0) := (q(Eq.refl (nat_lit 0)) : Expr)
      ⟨ex, q(nat_gcd_helper_dvd_left $ex $ey $pq)⟩
    else if d = y then
      have pq : Q(Nat.mod $ex $ey = 0) := (q(Eq.refl (nat_lit 0)) : Expr)
      ⟨ey, q(nat_gcd_helper_dvd_right $ex $ey $pq)⟩
    else
      have ea' : Q(Nat) := mkRawNatLit a.natAbs
      have eb' : Q(Nat) := mkRawNatLit b.natAbs
      if d = 1 then
        if a >= 0 then
          have pt : Q($ex * $ea' = $ey * $eb' + 1) := (q(Eq.refl ($ex * $ea')) : Expr)
          ⟨q(nat_lit 1), q(nat_gcd_helper_2' $ex $ey $ea' $eb' $pt)⟩
        else
          have pt : Q($ey * $eb' = $ex * $ea' + 1) := (q(Eq.refl ($ey * $eb')) : Expr)
          ⟨q(nat_lit 1), q(nat_gcd_helper_1' $ex $ey $ea' $eb' $pt)⟩
      else
        have ed : Q(Nat) := mkRawNatLit d
        have pu : Q(Nat.mod $ex $ed = 0) := (q(Eq.refl (nat_lit 0)) : Expr)
        have pv : Q(Nat.mod $ey $ed = 0) := (q(Eq.refl (nat_lit 0)) : Expr)
        if a >= 0 then
          have pt : Q($ex * $ea' = $ey * $eb' + $ed) := (q(Eq.refl ($ex * $ea')) : Expr)
          ⟨ed, q(nat_gcd_helper_2 $ed $ex $ey $ea' $eb' $pu $pv $pt)⟩
        else
          have pt : Q($ey * $eb' = $ex * $ea' + $ed) := (q(Eq.refl ($ey * $eb')) : Expr)
          ⟨ed, q(nat_gcd_helper_1 $ed $ex $ey $ea' $eb' $pu $pv $pt)⟩

Depends on / 依赖: Eq.refl, Nat.gcd_one_left, Nat.gcd_one_right, Nat.gcd_zero_left, Nat.gcd_zero_right, Nat.mod, Nat.xgcdAux, ex.natLit, ey.natLit, gcd_one_left, gcd_one_right, gcd_zero_left, gcd_zero_right, natLit, nat_gcd_helper_dvd_lef, nat_lit, xgcdAux
-/
def proveNatGCD (ex ey : Q(Nat)) : (ed : Q(Nat)) × Q(Nat.gcd $ex $ey = $ed) :=
  match ex.natLit!, ey.natLit! with
| 0, _ => have : ex =Q nat_lit 0 := ⟨⟩; ⟨ey, q(Nat.gcd_zero_left $ey)⟩
| _, 0 => have : ey =Q nat_lit 0 := ⟨⟩; ⟨ex, q(Nat.gcd_zero_right $ex)⟩
| 1, _ => have : ex =Q nat_lit 1 := ⟨⟩; ⟨q(nat_lit 1), q(Nat.gcd_one_left $ey)⟩
| _, 1 => have : ey =Q nat_lit 1 := ⟨⟩; ⟨q(nat_lit 1), q(Nat.gcd_one_right $ex)⟩
  | x, y =>
    let (d, a, b) := Nat.xgcdAux x 1 0 y 0 1
    if d = x then
      have pq : Q(Nat.mod $ey $ex = 0) := (q(Eq.refl (nat_lit 0)) : Expr)
      ⟨ex, q(nat_gcd_helper_dvd_left $ex $ey $pq)⟩
    else if d = y then
      have pq : Q(Nat.mod $ex $ey = 0) := (q(Eq.refl (nat_lit 0)) : Expr)
      ⟨ey, q(nat_gcd_helper_dvd_right $ex $ey $pq)⟩
    else
      have ea' : Q(Nat) := mkRawNatLit a.natAbs
      have eb' : Q(Nat) := mkRawNatLit b.natAbs
      if d = 1 then
        if a >= 0 then
          have pt : Q($ex * $ea' = $ey * $eb' + 1) := (q(Eq.refl ($ex * $ea')) : Expr)
          ⟨q(nat_lit 1), q(nat_gcd_helper_2' $ex $ey $ea' $eb' $pt)⟩
        else
          have pt : Q($ey * $eb' = $ex * $ea' + 1) := (q(Eq.refl ($ey * $eb')) : Expr)
          ⟨q(nat_lit 1), q(nat_gcd_helper_1' $ex $ey $ea' $eb' $pt)⟩
      else
        have ed : Q(Nat) := mkRawNatLit d
        have pu : Q(Nat.mod $ex $ed = 0) := (q(Eq.refl (nat_lit 0)) : Expr)
        have pv : Q(Nat.mod $ey $ed = 0) := (q(Eq.refl (nat_lit 0)) : Expr)
        if a >= 0 then
          have pt : Q($ex * $ea' = $ey * $eb' + $ed) := (q(Eq.refl ($ex * $ea')) : Expr)
          ⟨ed, q(nat_gcd_helper_2 $ed $ex $ey $ea' $eb' $pu $pv $pt)⟩
        else
          have pt : Q($ey * $eb' = $ex * $ea' + $ed) := (q(Eq.refl ($ey * $eb')) : Expr)
          ⟨ed, q(nat_gcd_helper_1 $ed $ex $ey $ea' $eb' $pu $pv $pt)⟩

/-- Evaluate the `Nat.gcd` function. -/
@[norm_num Nat.gcd _ _]
/--
Definition of `evalNatGCD` / `evalNatGCD` 的定义

English:
definition evalNatGCD
  signature: : NormNumExt where eval {u α} e
  body: do
  let .app (.app _ (x : Q(Nat))) (y : Q(Nat)) ← Meta.whnfR e | failure
haveI' : u =QL 0 := ⟨⟩; haveI' : α =Q Nat := ⟨⟩
haveI' : e =Q Nat.gcd x y := ⟨⟩
  let sNat : Q(AddMonoidWithOne Nat) := q(Nat.instAddMonoidWithOne)
  let ⟨ex, p⟩ ← deriveNat x sNat
  let ⟨ey, q⟩ ← deriveNat y sNat
  let ⟨ed, pf⟩ := proveNatGCD ex ey
  return .isNat sNat ed q(isNat_gcd $p $q $pf)

中文:
定义 eval自然数GCD
  签名: : NormNumExt where eval {u α} e
  定义体: do
  let .app (.app _ (x : Q(Nat))) (y : Q(Nat)) ← Meta.whnfR e | failure
haveI' : u =QL 0 := ⟨⟩; haveI' : α =Q Nat := ⟨⟩
haveI' : e =Q Nat.gcd x y := ⟨⟩
  let sNat : Q(AddMonoidWithOne Nat) := q(Nat.instAddMonoidWithOne)
  let ⟨ex, p⟩ ← deriveNat x sNat
  let ⟨ey, q⟩ ← deriveNat y sNat
  let ⟨ed, pf⟩ := proveNatGCD ex ey
  return .isNat sNat ed q(isNat_gcd $p $q $pf)
-/
def evalNatGCD : NormNumExt where eval {u α} e := do
  let .app (.app _ (x : Q(Nat))) (y : Q(Nat)) ← Meta.whnfR e | failure
haveI' : u =QL 0 := ⟨⟩; haveI' : α =Q Nat := ⟨⟩
haveI' : e =Q Nat.gcd x y := ⟨⟩
  let sNat : Q(AddMonoidWithOne Nat) := q(Nat.instAddMonoidWithOne)
  let ⟨ex, p⟩ ← deriveNat x sNat
  let ⟨ey, q⟩ ← deriveNat y sNat
  let ⟨ed, pf⟩ := proveNatGCD ex ey
  return .isNat sNat ed q(isNat_gcd $p $q $pf)

/--
Definition of `proveNatLCM` / `proveNatLCM` 的定义

English:
definition proveNatLCM
  signature: (ex ey : Q(Nat))
  body: match ex.natLit!, ey.natLit! with
  | 0, _ =>
    show (ed : Q(Nat)) × Q(Nat.lcm 0 $ey = $ed) from ⟨q(nat_lit 0), q(Nat.lcm_zero_left $ey)⟩
  | _, 0 =>
    show (ed : Q(Nat)) × Q(Nat.lcm $ex 0 = $ed) from ⟨q(nat_lit 0), q(Nat.lcm_zero_right $ex)⟩
  | 1, _ => show (ed : Q(Nat)) × Q(Nat.lcm 1 $ey = $ed) from ⟨ey, q(Nat.lcm_one_left $ey)⟩
  | _, 1 => show (ed : Q(Nat)) × Q(Nat.lcm $ex 1 = $ed) from ⟨ex, q(Nat.lcm_one_right $ex)⟩
  | x, y =>
    let ⟨ed, pd⟩ := proveNatGCD ex ey
    have p0 : Q(Nat.beq $ed 0 = false) := (q(Eq.refl false) : Expr)
    have em : Q(Nat) := mkRawNatLit (x * y / ed.natLit!)
    have pm : Q($ex * $ey = $ed * $em) := (q(Eq.refl ($ex * $ey)) : Expr)
    ⟨em, q(nat_lcm_helper $ex $ey $ed $em $pd $p0 $pm)⟩

中文:
定义 prove自然数LCM
  签名: (ex ey : Q(自然数))
  定义体: match ex.natLit!, ey.natLit! with
  | 0, _ =>
    show (ed : Q(Nat)) × Q(Nat.lcm 0 $ey = $ed) from ⟨q(nat_lit 0), q(Nat.lcm_zero_left $ey)⟩
  | _, 0 =>
    show (ed : Q(Nat)) × Q(Nat.lcm $ex 0 = $ed) from ⟨q(nat_lit 0), q(Nat.lcm_zero_right $ex)⟩
  | 1, _ => show (ed : Q(Nat)) × Q(Nat.lcm 1 $ey = $ed) from ⟨ey, q(Nat.lcm_one_left $ey)⟩
  | _, 1 => show (ed : Q(Nat)) × Q(Nat.lcm $ex 1 = $ed) from ⟨ex, q(Nat.lcm_one_right $ex)⟩
  | x, y =>
    let ⟨ed, pd⟩ := proveNatGCD ex ey
    have p0 : Q(Nat.beq $ed 0 = false) := (q(Eq.refl false) : Expr)
    have em : Q(Nat) := mkRawNatLit (x * y / ed.natLit!)
    have pm : Q($ex * $ey = $ed * $em) := (q(Eq.refl ($ex * $ey)) : Expr)
    ⟨em, q(nat_lcm_helper $ex $ey $ed $em $pd $p0 $pm)⟩

Depends on / 依赖: Nat.beq, Nat.lcm, Nat.lcm_one_left, Nat.lcm_one_right, Nat.lcm_zero_left, Nat.lcm_zero_right, PerfectlyNormalSpace, PerfectlyNormalSpace.toCompletelyNormalSpace, ex.natLit, ey.natLit, lcm_one_left, lcm_one_right, lcm_zero_left, lcm_zero_right, natLit, nat_lit, proveNatGCD, toCompletelyNormalSpace
-/
def proveNatLCM (ex ey : Q(Nat)) : (ed : Q(Nat)) × Q(Nat.lcm $ex $ey = $ed) :=
  match ex.natLit!, ey.natLit! with
  | 0, _ =>
    show (ed : Q(Nat)) × Q(Nat.lcm 0 $ey = $ed) from ⟨q(nat_lit 0), q(Nat.lcm_zero_left $ey)⟩
  | _, 0 =>
    show (ed : Q(Nat)) × Q(Nat.lcm $ex 0 = $ed) from ⟨q(nat_lit 0), q(Nat.lcm_zero_right $ex)⟩
  | 1, _ => show (ed : Q(Nat)) × Q(Nat.lcm 1 $ey = $ed) from ⟨ey, q(Nat.lcm_one_left $ey)⟩
  | _, 1 => show (ed : Q(Nat)) × Q(Nat.lcm $ex 1 = $ed) from ⟨ex, q(Nat.lcm_one_right $ex)⟩
  | x, y =>
    let ⟨ed, pd⟩ := proveNatGCD ex ey
    have p0 : Q(Nat.beq $ed 0 = false) := (q(Eq.refl false) : Expr)
    have em : Q(Nat) := mkRawNatLit (x * y / ed.natLit!)
    have pm : Q($ex * $ey = $ed * $em) := (q(Eq.refl ($ex * $ey)) : Expr)
    ⟨em, q(nat_lcm_helper $ex $ey $ed $em $pd $p0 $pm)⟩

/-- Evaluates the `Nat.lcm` function. -/
@[norm_num Nat.lcm _ _]
/--
Definition of `evalNatLCM` / `evalNatLCM` 的定义

English:
definition evalNatLCM
  signature: : NormNumExt where eval {u α} e
  body: do
  let .app (.app _ (x : Q(Nat))) (y : Q(Nat)) ← Meta.whnfR e | failure
haveI' : u =QL 0 := ⟨⟩; haveI' : α =Q Nat := ⟨⟩
haveI' : e =Q Nat.lcm x y := ⟨⟩
  let sNat : Q(AddMonoidWithOne Nat) := q(Nat.instAddMonoidWithOne)
  let ⟨ex, p⟩ ← deriveNat x sNat
  let ⟨ey, q⟩ ← deriveNat y sNat
  let ⟨ed, pf⟩ := proveNatLCM ex ey
  return .isNat sNat ed q(isNat_lcm $p $q $pf)

中文:
定义 eval自然数LCM
  签名: : NormNumExt where eval {u α} e
  定义体: do
  let .app (.app _ (x : Q(Nat))) (y : Q(Nat)) ← Meta.whnfR e | failure
haveI' : u =QL 0 := ⟨⟩; haveI' : α =Q Nat := ⟨⟩
haveI' : e =Q Nat.lcm x y := ⟨⟩
  let sNat : Q(AddMonoidWithOne Nat) := q(Nat.instAddMonoidWithOne)
  let ⟨ex, p⟩ ← deriveNat x sNat
  let ⟨ey, q⟩ ← deriveNat y sNat
  let ⟨ed, pf⟩ := proveNatLCM ex ey
  return .isNat sNat ed q(isNat_lcm $p $q $pf)
-/
def evalNatLCM : NormNumExt where eval {u α} e := do
  let .app (.app _ (x : Q(Nat))) (y : Q(Nat)) ← Meta.whnfR e | failure
haveI' : u =QL 0 := ⟨⟩; haveI' : α =Q Nat := ⟨⟩
haveI' : e =Q Nat.lcm x y := ⟨⟩
  let sNat : Q(AddMonoidWithOne Nat) := q(Nat.instAddMonoidWithOne)
  let ⟨ex, p⟩ ← deriveNat x sNat
  let ⟨ey, q⟩ ← deriveNat y sNat
  let ⟨ed, pf⟩ := proveNatLCM ex ey
  return .isNat sNat ed q(isNat_lcm $p $q $pf)

/--
Definition of `proveIntGCD` / `proveIntGCD` 的定义

English:
definition proveIntGCD
  signature: (ex ey : Q(Int))
  body: let ⟨ex', hx⟩ := rawIntLitNatAbs ex
  let ⟨ey', hy⟩ := rawIntLitNatAbs ey
  let ⟨ed, pf⟩ := proveNatGCD ex' ey'
  ⟨ed, q(int_gcd_helper $hx $hy $pf)⟩

中文:
定义 prove整数GCD
  签名: (ex ey : Q(整数))
  定义体: let ⟨ex', hx⟩ := rawIntLitNatAbs ex
  let ⟨ey', hy⟩ := rawIntLitNatAbs ey
  let ⟨ed, pf⟩ := proveNatGCD ex' ey'
  ⟨ed, q(int_gcd_helper $hx $hy $pf)⟩

Depends on / 依赖: PerfectlyNormalSpace, R0Space, int_gcd_helper, proveNatGCD, rawIntLitNatAbs
-/
def proveIntGCD (ex ey : Q(Int)) : (ed : Q(Nat)) × Q(Int.gcd $ex $ey = $ed) :=
  let ⟨ex', hx⟩ := rawIntLitNatAbs ex
  let ⟨ey', hy⟩ := rawIntLitNatAbs ey
  let ⟨ed, pf⟩ := proveNatGCD ex' ey'
  ⟨ed, q(int_gcd_helper $hx $hy $pf)⟩

/-- Evaluates the `Int.gcd` function. -/
@[norm_num Int.gcd _ _]
/--
Definition of `evalIntGCD` / `evalIntGCD` 的定义

English:
definition evalIntGCD
  signature: : NormNumExt where eval {u α} e
  body: do
  let .app (.app _ (x : Q(Int))) (y : Q(Int)) ← Meta.whnfR e | failure
  let ⟨ex, p⟩ ← deriveInt x _
  let ⟨ey, q⟩ ← deriveInt y _
haveI' : u =QL 0 := ⟨⟩; haveI' : α =Q Nat := ⟨⟩
haveI' : e =Q Int.gcd x y := ⟨⟩
  let ⟨ed, pf⟩ := proveIntGCD ex ey
  return .isNat _ ed q(isInt_gcd $p $q $pf)

中文:
定义 eval整数GCD
  签名: : NormNumExt where eval {u α} e
  定义体: do
  let .app (.app _ (x : Q(Int))) (y : Q(Int)) ← Meta.whnfR e | failure
  let ⟨ex, p⟩ ← deriveInt x _
  let ⟨ey, q⟩ ← deriveInt y _
haveI' : u =QL 0 := ⟨⟩; haveI' : α =Q Nat := ⟨⟩
haveI' : e =Q Int.gcd x y := ⟨⟩
  let ⟨ed, pf⟩ := proveIntGCD ex ey
  return .isNat _ ed q(isInt_gcd $p $q $pf)
-/
def evalIntGCD : NormNumExt where eval {u α} e := do
  let .app (.app _ (x : Q(Int))) (y : Q(Int)) ← Meta.whnfR e | failure
  let ⟨ex, p⟩ ← deriveInt x _
  let ⟨ey, q⟩ ← deriveInt y _
haveI' : u =QL 0 := ⟨⟩; haveI' : α =Q Nat := ⟨⟩
haveI' : e =Q Int.gcd x y := ⟨⟩
  let ⟨ed, pf⟩ := proveIntGCD ex ey
  return .isNat _ ed q(isInt_gcd $p $q $pf)

/--
Definition of `proveIntLCM` / `proveIntLCM` 的定义

English:
definition proveIntLCM
  signature: (ex ey : Q(Int))
  body: let ⟨ex', hx⟩ := rawIntLitNatAbs ex
  let ⟨ey', hy⟩ := rawIntLitNatAbs ey
  let ⟨ed, pf⟩ := proveNatLCM ex' ey'
  ⟨ed, q(int_lcm_helper $hx $hy $pf)⟩

中文:
定义 prove整数LCM
  签名: (ex ey : Q(整数))
  定义体: let ⟨ex', hx⟩ := rawIntLitNatAbs ex
  let ⟨ey', hy⟩ := rawIntLitNatAbs ey
  let ⟨ed, pf⟩ := proveNatLCM ex' ey'
  ⟨ed, q(int_lcm_helper $hx $hy $pf)⟩

Depends on / 依赖: IsEmbedding, IsEmbedding.subtypeVal.perfectlyNormalSpace, int_lcm_helper, perfectlyNormalSpace, proveNatLCM, rawIntLitNatAbs, subtypeVal
-/
def proveIntLCM (ex ey : Q(Int)) : (ed : Q(Nat)) × Q(Int.lcm $ex $ey = $ed) :=
  let ⟨ex', hx⟩ := rawIntLitNatAbs ex
  let ⟨ey', hy⟩ := rawIntLitNatAbs ey
  let ⟨ed, pf⟩ := proveNatLCM ex' ey'
  ⟨ed, q(int_lcm_helper $hx $hy $pf)⟩

/-- Evaluates the `Int.lcm` function. -/
@[norm_num Int.lcm _ _]
/--
Definition of `evalIntLCM` / `evalIntLCM` 的定义

English:
definition evalIntLCM
  signature: : NormNumExt where eval {u α} e
  body: do
  let .app (.app _ (x : Q(Int))) (y : Q(Int)) ← Meta.whnfR e | failure
  let ⟨ex, p⟩ ← deriveInt x _
  let ⟨ey, q⟩ ← deriveInt y _
haveI' : u =QL 0 := ⟨⟩; haveI' : α =Q Nat := ⟨⟩
haveI' : e =Q Int.lcm x y := ⟨⟩
  let ⟨ed, pf⟩ := proveIntLCM ex ey
  return .isNat _ ed q(isInt_lcm $p $q $pf)

中文:
定义 eval整数LCM
  签名: : NormNumExt where eval {u α} e
  定义体: do
  let .app (.app _ (x : Q(Int))) (y : Q(Int)) ← Meta.whnfR e | failure
  let ⟨ex, p⟩ ← deriveInt x _
  let ⟨ey, q⟩ ← deriveInt y _
haveI' : u =QL 0 := ⟨⟩; haveI' : α =Q Nat := ⟨⟩
haveI' : e =Q Int.lcm x y := ⟨⟩
  let ⟨ed, pf⟩ := proveIntLCM ex ey
  return .isNat _ ed q(isInt_lcm $p $q $pf)

Depends on / 依赖: T5Space, T6Space, T6Space.toT5Space, toT5Space
-/
def evalIntLCM : NormNumExt where eval {u α} e := do
  let .app (.app _ (x : Q(Int))) (y : Q(Int)) ← Meta.whnfR e | failure
  let ⟨ex, p⟩ ← deriveInt x _
  let ⟨ey, q⟩ ← deriveInt y _
haveI' : u =QL 0 := ⟨⟩; haveI' : α =Q Nat := ⟨⟩
haveI' : e =Q Int.lcm x y := ⟨⟩
  let ⟨ed, pf⟩ := proveIntLCM ex ey
  return .isNat _ ed q(isInt_lcm $p $q $pf)

/--
theorem `isInt_ratNum` / 定理 `isInt_ratNum`

English:
theorem isInt_ratNum
  statement: forall {q : Rat} {n : Int} {n' : Nat} {d : Nat},
  proof: Nat.pos_iff_ne_zero.mpr by simpa using hi.ne_zero
    simp_rw [Rat.mul_num, Rat.den_intCast, invOf_eq_inv,
      Rat.inv_natCast_den_of_pos this, Rat.inv_natCast_num_of_pos this,
      Rat.num_intCast, one_mul, mul_one, h, Nat.cast_one, Int.ediv_one, Int.cast_id]

中文:
定理 is整数_ratNum
  结论: 对任意 {q : 有理数} {n : 整数} {n' : 自然数} {d : 自然数},
  证明: Nat.pos_iff_ne_zero.mpr by simpa using hi.ne_zero
    simp_rw [Rat.mul_num, Rat.den_intCast, invOf_eq_inv,
      Rat.inv_natCast_den_of_pos this, Rat.inv_natCast_num_of_pos this,
      Rat.num_intCast, one_mul, mul_one, h, Nat.cast_one, Int.ediv_one, Int.cast_id]

Depends on / 依赖: Nat.pos_iff_ne_zero.mpr, hi.ne_zero, ne_zero, pos_iff_ne_zero
-/
theorem isInt_ratNum : forall {q : Rat} {n : Int} {n' : Nat} {d : Nat},
    IsRat q n d -> n.natAbs = n' -> n'.gcd d = 1 -> IsInt q.num n
  | _, n, _, d, ⟨hi, rfl⟩, rfl, h => by
    constructor
have : 0 < d := Nat.pos_iff_ne_zero.mpr by simpa using hi.ne_zero
    simp_rw [Rat.mul_num, Rat.den_intCast, invOf_eq_inv,
      Rat.inv_natCast_den_of_pos this, Rat.inv_natCast_num_of_pos this,
      Rat.num_intCast, one_mul, mul_one, h, Nat.cast_one, Int.ediv_one, Int.cast_id]

/--
theorem `isNat_ratDen` / 定理 `isNat_ratDen`

English:
theorem isNat_ratDen
  statement: forall {q : Rat} {n : Int} {n' : Nat} {d : Nat},
  proof: Nat.pos_iff_ne_zero.mpr by simpa using hi.ne_zero
    simp_rw [Rat.mul_den, Rat.den_intCast, invOf_eq_inv,
      Rat.inv_natCast_den_of_pos this, Rat.inv_natCast_num_of_pos this,
      Rat.num_intCast, one_mul, mul_one, Nat.cast_id, h, Nat.div_one]

中文:
定理 is自然数_ratDen
  结论: 对任意 {q : 有理数} {n : 整数} {n' : 自然数} {d : 自然数},
  证明: Nat.pos_iff_ne_zero.mpr by simpa using hi.ne_zero
    simp_rw [Rat.mul_den, Rat.den_intCast, invOf_eq_inv,
      Rat.inv_natCast_den_of_pos this, Rat.inv_natCast_num_of_pos this,
      Rat.num_intCast, one_mul, mul_one, Nat.cast_id, h, Nat.div_one]

Depends on / 依赖: IsEmbedding, IsEmbedding.subtypeVal.t6Space, Nat.pos_iff_ne_zero.mpr, hi.ne_zero, ne_zero, pos_iff_ne_zero, subtypeVal, t6Space
-/
theorem isNat_ratDen : forall {q : Rat} {n : Int} {n' : Nat} {d : Nat},
    IsRat q n d -> n.natAbs = n' -> n'.gcd d = 1 -> IsNat q.den d
  | _, n, _, d, ⟨hi, rfl⟩, rfl, h => by
    constructor
have : 0 < d := Nat.pos_iff_ne_zero.mpr by simpa using hi.ne_zero
    simp_rw [Rat.mul_den, Rat.den_intCast, invOf_eq_inv,
      Rat.inv_natCast_den_of_pos this, Rat.inv_natCast_num_of_pos this,
      Rat.num_intCast, one_mul, mul_one, Nat.cast_id, h, Nat.div_one]

/-- Evaluates the `Rat.num` function. -/
@[nolint unusedHavesSuffices, norm_num Rat.num _]
/--
Definition of `evalRatNum` / `evalRatNum` 的定义

English:
definition evalRatNum
  signature: : NormNumExt where eval {u α} e
  body: do
  let .proj _ _ (q : Q(Rat)) ← Meta.whnfR e | failure
have : u =QL 0 := ⟨⟩; have : α =Q Int := ⟨⟩; have : e =Q Rat.num q := ⟨⟩
  let ⟨q', n, d, eq⟩ ← deriveRat q (_inst := q(inferInstance))
  let ⟨n', hn⟩ := rawIntLitNatAbs n
  -- deriveRat ensures these are coprime, so the gcd will be 1
  let ⟨gcd, pf⟩ := proveNatGCD q($n') q($d)
have : gcd =Q nat_lit 1 := ⟨⟩
  return .isInt _ n q'.num q(isInt_ratNum $eq $hn $pf)

中文:
定义 evalRatNum
  签名: : NormNumExt where eval {u α} e
  定义体: do
  let .proj _ _ (q : Q(Rat)) ← Meta.whnfR e | failure
have : u =QL 0 := ⟨⟩; have : α =Q Int := ⟨⟩; have : e =Q Rat.num q := ⟨⟩
  let ⟨q', n, d, eq⟩ ← deriveRat q (_inst := q(inferInstance))
  let ⟨n', hn⟩ := rawIntLitNatAbs n
  -- deriveRat ensures these are coprime, so the gcd will be 1
  let ⟨gcd, pf⟩ := proveNatGCD q($n') q($d)
have : gcd =Q nat_lit 1 := ⟨⟩
  return .isInt _ n q'.num q(isInt_ratNum $eq $hn $pf)
-/
def evalRatNum : NormNumExt where eval {u α} e := do
  let .proj _ _ (q : Q(Rat)) ← Meta.whnfR e | failure
have : u =QL 0 := ⟨⟩; have : α =Q Int := ⟨⟩; have : e =Q Rat.num q := ⟨⟩
  let ⟨q', n, d, eq⟩ ← deriveRat q (_inst := q(inferInstance))
  let ⟨n', hn⟩ := rawIntLitNatAbs n
  -- deriveRat ensures these are coprime, so the gcd will be 1
  let ⟨gcd, pf⟩ := proveNatGCD q($n') q($d)
have : gcd =Q nat_lit 1 := ⟨⟩
  return .isInt _ n q'.num q(isInt_ratNum $eq $hn $pf)

/-- Evaluates the `Rat.den` function. -/
@[nolint unusedHavesSuffices, norm_num Rat.den _]
/--
Definition of `evalRatDen` / `evalRatDen` 的定义

English:
definition evalRatDen
  signature: : NormNumExt where eval {u α} e
  body: do
  let .proj _ _ (q : Q(Rat)) ← Meta.whnfR e | failure
have : u =QL 0 := ⟨⟩; have : α =Q Nat := ⟨⟩; have : e =Q Rat.den q := ⟨⟩
  let ⟨q', n, d, eq⟩ ← deriveRat q (_inst := q(inferInstance))
  let ⟨n', hn⟩ := rawIntLitNatAbs n
  -- deriveRat ensures these are coprime, so the gcd will be 1
  let ⟨gcd, pf⟩ := proveNatGCD q($n') q($d)
have : gcd =Q nat_lit 1 := ⟨⟩
  return .isNat _ d q(isNat_ratDen $eq $hn $pf)

中文:
定义 evalRatDen
  签名: : NormNumExt where eval {u α} e
  定义体: do
  let .proj _ _ (q : Q(Rat)) ← Meta.whnfR e | failure
have : u =QL 0 := ⟨⟩; have : α =Q Nat := ⟨⟩; have : e =Q Rat.den q := ⟨⟩
  let ⟨q', n, d, eq⟩ ← deriveRat q (_inst := q(inferInstance))
  let ⟨n', hn⟩ := rawIntLitNatAbs n
  -- deriveRat ensures these are coprime, so the gcd will be 1
  let ⟨gcd, pf⟩ := proveNatGCD q($n') q($d)
have : gcd =Q nat_lit 1 := ⟨⟩
  return .isNat _ d q(isNat_ratDen $eq $hn $pf)
-/
def evalRatDen : NormNumExt where eval {u α} e := do
  let .proj _ _ (q : Q(Rat)) ← Meta.whnfR e | failure
have : u =QL 0 := ⟨⟩; have : α =Q Nat := ⟨⟩; have : e =Q Rat.den q := ⟨⟩
  let ⟨q', n, d, eq⟩ ← deriveRat q (_inst := q(inferInstance))
  let ⟨n', hn⟩ := rawIntLitNatAbs n
  -- deriveRat ensures these are coprime, so the gcd will be 1
  let ⟨gcd, pf⟩ := proveNatGCD q($n') q($d)
have : gcd =Q nat_lit 1 := ⟨⟩
  return .isNat _ d q(isNat_ratDen $eq $hn $pf)

end NormNum

end Mathlib.Meta
