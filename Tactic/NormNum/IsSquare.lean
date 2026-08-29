/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public meta import Batteries.Data.Nat.Basic
public import Mathlib.Tactic.NormNum.GCD

/-!
# `norm_num` extension for `IsSquare`

The extension in this file handles natural, integer, and rational numbers.

## TODO
Add extensions for `ℚ≥0`, `ℝ`, `ℝ≥0`, `ℝ≥0∞`, `ℂ` (or any algebraically closed field?), `ZMod n`.
Probably, these extensions should go to different files.
-/

public meta section

namespace Mathlib.Meta.NormNum
open Qq

/--
theorem `isSquare_nat_of_isNat` / 定理 `isSquare_nat_of_isNat`

English:
theorem isSquare_nat_of_isNat
  given: (a n : Nat) (h : IsNat a n) (m : Nat) (hm : m * m = n)
  proof: ⟨m, h.1.trans hm.symm⟩

中文:
定理 isSquare_nat_of_is自然数
  条件: (a n : 自然数) (h : 是自然数 a n) (m : 自然数) (hm : m * m = n)
  证明: ⟨m, h.1.trans hm.symm⟩

Depends on / 依赖: hm.symm
-/
theorem isSquare_nat_of_isNat (a n : Nat) (h : IsNat a n) (m : Nat) (hm : m * m = n) :
    IsSquare a :=
  ⟨m, h.1.trans hm.symm⟩

/--
theorem `not_isSquare_nat_of_isNat` / 定理 `not_isSquare_nat_of_isNat`

English:
theorem not_isSquare_nat_of_isNat
  statement: (a n : Nat) (h : IsNat a n) (m k : Nat) (hm : m * m = k)
  proof: by
  rcases h with ⟨rfl⟩
  subst k
  rintro ⟨b, rfl⟩
  simp only [Nat.blt_eq, Nat.ble_eq, ← sq, Nat.pow_lt_pow_iff_left two_ne_zero] at hk₁ hk₂
  rw [← Nat.add_one_le_iff]; rw [← Nat.pow_le_pow_iff_left two_ne_zero] at hk₁
  grind

中文:
定理 not_isSquare_nat_of_is自然数
  结论: (a n : 自然数) (h : 是自然数 a n) (m k : 自然数) (hm : m * m = k)
  证明: by
  rcases h with ⟨rfl⟩
  subst k
  rintro ⟨b, rfl⟩
  simp only [Nat.blt_eq, Nat.ble_eq, ← sq, Nat.pow_lt_pow_iff_left two_ne_zero] at hk₁ hk₂
  rw [← Nat.add_one_le_iff]; rw [← Nat.pow_le_pow_iff_left two_ne_zero] at hk₁
  grind

Depends on / 依赖: Nat.add_one_le_iff, Nat.ble_eq, Nat.blt_eq, Nat.pow_le_pow_iff_left, Nat.pow_lt_pow_iff_left, add_one_le_iff, ble_eq, blt_eq, pow_le_pow_iff_left, pow_lt_pow_iff_left, two_ne_zero
-/
theorem not_isSquare_nat_of_isNat (a n : Nat) (h : IsNat a n) (m k : Nat) (hm : m * m = k)
    (hk₁ : Nat.blt k n) (hk₂ : Nat.ble n (k + 2 * m)) :
    ¬IsSquare a := by
  rcases h with ⟨rfl⟩
  subst k
  rintro ⟨b, rfl⟩
  simp only [Nat.blt_eq, Nat.ble_eq, ← sq, Nat.pow_lt_pow_iff_left two_ne_zero] at hk₁ hk₂
  rw [← Nat.add_one_le_iff]; rw [← Nat.pow_le_pow_iff_left two_ne_zero] at hk₁
  grind

/--
theorem `iff_isSquare_int_of_isNat` / 定理 `iff_isSquare_int_of_isNat`

English:
theorem iff_isSquare_int_of_isNat
  given: (a : Int) (n : Nat) (h : IsNat a n)
  statement: IsSquare n ↔ IsSquare a
  proof: by
  simp [h.1, Int.isSquare_natCast_iff]

中文:
定理 iff_isSquare_int_of_is自然数
  条件: (a : 整数) (n : 自然数) (h : 是自然数 a n)
  结论: IsSquare n ↔ IsSquare a
  证明: by
  simp [h.1, Int.isSquare_natCast_iff]

Depends on / 依赖: Int.isSquare_natCast_iff, isSquare_natCast_iff
-/
theorem iff_isSquare_int_of_isNat (a : Int) (n : Nat) (h : IsNat a n) : IsSquare n ↔ IsSquare a := by
  simp [h.1, Int.isSquare_natCast_iff]

/--
theorem `iff_isSquare_of_isInt_int` / 定理 `iff_isSquare_of_isInt_int`

English:
theorem iff_isSquare_of_isInt_int
  given: (a : Int) (n : Nat) (h : IsInt a (.negOfNat n))
  proof: by
  refine ⟨fun h' => by simp [h.1, h'], fun ⟨b, hb⟩ => ?_⟩
  rw [h.1]; rw [Int.cast_negOfNat] at hb
  rcases eq_or_ne b 0 with rfl | hb₀
  · simp_all
  · refine absurd hb (ne_of_lt ?_)
    exact lt_of_le_of_lt (by simp) (mul_self_pos.mpr hb₀)

中文:
定理 iff_isSquare_of_is整数_int
  条件: (a : 整数) (n : 自然数) (h : 是整数 a (.negOf自然数 n))
  证明: by
  refine ⟨fun h' => by simp [h.1, h'], fun ⟨b, hb⟩ => ?_⟩
  rw [h.1]; rw [Int.cast_negOfNat] at hb
  rcases eq_or_ne b 0 with rfl | hb₀
  · simp_all
  · refine absurd hb (ne_of_lt ?_)
    exact lt_of_le_of_lt (by simp) (mul_self_pos.mpr hb₀)

Depends on / 依赖: Int.cast_negOfNat, absurd, cast_negOfNat, eq_or_ne, lt_of_le_of_lt, mul_self_pos, mul_self_pos.mpr, ne_of_lt
-/
theorem iff_isSquare_of_isInt_int (a : Int) (n : Nat) (h : IsInt a (.negOfNat n)) :
    n = 0 ↔ IsSquare a := by
  refine ⟨fun h' => by simp [h.1, h'], fun ⟨b, hb⟩ => ?_⟩
  rw [h.1]; rw [Int.cast_negOfNat] at hb
  rcases eq_or_ne b 0 with rfl | hb₀
  · simp_all
  · refine absurd hb (ne_of_lt ?_)
    exact lt_of_le_of_lt (by simp) (mul_self_pos.mpr hb₀)

/--
theorem `iff_isSquare_of_isNat_rat` / 定理 `iff_isSquare_of_isNat_rat`

English:
theorem iff_isSquare_of_isNat_rat
  given: (a : Rat) (n : Nat) (h : IsNat a n)
  proof: by
  simp [h.1]

中文:
定理 iff_isSquare_of_is自然数_rat
  条件: (a : 有理数) (n : 自然数) (h : 是自然数 a n)
  证明: by
  simp [h.1]
-/
theorem iff_isSquare_of_isNat_rat (a : Rat) (n : Nat) (h : IsNat a n) :
    IsSquare n ↔ IsSquare a := by
  simp [h.1]

/--
theorem `iff_isSquare_of_isInt_rat` / 定理 `iff_isSquare_of_isInt_rat`

English:
theorem iff_isSquare_of_isInt_rat
  given: (a : Rat) (n : Nat) (h : IsInt a (.negOfNat n))
  proof: by
  refine ⟨fun h' => by simp [h.1, h'], fun ⟨b, hb⟩ => ?_⟩
  rw [h.1]; rw [Int.cast_negOfNat] at hb
  rcases eq_or_ne b 0 with rfl | hb₀
  · simp_all
  · refine absurd hb (ne_of_lt ?_)
    exact lt_of_le_of_lt (by simp) (mul_self_pos.mpr hb₀)

中文:
定理 iff_isSquare_of_is整数_rat
  条件: (a : 有理数) (n : 自然数) (h : 是整数 a (.negOf自然数 n))
  证明: by
  refine ⟨fun h' => by simp [h.1, h'], fun ⟨b, hb⟩ => ?_⟩
  rw [h.1]; rw [Int.cast_negOfNat] at hb
  rcases eq_or_ne b 0 with rfl | hb₀
  · simp_all
  · refine absurd hb (ne_of_lt ?_)
    exact lt_of_le_of_lt (by simp) (mul_self_pos.mpr hb₀)

Depends on / 依赖: Int.cast_negOfNat, absurd, cast_negOfNat, eq_or_ne, lt_of_le_of_lt, mul_self_pos, mul_self_pos.mpr, ne_of_lt
-/
theorem iff_isSquare_of_isInt_rat (a : Rat) (n : Nat) (h : IsInt a (.negOfNat n)) :
    n = 0 ↔ IsSquare a := by
  refine ⟨fun h' => by simp [h.1, h'], fun ⟨b, hb⟩ => ?_⟩
  rw [h.1]; rw [Int.cast_negOfNat] at hb
  rcases eq_or_ne b 0 with rfl | hb₀
  · simp_all
  · refine absurd hb (ne_of_lt ?_)
    exact lt_of_le_of_lt (by simp) (mul_self_pos.mpr hb₀)

/--
theorem `isSquare_of_isNNRat_rat` / 定理 `isSquare_of_isNNRat_rat`

English:
theorem isSquare_of_isNNRat_rat
  statement: (a : Rat) (n d : Nat) (hn : IsSquare n) (hd : IsSquare d)
  proof: by
  rcases hn with ⟨n, rfl⟩
  rcases hd with ⟨d, rfl⟩
  use n / d
  simp [ha.to_eq, div_mul_div_comm]

中文:
定理 isSquare_of_isNNRat_rat
  结论: (a : 有理数) (n d : 自然数) (hn : IsSquare n) (hd : IsSquare d)
  证明: by
  rcases hn with ⟨n, rfl⟩
  rcases hd with ⟨d, rfl⟩
  use n / d
  simp [ha.to_eq, div_mul_div_comm]

Depends on / 依赖: div_mul_div_comm, ha.to_eq, to_eq
-/
theorem isSquare_of_isNNRat_rat (a : Rat) (n d : Nat) (hn : IsSquare n) (hd : IsSquare d)
    (ha : IsNNRat a n d) : IsSquare a := by
  rcases hn with ⟨n, rfl⟩
  rcases hd with ⟨d, rfl⟩
  use n / d
  simp [ha.to_eq, div_mul_div_comm]

/--
theorem `not_isSquare_of_isNNRat_rat_of_num` / 定理 `not_isSquare_of_isNNRat_rat_of_num`

English:
theorem not_isSquare_of_isNNRat_rat_of_num
  statement: (a : Rat) (n d : Nat) (hn : ¬IsSquare n)
  proof: by
  rw [ha.to_eq rfl rfl]; rw [Rat.isSquare_iff]; rw [← Int.cast_natCast n]; rw [← Int.cast_natCast d]; rw [Rat.num_div_eq_of_coprime]
  · simp [hn]
  · contrapose! hnd
    have : n != 1 := by rintro rfl; simp at hn
    simp_all
  · simpa

中文:
定理 not_isSquare_of_isNNRat_rat_of_num
  结论: (a : 有理数) (n d : 自然数) (hn : ¬IsSquare n)
  证明: by
  rw [ha.to_eq rfl rfl]; rw [Rat.isSquare_iff]; rw [← Int.cast_natCast n]; rw [← Int.cast_natCast d]; rw [Rat.num_div_eq_of_coprime]
  · simp [hn]
  · contrapose! hnd
    have : n != 1 := by rintro rfl; simp at hn
    simp_all
  · simpa

Depends on / 依赖: Int.cast_natCast, Rat.isSquare_iff, Rat.num_div_eq_of_coprime, cast_natCast, contrapose, ha.to_eq, isSquare_iff, num_div_eq_of_coprime, to_eq
-/
theorem not_isSquare_of_isNNRat_rat_of_num (a : Rat) (n d : Nat) (hn : ¬IsSquare n)
    (hnd : n.Coprime d) (ha : IsNNRat a n d) : ¬IsSquare a := by
  rw [ha.to_eq rfl rfl]; rw [Rat.isSquare_iff]; rw [← Int.cast_natCast n]; rw [← Int.cast_natCast d]; rw [Rat.num_div_eq_of_coprime]
  · simp [hn]
  · contrapose! hnd
    have : n != 1 := by rintro rfl; simp at hn
    simp_all
  · simpa

/--
theorem `not_isSquare_of_isNNRat_rat_of_den` / 定理 `not_isSquare_of_isNNRat_rat_of_den`

English:
theorem not_isSquare_of_isNNRat_rat_of_den
  statement: (a : Rat) (n d : Nat) (hd : ¬IsSquare d) (hnd : n.Coprime d)
  proof: by
  rw [ha.to_eq rfl rfl]; rw [Rat.isSquare_iff]; rw [← Int.cast_natCast n]; rw [← Int.cast_natCast d]; rw [← Int.isSquare_natCast_iff (n := Rat.den _)]; rw [Rat.den_div_eq_of_coprime]
  · simp [hd]
  · contrapose! hnd
    simp_all
  · simpa

中文:
定理 not_isSquare_of_isNNRat_rat_of_den
  结论: (a : 有理数) (n d : 自然数) (hd : ¬IsSquare d) (hnd : n.Coprime d)
  证明: by
  rw [ha.to_eq rfl rfl]; rw [Rat.isSquare_iff]; rw [← Int.cast_natCast n]; rw [← Int.cast_natCast d]; rw [← Int.isSquare_natCast_iff (n := Rat.den _)]; rw [Rat.den_div_eq_of_coprime]
  · simp [hd]
  · contrapose! hnd
    simp_all
  · simpa

Depends on / 依赖: Int.cast_natCast, Int.isSquare_natCast_iff, Rat.den, Rat.den_div_eq_of_coprime, Rat.isSquare_iff, cast_natCast, contrapose, den_div_eq_of_coprime, ha.to_eq, isSquare_iff, isSquare_natCast_iff, to_eq
-/
theorem not_isSquare_of_isNNRat_rat_of_den (a : Rat) (n d : Nat) (hd : ¬IsSquare d) (hnd : n.Coprime d)
    (ha : IsNNRat a n d) : ¬IsSquare a := by
  rw [ha.to_eq rfl rfl]; rw [Rat.isSquare_iff]; rw [← Int.cast_natCast n]; rw [← Int.cast_natCast d]; rw [← Int.isSquare_natCast_iff (n := Rat.den _)]; rw [Rat.den_div_eq_of_coprime]
  · simp [hd]
  · contrapose! hnd
    simp_all
  · simpa

/--
theorem `not_isSquare_of_isRat_neg` / 定理 `not_isSquare_of_isRat_neg`

English:
theorem not_isSquare_of_isRat_neg
  statement: (a : Rat) (n d : Nat) (hn : n != 0) (hd : d != 0)
  proof: by
  rw [ha.neg_to_eq rfl rfl]
  rintro ⟨q, hq⟩
  refine absurd hq (ne_of_lt ?_)
  calc
    -(n / d : Rat) < 0 := by rw [Left.neg_neg_iff]; apply div_pos <;> simpa [Nat.pos_iff_ne_zero]
    _ <= q * q := mul_self_nonneg _

中文:
定理 not_isSquare_of_isRat_neg
  结论: (a : 有理数) (n d : 自然数) (hn : n != 0) (hd : d != 0)
  证明: by
  rw [ha.neg_to_eq rfl rfl]
  rintro ⟨q, hq⟩
  refine absurd hq (ne_of_lt ?_)
  calc
    -(n / d : Rat) < 0 := by rw [Left.neg_neg_iff]; apply div_pos <;> simpa [Nat.pos_iff_ne_zero]
    _ <= q * q := mul_self_nonneg _

Depends on / 依赖: Left.neg_neg_iff, Nat.pos_iff_ne_zero, absurd, div_pos, ha.neg_to_eq, mul_self_nonneg, ne_of_lt, neg_neg_iff, neg_to_eq, pos_iff_ne_zero
-/
theorem not_isSquare_of_isRat_neg (a : Rat) (n d : Nat) (hn : n != 0) (hd : d != 0)
    (ha : IsRat a (Int.negOfNat n) d) : ¬IsSquare a := by
  rw [ha.neg_to_eq rfl rfl]
  rintro ⟨q, hq⟩
  refine absurd hq (ne_of_lt ?_)
  calc
    -(n / d : Rat) < 0 := by rw [Left.neg_neg_iff]; apply div_pos <;> simpa [Nat.pos_iff_ne_zero]
    _ <= q * q := mul_self_nonneg _

open Lean

/-- `norm_num` extension for `IsSquare` on `ℕ`. -/
@[norm_num @IsSquare Nat _ _]
/--
Definition of `evalIsSquareNat` / `evalIsSquareNat` 的定义

English:
definition evalIsSquareNat
  signature: : NormNumExt where eval {u αP} e
  body: do
  match u, αP, e with
  | 0, ~q(Prop), ~q(@IsSquare Nat $mulN $a) => do
    let ⟨n, pa⟩ ← deriveNat (u := 0) (α := q(Nat)) a q(inferInstance)
    let m := Nat.sqrt n.natLit!
    if m * m = n.natLit! then
      have em : Q(Nat) := mkRawNatLit m
      have hm : Q($em * $em = $n) := (q(Eq.refl $n) :

中文:
定义 evalIsSquare自然数
  签名: : NormNumExt where eval {u αP} e
  定义体: do
  match u, αP, e with
  | 0, ~q(Prop), ~q(@IsSquare Nat $mulN $a) => do
    let ⟨n, pa⟩ ← deriveNat (u := 0) (α := q(Nat)) a q(inferInstance)
    let m := Nat.sqrt n.natLit!
    if m * m = n.natLit! then
      have em : Q(Nat) := mkRawNatLit m
      have hm : Q($em * $em = $n) := (q(Eq.refl $n) :
-/
def evalIsSquareNat : NormNumExt where eval {u αP} e := do
  match u, αP, e with
  | 0, ~q(Prop), ~q(@IsSquare Nat $mulN $a) => do
    let ⟨n, pa⟩ ← deriveNat (u := 0) (α := q(Nat)) a q(inferInstance)
    let m := Nat.sqrt n.natLit!
    if m * m = n.natLit! then
      have em : Q(Nat) := mkRawNatLit m
      have hm : Q($em * $em = $n) := (q(Eq.refl $n) : Expr)
      assertInstancesCommute
      return .isTrue (x := q(IsSquare $a)) q(isSquare_nat_of_isNat $a $n $pa $em $hm)
    else
      have em : Q(Nat) := mkRawNatLit m
      have ek : Q(Nat) := mkRawNatLit (m * m)
      have hm : Q($em * $em = $ek) := (q(Eq.refl $ek) : Expr)
      have hk₁ : Q(Nat.blt $ek $n) := (q(Eq.refl true) : Expr)
      have hk₂ : Q(Nat.ble $n ($ek + 2 * $em)) := (q(Eq.refl true) : Expr)
      assertInstancesCommute
      return .isFalse q(not_isSquare_nat_of_isNat $a $n $pa $em $ek $hm $hk₁ $hk₂)
  | _ => failure

/-- `norm_num` extension for `IsSquare` on `ℤ`. -/
@[norm_num @IsSquare Int _ _]
/--
Definition of `evalIsSquareInt` / `evalIsSquareInt` 的定义

English:
definition evalIsSquareInt
  signature: : NormNumExt where eval {u αP} e
  body: do
  match u, αP, e with
  | 0, ~q(Prop), ~q(@IsSquare Int $mulZ $a) => do
    match ← derive a with
    | .isNat sa n pa => do
      assertInstancesCommute
      let ⟨b, pb⟩ ← deriveBoolOfIff q(IsSquare $n) q(IsSquare $a)
        q(iff_isSquare_int_of_isNat $a $n $pa)
      return .ofBoolResult pb


中文:
定义 evalIsSquare整数
  签名: : NormNumExt where eval {u αP} e
  定义体: do
  match u, αP, e with
  | 0, ~q(Prop), ~q(@IsSquare Int $mulZ $a) => do
    match ← derive a with
    | .isNat sa n pa => do
      assertInstancesCommute
      let ⟨b, pb⟩ ← deriveBoolOfIff q(IsSquare $n) q(IsSquare $a)
        q(iff_isSquare_int_of_isNat $a $n $pa)
      return .ofBoolResult pb

-/
def evalIsSquareInt : NormNumExt where eval {u αP} e := do
  match u, αP, e with
  | 0, ~q(Prop), ~q(@IsSquare Int $mulZ $a) => do
    match ← derive a with
    | .isNat sa n pa => do
      assertInstancesCommute
      let ⟨b, pb⟩ ← deriveBoolOfIff q(IsSquare $n) q(IsSquare $a)
        q(iff_isSquare_int_of_isNat $a $n $pa)
      return .ofBoolResult pb
    | .isNegNat sa n pa => do
      assertInstancesCommute
      let ⟨b, pb⟩ ← deriveBoolOfIff q($n = 0) q(IsSquare $a) q(iff_isSquare_of_isInt_int $a $n $pa)
      return .ofBoolResult pb
    | _ => failure
  | _ => failure

/-- `norm_num` extension for `IsSquare` on `ℚ`. -/
@[norm_num @IsSquare Rat _ _]
/--
Definition of `evalIsSquareRat` / `evalIsSquareRat` 的定义

English:
definition evalIsSquareRat
  signature: : NormNumExt where eval {u αP} e
  body: do
  match u, αP, e with
  | 0, ~q(Prop), ~q(@IsSquare Rat $mulQ $a) => do
    match ← derive a with
    | .isNat sa n pa => do
      assertInstancesCommute
      let ⟨b, pb⟩ ← deriveBoolOfIff q(IsSquare $n) q(IsSquare $a)
        q(iff_isSquare_of_isNat_rat $a $n $pa)
      return .ofBoolResult pb


中文:
定义 evalIsSquareRat
  签名: : NormNumExt where eval {u αP} e
  定义体: do
  match u, αP, e with
  | 0, ~q(Prop), ~q(@IsSquare Rat $mulQ $a) => do
    match ← derive a with
    | .isNat sa n pa => do
      assertInstancesCommute
      let ⟨b, pb⟩ ← deriveBoolOfIff q(IsSquare $n) q(IsSquare $a)
        q(iff_isSquare_of_isNat_rat $a $n $pa)
      return .ofBoolResult pb

-/
def evalIsSquareRat : NormNumExt where eval {u αP} e := do
  match u, αP, e with
  | 0, ~q(Prop), ~q(@IsSquare Rat $mulQ $a) => do
    match ← derive a with
    | .isNat sa n pa => do
      assertInstancesCommute
      let ⟨b, pb⟩ ← deriveBoolOfIff q(IsSquare $n) q(IsSquare $a)
        q(iff_isSquare_of_isNat_rat $a $n $pa)
      return .ofBoolResult pb
    | .isNegNat sa n pa => do
      assertInstancesCommute
      let ⟨b, pb⟩ ← deriveBoolOfIff q($n = 0) q(IsSquare $a) q(iff_isSquare_of_isInt_rat $a $n $pa)
      return .ofBoolResult pb
    | .isNNRat sQ q n d pa => do
      -- We make sure to avoid proving `Nat.Coprime $n $d` unless we need to.
      -- Also, we do not derive `IsSquare $d` unless `$n` is a square
      match ← deriveBool q(IsSquare $n) with
      | .mk true pn =>
        match ← deriveBool q(IsSquare $d) with
        | .mk true pd =>
          assertInstancesCommute
          return .isTrue q(isSquare_of_isNNRat_rat $a $n $d $pn $pd $pa)
        | .mk false pd =>
          let ⟨e, he⟩ := proveNatGCD n d
have : e =Q 1 := ⟨⟩
          assertInstancesCommute
          return .isFalse q(not_isSquare_of_isNNRat_rat_of_den $a $n $d $pd $he $pa)
      | .mk false pn =>
        let ⟨e, he⟩ := proveNatGCD n d
have : e =Q 1 := ⟨⟩
        assertInstancesCommute
        return .isFalse q(not_isSquare_of_isNNRat_rat_of_num $a $n $d $pn $he $pa)
    | .isNegNNRat sQ q n d pa => do
      match ← deriveBool q($n = 0), ← deriveBool q($d = 0) with
      | .mk false pn, .mk false pd =>
        assertInstancesCommute
        return .isFalse q(not_isSquare_of_isRat_neg $a $n $d $pn $pd $pa)
      | _, _ => failure
    | _ => failure
  | _ => failure

end Mathlib.Meta.NormNum
