/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Kappelmann
-/
module

public import Mathlib.Algebra.Order.Round
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public meta import Mathlib.Algebra.Order.Round

/-!
# Floor Function for Rational Numbers

## Summary

We define the `FloorRing` instance on `ℚ`. Some technical lemmas relating `floor` to integer
division and modulo arithmetic are derived as well as some simple inequalities.

## Tags

rat, rationals, ℚ, floor
-/

@[expose] public section

assert_not_exists Finset

open Int

namespace Rat

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]
variable {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FloorRing Rat
  body: (FloorRing.ofFloor Rat Rat.floor) fun _ _ => Rat.le_floor_iff.symm

中文:
实例 :
  签名: Floor环 有理数
  定义体: (FloorRing.ofFloor Rat Rat.floor) fun _ _ => Rat.le_floor_iff.symm

Depends on / 依赖: FloorRing, FloorRing.ofFloor, Rat.floor, Rat.le_floor_iff.symm, le_floor_iff, ofFloor
-/
instance : FloorRing Rat :=
  (FloorRing.ofFloor Rat Rat.floor) fun _ _ => Rat.le_floor_iff.symm

/--
theorem `floor_def'` / 定理 `floor_def'`

English:
theorem floor_def'
  given: {q : Rat}
  statement: ⌊q⌋ = q.num / q.den
  proof: Rat.floor_def q

中文:
定理 floor_def'
  条件: {q : 有理数}
  结论: ⌊q⌋ = q.num / q.den
  证明: Rat.floor_def q
-/
protected theorem floor_def' {q : Rat} : ⌊q⌋ = q.num / q.den := Rat.floor_def q

/--
theorem `ceil_def'` / 定理 `ceil_def'`

English:
theorem ceil_def'
  given: (q : Rat)
  statement: ⌈q⌉ = -(-q.num / ↑q.den)
  proof: by
  change -⌊-q⌋ = _
  rw [Rat.floor_def']; rw [num_neg_eq_neg_num]; rw [den_neg_eq_den]


@[norm_cast]

中文:
定理 ceil_def'
  条件: (q : 有理数)
  结论: ⌈q⌉ = -(-q.num / ↑q.den)
  证明: by
  change -⌊-q⌋ = _
  rw [Rat.floor_def']; rw [num_neg_eq_neg_num]; rw [den_neg_eq_den]


@[norm_cast]
-/
protected theorem ceil_def' (q : Rat) : ⌈q⌉ = -(-q.num / ↑q.den) := by
  change -⌊-q⌋ = _
  rw [Rat.floor_def']; rw [num_neg_eq_neg_num]; rw [den_neg_eq_den]


@[norm_cast]
/--
theorem `floor_intCast_div_natCast` / 定理 `floor_intCast_div_natCast`

English:
theorem floor_intCast_div_natCast
  given: (n : Int) (d : Nat)
  statement: ⌊(↑n / ↑d : Rat)⌋ = n / (↑d : Int)
  proof: by
  rw [Rat.floor_def']
  obtain rfl | hd := eq_zero_or_pos (a := d)
  · simp
  set q := (n : Rat) / d with q_eq
  obtain ⟨c, n_eq_c_mul_num, d_eq_c_mul_denom⟩ : exists c, n = c * q.num ∧ (d : Int) = c * q.den := by
    rw [q_eq]
    exact mod_cast @Rat.exists_eq_mul_div_num_and_eq_mul_div_den n d 

中文:
定理 floor_intCast_div_natCast
  条件: (n : 整数) (d : 自然数)
  结论: ⌊(↑n / ↑d : 有理数)⌋ = n / (↑d : 整数)
  证明: by
  rw [Rat.floor_def']
  obtain rfl | hd := eq_zero_or_pos (a := d)
  · simp
  set q := (n : Rat) / d with q_eq
  obtain ⟨c, n_eq_c_mul_num, d_eq_c_mul_denom⟩ : exists c, n = c * q.num ∧ (d : Int) = c * q.den := by
    rw [q_eq]
    exact mod_cast @Rat.exists_eq_mul_div_num_and_eq_mul_div_den n d 

Depends on / 依赖: Int.mul_ediv_mul_of_pos, Int.natCast_nonneg, Int.natCast_pos, Rat.exists_eq_mul_div_num_and_eq_mul_div_den, Rat.floor_def, d_eq_c_mul_denom, eq_zero_or_pos, exists_eq_mul_div_num_and_eq_mul_div_den, floor_def, hd.ne, mod_cast, mul_ediv_mul_of_pos, n_eq_c_mul_num, natCast_nonneg, natCast_pos, pos_of_mul_pos_left, q.den, q.num, q_eq
-/
theorem floor_intCast_div_natCast (n : Int) (d : Nat) : ⌊(↑n / ↑d : Rat)⌋ = n / (↑d : Int) := by
  rw [Rat.floor_def']
  obtain rfl | hd := eq_zero_or_pos (a := d)
  · simp
  set q := (n : Rat) / d with q_eq
  obtain ⟨c, n_eq_c_mul_num, d_eq_c_mul_denom⟩ : exists c, n = c * q.num ∧ (d : Int) = c * q.den := by
    rw [q_eq]
    exact mod_cast @Rat.exists_eq_mul_div_num_and_eq_mul_div_den n d (mod_cast hd.ne')
  rw [n_eq_c_mul_num]; rw [d_eq_c_mul_denom]
  refine (Int.mul_ediv_mul_of_pos _ _ <| pos_of_mul_pos_left ?_ <| Int.natCast_nonneg q.den).symm
  rwa [← d_eq_c_mul_denom, Int.natCast_pos]

@[norm_cast]
/--
theorem `ceil_intCast_div_natCast` / 定理 `ceil_intCast_div_natCast`

English:
theorem ceil_intCast_div_natCast
  given: (n : Int) (d : Nat)
  statement: ⌈(↑n / ↑d : Rat)⌉ = -((-n) / (↑d : Int))
  proof: by
  conv_lhs => rw [← neg_neg ⌈_⌉, ← floor_neg]
  rw [← neg_div]; rw [← Int.cast_neg]; rw [floor_intCast_div_natCast]

@[norm_cast]

中文:
定理 ceil_intCast_div_natCast
  条件: (n : 整数) (d : 自然数)
  结论: ⌈(↑n / ↑d : 有理数)⌉ = -((-n) / (↑d : 整数))
  证明: by
  conv_lhs => rw [← neg_neg ⌈_⌉, ← floor_neg]
  rw [← neg_div]; rw [← Int.cast_neg]; rw [floor_intCast_div_natCast]

@[norm_cast]

Depends on / 依赖: Int.cast_neg, cast_neg, conv_lhs, floor_intCast_div_natCast, floor_neg, neg_div, neg_neg
-/
theorem ceil_intCast_div_natCast (n : Int) (d : Nat) : ⌈(↑n / ↑d : Rat)⌉ = -((-n) / (↑d : Int)) := by
  conv_lhs => rw [← neg_neg ⌈_⌉, ← floor_neg]
  rw [← neg_div]; rw [← Int.cast_neg]; rw [floor_intCast_div_natCast]

@[norm_cast]
/--
theorem `floor_natCast_div_natCast` / 定理 `floor_natCast_div_natCast`

English:
theorem floor_natCast_div_natCast
  given: (n d : Nat)
  statement: ⌊(↑n / ↑d : Rat)⌋ = n / d
  proof: floor_intCast_div_natCast n d

@[norm_cast]

中文:
定理 floor_natCast_div_natCast
  条件: (n d : 自然数)
  结论: ⌊(↑n / ↑d : 有理数)⌋ = n / d
  证明: floor_intCast_div_natCast n d

@[norm_cast]

Depends on / 依赖: floor_intCast_div_natCast
-/
theorem floor_natCast_div_natCast (n d : Nat) : ⌊(↑n / ↑d : Rat)⌋ = n / d :=
  floor_intCast_div_natCast n d

@[norm_cast]
/--
theorem `ceil_natCast_div_natCast` / 定理 `ceil_natCast_div_natCast`

English:
theorem ceil_natCast_div_natCast
  given: (n d : Nat)
  statement: ⌈(↑n / ↑d : Rat)⌉ = -((-n) / d)
  proof: ceil_intCast_div_natCast n d

@[norm_cast]

中文:
定理 ceil_natCast_div_natCast
  条件: (n d : 自然数)
  结论: ⌈(↑n / ↑d : 有理数)⌉ = -((-n) / d)
  证明: ceil_intCast_div_natCast n d

@[norm_cast]

Depends on / 依赖: ceil_intCast_div_natCast
-/
theorem ceil_natCast_div_natCast (n d : Nat) : ⌈(↑n / ↑d : Rat)⌉ = -((-n) / d) :=
  ceil_intCast_div_natCast n d

@[norm_cast]
/--
theorem `natFloor_natCast_div_natCast` / 定理 `natFloor_natCast_div_natCast`

English:
theorem natFloor_natCast_div_natCast
  given: (n d : Nat)
  statement: ⌊(↑n / ↑d : Rat)⌋₊ = n / d
  proof: by
  rw [← Int.ofNat_inj]; rw [Int.natCast_floor_eq_floor (by positivity)]
  push_cast
  exact floor_intCast_div_natCast n d

@[simp, norm_cast]

中文:
定理 natFloor_natCast_div_natCast
  条件: (n d : 自然数)
  结论: ⌊(↑n / ↑d : 有理数)⌋₊ = n / d
  证明: by
  rw [← Int.ofNat_inj]; rw [Int.natCast_floor_eq_floor (by positivity)]
  push_cast
  exact floor_intCast_div_natCast n d

@[simp, norm_cast]

Depends on / 依赖: Int.natCast_floor_eq_floor, Int.ofNat_inj, floor_intCast_div_natCast, natCast_floor_eq_floor, ofNat_inj
-/
theorem natFloor_natCast_div_natCast (n d : Nat) : ⌊(↑n / ↑d : Rat)⌋₊ = n / d := by
  rw [← Int.ofNat_inj]; rw [Int.natCast_floor_eq_floor (by positivity)]
  push_cast
  exact floor_intCast_div_natCast n d

@[simp, norm_cast]
/--
theorem `floor_cast` / 定理 `floor_cast`

English:
theorem floor_cast
  given: (x : Rat)
  statement: ⌊(x : α)⌋ = ⌊x⌋
  proof: floor_eq_iff.2 (mod_cast floor_eq_iff.1 (Eq.refl ⌊x⌋))

@[simp, norm_cast]

中文:
定理 floor_cast
  条件: (x : 有理数)
  结论: ⌊(x : α)⌋ = ⌊x⌋
  证明: floor_eq_iff.2 (mod_cast floor_eq_iff.1 (Eq.refl ⌊x⌋))

@[simp, norm_cast]

Depends on / 依赖: Eq.refl, floor_eq_iff, mod_cast
-/
theorem floor_cast (x : Rat) : ⌊(x : α)⌋ = ⌊x⌋ :=
  floor_eq_iff.2 (mod_cast floor_eq_iff.1 (Eq.refl ⌊x⌋))

@[simp, norm_cast]
/--
theorem `ceil_cast` / 定理 `ceil_cast`

English:
theorem ceil_cast
  given: (x : Rat)
  statement: ⌈(x : α)⌉ = ⌈x⌉
  proof: by
  rw [← neg_inj]; rw [← floor_neg]; rw [← floor_neg]; rw [← Rat.cast_neg]; rw [Rat.floor_cast]

@[simp, norm_cast]

中文:
定理 ceil_cast
  条件: (x : 有理数)
  结论: ⌈(x : α)⌉ = ⌈x⌉
  证明: by
  rw [← neg_inj]; rw [← floor_neg]; rw [← floor_neg]; rw [← Rat.cast_neg]; rw [Rat.floor_cast]

@[simp, norm_cast]

Depends on / 依赖: Rat.cast_neg, Rat.floor_cast, cast_neg, floor_cast, floor_neg, neg_inj
-/
theorem ceil_cast (x : Rat) : ⌈(x : α)⌉ = ⌈x⌉ := by
  rw [← neg_inj]; rw [← floor_neg]; rw [← floor_neg]; rw [← Rat.cast_neg]; rw [Rat.floor_cast]

@[simp, norm_cast]
/--
theorem `round_cast` / 定理 `round_cast`

English:
theorem round_cast
  given: (x : Rat)
  statement: round (x : α) = round x
  proof: by
  have : ((x + 1 / 2 : Rat) : α) = x + 1 / 2 := by simp
  rw [round_eq]; rw [round_eq]; rw [← this]; rw [floor_cast]

@[simp, norm_cast]

中文:
定理 round_cast
  条件: (x : 有理数)
  结论: round (x : α) = round x
  证明: by
  have : ((x + 1 / 2 : Rat) : α) = x + 1 / 2 := by simp
  rw [round_eq]; rw [round_eq]; rw [← this]; rw [floor_cast]

@[simp, norm_cast]

Depends on / 依赖: floor_cast, round_eq
-/
theorem round_cast (x : Rat) : round (x : α) = round x := by
  have : ((x + 1 / 2 : Rat) : α) = x + 1 / 2 := by simp
  rw [round_eq]; rw [round_eq]; rw [← this]; rw [floor_cast]

@[simp, norm_cast]
/--
theorem `cast_fract` / 定理 `cast_fract`

English:
theorem cast_fract
  given: (x : Rat)
  statement: (↑(fract x) : α) = fract (x : α)
  proof: by
  simp only [fract, cast_sub, cast_intCast, floor_cast]

@[simp]

中文:
定理 cast_fract
  条件: (x : 有理数)
  结论: (↑(fract x) : α) = fract (x : α)
  证明: by
  simp only [fract, cast_sub, cast_intCast, floor_cast]

@[simp]

Depends on / 依赖: cast_intCast, cast_sub, floor_cast
-/
theorem cast_fract (x : Rat) : (↑(fract x) : α) = fract (x : α) := by
  simp only [fract, cast_sub, cast_intCast, floor_cast]

@[simp]
/--
theorem `den_intFract` / 定理 `den_intFract`

English:
theorem den_intFract
  given: (x : Rat)
  statement: (fract x).den = x.den
  proof: Rat.sub_intCast_den _ _

中文:
定理 den_intFract
  条件: (x : 有理数)
  结论: (fract x).den = x.den
  证明: Rat.sub_intCast_den _ _

Depends on / 依赖: Rat.sub_intCast_den, sub_intCast_den
-/
theorem den_intFract (x : Rat) : (fract x).den = x.den :=
  Rat.sub_intCast_den _ _

section NormNum

open Mathlib.Meta.NormNum Qq

/--
theorem `isNat_intFloor` / 定理 `isNat_intFloor`

English:
theorem isNat_intFloor
  statement: {R} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
  proof: by rintro ⟨⟨⟩⟩; exact ⟨by simp⟩

中文:
定理 is自然数_intFloor
  结论: {R} [环 R] [线性序 R] [是StrictOrdered环 R] [Floor环 R]
  证明: by rintro ⟨⟨⟩⟩; exact ⟨by simp⟩
-/
theorem isNat_intFloor {R} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    (r : R) (m : Nat) :
    IsNat r m -> IsNat ⌊r⌋ m := by rintro ⟨⟨⟩⟩; exact ⟨by simp⟩

/--
theorem `isInt_intFloor` / 定理 `isInt_intFloor`

English:
theorem isInt_intFloor
  statement: {R} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
  proof: by rintro ⟨⟨⟩⟩; exact ⟨by simp⟩

中文:
定理 is整数_intFloor
  结论: {R} [环 R] [线性序 R] [是StrictOrdered环 R] [Floor环 R]
  证明: by rintro ⟨⟨⟩⟩; exact ⟨by simp⟩
-/
theorem isInt_intFloor {R} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    (r : R) (m : Int) :
    IsInt r m -> IsInt ⌊r⌋ m := by rintro ⟨⟨⟩⟩; exact ⟨by simp⟩

/--
theorem `isNat_intFloor_ofIsNNRat` / 定理 `isNat_intFloor_ofIsNNRat`

English:
theorem isNat_intFloor_ofIsNNRat
  given: (r : α) (n : Nat) (d : Nat)
  proof: by
  rintro ⟨inv, rfl⟩
  constructor
  simp only [invOf_eq_inv, ← div_eq_mul_inv]
  rw [← Int.ofNat_ediv_ofNat]; rw [← floor_natCast_div_natCast n d]; rw [← floor_cast (α := α)]; rw [Rat.cast_div]; rw [cast_natCast]; rw [cast_natCast]

中文:
定理 is自然数_intFloor_ofIsNNRat
  条件: (r : α) (n : 自然数) (d : 自然数)
  证明: by
  rintro ⟨inv, rfl⟩
  constructor
  simp only [invOf_eq_inv, ← div_eq_mul_inv]
  rw [← Int.ofNat_ediv_ofNat]; rw [← floor_natCast_div_natCast n d]; rw [← floor_cast (α := α)]; rw [Rat.cast_div]; rw [cast_natCast]; rw [cast_natCast]

Depends on / 依赖: Int.ofNat_ediv_ofNat, Rat.cast_div, cast_div, cast_natCast, div_eq_mul_inv, floor_cast, floor_natCast_div_natCast, invOf_eq_inv, ofNat_ediv_ofNat
-/
theorem isNat_intFloor_ofIsNNRat (r : α) (n : Nat) (d : Nat) :
    IsNNRat r n d -> IsNat ⌊r⌋ (n / d) := by
  rintro ⟨inv, rfl⟩
  constructor
  simp only [invOf_eq_inv, ← div_eq_mul_inv]
  rw [← Int.ofNat_ediv_ofNat]; rw [← floor_natCast_div_natCast n d]; rw [← floor_cast (α := α)]; rw [Rat.cast_div]; rw [cast_natCast]; rw [cast_natCast]

/--
theorem `isInt_intFloor_ofIsRat_neg` / 定理 `isInt_intFloor_ofIsRat_neg`

English:
theorem isInt_intFloor_ofIsRat_neg
  given: (r : α) (n : Nat) (d : Nat)
  proof: by
  rintro ⟨inv, rfl⟩
  constructor
  simp only [invOf_eq_inv, ← div_eq_mul_inv, Int.cast_id]
  rw [← ceil_intCast_div_natCast n d]; rw [Int.cast_natCast]
  rw [@negOfNat_eq (toNat _)]; rw [ofNat_eq_natCast]; rw [natCast_toNat_eq_self.mpr (ceil_nonneg (div_nonneg n.cast_nonneg d.cast_nonneg))]; rw 

中文:
定理 is整数_intFloor_ofIsRat_neg
  条件: (r : α) (n : 自然数) (d : 自然数)
  证明: by
  rintro ⟨inv, rfl⟩
  constructor
  simp only [invOf_eq_inv, ← div_eq_mul_inv, Int.cast_id]
  rw [← ceil_intCast_div_natCast n d]; rw [Int.cast_natCast]
  rw [@negOfNat_eq (toNat _)]; rw [ofNat_eq_natCast]; rw [natCast_toNat_eq_self.mpr (ceil_nonneg (div_nonneg n.cast_nonneg d.cast_nonneg))]; rw 

Depends on / 依赖: Int.cast_id, Int.cast_natCast, Rat.cast_d, cast_d, cast_id, cast_natCast, cast_nonneg, ceil_intCast_div_natCast, ceil_nonneg, d.cast_nonneg, div_eq_mul_inv, div_nonneg, floor_cast, floor_intCast_div_natCast, invOf_eq_inv, n.cast_nonneg, natCast_toNat_eq_self, natCast_toNat_eq_self.mpr, negOfNat, negOfNat_eq
-/
theorem isInt_intFloor_ofIsRat_neg (r : α) (n : Nat) (d : Nat) :
    IsRat r (.negOfNat n) d -> IsInt ⌊r⌋ (.negOfNat (-(-n / d) : Int).toNat) := by
  rintro ⟨inv, rfl⟩
  constructor
  simp only [invOf_eq_inv, ← div_eq_mul_inv, Int.cast_id]
  rw [← ceil_intCast_div_natCast n d]; rw [Int.cast_natCast]
  rw [@negOfNat_eq (toNat _)]; rw [ofNat_eq_natCast]; rw [natCast_toNat_eq_self.mpr (ceil_nonneg (div_nonneg n.cast_nonneg d.cast_nonneg))]; rw [← Int.cast_natCast n]; rw [ceil_intCast_div_natCast n d]; rw [neg_neg]; rw [← ofNat_eq_natCast]; rw [← negOfNat_eq]; rw [← floor_intCast_div_natCast (.negOfNat n) d]; rw [← floor_cast (α := α)]; rw [Rat.cast_div]; rw [cast_intCast]; rw [cast_natCast]

/-- `norm_num` extension for `Int.floor` -/
@[norm_num ⌊_⌋]
meta def evalIntFloor : NormNumExt where eval {u αZ} e := do
  match u, αZ, e with
  | 0, ~q(Int), ~q(@Int.floor $α $instR $instO $instF $x) =>
    match ← derive x with
    | .isBool .. => failure
    | .isNat _ _ pb => do
      let _i ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      return .isNat q(inferInstance) _ q(isNat_intFloor $x _ $pb)
    | .isNegNat _ _ pb => do
      let _i ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      -- floor always keeps naturals negative, so we can shortcut `.isInt`
      return .isNegNat q(inferInstance) _ q(isInt_intFloor _ _ $pb)
    | .isNNRat _ q n d h => do
      let _i ← synthInstanceQ q(Field $α)
      let _i ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      have z : Q(Nat) := Lean.mkRawNatLit q.floor.toNat
letI : z =Q n / d := ⟨⟩
      return .isNat q(inferInstance) z q(isNat_intFloor_ofIsNNRat $x $n $d $h)
    | .isNegNNRat _ q n d h => do
      let _i ← synthInstanceQ q(Field $α)
      let _i ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      have z : Q(Nat) := Lean.mkRawNatLit (-q.floor).toNat
letI : z =Q (-(-$n / $d) : Int).toNat := ⟨⟩
      return .isNegNat q(inferInstance) z q(isInt_intFloor_ofIsRat_neg $x $n $d $h)
  | _, _, _ => failure

/--
theorem `isNat_intCeil` / 定理 `isNat_intCeil`

English:
theorem isNat_intCeil
  statement: {R} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
  proof: by rintro ⟨⟨⟩⟩; exact ⟨by simp⟩

中文:
定理 is自然数_intCeil
  结论: {R} [环 R] [线性序 R] [是StrictOrdered环 R] [Floor环 R]
  证明: by rintro ⟨⟨⟩⟩; exact ⟨by simp⟩
-/
theorem isNat_intCeil {R} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    (r : R) (m : Nat) :
    IsNat r m -> IsNat ⌈r⌉ m := by rintro ⟨⟨⟩⟩; exact ⟨by simp⟩

/--
theorem `isInt_intCeil` / 定理 `isInt_intCeil`

English:
theorem isInt_intCeil
  statement: {R} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
  proof: by rintro ⟨⟨⟩⟩; exact ⟨by simp⟩

中文:
定理 is整数_intCeil
  结论: {R} [环 R] [线性序 R] [是StrictOrdered环 R] [Floor环 R]
  证明: by rintro ⟨⟨⟩⟩; exact ⟨by simp⟩
-/
theorem isInt_intCeil {R} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    (r : R) (m : Int) :
    IsInt r m -> IsInt ⌈r⌉ m := by rintro ⟨⟨⟩⟩; exact ⟨by simp⟩

/--
theorem `isNat_intCeil_ofIsNNRat` / 定理 `isNat_intCeil_ofIsNNRat`

English:
theorem isNat_intCeil_ofIsNNRat
  given: (r : α) (n : Nat) (d : Nat)
  proof: by
  rintro ⟨inv, rfl⟩
  constructor
  simp only [invOf_eq_inv, ← div_eq_mul_inv]
  rw [← ceil_intCast_div_natCast n d]; rw [← ceil_cast (α := α)]; rw [Rat.cast_div]; rw [cast_intCast]; rw [cast_natCast]; rw [Int.cast_natCast]; rw [Int.natCast_toNat_eq_self.mpr (ceil_nonneg (div_nonneg n.cast_nonneg

中文:
定理 is自然数_intCeil_ofIsNNRat
  条件: (r : α) (n : 自然数) (d : 自然数)
  证明: by
  rintro ⟨inv, rfl⟩
  constructor
  simp only [invOf_eq_inv, ← div_eq_mul_inv]
  rw [← ceil_intCast_div_natCast n d]; rw [← ceil_cast (α := α)]; rw [Rat.cast_div]; rw [cast_intCast]; rw [cast_natCast]; rw [Int.cast_natCast]; rw [Int.natCast_toNat_eq_self.mpr (ceil_nonneg (div_nonneg n.cast_nonneg

Depends on / 依赖: Int.cast_natCast, Int.natCast_toNat_eq_self.mpr, Rat.cast_div, cast_div, cast_intCast, cast_natCast, cast_nonneg, ceil_cast, ceil_intCast_div_natCast, ceil_nonneg, d.cast_nonneg, div_eq_mul_inv, div_nonneg, invOf_eq_inv, n.cast_nonneg, natCast_toNat_eq_self
-/
theorem isNat_intCeil_ofIsNNRat (r : α) (n : Nat) (d : Nat) :
    IsNNRat r n d -> IsNat ⌈r⌉ (-(-n / d) : Int).toNat := by
  rintro ⟨inv, rfl⟩
  constructor
  simp only [invOf_eq_inv, ← div_eq_mul_inv]
  rw [← ceil_intCast_div_natCast n d]; rw [← ceil_cast (α := α)]; rw [Rat.cast_div]; rw [cast_intCast]; rw [cast_natCast]; rw [Int.cast_natCast]; rw [Int.natCast_toNat_eq_self.mpr (ceil_nonneg (div_nonneg n.cast_nonneg d.cast_nonneg))]

/--
theorem `isInt_intCeil_ofIsRat_neg` / 定理 `isInt_intCeil_ofIsRat_neg`

English:
theorem isInt_intCeil_ofIsRat_neg
  given: (r : α) (n : Nat) (d : Nat)
  proof: by
  rintro ⟨inv, rfl⟩
  constructor
  simp only [invOf_eq_inv, ← div_eq_mul_inv, Int.cast_id]
  rw [@negOfNat_eq (n / d)]; rw [ofNat_eq_natCast]; rw [← ofNat_ediv_ofNat]; rw [← floor_natCast_div_natCast n d]; rw [floor_natCast_div_natCast n d]; rw [← neg_neg (n : Int)]; rw [← ofNat_eq_natCast]; rw 

中文:
定理 is整数_intCeil_ofIsRat_neg
  条件: (r : α) (n : 自然数) (d : 自然数)
  证明: by
  rintro ⟨inv, rfl⟩
  constructor
  simp only [invOf_eq_inv, ← div_eq_mul_inv, Int.cast_id]
  rw [@negOfNat_eq (n / d)]; rw [ofNat_eq_natCast]; rw [← ofNat_ediv_ofNat]; rw [← floor_natCast_div_natCast n d]; rw [floor_natCast_div_natCast n d]; rw [← neg_neg (n : Int)]; rw [← ofNat_eq_natCast]; rw 

Depends on / 依赖: Int.cast_id, Rat.cast_div, cast_div, cast_id, cast_intCast, cast_natCast, ceil_cast, ceil_intCast_div_natCast, div_eq_mul_inv, floor_natCast_div_natCast, invOf_eq_inv, negOfNat, negOfNat_eq, neg_neg, ofNat_ediv_ofNat, ofNat_eq_natCast
-/
theorem isInt_intCeil_ofIsRat_neg (r : α) (n : Nat) (d : Nat) :
    IsRat r (.negOfNat n) d -> IsInt ⌈r⌉ (.negOfNat (n / d)) := by
  rintro ⟨inv, rfl⟩
  constructor
  simp only [invOf_eq_inv, ← div_eq_mul_inv, Int.cast_id]
  rw [@negOfNat_eq (n / d)]; rw [ofNat_eq_natCast]; rw [← ofNat_ediv_ofNat]; rw [← floor_natCast_div_natCast n d]; rw [floor_natCast_div_natCast n d]; rw [← neg_neg (n : Int)]; rw [← ofNat_eq_natCast]; rw [← negOfNat_eq]; rw [← ceil_intCast_div_natCast (.negOfNat n) d]; rw [← ceil_cast (α := α)]; rw [Rat.cast_div]; rw [cast_intCast]; rw [cast_natCast]

/-- `norm_num` extension for `Int.ceil` -/
@[norm_num ⌈_⌉]
meta def evalIntCeil : NormNumExt where eval {u αZ} e := do
  match u, αZ, e with
  | 0, ~q(Int), ~q(@Int.ceil $α $instR $instO $instF $x) =>
    match ← derive x with
    | .isBool .. => failure
    | .isNat _ _ pb => do
      let _i ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      return .isNat q(inferInstance) _ q(isNat_intCeil $x _ $pb)
    | .isNegNat _ _ pb => do
      let _i ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      -- ceil always keeps naturals negative, so we can shortcut `.isInt`
      return .isNegNat q(inferInstance) _ q(isInt_intCeil _ _ $pb)
    | .isNNRat _ q n d h => do
      let _i ← synthInstanceQ q(Field $α)
      let _i ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      have z : Q(Nat) := Lean.mkRawNatLit q.ceil.toNat
letI : z =Q (-(-$n / $d) : Int).toNat := ⟨⟩
      return .isNat q(inferInstance) z q(isNat_intCeil_ofIsNNRat $x $n $d $h)
    | .isNegNNRat _ q n d h => do
      let _i ← synthInstanceQ q(Field $α)
      let _i ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      have z : Q(Nat) := Lean.mkRawNatLit (-q.ceil).toNat
letI : z =Q n / d := ⟨⟩
      return .isNegNat q(inferInstance) z q(isInt_intCeil_ofIsRat_neg $x $n $d $h)
  | _, _, _ => failure

/--
theorem `isNat_intFract_of_isNat` / 定理 `isNat_intFract_of_isNat`

English:
theorem isNat_intFract_of_isNat
  given: (r : R) (m : Nat)
  statement: IsNat r m -> IsNat (Int.fract r) 0
  proof: by
  rintro ⟨⟨⟩⟩; exact ⟨by simp⟩

中文:
定理 is自然数_intFract_of_is自然数
  条件: (r : R) (m : 自然数)
  结论: 是自然数 r m -> 是自然数 (整数.fract r) 0
  证明: by
  rintro ⟨⟨⟩⟩; exact ⟨by simp⟩
-/
theorem isNat_intFract_of_isNat (r : R) (m : Nat) : IsNat r m -> IsNat (Int.fract r) 0 := by
  rintro ⟨⟨⟩⟩; exact ⟨by simp⟩

/--
theorem `isNat_intFract_of_isInt` / 定理 `isNat_intFract_of_isInt`

English:
theorem isNat_intFract_of_isInt
  given: (r : R) (m : Int)
  statement: IsInt r m -> IsNat (Int.fract r) 0
  proof: by
  rintro ⟨⟨⟩⟩; exact ⟨by simp⟩

中文:
定理 is自然数_intFract_of_is整数
  条件: (r : R) (m : 整数)
  结论: 是整数 r m -> 是自然数 (整数.fract r) 0
  证明: by
  rintro ⟨⟨⟩⟩; exact ⟨by simp⟩
-/
theorem isNat_intFract_of_isInt (r : R) (m : Int) : IsInt r m -> IsNat (Int.fract r) 0 := by
  rintro ⟨⟨⟩⟩; exact ⟨by simp⟩

/--
theorem `isNNRat_intFract_of_isNNRat` / 定理 `isNNRat_intFract_of_isNNRat`

English:
theorem isNNRat_intFract_of_isNNRat
  given: (r : α) (n d : Nat)
  proof: by
  rintro ⟨inv, rfl⟩
  refine ⟨inv, ?_⟩
  simp only [invOf_eq_inv, ← div_eq_mul_inv, fract_div_natCast_eq_div_natCast_mod]

中文:
定理 isNNRat_intFract_of_isNNRat
  条件: (r : α) (n d : 自然数)
  证明: by
  rintro ⟨inv, rfl⟩
  refine ⟨inv, ?_⟩
  simp only [invOf_eq_inv, ← div_eq_mul_inv, fract_div_natCast_eq_div_natCast_mod]

Depends on / 依赖: div_eq_mul_inv, fract_div_natCast_eq_div_natCast_mod, invOf_eq_inv
-/
theorem isNNRat_intFract_of_isNNRat (r : α) (n d : Nat) :
    IsNNRat r n d -> IsNNRat (Int.fract r) (n % d) d := by
  rintro ⟨inv, rfl⟩
  refine ⟨inv, ?_⟩
  simp only [invOf_eq_inv, ← div_eq_mul_inv, fract_div_natCast_eq_div_natCast_mod]

/--
theorem `isRat_intFract_of_isRat_negOfNat` / 定理 `isRat_intFract_of_isRat_negOfNat`

English:
theorem isRat_intFract_of_isRat_negOfNat
  given: (r : α) (n d : Nat)
  proof: by
  rintro ⟨inv, rfl⟩
  refine ⟨inv, ?_⟩
  simp only [invOf_eq_inv, ← div_eq_mul_inv, fract_div_intCast_eq_div_intCast_mod,
    negOfNat_eq, ofNat_eq_natCast]

中文:
定理 isRat_intFract_of_isRat_negOf自然数
  条件: (r : α) (n d : 自然数)
  证明: by
  rintro ⟨inv, rfl⟩
  refine ⟨inv, ?_⟩
  simp only [invOf_eq_inv, ← div_eq_mul_inv, fract_div_intCast_eq_div_intCast_mod,
    negOfNat_eq, ofNat_eq_natCast]

Depends on / 依赖: div_eq_mul_inv, fract_div_intCast_eq_div_intCast_mod, invOf_eq_inv, negOfNat_eq, ofNat_eq_natCast
-/
theorem isRat_intFract_of_isRat_negOfNat (r : α) (n d : Nat) :
    IsRat r (negOfNat n) d -> IsRat (Int.fract r) (-n % d) d := by
  rintro ⟨inv, rfl⟩
  refine ⟨inv, ?_⟩
  simp only [invOf_eq_inv, ← div_eq_mul_inv, fract_div_intCast_eq_div_intCast_mod,
    negOfNat_eq, ofNat_eq_natCast]

/-- `norm_num` extension for `Int.fract` -/
@[norm_num (Int.fract _)]
meta def evalIntFract : NormNumExt where eval {u α} e := do
  match e with
  | ~q(@Int.fract _ $instR $instO $instF $x) =>
    match ← derive x with
    | .isBool .. => failure
    | .isNat _ _ pb => do
      let _i ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      have z : Q(Nat) := Lean.mkRawNatLit 0
letI : z =Q 0 := ⟨⟩
      return .isNat _ z q(isNat_intFract_of_isNat $x _ $pb)
    | .isNegNat _ _ pb => do
      let _i ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      have z : Q(Nat) := Lean.mkRawNatLit 0
letI : z =Q 0 := ⟨⟩
      return .isNat _ z q(isNat_intFract_of_isInt _ _ $pb)
    | .isNNRat _ q n d h => do
      let _i ← synthInstanceQ q(Field $α)
      let _i ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      have n' : Q(Nat) := Lean.mkRawNatLit (q.num.natAbs % q.den)
letI : n' =Q n % d := ⟨⟩
      return .isNNRat _ (q - Rat.floor q) n' d q(isNNRat_intFract_of_isNNRat _ $n $d $h)
    | .isNegNNRat _ q n d h => do
      let _i ← synthInstanceQ q(Field $α)
      let _i ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      have n' : Q(Int) := mkRawIntLit (q.num % q.den)
letI : n' =Q - n % d := ⟨⟩
      return .isRat _ (q - Rat.floor q) n' d q(isRat_intFract_of_isRat_negOfNat _ $n $d $h)
  | _, _, _ => failure


/--
theorem `isNat_round` / 定理 `isNat_round`

English:
theorem isNat_round
  statement: {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
  proof: by
  rintro ⟨⟨⟩⟩; exact ⟨by simp⟩

中文:
定理 is自然数_round
  结论: {R : 类型} [环 R] [线性序 R] [是StrictOrdered环 R] [Floor环 R]
  证明: by
  rintro ⟨⟨⟩⟩; exact ⟨by simp⟩
-/
theorem isNat_round {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    (r : R) (m : Nat) : IsNat r m -> IsNat (round r) m := by
  rintro ⟨⟨⟩⟩; exact ⟨by simp⟩

/--
theorem `isInt_round` / 定理 `isInt_round`

English:
theorem isInt_round
  statement: {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
  proof: by
  rintro ⟨⟨⟩⟩; exact ⟨by simp⟩

中文:
定理 is整数_round
  结论: {R : 类型} [环 R] [线性序 R] [是StrictOrdered环 R] [Floor环 R]
  证明: by
  rintro ⟨⟨⟩⟩; exact ⟨by simp⟩
-/
theorem isInt_round {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    (r : R) (m : Int) : IsInt r m -> IsInt (round r) m := by
  rintro ⟨⟨⟩⟩; exact ⟨by simp⟩

/--
theorem `IsRat.isInt_round` / 定理 `IsRat.isInt_round`

English:
theorem IsRat.isInt_round
  statement: {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  proof: by
  rintro ⟨inv, rfl⟩
  subst res
  constructor
  rw [invOf_eq_inv]; rw [← div_eq_mul_inv]
  norm_cast

中文:
定理 是有理数.is整数_round
  结论: {R : 类型} [域 R] [线性序 R] [是StrictOrdered环 R]
  证明: by
  rintro ⟨inv, rfl⟩
  subst res
  constructor
  rw [invOf_eq_inv]; rw [← div_eq_mul_inv]
  norm_cast

Depends on / 依赖: div_eq_mul_inv, invOf_eq_inv
-/
theorem IsRat.isInt_round {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [FloorRing R] (r : R) (n : Int) (d : Nat) (res : Int) (hres : round (n / d : Rat) = res) :
    IsRat r n d -> IsInt (round r) res := by
  rintro ⟨inv, rfl⟩
  subst res
  constructor
  rw [invOf_eq_inv]; rw [← div_eq_mul_inv]
  norm_cast

/-- local copy tagged `meta` for evaluation of `round` below -/
private meta local instance : FloorRing Rat :=
  (FloorRing.ofFloor Rat Rat.floor) fun _ _ => Rat.le_floor_iff.symm

/-- `norm_num` extension for `round` -/
@[norm_num round _]
meta def evalRound : NormNumExt where eval {u αZ} e := do
  match u, αZ, e with
  | 0, ~q(Int), ~q(@round $α $instRing $instLinearOrder $instFloorRing $x) =>
    match ← derive x with
    | .isBool .. => failure
    | .isNat sα nb pb => do
      let instIsStrictOrderedRing ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      return .isNat q(inferInstance) nb q(isNat_round $x _ $pb)
    | .isNegNat sα nb pb => do
      let _instIsStrictOrderedRing ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      return .isNegNat q(inferInstance) nb q(isInt_round _ _ $pb)
    | .isNNRat _ q n d h => do
      let _instField ← synthInstanceQ q(Field $α)
      let _instIsStrictOrderedRing ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      have z : Q(Int) := mkRawIntLit (round q)
haveI : z =Q round (Int.ofNat $n / $d : Rat) := ⟨⟩
      return .isInt q(inferInstance) z (round q)
        q(IsRat.isInt_round $x $n $d $z rfl (IsNNRat.to_isRat $h))
    | .isNegNNRat _ q n d h => do
      let _instField ← synthInstanceQ q(Field $α)
      let _instIsStrictOrderedRing ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      have z : Q(Int) := mkRawIntLit (round q)
haveI : z =Q round ((Int.negOfNat $n) / $d : Rat) := ⟨⟩
      return .isInt q(inferInstance) z (round q) q(IsRat.isInt_round $x (.negOfNat $n) $d $z rfl $h)
  | _, _, _ => failure

end NormNum

end Rat

/--
theorem `Int.mod_nat_eq_sub_mul_floor_rat_div` / 定理 `Int.mod_nat_eq_sub_mul_floor_rat_div`

English:
theorem Int.mod_nat_eq_sub_mul_floor_rat_div
  given: {n : Int} {d : Nat}
  statement: n % d = n - d * ⌊(n : Rat) / d⌋
  proof: by
  rw [Int.emod_def]; rw [Rat.floor_intCast_div_natCast]

中文:
定理 整数.mod_nat_eq_sub_mul_floor_rat_div
  条件: {n : 整数} {d : 自然数}
  结论: n % d = n - d * ⌊(n : 有理数) / d⌋
  证明: by
  rw [Int.emod_def]; rw [Rat.floor_intCast_div_natCast]

Depends on / 依赖: Int.emod_def, Rat.floor_intCast_div_natCast, emod_def, floor_intCast_div_natCast
-/
theorem Int.mod_nat_eq_sub_mul_floor_rat_div {n : Int} {d : Nat} : n % d = n - d * ⌊(n : Rat) / d⌋ := by
  rw [Int.emod_def]; rw [Rat.floor_intCast_div_natCast]

/--
theorem `Nat.coprime_sub_mul_floor_rat_div_of_coprime` / 定理 `Nat.coprime_sub_mul_floor_rat_div_of_coprime`

English:
theorem Nat.coprime_sub_mul_floor_rat_div_of_coprime
  given: {n d : Nat} (n_coprime_d : n.Coprime d)
  proof: by
  have : (n : Int) % d = n - d * ⌊(n : Rat) / d⌋ := Int.mod_nat_eq_sub_mul_floor_rat_div
  rw [← this]
  have : d.Coprime n := n_coprime_d.symm
  rwa [Nat.Coprime, Nat.gcd_rec] at this

中文:
定理 自然数.coprime_sub_mul_floor_rat_div_of_coprime
  条件: {n d : 自然数} (n_coprime_d : n.Coprime d)
  证明: by
  have : (n : Int) % d = n - d * ⌊(n : Rat) / d⌋ := Int.mod_nat_eq_sub_mul_floor_rat_div
  rw [← this]
  have : d.Coprime n := n_coprime_d.symm
  rwa [Nat.Coprime, Nat.gcd_rec] at this

Depends on / 依赖: Coprime, Int.mod_nat_eq_sub_mul_floor_rat_div, Nat.Coprime, Nat.gcd_rec, d.Coprime, gcd_rec, mod_nat_eq_sub_mul_floor_rat_div, n_coprime_d, n_coprime_d.symm
-/
theorem Nat.coprime_sub_mul_floor_rat_div_of_coprime {n d : Nat} (n_coprime_d : n.Coprime d) :
    ((n : Int) - d * ⌊(n : Rat) / d⌋).natAbs.Coprime d := by
  have : (n : Int) % d = n - d * ⌊(n : Rat) / d⌋ := Int.mod_nat_eq_sub_mul_floor_rat_div
  rw [← this]
  have : d.Coprime n := n_coprime_d.symm
  rwa [Nat.Coprime, Nat.gcd_rec] at this

namespace Rat

/--
theorem `num_lt_succ_floor_mul_den` / 定理 `num_lt_succ_floor_mul_den`

English:
theorem num_lt_succ_floor_mul_den
  given: (q : Rat)
  statement: q.num < (⌊q⌋ + 1) * q.den
  proof: by
  suffices (q.num : Rat) < (⌊q⌋ + 1) * q.den from mod_cast this
  suffices (q.num : Rat) < (q - fract q + 1) * q.den by
have : (⌊q⌋ : Rat) = q - fract q := eq_sub_of_add_eq floor_add_fract q
    rwa [this]
  suffices (q.num : Rat) < q.num + (1 - fract q) * q.den by
    have : (q - fract q + 1) * 

中文:
定理 num_lt_succ_floor_mul_den
  条件: (q : 有理数)
  结论: q.num < (⌊q⌋ + 1) * q.den
  证明: by
  suffices (q.num : Rat) < (⌊q⌋ + 1) * q.den from mod_cast this
  suffices (q.num : Rat) < (q - fract q + 1) * q.den by
have : (⌊q⌋ : Rat) = q - fract q := eq_sub_of_add_eq floor_add_fract q
    rwa [this]
  suffices (q.num : Rat) < q.num + (1 - fract q) * q.den by
    have : (q - fract q + 1) * 

Depends on / 依赖: add_mul, eq_sub_of_add_eq, floor_add_fract, mod_cast, q.den, q.num
-/
theorem num_lt_succ_floor_mul_den (q : Rat) : q.num < (⌊q⌋ + 1) * q.den := by
  suffices (q.num : Rat) < (⌊q⌋ + 1) * q.den from mod_cast this
  suffices (q.num : Rat) < (q - fract q + 1) * q.den by
have : (⌊q⌋ : Rat) = q - fract q := eq_sub_of_add_eq floor_add_fract q
    rwa [this]
  suffices (q.num : Rat) < q.num + (1 - fract q) * q.den by
    have : (q - fract q + 1) * q.den = q.num + (1 - fract q) * q.den := by
      calc
        (q - fract q + 1) * q.den = (q + (1 - fract q)) * q.den := by ring
        _ = q * q.den + (1 - fract q) * q.den := by rw [add_mul]
        _ = q.num + (1 - fract q) * q.den := by simp
    rwa [this]
  suffices 0 < (1 - fract q) * q.den by
    rw [← sub_lt_iff_lt_add']
    simpa
  have : 0 < 1 - fract q := by
    have : fract q < 1 := fract_lt_one q
    have : 0 + fract q < 1 := by simp [this]
    rwa [lt_sub_iff_add_lt]
  exact mul_pos this (by exact mod_cast q.pos)

/--
theorem `fract_inv_num_lt_num_of_pos` / 定理 `fract_inv_num_lt_num_of_pos`

English:
theorem fract_inv_num_lt_num_of_pos
  given: {q : Rat} (q_pos : 0 < q)
  statement: (fract q⁻¹).num < q.num
  proof: by
  -- we know that the numerator must be positive
  have q_num_pos : 0 < q.num := Rat.num_pos.mpr q_pos
  -- we will work with the absolute value of the numerator, which is equal to the numerator
  have q_num_abs_eq_q_num : (q.num.natAbs : Int) = q.num := Int.natAbs_of_nonneg q_num_pos.le
  set q_

中文:
定理 fract_inv_num_lt_num_of_pos
  条件: {q : 有理数} (q_pos : 0 < q)
  结论: (fract q⁻¹).num < q.num
  证明: by
  -- we know that the numerator must be positive
  have q_num_pos : 0 < q.num := Rat.num_pos.mpr q_pos
  -- we will work with the absolute value of the numerator, which is equal to the numerator
  have q_num_abs_eq_q_num : (q.num.natAbs : Int) = q.num := Int.natAbs_of_nonneg q_num_pos.le
  set q_
-/
theorem fract_inv_num_lt_num_of_pos {q : Rat} (q_pos : 0 < q) : (fract q⁻¹).num < q.num := by
  -- we know that the numerator must be positive
  have q_num_pos : 0 < q.num := Rat.num_pos.mpr q_pos
  -- we will work with the absolute value of the numerator, which is equal to the numerator
  have q_num_abs_eq_q_num : (q.num.natAbs : Int) = q.num := Int.natAbs_of_nonneg q_num_pos.le
  set q_inv : Rat := q.den / q.num with q_inv_def
  have q_inv_eq : q⁻¹ = q_inv := by rw [q_inv_def, inv_def, divInt_eq_div, Int.cast_natCast]
  suffices (q_inv - ⌊q_inv⌋).num < q.num by rwa [q_inv_eq]
  suffices ((q.den - q.num * ⌊q_inv⌋ : Rat) / q.num).num < q.num by
    simp only [gt_iff_lt, q_inv]
    field_simp
    simp [q_inv, this]
  suffices (q.den : Int) - q.num * ⌊q_inv⌋ < q.num by
    -- use that `q.num` and `q.den` are coprime to show that the numerator stays unreduced
    have : ((q.den - q.num * ⌊q_inv⌋ : Rat) / q.num).num = q.den - q.num * ⌊q_inv⌋ := by
      suffices ((q.den : Int) - q.num * ⌊q_inv⌋).natAbs.Coprime q.num.natAbs from
        mod_cast Rat.num_div_eq_of_coprime q_num_pos this
      have tmp := Nat.coprime_sub_mul_floor_rat_div_of_coprime q.reduced.symm
      simpa only [Nat.cast_natAbs, abs_of_nonneg q_num_pos.le] using! tmp
    rwa [this]
  -- to show the claim, start with the following inequality
  have q_inv_num_denom_ineq : q⁻¹.num - ⌊q⁻¹⌋ * q⁻¹.den < q⁻¹.den := by
    have : q⁻¹.num < (⌊q⁻¹⌋ + 1) * q⁻¹.den := Rat.num_lt_succ_floor_mul_den q⁻¹
    have : q⁻¹.num < ⌊q⁻¹⌋ * q⁻¹.den + q⁻¹.den := by rwa [right_distrib, one_mul] at this
    rwa [← sub_lt_iff_lt_add'] at this
  -- use that `q.num` and `q.den` are coprime to show that q_inv is the unreduced reciprocal
  -- of `q`
  have : q_inv.num = q.den ∧ q_inv.den = q.num.natAbs := by
    have coprime_q_denom_q_num : q.den.Coprime q.num.natAbs := q.reduced.symm
    have : Int.natAbs q.den = q.den := by simp
    rw [← this] at coprime_q_denom_q_num
    rw [q_inv_def]
    constructor
    · exact mod_cast Rat.num_div_eq_of_coprime q_num_pos coprime_q_denom_q_num
    · suffices (((q.den : Rat) / q.num).den : Int) = q.num.natAbs by exact mod_cast this
      rw [q_num_abs_eq_q_num]
      exact mod_cast Rat.den_div_eq_of_coprime q_num_pos coprime_q_denom_q_num
  rwa [q_inv_eq, this.left, this.right, q_num_abs_eq_q_num, mul_comm] at q_inv_num_denom_ineq

end Rat
