/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public meta import Mathlib.Data.Rat.Floor

public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.Order.Ring.NNRat
public import Mathlib.Data.Rat.Floor

/-!
# Floor Function for Non-negative Rational Numbers

## Summary

We define the `FloorSemiring` instance on `ℚ≥0`, and relate its operators to `NNRat.cast`.

Note that we cannot talk about `Int.fract`, which currently only works for rings.

## Tags

nnrat, rationals, ℚ≥0, floor
-/

@[expose] public section

assert_not_exists Finset

namespace NNRat

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FloorSemiring Rat>=0
  body: ⌊q.val⌋₊
  ceil q := ⌈q.val⌉₊
  floor_of_neg h := by simpa using h.trans zero_lt_one
  gc_floor {a n} h := by rw [← NNRat.coe_le_coe, Nat.le_floor_iff] <;> norm_cast
  gc_ceil {a b} := by rw [← NNRat.coe_le_coe, Nat.ceil_le]; norm_cast

@[simp, norm_cast]

中文:
实例 :
  签名: FloorSemiring Rat>=0
  定义体: ⌊q.val⌋₊
  ceil q := ⌈q.val⌉₊
  floor_of_neg h := by simpa using h.trans zero_lt_one
  gc_floor {a n} h := by rw [← NNRat.coe_le_coe, Nat.le_floor_iff] <;> norm_cast
  gc_ceil {a b} := by rw [← NNRat.coe_le_coe, Nat.ceil_le]; norm_cast

@[simp, norm_cast]

Depends on / 依赖: q.val
-/
instance : FloorSemiring Rat>=0 where
  floor q := ⌊q.val⌋₊
  ceil q := ⌈q.val⌉₊
  floor_of_neg h := by simpa using h.trans zero_lt_one
  gc_floor {a n} h := by rw [← NNRat.coe_le_coe, Nat.le_floor_iff] <;> norm_cast
  gc_ceil {a b} := by rw [← NNRat.coe_le_coe, Nat.ceil_le]; norm_cast

@[simp, norm_cast]
/--
theorem `floor_coe` / 定理 `floor_coe`

English:
theorem floor_coe
  given: (q : Rat>=0)
  statement: ⌊(q : Rat)⌋₊ = ⌊q⌋₊
  proof: rfl

@[simp, norm_cast]

中文:
定理 floor_coe
  条件: (q : Rat>=0)
  结论: ⌊(q : Rat)⌋₊ = ⌊q⌋₊
  证明: rfl

@[simp, norm_cast]
-/
theorem floor_coe (q : Rat>=0) : ⌊(q : Rat)⌋₊ = ⌊q⌋₊ := rfl

@[simp, norm_cast]
/--
theorem `ceil_coe` / 定理 `ceil_coe`

English:
theorem ceil_coe
  given: (q : Rat>=0)
  statement: ⌈(q : Rat)⌉₊ = ⌈q⌉₊
  proof: rfl

@[simp, norm_cast]

中文:
定理 ceil_coe
  条件: (q : Rat>=0)
  结论: ⌈(q : Rat)⌉₊ = ⌈q⌉₊
  证明: rfl

@[simp, norm_cast]
-/
theorem ceil_coe (q : Rat>=0) : ⌈(q : Rat)⌉₊ = ⌈q⌉₊ := rfl

@[simp, norm_cast]
/--
theorem `coe_floor` / 定理 `coe_floor`

English:
theorem coe_floor
  given: (q : Rat>=0)
  statement: ↑⌊q⌋₊ = ⌊(q : Rat)⌋
  proof: Int.natCast_floor_eq_floor q.coe_nonneg

@[simp, norm_cast]

中文:
定理 coe_floor
  条件: (q : Rat>=0)
  结论: ↑⌊q⌋₊ = ⌊(q : Rat)⌋
  证明: Int.natCast_floor_eq_floor q.coe_nonneg

@[simp, norm_cast]

Depends on / 依赖: Int.natCast_floor_eq_floor, coe_nonneg, natCast_floor_eq_floor, q.coe_nonneg
-/
theorem coe_floor (q : Rat>=0) : ↑⌊q⌋₊ = ⌊(q : Rat)⌋ := Int.natCast_floor_eq_floor q.coe_nonneg

@[simp, norm_cast]
/--
theorem `coe_ceil` / 定理 `coe_ceil`

English:
theorem coe_ceil
  given: (q : Rat>=0)
  statement: ↑⌈q⌉₊ = ⌈(q : Rat)⌉
  proof: Int.natCast_ceil_eq_ceil q.coe_nonneg

中文:
定理 coe_ceil
  条件: (q : Rat>=0)
  结论: ↑⌈q⌉₊ = ⌈(q : Rat)⌉
  证明: Int.natCast_ceil_eq_ceil q.coe_nonneg

Depends on / 依赖: Int.natCast_ceil_eq_ceil, coe_nonneg, natCast_ceil_eq_ceil, q.coe_nonneg
-/
theorem coe_ceil (q : Rat>=0) : ↑⌈q⌉₊ = ⌈(q : Rat)⌉ := Int.natCast_ceil_eq_ceil q.coe_nonneg

/--
theorem `floor_def` / 定理 `floor_def`

English:
theorem floor_def
  given: (q : Rat>=0)
  statement: ⌊q⌋₊ = q.num / q.den
  proof: by
  rw [← Int.natCast_inj]; rw [NNRat.coe_floor]; rw [Rat.floor_def']; rw [Int.natCast_ediv]; rw [den_coe]; rw [num_coe]

中文:
定理 floor_def
  条件: (q : Rat>=0)
  结论: ⌊q⌋₊ = q.num / q.den
  证明: by
  rw [← Int.natCast_inj]; rw [NNRat.coe_floor]; rw [Rat.floor_def']; rw [Int.natCast_ediv]; rw [den_coe]; rw [num_coe]
-/
protected theorem floor_def (q : Rat>=0) : ⌊q⌋₊ = q.num / q.den := by
  rw [← Int.natCast_inj]; rw [NNRat.coe_floor]; rw [Rat.floor_def']; rw [Int.natCast_ediv]; rw [den_coe]; rw [num_coe]

section Semifield

variable {K} [Semifield K] [LinearOrder K] [IsStrictOrderedRing K] [FloorSemiring K]

@[simp, norm_cast]
/--
theorem `floor_cast` / 定理 `floor_cast`

English:
theorem floor_cast
  given: (x : Rat>=0)
  statement: ⌊(x : K)⌋₊ = ⌊x⌋₊
  proof: (Nat.floor_eq_iff x.cast_nonneg).2 (mod_cast (Nat.floor_eq_iff x.cast_nonneg).1 (Eq.refl ⌊x⌋₊))

@[simp, norm_cast]

中文:
定理 floor_cast
  条件: (x : Rat>=0)
  结论: ⌊(x : K)⌋₊ = ⌊x⌋₊
  证明: (Nat.floor_eq_iff x.cast_nonneg).2 (mod_cast (Nat.floor_eq_iff x.cast_nonneg).1 (Eq.refl ⌊x⌋₊))

@[simp, norm_cast]

Depends on / 依赖: Eq.refl, Nat.floor_eq_iff, cast_nonneg, floor_eq_iff, mod_cast, x.cast_nonneg
-/
theorem floor_cast (x : Rat>=0) : ⌊(x : K)⌋₊ = ⌊x⌋₊ :=
  (Nat.floor_eq_iff x.cast_nonneg).2 (mod_cast (Nat.floor_eq_iff x.cast_nonneg).1 (Eq.refl ⌊x⌋₊))

@[simp, norm_cast]
/--
theorem `ceil_cast` / 定理 `ceil_cast`

English:
theorem ceil_cast
  given: (x : Rat>=0)
  statement: ⌈(x : K)⌉₊ = ⌈x⌉₊
  proof: by
  obtain rfl | hx := eq_or_ne x 0
  · simp
  · refine (Nat.ceil_eq_iff ?_).2 (mod_cast (Nat.ceil_eq_iff ?_).1 (Eq.refl ⌈x⌉₊)) <;> simpa

中文:
定理 ceil_cast
  条件: (x : Rat>=0)
  结论: ⌈(x : K)⌉₊ = ⌈x⌉₊
  证明: by
  obtain rfl | hx := eq_or_ne x 0
  · simp
  · refine (Nat.ceil_eq_iff ?_).2 (mod_cast (Nat.ceil_eq_iff ?_).1 (Eq.refl ⌈x⌉₊)) <;> simpa

Depends on / 依赖: Eq.refl, Nat.ceil_eq_iff, ceil_eq_iff, eq_or_ne, mod_cast
-/
theorem ceil_cast (x : Rat>=0) : ⌈(x : K)⌉₊ = ⌈x⌉₊ := by
  obtain rfl | hx := eq_or_ne x 0
  · simp
  · refine (Nat.ceil_eq_iff ?_).2 (mod_cast (Nat.ceil_eq_iff ?_).1 (Eq.refl ⌈x⌉₊)) <;> simpa

end Semifield

section Field

variable {K} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

@[simp, norm_cast]
/--
theorem `intFloor_cast` / 定理 `intFloor_cast`

English:
theorem intFloor_cast
  given: (x : Rat>=0)
  statement: ⌊(x : K)⌋ = ⌊(x : Rat)⌋
  proof: by
  rw [Int.floor_eq_iff]; rw [← coe_floor]
  norm_cast
  norm_cast
  rw [Nat.cast_add_one]; rw [← Nat.floor_eq_iff zero_le]

@[simp, norm_cast]

中文:
定理 intFloor_cast
  条件: (x : Rat>=0)
  结论: ⌊(x : K)⌋ = ⌊(x : Rat)⌋
  证明: by
  rw [Int.floor_eq_iff]; rw [← coe_floor]
  norm_cast
  norm_cast
  rw [Nat.cast_add_one]; rw [← Nat.floor_eq_iff zero_le]

@[simp, norm_cast]

Depends on / 依赖: Int.floor_eq_iff, Nat.cast_add_one, Nat.floor_eq_iff, cast_add_one, coe_floor, floor_eq_iff, zero_le
-/
theorem intFloor_cast (x : Rat>=0) : ⌊(x : K)⌋ = ⌊(x : Rat)⌋ := by
  rw [Int.floor_eq_iff]; rw [← coe_floor]
  norm_cast
  norm_cast
  rw [Nat.cast_add_one]; rw [← Nat.floor_eq_iff zero_le]

@[simp, norm_cast]
/--
theorem `intCeil_cast` / 定理 `intCeil_cast`

English:
theorem intCeil_cast
  given: (x : Rat>=0)
  statement: ⌈(x : K)⌉ = ⌈(x : Rat)⌉
  proof: by
  rw [Int.ceil_eq_iff]; rw [← coe_ceil]; rw [sub_lt_iff_lt_add]
  constructor
· exact_mod_cast NNRat.cast_strictMono Nat.ceil_lt_add_one zero_le
  · rw [Int.cast_natCast, NNRat.cast_le_natCast]
    exact Nat.le_ceil _

中文:
定理 intCeil_cast
  条件: (x : Rat>=0)
  结论: ⌈(x : K)⌉ = ⌈(x : Rat)⌉
  证明: by
  rw [Int.ceil_eq_iff]; rw [← coe_ceil]; rw [sub_lt_iff_lt_add]
  constructor
· exact_mod_cast NNRat.cast_strictMono Nat.ceil_lt_add_one zero_le
  · rw [Int.cast_natCast, NNRat.cast_le_natCast]
    exact Nat.le_ceil _

Depends on / 依赖: Int.cast_natCast, Int.ceil_eq_iff, NNRat.cast_le_natCast, NNRat.cast_strictMono, Nat.ceil_lt_add_one, Nat.le_ceil, cast_le_natCast, cast_natCast, cast_strictMono, ceil_eq_iff, ceil_lt_add_one, coe_ceil, le_ceil, sub_lt_iff_lt_add, zero_le
-/
theorem intCeil_cast (x : Rat>=0) : ⌈(x : K)⌉ = ⌈(x : Rat)⌉ := by
  rw [Int.ceil_eq_iff]; rw [← coe_ceil]; rw [sub_lt_iff_lt_add]
  constructor
· exact_mod_cast NNRat.cast_strictMono Nat.ceil_lt_add_one zero_le
  · rw [Int.cast_natCast, NNRat.cast_le_natCast]
    exact Nat.le_ceil _

end Field

@[norm_cast]
/--
theorem `floor_natCast_div_natCast` / 定理 `floor_natCast_div_natCast`

English:
theorem floor_natCast_div_natCast
  given: (n d : Nat)
  statement: ⌊(↑n / ↑d : Rat>=0)⌋₊ = n / d
  proof: Rat.natFloor_natCast_div_natCast n d

中文:
定理 floor_natCast_div_natCast
  条件: (n d : 自然数)
  结论: ⌊(↑n / ↑d : Rat>=0)⌋₊ = n / d
  证明: Rat.natFloor_natCast_div_natCast n d

Depends on / 依赖: Rat.natFloor_natCast_div_natCast, natFloor_natCast_div_natCast
-/
theorem floor_natCast_div_natCast (n d : Nat) : ⌊(↑n / ↑d : Rat>=0)⌋₊ = n / d :=
  Rat.natFloor_natCast_div_natCast n d

end NNRat

namespace Mathlib.Meta.NormNum

open Qq


/--
theorem `IsNat.natCeil` / 定理 `IsNat.natCeil`

English:
theorem IsNat.natCeil
  statement: {R : Type*} [Semiring R] [LinearOrder R] [IsStrictOrderedRing R]
  proof: by
  rintro ⟨⟨⟩⟩
  exact ⟨by simp⟩

中文:
定理 IsNat.natCeil
  结论: {R : 类型} [Semiring R] [LinearOrder R] [IsStrictOrderedRing R]
  证明: by
  rintro ⟨⟨⟩⟩
  exact ⟨by simp⟩
-/
theorem IsNat.natCeil {R : Type*} [Semiring R] [LinearOrder R] [IsStrictOrderedRing R]
    [FloorSemiring R] (r : R) (m : Nat) : IsNat r m -> IsNat (⌈r⌉₊) m := by
  rintro ⟨⟨⟩⟩
  exact ⟨by simp⟩

/--
theorem `IsInt.natCeil` / 定理 `IsInt.natCeil`

English:
theorem IsInt.natCeil
  statement: {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorSemiring R]
  proof: by
  rintro ⟨⟨⟩⟩
  exact ⟨by simp⟩

中文:
定理 IsInt.natCeil
  结论: {R : 类型} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorSemiring R]
  证明: by
  rintro ⟨⟨⟩⟩
  exact ⟨by simp⟩
-/
theorem IsInt.natCeil {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorSemiring R]
    (r : R) (m : Nat) : IsInt r (.negOfNat m) -> IsNat (⌈r⌉₊) 0 := by
  rintro ⟨⟨⟩⟩
  exact ⟨by simp⟩

/--
theorem `IsNNRat.natCeil` / 定理 `IsNNRat.natCeil`

English:
theorem IsNNRat.natCeil
  statement: {R : Type*} [Semifield R] [LinearOrder R] [IsStrictOrderedRing R]
  proof: by
  constructor
  rw [← hres]; rw [h.to_eq rfl rfl]; rw [← @NNRat.ceil_cast R]
  simp

中文:
定理 IsNNRat.natCeil
  结论: {R : 类型} [Semifield R] [LinearOrder R] [IsStrictOrderedRing R]
  证明: by
  constructor
  rw [← hres]; rw [h.to_eq rfl rfl]; rw [← @NNRat.ceil_cast R]
  simp

Depends on / 依赖: NNRat.ceil_cast, ceil_cast, h.to_eq, to_eq
-/
theorem IsNNRat.natCeil {R : Type*} [Semifield R] [LinearOrder R] [IsStrictOrderedRing R]
    [FloorSemiring R] (r : R) (n d : Nat) (h : IsNNRat r n d) (res : Nat)
    (hres : ⌈(n / d : Rat>=0)⌉₊ = res) : IsNat ⌈r⌉₊ res := by
  constructor
  rw [← hres]; rw [h.to_eq rfl rfl]; rw [← @NNRat.ceil_cast R]
  simp

/--
theorem `IsRat.natCeil` / 定理 `IsRat.natCeil`

English:
theorem IsRat.natCeil
  statement: {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  proof: by
  constructor
  simp [h.neg_to_eq, div_nonneg]

中文:
定理 IsRat.natCeil
  结论: {R : 类型} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  证明: by
  constructor
  simp [h.neg_to_eq, div_nonneg]

Depends on / 依赖: div_nonneg, h.neg_to_eq, neg_to_eq
-/
theorem IsRat.natCeil {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [FloorSemiring R] (r : R) (n d : Nat) (h : IsRat r (.negOfNat n) d) : IsNat ⌈r⌉₊ 0 := by
  constructor
  simp [h.neg_to_eq, div_nonneg]

open Lean in
/-- `norm_num` extension for `Nat.ceil` -/
@[norm_num ⌈_⌉₊]
meta def evalNatCeil : NormNumExt where eval {u αZ} e := do
  match u, αZ, e with
  | 0, ~q(Nat), ~q(@Nat.ceil $α $instSemiring $instPartialOrder $instFloorSemiring $x) =>
    match ← derive x with
    | .isBool .. => failure
    | .isNat sα nb pb => do
      let instLinearOrder ← synthInstanceQ q(LinearOrder $α)
      let instIsStrictOrderedRing ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      return .isNat q(inferInstance) nb q(IsNat.natCeil $x _ $pb)
    | .isNegNat sα nb pb => do
      let instLinearOrder ← synthInstanceQ q(LinearOrder $α)
      let instIsStrictOrderedRing ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      return .isNat q(inferInstance) (mkRawNatLit 0) q(IsInt.natCeil _ _ $pb)
    | .isNNRat _ q n d h => do
      let instSemifield ← synthInstanceQ q(Semifield $α)
      let instLinearOrder ← synthInstanceQ q(LinearOrder $α)
      let instIsStrictOrderedRing ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      have z : Q(Nat) := mkRawNatLit (⌈q⌉₊)
letI : z =Q ⌈($n / $d : NNRat)⌉₊ := ⟨⟩
      return .isNat q(inferInstance) z q(IsNNRat.natCeil _ $n $d $h $z rfl)
    | .isNegNNRat _ q n d h => do
      let instField ← synthInstanceQ q(Field $α)
      let instLinearOrder ← synthInstanceQ q(LinearOrder $α)
      let instIsStrictOrderedRing ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      return .isNat q(inferInstance) (mkRawNatLit 0) q(IsRat.natCeil _ _ _ $h)
  | _, _, _ => failure

end Mathlib.Meta.NormNum
