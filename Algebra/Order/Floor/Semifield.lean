/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kevin Kappelmann
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Tactic.Linarith

/-!
# Lemmas on `Nat.floor` and `Nat.ceil` for semifields

This file contains basic results on the natural-valued floor and ceiling functions.

## Tags

rounding, floor, ceil
-/

public section

assert_not_exists Finset

open Set

variable {R K : Type*}

namespace Nat

-- TODO: should these lemmas be `simp`? `norm_cast`?
section LinearOrderedSemifield
variable [Semifield K] [LinearOrder K] [IsStrictOrderedRing K] [FloorSemiring K]

/--
theorem `floor_div_natCast` / 定理 `floor_div_natCast`

English:
theorem floor_div_natCast
  given: (a : K) (n : Nat)
  statement: ⌊a / n⌋₊ = ⌊a⌋₊ / n
  proof: by
  obtain rfl | hn := n.eq_zero_or_pos
  · simp
  nth_rw 2 [← div_mul_cancel₀ (a := a) (b := ↑n) (by positivity)]
  rw [mul_cast_floor_div_cancel (Nat.ne_zero_of_lt hn)]

中文:
定理 floor_div_natCast
  条件: (a : K) (n : 自然数)
  结论: ⌊a / n⌋₊ = ⌊a⌋₊ / n
  证明: by
  obtain rfl | hn := n.eq_zero_or_pos
  · simp
  nth_rw 2 [← div_mul_cancel₀ (a := a) (b := ↑n) (by positivity)]
  rw [mul_cast_floor_div_cancel (Nat.ne_zero_of_lt hn)]

Depends on / 依赖: Nat.ne_zero_of_lt, eq_zero_or_pos, mul_cast_floor_div_cancel, n.eq_zero_or_pos, ne_zero_of_lt, nth_rw
-/
theorem floor_div_natCast (a : K) (n : Nat) : ⌊a / n⌋₊ = ⌊a⌋₊ / n := by
  obtain rfl | hn := n.eq_zero_or_pos
  · simp
  nth_rw 2 [← div_mul_cancel₀ (a := a) (b := ↑n) (by positivity)]
  rw [mul_cast_floor_div_cancel (Nat.ne_zero_of_lt hn)]

/--
theorem `floor_div_ofNat` / 定理 `floor_div_ofNat`

English:
theorem floor_div_ofNat
  given: (a : K) (n : Nat) [n.AtLeastTwo]
  proof: floor_div_natCast a n

中文:
定理 floor_div_of自然数
  条件: (a : K) (n : 自然数) [n.AtLeastTwo]
  证明: floor_div_natCast a n

Depends on / 依赖: floor_div_natCast
-/
theorem floor_div_ofNat (a : K) (n : Nat) [n.AtLeastTwo] :
    ⌊a / ofNat(n)⌋₊ = ⌊a⌋₊ / ofNat(n) :=
  floor_div_natCast a n

/--
theorem `floor_div_eq_div` / 定理 `floor_div_eq_div`

English:
theorem floor_div_eq_div
  given: (m n : Nat)
  statement: ⌊(m : K) / n⌋₊ = m / n
  proof: by
  convert! floor_div_natCast (m : K) n
  rw [m.floor_natCast]

中文:
定理 floor_div_eq_div
  条件: (m n : 自然数)
  结论: ⌊(m : K) / n⌋₊ = m / n
  证明: by
  convert! floor_div_natCast (m : K) n
  rw [m.floor_natCast]

Depends on / 依赖: convert, floor_div_natCast, floor_natCast, m.floor_natCast
-/
theorem floor_div_eq_div (m n : Nat) : ⌊(m : K) / n⌋₊ = m / n := by
  convert! floor_div_natCast (m : K) n
  rw [m.floor_natCast]

end LinearOrderedSemifield

section LinearOrderedField
variable [Field K] [LinearOrder K] [IsOrderedRing K] [FloorSemiring K] {a b : K}

/--
lemma `mul_lt_floor` / 引理 `mul_lt_floor`

English:
lemma mul_lt_floor
  given: (hb₀ : 0 < b) (hb : b < 1) (hba : ⌈b / (1 - b)⌉₊ <= a)
  statement: b * a < ⌊a⌋₊
  proof: by
  calc
    b * a < b * (⌊a⌋₊ + 1) := by gcongr; apply lt_floor_add_one
    _ <= ⌊a⌋₊ := by
      rw [_root_.mul_add_one]; rw [← le_sub_iff_add_le']; rw [← one_sub_mul]; rw [← div_le_iff₀' (by linarith)]; rw [← ceil_le]
      exact le_floor hba

中文:
引理 mul_lt_floor
  条件: (hb₀ : 0 < b) (hb : b < 1) (hba : ⌈b / (1 - b)⌉₊ <= a)
  结论: b * a < ⌊a⌋₊
  证明: by
  calc
    b * a < b * (⌊a⌋₊ + 1) := by gcongr; apply lt_floor_add_one
    _ <= ⌊a⌋₊ := by
      rw [_root_.mul_add_one]; rw [← le_sub_iff_add_le']; rw [← one_sub_mul]; rw [← div_le_iff₀' (by linarith)]; rw [← ceil_le]
      exact le_floor hba

Depends on / 依赖: _root_, _root_.mul_add_one, ceil_le, le_floor, le_sub_iff_add_le, lt_floor_add_one, mul_add_one, one_sub_mul
-/
lemma mul_lt_floor (hb₀ : 0 < b) (hb : b < 1) (hba : ⌈b / (1 - b)⌉₊ <= a) : b * a < ⌊a⌋₊ := by
  calc
    b * a < b * (⌊a⌋₊ + 1) := by gcongr; apply lt_floor_add_one
    _ <= ⌊a⌋₊ := by
      rw [_root_.mul_add_one]; rw [← le_sub_iff_add_le']; rw [← one_sub_mul]; rw [← div_le_iff₀' (by linarith)]; rw [← ceil_le]
      exact le_floor hba

/--
lemma `ceil_lt_mul` / 引理 `ceil_lt_mul`

English:
lemma ceil_lt_mul
  given: (hb : 1 < b) (hba : ⌈(b - 1)⁻¹⌉₊ / b < a)
  statement: ⌈a⌉₊ < b * a
  proof: by
  obtain hab | hba := le_total a (b - 1)⁻¹
  · calc
      ⌈a⌉₊ <= (⌈(b - 1)⁻¹⌉₊ : K) := by gcongr
      _ < b * a := by rwa [← div_lt_iff₀']; positivity
  · rw [← sub_pos] at hb
    calc
⌈a⌉₊ < a + 1 := ceil_lt_add_one hba.trans' by positivity
      _ = a + (b - 1) * (b - 1)⁻¹ := by rw [mul_inv_c

中文:
引理 ceil_lt_mul
  条件: (hb : 1 < b) (hba : ⌈(b - 1)⁻¹⌉₊ / b < a)
  结论: ⌈a⌉₊ < b * a
  证明: by
  obtain hab | hba := le_total a (b - 1)⁻¹
  · calc
      ⌈a⌉₊ <= (⌈(b - 1)⁻¹⌉₊ : K) := by gcongr
      _ < b * a := by rwa [← div_lt_iff₀']; positivity
  · rw [← sub_pos] at hb
    calc
⌈a⌉₊ < a + 1 := ceil_lt_add_one hba.trans' by positivity
      _ = a + (b - 1) * (b - 1)⁻¹ := by rw [mul_inv_c

Depends on / 依赖: add_sub_cancel, ceil_lt_add_one, hba.trans, le_total, sub_one_mul, sub_pos
-/
lemma ceil_lt_mul (hb : 1 < b) (hba : ⌈(b - 1)⁻¹⌉₊ / b < a) : ⌈a⌉₊ < b * a := by
  obtain hab | hba := le_total a (b - 1)⁻¹
  · calc
      ⌈a⌉₊ <= (⌈(b - 1)⁻¹⌉₊ : K) := by gcongr
      _ < b * a := by rwa [← div_lt_iff₀']; positivity
  · rw [← sub_pos] at hb
    calc
⌈a⌉₊ < a + 1 := ceil_lt_add_one hba.trans' by positivity
      _ = a + (b - 1) * (b - 1)⁻¹ := by rw [mul_inv_cancel₀]; positivity
      _ <= a + (b - 1) * a := by gcongr
      _ = b * a := by rw [sub_one_mul, add_sub_cancel]

/--
lemma `ceil_le_mul` / 引理 `ceil_le_mul`

English:
lemma ceil_le_mul
  given: (hb : 1 < b) (hba : ⌈(b - 1)⁻¹⌉₊ / b <= a)
  statement: ⌈a⌉₊ <= b * a
  proof: by
  obtain rfl | hba := hba.eq_or_lt
  · rw [mul_div_cancel₀, cast_le, ceil_le]
    · exact _root_.div_le_self (by positivity) hb.le
    · positivity
  · exact (ceil_lt_mul hb hba).le

中文:
引理 ceil_le_mul
  条件: (hb : 1 < b) (hba : ⌈(b - 1)⁻¹⌉₊ / b <= a)
  结论: ⌈a⌉₊ <= b * a
  证明: by
  obtain rfl | hba := hba.eq_or_lt
  · rw [mul_div_cancel₀, cast_le, ceil_le]
    · exact _root_.div_le_self (by positivity) hb.le
    · positivity
  · exact (ceil_lt_mul hb hba).le

Depends on / 依赖: _root_, _root_.div_le_self, cast_le, ceil_le, ceil_lt_mul, div_le_self, eq_or_lt, hb.le, hba.eq_or_lt
-/
lemma ceil_le_mul (hb : 1 < b) (hba : ⌈(b - 1)⁻¹⌉₊ / b <= a) : ⌈a⌉₊ <= b * a := by
  obtain rfl | hba := hba.eq_or_lt
  · rw [mul_div_cancel₀, cast_le, ceil_le]
    · exact _root_.div_le_self (by positivity) hb.le
    · positivity
  · exact (ceil_lt_mul hb hba).le

/--
lemma `div_two_lt_floor` / 引理 `div_two_lt_floor`

English:
lemma div_two_lt_floor
  given: (ha : 1 <= a)
  statement: a / 2 < ⌊a⌋₊
  proof: by
  rw [div_eq_inv_mul]; refine mul_lt_floor ?_ ?_ ?_ <;> norm_num; assumption

中文:
引理 div_two_lt_floor
  条件: (ha : 1 <= a)
  结论: a / 2 < ⌊a⌋₊
  证明: by
  rw [div_eq_inv_mul]; refine mul_lt_floor ?_ ?_ ?_ <;> norm_num; assumption

Depends on / 依赖: div_eq_inv_mul, mul_lt_floor
-/
lemma div_two_lt_floor (ha : 1 <= a) : a / 2 < ⌊a⌋₊ := by
  rw [div_eq_inv_mul]; refine mul_lt_floor ?_ ?_ ?_ <;> norm_num; assumption

/--
lemma `ceil_lt_two_mul` / 引理 `ceil_lt_two_mul`

English:
lemma ceil_lt_two_mul
  given: (ha : 2⁻¹ < a)
  statement: ⌈a⌉₊ < 2 * a
  proof: ceil_lt_mul one_lt_two (by norm_num at ha ⊢; exact ha)

中文:
引理 ceil_lt_two_mul
  条件: (ha : 2⁻¹ < a)
  结论: ⌈a⌉₊ < 2 * a
  证明: ceil_lt_mul one_lt_two (by norm_num at ha ⊢; exact ha)

Depends on / 依赖: ceil_lt_mul, one_lt_two
-/
lemma ceil_lt_two_mul (ha : 2⁻¹ < a) : ⌈a⌉₊ < 2 * a :=
  ceil_lt_mul one_lt_two (by norm_num at ha ⊢; exact ha)

/--
lemma `ceil_le_two_mul` / 引理 `ceil_le_two_mul`

English:
lemma ceil_le_two_mul
  given: (ha : 2⁻¹ <= a)
  statement: ⌈a⌉₊ <= 2 * a
  proof: ceil_le_mul one_lt_two (by norm_num at ha ⊢; exact ha)

中文:
引理 ceil_le_two_mul
  条件: (ha : 2⁻¹ <= a)
  结论: ⌈a⌉₊ <= 2 * a
  证明: ceil_le_mul one_lt_two (by norm_num at ha ⊢; exact ha)

Depends on / 依赖: ceil_le_mul, one_lt_two
-/
lemma ceil_le_two_mul (ha : 2⁻¹ <= a) : ⌈a⌉₊ <= 2 * a :=
  ceil_le_mul one_lt_two (by norm_num at ha ⊢; exact ha)

end LinearOrderedField

end Nat

namespace Mathlib.Meta.NormNum

open Qq


/--
theorem `IsNat.natFloor` / 定理 `IsNat.natFloor`

English:
theorem IsNat.natFloor
  statement: {R : Type*} [Semiring R] [LinearOrder R] [IsStrictOrderedRing R]
  proof: by
  rintro ⟨⟨⟩⟩
  exact ⟨by simp⟩

中文:
定理 是自然数.natFloor
  结论: {R : 类型} [半环 R] [线性序 R] [是StrictOrdered环 R]
  证明: by
  rintro ⟨⟨⟩⟩
  exact ⟨by simp⟩
-/
theorem IsNat.natFloor {R : Type*} [Semiring R] [LinearOrder R] [IsStrictOrderedRing R]
    [FloorSemiring R] (r : R) (m : Nat) : IsNat r m -> IsNat (⌊r⌋₊) m := by
  rintro ⟨⟨⟩⟩
  exact ⟨by simp⟩

/--
theorem `IsInt.natFloor` / 定理 `IsInt.natFloor`

English:
theorem IsInt.natFloor
  statement: {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
  proof: by
  rintro ⟨⟨⟩⟩
exact ⟨Nat.floor_of_nonpos by simp⟩

中文:
定理 是整数.natFloor
  结论: {R : 类型} [环 R] [线性序 R] [是StrictOrdered环 R]
  证明: by
  rintro ⟨⟨⟩⟩
exact ⟨Nat.floor_of_nonpos by simp⟩

Depends on / 依赖: Nat.floor_of_nonpos, floor_of_nonpos
-/
theorem IsInt.natFloor {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
    [FloorSemiring R] (r : R) (m : Nat) : IsInt r (.negOfNat m) -> IsNat (⌊r⌋₊) 0 := by
  rintro ⟨⟨⟩⟩
exact ⟨Nat.floor_of_nonpos by simp⟩

/--
theorem `IsNNRat.natFloor` / 定理 `IsNNRat.natFloor`

English:
theorem IsNNRat.natFloor
  statement: {R : Type*} [Semifield R] [LinearOrder R] [IsStrictOrderedRing R]
  proof: by
  constructor
  rw [← hres]; rw [h.to_eq rfl rfl]; rw [Nat.floor_div_eq_div]; rw [Nat.cast_id]

中文:
定理 是NNRat.natFloor
  结论: {R : 类型} [半域 R] [线性序 R] [是StrictOrdered环 R]
  证明: by
  constructor
  rw [← hres]; rw [h.to_eq rfl rfl]; rw [Nat.floor_div_eq_div]; rw [Nat.cast_id]

Depends on / 依赖: Nat.cast_id, Nat.floor_div_eq_div, cast_id, floor_div_eq_div, h.to_eq, to_eq
-/
theorem IsNNRat.natFloor {R : Type*} [Semifield R] [LinearOrder R] [IsStrictOrderedRing R]
    [FloorSemiring R] (r : R) (n d : Nat) (h : IsNNRat r n d) (res : Nat) (hres : n / d = res) :
    IsNat ⌊r⌋₊ res := by
  constructor
  rw [← hres]; rw [h.to_eq rfl rfl]; rw [Nat.floor_div_eq_div]; rw [Nat.cast_id]

/--
theorem `IsRat.natFloor` / 定理 `IsRat.natFloor`

English:
theorem IsRat.natFloor
  statement: {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  proof: by
  rcases h with ⟨hd, rfl⟩
  constructor
  rw [Nat.cast_zero]; rw [Nat.floor_eq_zero]
  exact lt_of_le_of_lt (by simp [mul_nonneg]) one_pos

中文:
定理 是有理数.natFloor
  结论: {R : 类型} [域 R] [线性序 R] [是StrictOrdered环 R]
  证明: by
  rcases h with ⟨hd, rfl⟩
  constructor
  rw [Nat.cast_zero]; rw [Nat.floor_eq_zero]
  exact lt_of_le_of_lt (by simp [mul_nonneg]) one_pos

Depends on / 依赖: Nat.cast_zero, Nat.floor_eq_zero, cast_zero, floor_eq_zero, lt_of_le_of_lt, mul_nonneg, one_pos
-/
theorem IsRat.natFloor {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [FloorSemiring R] (r : R) (n d : Nat) (h : IsRat r (Int.negOfNat n) d) : IsNat ⌊r⌋₊ 0 := by
  rcases h with ⟨hd, rfl⟩
  constructor
  rw [Nat.cast_zero]; rw [Nat.floor_eq_zero]
  exact lt_of_le_of_lt (by simp [mul_nonneg]) one_pos

open Lean in
/-- `norm_num` extension for `Nat.floor` -/
@[norm_num ⌊_⌋₊]
meta def evalNatFloor : NormNumExt where eval {u αZ} e := do
  match u, αZ, e with
  | 0, ~q(Nat), ~q(@Nat.floor $α $instSemiring $instPartialOrder $instFloorSemiring $x) =>
    match ← derive x with
    | .isBool .. => failure
    | .isNat sα nb pb => do
      let instLinearOrder ← synthInstanceQ q(LinearOrder $α)
      let instIsStrictOrderedRing ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      return .isNat q(inferInstance) nb q(IsNat.natFloor $x _ $pb)
    | .isNegNat sα nb pb => do
      let instLinearOrder ← synthInstanceQ q(LinearOrder $α)
      let instIsStrictOrderedRing ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      return .isNat q(inferInstance) (mkRawNatLit 0) q(IsInt.natFloor _ _ $pb)
    | .isNNRat dα q n d h => do
      let instSemifield ← synthInstanceQ q(Semifield $α)
      let instLinearOrder ← synthInstanceQ q(LinearOrder $α)
      let instIsStrictOrderedRing ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      have z : Q(Nat) := mkRawNatLit (q.num.toNat / q.den)
haveI : z =Q n / d := ⟨⟩
      return .isNat q(inferInstance) z q(IsNNRat.natFloor _ $n $d $h $z rfl)
    | .isNegNNRat _ q n d h => do
      let instField ← synthInstanceQ q(Field $α)
      let instLinearOrder ← synthInstanceQ q(LinearOrder $α)
      let instIsStrictOrderedRing ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      return .isNat q(inferInstance) (mkRawNatLit 0) q(IsRat.natFloor $x $n $d $h)
  | _, _, _ => failure

end Mathlib.Meta.NormNum
