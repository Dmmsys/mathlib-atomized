/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Int
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.Ring.Int.Defs

/-!
# The rational numbers possess a linear order

This file constructs the order on `ℚ` and proves various facts relating the order to
ring structure on `ℚ`. This only uses unbundled type classes, e.g. `CovariantClass`,
relating the order structure and algebra structure on `ℚ`.
For the bundled `LinearOrderedCommRing` instance on `ℚ`, see `Algebra.Order.Ring.Rat`.

## Tags

rat, rationals, field, ℚ, numerator, denominator, num, denom, order, ordering
-/

@[expose] public section

assert_not_exists IsOrderedMonoid Field Finset Set.Icc GaloisConnection

namespace Rat

variable {a b c p q : Rat}

/--
lemma `mkRat_nonneg` / 引理 `mkRat_nonneg`

English:
lemma mkRat_nonneg
  given: {a : Int} (ha : 0 <= a) (b : Nat)
  statement: 0 <= mkRat a b
  proof: by
  simpa using divInt_nonneg ha (Int.natCast_nonneg _)

中文:
引理 mkRat_nonneg
  条件: {a : 整数} (ha : 0 <= a) (b : 自然数)
  结论: 0 <= mkRat a b
  证明: by
  simpa using divInt_nonneg ha (Int.natCast_nonneg _)
-/
@[simp] lemma mkRat_nonneg {a : Int} (ha : 0 <= a) (b : Nat) : 0 <= mkRat a b := by
  simpa using divInt_nonneg ha (Int.natCast_nonneg _)

/--
theorem `ofScientific_nonneg` / 定理 `ofScientific_nonneg`

English:
theorem ofScientific_nonneg
  given: (m : Nat) (s : Bool) (e : Nat)
  statement: 0 <= Rat.ofScientific m s e
  proof: by
  rw [Rat.ofScientific]
  cases s
  · rw [if_neg (by decide)]
exact num_nonneg.mp Int.natCast_nonneg _
  · grind [normalize_eq_mkRat, Rat.mkRat_nonneg]

中文:
定理 ofScientific_nonneg
  条件: (m : 自然数) (s : 布尔) (e : 自然数)
  结论: 0 <= Rat.ofScientific m s e
  证明: by
  rw [Rat.ofScientific]
  cases s
  · rw [if_neg (by decide)]
exact num_nonneg.mp Int.natCast_nonneg _
  · grind [normalize_eq_mkRat, Rat.mkRat_nonneg]

Depends on / 依赖: Int.natCast_nonneg, Rat.mkRat_nonneg, Rat.ofScientific, if_neg, mkRat_nonneg, natCast_nonneg, normalize_eq_mkRat, num_nonneg, num_nonneg.mp, ofScientific
-/
theorem ofScientific_nonneg (m : Nat) (s : Bool) (e : Nat) : 0 <= Rat.ofScientific m s e := by
  rw [Rat.ofScientific]
  cases s
  · rw [if_neg (by decide)]
exact num_nonneg.mp Int.natCast_nonneg _
  · grind [normalize_eq_mkRat, Rat.mkRat_nonneg]

/--
Instance `_root_.NNRatCast.toOfScientific` / 实例 `_root_.NNRatCast.toOfScientific`

English:
instance _root_.NNRatCast.toOfScientific
  signature: {K} [NNRatCast K]
  body: NNRat.cast ⟨Rat.ofScientific m b d, ofScientific_nonneg m b d⟩

中文:
实例 _root_.NNRatCast.toOfScientific
  签名: {K} [NNRatCast K]
  定义体: NNRat.cast ⟨Rat.ofScientific m b d, ofScientific_nonneg m b d⟩

Depends on / 依赖: NNRat.cast, Rat.ofScientific, ofScientific, ofScientific_nonneg
-/
instance _root_.NNRatCast.toOfScientific {K} [NNRatCast K] : OfScientific K where
  ofScientific (m : Nat) (b : Bool) (d : Nat) :=
    NNRat.cast ⟨Rat.ofScientific m b d, ofScientific_nonneg m b d⟩

/--
theorem `_root_.NNRatCast.toOfScientific_def` / 定理 `_root_.NNRatCast.toOfScientific_def`

English:
theorem _root_.NNRatCast.toOfScientific_def
  given: {K} [NNRatCast K] (m : Nat) (b : Bool) (d : Nat)
  proof: rfl

中文:
定理 _root_.NNRatCast.toOfScientific_def
  条件: {K} [NNRatCast K] (m : 自然数) (b : 布尔) (d : 自然数)
  证明: rfl
-/
theorem _root_.NNRatCast.toOfScientific_def {K} [NNRatCast K] (m : Nat) (b : Bool) (d : Nat) :
    (OfScientific.ofScientific m b d : K) =
      NNRat.cast ⟨(OfScientific.ofScientific m b d : Rat), ofScientific_nonneg m b d⟩ :=
  rfl

/-- Casting a scientific literal via `ℚ≥0` is the same as casting directly. -/
@[simp, norm_cast]
/--
theorem `_root_.NNRat.cast_ofScientific` / 定理 `_root_.NNRat.cast_ofScientific`

English:
theorem _root_.NNRat.cast_ofScientific
  given: {K} [NNRatCast K] (m : Nat) (s : Bool) (e : Nat)
  proof: rfl

中文:
定理 _root_.NNRat.cast_ofScientific
  条件: {K} [NNRatCast K] (m : 自然数) (s : 布尔) (e : 自然数)
  证明: rfl
-/
theorem _root_.NNRat.cast_ofScientific {K} [NNRatCast K] (m : Nat) (s : Bool) (e : Nat) :
    (OfScientific.ofScientific m s e : Rat>=0) = (OfScientific.ofScientific m s e : K) :=
  rfl

/--
lemma `divInt_le_divInt` / 引理 `divInt_le_divInt`

English:
lemma divInt_le_divInt
  given: {a b c d : Int} (b0 : 0 < b) (d0 : 0 < d)
  proof: by
  rw [Rat.le_iff_sub_nonneg]; rw [← Int.sub_nonneg]
  simp [sub_eq_add_neg, ne_of_gt b0, ne_of_gt d0, Int.mul_pos d0 b0]

中文:
引理 divInt_le_divInt
  条件: {a b c d : 整数} (b0 : 0 < b) (d0 : 0 < d)
  证明: by
  rw [Rat.le_iff_sub_nonneg]; rw [← Int.sub_nonneg]
  simp [sub_eq_add_neg, ne_of_gt b0, ne_of_gt d0, Int.mul_pos d0 b0]
-/
protected lemma divInt_le_divInt {a b c d : Int} (b0 : 0 < b) (d0 : 0 < d) :
    a /. b <= c /. d ↔ a * d <= c * b := by
  rw [Rat.le_iff_sub_nonneg]; rw [← Int.sub_nonneg]
  simp [sub_eq_add_neg, ne_of_gt b0, ne_of_gt d0, Int.mul_pos d0 b0]

/--
lemma `lt_iff_le_not_ge` / 引理 `lt_iff_le_not_ge`

English:
lemma lt_iff_le_not_ge
  given: (a b : Rat)
  statement: a < b ↔ a <= b ∧ ¬b <= a
  proof: Std.LawfulOrderLT.lt_iff a b

中文:
引理 lt_iff_le_not_ge
  条件: (a b : Rat)
  结论: a < b ↔ a <= b ∧ ¬b <= a
  证明: Std.LawfulOrderLT.lt_iff a b
-/
protected lemma lt_iff_le_not_ge (a b : Rat) : a < b ↔ a <= b ∧ ¬b <= a :=
  Std.LawfulOrderLT.lt_iff a b

/--
Instance `linearOrder` / 实例 `linearOrder`

English:
instance linearOrder
  signature: : LinearOrder Rat where
  body: Rat.le_refl
  le_trans _ _ _ := Rat.le_trans
  le_antisymm _ _ := Rat.le_antisymm
  le_total _ _ := Rat.le_total
  toDecidableEq := inferInstance
  toDecidableLE := inferInstance
  toDecidableLT := inferInstance
  lt_iff_le_not_ge := Rat.lt_iff_le_not_ge

中文:
实例 linearOrder
  签名: : LinearOrder Rat where
  定义体: Rat.le_refl
  le_trans _ _ _ := Rat.le_trans
  le_antisymm _ _ := Rat.le_antisymm
  le_total _ _ := Rat.le_total
  toDecidableEq := inferInstance
  toDecidableLE := inferInstance
  toDecidableLT := inferInstance
  lt_iff_le_not_ge := Rat.lt_iff_le_not_ge

Depends on / 依赖: Rat.le_refl, le_refl
-/
instance linearOrder : LinearOrder Rat where
  le_refl _ := Rat.le_refl
  le_trans _ _ _ := Rat.le_trans
  le_antisymm _ _ := Rat.le_antisymm
  le_total _ _ := Rat.le_total
  toDecidableEq := inferInstance
  toDecidableLE := inferInstance
  toDecidableLT := inferInstance
  lt_iff_le_not_ge := Rat.lt_iff_le_not_ge

/--
theorem `mkRat_nonneg_iff` / 定理 `mkRat_nonneg_iff`

English:
theorem mkRat_nonneg_iff
  given: (a : Int) {b : Nat} (hb : b != 0)
  statement: 0 <= mkRat a b ↔ 0 <= a
  proof: divInt_nonneg_iff_of_pos_right (show 0 < (b : Int) by simpa using Nat.pos_of_ne_zero hb)

中文:
定理 mkRat_nonneg_iff
  条件: (a : 整数) {b : 自然数} (hb : b != 0)
  结论: 0 <= mkRat a b ↔ 0 <= a
  证明: divInt_nonneg_iff_of_pos_right (show 0 < (b : Int) by simpa using Nat.pos_of_ne_zero hb)

Depends on / 依赖: Nat.pos_of_ne_zero, divInt_nonneg_iff_of_pos_right, pos_of_ne_zero
-/
theorem mkRat_nonneg_iff (a : Int) {b : Nat} (hb : b != 0) : 0 <= mkRat a b ↔ 0 <= a :=
  divInt_nonneg_iff_of_pos_right (show 0 < (b : Int) by simpa using Nat.pos_of_ne_zero hb)

/--
theorem `mkRat_pos_iff` / 定理 `mkRat_pos_iff`

English:
theorem mkRat_pos_iff
  given: (a : Int) {b : Nat} (hb : b != 0)
  statement: 0 < mkRat a b ↔ 0 < a
  proof: by
  grind [mkRat_nonneg_iff, Rat.mkRat_eq_zero]

中文:
定理 mkRat_pos_iff
  条件: (a : 整数) {b : 自然数} (hb : b != 0)
  结论: 0 < mkRat a b ↔ 0 < a
  证明: by
  grind [mkRat_nonneg_iff, Rat.mkRat_eq_zero]

Depends on / 依赖: Rat.mkRat_eq_zero, mkRat_eq_zero, mkRat_nonneg_iff
-/
theorem mkRat_pos_iff (a : Int) {b : Nat} (hb : b != 0) : 0 < mkRat a b ↔ 0 < a := by
  grind [mkRat_nonneg_iff, Rat.mkRat_eq_zero]

/--
theorem `mkRat_pos` / 定理 `mkRat_pos`

English:
theorem mkRat_pos
  given: {a : Int} (ha : 0 < a) {b : Nat} (hb : b != 0)
  statement: 0 < mkRat a b
  proof: (mkRat_pos_iff a hb).mpr ha

中文:
定理 mkRat_pos
  条件: {a : 整数} (ha : 0 < a) {b : 自然数} (hb : b != 0)
  结论: 0 < mkRat a b
  证明: (mkRat_pos_iff a hb).mpr ha

Depends on / 依赖: mkRat_pos_iff
-/
theorem mkRat_pos {a : Int} (ha : 0 < a) {b : Nat} (hb : b != 0) : 0 < mkRat a b :=
  (mkRat_pos_iff a hb).mpr ha

/--
theorem `mkRat_nonpos_iff` / 定理 `mkRat_nonpos_iff`

English:
theorem mkRat_nonpos_iff
  given: (a : Int) {b : Nat} (hb : b != 0)
  statement: mkRat a b <= 0 ↔ a <= 0
  proof: by
  grind [mkRat_pos_iff]

中文:
定理 mkRat_nonpos_iff
  条件: (a : 整数) {b : 自然数} (hb : b != 0)
  结论: mkRat a b <= 0 ↔ a <= 0
  证明: by
  grind [mkRat_pos_iff]

Depends on / 依赖: mkRat_pos_iff
-/
theorem mkRat_nonpos_iff (a : Int) {b : Nat} (hb : b != 0) : mkRat a b <= 0 ↔ a <= 0 := by
  grind [mkRat_pos_iff]

/--
theorem `mkRat_nonpos` / 定理 `mkRat_nonpos`

English:
theorem mkRat_nonpos
  given: {a : Int} (ha : a <= 0) (b : Nat)
  statement: mkRat a b <= 0
  proof: by
  obtain rfl | hb := eq_or_ne b 0
  · simp
  · exact (mkRat_nonpos_iff a hb).mpr ha

中文:
定理 mkRat_nonpos
  条件: {a : 整数} (ha : a <= 0) (b : 自然数)
  结论: mkRat a b <= 0
  证明: by
  obtain rfl | hb := eq_or_ne b 0
  · simp
  · exact (mkRat_nonpos_iff a hb).mpr ha

Depends on / 依赖: eq_or_ne, mkRat_nonpos_iff
-/
theorem mkRat_nonpos {a : Int} (ha : a <= 0) (b : Nat) : mkRat a b <= 0 := by
  obtain rfl | hb := eq_or_ne b 0
  · simp
  · exact (mkRat_nonpos_iff a hb).mpr ha

/--
theorem `mkRat_neg_iff` / 定理 `mkRat_neg_iff`

English:
theorem mkRat_neg_iff
  given: (a : Int) {b : Nat} (hb : b != 0)
  statement: mkRat a b < 0 ↔ a < 0
  proof: by
  grind [mkRat_nonneg_iff]

中文:
定理 mkRat_neg_iff
  条件: (a : 整数) {b : 自然数} (hb : b != 0)
  结论: mkRat a b < 0 ↔ a < 0
  证明: by
  grind [mkRat_nonneg_iff]

Depends on / 依赖: mkRat_nonneg_iff
-/
theorem mkRat_neg_iff (a : Int) {b : Nat} (hb : b != 0) : mkRat a b < 0 ↔ a < 0 := by
  grind [mkRat_nonneg_iff]

/--
theorem `mkRat_neg` / 定理 `mkRat_neg`

English:
theorem mkRat_neg
  given: {a : Int} (ha : a < 0) {b : Nat} (hb : b != 0)
  statement: mkRat a b < 0
  proof: (mkRat_neg_iff a hb).mpr ha

中文:
定理 mkRat_neg
  条件: {a : 整数} (ha : a < 0) {b : 自然数} (hb : b != 0)
  结论: mkRat a b < 0
  证明: (mkRat_neg_iff a hb).mpr ha

Depends on / 依赖: mkRat_neg_iff
-/
theorem mkRat_neg {a : Int} (ha : a < 0) {b : Nat} (hb : b != 0) : mkRat a b < 0 :=
  (mkRat_neg_iff a hb).mpr ha


/--
Instance `instDistribLattice` / 实例 `instDistribLattice`

English:
instance instDistribLattice
  signature: : DistribLattice Rat
  body: inferInstance

中文:
实例 instDistribLattice
  签名: : DistribLattice Rat
  定义体: inferInstance
-/
instance instDistribLattice : DistribLattice Rat := inferInstance
/--
Instance `instLattice` / 实例 `instLattice`

English:
instance instLattice
  signature: : Lattice Rat
  body: inferInstance

中文:
实例 instLattice
  签名: : Lattice Rat
  定义体: inferInstance
-/
instance instLattice : Lattice Rat := inferInstance
/--
Instance `instSemilatticeInf` / 实例 `instSemilatticeInf`

English:
instance instSemilatticeInf
  signature: : SemilatticeInf Rat
  body: inferInstance

中文:
实例 instSemilatticeInf
  签名: : SemilatticeInf Rat
  定义体: inferInstance
-/
instance instSemilatticeInf : SemilatticeInf Rat := inferInstance
/--
Instance `instSemilatticeSup` / 实例 `instSemilatticeSup`

English:
instance instSemilatticeSup
  signature: : SemilatticeSup Rat
  body: inferInstance

中文:
实例 instSemilatticeSup
  签名: : SemilatticeSup Rat
  定义体: inferInstance
-/
instance instSemilatticeSup : SemilatticeSup Rat := inferInstance
/--
Instance `instInf` / 实例 `instInf`

English:
instance instInf
  signature: : Min Rat
  body: inferInstance

中文:
实例 instInf
  签名: : Min Rat
  定义体: inferInstance
-/
instance instInf : Min Rat := inferInstance
/--
Instance `instSup` / 实例 `instSup`

English:
instance instSup
  signature: : Max Rat
  body: inferInstance

中文:
实例 instSup
  签名: : Max Rat
  定义体: inferInstance
-/
instance instSup : Max Rat := inferInstance
/--
Instance `instPartialOrder` / 实例 `instPartialOrder`

English:
instance instPartialOrder
  signature: : PartialOrder Rat
  body: inferInstance

中文:
实例 instPartialOrder
  签名: : PartialOrder Rat
  定义体: inferInstance
-/
instance instPartialOrder : PartialOrder Rat := inferInstance
/--
Instance `instPreorder` / 实例 `instPreorder`

English:
instance instPreorder
  signature: : Preorder Rat
  body: inferInstance

中文:
实例 instPreorder
  签名: : Preorder Rat
  定义体: inferInstance
-/
instance instPreorder : Preorder Rat := inferInstance


/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddLeftMono Rat
  body: fun _ _ _ h => Rat.add_le_add_left.2 h

中文:
实例 :
  签名: AddLeftMono Rat
  定义体: fun _ _ _ h => Rat.add_le_add_left.2 h

Depends on / 依赖: Rat.add_le_add_left, add_le_add_left
-/
instance : AddLeftMono Rat where
  elim := fun _ _ _ h => Rat.add_le_add_left.2 h

/--
lemma `num_nonpos` / 引理 `num_nonpos`

English:
lemma num_nonpos
  given: {a : Rat}
  statement: a.num <= 0 ↔ a <= 0
  proof: by
  simp +instances [Int.le_iff_lt_or_eq, instLE, Rat.blt]

中文:
引理 num_nonpos
  条件: {a : Rat}
  结论: a.num <= 0 ↔ a <= 0
  证明: by
  simp +instances [Int.le_iff_lt_or_eq, instLE, Rat.blt]
-/
@[simp] lemma num_nonpos {a : Rat} : a.num <= 0 ↔ a <= 0 := by
  simp +instances [Int.le_iff_lt_or_eq, instLE, Rat.blt]
/--
lemma `num_pos` / 引理 `num_pos`

English:
lemma num_pos
  given: {a : Rat}
  statement: 0 < a.num ↔ 0 < a
  proof: lt_iff_lt_of_le_iff_le num_nonpos

中文:
引理 num_pos
  条件: {a : Rat}
  结论: 0 < a.num ↔ 0 < a
  证明: lt_iff_lt_of_le_iff_le num_nonpos
-/
@[simp] lemma num_pos {a : Rat} : 0 < a.num ↔ 0 < a := lt_iff_lt_of_le_iff_le num_nonpos
/--
lemma `num_neg` / 引理 `num_neg`

English:
lemma num_neg
  given: {a : Rat}
  statement: a.num < 0 ↔ a < 0
  proof: lt_iff_lt_of_le_iff_le num_nonneg

中文:
引理 num_neg
  条件: {a : Rat}
  结论: a.num < 0 ↔ a < 0
  证明: lt_iff_lt_of_le_iff_le num_nonneg
-/
@[simp] lemma num_neg {a : Rat} : a.num < 0 ↔ a < 0 := lt_iff_lt_of_le_iff_le num_nonneg

/--
theorem `div_lt_div_iff_mul_lt_mul` / 定理 `div_lt_div_iff_mul_lt_mul`

English:
theorem div_lt_div_iff_mul_lt_mul
  proof: by
  simp only [lt_iff_le_not_ge]
  apply and_congr
  · simp [div_def', Rat.divInt_le_divInt b_pos d_pos]
  · simp [div_def', Rat.divInt_le_divInt d_pos b_pos]

中文:
定理 div_lt_div_iff_mul_lt_mul
  证明: by
  simp only [lt_iff_le_not_ge]
  apply and_congr
  · simp [div_def', Rat.divInt_le_divInt b_pos d_pos]
  · simp [div_def', Rat.divInt_le_divInt d_pos b_pos]
-/
@[deprecated "use `div_lt_div_iff₀`" (since := "2026-03-20")] theorem div_lt_div_iff_mul_lt_mul
    {a b c d : Int} (b_pos : 0 < b) (d_pos : 0 < d) :
    (a : Rat) / b < c / d ↔ a * d < c * b := by
  simp only [lt_iff_le_not_ge]
  apply and_congr
  · simp [div_def', Rat.divInt_le_divInt b_pos d_pos]
  · simp [div_def', Rat.divInt_le_divInt d_pos b_pos]

/--
theorem `num_le_denom_iff` / 定理 `num_le_denom_iff`

English:
theorem num_le_denom_iff
  given: {q : Rat}
  statement: q.num <= q.den ↔ q <= 1
  proof: by simp [Rat.le_iff]

中文:
定理 num_le_denom_iff
  条件: {q : Rat}
  结论: q.num <= q.den ↔ q <= 1
  证明: by simp [Rat.le_iff]

Depends on / 依赖: Rat.le_iff, le_iff
-/
theorem num_le_denom_iff {q : Rat} : q.num <= q.den ↔ q <= 1 := by simp [Rat.le_iff]

/--
theorem `num_lt_denom_iff` / 定理 `num_lt_denom_iff`

English:
theorem num_lt_denom_iff
  given: {q : Rat}
  statement: q.num < q.den ↔ q < 1
  proof: by simp [Rat.lt_iff]

@[deprecated (since := "2026-02-24")] alias lt_one_iff_num_lt_denom := Rat.num_lt_denom_iff

中文:
定理 num_lt_denom_iff
  条件: {q : Rat}
  结论: q.num < q.den ↔ q < 1
  证明: by simp [Rat.lt_iff]

@[deprecated (since := "2026-02-24")] alias lt_one_iff_num_lt_denom := Rat.num_lt_denom_iff

Depends on / 依赖: Rat.lt_iff, lt_iff
-/
theorem num_lt_denom_iff {q : Rat} : q.num < q.den ↔ q < 1 := by simp [Rat.lt_iff]

@[deprecated (since := "2026-02-24")] alias lt_one_iff_num_lt_denom := Rat.num_lt_denom_iff

/--
theorem `abs_def` / 定理 `abs_def`

English:
theorem abs_def
  given: (q : Rat)
  statement: |q| = q.num.natAbs /. q.den
  proof: by
  grind [abs_of_nonpos, neg_def, Rat.num_nonneg, abs_of_nonneg, num_divInt_den]

中文:
定理 abs_def
  条件: (q : Rat)
  结论: |q| = q.num.natAbs /. q.den
  证明: by
  grind [abs_of_nonpos, neg_def, Rat.num_nonneg, abs_of_nonneg, num_divInt_den]

Depends on / 依赖: Rat.num_nonneg, abs_of_nonneg, abs_of_nonpos, neg_def, num_divInt_den, num_nonneg
-/
theorem abs_def (q : Rat) : |q| = q.num.natAbs /. q.den := by
  grind [abs_of_nonpos, neg_def, Rat.num_nonneg, abs_of_nonneg, num_divInt_den]

/--
theorem `abs_def'` / 定理 `abs_def'`

English:
theorem abs_def'
  given: (q : Rat)
  proof: by
  refine ext ?_ ?_ <;>
    simp [Int.abs_eq_natAbs, abs_def,
      ← Rat.mk_eq_divInt (num := q.num.natAbs) (nz := q.den_ne_zero) (c := q.reduced)]

@[simp]

中文:
定理 abs_def'
  条件: (q : Rat)
  证明: by
  refine ext ?_ ?_ <;>
    simp [Int.abs_eq_natAbs, abs_def,
      ← Rat.mk_eq_divInt (num := q.num.natAbs) (nz := q.den_ne_zero) (c := q.reduced)]

@[simp]

Depends on / 依赖: Int.abs_eq_natAbs, Rat.mk_eq_divInt, abs_def, abs_eq_natAbs, den_ne_zero, mk_eq_divInt, natAbs, q.den_ne_zero, q.num.natAbs, q.reduced, reduced
-/
theorem abs_def' (q : Rat) :
    |q| = ⟨|q.num|, q.den, q.den_ne_zero, q.num.abs_eq_natAbs ▸ q.reduced⟩ := by
  refine ext ?_ ?_ <;>
    simp [Int.abs_eq_natAbs, abs_def,
      ← Rat.mk_eq_divInt (num := q.num.natAbs) (nz := q.den_ne_zero) (c := q.reduced)]

@[simp]
/--
theorem `num_abs_eq_abs_num` / 定理 `num_abs_eq_abs_num`

English:
theorem num_abs_eq_abs_num
  given: (q : Rat)
  statement: |q|.num = |q.num|
  proof: by
  rw [abs_def']

@[simp]

中文:
定理 num_abs_eq_abs_num
  条件: (q : Rat)
  结论: |q|.num = |q.num|
  证明: by
  rw [abs_def']

@[simp]

Depends on / 依赖: abs_def
-/
theorem num_abs_eq_abs_num (q : Rat) : |q|.num = |q.num| := by
  rw [abs_def']

@[simp]
/--
theorem `den_abs_eq_den` / 定理 `den_abs_eq_den`

English:
theorem den_abs_eq_den
  given: (q : Rat)
  statement: |q|.den = q.den
  proof: by
  rw [abs_def']

中文:
定理 den_abs_eq_den
  条件: (q : Rat)
  结论: |q|.den = q.den
  证明: by
  rw [abs_def']

Depends on / 依赖: abs_def
-/
theorem den_abs_eq_den (q : Rat) : |q|.den = q.den := by
  rw [abs_def']

end Rat
