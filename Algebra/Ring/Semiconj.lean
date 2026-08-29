/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov, Neil Strickland
-/
module

public import Mathlib.Algebra.Group.Semiconj.Defs
public import Mathlib.Algebra.Ring.Defs

/-!
# Semirings and rings

This file gives lemmas about semirings, rings and domains.
This is analogous to `Mathlib/Algebra/Group/Basic.lean`,
the difference being that the former is about `+` and `*` separately, while
the present file is about their interaction.

For the definitions of semirings and rings see `Mathlib/Algebra/Ring/Defs.lean`.

-/

public section


universe u

variable {R : Type u}

open Function

namespace SemiconjBy

@[simp]
/--
theorem `add_right` / 定理 `add_right`

English:
theorem add_right
  given: [Distrib R] {a x y x' y' : R} (h : SemiconjBy a x y) (h' : SemiconjBy a x' y')
  proof: by
  simp only [SemiconjBy, left_distrib, right_distrib, h.eq, h'.eq]

@[simp]

中文:
定理 add_right
  条件: [Distrib R] {a x y x' y' : R} (h : SemiconjBy a x y) (h' : SemiconjBy a x' y')
  证明: by
  simp only [SemiconjBy, left_distrib, right_distrib, h.eq, h'.eq]

@[simp]

Depends on / 依赖: SemiconjBy, h.eq, left_distrib, right_distrib
-/
theorem add_right [Distrib R] {a x y x' y' : R} (h : SemiconjBy a x y) (h' : SemiconjBy a x' y') :
    SemiconjBy a (x + x') (y + y') := by
  simp only [SemiconjBy, left_distrib, right_distrib, h.eq, h'.eq]

@[simp]
/--
theorem `add_left` / 定理 `add_left`

English:
theorem add_left
  given: [Distrib R] {a b x y : R} (ha : SemiconjBy a x y) (hb : SemiconjBy b x y)
  proof: by
  simp only [SemiconjBy, left_distrib, right_distrib, ha.eq, hb.eq]

中文:
定理 add_left
  条件: [Distrib R] {a b x y : R} (ha : SemiconjBy a x y) (hb : SemiconjBy b x y)
  证明: by
  simp only [SemiconjBy, left_distrib, right_distrib, ha.eq, hb.eq]

Depends on / 依赖: SemiconjBy, ha.eq, hb.eq, left_distrib, right_distrib
-/
theorem add_left [Distrib R] {a b x y : R} (ha : SemiconjBy a x y) (hb : SemiconjBy b x y) :
    SemiconjBy (a + b) x y := by
  simp only [SemiconjBy, left_distrib, right_distrib, ha.eq, hb.eq]

section

variable [Mul R] [HasDistribNeg R] {a x y : R}

/--
theorem `neg_right` / 定理 `neg_right`

English:
theorem neg_right
  given: (h : SemiconjBy a x y)
  statement: SemiconjBy a (-x) (-y)
  proof: by
  simp only [SemiconjBy, h.eq, neg_mul, mul_neg]

@[simp]

中文:
定理 neg_right
  条件: (h : SemiconjBy a x y)
  结论: SemiconjBy a (-x) (-y)
  证明: by
  simp only [SemiconjBy, h.eq, neg_mul, mul_neg]

@[simp]

Depends on / 依赖: SemiconjBy, h.eq, mul_neg, neg_mul
-/
theorem neg_right (h : SemiconjBy a x y) : SemiconjBy a (-x) (-y) := by
  simp only [SemiconjBy, h.eq, neg_mul, mul_neg]

@[simp]
/--
theorem `neg_right_iff` / 定理 `neg_right_iff`

English:
theorem neg_right_iff
  statement: SemiconjBy a (-x) (-y) ↔ SemiconjBy a x y
  proof: ⟨fun h => neg_neg x ▸ neg_neg y ▸ h.neg_right, SemiconjBy.neg_right⟩

中文:
定理 neg_right_iff
  结论: SemiconjBy a (-x) (-y) ↔ SemiconjBy a x y
  证明: ⟨fun h => neg_neg x ▸ neg_neg y ▸ h.neg_right, SemiconjBy.neg_right⟩

Depends on / 依赖: SemiconjBy, SemiconjBy.neg_right, h.neg_right, neg_neg, neg_right
-/
theorem neg_right_iff : SemiconjBy a (-x) (-y) ↔ SemiconjBy a x y :=
  ⟨fun h => neg_neg x ▸ neg_neg y ▸ h.neg_right, SemiconjBy.neg_right⟩

/--
theorem `neg_left` / 定理 `neg_left`

English:
theorem neg_left
  given: (h : SemiconjBy a x y)
  statement: SemiconjBy (-a) x y
  proof: by
  simp only [SemiconjBy, h.eq, neg_mul, mul_neg]

@[simp]

中文:
定理 neg_left
  条件: (h : SemiconjBy a x y)
  结论: SemiconjBy (-a) x y
  证明: by
  simp only [SemiconjBy, h.eq, neg_mul, mul_neg]

@[simp]

Depends on / 依赖: SemiconjBy, h.eq, mul_neg, neg_mul
-/
theorem neg_left (h : SemiconjBy a x y) : SemiconjBy (-a) x y := by
  simp only [SemiconjBy, h.eq, neg_mul, mul_neg]

@[simp]
/--
theorem `neg_left_iff` / 定理 `neg_left_iff`

English:
theorem neg_left_iff
  statement: SemiconjBy (-a) x y ↔ SemiconjBy a x y
  proof: ⟨fun h => neg_neg a ▸ h.neg_left, SemiconjBy.neg_left⟩

中文:
定理 neg_left_iff
  结论: SemiconjBy (-a) x y ↔ SemiconjBy a x y
  证明: ⟨fun h => neg_neg a ▸ h.neg_left, SemiconjBy.neg_left⟩

Depends on / 依赖: SemiconjBy, SemiconjBy.neg_left, h.neg_left, neg_left, neg_neg
-/
theorem neg_left_iff : SemiconjBy (-a) x y ↔ SemiconjBy a x y :=
  ⟨fun h => neg_neg a ▸ h.neg_left, SemiconjBy.neg_left⟩

end

section

variable [MulOneClass R] [HasDistribNeg R]

/--
theorem `neg_one_right` / 定理 `neg_one_right`

English:
theorem neg_one_right
  given: (a : R)
  statement: SemiconjBy a (-1) (-1)
  proof: by simp

中文:
定理 neg_one_right
  条件: (a : R)
  结论: SemiconjBy a (-1) (-1)
  证明: by simp
-/
theorem neg_one_right (a : R) : SemiconjBy a (-1) (-1) := by simp

/--
theorem `neg_one_left` / 定理 `neg_one_left`

English:
theorem neg_one_left
  given: (x : R)
  statement: SemiconjBy (-1) x x
  proof: by simp

中文:
定理 neg_one_left
  条件: (x : R)
  结论: SemiconjBy (-1) x x
  证明: by simp
-/
theorem neg_one_left (x : R) : SemiconjBy (-1) x x := by simp

end

section

variable [NonUnitalNonAssocRing R] {a b x y x' y' : R}

@[simp]
/--
theorem `sub_right` / 定理 `sub_right`

English:
theorem sub_right
  given: (h : SemiconjBy a x y) (h' : SemiconjBy a x' y')
  proof: by
  simpa only [sub_eq_add_neg] using h.add_right h'.neg_right

@[simp]

中文:
定理 sub_right
  条件: (h : SemiconjBy a x y) (h' : SemiconjBy a x' y')
  证明: by
  simpa only [sub_eq_add_neg] using h.add_right h'.neg_right

@[simp]

Depends on / 依赖: add_right, h.add_right, neg_right, sub_eq_add_neg
-/
theorem sub_right (h : SemiconjBy a x y) (h' : SemiconjBy a x' y') :
    SemiconjBy a (x - x') (y - y') := by
  simpa only [sub_eq_add_neg] using h.add_right h'.neg_right

@[simp]
/--
theorem `sub_left` / 定理 `sub_left`

English:
theorem sub_left
  given: (ha : SemiconjBy a x y) (hb : SemiconjBy b x y)
  proof: by
  simpa only [sub_eq_add_neg] using ha.add_left hb.neg_left

中文:
定理 sub_left
  条件: (ha : SemiconjBy a x y) (hb : SemiconjBy b x y)
  证明: by
  simpa only [sub_eq_add_neg] using ha.add_left hb.neg_left

Depends on / 依赖: add_left, ha.add_left, hb.neg_left, neg_left, sub_eq_add_neg
-/
theorem sub_left (ha : SemiconjBy a x y) (hb : SemiconjBy b x y) :
    SemiconjBy (a - b) x y := by
  simpa only [sub_eq_add_neg] using ha.add_left hb.neg_left

end

end SemiconjBy
