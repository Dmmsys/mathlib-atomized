/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, David Kurniadi Angdinata
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

/-!
# Models of elliptic curves with prescribed j-invariant

This file defines the Weierstrass equation over a field with prescribed j-invariant,
proved that it is an elliptic curve, and that its j-invariant is equal to the given value.
It is a modification of [silverman2009], Chapter III, Proposition 1.4 (c).

## Main definitions

* `WeierstrassCurve.ofJ0`: an elliptic curve whose j-invariant is 0.
* `WeierstrassCurve.ofJ1728`: an elliptic curve whose j-invariant is 1728.
* `WeierstrassCurve.ofJNe0Or1728`: an elliptic curve whose j-invariant is neither 0 nor 1728.
* `WeierstrassCurve.ofJ`: an elliptic curve whose j-invariant equal to j.

## Main statements

* `WeierstrassCurve.ofJ_j`: the j-invariant of `WeierstrassCurve.ofJ` is equal to j.

## References

* [J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, weierstrass equation, j invariant
-/

@[expose] public section

namespace WeierstrassCurve

variable (R : Type*) [CommRing R] (W : WeierstrassCurve R)

/--
Definition of `ofJ0` / `ofJ0` 的定义

English:
definition ofJ0
  signature: : WeierstrassCurve R
  body: ⟨0, 0, 1, 0, 0⟩

中文:
定义 ofJ0
  签名: : WeierstrassCurve R
  定义体: ⟨0, 0, 1, 0, 0⟩
-/
def ofJ0 : WeierstrassCurve R :=
  ⟨0, 0, 1, 0, 0⟩

/--
lemma `ofJ0_c₄` / 引理 `ofJ0_c₄`

English:
lemma ofJ0_c₄
  statement: (ofJ0 R).c₄ = 0
  proof: by
  rw [ofJ0]; rw [c₄]; rw [b₂]; rw [b₄]
  norm_num1

中文:
引理 ofJ0_c₄
  结论: (ofJ0 R).c₄ = 0
  证明: by
  rw [ofJ0]; rw [c₄]; rw [b₂]; rw [b₄]
  norm_num1

Depends on / 依赖: norm_num1
-/
lemma ofJ0_c₄ : (ofJ0 R).c₄ = 0 := by
  rw [ofJ0]; rw [c₄]; rw [b₂]; rw [b₄]
  norm_num1

/--
lemma `ofJ0_Δ` / 引理 `ofJ0_Δ`

English:
lemma ofJ0_Δ
  statement: (ofJ0 R).Δ = -27
  proof: by
  rw [ofJ0]; rw [Δ]; rw [b₂]; rw [b₄]; rw [b₆]; rw [b₈]
  norm_num1

中文:
引理 ofJ0_Δ
  结论: (ofJ0 R).Δ = -27
  证明: by
  rw [ofJ0]; rw [Δ]; rw [b₂]; rw [b₄]; rw [b₆]; rw [b₈]
  norm_num1

Depends on / 依赖: norm_num1
-/
lemma ofJ0_Δ : (ofJ0 R).Δ = -27 := by
  rw [ofJ0]; rw [Δ]; rw [b₂]; rw [b₄]; rw [b₆]; rw [b₈]
  norm_num1

/--
Definition of `ofJ1728` / `ofJ1728` 的定义

English:
definition ofJ1728
  signature: : WeierstrassCurve R
  body: ⟨0, 0, 0, 1, 0⟩

中文:
定义 ofJ1728
  签名: : WeierstrassCurve R
  定义体: ⟨0, 0, 0, 1, 0⟩
-/
def ofJ1728 : WeierstrassCurve R :=
  ⟨0, 0, 0, 1, 0⟩

/--
lemma `ofJ1728_c₄` / 引理 `ofJ1728_c₄`

English:
lemma ofJ1728_c₄
  statement: (ofJ1728 R).c₄ = -48
  proof: by
  rw [ofJ1728]; rw [c₄]; rw [b₂]; rw [b₄]
  norm_num1

中文:
引理 ofJ1728_c₄
  结论: (ofJ1728 R).c₄ = -48
  证明: by
  rw [ofJ1728]; rw [c₄]; rw [b₂]; rw [b₄]
  norm_num1

Depends on / 依赖: norm_num1, ofJ1728
-/
lemma ofJ1728_c₄ : (ofJ1728 R).c₄ = -48 := by
  rw [ofJ1728]; rw [c₄]; rw [b₂]; rw [b₄]
  norm_num1

/--
lemma `ofJ1728_Δ` / 引理 `ofJ1728_Δ`

English:
lemma ofJ1728_Δ
  statement: (ofJ1728 R).Δ = -64
  proof: by
  rw [ofJ1728]; rw [Δ]; rw [b₂]; rw [b₄]; rw [b₆]; rw [b₈]
  norm_num1

中文:
引理 ofJ1728_Δ
  结论: (ofJ1728 R).Δ = -64
  证明: by
  rw [ofJ1728]; rw [Δ]; rw [b₂]; rw [b₄]; rw [b₆]; rw [b₈]
  norm_num1

Depends on / 依赖: norm_num1, ofJ1728
-/
lemma ofJ1728_Δ : (ofJ1728 R).Δ = -64 := by
  rw [ofJ1728]; rw [Δ]; rw [b₂]; rw [b₄]; rw [b₆]; rw [b₈]
  norm_num1

variable {R} (j : R)

/--
Definition of `ofJNe0Or1728` / `ofJNe0Or1728` 的定义

English:
definition ofJNe0Or1728
  signature: : WeierstrassCurve R
  body: ⟨j - 1728, 0, 0, -36 * (j - 1728) ^ 3, -(j - 1728) ^ 5⟩

中文:
定义 ofJNe0Or1728
  签名: : WeierstrassCurve R
  定义体: ⟨j - 1728, 0, 0, -36 * (j - 1728) ^ 3, -(j - 1728) ^ 5⟩
-/
def ofJNe0Or1728 : WeierstrassCurve R :=
  ⟨j - 1728, 0, 0, -36 * (j - 1728) ^ 3, -(j - 1728) ^ 5⟩

/--
lemma `ofJNe0Or1728_c₄` / 引理 `ofJNe0Or1728_c₄`

English:
lemma ofJNe0Or1728_c₄
  statement: (ofJNe0Or1728 j).c₄ = j * (j - 1728) ^ 3
  proof: by
  simp only [ofJNe0Or1728, c₄, b₂, b₄]
  ring1

中文:
引理 ofJNe0Or1728_c₄
  结论: (ofJNe0Or1728 j).c₄ = j * (j - 1728) ^ 3
  证明: by
  simp only [ofJNe0Or1728, c₄, b₂, b₄]
  ring1

Depends on / 依赖: ofJNe0Or1728
-/
lemma ofJNe0Or1728_c₄ : (ofJNe0Or1728 j).c₄ = j * (j - 1728) ^ 3 := by
  simp only [ofJNe0Or1728, c₄, b₂, b₄]
  ring1

/--
lemma `ofJNe0Or1728_Δ` / 引理 `ofJNe0Or1728_Δ`

English:
lemma ofJNe0Or1728_Δ
  statement: (ofJNe0Or1728 j).Δ = j ^ 2 * (j - 1728) ^ 9
  proof: by
  simp only [ofJNe0Or1728, Δ, b₂, b₄, b₆, b₈]
  ring1

中文:
引理 ofJNe0Or1728_Δ
  结论: (ofJNe0Or1728 j).Δ = j ^ 2 * (j - 1728) ^ 9
  证明: by
  simp only [ofJNe0Or1728, Δ, b₂, b₄, b₆, b₈]
  ring1

Depends on / 依赖: ofJNe0Or1728
-/
lemma ofJNe0Or1728_Δ : (ofJNe0Or1728 j).Δ = j ^ 2 * (j - 1728) ^ 9 := by
  simp only [ofJNe0Or1728, Δ, b₂, b₄, b₆, b₈]
  ring1

variable (R) [W.IsElliptic]

-- TODO: change to `[IsUnit ...]` once https://github.com/leanprover-community/mathlib4/issues/17458 is merged
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [hu
  signature: : Fact (IsUnit (3 : R))] : (ofJ0 R).IsElliptic
  body: by
  rw [isElliptic_iff]; rw [ofJ0_Δ]
  convert! (hu.out.pow 3).neg
  norm_num1

中文:
实例 [hu
  签名: : Fact (IsUnit (3 : R))] : (ofJ0 R).IsElliptic
  定义体: by
  rw [isElliptic_iff]; rw [ofJ0_Δ]
  convert! (hu.out.pow 3).neg
  norm_num1

Depends on / 依赖: convert, hu.out.pow, isElliptic_iff, norm_num1
-/
instance [hu : Fact (IsUnit (3 : R))] : (ofJ0 R).IsElliptic := by
  rw [isElliptic_iff]; rw [ofJ0_Δ]
  convert! (hu.out.pow 3).neg
  norm_num1

-- TODO: change to `[IsUnit ...]` once https://github.com/leanprover-community/mathlib4/issues/17458 is merged
/--
lemma `ofJ0_j` / 引理 `ofJ0_j`

English:
lemma ofJ0_j
  given: [Fact (IsUnit (3 : R))]
  statement: (ofJ0 R).j = 0
  proof: by
  rw [j]; rw [ofJ0_c₄]
  ring1

中文:
引理 ofJ0_j
  条件: [Fact (IsUnit (3 : R))]
  结论: (ofJ0 R).j = 0
  证明: by
  rw [j]; rw [ofJ0_c₄]
  ring1
-/
lemma ofJ0_j [Fact (IsUnit (3 : R))] : (ofJ0 R).j = 0 := by
  rw [j]; rw [ofJ0_c₄]
  ring1

-- TODO: change to `[IsUnit ...]` once https://github.com/leanprover-community/mathlib4/issues/17458 is merged
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [hu
  signature: : Fact (IsUnit (2 : R))] : (ofJ1728 R).IsElliptic
  body: by
  rw [isElliptic_iff]; rw [ofJ1728_Δ]
  convert! (hu.out.pow 6).neg
  norm_num1

中文:
实例 [hu
  签名: : Fact (IsUnit (2 : R))] : (ofJ1728 R).IsElliptic
  定义体: by
  rw [isElliptic_iff]; rw [ofJ1728_Δ]
  convert! (hu.out.pow 6).neg
  norm_num1

Depends on / 依赖: convert, hu.out.pow, isElliptic_iff, norm_num1
-/
instance [hu : Fact (IsUnit (2 : R))] : (ofJ1728 R).IsElliptic := by
  rw [isElliptic_iff]; rw [ofJ1728_Δ]
  convert! (hu.out.pow 6).neg
  norm_num1

-- TODO: change to `[IsUnit ...]` once https://github.com/leanprover-community/mathlib4/issues/17458 is merged
/--
lemma `ofJ1728_j` / 引理 `ofJ1728_j`

English:
lemma ofJ1728_j
  given: [Fact (IsUnit (2 : R))]
  statement: (ofJ1728 R).j = 1728
  proof: by
  rw [j]; rw [Units.inv_mul_eq_iff_eq_mul]; rw [ofJ1728_c₄]; rw [coe_Δ']; rw [ofJ1728_Δ]
  norm_num1

中文:
引理 ofJ1728_j
  条件: [Fact (IsUnit (2 : R))]
  结论: (ofJ1728 R).j = 1728
  证明: by
  rw [j]; rw [Units.inv_mul_eq_iff_eq_mul]; rw [ofJ1728_c₄]; rw [coe_Δ']; rw [ofJ1728_Δ]
  norm_num1

Depends on / 依赖: Units.inv_mul_eq_iff_eq_mul, inv_mul_eq_iff_eq_mul, norm_num1
-/
lemma ofJ1728_j [Fact (IsUnit (2 : R))] : (ofJ1728 R).j = 1728 := by
  rw [j]; rw [Units.inv_mul_eq_iff_eq_mul]; rw [ofJ1728_c₄]; rw [coe_Δ']; rw [ofJ1728_Δ]
  norm_num1

variable {R}

-- TODO: change to `[IsUnit ...]` once https://github.com/leanprover-community/mathlib4/issues/17458 is merged
/-- When j and j - 1728 are both units,
`Y² + (j - 1728)XY = X³ - 36(j - 1728)³X - (j - 1728)⁵` is an elliptic curve.
It is of j-invariant j (see `WeierstrassCurve.ofJNe0Or1728_j`). -/
instance (j : R) [h1 : Fact (IsUnit j)] [h2 : Fact (IsUnit (j - 1728))] :
    (ofJNe0Or1728 j).IsElliptic := by
  rw [isElliptic_iff]; rw [ofJNe0Or1728_Δ]
  exact (h1.out.pow 2).mul (h2.out.pow 9)

-- TODO: change to `[IsUnit ...]` once https://github.com/leanprover-community/mathlib4/issues/17458 is merged
/--
lemma `ofJNe0Or1728_j` / 引理 `ofJNe0Or1728_j`

English:
lemma ofJNe0Or1728_j
  given: (j : R) [Fact (IsUnit j)] [Fact (IsUnit (j - 1728))]
  proof: by
  rw [WeierstrassCurve.j]; rw [Units.inv_mul_eq_iff_eq_mul]; rw [ofJNe0Or1728_c₄]; rw [coe_Δ']; rw [ofJNe0Or1728_Δ]
  ring1

中文:
引理 ofJNe0Or1728_j
  条件: (j : R) [Fact (IsUnit j)] [Fact (IsUnit (j - 1728))]
  证明: by
  rw [WeierstrassCurve.j]; rw [Units.inv_mul_eq_iff_eq_mul]; rw [ofJNe0Or1728_c₄]; rw [coe_Δ']; rw [ofJNe0Or1728_Δ]
  ring1

Depends on / 依赖: Units.inv_mul_eq_iff_eq_mul, WeierstrassCurve, WeierstrassCurve.j, inv_mul_eq_iff_eq_mul
-/
lemma ofJNe0Or1728_j (j : R) [Fact (IsUnit j)] [Fact (IsUnit (j - 1728))] :
    (ofJNe0Or1728 j).j = j := by
  rw [WeierstrassCurve.j]; rw [Units.inv_mul_eq_iff_eq_mul]; rw [ofJNe0Or1728_c₄]; rw [coe_Δ']; rw [ofJNe0Or1728_Δ]
  ring1

variable {F : Type*} [Field F] (j : F) [DecidableEq F]

/--
Definition of `ofJ` / `ofJ` 的定义

English:
definition ofJ
  signature: : WeierstrassCurve F
  body: if j = 0 then if (3 : F) = 0 then ofJ1728 F else ofJ0 F
  else if j = 1728 then ofJ1728 F else ofJNe0Or1728 j

中文:
定义 ofJ
  签名: : WeierstrassCurve F
  定义体: if j = 0 then if (3 : F) = 0 then ofJ1728 F else ofJ0 F
  else if j = 1728 then ofJ1728 F else ofJNe0Or1728 j

Depends on / 依赖: ofJ1728, ofJNe0Or1728
-/
def ofJ : WeierstrassCurve F :=
  if j = 0 then if (3 : F) = 0 then ofJ1728 F else ofJ0 F
  else if j = 1728 then ofJ1728 F else ofJNe0Or1728 j

/--
lemma `ofJ_0_of_three_ne_zero` / 引理 `ofJ_0_of_three_ne_zero`

English:
lemma ofJ_0_of_three_ne_zero
  given: (h3 : (3 : F) != 0)
  statement: ofJ 0 = ofJ0 F
  proof: by
  rw [ofJ]; rw [if_pos rfl]; rw [if_neg h3]

中文:
引理 ofJ_0_of_three_ne_zero
  条件: (h3 : (3 : F) != 0)
  结论: ofJ 0 = ofJ0 F
  证明: by
  rw [ofJ]; rw [if_pos rfl]; rw [if_neg h3]

Depends on / 依赖: Localization, Localization.inverts, if_neg, if_pos, inverts, toHoCat, weakEquivalence_iff, weakEquivalences
-/
lemma ofJ_0_of_three_ne_zero (h3 : (3 : F) != 0) : ofJ 0 = ofJ0 F := by
  rw [ofJ]; rw [if_pos rfl]; rw [if_neg h3]

/--
lemma `ofJ_0_of_three_eq_zero` / 引理 `ofJ_0_of_three_eq_zero`

English:
lemma ofJ_0_of_three_eq_zero
  given: (h3 : (3 : F) = 0)
  statement: ofJ 0 = ofJ1728 F
  proof: by
  rw [ofJ]; rw [if_pos rfl]; rw [if_pos h3]

中文:
引理 ofJ_0_of_three_eq_zero
  条件: (h3 : (3 : F) = 0)
  结论: ofJ 0 = ofJ1728 F
  证明: by
  rw [ofJ]; rw [if_pos rfl]; rw [if_pos h3]

Depends on / 依赖: if_pos
-/
lemma ofJ_0_of_three_eq_zero (h3 : (3 : F) = 0) : ofJ 0 = ofJ1728 F := by
  rw [ofJ]; rw [if_pos rfl]; rw [if_pos h3]

/--
lemma `ofJ_0_of_two_eq_zero` / 引理 `ofJ_0_of_two_eq_zero`

English:
lemma ofJ_0_of_two_eq_zero
  given: (h2 : (2 : F) = 0)
  statement: ofJ 0 = ofJ0 F
  proof: by
  rw [ofJ]; rw [if_pos rfl]; rw [if_neg ((show (3 : F) = 1 by linear_combination h2) ▸ one_ne_zero)]

中文:
引理 ofJ_0_of_two_eq_zero
  条件: (h2 : (2 : F) = 0)
  结论: ofJ 0 = ofJ0 F
  证明: by
  rw [ofJ]; rw [if_pos rfl]; rw [if_neg ((show (3 : F) = 1 by linear_combination h2) ▸ one_ne_zero)]

Depends on / 依赖: if_neg, if_pos, linear_combination, one_ne_zero
-/
lemma ofJ_0_of_two_eq_zero (h2 : (2 : F) = 0) : ofJ 0 = ofJ0 F := by
  rw [ofJ]; rw [if_pos rfl]; rw [if_neg ((show (3 : F) = 1 by linear_combination h2) ▸ one_ne_zero)]

/--
lemma `ofJ_1728_of_three_eq_zero` / 引理 `ofJ_1728_of_three_eq_zero`

English:
lemma ofJ_1728_of_three_eq_zero
  given: (h3 : (3 : F) = 0)
  statement: ofJ 1728 = ofJ1728 F
  proof: by
  rw [ofJ]; rw [if_pos (by linear_combination 576 * h3)]; rw [if_pos h3]

中文:
引理 ofJ_1728_of_three_eq_zero
  条件: (h3 : (3 : F) = 0)
  结论: ofJ 1728 = ofJ1728 F
  证明: by
  rw [ofJ]; rw [if_pos (by linear_combination 576 * h3)]; rw [if_pos h3]

Depends on / 依赖: if_pos, linear_combination
-/
lemma ofJ_1728_of_three_eq_zero (h3 : (3 : F) = 0) : ofJ 1728 = ofJ1728 F := by
  rw [ofJ]; rw [if_pos (by linear_combination 576 * h3)]; rw [if_pos h3]

/--
lemma `ofJ_1728_of_two_ne_zero` / 引理 `ofJ_1728_of_two_ne_zero`

English:
lemma ofJ_1728_of_two_ne_zero
  given: (h2 : (2 : F) != 0)
  statement: ofJ 1728 = ofJ1728 F
  proof: by
  by_cases h3 : (3 : F) = 0
  · exact ofJ_1728_of_three_eq_zero h3
  · rw [ofJ, show (1728 : F) = 2 ^ 6 * 3 ^ 3 by norm_num1,
      if_neg (mul_ne_zero (pow_ne_zero 6 h2) (pow_ne_zero 3 h3)), if_pos rfl]

中文:
引理 ofJ_1728_of_two_ne_zero
  条件: (h2 : (2 : F) != 0)
  结论: ofJ 1728 = ofJ1728 F
  证明: by
  by_cases h3 : (3 : F) = 0
  · exact ofJ_1728_of_three_eq_zero h3
  · rw [ofJ, show (1728 : F) = 2 ^ 6 * 3 ^ 3 by norm_num1,
      if_neg (mul_ne_zero (pow_ne_zero 6 h2) (pow_ne_zero 3 h3)), if_pos rfl]

Depends on / 依赖: if_neg, if_pos, mul_ne_zero, norm_num1, ofJ_1728_of_three_eq_zero, pow_ne_zero
-/
lemma ofJ_1728_of_two_ne_zero (h2 : (2 : F) != 0) : ofJ 1728 = ofJ1728 F := by
  by_cases h3 : (3 : F) = 0
  · exact ofJ_1728_of_three_eq_zero h3
  · rw [ofJ, show (1728 : F) = 2 ^ 6 * 3 ^ 3 by norm_num1,
      if_neg (mul_ne_zero (pow_ne_zero 6 h2) (pow_ne_zero 3 h3)), if_pos rfl]

/--
lemma `ofJ_1728_of_two_eq_zero` / 引理 `ofJ_1728_of_two_eq_zero`

English:
lemma ofJ_1728_of_two_eq_zero
  given: (h2 : (2 : F) = 0)
  statement: ofJ 1728 = ofJ0 F
  proof: by
  rw [ofJ]; rw [if_pos (by linear_combination 864 * h2)]; rw [if_neg ((show (3 : F) = 1 by linear_combination h2) ▸ one_ne_zero)]

中文:
引理 ofJ_1728_of_two_eq_zero
  条件: (h2 : (2 : F) = 0)
  结论: ofJ 1728 = ofJ0 F
  证明: by
  rw [ofJ]; rw [if_pos (by linear_combination 864 * h2)]; rw [if_neg ((show (3 : F) = 1 by linear_combination h2) ▸ one_ne_zero)]

Depends on / 依赖: if_neg, if_pos, linear_combination, one_ne_zero
-/
lemma ofJ_1728_of_two_eq_zero (h2 : (2 : F) = 0) : ofJ 1728 = ofJ0 F := by
  rw [ofJ]; rw [if_pos (by linear_combination 864 * h2)]; rw [if_neg ((show (3 : F) = 1 by linear_combination h2) ▸ one_ne_zero)]

/--
lemma `ofJ_ne_0_ne_1728` / 引理 `ofJ_ne_0_ne_1728`

English:
lemma ofJ_ne_0_ne_1728
  given: (h0 : j != 0) (h1728 : j != 1728)
  statement: ofJ j = ofJNe0Or1728 j
  proof: by
  rw [ofJ]; rw [if_neg h0]; rw [if_neg h1728]

中文:
引理 ofJ_ne_0_ne_1728
  条件: (h0 : j != 0) (h1728 : j != 1728)
  结论: ofJ j = ofJNe0Or1728 j
  证明: by
  rw [ofJ]; rw [if_neg h0]; rw [if_neg h1728]

Depends on / 依赖: if_neg
-/
lemma ofJ_ne_0_ne_1728 (h0 : j != 0) (h1728 : j != 1728) : ofJ j = ofJNe0Or1728 j := by
  rw [ofJ]; rw [if_neg h0]; rw [if_neg h1728]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (ofJ j).IsElliptic
  body: by
  by_cases h0 : j = 0
  · by_cases h3 : (3 : F) = 0
· have : Fact IsUnit (2 : F) := ⟨.of_mul_eq_one 2 by linear_combination h3⟩
      rw [h0]; rw [ofJ_0_of_three_eq_zero h3]
      infer_instance
    · have := Fact.mk (Ne.isUnit h3)
      rw [h0]; rw [ofJ_0_of_three_ne_zero h3]
      infer_instanc

中文:
实例 :
  签名: (ofJ j).IsElliptic
  定义体: by
  by_cases h0 : j = 0
  · by_cases h3 : (3 : F) = 0
· have : Fact IsUnit (2 : F) := ⟨.of_mul_eq_one 2 by linear_combination h3⟩
      rw [h0]; rw [ofJ_0_of_three_eq_zero h3]
      infer_instance
    · have := Fact.mk (Ne.isUnit h3)
      rw [h0]; rw [ofJ_0_of_three_ne_zero h3]
      infer_instanc

Depends on / 依赖: Fact.mk, IsUnit, Ne.isUnit, h2.isUnit, infer_instance, isUnit, linear_combination, ofJ_0_of_three_eq_zero, ofJ_0_of_three_ne_zero, ofJ_1728_of_two_ne_zero, of_mul_eq_one
-/
instance : (ofJ j).IsElliptic := by
  by_cases h0 : j = 0
  · by_cases h3 : (3 : F) = 0
· have : Fact IsUnit (2 : F) := ⟨.of_mul_eq_one 2 by linear_combination h3⟩
      rw [h0]; rw [ofJ_0_of_three_eq_zero h3]
      infer_instance
    · have := Fact.mk (Ne.isUnit h3)
      rw [h0]; rw [ofJ_0_of_three_ne_zero h3]
      infer_instance
  · by_cases h1728 : j = 1728
    · have h2 : (2 : F) != 0 := fun h => h0 (by linear_combination h1728 + 864 * h)
      have := Fact.mk h2.isUnit
      rw [h1728]; rw [ofJ_1728_of_two_ne_zero h2]
      infer_instance
    · have := Fact.mk (Ne.isUnit h0)
      have := Fact.mk (sub_ne_zero.2 h1728).isUnit
      rw [ofJ_ne_0_ne_1728 j h0 h1728]
      infer_instance

/--
lemma `ofJ_j` / 引理 `ofJ_j`

English:
lemma ofJ_j
  statement: (ofJ j).j = j
  proof: by
  by_cases h0 : j = 0
  · by_cases h3 : (3 : F) = 0
· have : Fact IsUnit (2 : F) := ⟨.of_mul_eq_one 2 by linear_combination h3⟩
      simp_rw [h0, ofJ_0_of_three_eq_zero h3, ofJ1728_j]
      linear_combination 576 * h3
    · have := Fact.mk (Ne.isUnit h3)
      simp_rw [h0, ofJ_0_of_three_ne_zero

中文:
引理 ofJ_j
  结论: (ofJ j).j = j
  证明: by
  by_cases h0 : j = 0
  · by_cases h3 : (3 : F) = 0
· have : Fact IsUnit (2 : F) := ⟨.of_mul_eq_one 2 by linear_combination h3⟩
      simp_rw [h0, ofJ_0_of_three_eq_zero h3, ofJ1728_j]
      linear_combination 576 * h3
    · have := Fact.mk (Ne.isUnit h3)
      simp_rw [h0, ofJ_0_of_three_ne_zero

Depends on / 依赖: Fact.mk, IsUnit, Ne.is, Ne.isUnit, h2.isUnit, isUnit, linear_combination, ofJ0_j, ofJ1728_j, ofJ_0_of_three_eq_zero, ofJ_0_of_three_ne_zero, ofJ_1728_of_two_ne_zero, of_mul_eq_one, simp_rw
-/
lemma ofJ_j : (ofJ j).j = j := by
  by_cases h0 : j = 0
  · by_cases h3 : (3 : F) = 0
· have : Fact IsUnit (2 : F) := ⟨.of_mul_eq_one 2 by linear_combination h3⟩
      simp_rw [h0, ofJ_0_of_three_eq_zero h3, ofJ1728_j]
      linear_combination 576 * h3
    · have := Fact.mk (Ne.isUnit h3)
      simp_rw [h0, ofJ_0_of_three_ne_zero h3, ofJ0_j]
  · by_cases h1728 : j = 1728
    · have h2 : (2 : F) != 0 := fun h => h0 (by linear_combination h1728 + 864 * h)
      have := Fact.mk h2.isUnit
      simp_rw [h1728, ofJ_1728_of_two_ne_zero h2, ofJ1728_j]
    · have := Fact.mk (Ne.isUnit h0)
      have := Fact.mk (sub_ne_zero.2 h1728).isUnit
      simp_rw [ofJ_ne_0_ne_1728 j h0 h1728, ofJNe0Or1728_j]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited { W : WeierstrassCurve F // W.IsElliptic }
  body: ⟨⟨ofJ 37, inferInstance⟩⟩

中文:
实例 :
  签名: Inhabited { W : WeierstrassCurve F // W.IsElliptic }
  定义体: ⟨⟨ofJ 37, inferInstance⟩⟩
-/
instance : Inhabited { W : WeierstrassCurve F // W.IsElliptic } :=
  ⟨⟨ofJ 37, inferInstance⟩⟩

end WeierstrassCurve
