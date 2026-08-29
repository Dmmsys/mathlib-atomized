/-
Copyright (c) 2024 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
public import Mathlib.Tactic.ComputeDegree

/-!
# Division polynomials of Weierstrass curves

This file computes the leading terms of certain polynomials associated to division polynomials of
Weierstrass curves defined in
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean`.

## Mathematical background

Let `W` be a Weierstrass curve over a commutative ring `R`. By strong induction,
* `preΨₙ` has leading coefficient `n / 2` and degree `(n² - 4) / 2` if `n` is even,
* `preΨₙ` has leading coefficient `n` and degree `(n² - 1) / 2` if `n` is odd,
* `ΨSqₙ` has leading coefficient `n²` and degree `n² - 1`, and
* `Φₙ` has leading coefficient `1` and degree `n²`.

In particular, when `R` is an integral domain of characteristic different from `n`, the univariate
polynomials `preΨₙ`, `ΨSqₙ`, and `Φₙ` all have their expected leading terms.

## Main statements

* `WeierstrassCurve.natDegree_preΨ_le`: the degree bound `d` of `preΨₙ`.
* `WeierstrassCurve.coeff_preΨ`: the `d`-th coefficient of `preΨₙ`.
* `WeierstrassCurve.natDegree_preΨ`: the degree of `preΨₙ` when `n ≠ 0`.
* `WeierstrassCurve.leadingCoeff_preΨ`: the leading coefficient of `preΨₙ` when `n ≠ 0`.
* `WeierstrassCurve.natDegree_ΨSq_le`: the degree bound `d` of `ΨSqₙ`.
* `WeierstrassCurve.coeff_ΨSq`: the `d`-th coefficient of `ΨSqₙ`.
* `WeierstrassCurve.natDegree_ΨSq`: the degree of `ΨSqₙ` when `n ≠ 0`.
* `WeierstrassCurve.leadingCoeff_ΨSq`: the leading coefficient of `ΨSqₙ` when `n ≠ 0`.
* `WeierstrassCurve.natDegree_Φ_le`: the degree bound `d` of `Φₙ`.
* `WeierstrassCurve.coeff_Φ`: the `d`-th coefficient of `Φₙ`.
* `WeierstrassCurve.natDegree_Φ`: the degree of `Φₙ` when `n ≠ 0`.
* `WeierstrassCurve.leadingCoeff_Φ`: the leading coefficient of `Φₙ` when `n ≠ 0`.

## References

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, division polynomial, torsion point
-/

public section

open Polynomial

universe u

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

section Ψ₂Sq

/--
lemma `natDegree_Ψ₂Sq_le` / 引理 `natDegree_Ψ₂Sq_le`

English:
lemma natDegree_Ψ₂Sq_le
  statement: W.Ψ₂Sq.natDegree <= 3
  proof: by
  rw [Ψ₂Sq]
  compute_degree

@[simp]

中文:
引理 natDegree_Ψ₂Sq_le
  结论: W.Ψ₂Sq.natDegree <= 3
  证明: by
  rw [Ψ₂Sq]
  compute_degree

@[simp]

Depends on / 依赖: compute_degree
-/
lemma natDegree_Ψ₂Sq_le : W.Ψ₂Sq.natDegree <= 3 := by
  rw [Ψ₂Sq]
  compute_degree

@[simp]
/--
lemma `coeff_Ψ₂Sq` / 引理 `coeff_Ψ₂Sq`

English:
lemma coeff_Ψ₂Sq
  statement: W.Ψ₂Sq.coeff 3 = 4
  proof: by
  rw [Ψ₂Sq]
  compute_degree!

中文:
引理 coeff_Ψ₂Sq
  结论: W.Ψ₂Sq.coeff 3 = 4
  证明: by
  rw [Ψ₂Sq]
  compute_degree!

Depends on / 依赖: compute_degree
-/
lemma coeff_Ψ₂Sq : W.Ψ₂Sq.coeff 3 = 4 := by
  rw [Ψ₂Sq]
  compute_degree!

/--
lemma `coeff_Ψ₂Sq_ne_zero` / 引理 `coeff_Ψ₂Sq_ne_zero`

English:
lemma coeff_Ψ₂Sq_ne_zero
  given: (h : (4 : R) != 0)
  statement: W.Ψ₂Sq.coeff 3 != 0
  proof: by
  rwa [coeff_Ψ₂Sq]

@[simp]

中文:
引理 coeff_Ψ₂Sq_ne_zero
  条件: (h : (4 : R) != 0)
  结论: W.Ψ₂Sq.coeff 3 != 0
  证明: by
  rwa [coeff_Ψ₂Sq]

@[simp]
-/
lemma coeff_Ψ₂Sq_ne_zero (h : (4 : R) != 0) : W.Ψ₂Sq.coeff 3 != 0 := by
  rwa [coeff_Ψ₂Sq]

@[simp]
/--
lemma `natDegree_Ψ₂Sq` / 引理 `natDegree_Ψ₂Sq`

English:
lemma natDegree_Ψ₂Sq
  given: (h : (4 : R) != 0)
  statement: W.Ψ₂Sq.natDegree = 3
  proof: natDegree_eq_of_le_of_coeff_ne_zero W.natDegree_Ψ₂Sq_le W.coeff_Ψ₂Sq_ne_zero h

中文:
引理 natDegree_Ψ₂Sq
  条件: (h : (4 : R) != 0)
  结论: W.Ψ₂Sq.natDegree = 3
  证明: natDegree_eq_of_le_of_coeff_ne_zero W.natDegree_Ψ₂Sq_le W.coeff_Ψ₂Sq_ne_zero h

Depends on / 依赖: W.coeff_, W.natDegree_, natDegree_eq_of_le_of_coeff_ne_zero
-/
lemma natDegree_Ψ₂Sq (h : (4 : R) != 0) : W.Ψ₂Sq.natDegree = 3 :=
natDegree_eq_of_le_of_coeff_ne_zero W.natDegree_Ψ₂Sq_le W.coeff_Ψ₂Sq_ne_zero h

/--
lemma `natDegree_Ψ₂Sq_pos` / 引理 `natDegree_Ψ₂Sq_pos`

English:
lemma natDegree_Ψ₂Sq_pos
  given: (h : (4 : R) != 0)
  statement: 0 < W.Ψ₂Sq.natDegree
  proof: W.natDegree_Ψ₂Sq h ▸ three_pos

@[simp]

中文:
引理 natDegree_Ψ₂Sq_pos
  条件: (h : (4 : R) != 0)
  结论: 0 < W.Ψ₂Sq.natDegree
  证明: W.natDegree_Ψ₂Sq h ▸ three_pos

@[simp]

Depends on / 依赖: W.natDegree_, three_pos
-/
lemma natDegree_Ψ₂Sq_pos (h : (4 : R) != 0) : 0 < W.Ψ₂Sq.natDegree :=
  W.natDegree_Ψ₂Sq h ▸ three_pos

@[simp]
/--
lemma `leadingCoeff_Ψ₂Sq` / 引理 `leadingCoeff_Ψ₂Sq`

English:
lemma leadingCoeff_Ψ₂Sq
  given: (h : (4 : R) != 0)
  statement: W.Ψ₂Sq.leadingCoeff = 4
  proof: by
  rw [leadingCoeff]; rw [W.natDegree_Ψ₂Sq h]; rw [coeff_Ψ₂Sq]

中文:
引理 leadingCoeff_Ψ₂Sq
  条件: (h : (4 : R) != 0)
  结论: W.Ψ₂Sq.leadingCoeff = 4
  证明: by
  rw [leadingCoeff]; rw [W.natDegree_Ψ₂Sq h]; rw [coeff_Ψ₂Sq]

Depends on / 依赖: W.natDegree_, leadingCoeff
-/
lemma leadingCoeff_Ψ₂Sq (h : (4 : R) != 0) : W.Ψ₂Sq.leadingCoeff = 4 := by
  rw [leadingCoeff]; rw [W.natDegree_Ψ₂Sq h]; rw [coeff_Ψ₂Sq]

/--
lemma `Ψ₂Sq_ne_zero` / 引理 `Ψ₂Sq_ne_zero`

English:
lemma Ψ₂Sq_ne_zero
  given: (h : (4 : R) != 0)
  statement: W.Ψ₂Sq != 0
  proof: ne_zero_of_natDegree_gt W.natDegree_Ψ₂Sq_pos h

中文:
引理 Ψ₂Sq_ne_zero
  条件: (h : (4 : R) != 0)
  结论: W.Ψ₂Sq != 0
  证明: ne_zero_of_natDegree_gt W.natDegree_Ψ₂Sq_pos h

Depends on / 依赖: W.natDegree_, ne_zero_of_natDegree_gt
-/
lemma Ψ₂Sq_ne_zero (h : (4 : R) != 0) : W.Ψ₂Sq != 0 :=
ne_zero_of_natDegree_gt W.natDegree_Ψ₂Sq_pos h

end Ψ₂Sq

section Ψ₃

/--
lemma `natDegree_Ψ₃_le` / 引理 `natDegree_Ψ₃_le`

English:
lemma natDegree_Ψ₃_le
  statement: W.Ψ₃.natDegree <= 4
  proof: by
  rw [Ψ₃]
  compute_degree

@[simp]

中文:
引理 natDegree_Ψ₃_le
  结论: W.Ψ₃.natDegree <= 4
  证明: by
  rw [Ψ₃]
  compute_degree

@[simp]

Depends on / 依赖: compute_degree
-/
lemma natDegree_Ψ₃_le : W.Ψ₃.natDegree <= 4 := by
  rw [Ψ₃]
  compute_degree

@[simp]
/--
lemma `coeff_Ψ₃` / 引理 `coeff_Ψ₃`

English:
lemma coeff_Ψ₃
  statement: W.Ψ₃.coeff 4 = 3
  proof: by
  rw [Ψ₃]
  compute_degree!

中文:
引理 coeff_Ψ₃
  结论: W.Ψ₃.coeff 4 = 3
  证明: by
  rw [Ψ₃]
  compute_degree!

Depends on / 依赖: compute_degree
-/
lemma coeff_Ψ₃ : W.Ψ₃.coeff 4 = 3 := by
  rw [Ψ₃]
  compute_degree!

/--
lemma `coeff_Ψ₃_ne_zero` / 引理 `coeff_Ψ₃_ne_zero`

English:
lemma coeff_Ψ₃_ne_zero
  given: (h : (3 : R) != 0)
  statement: W.Ψ₃.coeff 4 != 0
  proof: by
  rwa [coeff_Ψ₃]

@[simp]

中文:
引理 coeff_Ψ₃_ne_zero
  条件: (h : (3 : R) != 0)
  结论: W.Ψ₃.coeff 4 != 0
  证明: by
  rwa [coeff_Ψ₃]

@[simp]
-/
lemma coeff_Ψ₃_ne_zero (h : (3 : R) != 0) : W.Ψ₃.coeff 4 != 0 := by
  rwa [coeff_Ψ₃]

@[simp]
/--
lemma `natDegree_Ψ₃` / 引理 `natDegree_Ψ₃`

English:
lemma natDegree_Ψ₃
  given: (h : (3 : R) != 0)
  statement: W.Ψ₃.natDegree = 4
  proof: natDegree_eq_of_le_of_coeff_ne_zero W.natDegree_Ψ₃_le W.coeff_Ψ₃_ne_zero h

中文:
引理 natDegree_Ψ₃
  条件: (h : (3 : R) != 0)
  结论: W.Ψ₃.natDegree = 4
  证明: natDegree_eq_of_le_of_coeff_ne_zero W.natDegree_Ψ₃_le W.coeff_Ψ₃_ne_zero h

Depends on / 依赖: W.coeff_, W.natDegree_, natDegree_eq_of_le_of_coeff_ne_zero
-/
lemma natDegree_Ψ₃ (h : (3 : R) != 0) : W.Ψ₃.natDegree = 4 :=
natDegree_eq_of_le_of_coeff_ne_zero W.natDegree_Ψ₃_le W.coeff_Ψ₃_ne_zero h

/--
lemma `natDegree_Ψ₃_pos` / 引理 `natDegree_Ψ₃_pos`

English:
lemma natDegree_Ψ₃_pos
  given: (h : (3 : R) != 0)
  statement: 0 < W.Ψ₃.natDegree
  proof: W.natDegree_Ψ₃ h ▸ four_pos

@[simp]

中文:
引理 natDegree_Ψ₃_pos
  条件: (h : (3 : R) != 0)
  结论: 0 < W.Ψ₃.natDegree
  证明: W.natDegree_Ψ₃ h ▸ four_pos

@[simp]

Depends on / 依赖: W.natDegree_, four_pos
-/
lemma natDegree_Ψ₃_pos (h : (3 : R) != 0) : 0 < W.Ψ₃.natDegree :=
  W.natDegree_Ψ₃ h ▸ four_pos

@[simp]
/--
lemma `leadingCoeff_Ψ₃` / 引理 `leadingCoeff_Ψ₃`

English:
lemma leadingCoeff_Ψ₃
  given: (h : (3 : R) != 0)
  statement: W.Ψ₃.leadingCoeff = 3
  proof: by
  rw [leadingCoeff]; rw [W.natDegree_Ψ₃ h]; rw [coeff_Ψ₃]

中文:
引理 leadingCoeff_Ψ₃
  条件: (h : (3 : R) != 0)
  结论: W.Ψ₃.leadingCoeff = 3
  证明: by
  rw [leadingCoeff]; rw [W.natDegree_Ψ₃ h]; rw [coeff_Ψ₃]

Depends on / 依赖: W.natDegree_, leadingCoeff
-/
lemma leadingCoeff_Ψ₃ (h : (3 : R) != 0) : W.Ψ₃.leadingCoeff = 3 := by
  rw [leadingCoeff]; rw [W.natDegree_Ψ₃ h]; rw [coeff_Ψ₃]

/--
lemma `Ψ₃_ne_zero` / 引理 `Ψ₃_ne_zero`

English:
lemma Ψ₃_ne_zero
  given: (h : (3 : R) != 0)
  statement: W.Ψ₃ != 0
  proof: ne_zero_of_natDegree_gt W.natDegree_Ψ₃_pos h

中文:
引理 Ψ₃_ne_zero
  条件: (h : (3 : R) != 0)
  结论: W.Ψ₃ != 0
  证明: ne_zero_of_natDegree_gt W.natDegree_Ψ₃_pos h

Depends on / 依赖: W.natDegree_, ne_zero_of_natDegree_gt
-/
lemma Ψ₃_ne_zero (h : (3 : R) != 0) : W.Ψ₃ != 0 :=
ne_zero_of_natDegree_gt W.natDegree_Ψ₃_pos h

end Ψ₃

section preΨ₄

/--
lemma `natDegree_preΨ₄_le` / 引理 `natDegree_preΨ₄_le`

English:
lemma natDegree_preΨ₄_le
  statement: W.preΨ₄.natDegree <= 6
  proof: by
  rw [preΨ₄]
  compute_degree

@[simp]

中文:
引理 natDegree_preΨ₄_le
  结论: W.preΨ₄.natDegree <= 6
  证明: by
  rw [preΨ₄]
  compute_degree

@[simp]

Depends on / 依赖: compute_degree
-/
lemma natDegree_preΨ₄_le : W.preΨ₄.natDegree <= 6 := by
  rw [preΨ₄]
  compute_degree

@[simp]
/--
lemma `coeff_preΨ₄` / 引理 `coeff_preΨ₄`

English:
lemma coeff_preΨ₄
  statement: W.preΨ₄.coeff 6 = 2
  proof: by
  rw [preΨ₄]
  compute_degree!

中文:
引理 coeff_preΨ₄
  结论: W.preΨ₄.coeff 6 = 2
  证明: by
  rw [preΨ₄]
  compute_degree!

Depends on / 依赖: compute_degree
-/
lemma coeff_preΨ₄ : W.preΨ₄.coeff 6 = 2 := by
  rw [preΨ₄]
  compute_degree!

/--
lemma `coeff_preΨ₄_ne_zero` / 引理 `coeff_preΨ₄_ne_zero`

English:
lemma coeff_preΨ₄_ne_zero
  given: (h : (2 : R) != 0)
  statement: W.preΨ₄.coeff 6 != 0
  proof: by
  rwa [coeff_preΨ₄]

@[simp]

中文:
引理 coeff_preΨ₄_ne_zero
  条件: (h : (2 : R) != 0)
  结论: W.preΨ₄.coeff 6 != 0
  证明: by
  rwa [coeff_preΨ₄]

@[simp]
-/
lemma coeff_preΨ₄_ne_zero (h : (2 : R) != 0) : W.preΨ₄.coeff 6 != 0 := by
  rwa [coeff_preΨ₄]

@[simp]
/--
lemma `natDegree_preΨ₄` / 引理 `natDegree_preΨ₄`

English:
lemma natDegree_preΨ₄
  given: (h : (2 : R) != 0)
  statement: W.preΨ₄.natDegree = 6
  proof: natDegree_eq_of_le_of_coeff_ne_zero W.natDegree_preΨ₄_le W.coeff_preΨ₄_ne_zero h

中文:
引理 natDegree_preΨ₄
  条件: (h : (2 : R) != 0)
  结论: W.preΨ₄.natDegree = 6
  证明: natDegree_eq_of_le_of_coeff_ne_zero W.natDegree_preΨ₄_le W.coeff_preΨ₄_ne_zero h

Depends on / 依赖: W.coeff_pre, W.natDegree_pre, natDegree_eq_of_le_of_coeff_ne_zero
-/
lemma natDegree_preΨ₄ (h : (2 : R) != 0) : W.preΨ₄.natDegree = 6 :=
natDegree_eq_of_le_of_coeff_ne_zero W.natDegree_preΨ₄_le W.coeff_preΨ₄_ne_zero h

/--
lemma `natDegree_preΨ₄_pos` / 引理 `natDegree_preΨ₄_pos`

English:
lemma natDegree_preΨ₄_pos
  given: (h : (2 : R) != 0)
  statement: 0 < W.preΨ₄.natDegree
  proof: by
  linarith only [W.natDegree_preΨ₄ h]

@[simp]

中文:
引理 natDegree_preΨ₄_pos
  条件: (h : (2 : R) != 0)
  结论: 0 < W.preΨ₄.natDegree
  证明: by
  linarith only [W.natDegree_preΨ₄ h]

@[simp]

Depends on / 依赖: W.natDegree_pre
-/
lemma natDegree_preΨ₄_pos (h : (2 : R) != 0) : 0 < W.preΨ₄.natDegree := by
  linarith only [W.natDegree_preΨ₄ h]

@[simp]
/--
lemma `leadingCoeff_preΨ₄` / 引理 `leadingCoeff_preΨ₄`

English:
lemma leadingCoeff_preΨ₄
  given: (h : (2 : R) != 0)
  statement: W.preΨ₄.leadingCoeff = 2
  proof: by
  rw [leadingCoeff]; rw [W.natDegree_preΨ₄ h]; rw [coeff_preΨ₄]

中文:
引理 leadingCoeff_preΨ₄
  条件: (h : (2 : R) != 0)
  结论: W.preΨ₄.leadingCoeff = 2
  证明: by
  rw [leadingCoeff]; rw [W.natDegree_preΨ₄ h]; rw [coeff_preΨ₄]

Depends on / 依赖: W.natDegree_pre, leadingCoeff
-/
lemma leadingCoeff_preΨ₄ (h : (2 : R) != 0) : W.preΨ₄.leadingCoeff = 2 := by
  rw [leadingCoeff]; rw [W.natDegree_preΨ₄ h]; rw [coeff_preΨ₄]

/--
lemma `preΨ₄_ne_zero` / 引理 `preΨ₄_ne_zero`

English:
lemma preΨ₄_ne_zero
  given: (h : (2 : R) != 0)
  statement: W.preΨ₄ != 0
  proof: ne_zero_of_natDegree_gt W.natDegree_preΨ₄_pos h

中文:
引理 preΨ₄_ne_zero
  条件: (h : (2 : R) != 0)
  结论: W.preΨ₄ != 0
  证明: ne_zero_of_natDegree_gt W.natDegree_preΨ₄_pos h

Depends on / 依赖: W.natDegree_pre, ne_zero_of_natDegree_gt
-/
lemma preΨ₄_ne_zero (h : (2 : R) != 0) : W.preΨ₄ != 0 :=
ne_zero_of_natDegree_gt W.natDegree_preΨ₄_pos h

end preΨ₄

section preΨ'

/--
Definition of `expDegree` / `expDegree` 的定义

English:
definition expDegree
  signature: (n : Nat)
  body: (n ^ 2 - if Even n then 4 else 1) / 2

中文:
定义 expDegree
  签名: (n : 自然数)
  定义体: (n ^ 2 - if Even n then 4 else 1) / 2
-/
private def expDegree (n : Nat) : Nat :=
  (n ^ 2 - if Even n then 4 else 1) / 2

/--
lemma `expDegree_cast` / 引理 `expDegree_cast`

English:
lemma expDegree_cast
  given: {n : Nat} (hn : n != 0)
  proof: by
  rcases n.even_or_odd' with ⟨n, rfl | rfl⟩
  · rcases n with _ | n
    · contradiction
    push_cast [expDegree, show (2 * (n + 1)) ^ 2 = 2 * (2 * n * (n + 2)) + 4 by ring1, even_two_mul,
      Nat.add_sub_cancel, Nat.mul_div_cancel_left _ two_pos]
    ring1
  · push_cast [expDegree, show (2 * n + 1) ^ 2 = 2 * (2 * n * (n + 1)) + 1 by ring1,
      n.not_even_two_mul_add_one, Nat.add_sub_cancel, Nat.mul_div_cancel_left _ two_pos]
    ring1

中文:
引理 expDegree_cast
  条件: {n : 自然数} (hn : n != 0)
  证明: by
  rcases n.even_or_odd' with ⟨n, rfl | rfl⟩
  · rcases n with _ | n
    · contradiction
    push_cast [expDegree, show (2 * (n + 1)) ^ 2 = 2 * (2 * n * (n + 2)) + 4 by ring1, even_two_mul,
      Nat.add_sub_cancel, Nat.mul_div_cancel_left _ two_pos]
    ring1
  · push_cast [expDegree, show (2 * n + 1) ^ 2 = 2 * (2 * n * (n + 1)) + 1 by ring1,
      n.not_even_two_mul_add_one, Nat.add_sub_cancel, Nat.mul_div_cancel_left _ two_pos]
    ring1
-/
private lemma expDegree_cast {n : Nat} (hn : n != 0) :
    2 * (expDegree n : Int) = n ^ 2 - if Even n then 4 else 1 := by
  rcases n.even_or_odd' with ⟨n, rfl | rfl⟩
  · rcases n with _ | n
    · contradiction
    push_cast [expDegree, show (2 * (n + 1)) ^ 2 = 2 * (2 * n * (n + 2)) + 4 by ring1, even_two_mul,
      Nat.add_sub_cancel, Nat.mul_div_cancel_left _ two_pos]
    ring1
  · push_cast [expDegree, show (2 * n + 1) ^ 2 = 2 * (2 * n * (n + 1)) + 1 by ring1,
      n.not_even_two_mul_add_one, Nat.add_sub_cancel, Nat.mul_div_cancel_left _ two_pos]
    ring1

/--
lemma `expDegree_rec` / 引理 `expDegree_rec`

English:
lemma expDegree_rec
  given: (m : Nat)
  proof: by
  push_cast [← @Nat.cast_inj Int, ← mul_left_cancel_iff_of_pos (b := (expDegree _ : Int)) two_pos,
    mul_add, mul_left_comm (2 : Int)]
  repeat rw [expDegree_cast <| by lia]
  push_cast [Nat.even_add_one, ite_not, even_two_mul]
  constructor <;> constructor <;> split_ifs <;> ring1

中文:
引理 expDegree_rec
  条件: (m : 自然数)
  证明: by
  push_cast [← @Nat.cast_inj Int, ← mul_left_cancel_iff_of_pos (b := (expDegree _ : Int)) two_pos,
    mul_add, mul_left_comm (2 : Int)]
  repeat rw [expDegree_cast <| by lia]
  push_cast [Nat.even_add_one, ite_not, even_two_mul]
  constructor <;> constructor <;> split_ifs <;> ring1
-/
private lemma expDegree_rec (m : Nat) :
    (expDegree (2 * (m + 3)) = 2 * expDegree (m + 2) + expDegree (m + 3) + expDegree (m + 5) ∧
    expDegree (2 * (m + 3)) = expDegree (m + 1) + expDegree (m + 3) + 2 * expDegree (m + 4)) ∧
    (expDegree (2 * (m + 2) + 1) =
      expDegree (m + 4) + 3 * expDegree (m + 2) + (if Even m then 2 * 3 else 0) ∧
    expDegree (2 * (m + 2) + 1) =
      expDegree (m + 1) + 3 * expDegree (m + 3) + (if Even m then 0 else 2 * 3)) := by
  push_cast [← @Nat.cast_inj Int, ← mul_left_cancel_iff_of_pos (b := (expDegree _ : Int)) two_pos,
    mul_add, mul_left_comm (2 : Int)]
  repeat rw [expDegree_cast <| by lia]
  push_cast [Nat.even_add_one, ite_not, even_two_mul]
  constructor <;> constructor <;> split_ifs <;> ring1

/--
Definition of `expCoeff` / `expCoeff` 的定义

English:
definition expCoeff
  signature: (n : Nat)
  body: if Even n then n / 2 else n

中文:
定义 expCoeff
  签名: (n : 自然数)
  定义体: if Even n then n / 2 else n
-/
private def expCoeff (n : Nat) : Int :=
  if Even n then n / 2 else n

/--
lemma `expCoeff_cast` / 引理 `expCoeff_cast`

English:
lemma expCoeff_cast
  given: (n : Nat)
  statement: (expCoeff n : Rat) = if Even n then (n / 2 : Rat) else n
  proof: by
  rcases n.even_or_odd' with ⟨n, rfl | rfl⟩ <;> simp [expCoeff, n.not_even_two_mul_add_one]

中文:
引理 expCoeff_cast
  条件: (n : 自然数)
  结论: (expCoeff n : 有理数) = if Even n then (n / 2 : 有理数) else n
  证明: by
  rcases n.even_or_odd' with ⟨n, rfl | rfl⟩ <;> simp [expCoeff, n.not_even_two_mul_add_one]
-/
private lemma expCoeff_cast (n : Nat) : (expCoeff n : Rat) = if Even n then (n / 2 : Rat) else n := by
  rcases n.even_or_odd' with ⟨n, rfl | rfl⟩ <;> simp [expCoeff, n.not_even_two_mul_add_one]

/--
lemma `expCoeff_rec` / 引理 `expCoeff_rec`

English:
lemma expCoeff_rec
  given: (m : Nat)
  proof: by
  push_cast [← @Int.cast_inj Rat, expCoeff_cast, even_two_mul, m.not_even_two_mul_add_one,
    Nat.even_add_one, ite_not]
  constructor <;> split_ifs <;> ring1

中文:
引理 expCoeff_rec
  条件: (m : 自然数)
  证明: by
  push_cast [← @Int.cast_inj Rat, expCoeff_cast, even_two_mul, m.not_even_two_mul_add_one,
    Nat.even_add_one, ite_not]
  constructor <;> split_ifs <;> ring1
-/
private lemma expCoeff_rec (m : Nat) :
    (expCoeff (2 * (m + 3)) =
      expCoeff (m + 2) ^ 2 * expCoeff (m + 3) * expCoeff (m + 5) -
        expCoeff (m + 1) * expCoeff (m + 3) * expCoeff (m + 4) ^ 2) ∧
    (expCoeff (2 * (m + 2) + 1) =
      expCoeff (m + 4) * expCoeff (m + 2) ^ 3 * (if Even m then 4 ^ 2 else 1) -
        expCoeff (m + 1) * expCoeff (m + 3) ^ 3 * (if Even m then 1 else 4 ^ 2)) := by
  push_cast [← @Int.cast_inj Rat, expCoeff_cast, even_two_mul, m.not_even_two_mul_add_one,
    Nat.even_add_one, ite_not]
  constructor <;> split_ifs <;> ring1

/--
lemma `natDegree_coeff_preΨ'` / 引理 `natDegree_coeff_preΨ'`

English:
lemma natDegree_coeff_preΨ'
  given: (n : Nat)
  proof: by
  let dm {m n p q} : _ -> _ -> (p * q : R[X]).natDegree <= m + n := natDegree_mul_le_of_le
  let dp {m n p} : _ -> (p ^ n : R[X]).natDegree <= n * m := natDegree_pow_le_of_le n
  let cm {m n p q} : _ -> _ -> (p * q : R[X]).coeff (m + n) = _ := coeff_mul_add_eq_of_natDegree_le
  let cp {m n p} : _ -> (p ^ m : R[X]).coeff (m * n) = _ := coeff_pow_of_natDegree_le
  induction n using normEDSRec with
  | zero => simpa only [preΨ'_zero] using ⟨natDegree_zero.le, Int.cast_zero.symm⟩
  | one => simpa only [preΨ'_one] using ⟨natDegree_one.le, coeff_one_zero.trans Int.cast_one.symm⟩
  | two => simpa only [preΨ'_two] using ⟨natDegree_one.le, coeff_one_zero.trans Int.cast_one.symm⟩
  | three => simpa only [preΨ'_three] using ⟨W.natDegree_Ψ₃_le, W.coeff_Ψ₃ ▸ Int.cast_three.symm⟩
  | four => simpa only [preΨ'_four] using ⟨W.natDegree_preΨ₄_le, W.coeff_preΨ₄ ▸ Int.cast_two.symm⟩
  | even m h₁ h₂ h₃ h₄ h₅ =>
    constructor
    · nth_rw 1 [preΨ'_even, ← max_self <| expDegree _, (expDegree_rec m).1.1, (expDegree_rec m).1.2]
      exact natDegree_sub_le_of_le (dm (dm (dp h₂.1) h₃.1) h₅.1) (dm (dm h₁.1 h₃.1) (dp h₄.1))
    · nth_rw 1 [preΨ'_even, coeff_sub, (expDegree_rec m).1.1, cm (dm (dp h₂.1) h₃.1) h₅.1,
        cm (dp h₂.1) h₃.1, cp h₂.1, h₂.2, h₃.2, h₅.2, (expDegree_rec m).1.2,
        cm (dm h₁.1 h₃.1) (dp h₄.1), cm h₁.1 h₃.1, h₁.2, cp h₄.1, h₃.2, h₄.2, (expCoeff_rec m).1]
      norm_cast
  | odd m h₁ h₂ h₃ h₄ =>
    rw [preΨ'_odd]
    constructor
    · nth_rw 1 [← max_self <| expDegree _, (expDegree_rec m).2.1, (expDegree_rec m).2.2]
      refine natDegree_sub_le_of_le (dm (dm h₄.1 (dp h₂.1)) ?_) (dm (dm h₁.1 (dp h₃.1)) ?_) <;>
        split_ifs <;> simp only [natDegree_one.le, dp W.natDegree_Ψ₂Sq_le]
    · nth_rw 1 [coeff_sub, (expDegree_rec m).2.1, cm (dm h₄.1 (dp h₂.1)), cm h₄.1 (dp h₂.1),
        h₄.2, cp h₂.1, h₂.2, apply_ite₂ coeff, cp W.natDegree_Ψ₂Sq_le, coeff_Ψ₂Sq, coeff_one_zero,
        (expDegree_rec m).2.2, cm (dm h₁.1 (dp h₃.1)), cm h₁.1 (dp h₃.1), h₁.2, cp h₃.1, h₃.2,
        apply_ite₂ coeff, cp W.natDegree_Ψ₂Sq_le, coeff_one_zero, coeff_Ψ₂Sq, (expCoeff_rec m).2]
      · norm_cast
      all_goals split_ifs <;> simp only [natDegree_one.le, dp W.natDegree_Ψ₂Sq_le]

中文:
引理 natDegree_coeff_preΨ'
  条件: (n : 自然数)
  证明: by
  let dm {m n p q} : _ -> _ -> (p * q : R[X]).natDegree <= m + n := natDegree_mul_le_of_le
  let dp {m n p} : _ -> (p ^ n : R[X]).natDegree <= n * m := natDegree_pow_le_of_le n
  let cm {m n p q} : _ -> _ -> (p * q : R[X]).coeff (m + n) = _ := coeff_mul_add_eq_of_natDegree_le
  let cp {m n p} : _ -> (p ^ m : R[X]).coeff (m * n) = _ := coeff_pow_of_natDegree_le
  induction n using normEDSRec with
  | zero => simpa only [preΨ'_zero] using ⟨natDegree_zero.le, Int.cast_zero.symm⟩
  | one => simpa only [preΨ'_one] using ⟨natDegree_one.le, coeff_one_zero.trans Int.cast_one.symm⟩
  | two => simpa only [preΨ'_two] using ⟨natDegree_one.le, coeff_one_zero.trans Int.cast_one.symm⟩
  | three => simpa only [preΨ'_three] using ⟨W.natDegree_Ψ₃_le, W.coeff_Ψ₃ ▸ Int.cast_three.symm⟩
  | four => simpa only [preΨ'_four] using ⟨W.natDegree_preΨ₄_le, W.coeff_preΨ₄ ▸ Int.cast_two.symm⟩
  | even m h₁ h₂ h₃ h₄ h₅ =>
    constructor
    · nth_rw 1 [preΨ'_even, ← max_self <| expDegree _, (expDegree_rec m).1.1, (expDegree_rec m).1.2]
      exact natDegree_sub_le_of_le (dm (dm (dp h₂.1) h₃.1) h₅.1) (dm (dm h₁.1 h₃.1) (dp h₄.1))
    · nth_rw 1 [preΨ'_even, coeff_sub, (expDegree_rec m).1.1, cm (dm (dp h₂.1) h₃.1) h₅.1,
        cm (dp h₂.1) h₃.1, cp h₂.1, h₂.2, h₃.2, h₅.2, (expDegree_rec m).1.2,
        cm (dm h₁.1 h₃.1) (dp h₄.1), cm h₁.1 h₃.1, h₁.2, cp h₄.1, h₃.2, h₄.2, (expCoeff_rec m).1]
      norm_cast
  | odd m h₁ h₂ h₃ h₄ =>
    rw [preΨ'_odd]
    constructor
    · nth_rw 1 [← max_self <| expDegree _, (expDegree_rec m).2.1, (expDegree_rec m).2.2]
      refine natDegree_sub_le_of_le (dm (dm h₄.1 (dp h₂.1)) ?_) (dm (dm h₁.1 (dp h₃.1)) ?_) <;>
        split_ifs <;> simp only [natDegree_one.le, dp W.natDegree_Ψ₂Sq_le]
    · nth_rw 1 [coeff_sub, (expDegree_rec m).2.1, cm (dm h₄.1 (dp h₂.1)), cm h₄.1 (dp h₂.1),
        h₄.2, cp h₂.1, h₂.2, apply_ite₂ coeff, cp W.natDegree_Ψ₂Sq_le, coeff_Ψ₂Sq, coeff_one_zero,
        (expDegree_rec m).2.2, cm (dm h₁.1 (dp h₃.1)), cm h₁.1 (dp h₃.1), h₁.2, cp h₃.1, h₃.2,
        apply_ite₂ coeff, cp W.natDegree_Ψ₂Sq_le, coeff_one_zero, coeff_Ψ₂Sq, (expCoeff_rec m).2]
      · norm_cast
      all_goals split_ifs <;> simp only [natDegree_one.le, dp W.natDegree_Ψ₂Sq_le]
-/
private lemma natDegree_coeff_preΨ' (n : Nat) :
    (W.preΨ' n).natDegree <= expDegree n ∧ (W.preΨ' n).coeff (expDegree n) = expCoeff n := by
  let dm {m n p q} : _ -> _ -> (p * q : R[X]).natDegree <= m + n := natDegree_mul_le_of_le
  let dp {m n p} : _ -> (p ^ n : R[X]).natDegree <= n * m := natDegree_pow_le_of_le n
  let cm {m n p q} : _ -> _ -> (p * q : R[X]).coeff (m + n) = _ := coeff_mul_add_eq_of_natDegree_le
  let cp {m n p} : _ -> (p ^ m : R[X]).coeff (m * n) = _ := coeff_pow_of_natDegree_le
  induction n using normEDSRec with
  | zero => simpa only [preΨ'_zero] using ⟨natDegree_zero.le, Int.cast_zero.symm⟩
  | one => simpa only [preΨ'_one] using ⟨natDegree_one.le, coeff_one_zero.trans Int.cast_one.symm⟩
  | two => simpa only [preΨ'_two] using ⟨natDegree_one.le, coeff_one_zero.trans Int.cast_one.symm⟩
  | three => simpa only [preΨ'_three] using ⟨W.natDegree_Ψ₃_le, W.coeff_Ψ₃ ▸ Int.cast_three.symm⟩
  | four => simpa only [preΨ'_four] using ⟨W.natDegree_preΨ₄_le, W.coeff_preΨ₄ ▸ Int.cast_two.symm⟩
  | even m h₁ h₂ h₃ h₄ h₅ =>
    constructor
    · nth_rw 1 [preΨ'_even, ← max_self <| expDegree _, (expDegree_rec m).1.1, (expDegree_rec m).1.2]
      exact natDegree_sub_le_of_le (dm (dm (dp h₂.1) h₃.1) h₅.1) (dm (dm h₁.1 h₃.1) (dp h₄.1))
    · nth_rw 1 [preΨ'_even, coeff_sub, (expDegree_rec m).1.1, cm (dm (dp h₂.1) h₃.1) h₅.1,
        cm (dp h₂.1) h₃.1, cp h₂.1, h₂.2, h₃.2, h₅.2, (expDegree_rec m).1.2,
        cm (dm h₁.1 h₃.1) (dp h₄.1), cm h₁.1 h₃.1, h₁.2, cp h₄.1, h₃.2, h₄.2, (expCoeff_rec m).1]
      norm_cast
  | odd m h₁ h₂ h₃ h₄ =>
    rw [preΨ'_odd]
    constructor
    · nth_rw 1 [← max_self <| expDegree _, (expDegree_rec m).2.1, (expDegree_rec m).2.2]
      refine natDegree_sub_le_of_le (dm (dm h₄.1 (dp h₂.1)) ?_) (dm (dm h₁.1 (dp h₃.1)) ?_) <;>
        split_ifs <;> simp only [natDegree_one.le, dp W.natDegree_Ψ₂Sq_le]
    · nth_rw 1 [coeff_sub, (expDegree_rec m).2.1, cm (dm h₄.1 (dp h₂.1)), cm h₄.1 (dp h₂.1),
        h₄.2, cp h₂.1, h₂.2, apply_ite₂ coeff, cp W.natDegree_Ψ₂Sq_le, coeff_Ψ₂Sq, coeff_one_zero,
        (expDegree_rec m).2.2, cm (dm h₁.1 (dp h₃.1)), cm h₁.1 (dp h₃.1), h₁.2, cp h₃.1, h₃.2,
        apply_ite₂ coeff, cp W.natDegree_Ψ₂Sq_le, coeff_one_zero, coeff_Ψ₂Sq, (expCoeff_rec m).2]
      · norm_cast
      all_goals split_ifs <;> simp only [natDegree_one.le, dp W.natDegree_Ψ₂Sq_le]

/--
lemma `natDegree_preΨ'_le` / 引理 `natDegree_preΨ'_le`

English:
lemma natDegree_preΨ'_le
  given: (n : Nat)
  statement: (W.preΨ' n).natDegree <= (n ^ 2 - if Even n then 4 else 1) / 2
  proof: (W.natDegree_coeff_preΨ' n).left

@[simp]

中文:
引理 natDegree_preΨ'_le
  条件: (n : 自然数)
  结论: (W.preΨ' n).natDegree <= (n ^ 2 - if Even n then 4 else 1) / 2
  证明: (W.natDegree_coeff_preΨ' n).left

@[simp]

Depends on / 依赖: W.natDegree_coeff_pre
-/
lemma natDegree_preΨ'_le (n : Nat) : (W.preΨ' n).natDegree <= (n ^ 2 - if Even n then 4 else 1) / 2 :=
  (W.natDegree_coeff_preΨ' n).left

@[simp]
/--
lemma `coeff_preΨ'` / 引理 `coeff_preΨ'`

English:
lemma coeff_preΨ'
  given: (n : Nat)
  statement: (W.preΨ' n).coeff ((n ^ 2 - if Even n then 4 else 1) / 2) =
  proof: by
  convert! (W.natDegree_coeff_preΨ' n).right using 1
  rcases n.even_or_odd' with ⟨n, rfl | rfl⟩ <;> simp [expCoeff, n.not_even_two_mul_add_one]

中文:
引理 coeff_preΨ'
  条件: (n : 自然数)
  结论: (W.preΨ' n).coeff ((n ^ 2 - if Even n then 4 else 1) / 2) =
  证明: by
  convert! (W.natDegree_coeff_preΨ' n).right using 1
  rcases n.even_or_odd' with ⟨n, rfl | rfl⟩ <;> simp [expCoeff, n.not_even_two_mul_add_one]

Depends on / 依赖: W.natDegree_coeff_pre, convert, even_or_odd, expCoeff, n.even_or_odd, n.not_even_two_mul_add_one, not_even_two_mul_add_one
-/
lemma coeff_preΨ' (n : Nat) : (W.preΨ' n).coeff ((n ^ 2 - if Even n then 4 else 1) / 2) =
    if Even n then n / 2 else n := by
  convert! (W.natDegree_coeff_preΨ' n).right using 1
  rcases n.even_or_odd' with ⟨n, rfl | rfl⟩ <;> simp [expCoeff, n.not_even_two_mul_add_one]

/--
lemma `coeff_preΨ'_ne_zero` / 引理 `coeff_preΨ'_ne_zero`

English:
lemma coeff_preΨ'_ne_zero
  given: {n : Nat} (h : (n : R) != 0)
  proof: by
  rcases n.even_or_odd' with ⟨n, rfl | rfl⟩
  · rw [coeff_preΨ', if_pos <| even_two_mul n, n.mul_div_cancel_left two_pos]
exact right_ne_zero_of_mul by rwa [← Nat.cast_mul]
  · rwa [coeff_preΨ', if_neg n.not_even_two_mul_add_one]

@[simp]

中文:
引理 coeff_preΨ'_ne_zero
  条件: {n : 自然数} (h : (n : R) != 0)
  证明: by
  rcases n.even_or_odd' with ⟨n, rfl | rfl⟩
  · rw [coeff_preΨ', if_pos <| even_two_mul n, n.mul_div_cancel_left two_pos]
exact right_ne_zero_of_mul by rwa [← Nat.cast_mul]
  · rwa [coeff_preΨ', if_neg n.not_even_two_mul_add_one]

@[simp]
-/
lemma coeff_preΨ'_ne_zero {n : Nat} (h : (n : R) != 0) :
    (W.preΨ' n).coeff ((n ^ 2 - if Even n then 4 else 1) / 2) != 0 := by
  rcases n.even_or_odd' with ⟨n, rfl | rfl⟩
  · rw [coeff_preΨ', if_pos <| even_two_mul n, n.mul_div_cancel_left two_pos]
exact right_ne_zero_of_mul by rwa [← Nat.cast_mul]
  · rwa [coeff_preΨ', if_neg n.not_even_two_mul_add_one]

@[simp]
/--
lemma `natDegree_preΨ'` / 引理 `natDegree_preΨ'`

English:
lemma natDegree_preΨ'
  given: {n : Nat} (h : (n : R) != 0)
  proof: natDegree_eq_of_le_of_coeff_ne_zero (W.natDegree_preΨ'_le n) W.coeff_preΨ'_ne_zero h

中文:
引理 natDegree_preΨ'
  条件: {n : 自然数} (h : (n : R) != 0)
  证明: natDegree_eq_of_le_of_coeff_ne_zero (W.natDegree_preΨ'_le n) W.coeff_preΨ'_ne_zero h
-/
lemma natDegree_preΨ' {n : Nat} (h : (n : R) != 0) :
    (W.preΨ' n).natDegree = (n ^ 2 - if Even n then 4 else 1) / 2 :=
natDegree_eq_of_le_of_coeff_ne_zero (W.natDegree_preΨ'_le n) W.coeff_preΨ'_ne_zero h

/--
lemma `natDegree_preΨ'_pos` / 引理 `natDegree_preΨ'_pos`

English:
lemma natDegree_preΨ'_pos
  given: {n : Nat} (hn : 2 < n) (h : (n : R) != 0)
  statement: 0 < (W.preΨ' n).natDegree
  proof: by
  simp_rw [W.natDegree_preΨ' h, Nat.div_pos_iff, zero_lt_two, true_and]
split_ifs <;> exact Nat.AtLeastTwo.prop.trans Nat.sub_le_sub_right (Nat.pow_le_pow_left hn 2) _

@[simp]

中文:
引理 natDegree_preΨ'_pos
  条件: {n : 自然数} (hn : 2 < n) (h : (n : R) != 0)
  结论: 0 < (W.preΨ' n).natDegree
  证明: by
  simp_rw [W.natDegree_preΨ' h, Nat.div_pos_iff, zero_lt_two, true_and]
split_ifs <;> exact Nat.AtLeastTwo.prop.trans Nat.sub_le_sub_right (Nat.pow_le_pow_left hn 2) _

@[simp]
-/
lemma natDegree_preΨ'_pos {n : Nat} (hn : 2 < n) (h : (n : R) != 0) : 0 < (W.preΨ' n).natDegree := by
  simp_rw [W.natDegree_preΨ' h, Nat.div_pos_iff, zero_lt_two, true_and]
split_ifs <;> exact Nat.AtLeastTwo.prop.trans Nat.sub_le_sub_right (Nat.pow_le_pow_left hn 2) _

@[simp]
/--
lemma `leadingCoeff_preΨ'` / 引理 `leadingCoeff_preΨ'`

English:
lemma leadingCoeff_preΨ'
  given: {n : Nat} (h : (n : R) != 0)
  proof: by
  rw [leadingCoeff]; rw [W.natDegree_preΨ' h]; rw [coeff_preΨ']

中文:
引理 leadingCoeff_preΨ'
  条件: {n : 自然数} (h : (n : R) != 0)
  证明: by
  rw [leadingCoeff]; rw [W.natDegree_preΨ' h]; rw [coeff_preΨ']

Depends on / 依赖: W.natDegree_pre, leadingCoeff
-/
lemma leadingCoeff_preΨ' {n : Nat} (h : (n : R) != 0) :
    (W.preΨ' n).leadingCoeff = if Even n then n / 2 else n := by
  rw [leadingCoeff]; rw [W.natDegree_preΨ' h]; rw [coeff_preΨ']

/--
lemma `preΨ'_ne_zero` / 引理 `preΨ'_ne_zero`

English:
lemma preΨ'_ne_zero
  given: [Nontrivial R] {n : Nat} (h : (n : R) != 0)
  statement: W.preΨ' n != 0
  proof: by
  by_cases hn : 2 < n
· exact ne_zero_of_natDegree_gt W.natDegree_preΨ'_pos hn h
  · rcases n with _ | _ | _ <;> aesop

中文:
引理 preΨ'_ne_zero
  条件: [非平凡 R] {n : 自然数} (h : (n : R) != 0)
  结论: W.preΨ' n != 0
  证明: by
  by_cases hn : 2 < n
· exact ne_zero_of_natDegree_gt W.natDegree_preΨ'_pos hn h
  · rcases n with _ | _ | _ <;> aesop
-/
lemma preΨ'_ne_zero [Nontrivial R] {n : Nat} (h : (n : R) != 0) : W.preΨ' n != 0 := by
  by_cases hn : 2 < n
· exact ne_zero_of_natDegree_gt W.natDegree_preΨ'_pos hn h
  · rcases n with _ | _ | _ <;> aesop

end preΨ'

section preΨ

/--
lemma `natDegree_preΨ_le` / 引理 `natDegree_preΨ_le`

English:
lemma natDegree_preΨ_le
  given: (n : Int)
  statement: (W.preΨ n).natDegree <=
  proof: by
  induction n using Int.negInduction with
  | nat n => exact_mod_cast W.preΨ_ofNat n ▸ W.natDegree_preΨ'_le n
  | neg ih => simp_rw [preΨ_neg, natDegree_neg, Int.natAbs_neg, even_neg, ih]

@[simp]

中文:
引理 natDegree_preΨ_le
  条件: (n : 整数)
  结论: (W.preΨ n).natDegree <=
  证明: by
  induction n using Int.negInduction with
  | nat n => exact_mod_cast W.preΨ_ofNat n ▸ W.natDegree_preΨ'_le n
  | neg ih => simp_rw [preΨ_neg, natDegree_neg, Int.natAbs_neg, even_neg, ih]

@[simp]

Depends on / 依赖: Int.natAbs_neg, Int.negInduction, W.natDegree_pre, W.pre, even_neg, natAbs_neg, natDegree_neg, negInduction, simp_rw
-/
lemma natDegree_preΨ_le (n : Int) : (W.preΨ n).natDegree <=
    (n.natAbs ^ 2 - if Even n then 4 else 1) / 2 := by
  induction n using Int.negInduction with
  | nat n => exact_mod_cast W.preΨ_ofNat n ▸ W.natDegree_preΨ'_le n
  | neg ih => simp_rw [preΨ_neg, natDegree_neg, Int.natAbs_neg, even_neg, ih]

@[simp]
/--
lemma `coeff_preΨ` / 引理 `coeff_preΨ`

English:
lemma coeff_preΨ
  given: (n : Int)
  statement: (W.preΨ n).coeff ((n.natAbs ^ 2 - if Even n then 4 else 1) / 2) =
  proof: by
  induction n using Int.negInduction with
  | nat n => exact_mod_cast W.preΨ_ofNat n ▸ W.coeff_preΨ' n
  | neg ih n =>
    simp_rw [preΨ_neg, coeff_neg, Int.natAbs_neg, even_neg]
    rcases ih n, n.even_or_odd' with ⟨ih, ⟨n, rfl | rfl⟩⟩ <;>
      push_cast [even_two_mul, Int.not_even_two_mul_add_one, Int.neg_ediv_of_dvd ⟨n, rfl⟩] at * <;>
      rw [ih]

中文:
引理 coeff_preΨ
  条件: (n : 整数)
  结论: (W.preΨ n).coeff ((n.natAbs ^ 2 - if Even n then 4 else 1) / 2) =
  证明: by
  induction n using Int.negInduction with
  | nat n => exact_mod_cast W.preΨ_ofNat n ▸ W.coeff_preΨ' n
  | neg ih n =>
    simp_rw [preΨ_neg, coeff_neg, Int.natAbs_neg, even_neg]
    rcases ih n, n.even_or_odd' with ⟨ih, ⟨n, rfl | rfl⟩⟩ <;>
      push_cast [even_two_mul, Int.not_even_two_mul_add_one, Int.neg_ediv_of_dvd ⟨n, rfl⟩] at * <;>
      rw [ih]

Depends on / 依赖: Int.natAbs_neg, Int.negInduction, Int.neg_ediv_of_dvd, Int.not_even_two_mul_add_one, W.coeff_pre, W.pre, coeff_neg, even_neg, even_or_odd, even_two_mul, n.even_or_odd, natAbs_neg, negInduction, neg_ediv_of_dvd, not_even_two_mul_add_one, simp_rw
-/
lemma coeff_preΨ (n : Int) : (W.preΨ n).coeff ((n.natAbs ^ 2 - if Even n then 4 else 1) / 2) =
    if Even n then n / 2 else n := by
  induction n using Int.negInduction with
  | nat n => exact_mod_cast W.preΨ_ofNat n ▸ W.coeff_preΨ' n
  | neg ih n =>
    simp_rw [preΨ_neg, coeff_neg, Int.natAbs_neg, even_neg]
    rcases ih n, n.even_or_odd' with ⟨ih, ⟨n, rfl | rfl⟩⟩ <;>
      push_cast [even_two_mul, Int.not_even_two_mul_add_one, Int.neg_ediv_of_dvd ⟨n, rfl⟩] at * <;>
      rw [ih]

/--
lemma `coeff_preΨ_ne_zero` / 引理 `coeff_preΨ_ne_zero`

English:
lemma coeff_preΨ_ne_zero
  given: {n : Int} (h : (n : R) != 0)
  proof: by
  induction n using Int.negInduction with
  | nat n => simpa only [preΨ_ofNat, Int.even_coe_nat]
using! W.coeff_preΨ'_ne_zero by exact_mod_cast h
  | neg ih n => simpa only [preΨ_neg, coeff_neg, neg_ne_zero, Int.natAbs_neg, even_neg]
using! ih n neg_ne_zero.mp by exact_mod_cast h

@[simp]

中文:
引理 coeff_preΨ_ne_zero
  条件: {n : 整数} (h : (n : R) != 0)
  证明: by
  induction n using Int.negInduction with
  | nat n => simpa only [preΨ_ofNat, Int.even_coe_nat]
using! W.coeff_preΨ'_ne_zero by exact_mod_cast h
  | neg ih n => simpa only [preΨ_neg, coeff_neg, neg_ne_zero, Int.natAbs_neg, even_neg]
using! ih n neg_ne_zero.mp by exact_mod_cast h

@[simp]

Depends on / 依赖: Int.even_coe_nat, Int.natAbs_neg, Int.negInduction, W.coeff_pre, _ne_zero, coeff_neg, even_coe_nat, even_neg, natAbs_neg, negInduction, neg_ne_zero, neg_ne_zero.mp
-/
lemma coeff_preΨ_ne_zero {n : Int} (h : (n : R) != 0) :
    (W.preΨ n).coeff ((n.natAbs ^ 2 - if Even n then 4 else 1) / 2) != 0 := by
  induction n using Int.negInduction with
  | nat n => simpa only [preΨ_ofNat, Int.even_coe_nat]
using! W.coeff_preΨ'_ne_zero by exact_mod_cast h
  | neg ih n => simpa only [preΨ_neg, coeff_neg, neg_ne_zero, Int.natAbs_neg, even_neg]
using! ih n neg_ne_zero.mp by exact_mod_cast h

@[simp]
/--
lemma `natDegree_preΨ` / 引理 `natDegree_preΨ`

English:
lemma natDegree_preΨ
  given: {n : Int} (h : (n : R) != 0)
  proof: natDegree_eq_of_le_of_coeff_ne_zero (W.natDegree_preΨ_le n) W.coeff_preΨ_ne_zero h

中文:
引理 natDegree_preΨ
  条件: {n : 整数} (h : (n : R) != 0)
  证明: natDegree_eq_of_le_of_coeff_ne_zero (W.natDegree_preΨ_le n) W.coeff_preΨ_ne_zero h

Depends on / 依赖: W.coeff_pre, W.natDegree_pre, natDegree_eq_of_le_of_coeff_ne_zero
-/
lemma natDegree_preΨ {n : Int} (h : (n : R) != 0) :
    (W.preΨ n).natDegree = (n.natAbs ^ 2 - if Even n then 4 else 1) / 2 :=
natDegree_eq_of_le_of_coeff_ne_zero (W.natDegree_preΨ_le n) W.coeff_preΨ_ne_zero h

/--
lemma `natDegree_preΨ_pos` / 引理 `natDegree_preΨ_pos`

English:
lemma natDegree_preΨ_pos
  given: {n : Int} (hn : 2 < n.natAbs) (h : (n : R) != 0)
  proof: by
  induction n using Int.negInduction with
| nat n => simpa only [preΨ_ofNat] using! W.natDegree_preΨ'_pos hn by exact_mod_cast h
  | neg ih n => simpa only [preΨ_neg, natDegree_neg]
using! ih n (by rwa [← Int.natAbs_neg]) neg_ne_zero.mp by exact_mod_cast h

@[simp]

中文:
引理 natDegree_preΨ_pos
  条件: {n : 整数} (hn : 2 < n.natAbs) (h : (n : R) != 0)
  证明: by
  induction n using Int.negInduction with
| nat n => simpa only [preΨ_ofNat] using! W.natDegree_preΨ'_pos hn by exact_mod_cast h
  | neg ih n => simpa only [preΨ_neg, natDegree_neg]
using! ih n (by rwa [← Int.natAbs_neg]) neg_ne_zero.mp by exact_mod_cast h

@[simp]

Depends on / 依赖: Int.natAbs_neg, Int.negInduction, W.natDegree_pre, _pos, natAbs_neg, natDegree_neg, negInduction, neg_ne_zero, neg_ne_zero.mp
-/
lemma natDegree_preΨ_pos {n : Int} (hn : 2 < n.natAbs) (h : (n : R) != 0) :
    0 < (W.preΨ n).natDegree := by
  induction n using Int.negInduction with
| nat n => simpa only [preΨ_ofNat] using! W.natDegree_preΨ'_pos hn by exact_mod_cast h
  | neg ih n => simpa only [preΨ_neg, natDegree_neg]
using! ih n (by rwa [← Int.natAbs_neg]) neg_ne_zero.mp by exact_mod_cast h

@[simp]
/--
lemma `leadingCoeff_preΨ` / 引理 `leadingCoeff_preΨ`

English:
lemma leadingCoeff_preΨ
  given: {n : Int} (h : (n : R) != 0)
  proof: by
  rw [leadingCoeff]; rw [W.natDegree_preΨ h]; rw [coeff_preΨ]

中文:
引理 leadingCoeff_preΨ
  条件: {n : 整数} (h : (n : R) != 0)
  证明: by
  rw [leadingCoeff]; rw [W.natDegree_preΨ h]; rw [coeff_preΨ]

Depends on / 依赖: W.natDegree_pre, leadingCoeff
-/
lemma leadingCoeff_preΨ {n : Int} (h : (n : R) != 0) :
    (W.preΨ n).leadingCoeff = if Even n then n / 2 else n := by
  rw [leadingCoeff]; rw [W.natDegree_preΨ h]; rw [coeff_preΨ]

/--
lemma `preΨ_ne_zero` / 引理 `preΨ_ne_zero`

English:
lemma preΨ_ne_zero
  given: [Nontrivial R] {n : Int} (h : (n : R) != 0)
  statement: W.preΨ n != 0
  proof: by
  induction n using Int.negInduction with
| nat n => simpa only [preΨ_ofNat] using W.preΨ'_ne_zero by exact_mod_cast h
  | neg ih n => simpa only [preΨ_neg, neg_ne_zero]
using ih n neg_ne_zero.mp by exact_mod_cast h

中文:
引理 preΨ_ne_zero
  条件: [非平凡 R] {n : 整数} (h : (n : R) != 0)
  结论: W.preΨ n != 0
  证明: by
  induction n using Int.negInduction with
| nat n => simpa only [preΨ_ofNat] using W.preΨ'_ne_zero by exact_mod_cast h
  | neg ih n => simpa only [preΨ_neg, neg_ne_zero]
using ih n neg_ne_zero.mp by exact_mod_cast h

Depends on / 依赖: Int.negInduction, W.pre, _ne_zero, negInduction, neg_ne_zero, neg_ne_zero.mp
-/
lemma preΨ_ne_zero [Nontrivial R] {n : Int} (h : (n : R) != 0) : W.preΨ n != 0 := by
  induction n using Int.negInduction with
| nat n => simpa only [preΨ_ofNat] using W.preΨ'_ne_zero by exact_mod_cast h
  | neg ih n => simpa only [preΨ_neg, neg_ne_zero]
using ih n neg_ne_zero.mp by exact_mod_cast h

end preΨ

section ΨSq

/--
lemma `natDegree_coeff_ΨSq_ofNat` / 引理 `natDegree_coeff_ΨSq_ofNat`

English:
lemma natDegree_coeff_ΨSq_ofNat
  given: (n : Nat)
  proof: by
  let dp {m n p} : _ -> (p ^ n : R[X]).natDegree <= n * m := natDegree_pow_le_of_le n
  let h {n} := W.natDegree_coeff_preΨ' n
  rcases n with _ | n
  · simp
  have hd : (n + 1) ^ 2 - 1 = 2 * expDegree (n + 1) + if Even (n + 1) then 3 else 0 := by
    push_cast [← @Nat.cast_inj Int, add_sq, expDegree_cast n.succ_ne_zero]
    split_ifs <;> ring1
  have hc : (n + 1 : Nat) ^ 2 = expCoeff (n + 1) ^ 2 * if Even (n + 1) then 4 else 1 := by
    push_cast [← @Int.cast_inj Rat, expCoeff_cast]
    split_ifs <;> ring1
  rw [ΨSq_ofNat]; rw [hd]
  constructor
  · refine natDegree_mul_le_of_le (dp h.1) ?_
    split_ifs <;> simp only [natDegree_one.le, W.natDegree_Ψ₂Sq_le]
  · rw [coeff_mul_add_eq_of_natDegree_le (dp h.1), coeff_pow_of_natDegree_le h.1, h.2,
      apply_ite₂ coeff, coeff_Ψ₂Sq, coeff_one_zero, hc]
    · norm_cast
    split_ifs <;> simp only [natDegree_one.le, W.natDegree_Ψ₂Sq_le]

中文:
引理 natDegree_coeff_ΨSq_of自然数
  条件: (n : 自然数)
  证明: by
  let dp {m n p} : _ -> (p ^ n : R[X]).natDegree <= n * m := natDegree_pow_le_of_le n
  let h {n} := W.natDegree_coeff_preΨ' n
  rcases n with _ | n
  · simp
  have hd : (n + 1) ^ 2 - 1 = 2 * expDegree (n + 1) + if Even (n + 1) then 3 else 0 := by
    push_cast [← @Nat.cast_inj Int, add_sq, expDegree_cast n.succ_ne_zero]
    split_ifs <;> ring1
  have hc : (n + 1 : Nat) ^ 2 = expCoeff (n + 1) ^ 2 * if Even (n + 1) then 4 else 1 := by
    push_cast [← @Int.cast_inj Rat, expCoeff_cast]
    split_ifs <;> ring1
  rw [ΨSq_ofNat]; rw [hd]
  constructor
  · refine natDegree_mul_le_of_le (dp h.1) ?_
    split_ifs <;> simp only [natDegree_one.le, W.natDegree_Ψ₂Sq_le]
  · rw [coeff_mul_add_eq_of_natDegree_le (dp h.1), coeff_pow_of_natDegree_le h.1, h.2,
      apply_ite₂ coeff, coeff_Ψ₂Sq, coeff_one_zero, hc]
    · norm_cast
    split_ifs <;> simp only [natDegree_one.le, W.natDegree_Ψ₂Sq_le]
-/
private lemma natDegree_coeff_ΨSq_ofNat (n : Nat) :
    (W.ΨSq n).natDegree <= n ^ 2 - 1 ∧ (W.ΨSq n).coeff (n ^ 2 - 1) = (n ^ 2 : Int) := by
  let dp {m n p} : _ -> (p ^ n : R[X]).natDegree <= n * m := natDegree_pow_le_of_le n
  let h {n} := W.natDegree_coeff_preΨ' n
  rcases n with _ | n
  · simp
  have hd : (n + 1) ^ 2 - 1 = 2 * expDegree (n + 1) + if Even (n + 1) then 3 else 0 := by
    push_cast [← @Nat.cast_inj Int, add_sq, expDegree_cast n.succ_ne_zero]
    split_ifs <;> ring1
  have hc : (n + 1 : Nat) ^ 2 = expCoeff (n + 1) ^ 2 * if Even (n + 1) then 4 else 1 := by
    push_cast [← @Int.cast_inj Rat, expCoeff_cast]
    split_ifs <;> ring1
  rw [ΨSq_ofNat]; rw [hd]
  constructor
  · refine natDegree_mul_le_of_le (dp h.1) ?_
    split_ifs <;> simp only [natDegree_one.le, W.natDegree_Ψ₂Sq_le]
  · rw [coeff_mul_add_eq_of_natDegree_le (dp h.1), coeff_pow_of_natDegree_le h.1, h.2,
      apply_ite₂ coeff, coeff_Ψ₂Sq, coeff_one_zero, hc]
    · norm_cast
    split_ifs <;> simp only [natDegree_one.le, W.natDegree_Ψ₂Sq_le]

/--
lemma `natDegree_ΨSq_le` / 引理 `natDegree_ΨSq_le`

English:
lemma natDegree_ΨSq_le
  given: (n : Int)
  statement: (W.ΨSq n).natDegree <= n.natAbs ^ 2 - 1
  proof: by
  induction n using Int.negInduction with
  | nat n => exact (W.natDegree_coeff_ΨSq_ofNat n).left
  | neg ih => simp_rw [ΨSq_neg, Int.natAbs_neg, ih]

@[simp]

中文:
引理 natDegree_ΨSq_le
  条件: (n : 整数)
  结论: (W.ΨSq n).natDegree <= n.natAbs ^ 2 - 1
  证明: by
  induction n using Int.negInduction with
  | nat n => exact (W.natDegree_coeff_ΨSq_ofNat n).left
  | neg ih => simp_rw [ΨSq_neg, Int.natAbs_neg, ih]

@[simp]

Depends on / 依赖: Int.natAbs_neg, Int.negInduction, W.natDegree_coeff_, natAbs_neg, negInduction, simp_rw
-/
lemma natDegree_ΨSq_le (n : Int) : (W.ΨSq n).natDegree <= n.natAbs ^ 2 - 1 := by
  induction n using Int.negInduction with
  | nat n => exact (W.natDegree_coeff_ΨSq_ofNat n).left
  | neg ih => simp_rw [ΨSq_neg, Int.natAbs_neg, ih]

@[simp]
/--
lemma `coeff_ΨSq` / 引理 `coeff_ΨSq`

English:
lemma coeff_ΨSq
  given: (n : Int)
  statement: (W.ΨSq n).coeff (n.natAbs ^ 2 - 1) = n ^ 2
  proof: by
  induction n using Int.negInduction with
  | nat n => exact_mod_cast (W.natDegree_coeff_ΨSq_ofNat n).right
  | neg ih => rw [ΨSq_neg, Int.natAbs_neg, ← Int.cast_pow, neg_sq, Int.cast_pow, ih]

中文:
引理 coeff_ΨSq
  条件: (n : 整数)
  结论: (W.ΨSq n).coeff (n.natAbs ^ 2 - 1) = n ^ 2
  证明: by
  induction n using Int.negInduction with
  | nat n => exact_mod_cast (W.natDegree_coeff_ΨSq_ofNat n).right
  | neg ih => rw [ΨSq_neg, Int.natAbs_neg, ← Int.cast_pow, neg_sq, Int.cast_pow, ih]

Depends on / 依赖: Int.cast_pow, Int.natAbs_neg, Int.negInduction, W.natDegree_coeff_, cast_pow, natAbs_neg, negInduction, neg_sq
-/
lemma coeff_ΨSq (n : Int) : (W.ΨSq n).coeff (n.natAbs ^ 2 - 1) = n ^ 2 := by
  induction n using Int.negInduction with
  | nat n => exact_mod_cast (W.natDegree_coeff_ΨSq_ofNat n).right
  | neg ih => rw [ΨSq_neg, Int.natAbs_neg, ← Int.cast_pow, neg_sq, Int.cast_pow, ih]

/--
lemma `coeff_ΨSq_ne_zero` / 引理 `coeff_ΨSq_ne_zero`

English:
lemma coeff_ΨSq_ne_zero
  given: [NoZeroDivisors R] {n : Int} (h : (n : R) != 0)
  proof: by
  simpa

@[simp]

中文:
引理 coeff_ΨSq_ne_zero
  条件: [无零因子 R] {n : 整数} (h : (n : R) != 0)
  证明: by
  simpa

@[simp]
-/
lemma coeff_ΨSq_ne_zero [NoZeroDivisors R] {n : Int} (h : (n : R) != 0) :
    (W.ΨSq n).coeff (n.natAbs ^ 2 - 1) != 0 := by
  simpa

@[simp]
/--
lemma `natDegree_ΨSq` / 引理 `natDegree_ΨSq`

English:
lemma natDegree_ΨSq
  given: [NoZeroDivisors R] {n : Int} (h : (n : R) != 0)
  proof: natDegree_eq_of_le_of_coeff_ne_zero (W.natDegree_ΨSq_le n) W.coeff_ΨSq_ne_zero h

中文:
引理 natDegree_ΨSq
  条件: [无零因子 R] {n : 整数} (h : (n : R) != 0)
  证明: natDegree_eq_of_le_of_coeff_ne_zero (W.natDegree_ΨSq_le n) W.coeff_ΨSq_ne_zero h

Depends on / 依赖: W.coeff_, W.natDegree_, natDegree_eq_of_le_of_coeff_ne_zero
-/
lemma natDegree_ΨSq [NoZeroDivisors R] {n : Int} (h : (n : R) != 0) :
    (W.ΨSq n).natDegree = n.natAbs ^ 2 - 1 :=
natDegree_eq_of_le_of_coeff_ne_zero (W.natDegree_ΨSq_le n) W.coeff_ΨSq_ne_zero h

/--
lemma `natDegree_ΨSq_pos` / 引理 `natDegree_ΨSq_pos`

English:
lemma natDegree_ΨSq_pos
  given: [NoZeroDivisors R] {n : Int} (hn : 1 < n.natAbs) (h : (n : R) != 0)
  proof: by
  simpa [W.natDegree_ΨSq h]

@[simp]

中文:
引理 natDegree_ΨSq_pos
  条件: [无零因子 R] {n : 整数} (hn : 1 < n.natAbs) (h : (n : R) != 0)
  证明: by
  simpa [W.natDegree_ΨSq h]

@[simp]

Depends on / 依赖: W.natDegree_
-/
lemma natDegree_ΨSq_pos [NoZeroDivisors R] {n : Int} (hn : 1 < n.natAbs) (h : (n : R) != 0) :
    0 < (W.ΨSq n).natDegree := by
  simpa [W.natDegree_ΨSq h]

@[simp]
/--
lemma `leadingCoeff_ΨSq` / 引理 `leadingCoeff_ΨSq`

English:
lemma leadingCoeff_ΨSq
  given: [NoZeroDivisors R] {n : Int} (h : (n : R) != 0)
  proof: by
  rw [leadingCoeff]; rw [W.natDegree_ΨSq h]; rw [coeff_ΨSq]

中文:
引理 leadingCoeff_ΨSq
  条件: [无零因子 R] {n : 整数} (h : (n : R) != 0)
  证明: by
  rw [leadingCoeff]; rw [W.natDegree_ΨSq h]; rw [coeff_ΨSq]

Depends on / 依赖: W.natDegree_, leadingCoeff
-/
lemma leadingCoeff_ΨSq [NoZeroDivisors R] {n : Int} (h : (n : R) != 0) :
    (W.ΨSq n).leadingCoeff = n ^ 2 := by
  rw [leadingCoeff]; rw [W.natDegree_ΨSq h]; rw [coeff_ΨSq]

/--
lemma `ΨSq_ne_zero` / 引理 `ΨSq_ne_zero`

English:
lemma ΨSq_ne_zero
  given: [NoZeroDivisors R] {n : Int} (h : (n : R) != 0)
  statement: W.ΨSq n != 0
  proof: by
  by_cases hn : 1 < n.natAbs
· exact ne_zero_of_natDegree_gt W.natDegree_ΨSq_pos hn h
  · rcases hm : n.natAbs with _ | m
    · push_cast [Int.natAbs_eq_zero.mp hm, ne_self_iff_false] at h
    · rcases Int.natAbs_eq_iff.mp hm with rfl | rfl <;>
        rw [hm]; rw [Nat.lt_add_left_iff_pos]; rw [Nat.not_lt_eq]; rw [Nat.le_zero] at hn <;>
        push_cast [hn, ΨSq_neg, ΨSq_one] <;>
exact fun h' => h C_injective by push_cast [hn, C_neg, C_1, h', neg_zero, C_0]; rfl

中文:
引理 ΨSq_ne_zero
  条件: [无零因子 R] {n : 整数} (h : (n : R) != 0)
  结论: W.ΨSq n != 0
  证明: by
  by_cases hn : 1 < n.natAbs
· exact ne_zero_of_natDegree_gt W.natDegree_ΨSq_pos hn h
  · rcases hm : n.natAbs with _ | m
    · push_cast [Int.natAbs_eq_zero.mp hm, ne_self_iff_false] at h
    · rcases Int.natAbs_eq_iff.mp hm with rfl | rfl <;>
        rw [hm]; rw [Nat.lt_add_left_iff_pos]; rw [Nat.not_lt_eq]; rw [Nat.le_zero] at hn <;>
        push_cast [hn, ΨSq_neg, ΨSq_one] <;>
exact fun h' => h C_injective by push_cast [hn, C_neg, C_1, h', neg_zero, C_0]; rfl

Depends on / 依赖: C_injective, C_neg, Int.natAbs_eq_iff.mp, Int.natAbs_eq_zero.mp, Nat.le_zero, Nat.lt_add_left_iff_pos, Nat.not_lt_eq, W.natDegree_, le_zero, lt_add_left_iff_pos, n.natAbs, natAbs, natAbs_eq_iff, natAbs_eq_zero, ne_self_iff_false, ne_zero_of_natDegree_gt, neg_zero, not_lt_eq
-/
lemma ΨSq_ne_zero [NoZeroDivisors R] {n : Int} (h : (n : R) != 0) : W.ΨSq n != 0 := by
  by_cases hn : 1 < n.natAbs
· exact ne_zero_of_natDegree_gt W.natDegree_ΨSq_pos hn h
  · rcases hm : n.natAbs with _ | m
    · push_cast [Int.natAbs_eq_zero.mp hm, ne_self_iff_false] at h
    · rcases Int.natAbs_eq_iff.mp hm with rfl | rfl <;>
        rw [hm]; rw [Nat.lt_add_left_iff_pos]; rw [Nat.not_lt_eq]; rw [Nat.le_zero] at hn <;>
        push_cast [hn, ΨSq_neg, ΨSq_one] <;>
exact fun h' => h C_injective by push_cast [hn, C_neg, C_1, h', neg_zero, C_0]; rfl

end ΨSq

section Φ

/--
lemma `natDegree_coeff_Φ_ofNat` / 引理 `natDegree_coeff_Φ_ofNat`

English:
lemma natDegree_coeff_Φ_ofNat
  given: (n : Nat)
  proof: by
  let dm {m n p q} : _ -> _ -> (p * q : R[X]).natDegree <= m + n := natDegree_mul_le_of_le
  let dp {m n p} : _ -> (p ^ n : R[X]).natDegree <= n * m := natDegree_pow_le_of_le n
  let cm {m n p q} : _ -> _ -> (p * q : R[X]).coeff (m + n) = _ := coeff_mul_add_eq_of_natDegree_le
  let h {n} := W.natDegree_coeff_preΨ' n
  rcases n with _ | _ | n
  iterate 2 simp [natDegree_X_le]
  have hd : (n + 1 + 1) ^ 2 = 1 + 2 * expDegree (n + 2) + if Even (n + 1) then 0 else 3 := by
    push_cast [← @Nat.cast_inj Int, expDegree_cast (n + 1).succ_ne_zero, Nat.even_add_one, ite_not]
    split_ifs <;> ring1
  have hd' : (n + 1 + 1) ^ 2 =
      expDegree (n + 3) + expDegree (n + 1) + if Even (n + 1) then 3 else 0 := by
    push_cast [← @Nat.cast_inj Int, ← mul_left_cancel_iff_of_pos (b := (_ ^ 2 : Int)) two_pos, mul_add,
      expDegree_cast (n + 2).succ_ne_zero, expDegree_cast n.succ_ne_zero, Nat.even_add_one, ite_not]
    split_ifs <;> ring1
  have hc : (1 : Int) = 1 * expCoeff (n + 2) ^ 2 * (if Even (n + 1) then 1 else 4) -
      expCoeff (n + 3) * expCoeff (n + 1) * (if Even (n + 1) then 4 else 1) := by
    push_cast [← @Int.cast_inj Rat, expCoeff_cast, Nat.even_add_one, ite_not]
    split_ifs <;> ring1
  rw [Nat.cast_add]; rw [Nat.cast_one]; rw [Φ_ofNat]
  constructor
  · nth_rw 1 [← max_self <| (_ + _) ^ 2, hd, hd']
    refine natDegree_sub_le_of_le (dm (dm natDegree_X_le (dp h.1)) ?_) (dm (dm h.1 h.1) ?_) <;>
      split_ifs <;> simp only [natDegree_one.le, W.natDegree_Ψ₂Sq_le]
  · nth_rw 1 [coeff_sub, hd, hd', cm (dm natDegree_X_le (dp h.1)), cm natDegree_X_le (dp h.1),
      coeff_X_one, coeff_pow_of_natDegree_le h.1, h.2, apply_ite₂ coeff, coeff_one_zero, coeff_Ψ₂Sq,
      cm (dm h.1 h.1), cm h.1 h.1, h.2, h.2, apply_ite₂ coeff, coeff_one_zero, coeff_Ψ₂Sq]
    conv_rhs => rw [← Int.cast_one, hc]
    · norm_cast
    all_goals split_ifs <;> simp only [natDegree_one.le, W.natDegree_Ψ₂Sq_le]

中文:
引理 natDegree_coeff_Φ_of自然数
  条件: (n : 自然数)
  证明: by
  let dm {m n p q} : _ -> _ -> (p * q : R[X]).natDegree <= m + n := natDegree_mul_le_of_le
  let dp {m n p} : _ -> (p ^ n : R[X]).natDegree <= n * m := natDegree_pow_le_of_le n
  let cm {m n p q} : _ -> _ -> (p * q : R[X]).coeff (m + n) = _ := coeff_mul_add_eq_of_natDegree_le
  let h {n} := W.natDegree_coeff_preΨ' n
  rcases n with _ | _ | n
  iterate 2 simp [natDegree_X_le]
  have hd : (n + 1 + 1) ^ 2 = 1 + 2 * expDegree (n + 2) + if Even (n + 1) then 0 else 3 := by
    push_cast [← @Nat.cast_inj Int, expDegree_cast (n + 1).succ_ne_zero, Nat.even_add_one, ite_not]
    split_ifs <;> ring1
  have hd' : (n + 1 + 1) ^ 2 =
      expDegree (n + 3) + expDegree (n + 1) + if Even (n + 1) then 3 else 0 := by
    push_cast [← @Nat.cast_inj Int, ← mul_left_cancel_iff_of_pos (b := (_ ^ 2 : Int)) two_pos, mul_add,
      expDegree_cast (n + 2).succ_ne_zero, expDegree_cast n.succ_ne_zero, Nat.even_add_one, ite_not]
    split_ifs <;> ring1
  have hc : (1 : Int) = 1 * expCoeff (n + 2) ^ 2 * (if Even (n + 1) then 1 else 4) -
      expCoeff (n + 3) * expCoeff (n + 1) * (if Even (n + 1) then 4 else 1) := by
    push_cast [← @Int.cast_inj Rat, expCoeff_cast, Nat.even_add_one, ite_not]
    split_ifs <;> ring1
  rw [Nat.cast_add]; rw [Nat.cast_one]; rw [Φ_ofNat]
  constructor
  · nth_rw 1 [← max_self <| (_ + _) ^ 2, hd, hd']
    refine natDegree_sub_le_of_le (dm (dm natDegree_X_le (dp h.1)) ?_) (dm (dm h.1 h.1) ?_) <;>
      split_ifs <;> simp only [natDegree_one.le, W.natDegree_Ψ₂Sq_le]
  · nth_rw 1 [coeff_sub, hd, hd', cm (dm natDegree_X_le (dp h.1)), cm natDegree_X_le (dp h.1),
      coeff_X_one, coeff_pow_of_natDegree_le h.1, h.2, apply_ite₂ coeff, coeff_one_zero, coeff_Ψ₂Sq,
      cm (dm h.1 h.1), cm h.1 h.1, h.2, h.2, apply_ite₂ coeff, coeff_one_zero, coeff_Ψ₂Sq]
    conv_rhs => rw [← Int.cast_one, hc]
    · norm_cast
    all_goals split_ifs <;> simp only [natDegree_one.le, W.natDegree_Ψ₂Sq_le]
-/
private lemma natDegree_coeff_Φ_ofNat (n : Nat) :
    (W.Φ n).natDegree <= n ^ 2 ∧ (W.Φ n).coeff (n ^ 2) = 1 := by
  let dm {m n p q} : _ -> _ -> (p * q : R[X]).natDegree <= m + n := natDegree_mul_le_of_le
  let dp {m n p} : _ -> (p ^ n : R[X]).natDegree <= n * m := natDegree_pow_le_of_le n
  let cm {m n p q} : _ -> _ -> (p * q : R[X]).coeff (m + n) = _ := coeff_mul_add_eq_of_natDegree_le
  let h {n} := W.natDegree_coeff_preΨ' n
  rcases n with _ | _ | n
  iterate 2 simp [natDegree_X_le]
  have hd : (n + 1 + 1) ^ 2 = 1 + 2 * expDegree (n + 2) + if Even (n + 1) then 0 else 3 := by
    push_cast [← @Nat.cast_inj Int, expDegree_cast (n + 1).succ_ne_zero, Nat.even_add_one, ite_not]
    split_ifs <;> ring1
  have hd' : (n + 1 + 1) ^ 2 =
      expDegree (n + 3) + expDegree (n + 1) + if Even (n + 1) then 3 else 0 := by
    push_cast [← @Nat.cast_inj Int, ← mul_left_cancel_iff_of_pos (b := (_ ^ 2 : Int)) two_pos, mul_add,
      expDegree_cast (n + 2).succ_ne_zero, expDegree_cast n.succ_ne_zero, Nat.even_add_one, ite_not]
    split_ifs <;> ring1
  have hc : (1 : Int) = 1 * expCoeff (n + 2) ^ 2 * (if Even (n + 1) then 1 else 4) -
      expCoeff (n + 3) * expCoeff (n + 1) * (if Even (n + 1) then 4 else 1) := by
    push_cast [← @Int.cast_inj Rat, expCoeff_cast, Nat.even_add_one, ite_not]
    split_ifs <;> ring1
  rw [Nat.cast_add]; rw [Nat.cast_one]; rw [Φ_ofNat]
  constructor
  · nth_rw 1 [← max_self <| (_ + _) ^ 2, hd, hd']
    refine natDegree_sub_le_of_le (dm (dm natDegree_X_le (dp h.1)) ?_) (dm (dm h.1 h.1) ?_) <;>
      split_ifs <;> simp only [natDegree_one.le, W.natDegree_Ψ₂Sq_le]
  · nth_rw 1 [coeff_sub, hd, hd', cm (dm natDegree_X_le (dp h.1)), cm natDegree_X_le (dp h.1),
      coeff_X_one, coeff_pow_of_natDegree_le h.1, h.2, apply_ite₂ coeff, coeff_one_zero, coeff_Ψ₂Sq,
      cm (dm h.1 h.1), cm h.1 h.1, h.2, h.2, apply_ite₂ coeff, coeff_one_zero, coeff_Ψ₂Sq]
    conv_rhs => rw [← Int.cast_one, hc]
    · norm_cast
    all_goals split_ifs <;> simp only [natDegree_one.le, W.natDegree_Ψ₂Sq_le]

/--
lemma `natDegree_Φ_le` / 引理 `natDegree_Φ_le`

English:
lemma natDegree_Φ_le
  given: (n : Int)
  statement: (W.Φ n).natDegree <= n.natAbs ^ 2
  proof: by
  induction n using Int.negInduction with
  | nat n => exact (W.natDegree_coeff_Φ_ofNat n).left
  | neg ih => simp_rw [Φ_neg, Int.natAbs_neg, ih]

@[simp]

中文:
引理 natDegree_Φ_le
  条件: (n : 整数)
  结论: (W.Φ n).natDegree <= n.natAbs ^ 2
  证明: by
  induction n using Int.negInduction with
  | nat n => exact (W.natDegree_coeff_Φ_ofNat n).left
  | neg ih => simp_rw [Φ_neg, Int.natAbs_neg, ih]

@[simp]

Depends on / 依赖: Int.natAbs_neg, Int.negInduction, W.natDegree_coeff_, natAbs_neg, negInduction, simp_rw
-/
lemma natDegree_Φ_le (n : Int) : (W.Φ n).natDegree <= n.natAbs ^ 2 := by
  induction n using Int.negInduction with
  | nat n => exact (W.natDegree_coeff_Φ_ofNat n).left
  | neg ih => simp_rw [Φ_neg, Int.natAbs_neg, ih]

@[simp]
/--
lemma `coeff_Φ` / 引理 `coeff_Φ`

English:
lemma coeff_Φ
  given: (n : Int)
  statement: (W.Φ n).coeff (n.natAbs ^ 2) = 1
  proof: by
  induction n using Int.negInduction with
  | nat n => exact (W.natDegree_coeff_Φ_ofNat n).right
  | neg ih => rw [Φ_neg, Int.natAbs_neg, ih]

中文:
引理 coeff_Φ
  条件: (n : 整数)
  结论: (W.Φ n).coeff (n.natAbs ^ 2) = 1
  证明: by
  induction n using Int.negInduction with
  | nat n => exact (W.natDegree_coeff_Φ_ofNat n).right
  | neg ih => rw [Φ_neg, Int.natAbs_neg, ih]

Depends on / 依赖: Int.natAbs_neg, Int.negInduction, W.natDegree_coeff_, natAbs_neg, negInduction
-/
lemma coeff_Φ (n : Int) : (W.Φ n).coeff (n.natAbs ^ 2) = 1 := by
  induction n using Int.negInduction with
  | nat n => exact (W.natDegree_coeff_Φ_ofNat n).right
  | neg ih => rw [Φ_neg, Int.natAbs_neg, ih]

/--
lemma `coeff_Φ_ne_zero` / 引理 `coeff_Φ_ne_zero`

English:
lemma coeff_Φ_ne_zero
  given: [Nontrivial R] (n : Int)
  statement: (W.Φ n).coeff (n.natAbs ^ 2) != 0
  proof: W.coeff_Φ n ▸ one_ne_zero

@[simp]

中文:
引理 coeff_Φ_ne_zero
  条件: [非平凡 R] (n : 整数)
  结论: (W.Φ n).coeff (n.natAbs ^ 2) != 0
  证明: W.coeff_Φ n ▸ one_ne_zero

@[simp]

Depends on / 依赖: W.coeff_, one_ne_zero
-/
lemma coeff_Φ_ne_zero [Nontrivial R] (n : Int) : (W.Φ n).coeff (n.natAbs ^ 2) != 0 :=
  W.coeff_Φ n ▸ one_ne_zero

@[simp]
/--
lemma `natDegree_Φ` / 引理 `natDegree_Φ`

English:
lemma natDegree_Φ
  given: [Nontrivial R] (n : Int)
  statement: (W.Φ n).natDegree = n.natAbs ^ 2
  proof: natDegree_eq_of_le_of_coeff_ne_zero (W.natDegree_Φ_le n) W.coeff_Φ_ne_zero n

中文:
引理 natDegree_Φ
  条件: [非平凡 R] (n : 整数)
  结论: (W.Φ n).natDegree = n.natAbs ^ 2
  证明: natDegree_eq_of_le_of_coeff_ne_zero (W.natDegree_Φ_le n) W.coeff_Φ_ne_zero n

Depends on / 依赖: W.coeff_, W.natDegree_, natDegree_eq_of_le_of_coeff_ne_zero
-/
lemma natDegree_Φ [Nontrivial R] (n : Int) : (W.Φ n).natDegree = n.natAbs ^ 2 :=
natDegree_eq_of_le_of_coeff_ne_zero (W.natDegree_Φ_le n) W.coeff_Φ_ne_zero n

/--
lemma `natDegree_Φ_pos` / 引理 `natDegree_Φ_pos`

English:
lemma natDegree_Φ_pos
  given: [Nontrivial R] {n : Int} (hn : n != 0)
  statement: 0 < (W.Φ n).natDegree
  proof: by
  simpa [sq_pos_iff]

@[simp]

中文:
引理 natDegree_Φ_pos
  条件: [非平凡 R] {n : 整数} (hn : n != 0)
  结论: 0 < (W.Φ n).natDegree
  证明: by
  simpa [sq_pos_iff]

@[simp]

Depends on / 依赖: sq_pos_iff
-/
lemma natDegree_Φ_pos [Nontrivial R] {n : Int} (hn : n != 0) : 0 < (W.Φ n).natDegree := by
  simpa [sq_pos_iff]

@[simp]
/--
lemma `leadingCoeff_Φ` / 引理 `leadingCoeff_Φ`

English:
lemma leadingCoeff_Φ
  given: [Nontrivial R] (n : Int)
  statement: (W.Φ n).leadingCoeff = 1
  proof: by
  rw [leadingCoeff]; rw [natDegree_Φ]; rw [coeff_Φ]

中文:
引理 leadingCoeff_Φ
  条件: [非平凡 R] (n : 整数)
  结论: (W.Φ n).leadingCoeff = 1
  证明: by
  rw [leadingCoeff]; rw [natDegree_Φ]; rw [coeff_Φ]

Depends on / 依赖: leadingCoeff
-/
lemma leadingCoeff_Φ [Nontrivial R] (n : Int) : (W.Φ n).leadingCoeff = 1 := by
  rw [leadingCoeff]; rw [natDegree_Φ]; rw [coeff_Φ]

/--
lemma `Φ_ne_zero` / 引理 `Φ_ne_zero`

English:
lemma Φ_ne_zero
  given: [Nontrivial R] (n : Int)
  statement: W.Φ n != 0
  proof: by
  by_cases hn : n = 0
  · simpa only [hn, Φ_zero] using one_ne_zero
· exact ne_zero_of_natDegree_gt W.natDegree_Φ_pos hn

中文:
引理 Φ_ne_zero
  条件: [非平凡 R] (n : 整数)
  结论: W.Φ n != 0
  证明: by
  by_cases hn : n = 0
  · simpa only [hn, Φ_zero] using one_ne_zero
· exact ne_zero_of_natDegree_gt W.natDegree_Φ_pos hn

Depends on / 依赖: W.natDegree_, ne_zero_of_natDegree_gt, one_ne_zero
-/
lemma Φ_ne_zero [Nontrivial R] (n : Int) : W.Φ n != 0 := by
  by_cases hn : n = 0
  · simpa only [hn, Φ_zero] using one_ne_zero
· exact ne_zero_of_natDegree_gt W.natDegree_Φ_pos hn

end Φ

end WeierstrassCurve
