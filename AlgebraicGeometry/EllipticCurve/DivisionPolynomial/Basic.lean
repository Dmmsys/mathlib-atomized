/-
Copyright (c) 2024 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.NumberTheory.EllipticDivisibilitySequence

/-!
# Division polynomials of Weierstrass curves

This file defines certain polynomials associated to division polynomials of Weierstrass curves.
These are defined in terms of the auxiliary sequences for normalised elliptic divisibility sequences
(EDS) as defined in `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`.

## Mathematical background

Let `W` be a Weierstrass curve over a commutative ring `R`. The sequence of `n`-division polynomials
`ψₙ ∈ R[X, Y]` of `W` is the normalised EDS with initial values
* `ψ₀ := 0`,
* `ψ₁ := 1`,
* `ψ₂ := 2Y + a₁X + a₃`,
* `ψ₃ := 3X⁴ + b₂X³ + 3b₄X² + 3b₆X + b₈`, and
* `ψ₄ := ψ₂ ⬝ (2X⁶ + b₂X⁵ + 5b₄X⁴ + 10b₆X³ + 10b₈X² + (b₂b₈ - b₄b₆)X + (b₄b₈ - b₆²))`.

Furthermore, define the associated sequences `φₙ, ωₙ ∈ R[X, Y]` by
* `φₙ := Xψₙ² - ψₙ₊₁ ⬝ ψₙ₋₁`, and
* `ωₙ := (ψ₂ₙ / ψₙ - ψₙ ⬝ (a₁φₙ + a₃ψₙ²)) / 2`.

Note that `ωₙ` is always well-defined as a polynomial in `R[X, Y]`. As a start, it can be shown by
induction that `ψₙ` always divides `ψ₂ₙ` in `R[X, Y]`, so that `ψ₂ₙ / ψₙ` is always well-defined as
a polynomial, while division by `2` is well-defined when `R` has characteristic different from `2`.
In general, it can be shown that `2` always divides the polynomial `ψ₂ₙ / ψₙ - ψₙ ⬝ (a₁φₙ + a₃ψₙ²)`
in the characteristic `0` universal ring `𝓡[X, Y] := ℤ[A₁, A₂, A₃, A₄, A₆][X, Y]` of `W`, where the
`Aᵢ` are indeterminates. Then `ωₙ` can be equivalently defined as the image of this division under
the associated universal morphism `𝓡[X, Y] → R[X, Y]` mapping `Aᵢ` to `aᵢ`.

Now, in the coordinate ring `R[W]`, note that `ψ₂²` is congruent to the polynomial
`Ψ₂Sq := 4X³ + b₂X² + 2b₄X + b₆ ∈ R[X]`. As such, the recurrences of a normalised EDS show that
`ψₙ / ψ₂` are congruent to certain polynomials in `R[W]`. In particular, define `preΨₙ ∈ R[X]` as
the auxiliary sequence for a normalised EDS with extra parameter `Ψ₂Sq²` and initial values
* `preΨ₀ := 0`,
* `preΨ₁ := 1`,
* `preΨ₂ := 1`,
* `preΨ₃ := ψ₃`, and
* `preΨ₄ := ψ₄ / ψ₂`.

The corresponding normalised EDS `Ψₙ ∈ R[X, Y]` is then given by
* `Ψₙ := preΨₙ ⬝ ψ₂` if `n` is even, and
* `Ψₙ := preΨₙ` if `n` is odd.

Furthermore, define the associated sequences `ΨSqₙ, Φₙ ∈ R[X]` by
* `ΨSqₙ := preΨₙ² ⬝ Ψ₂Sq` if `n` is even,
* `ΨSqₙ := preΨₙ²` if `n` is odd,
* `Φₙ := XΨSqₙ - preΨₙ₊₁ ⬝ preΨₙ₋₁` if `n` is even, and
* `Φₙ := XΨSqₙ - preΨₙ₊₁ ⬝ preΨₙ₋₁ ⬝ Ψ₂Sq` if `n` is odd.

With these definitions, `ψₙ ∈ R[X, Y]` and `φₙ ∈ R[X, Y]` are congruent in `R[W]` to `Ψₙ ∈ R[X, Y]`
and `Φₙ ∈ R[X]` respectively, which are defined in terms of `Ψ₂Sq ∈ R[X]` and `preΨₙ ∈ R[X]`.

## Main definitions

* `WeierstrassCurve.preΨ`: the univariate polynomials `preΨₙ`.
* `WeierstrassCurve.ΨSq`: the univariate polynomials `ΨSqₙ`.
* `WeierstrassCurve.Ψ`: the bivariate polynomials `Ψₙ`.
* `WeierstrassCurve.Φ`: the univariate polynomials `Φₙ`.
* `WeierstrassCurve.ψ`: the bivariate `n`-division polynomials `ψₙ`.
* `WeierstrassCurve.φ`: the bivariate polynomials `φₙ`.
* TODO: the bivariate polynomials `ωₙ`.

## Implementation notes

Analogously to `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`, the bivariate polynomials
`Ψₙ` are defined in terms of the univariate polynomials `preΨₙ`. This is done partially to avoid
ring division, but more crucially to allow the definition of `ΨSqₙ` and `Φₙ` as univariate
polynomials without needing to work under the coordinate ring, and to allow the computation of their
leading terms without ambiguity. Furthermore, evaluating these polynomials at a rational point on
`W` recovers their original definition up to linear combinations of the Weierstrass equation of `W`,
hence also avoiding the need to work in the coordinate ring.

TODO: implementation notes for the definition of `ωₙ`.

## References

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, division polynomial, torsion point
-/

@[expose] public section

open Polynomial
open scoped Polynomial.Bivariate

local macro "C_simp" : tactic =>
  `(tactic| simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow])

universe r s u v

namespace WeierstrassCurve

variable {R : Type r} {S : Type s} [CommRing R] [CommRing S] (W : WeierstrassCurve R)

section Ψ₂Sq

/-! ### The univariate polynomial `Ψ₂Sq` -/

/--
Definition of `ψ₂` / `ψ₂` 的定义

English:
definition ψ₂
  signature: : R[X][Y]
  body: W.toAffine.polynomialY

中文:
定义 ψ₂
  签名: : R[X][Y]
  定义体: W.toAffine.polynomialY

Depends on / 依赖: W.toAffine.polynomialY, polynomialY, toAffine
-/
noncomputable def ψ₂ : R[X][Y] :=
  W.toAffine.polynomialY

/--
Definition of `Ψ₂Sq` / `Ψ₂Sq` 的定义

English:
definition Ψ₂Sq
  signature: : R[X]
  body: C 4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆

中文:
定义 Ψ₂Sq
  签名: : R[X]
  定义体: C 4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆
-/
noncomputable def Ψ₂Sq : R[X] :=
  C 4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆

/--
lemma `C_Ψ₂Sq` / 引理 `C_Ψ₂Sq`

English:
lemma C_Ψ₂Sq
  statement: C W.Ψ₂Sq = W.ψ₂ ^ 2 - 4 * W.toAffine.polynomial
  proof: by
  rw [Ψ₂Sq]; rw [ψ₂]; rw [b₂]; rw [b₄]; rw [b₆]; rw [Affine.polynomialY]; rw [Affine.polynomial]
  C_simp
  ring1

中文:
引理 C_Ψ₂Sq
  结论: C W.Ψ₂Sq = W.ψ₂ ^ 2 - 4 * W.toAffine.polynomial
  证明: by
  rw [Ψ₂Sq]; rw [ψ₂]; rw [b₂]; rw [b₄]; rw [b₆]; rw [Affine.polynomialY]; rw [Affine.polynomial]
  C_simp
  ring1

Depends on / 依赖: Affine, Affine.polynomial, Affine.polynomialY, C_simp, polynomial, polynomialY
-/
lemma C_Ψ₂Sq : C W.Ψ₂Sq = W.ψ₂ ^ 2 - 4 * W.toAffine.polynomial := by
  rw [Ψ₂Sq]; rw [ψ₂]; rw [b₂]; rw [b₄]; rw [b₆]; rw [Affine.polynomialY]; rw [Affine.polynomial]
  C_simp
  ring1

/--
lemma `ψ₂_sq` / 引理 `ψ₂_sq`

English:
lemma ψ₂_sq
  statement: W.ψ₂ ^ 2 = C W.Ψ₂Sq + 4 * W.toAffine.polynomial
  proof: by
  simp [C_Ψ₂Sq]

中文:
引理 ψ₂_sq
  结论: W.ψ₂ ^ 2 = C W.Ψ₂Sq + 4 * W.toAffine.polynomial
  证明: by
  simp [C_Ψ₂Sq]
-/
lemma ψ₂_sq : W.ψ₂ ^ 2 = C W.Ψ₂Sq + 4 * W.toAffine.polynomial := by
  simp [C_Ψ₂Sq]

/--
lemma `Affine.CoordinateRing.mk_ψ₂_sq` / 引理 `Affine.CoordinateRing.mk_ψ₂_sq`

English:
lemma Affine.CoordinateRing.mk_ψ₂_sq
  statement: mk W W.ψ₂ ^ 2 = mk W (C W.Ψ₂Sq)
  proof: by
  simp [C_Ψ₂Sq]

中文:
引理 仿射.CoordinateRing.mk_ψ₂_sq
  结论: mk W W.ψ₂ ^ 2 = mk W (C W.Ψ₂Sq)
  证明: by
  simp [C_Ψ₂Sq]
-/
lemma Affine.CoordinateRing.mk_ψ₂_sq : mk W W.ψ₂ ^ 2 = mk W (C W.Ψ₂Sq) := by
  simp [C_Ψ₂Sq]

-- TODO: remove `twoTorsionPolynomial` in favour of `Ψ₂Sq`
/--
lemma `Ψ₂Sq_eq` / 引理 `Ψ₂Sq_eq`

English:
lemma Ψ₂Sq_eq
  statement: W.Ψ₂Sq = W.twoTorsionPolynomial.toPoly
  proof: rfl

中文:
引理 Ψ₂Sq_eq
  结论: W.Ψ₂Sq = W.twoTorsionPolynomial.toPoly
  证明: rfl

Depends on / 依赖: HomologyPretheory, HomologyPretheory.h
-/
lemma Ψ₂Sq_eq : W.Ψ₂Sq = W.twoTorsionPolynomial.toPoly :=
  rfl

end Ψ₂Sq

section preΨ'

/-! ### The univariate polynomials `preΨₙ` for `n ∈ ℕ` -/

/--
Definition of `Ψ₃` / `Ψ₃` 的定义

English:
definition Ψ₃
  signature: : R[X]
  body: 3 * X ^ 4 + C W.b₂ * X ^ 3 + 3 * C W.b₄ * X ^ 2 + 3 * C W.b₆ * X + C W.b₈

中文:
定义 Ψ₃
  签名: : R[X]
  定义体: 3 * X ^ 4 + C W.b₂ * X ^ 3 + 3 * C W.b₄ * X ^ 2 + 3 * C W.b₆ * X + C W.b₈

Depends on / 依赖: HomologyPretheory, HomologyPretheory.hFunctor, hFunctor
-/
noncomputable def Ψ₃ : R[X] :=
  3 * X ^ 4 + C W.b₂ * X ^ 3 + 3 * C W.b₄ * X ^ 2 + 3 * C W.b₆ * X + C W.b₈

/--
Definition of `preΨ₄` / `preΨ₄` 的定义

English:
definition preΨ₄
  signature: : R[X]
  body: 2 * X ^ 6 + C W.b₂ * X ^ 5 + 5 * C W.b₄ * X ^ 4 + 10 * C W.b₆ * X ^ 3 + 10 * C W.b₈ * X ^ 2 +
    C (W.b₂ * W.b₈ - W.b₄ * W.b₆) * X + C (W.b₄ * W.b₈ - W.b₆ ^ 2)

中文:
定义 preΨ₄
  签名: : R[X]
  定义体: 2 * X ^ 6 + C W.b₂ * X ^ 5 + 5 * C W.b₄ * X ^ 4 + 10 * C W.b₆ * X ^ 3 + 10 * C W.b₈ * X ^ 2 +
    C (W.b₂ * W.b₈ - W.b₄ * W.b₆) * X + C (W.b₄ * W.b₈ - W.b₆ ^ 2)
-/
noncomputable def preΨ₄ : R[X] :=
  2 * X ^ 6 + C W.b₂ * X ^ 5 + 5 * C W.b₄ * X ^ 4 + 10 * C W.b₆ * X ^ 3 + 10 * C W.b₈ * X ^ 2 +
    C (W.b₂ * W.b₈ - W.b₄ * W.b₆) * X + C (W.b₄ * W.b₈ - W.b₆ ^ 2)

/--
Definition of `preΨ'` / `preΨ'` 的定义

English:
definition preΨ'
  signature: (n : Nat)
  body: preNormEDS' (W.Ψ₂Sq ^ 2) W.Ψ₃ W.preΨ₄ n

@[simp]

中文:
定义 preΨ'
  签名: (n : 自然数)
  定义体: preNormEDS' (W.Ψ₂Sq ^ 2) W.Ψ₃ W.preΨ₄ n

@[simp]

Depends on / 依赖: W.pre, preNormEDS
-/
noncomputable def preΨ' (n : Nat) : R[X] :=
  preNormEDS' (W.Ψ₂Sq ^ 2) W.Ψ₃ W.preΨ₄ n

@[simp]
/--
lemma `preΨ'_zero` / 引理 `preΨ'_zero`

English:
lemma preΨ'_zero
  statement: W.preΨ' 0 = 0
  proof: preNormEDS'_zero ..

@[simp]

中文:
引理 preΨ'_zero
  结论: W.preΨ' 0 = 0
  证明: preNormEDS'_zero ..

@[simp]
-/
lemma preΨ'_zero : W.preΨ' 0 = 0 :=
  preNormEDS'_zero ..

@[simp]
/--
lemma `preΨ'_one` / 引理 `preΨ'_one`

English:
lemma preΨ'_one
  statement: W.preΨ' 1 = 1
  proof: preNormEDS'_one ..

@[simp]

中文:
引理 preΨ'_one
  结论: W.preΨ' 1 = 1
  证明: preNormEDS'_one ..

@[simp]
-/
lemma preΨ'_one : W.preΨ' 1 = 1 :=
  preNormEDS'_one ..

@[simp]
/--
lemma `preΨ'_two` / 引理 `preΨ'_two`

English:
lemma preΨ'_two
  statement: W.preΨ' 2 = 1
  proof: preNormEDS'_two ..

@[simp]

中文:
引理 preΨ'_two
  结论: W.preΨ' 2 = 1
  证明: preNormEDS'_two ..

@[simp]
-/
lemma preΨ'_two : W.preΨ' 2 = 1 :=
  preNormEDS'_two ..

@[simp]
/--
lemma `preΨ'_three` / 引理 `preΨ'_three`

English:
lemma preΨ'_three
  statement: W.preΨ' 3 = W.Ψ₃
  proof: preNormEDS'_three ..

@[simp]

中文:
引理 preΨ'_three
  结论: W.preΨ' 3 = W.Ψ₃
  证明: preNormEDS'_three ..

@[simp]
-/
lemma preΨ'_three : W.preΨ' 3 = W.Ψ₃ :=
  preNormEDS'_three ..

@[simp]
/--
lemma `preΨ'_four` / 引理 `preΨ'_four`

English:
lemma preΨ'_four
  statement: W.preΨ' 4 = W.preΨ₄
  proof: preNormEDS'_four ..

中文:
引理 preΨ'_four
  结论: W.preΨ' 4 = W.preΨ₄
  证明: preNormEDS'_four ..
-/
lemma preΨ'_four : W.preΨ' 4 = W.preΨ₄ :=
  preNormEDS'_four ..

/--
lemma `preΨ'_even` / 引理 `preΨ'_even`

English:
lemma preΨ'_even
  given: (m : Nat)
  statement: W.preΨ' (2 * (m + 3)) =
  proof: preNormEDS'_even ..

中文:
引理 preΨ'_even
  条件: (m : 自然数)
  结论: W.preΨ' (2 * (m + 3)) =
  证明: preNormEDS'_even ..
-/
lemma preΨ'_even (m : Nat) : W.preΨ' (2 * (m + 3)) =
    W.preΨ' (m + 2) ^ 2 * W.preΨ' (m + 3) * W.preΨ' (m + 5) -
      W.preΨ' (m + 1) * W.preΨ' (m + 3) * W.preΨ' (m + 4) ^ 2 :=
  preNormEDS'_even ..

/--
lemma `preΨ'_odd` / 引理 `preΨ'_odd`

English:
lemma preΨ'_odd
  given: (m : Nat)
  statement: W.preΨ' (2 * (m + 2) + 1) =
  proof: preNormEDS'_odd ..

中文:
引理 preΨ'_odd
  条件: (m : 自然数)
  结论: W.preΨ' (2 * (m + 2) + 1) =
  证明: preNormEDS'_odd ..
-/
lemma preΨ'_odd (m : Nat) : W.preΨ' (2 * (m + 2) + 1) =
    W.preΨ' (m + 4) * W.preΨ' (m + 2) ^ 3 * (if Even m then W.Ψ₂Sq ^ 2 else 1) -
      W.preΨ' (m + 1) * W.preΨ' (m + 3) ^ 3 * (if Even m then 1 else W.Ψ₂Sq ^ 2) :=
  preNormEDS'_odd ..

end preΨ'

section preΨ

/-! ### The univariate polynomials `preΨₙ` for `n ∈ ℤ` -/

/--
Definition of `preΨ` / `preΨ` 的定义

English:
definition preΨ
  signature: (n : Int)
  body: preNormEDS (W.Ψ₂Sq ^ 2) W.Ψ₃ W.preΨ₄ n

@[simp]

中文:
定义 preΨ
  签名: (n : 整数)
  定义体: preNormEDS (W.Ψ₂Sq ^ 2) W.Ψ₃ W.preΨ₄ n

@[simp]

Depends on / 依赖: W.pre, preNormEDS
-/
noncomputable def preΨ (n : Int) : R[X] :=
  preNormEDS (W.Ψ₂Sq ^ 2) W.Ψ₃ W.preΨ₄ n

@[simp]
/--
lemma `preΨ_ofNat` / 引理 `preΨ_ofNat`

English:
lemma preΨ_ofNat
  given: (n : Nat)
  statement: W.preΨ n = W.preΨ' n
  proof: preNormEDS_ofNat ..

@[simp]

中文:
引理 preΨ_of自然数
  条件: (n : 自然数)
  结论: W.preΨ n = W.preΨ' n
  证明: preNormEDS_ofNat ..

@[simp]

Depends on / 依赖: preNormEDS_ofNat
-/
lemma preΨ_ofNat (n : Nat) : W.preΨ n = W.preΨ' n :=
  preNormEDS_ofNat ..

@[simp]
/--
lemma `preΨ_zero` / 引理 `preΨ_zero`

English:
lemma preΨ_zero
  statement: W.preΨ 0 = 0
  proof: preNormEDS_zero ..

@[simp]

中文:
引理 preΨ_zero
  结论: W.preΨ 0 = 0
  证明: preNormEDS_zero ..

@[simp]

Depends on / 依赖: preNormEDS_zero
-/
lemma preΨ_zero : W.preΨ 0 = 0 :=
  preNormEDS_zero ..

@[simp]
/--
lemma `preΨ_one` / 引理 `preΨ_one`

English:
lemma preΨ_one
  statement: W.preΨ 1 = 1
  proof: preNormEDS_one ..

@[simp]

中文:
引理 preΨ_one
  结论: W.preΨ 1 = 1
  证明: preNormEDS_one ..

@[simp]

Depends on / 依赖: preNormEDS_one
-/
lemma preΨ_one : W.preΨ 1 = 1 :=
  preNormEDS_one ..

@[simp]
/--
lemma `preΨ_two` / 引理 `preΨ_two`

English:
lemma preΨ_two
  statement: W.preΨ 2 = 1
  proof: preNormEDS_two ..

@[simp]

中文:
引理 preΨ_two
  结论: W.preΨ 2 = 1
  证明: preNormEDS_two ..

@[simp]

Depends on / 依赖: preNormEDS_two
-/
lemma preΨ_two : W.preΨ 2 = 1 :=
  preNormEDS_two ..

@[simp]
/--
lemma `preΨ_three` / 引理 `preΨ_three`

English:
lemma preΨ_three
  statement: W.preΨ 3 = W.Ψ₃
  proof: preNormEDS_three ..

@[simp]

中文:
引理 preΨ_three
  结论: W.preΨ 3 = W.Ψ₃
  证明: preNormEDS_three ..

@[simp]

Depends on / 依赖: preNormEDS_three
-/
lemma preΨ_three : W.preΨ 3 = W.Ψ₃ :=
  preNormEDS_three ..

@[simp]
/--
lemma `preΨ_four` / 引理 `preΨ_four`

English:
lemma preΨ_four
  statement: W.preΨ 4 = W.preΨ₄
  proof: preNormEDS_four ..

@[simp]

中文:
引理 preΨ_four
  结论: W.preΨ 4 = W.preΨ₄
  证明: preNormEDS_four ..

@[simp]

Depends on / 依赖: preNormEDS_four
-/
lemma preΨ_four : W.preΨ 4 = W.preΨ₄ :=
  preNormEDS_four ..

@[simp]
/--
lemma `preΨ_neg` / 引理 `preΨ_neg`

English:
lemma preΨ_neg
  given: (n : Int)
  statement: W.preΨ (-n) = -W.preΨ n
  proof: preNormEDS_neg ..

中文:
引理 preΨ_neg
  条件: (n : 整数)
  结论: W.preΨ (-n) = -W.preΨ n
  证明: preNormEDS_neg ..

Depends on / 依赖: preNormEDS_neg
-/
lemma preΨ_neg (n : Int) : W.preΨ (-n) = -W.preΨ n :=
  preNormEDS_neg ..

/--
lemma `preΨ_even` / 引理 `preΨ_even`

English:
lemma preΨ_even
  given: (m : Int)
  statement: W.preΨ (2 * m) =
  proof: preNormEDS_even ..

中文:
引理 preΨ_even
  条件: (m : 整数)
  结论: W.preΨ (2 * m) =
  证明: preNormEDS_even ..

Depends on / 依赖: preNormEDS_even
-/
lemma preΨ_even (m : Int) : W.preΨ (2 * m) =
    W.preΨ (m - 1) ^ 2 * W.preΨ m * W.preΨ (m + 2) -
      W.preΨ (m - 2) * W.preΨ m * W.preΨ (m + 1) ^ 2 :=
  preNormEDS_even ..

/--
lemma `preΨ_odd` / 引理 `preΨ_odd`

English:
lemma preΨ_odd
  given: (m : Int)
  statement: W.preΨ (2 * m + 1) =
  proof: preNormEDS_odd ..

中文:
引理 preΨ_odd
  条件: (m : 整数)
  结论: W.preΨ (2 * m + 1) =
  证明: preNormEDS_odd ..

Depends on / 依赖: preNormEDS_odd
-/
lemma preΨ_odd (m : Int) : W.preΨ (2 * m + 1) =
    W.preΨ (m + 2) * W.preΨ m ^ 3 * (if Even m then W.Ψ₂Sq ^ 2 else 1) -
      W.preΨ (m - 1) * W.preΨ (m + 1) ^ 3 * (if Even m then 1 else W.Ψ₂Sq ^ 2) :=
  preNormEDS_odd ..

end preΨ

section ΨSq

/-! ### The univariate polynomials `ΨSqₙ` -/

/--
Definition of `ΨSq` / `ΨSq` 的定义

English:
definition ΨSq
  signature: (n : Int)
  body: W.preΨ n ^ 2 * if Even n then W.Ψ₂Sq else 1

@[simp]

中文:
定义 ΨSq
  签名: (n : 整数)
  定义体: W.preΨ n ^ 2 * if Even n then W.Ψ₂Sq else 1

@[simp]

Depends on / 依赖: W.pre
-/
noncomputable def ΨSq (n : Int) : R[X] :=
  W.preΨ n ^ 2 * if Even n then W.Ψ₂Sq else 1

@[simp]
/--
lemma `ΨSq_ofNat` / 引理 `ΨSq_ofNat`

English:
lemma ΨSq_ofNat
  given: (n : Nat)
  statement: W.ΨSq n = W.preΨ' n ^ 2 * if Even n then W.Ψ₂Sq else 1
  proof: by
  simp [ΨSq]

@[simp]

中文:
引理 ΨSq_of自然数
  条件: (n : 自然数)
  结论: W.ΨSq n = W.preΨ' n ^ 2 * if Even n then W.Ψ₂Sq else 1
  证明: by
  simp [ΨSq]

@[simp]
-/
lemma ΨSq_ofNat (n : Nat) : W.ΨSq n = W.preΨ' n ^ 2 * if Even n then W.Ψ₂Sq else 1 := by
  simp [ΨSq]

@[simp]
/--
lemma `ΨSq_zero` / 引理 `ΨSq_zero`

English:
lemma ΨSq_zero
  statement: W.ΨSq 0 = 0
  proof: by
  simp [ΨSq]

@[simp]

中文:
引理 ΨSq_zero
  结论: W.ΨSq 0 = 0
  证明: by
  simp [ΨSq]

@[simp]
-/
lemma ΨSq_zero : W.ΨSq 0 = 0 := by
  simp [ΨSq]

@[simp]
/--
lemma `ΨSq_one` / 引理 `ΨSq_one`

English:
lemma ΨSq_one
  statement: W.ΨSq 1 = 1
  proof: by
  simp [ΨSq]

@[simp]

中文:
引理 ΨSq_one
  结论: W.ΨSq 1 = 1
  证明: by
  simp [ΨSq]

@[simp]
-/
lemma ΨSq_one : W.ΨSq 1 = 1 := by
  simp [ΨSq]

@[simp]
/--
lemma `ΨSq_two` / 引理 `ΨSq_two`

English:
lemma ΨSq_two
  statement: W.ΨSq 2 = W.Ψ₂Sq
  proof: by
  simp [ΨSq]

@[simp]

中文:
引理 ΨSq_two
  结论: W.ΨSq 2 = W.Ψ₂Sq
  证明: by
  simp [ΨSq]

@[simp]
-/
lemma ΨSq_two : W.ΨSq 2 = W.Ψ₂Sq := by
  simp [ΨSq]

@[simp]
/--
lemma `ΨSq_three` / 引理 `ΨSq_three`

English:
lemma ΨSq_three
  statement: W.ΨSq 3 = W.Ψ₃ ^ 2
  proof: by
  simp [ΨSq, show ¬Even (3 : Int) by decide]

@[simp]

中文:
引理 ΨSq_three
  结论: W.ΨSq 3 = W.Ψ₃ ^ 2
  证明: by
  simp [ΨSq, show ¬Even (3 : Int) by decide]

@[simp]
-/
lemma ΨSq_three : W.ΨSq 3 = W.Ψ₃ ^ 2 := by
  simp [ΨSq, show ¬Even (3 : Int) by decide]

@[simp]
/--
lemma `ΨSq_four` / 引理 `ΨSq_four`

English:
lemma ΨSq_four
  statement: W.ΨSq 4 = W.preΨ₄ ^ 2 * W.Ψ₂Sq
  proof: by
  simp [ΨSq, show ¬Odd (4 : Int) by decide]

@[simp]

中文:
引理 ΨSq_four
  结论: W.ΨSq 4 = W.preΨ₄ ^ 2 * W.Ψ₂Sq
  证明: by
  simp [ΨSq, show ¬Odd (4 : Int) by decide]

@[simp]
-/
lemma ΨSq_four : W.ΨSq 4 = W.preΨ₄ ^ 2 * W.Ψ₂Sq := by
  simp [ΨSq, show ¬Odd (4 : Int) by decide]

@[simp]
/--
lemma `ΨSq_neg` / 引理 `ΨSq_neg`

English:
lemma ΨSq_neg
  given: (n : Int)
  statement: W.ΨSq (-n) = W.ΨSq n
  proof: by
  simp [ΨSq]

中文:
引理 ΨSq_neg
  条件: (n : 整数)
  结论: W.ΨSq (-n) = W.ΨSq n
  证明: by
  simp [ΨSq]
-/
lemma ΨSq_neg (n : Int) : W.ΨSq (-n) = W.ΨSq n := by
  simp [ΨSq]

/--
lemma `ΨSq_even` / 引理 `ΨSq_even`

English:
lemma ΨSq_even
  given: (m : Int)
  statement: W.ΨSq (2 * m) =
  proof: by
  rw [ΨSq]; rw [preΨ_even]; rw [if_pos <| even_two_mul m]

中文:
引理 ΨSq_even
  条件: (m : 整数)
  结论: W.ΨSq (2 * m) =
  证明: by
  rw [ΨSq]; rw [preΨ_even]; rw [if_pos <| even_two_mul m]

Depends on / 依赖: even_two_mul, if_pos
-/
lemma ΨSq_even (m : Int) : W.ΨSq (2 * m) =
    (W.preΨ (m - 1) ^ 2 * W.preΨ m * W.preΨ (m + 2) -
      W.preΨ (m - 2) * W.preΨ m * W.preΨ (m + 1) ^ 2) ^ 2 * W.Ψ₂Sq := by
  rw [ΨSq]; rw [preΨ_even]; rw [if_pos <| even_two_mul m]

/--
lemma `ΨSq_odd` / 引理 `ΨSq_odd`

English:
lemma ΨSq_odd
  given: (m : Int)
  statement: W.ΨSq (2 * m + 1) =
  proof: by
  rw [ΨSq]; rw [preΨ_odd]; rw [if_neg m.not_even_two_mul_add_one]; rw [mul_one]

中文:
引理 ΨSq_odd
  条件: (m : 整数)
  结论: W.ΨSq (2 * m + 1) =
  证明: by
  rw [ΨSq]; rw [preΨ_odd]; rw [if_neg m.not_even_two_mul_add_one]; rw [mul_one]

Depends on / 依赖: if_neg, m.not_even_two_mul_add_one, mul_one, not_even_two_mul_add_one
-/
lemma ΨSq_odd (m : Int) : W.ΨSq (2 * m + 1) =
    (W.preΨ (m + 2) * W.preΨ m ^ 3 * (if Even m then W.Ψ₂Sq ^ 2 else 1) -
      W.preΨ (m - 1) * W.preΨ (m + 1) ^ 3 * (if Even m then 1 else W.Ψ₂Sq ^ 2)) ^ 2 := by
  rw [ΨSq]; rw [preΨ_odd]; rw [if_neg m.not_even_two_mul_add_one]; rw [mul_one]

end ΨSq

section Ψ

/-! ### The bivariate polynomials `Ψₙ` -/

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def Ψ (n : Int)
  body: C (W.preΨ n) * if Even n then W.ψ₂ else 1

中文:
定义 noncomputable
  签名: def Ψ (n : 整数)
  定义体: C (W.preΨ n) * if Even n then W.ψ₂ else 1
-/
protected noncomputable def Ψ (n : Int) : R[X][Y] :=
  C (W.preΨ n) * if Even n then W.ψ₂ else 1

open WeierstrassCurve (Ψ)

@[simp]
/--
lemma `Ψ_ofNat` / 引理 `Ψ_ofNat`

English:
lemma Ψ_ofNat
  given: (n : Nat)
  statement: W.Ψ n = C (W.preΨ' n) * if Even n then W.ψ₂ else 1
  proof: by
  simp [Ψ]

@[simp]

中文:
引理 Ψ_of自然数
  条件: (n : 自然数)
  结论: W.Ψ n = C (W.preΨ' n) * if Even n then W.ψ₂ else 1
  证明: by
  simp [Ψ]

@[simp]
-/
lemma Ψ_ofNat (n : Nat) : W.Ψ n = C (W.preΨ' n) * if Even n then W.ψ₂ else 1 := by
  simp [Ψ]

@[simp]
/--
lemma `Ψ_zero` / 引理 `Ψ_zero`

English:
lemma Ψ_zero
  statement: W.Ψ 0 = 0
  proof: by
  simp [Ψ]

@[simp]

中文:
引理 Ψ_zero
  结论: W.Ψ 0 = 0
  证明: by
  simp [Ψ]

@[simp]
-/
lemma Ψ_zero : W.Ψ 0 = 0 := by
  simp [Ψ]

@[simp]
/--
lemma `Ψ_one` / 引理 `Ψ_one`

English:
lemma Ψ_one
  statement: W.Ψ 1 = 1
  proof: by
  simp [Ψ]

@[simp]

中文:
引理 Ψ_one
  结论: W.Ψ 1 = 1
  证明: by
  simp [Ψ]

@[simp]
-/
lemma Ψ_one : W.Ψ 1 = 1 := by
  simp [Ψ]

@[simp]
/--
lemma `Ψ_two` / 引理 `Ψ_two`

English:
lemma Ψ_two
  statement: W.Ψ 2 = W.ψ₂
  proof: by
  simp [Ψ]

@[simp]

中文:
引理 Ψ_two
  结论: W.Ψ 2 = W.ψ₂
  证明: by
  simp [Ψ]

@[simp]
-/
lemma Ψ_two : W.Ψ 2 = W.ψ₂ := by
  simp [Ψ]

@[simp]
/--
lemma `Ψ_three` / 引理 `Ψ_three`

English:
lemma Ψ_three
  statement: W.Ψ 3 = C W.Ψ₃
  proof: by
  simp [Ψ, show ¬Even (3 : Int) by decide]

@[simp]

中文:
引理 Ψ_three
  结论: W.Ψ 3 = C W.Ψ₃
  证明: by
  simp [Ψ, show ¬Even (3 : Int) by decide]

@[simp]

Depends on / 依赖: Category, InducedCategory
-/
lemma Ψ_three : W.Ψ 3 = C W.Ψ₃ := by
  simp [Ψ, show ¬Even (3 : Int) by decide]

@[simp]
/--
lemma `Ψ_four` / 引理 `Ψ_four`

English:
lemma Ψ_four
  statement: W.Ψ 4 = C W.preΨ₄ * W.ψ₂
  proof: by
  simp [Ψ, show ¬Odd (4 : Int) by decide]

@[simp]

中文:
引理 Ψ_four
  结论: W.Ψ 4 = C W.preΨ₄ * W.ψ₂
  证明: by
  simp [Ψ, show ¬Odd (4 : Int) by decide]

@[simp]

Depends on / 依赖: i.as, j.as
-/
lemma Ψ_four : W.Ψ 4 = C W.preΨ₄ * W.ψ₂ := by
  simp [Ψ, show ¬Odd (4 : Int) by decide]

@[simp]
/--
lemma `Ψ_neg` / 引理 `Ψ_neg`

English:
lemma Ψ_neg
  given: (n : Int)
  statement: W.Ψ (-n) = -W.Ψ n
  proof: by
  simp_rw [Ψ, preΨ_neg, C_neg, neg_mul, even_neg]

中文:
引理 Ψ_neg
  条件: (n : 整数)
  结论: W.Ψ (-n) = -W.Ψ n
  证明: by
  simp_rw [Ψ, preΨ_neg, C_neg, neg_mul, even_neg]

Depends on / 依赖: C_neg, Category, even_neg, i.as, j.as, neg_mul, simp_rw
-/
lemma Ψ_neg (n : Int) : W.Ψ (-n) = -W.Ψ n := by
  simp_rw [Ψ, preΨ_neg, C_neg, neg_mul, even_neg]

/--
lemma `Ψ_even` / 引理 `Ψ_even`

English:
lemma Ψ_even
  given: (m : Int)
  statement: W.Ψ (2 * m) * W.ψ₂ =
  proof: by
  simp_rw [Ψ, preΨ_even, if_pos <| even_two_mul m, Int.even_add, Int.even_sub, even_two, iff_true,
    Int.not_even_one, iff_false]
  split_ifs <;> C_simp <;> ring1

中文:
引理 Ψ_even
  条件: (m : 整数)
  结论: W.Ψ (2 * m) * W.ψ₂ =
  证明: by
  simp_rw [Ψ, preΨ_even, if_pos <| even_two_mul m, Int.even_add, Int.even_sub, even_two, iff_true,
    Int.not_even_one, iff_false]
  split_ifs <;> C_simp <;> ring1

Depends on / 依赖: C_simp, Int.even_add, Int.even_sub, Int.not_even_one, even_add, even_sub, even_two, even_two_mul, if_pos, iff_false, iff_true, not_even_one, simp_rw, split_ifs
-/
lemma Ψ_even (m : Int) : W.Ψ (2 * m) * W.ψ₂ =
    W.Ψ (m - 1) ^ 2 * W.Ψ m * W.Ψ (m + 2) - W.Ψ (m - 2) * W.Ψ m * W.Ψ (m + 1) ^ 2 := by
  simp_rw [Ψ, preΨ_even, if_pos <| even_two_mul m, Int.even_add, Int.even_sub, even_two, iff_true,
    Int.not_even_one, iff_false]
  split_ifs <;> C_simp <;> ring1

/--
lemma `Ψ_odd` / 引理 `Ψ_odd`

English:
lemma Ψ_odd
  given: (m : Int)
  statement: W.Ψ (2 * m + 1) =
  proof: by
  simp_rw [Ψ, preΨ_odd, if_neg m.not_even_two_mul_add_one, Int.even_add, Int.even_sub, even_two,
    iff_true, Int.not_even_one, iff_false]
  split_ifs <;> C_simp <;> rw [C_Ψ₂Sq] <;> ring1

中文:
引理 Ψ_odd
  条件: (m : 整数)
  结论: W.Ψ (2 * m + 1) =
  证明: by
  simp_rw [Ψ, preΨ_odd, if_neg m.not_even_two_mul_add_one, Int.even_add, Int.even_sub, even_two,
    iff_true, Int.not_even_one, iff_false]
  split_ifs <;> C_simp <;> rw [C_Ψ₂Sq] <;> ring1

Depends on / 依赖: C_simp, Int.even_add, Int.even_sub, Int.not_even_one, comp_id, even_add, even_sub, even_two, f.left, f.right, if_neg, iff_false, iff_true, m.not_even_two_mul_add_one, not_even_one, not_even_two_mul_add_one, simp_rw, split_ifs
-/
lemma Ψ_odd (m : Int) : W.Ψ (2 * m + 1) =
    W.Ψ (m + 2) * W.Ψ m ^ 3 - W.Ψ (m - 1) * W.Ψ (m + 1) ^ 3 +
      W.toAffine.polynomial * (16 * W.toAffine.polynomial - 8 * W.ψ₂ ^ 2) *
        C (if Even m then W.preΨ (m + 2) * W.preΨ m ^ 3
            else -W.preΨ (m - 1) * W.preΨ (m + 1) ^ 3) := by
  simp_rw [Ψ, preΨ_odd, if_neg m.not_even_two_mul_add_one, Int.even_add, Int.even_sub, even_two,
    iff_true, Int.not_even_one, iff_false]
  split_ifs <;> C_simp <;> rw [C_Ψ₂Sq] <;> ring1

/--
lemma `Affine.CoordinateRing.mk_Ψ_sq` / 引理 `Affine.CoordinateRing.mk_Ψ_sq`

English:
lemma Affine.CoordinateRing.mk_Ψ_sq
  given: (n : Int)
  statement: mk W (W.Ψ n) ^ 2 = mk W (C <| W.ΨSq n)
  proof: by
  simp_rw [Ψ, ΨSq, map_mul, apply_ite C, apply_ite <| mk W, mul_pow, ite_pow, mk_ψ₂_sq, map_one,
    one_pow, map_pow]

中文:
引理 仿射.CoordinateRing.mk_Ψ_sq
  条件: (n : 整数)
  结论: mk W (W.Ψ n) ^ 2 = mk W (C <| W.ΨSq n)
  证明: by
  simp_rw [Ψ, ΨSq, map_mul, apply_ite C, apply_ite <| mk W, mul_pow, ite_pow, mk_ψ₂_sq, map_one,
    one_pow, map_pow]

Depends on / 依赖: apply_ite, ite_pow, map_mul, map_one, map_pow, mul_pow, one_pow, simp_rw
-/
lemma Affine.CoordinateRing.mk_Ψ_sq (n : Int) : mk W (W.Ψ n) ^ 2 = mk W (C <| W.ΨSq n) := by
  simp_rw [Ψ, ΨSq, map_mul, apply_ite C, apply_ite <| mk W, mul_pow, ite_pow, mk_ψ₂_sq, map_one,
    one_pow, map_pow]

end Ψ

section Φ

/-! ### The univariate polynomials `Φₙ` -/

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def Φ (n : Int)
  body: X * W.ΨSq n - W.preΨ (n + 1) * W.preΨ (n - 1) * if Even n then 1 else W.Ψ₂Sq

中文:
定义 noncomputable
  签名: def Φ (n : 整数)
  定义体: X * W.ΨSq n - W.preΨ (n + 1) * W.preΨ (n - 1) * if Even n then 1 else W.Ψ₂Sq
-/
protected noncomputable def Φ (n : Int) : R[X] :=
  X * W.ΨSq n - W.preΨ (n + 1) * W.preΨ (n - 1) * if Even n then 1 else W.Ψ₂Sq

open WeierstrassCurve (Φ)

@[simp]
/--
lemma `Φ_ofNat` / 引理 `Φ_ofNat`

English:
lemma Φ_ofNat
  given: (n : Nat)
  statement: W.Φ (n + 1) =
  proof: by
  rw [Φ]; rw [add_sub_cancel_right]
  norm_cast
  simp_rw [ΨSq_ofNat, Nat.even_add_one, ite_not, ← mul_assoc, preΨ_ofNat]

@[simp]

中文:
引理 Φ_of自然数
  条件: (n : 自然数)
  结论: W.Φ (n + 1) =
  证明: by
  rw [Φ]; rw [add_sub_cancel_right]
  norm_cast
  simp_rw [ΨSq_ofNat, Nat.even_add_one, ite_not, ← mul_assoc, preΨ_ofNat]

@[simp]

Depends on / 依赖: Nat.even_add_one, add_sub_cancel_right, even_add_one, ite_not, mul_assoc, simp_rw
-/
lemma Φ_ofNat (n : Nat) : W.Φ (n + 1) =
    X * W.preΨ' (n + 1) ^ 2 * (if Even n then 1 else W.Ψ₂Sq) -
      W.preΨ' (n + 2) * W.preΨ' n * (if Even n then W.Ψ₂Sq else 1) := by
  rw [Φ]; rw [add_sub_cancel_right]
  norm_cast
  simp_rw [ΨSq_ofNat, Nat.even_add_one, ite_not, ← mul_assoc, preΨ_ofNat]

@[simp]
/--
lemma `Φ_zero` / 引理 `Φ_zero`

English:
lemma Φ_zero
  statement: W.Φ 0 = 1
  proof: by
  simp [Φ]

@[simp]

中文:
引理 Φ_zero
  结论: W.Φ 0 = 1
  证明: by
  simp [Φ]

@[simp]
-/
lemma Φ_zero : W.Φ 0 = 1 := by
  simp [Φ]

@[simp]
/--
lemma `Φ_one` / 引理 `Φ_one`

English:
lemma Φ_one
  statement: W.Φ 1 = X
  proof: by
  simp [Φ]

@[simp]

中文:
引理 Φ_one
  结论: W.Φ 1 = X
  证明: by
  simp [Φ]

@[simp]
-/
lemma Φ_one : W.Φ 1 = X := by
  simp [Φ]

@[simp]
/--
lemma `Φ_two` / 引理 `Φ_two`

English:
lemma Φ_two
  statement: W.Φ 2 = X ^ 4 - C W.b₄ * X ^ 2 - C (2 * W.b₆) * X - C W.b₈
  proof: by
  rw [show 2 = ((1 : Nat) + 1 : Int) by rfl]; rw [Φ_ofNat]; rw [preΨ'_two]; rw [if_neg Nat.not_even_one]; rw [Ψ₂Sq]; rw [preΨ'_three]; rw [preΨ'_one]; rw [if_neg Nat.not_even_one]; rw [Ψ₃]
  C_simp
  ring1

@[simp]

中文:
引理 Φ_two
  结论: W.Φ 2 = X ^ 4 - C W.b₄ * X ^ 2 - C (2 * W.b₆) * X - C W.b₈
  证明: by
  rw [show 2 = ((1 : Nat) + 1 : Int) by rfl]; rw [Φ_ofNat]; rw [preΨ'_two]; rw [if_neg Nat.not_even_one]; rw [Ψ₂Sq]; rw [preΨ'_three]; rw [preΨ'_one]; rw [if_neg Nat.not_even_one]; rw [Ψ₃]
  C_simp
  ring1

@[simp]

Depends on / 依赖: C_simp, Nat.not_even_one, _one, _three, _two, if_neg, not_even_one
-/
lemma Φ_two : W.Φ 2 = X ^ 4 - C W.b₄ * X ^ 2 - C (2 * W.b₆) * X - C W.b₈ := by
  rw [show 2 = ((1 : Nat) + 1 : Int) by rfl]; rw [Φ_ofNat]; rw [preΨ'_two]; rw [if_neg Nat.not_even_one]; rw [Ψ₂Sq]; rw [preΨ'_three]; rw [preΨ'_one]; rw [if_neg Nat.not_even_one]; rw [Ψ₃]
  C_simp
  ring1

@[simp]
/--
lemma `Φ_three` / 引理 `Φ_three`

English:
lemma Φ_three
  statement: W.Φ 3 = X * W.Ψ₃ ^ 2 - W.preΨ₄ * W.Ψ₂Sq
  proof: by
  rw [show 3 = ((2 : Nat) + 1 : Int) by rfl]; rw [Φ_ofNat]; rw [preΨ'_three]; rw [if_pos <| by decide]; rw [mul_one]; rw [preΨ'_four]; rw [preΨ'_two]; rw [mul_one]; rw [if_pos even_two]

@[simp]

中文:
引理 Φ_three
  结论: W.Φ 3 = X * W.Ψ₃ ^ 2 - W.preΨ₄ * W.Ψ₂Sq
  证明: by
  rw [show 3 = ((2 : Nat) + 1 : Int) by rfl]; rw [Φ_ofNat]; rw [preΨ'_three]; rw [if_pos <| by decide]; rw [mul_one]; rw [preΨ'_four]; rw [preΨ'_two]; rw [mul_one]; rw [if_pos even_two]

@[simp]

Depends on / 依赖: _four, _three, _two, even_two, if_pos, mul_one
-/
lemma Φ_three : W.Φ 3 = X * W.Ψ₃ ^ 2 - W.preΨ₄ * W.Ψ₂Sq := by
  rw [show 3 = ((2 : Nat) + 1 : Int) by rfl]; rw [Φ_ofNat]; rw [preΨ'_three]; rw [if_pos <| by decide]; rw [mul_one]; rw [preΨ'_four]; rw [preΨ'_two]; rw [mul_one]; rw [if_pos even_two]

@[simp]
/--
lemma `Φ_four` / 引理 `Φ_four`

English:
lemma Φ_four
  statement: W.Φ 4 = X * W.preΨ₄ ^ 2 * W.Ψ₂Sq - W.Ψ₃ * (W.preΨ₄ * W.Ψ₂Sq ^ 2 - W.Ψ₃ ^ 3)
  proof: by
  rw [show 4 = ((3 : Nat) + 1 : Int) by rfl]; rw [Φ_ofNat]; rw [preΨ'_four]; rw [if_neg <| by decide]; rw [show 3 + 2 = 2 * 2 + 1 by rfl]; rw [preΨ'_odd]; rw [preΨ'_four]; rw [preΨ'_two]; rw [if_pos Even.zero]; rw [preΨ'_one]; rw [preΨ'_three]; rw [if_pos Even.zero]; rw [if_neg by decide]
  ring1

中文:
引理 Φ_four
  结论: W.Φ 4 = X * W.preΨ₄ ^ 2 * W.Ψ₂Sq - W.Ψ₃ * (W.preΨ₄ * W.Ψ₂Sq ^ 2 - W.Ψ₃ ^ 3)
  证明: by
  rw [show 4 = ((3 : Nat) + 1 : Int) by rfl]; rw [Φ_ofNat]; rw [preΨ'_four]; rw [if_neg <| by decide]; rw [show 3 + 2 = 2 * 2 + 1 by rfl]; rw [preΨ'_odd]; rw [preΨ'_four]; rw [preΨ'_two]; rw [if_pos Even.zero]; rw [preΨ'_one]; rw [preΨ'_three]; rw [if_pos Even.zero]; rw [if_neg by decide]
  ring1

Depends on / 依赖: Even.zero, _four, _odd, _one, _three, _two, if_neg, if_pos
-/
lemma Φ_four : W.Φ 4 = X * W.preΨ₄ ^ 2 * W.Ψ₂Sq - W.Ψ₃ * (W.preΨ₄ * W.Ψ₂Sq ^ 2 - W.Ψ₃ ^ 3) := by
  rw [show 4 = ((3 : Nat) + 1 : Int) by rfl]; rw [Φ_ofNat]; rw [preΨ'_four]; rw [if_neg <| by decide]; rw [show 3 + 2 = 2 * 2 + 1 by rfl]; rw [preΨ'_odd]; rw [preΨ'_four]; rw [preΨ'_two]; rw [if_pos Even.zero]; rw [preΨ'_one]; rw [preΨ'_three]; rw [if_pos Even.zero]; rw [if_neg by decide]
  ring1

@[simp]
/--
lemma `Φ_neg` / 引理 `Φ_neg`

English:
lemma Φ_neg
  given: (n : Int)
  statement: W.Φ (-n) = W.Φ n
  proof: by
  simp_rw [Φ, ΨSq_neg, ← sub_neg_eq_add, ← neg_sub', sub_neg_eq_add, ← neg_add', preΨ_neg,
neg_mul_neg, mul_comm W.preΨ n - 1, even_neg]

中文:
引理 Φ_neg
  条件: (n : 整数)
  结论: W.Φ (-n) = W.Φ n
  证明: by
  simp_rw [Φ, ΨSq_neg, ← sub_neg_eq_add, ← neg_sub', sub_neg_eq_add, ← neg_add', preΨ_neg,
neg_mul_neg, mul_comm W.preΨ n - 1, even_neg]

Depends on / 依赖: W.pre, even_neg, mul_comm, neg_add, neg_mul_neg, neg_sub, simp_rw, sub_neg_eq_add
-/
lemma Φ_neg (n : Int) : W.Φ (-n) = W.Φ n := by
  simp_rw [Φ, ΨSq_neg, ← sub_neg_eq_add, ← neg_sub', sub_neg_eq_add, ← neg_add', preΨ_neg,
neg_mul_neg, mul_comm W.preΨ n - 1, even_neg]

end Φ

section ψ

/-! ### The bivariate polynomials `ψₙ` -/

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def ψ (n : Int)
  body: normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n

中文:
定义 noncomputable
  签名: def ψ (n : 整数)
  定义体: normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n
-/
protected noncomputable def ψ (n : Int) : R[X][Y] :=
  normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n

open WeierstrassCurve (Ψ ψ)

@[simp]
/--
lemma `ψ_zero` / 引理 `ψ_zero`

English:
lemma ψ_zero
  statement: W.ψ 0 = 0
  proof: normEDS_zero ..

@[simp]

中文:
引理 ψ_zero
  结论: W.ψ 0 = 0
  证明: normEDS_zero ..

@[simp]

Depends on / 依赖: normEDS_zero
-/
lemma ψ_zero : W.ψ 0 = 0 :=
  normEDS_zero ..

@[simp]
/--
lemma `ψ_one` / 引理 `ψ_one`

English:
lemma ψ_one
  statement: W.ψ 1 = 1
  proof: normEDS_one ..

@[simp]

中文:
引理 ψ_one
  结论: W.ψ 1 = 1
  证明: normEDS_one ..

@[simp]

Depends on / 依赖: normEDS_one
-/
lemma ψ_one : W.ψ 1 = 1 :=
  normEDS_one ..

@[simp]
/--
lemma `ψ_two` / 引理 `ψ_two`

English:
lemma ψ_two
  statement: W.ψ 2 = W.ψ₂
  proof: normEDS_two ..

@[simp]

中文:
引理 ψ_two
  结论: W.ψ 2 = W.ψ₂
  证明: normEDS_two ..

@[simp]

Depends on / 依赖: normEDS_two
-/
lemma ψ_two : W.ψ 2 = W.ψ₂ :=
  normEDS_two ..

@[simp]
/--
lemma `ψ_three` / 引理 `ψ_three`

English:
lemma ψ_three
  statement: W.ψ 3 = C W.Ψ₃
  proof: normEDS_three ..

@[simp]

中文:
引理 ψ_three
  结论: W.ψ 3 = C W.Ψ₃
  证明: normEDS_three ..

@[simp]

Depends on / 依赖: normEDS_three
-/
lemma ψ_three : W.ψ 3 = C W.Ψ₃ :=
  normEDS_three ..

@[simp]
/--
lemma `ψ_four` / 引理 `ψ_four`

English:
lemma ψ_four
  statement: W.ψ 4 = C W.preΨ₄ * W.ψ₂
  proof: normEDS_four ..

@[simp]

中文:
引理 ψ_four
  结论: W.ψ 4 = C W.preΨ₄ * W.ψ₂
  证明: normEDS_four ..

@[simp]

Depends on / 依赖: normEDS_four
-/
lemma ψ_four : W.ψ 4 = C W.preΨ₄ * W.ψ₂ :=
  normEDS_four ..

@[simp]
/--
lemma `ψ_neg` / 引理 `ψ_neg`

English:
lemma ψ_neg
  given: (n : Int)
  statement: W.ψ (-n) = -W.ψ n
  proof: normEDS_neg ..

中文:
引理 ψ_neg
  条件: (n : 整数)
  结论: W.ψ (-n) = -W.ψ n
  证明: normEDS_neg ..

Depends on / 依赖: normEDS_neg
-/
lemma ψ_neg (n : Int) : W.ψ (-n) = -W.ψ n :=
  normEDS_neg ..

/--
lemma `ψ_even` / 引理 `ψ_even`

English:
lemma ψ_even
  given: (m : Int)
  statement: W.ψ (2 * m) * W.ψ₂ =
  proof: normEDS_even ..

中文:
引理 ψ_even
  条件: (m : 整数)
  结论: W.ψ (2 * m) * W.ψ₂ =
  证明: normEDS_even ..

Depends on / 依赖: normEDS_even
-/
lemma ψ_even (m : Int) : W.ψ (2 * m) * W.ψ₂ =
    W.ψ (m - 1) ^ 2 * W.ψ m * W.ψ (m + 2) - W.ψ (m - 2) * W.ψ m * W.ψ (m + 1) ^ 2 :=
  normEDS_even ..

/--
lemma `ψ_odd` / 引理 `ψ_odd`

English:
lemma ψ_odd
  given: (m : Int)
  statement: W.ψ (2 * m + 1) =
  proof: normEDS_odd ..

中文:
引理 ψ_odd
  条件: (m : 整数)
  结论: W.ψ (2 * m + 1) =
  证明: normEDS_odd ..

Depends on / 依赖: normEDS_odd
-/
lemma ψ_odd (m : Int) : W.ψ (2 * m + 1) =
    W.ψ (m + 2) * W.ψ m ^ 3 - W.ψ (m - 1) * W.ψ (m + 1) ^ 3 :=
  normEDS_odd ..

/--
lemma `Affine.CoordinateRing.mk_ψ` / 引理 `Affine.CoordinateRing.mk_ψ`

English:
lemma Affine.CoordinateRing.mk_ψ
  given: (n : Int)
  statement: mk W (W.ψ n) = mk W (W.Ψ n)
  proof: by
  simp_rw [ψ, normEDS, Ψ, preΨ, map_mul, map_preNormEDS, map_pow, ← mk_ψ₂_sq, ← pow_mul]

中文:
引理 仿射.CoordinateRing.mk_ψ
  条件: (n : 整数)
  结论: mk W (W.ψ n) = mk W (W.Ψ n)
  证明: by
  simp_rw [ψ, normEDS, Ψ, preΨ, map_mul, map_preNormEDS, map_pow, ← mk_ψ₂_sq, ← pow_mul]

Depends on / 依赖: map_mul, map_pow, map_preNormEDS, normEDS, pow_mul, simp_rw
-/
lemma Affine.CoordinateRing.mk_ψ (n : Int) : mk W (W.ψ n) = mk W (W.Ψ n) := by
  simp_rw [ψ, normEDS, Ψ, preΨ, map_mul, map_preNormEDS, map_pow, ← mk_ψ₂_sq, ← pow_mul]

end ψ

section φ

/-! ### The bivariate polynomials `φₙ` -/

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def φ (n : Int)
  body: C X * W.ψ n ^ 2 - W.ψ (n + 1) * W.ψ (n - 1)

中文:
定义 noncomputable
  签名: def φ (n : 整数)
  定义体: C X * W.ψ n ^ 2 - W.ψ (n + 1) * W.ψ (n - 1)

Depends on / 依赖: infer_instance
-/
protected noncomputable def φ (n : Int) : R[X][Y] :=
  C X * W.ψ n ^ 2 - W.ψ (n + 1) * W.ψ (n - 1)

open WeierstrassCurve (Ψ Φ φ)

@[simp]
/--
lemma `φ_zero` / 引理 `φ_zero`

English:
lemma φ_zero
  statement: W.φ 0 = 1
  proof: by
  simp [φ]

@[simp]

中文:
引理 φ_zero
  结论: W.φ 0 = 1
  证明: by
  simp [φ]

@[simp]

Depends on / 依赖: Nonempty
-/
lemma φ_zero : W.φ 0 = 1 := by
  simp [φ]

@[simp]
/--
lemma `φ_one` / 引理 `φ_one`

English:
lemma φ_one
  statement: W.φ 1 = C X
  proof: by
  simp [φ]

@[simp]

中文:
引理 φ_one
  结论: W.φ 1 = C X
  证明: by
  simp [φ]

@[simp]
-/
lemma φ_one : W.φ 1 = C X := by
  simp [φ]

@[simp]
/--
lemma `φ_two` / 引理 `φ_two`

English:
lemma φ_two
  statement: W.φ 2 = C X * W.ψ₂ ^ 2 - C W.Ψ₃
  proof: by
  simp [φ]

@[simp]

中文:
引理 φ_two
  结论: W.φ 2 = C X * W.ψ₂ ^ 2 - C W.Ψ₃
  证明: by
  simp [φ]

@[simp]
-/
lemma φ_two : W.φ 2 = C X * W.ψ₂ ^ 2 - C W.Ψ₃ := by
  simp [φ]

@[simp]
/--
lemma `φ_three` / 引理 `φ_three`

English:
lemma φ_three
  statement: W.φ 3 = C X * C W.Ψ₃ ^ 2 - C W.preΨ₄ * W.ψ₂ ^ 2
  proof: by
  simp [φ, mul_assoc, sq]

@[simp]

中文:
引理 φ_three
  结论: W.φ 3 = C X * C W.Ψ₃ ^ 2 - C W.preΨ₄ * W.ψ₂ ^ 2
  证明: by
  simp [φ, mul_assoc, sq]

@[simp]

Depends on / 依赖: infer_instance, mul_assoc
-/
lemma φ_three : W.φ 3 = C X * C W.Ψ₃ ^ 2 - C W.preΨ₄ * W.ψ₂ ^ 2 := by
  simp [φ, mul_assoc, sq]

@[simp]
/--
lemma `φ_four` / 引理 `φ_four`

English:
lemma φ_four
  proof: by
  rw [φ]; rw [ψ_four]; rw [show (4 + 1 : Int) = 2 * 2 + 1 by rfl]; rw [ψ_odd]; rw [two_add_two_eq_four]; rw [ψ_four]; rw [show (2 - 1 : Int) = 1 by rfl]; rw [ψ_two]; rw [ψ_one]; rw [two_add_one_eq_three]; rw [show (4 - 1 : Int) = 3 by rfl]; rw [ψ_three]
  ring1

@[simp]

中文:
引理 φ_four
  证明: by
  rw [φ]; rw [ψ_four]; rw [show (4 + 1 : Int) = 2 * 2 + 1 by rfl]; rw [ψ_odd]; rw [two_add_two_eq_four]; rw [ψ_four]; rw [show (2 - 1 : Int) = 1 by rfl]; rw [ψ_two]; rw [ψ_one]; rw [two_add_one_eq_three]; rw [show (4 - 1 : Int) = 3 by rfl]; rw [ψ_three]
  ring1

@[simp]

Depends on / 依赖: ULift.up_surjective.pathConnectedSpace, continuous_uliftUp, pathConnectedSpace, two_add_one_eq_three, two_add_two_eq_four, up_surjective
-/
lemma φ_four :
    W.φ 4 = C X * C W.preΨ₄ ^ 2 * W.ψ₂ ^ 2 - C W.preΨ₄ * W.ψ₂ ^ 4 * C W.Ψ₃ + C W.Ψ₃ ^ 4 := by
  rw [φ]; rw [ψ_four]; rw [show (4 + 1 : Int) = 2 * 2 + 1 by rfl]; rw [ψ_odd]; rw [two_add_two_eq_four]; rw [ψ_four]; rw [show (2 - 1 : Int) = 1 by rfl]; rw [ψ_two]; rw [ψ_one]; rw [two_add_one_eq_three]; rw [show (4 - 1 : Int) = 3 by rfl]; rw [ψ_three]
  ring1

@[simp]
/--
lemma `φ_neg` / 引理 `φ_neg`

English:
lemma φ_neg
  given: (n : Int)
  statement: W.φ (-n) = W.φ n
  proof: by
  simp_rw [φ, ψ_neg, neg_sq, ← sub_neg_eq_add, ← neg_sub', sub_neg_eq_add, ← neg_add', ψ_neg,
neg_mul_neg, mul_comm W.ψ n - 1]

中文:
引理 φ_neg
  条件: (n : 整数)
  结论: W.φ (-n) = W.φ n
  证明: by
  simp_rw [φ, ψ_neg, neg_sq, ← sub_neg_eq_add, ← neg_sub', sub_neg_eq_add, ← neg_add', ψ_neg,
neg_mul_neg, mul_comm W.ψ n - 1]

Depends on / 依赖: mul_comm, neg_add, neg_mul_neg, neg_sq, neg_sub, simp_rw, sub_neg_eq_add
-/
lemma φ_neg (n : Int) : W.φ (-n) = W.φ n := by
  simp_rw [φ, ψ_neg, neg_sq, ← sub_neg_eq_add, ← neg_sub', sub_neg_eq_add, ← neg_add', ψ_neg,
neg_mul_neg, mul_comm W.ψ n - 1]

/--
lemma `Affine.CoordinateRing.mk_φ` / 引理 `Affine.CoordinateRing.mk_φ`

English:
lemma Affine.CoordinateRing.mk_φ
  given: (n : Int)
  statement: mk W (W.φ n) = mk W (C <| W.Φ n)
  proof: by
  simp_rw [φ, Φ, map_sub, map_mul, map_pow, mk_ψ, mk_Ψ_sq, Ψ, map_mul,
mul_mul_mul_comm _ mk W ite .., Int.even_add_one, Int.even_sub_one, ite_not, ← sq,
apply_ite C, apply_ite mk W, ite_pow, map_one, one_pow, mk_ψ₂_sq]

中文:
引理 仿射.CoordinateRing.mk_φ
  条件: (n : 整数)
  结论: mk W (W.φ n) = mk W (C <| W.Φ n)
  证明: by
  simp_rw [φ, Φ, map_sub, map_mul, map_pow, mk_ψ, mk_Ψ_sq, Ψ, map_mul,
mul_mul_mul_comm _ mk W ite .., Int.even_add_one, Int.even_sub_one, ite_not, ← sq,
apply_ite C, apply_ite mk W, ite_pow, map_one, one_pow, mk_ψ₂_sq]

Depends on / 依赖: Int.even_add_one, Int.even_sub_one, apply_ite, even_add_one, even_sub_one, ite_not, ite_pow, map_mul, map_one, map_pow, map_sub, mul_mul_mul_comm, one_pow, simp_rw
-/
lemma Affine.CoordinateRing.mk_φ (n : Int) : mk W (W.φ n) = mk W (C <| W.Φ n) := by
  simp_rw [φ, Φ, map_sub, map_mul, map_pow, mk_ψ, mk_Ψ_sq, Ψ, map_mul,
mul_mul_mul_comm _ mk W ite .., Int.even_add_one, Int.even_sub_one, ite_not, ← sq,
apply_ite C, apply_ite mk W, ite_pow, map_one, one_pow, mk_ψ₂_sq]

end φ

section Map

/-! ### Maps across ring homomorphisms -/

open WeierstrassCurve (Ψ Φ ψ φ)

variable (f : R ->+* S)

@[simp]
/--
lemma `map_ψ₂` / 引理 `map_ψ₂`

English:
lemma map_ψ₂
  statement: (W.map f).ψ₂ = W.ψ₂.map (mapRingHom f)
  proof: by
  simp_rw [ψ₂, Affine.map_polynomialY]

@[simp]

中文:
引理 map_ψ₂
  结论: (W.map f).ψ₂ = W.ψ₂.map (mapRingHom f)
  证明: by
  simp_rw [ψ₂, Affine.map_polynomialY]

@[simp]

Depends on / 依赖: Affine, Affine.map_polynomialY, map_polynomialY, simp_rw
-/
lemma map_ψ₂ : (W.map f).ψ₂ = W.ψ₂.map (mapRingHom f) := by
  simp_rw [ψ₂, Affine.map_polynomialY]

@[simp]
/--
lemma `map_Ψ₂Sq` / 引理 `map_Ψ₂Sq`

English:
lemma map_Ψ₂Sq
  statement: (W.map f).Ψ₂Sq = W.Ψ₂Sq.map f
  proof: by
  simp [Ψ₂Sq, map_ofNat]

@[simp]

中文:
引理 map_Ψ₂Sq
  结论: (W.map f).Ψ₂Sq = W.Ψ₂Sq.map f
  证明: by
  simp [Ψ₂Sq, map_ofNat]

@[simp]

Depends on / 依赖: map_ofNat
-/
lemma map_Ψ₂Sq : (W.map f).Ψ₂Sq = W.Ψ₂Sq.map f := by
  simp [Ψ₂Sq, map_ofNat]

@[simp]
/--
lemma `map_Ψ₃` / 引理 `map_Ψ₃`

English:
lemma map_Ψ₃
  statement: (W.map f).Ψ₃ = W.Ψ₃.map f
  proof: by
  simp [Ψ₃]

@[simp]

中文:
引理 map_Ψ₃
  结论: (W.map f).Ψ₃ = W.Ψ₃.map f
  证明: by
  simp [Ψ₃]

@[simp]
-/
lemma map_Ψ₃ : (W.map f).Ψ₃ = W.Ψ₃.map f := by
  simp [Ψ₃]

@[simp]
/--
lemma `map_preΨ₄` / 引理 `map_preΨ₄`

English:
lemma map_preΨ₄
  statement: (W.map f).preΨ₄ = W.preΨ₄.map f
  proof: by
  simp [preΨ₄]

@[simp]

中文:
引理 map_preΨ₄
  结论: (W.map f).preΨ₄ = W.preΨ₄.map f
  证明: by
  simp [preΨ₄]

@[simp]
-/
lemma map_preΨ₄ : (W.map f).preΨ₄ = W.preΨ₄.map f := by
  simp [preΨ₄]

@[simp]
/--
lemma `map_preΨ'` / 引理 `map_preΨ'`

English:
lemma map_preΨ'
  given: (n : Nat)
  statement: (W.map f).preΨ' n = (W.preΨ' n).map f
  proof: by
  simp [preΨ', ← coe_mapRingHom]

@[simp]

中文:
引理 map_preΨ'
  条件: (n : 自然数)
  结论: (W.map f).preΨ' n = (W.preΨ' n).map f
  证明: by
  simp [preΨ', ← coe_mapRingHom]

@[simp]

Depends on / 依赖: coe_mapRingHom
-/
lemma map_preΨ' (n : Nat) : (W.map f).preΨ' n = (W.preΨ' n).map f := by
  simp [preΨ', ← coe_mapRingHom]

@[simp]
/--
lemma `map_preΨ` / 引理 `map_preΨ`

English:
lemma map_preΨ
  given: (n : Int)
  statement: (W.map f).preΨ n = (W.preΨ n).map f
  proof: by
  simp [preΨ, ← coe_mapRingHom]

@[simp]

中文:
引理 map_preΨ
  条件: (n : 整数)
  结论: (W.map f).preΨ n = (W.preΨ n).map f
  证明: by
  simp [preΨ, ← coe_mapRingHom]

@[simp]

Depends on / 依赖: coe_mapRingHom
-/
lemma map_preΨ (n : Int) : (W.map f).preΨ n = (W.preΨ n).map f := by
  simp [preΨ, ← coe_mapRingHom]

@[simp]
/--
lemma `map_ΨSq` / 引理 `map_ΨSq`

English:
lemma map_ΨSq
  given: (n : Int)
  statement: (W.map f).ΨSq n = (W.ΨSq n).map f
  proof: by
  simp [ΨSq, ← coe_mapRingHom, apply_ite <| mapRingHom f]

@[simp]

中文:
引理 map_ΨSq
  条件: (n : 整数)
  结论: (W.map f).ΨSq n = (W.ΨSq n).map f
  证明: by
  simp [ΨSq, ← coe_mapRingHom, apply_ite <| mapRingHom f]

@[simp]

Depends on / 依赖: apply_ite, coe_mapRingHom, mapRingHom
-/
lemma map_ΨSq (n : Int) : (W.map f).ΨSq n = (W.ΨSq n).map f := by
  simp [ΨSq, ← coe_mapRingHom, apply_ite <| mapRingHom f]

@[simp]
/--
lemma `map_Ψ` / 引理 `map_Ψ`

English:
lemma map_Ψ
  given: (n : Int)
  statement: (W.map f).Ψ n = (W.Ψ n).map (mapRingHom f)
  proof: by
  rw [← coe_mapRingHom]
  simp [Ψ, apply_ite <| mapRingHom _]

@[simp]

中文:
引理 map_Ψ
  条件: (n : 整数)
  结论: (W.map f).Ψ n = (W.Ψ n).map (mapRingHom f)
  证明: by
  rw [← coe_mapRingHom]
  simp [Ψ, apply_ite <| mapRingHom _]

@[simp]

Depends on / 依赖: apply_ite, coe_mapRingHom, mapRingHom
-/
lemma map_Ψ (n : Int) : (W.map f).Ψ n = (W.Ψ n).map (mapRingHom f) := by
  rw [← coe_mapRingHom]
  simp [Ψ, apply_ite <| mapRingHom _]

@[simp]
/--
lemma `map_Φ` / 引理 `map_Φ`

English:
lemma map_Φ
  given: (n : Int)
  statement: (W.map f).Φ n = (W.Φ n).map f
  proof: by
  rw [← coe_mapRingHom]
  simp [Φ, map_sub, apply_ite <| mapRingHom f]

@[simp]

中文:
引理 map_Φ
  条件: (n : 整数)
  结论: (W.map f).Φ n = (W.Φ n).map f
  证明: by
  rw [← coe_mapRingHom]
  simp [Φ, map_sub, apply_ite <| mapRingHom f]

@[simp]

Depends on / 依赖: apply_ite, coe_mapRingHom, mapRingHom, map_sub
-/
lemma map_Φ (n : Int) : (W.map f).Φ n = (W.Φ n).map f := by
  rw [← coe_mapRingHom]
  simp [Φ, map_sub, apply_ite <| mapRingHom f]

@[simp]
/--
lemma `map_ψ` / 引理 `map_ψ`

English:
lemma map_ψ
  given: (n : Int)
  statement: (W.map f).ψ n = (W.ψ n).map (mapRingHom f)
  proof: by
  rw [← coe_mapRingHom]
  simp [ψ]

@[simp]

中文:
引理 map_ψ
  条件: (n : 整数)
  结论: (W.map f).ψ n = (W.ψ n).map (mapRingHom f)
  证明: by
  rw [← coe_mapRingHom]
  simp [ψ]

@[simp]

Depends on / 依赖: coe_mapRingHom
-/
lemma map_ψ (n : Int) : (W.map f).ψ n = (W.ψ n).map (mapRingHom f) := by
  rw [← coe_mapRingHom]
  simp [ψ]

@[simp]
/--
lemma `map_φ` / 引理 `map_φ`

English:
lemma map_φ
  given: (n : Int)
  statement: (W.map f).φ n = (W.φ n).map (mapRingHom f)
  proof: by
  simp [φ]

中文:
引理 map_φ
  条件: (n : 整数)
  结论: (W.map f).φ n = (W.φ n).map (mapRingHom f)
  证明: by
  simp [φ]
-/
lemma map_φ (n : Int) : (W.map f).φ n = (W.φ n).map (mapRingHom f) := by
  simp [φ]

end Map

section BaseChange

/-! ### Base changes across algebra homomorphisms -/

variable [Algebra R S] {A : Type u} [CommRing A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
  {B : Type v} [CommRing B] [Algebra R B] [Algebra S B] [IsScalarTower R S B] (f : A ->ₐ[S] B)

/--
lemma `baseChange_ψ₂` / 引理 `baseChange_ψ₂`

English:
lemma baseChange_ψ₂
  statement: (W⁄B).ψ₂ = (W⁄A).ψ₂.map (mapRingHom f)
  proof: by
  rw [← map_ψ₂]; rw [map_baseChange]

中文:
引理 baseChange_ψ₂
  结论: (W⁄B).ψ₂ = (W⁄A).ψ₂.map (mapRingHom f)
  证明: by
  rw [← map_ψ₂]; rw [map_baseChange]

Depends on / 依赖: map_baseChange
-/
lemma baseChange_ψ₂ : (W⁄B).ψ₂ = (W⁄A).ψ₂.map (mapRingHom f) := by
  rw [← map_ψ₂]; rw [map_baseChange]

/--
lemma `baseChange_Ψ₂Sq` / 引理 `baseChange_Ψ₂Sq`

English:
lemma baseChange_Ψ₂Sq
  statement: (W⁄B).Ψ₂Sq = (W⁄A).Ψ₂Sq.map f
  proof: by
  rw [← map_Ψ₂Sq]; rw [map_baseChange]

中文:
引理 baseChange_Ψ₂Sq
  结论: (W⁄B).Ψ₂Sq = (W⁄A).Ψ₂Sq.map f
  证明: by
  rw [← map_Ψ₂Sq]; rw [map_baseChange]

Depends on / 依赖: map_baseChange
-/
lemma baseChange_Ψ₂Sq : (W⁄B).Ψ₂Sq = (W⁄A).Ψ₂Sq.map f := by
  rw [← map_Ψ₂Sq]; rw [map_baseChange]

/--
lemma `baseChange_Ψ₃` / 引理 `baseChange_Ψ₃`

English:
lemma baseChange_Ψ₃
  statement: (W⁄B).Ψ₃ = (W⁄A).Ψ₃.map f
  proof: by
  rw [← map_Ψ₃]; rw [map_baseChange]

中文:
引理 baseChange_Ψ₃
  结论: (W⁄B).Ψ₃ = (W⁄A).Ψ₃.map f
  证明: by
  rw [← map_Ψ₃]; rw [map_baseChange]

Depends on / 依赖: map_baseChange
-/
lemma baseChange_Ψ₃ : (W⁄B).Ψ₃ = (W⁄A).Ψ₃.map f := by
  rw [← map_Ψ₃]; rw [map_baseChange]

/--
lemma `baseChange_preΨ₄` / 引理 `baseChange_preΨ₄`

English:
lemma baseChange_preΨ₄
  statement: (W⁄B).preΨ₄ = (W⁄A).preΨ₄.map f
  proof: by
  rw [← map_preΨ₄]; rw [map_baseChange]

中文:
引理 baseChange_preΨ₄
  结论: (W⁄B).preΨ₄ = (W⁄A).preΨ₄.map f
  证明: by
  rw [← map_preΨ₄]; rw [map_baseChange]

Depends on / 依赖: map_baseChange
-/
lemma baseChange_preΨ₄ : (W⁄B).preΨ₄ = (W⁄A).preΨ₄.map f := by
  rw [← map_preΨ₄]; rw [map_baseChange]

/--
lemma `baseChange_preΨ'` / 引理 `baseChange_preΨ'`

English:
lemma baseChange_preΨ'
  given: (n : Nat)
  statement: (W⁄B).preΨ' n = ((W⁄A).preΨ' n).map f
  proof: by
  rw [← map_preΨ']; rw [map_baseChange]

中文:
引理 baseChange_preΨ'
  条件: (n : 自然数)
  结论: (W⁄B).preΨ' n = ((W⁄A).preΨ' n).map f
  证明: by
  rw [← map_preΨ']; rw [map_baseChange]

Depends on / 依赖: map_baseChange
-/
lemma baseChange_preΨ' (n : Nat) : (W⁄B).preΨ' n = ((W⁄A).preΨ' n).map f := by
  rw [← map_preΨ']; rw [map_baseChange]

/--
lemma `baseChange_preΨ` / 引理 `baseChange_preΨ`

English:
lemma baseChange_preΨ
  given: (n : Int)
  statement: (W⁄B).preΨ n = ((W⁄A).preΨ n).map f
  proof: by
  rw [← map_preΨ]; rw [map_baseChange]

中文:
引理 baseChange_preΨ
  条件: (n : 整数)
  结论: (W⁄B).preΨ n = ((W⁄A).preΨ n).map f
  证明: by
  rw [← map_preΨ]; rw [map_baseChange]

Depends on / 依赖: map_baseChange
-/
lemma baseChange_preΨ (n : Int) : (W⁄B).preΨ n = ((W⁄A).preΨ n).map f := by
  rw [← map_preΨ]; rw [map_baseChange]

/--
lemma `baseChange_ΨSq` / 引理 `baseChange_ΨSq`

English:
lemma baseChange_ΨSq
  given: (n : Int)
  statement: (W⁄B).ΨSq n = ((W⁄A).ΨSq n).map f
  proof: by
  rw [← map_ΨSq]; rw [map_baseChange]

中文:
引理 baseChange_ΨSq
  条件: (n : 整数)
  结论: (W⁄B).ΨSq n = ((W⁄A).ΨSq n).map f
  证明: by
  rw [← map_ΨSq]; rw [map_baseChange]

Depends on / 依赖: map_baseChange
-/
lemma baseChange_ΨSq (n : Int) : (W⁄B).ΨSq n = ((W⁄A).ΨSq n).map f := by
  rw [← map_ΨSq]; rw [map_baseChange]

/--
lemma `baseChange_Ψ` / 引理 `baseChange_Ψ`

English:
lemma baseChange_Ψ
  given: (n : Int)
  statement: (W⁄B).Ψ n = ((W⁄A).Ψ n).map (mapRingHom f)
  proof: by
  rw [← map_Ψ]; rw [map_baseChange]

中文:
引理 baseChange_Ψ
  条件: (n : 整数)
  结论: (W⁄B).Ψ n = ((W⁄A).Ψ n).map (mapRingHom f)
  证明: by
  rw [← map_Ψ]; rw [map_baseChange]

Depends on / 依赖: map_baseChange
-/
lemma baseChange_Ψ (n : Int) : (W⁄B).Ψ n = ((W⁄A).Ψ n).map (mapRingHom f) := by
  rw [← map_Ψ]; rw [map_baseChange]

/--
lemma `baseChange_Φ` / 引理 `baseChange_Φ`

English:
lemma baseChange_Φ
  given: (n : Int)
  statement: (W⁄B).Φ n = ((W⁄A).Φ n).map f
  proof: by
  rw [← map_Φ]; rw [map_baseChange]

中文:
引理 baseChange_Φ
  条件: (n : 整数)
  结论: (W⁄B).Φ n = ((W⁄A).Φ n).map f
  证明: by
  rw [← map_Φ]; rw [map_baseChange]

Depends on / 依赖: map_baseChange
-/
lemma baseChange_Φ (n : Int) : (W⁄B).Φ n = ((W⁄A).Φ n).map f := by
  rw [← map_Φ]; rw [map_baseChange]

/--
lemma `baseChange_ψ` / 引理 `baseChange_ψ`

English:
lemma baseChange_ψ
  given: (n : Int)
  statement: (W⁄B).ψ n = ((W⁄A).ψ n).map (mapRingHom f)
  proof: by
  rw [← map_ψ]; rw [map_baseChange]

中文:
引理 baseChange_ψ
  条件: (n : 整数)
  结论: (W⁄B).ψ n = ((W⁄A).ψ n).map (mapRingHom f)
  证明: by
  rw [← map_ψ]; rw [map_baseChange]

Depends on / 依赖: map_baseChange
-/
lemma baseChange_ψ (n : Int) : (W⁄B).ψ n = ((W⁄A).ψ n).map (mapRingHom f) := by
  rw [← map_ψ]; rw [map_baseChange]

/--
lemma `baseChange_φ` / 引理 `baseChange_φ`

English:
lemma baseChange_φ
  given: (n : Int)
  statement: (W⁄B).φ n = ((W⁄A).φ n).map (mapRingHom f)
  proof: by
  rw [← map_φ]; rw [map_baseChange]

中文:
引理 baseChange_φ
  条件: (n : 整数)
  结论: (W⁄B).φ n = ((W⁄A).φ n).map (mapRingHom f)
  证明: by
  rw [← map_φ]; rw [map_baseChange]

Depends on / 依赖: map_baseChange
-/
lemma baseChange_φ (n : Int) : (W⁄B).φ n = ((W⁄A).φ n).map (mapRingHom f) := by
  rw [← map_φ]; rw [map_baseChange]

end BaseChange

end WeierstrassCurve
