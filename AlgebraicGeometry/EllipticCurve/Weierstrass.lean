/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, David Kurniadi Angdinata
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.CubicDiscriminant
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination

/-!
# Weierstrass equations of elliptic curves

This file defines the structure of an elliptic curve as a nonsingular Weierstrass curve given by a
Weierstrass equation, which is mathematically accurate in many cases but also good for computation.

## Mathematical background

Let `S` be a scheme. The actual category of elliptic curves over `S` is a large category, whose
objects are schemes `E` equipped with a map `E → S`, a section `S → E`, and some axioms (the map is
smooth and proper and the fibres are geometrically-connected one-dimensional group varieties). In
the special case where `S` is the spectrum of some commutative ring `R` whose Picard group is zero
(this includes all fields, all PIDs, and many other commutative rings) it can be shown (using a lot
of algebro-geometric machinery) that every elliptic curve `E` is a projective plane cubic isomorphic
to a Weierstrass curve given by the equation `Y² + a₁XY + a₃Y = X³ + a₂X² + a₄X + a₆` for some `aᵢ`
in `R`, and such that a certain quantity called the discriminant of `E` is a unit in `R`. If `R` is
a field, this quantity divides the discriminant of a cubic polynomial whose roots over a splitting
field of `R` are precisely the `X`-coordinates of the non-zero 2-torsion points of `E`.

## Main definitions

* `WeierstrassCurve`: a Weierstrass curve over a commutative ring.
* `WeierstrassCurve.Δ`: the discriminant of a Weierstrass curve.
* `WeierstrassCurve.map`: the Weierstrass curve mapped over a ring homomorphism.
* `WeierstrassCurve.twoTorsionPolynomial`: the 2-torsion polynomial of a Weierstrass curve.
* `WeierstrassCurve.IsElliptic`: typeclass asserting that a Weierstrass curve is an elliptic curve.
* `WeierstrassCurve.j`: the j-invariant of an elliptic curve.

## Main statements

* `WeierstrassCurve.twoTorsionPolynomial_discr`: the discriminant of a Weierstrass curve is a
  constant factor of the cubic discriminant of its 2-torsion polynomial.

## Implementation notes

The definition of elliptic curves in this file makes sense for all commutative rings `R`, but it
only gives a type which can be beefed up to a category which is equivalent to the category of
elliptic curves over the spectrum `Spec(R)` of `R` in the case that `R` has trivial Picard group
`Pic(R)` or, slightly more generally, when its 12-torsion is trivial. The issue is that for a
general ring `R`, there might be elliptic curves over `Spec(R)` in the sense of algebraic geometry
which are not globally defined by a cubic equation valid over the entire base.

## References

* [N Katz and B Mazur, *Arithmetic Moduli of Elliptic Curves*][katz_mazur]
* [P Deligne, *Courbes Elliptiques: Formulaire (d'après J. Tate)*][deligne_formulaire]
* [J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, weierstrass equation, j invariant
-/

@[expose] public section

local macro "map_simp" : tactic =>
  `(tactic| simp only [map_ofNat, map_neg, map_add, map_sub, map_mul, map_pow])

universe s u v w

/-! ## Weierstrass curves -/

/-- A Weierstrass curve `Y² + a₁XY + a₃Y = X³ + a₂X² + a₄X + a₆` with parameters `aᵢ`. -/
@[ext]
/--
Definition of `WeierstrassCurve` / `WeierstrassCurve` 的定义

English:
structure WeierstrassCurve
  parameters: (R : Type u)
  axioms and operations (5):
    - a₁ : R
    - a₂ : R
    - a₃ : R
    - a₄ : R
    - a₆ : R

中文:
结构 WeierstrassCurve
  参数: (R : 类型u)
  公理与运算 (5 个):
    - a₁ : R
    - a₂ : R
    - a₃ : R
    - a₄ : R
    - a₆ : R
-/
structure WeierstrassCurve (R : Type u) where
  /-- The `a₁` coefficient of a Weierstrass curve. -/
  a₁ : R
  /-- The `a₂` coefficient of a Weierstrass curve. -/
  a₂ : R
  /-- The `a₃` coefficient of a Weierstrass curve. -/
  a₃ : R
  /-- The `a₄` coefficient of a Weierstrass curve. -/
  a₄ : R
  /-- The `a₆` coefficient of a Weierstrass curve. -/
  a₆ : R

namespace WeierstrassCurve

instance {R : Type u} [Inhabited R] : Inhabited WeierstrassCurve R :=
  ⟨⟨default, default, default, default, default⟩⟩

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

section Quantity

/-! ### Standard quantities -/

/--
Definition of `b₂` / `b₂` 的定义

English:
definition b₂
  signature: : R
  body: W.a₁ ^ 2 + 4 * W.a₂

中文:
定义 b₂
  签名: : R
  定义体: W.a₁ ^ 2 + 4 * W.a₂
-/
def b₂ : R :=
  W.a₁ ^ 2 + 4 * W.a₂

/--
Definition of `b₄` / `b₄` 的定义

English:
definition b₄
  signature: : R
  body: 2 * W.a₄ + W.a₁ * W.a₃

中文:
定义 b₄
  签名: : R
  定义体: 2 * W.a₄ + W.a₁ * W.a₃
-/
def b₄ : R :=
  2 * W.a₄ + W.a₁ * W.a₃

/--
Definition of `b₆` / `b₆` 的定义

English:
definition b₆
  signature: : R
  body: W.a₃ ^ 2 + 4 * W.a₆

中文:
定义 b₆
  签名: : R
  定义体: W.a₃ ^ 2 + 4 * W.a₆
-/
def b₆ : R :=
  W.a₃ ^ 2 + 4 * W.a₆

/--
Definition of `b₈` / `b₈` 的定义

English:
definition b₈
  signature: : R
  body: W.a₁ ^ 2 * W.a₆ + 4 * W.a₂ * W.a₆ - W.a₁ * W.a₃ * W.a₄ + W.a₂ * W.a₃ ^ 2 - W.a₄ ^ 2

中文:
定义 b₈
  签名: : R
  定义体: W.a₁ ^ 2 * W.a₆ + 4 * W.a₂ * W.a₆ - W.a₁ * W.a₃ * W.a₄ + W.a₂ * W.a₃ ^ 2 - W.a₄ ^ 2
-/
def b₈ : R :=
  W.a₁ ^ 2 * W.a₆ + 4 * W.a₂ * W.a₆ - W.a₁ * W.a₃ * W.a₄ + W.a₂ * W.a₃ ^ 2 - W.a₄ ^ 2

/--
lemma `b_relation` / 引理 `b_relation`

English:
lemma b_relation
  statement: 4 * W.b₈ = W.b₂ * W.b₆ - W.b₄ ^ 2
  proof: by
  simp only [b₂, b₄, b₆, b₈]
  ring1

中文:
引理 b_relation
  结论: 4 * W.b₈ = W.b₂ * W.b₆ - W.b₄ ^ 2
  证明: by
  simp only [b₂, b₄, b₆, b₈]
  ring1
-/
lemma b_relation : 4 * W.b₈ = W.b₂ * W.b₆ - W.b₄ ^ 2 := by
  simp only [b₂, b₄, b₆, b₈]
  ring1

/--
Definition of `c₄` / `c₄` 的定义

English:
definition c₄
  signature: : R
  body: W.b₂ ^ 2 - 24 * W.b₄

中文:
定义 c₄
  签名: : R
  定义体: W.b₂ ^ 2 - 24 * W.b₄
-/
def c₄ : R :=
  W.b₂ ^ 2 - 24 * W.b₄

/--
Definition of `c₆` / `c₆` 的定义

English:
definition c₆
  signature: : R
  body: -W.b₂ ^ 3 + 36 * W.b₂ * W.b₄ - 216 * W.b₆

中文:
定义 c₆
  签名: : R
  定义体: -W.b₂ ^ 3 + 36 * W.b₂ * W.b₄ - 216 * W.b₆
-/
def c₆ : R :=
  -W.b₂ ^ 3 + 36 * W.b₂ * W.b₄ - 216 * W.b₆

/--
Definition of `Δ` / `Δ` 的定义

English:
definition Δ
  signature: : R
  body: -W.b₂ ^ 2 * W.b₈ - 8 * W.b₄ ^ 3 - 27 * W.b₆ ^ 2 + 9 * W.b₂ * W.b₄ * W.b₆

中文:
定义 Δ
  签名: : R
  定义体: -W.b₂ ^ 2 * W.b₈ - 8 * W.b₄ ^ 3 - 27 * W.b₆ ^ 2 + 9 * W.b₂ * W.b₄ * W.b₆
-/
def Δ : R :=
  -W.b₂ ^ 2 * W.b₈ - 8 * W.b₄ ^ 3 - 27 * W.b₆ ^ 2 + 9 * W.b₂ * W.b₄ * W.b₆

/--
lemma `c_relation` / 引理 `c_relation`

English:
lemma c_relation
  statement: 1728 * W.Δ = W.c₄ ^ 3 - W.c₆ ^ 2
  proof: by
  simp only [b₂, b₄, b₆, b₈, c₄, c₆, Δ]
  ring1

中文:
引理 c_relation
  结论: 1728 * W.Δ = W.c₄ ^ 3 - W.c₆ ^ 2
  证明: by
  simp only [b₂, b₄, b₆, b₈, c₄, c₆, Δ]
  ring1
-/
lemma c_relation : 1728 * W.Δ = W.c₄ ^ 3 - W.c₆ ^ 2 := by
  simp only [b₂, b₄, b₆, b₈, c₄, c₆, Δ]
  ring1

section CharTwo

variable [CharP R 2]

/--
lemma `b₂_of_char_two` / 引理 `b₂_of_char_two`

English:
lemma b₂_of_char_two
  statement: W.b₂ = W.a₁ ^ 2
  proof: by
  rw [b₂]
  linear_combination 2 * W.a₂ * CharP.cast_eq_zero R 2

中文:
引理 b₂_of_char_two
  结论: W.b₂ = W.a₁ ^ 2
  证明: by
  rw [b₂]
  linear_combination 2 * W.a₂ * CharP.cast_eq_zero R 2

Depends on / 依赖: CharP.cast_eq_zero, cast_eq_zero, linear_combination
-/
lemma b₂_of_char_two : W.b₂ = W.a₁ ^ 2 := by
  rw [b₂]
  linear_combination 2 * W.a₂ * CharP.cast_eq_zero R 2

/--
lemma `b₄_of_char_two` / 引理 `b₄_of_char_two`

English:
lemma b₄_of_char_two
  statement: W.b₄ = W.a₁ * W.a₃
  proof: by
  rw [b₄]
  linear_combination W.a₄ * CharP.cast_eq_zero R 2

中文:
引理 b₄_of_char_two
  结论: W.b₄ = W.a₁ * W.a₃
  证明: by
  rw [b₄]
  linear_combination W.a₄ * CharP.cast_eq_zero R 2

Depends on / 依赖: CharP.cast_eq_zero, cast_eq_zero, linear_combination
-/
lemma b₄_of_char_two : W.b₄ = W.a₁ * W.a₃ := by
  rw [b₄]
  linear_combination W.a₄ * CharP.cast_eq_zero R 2

/--
lemma `b₆_of_char_two` / 引理 `b₆_of_char_two`

English:
lemma b₆_of_char_two
  statement: W.b₆ = W.a₃ ^ 2
  proof: by
  rw [b₆]
  linear_combination 2 * W.a₆ * CharP.cast_eq_zero R 2

中文:
引理 b₆_of_char_two
  结论: W.b₆ = W.a₃ ^ 2
  证明: by
  rw [b₆]
  linear_combination 2 * W.a₆ * CharP.cast_eq_zero R 2

Depends on / 依赖: CharP.cast_eq_zero, cast_eq_zero, linear_combination
-/
lemma b₆_of_char_two : W.b₆ = W.a₃ ^ 2 := by
  rw [b₆]
  linear_combination 2 * W.a₆ * CharP.cast_eq_zero R 2

/--
lemma `b₈_of_char_two` / 引理 `b₈_of_char_two`

English:
lemma b₈_of_char_two
  proof: by
  rw [b₈]
  linear_combination (2 * W.a₂ * W.a₆ - W.a₁ * W.a₃ * W.a₄ - W.a₄ ^ 2) * CharP.cast_eq_zero R 2

中文:
引理 b₈_of_char_two
  证明: by
  rw [b₈]
  linear_combination (2 * W.a₂ * W.a₆ - W.a₁ * W.a₃ * W.a₄ - W.a₄ ^ 2) * CharP.cast_eq_zero R 2

Depends on / 依赖: CharP.cast_eq_zero, cast_eq_zero, linear_combination
-/
lemma b₈_of_char_two :
    W.b₈ = W.a₁ ^ 2 * W.a₆ + W.a₁ * W.a₃ * W.a₄ + W.a₂ * W.a₃ ^ 2 + W.a₄ ^ 2 := by
  rw [b₈]
  linear_combination (2 * W.a₂ * W.a₆ - W.a₁ * W.a₃ * W.a₄ - W.a₄ ^ 2) * CharP.cast_eq_zero R 2

/--
lemma `c₄_of_char_two` / 引理 `c₄_of_char_two`

English:
lemma c₄_of_char_two
  statement: W.c₄ = W.a₁ ^ 4
  proof: by
  rw [c₄]; rw [b₂_of_char_two]
  linear_combination -12 * W.b₄ * CharP.cast_eq_zero R 2

中文:
引理 c₄_of_char_two
  结论: W.c₄ = W.a₁ ^ 4
  证明: by
  rw [c₄]; rw [b₂_of_char_two]
  linear_combination -12 * W.b₄ * CharP.cast_eq_zero R 2

Depends on / 依赖: CharP.cast_eq_zero, cast_eq_zero, linear_combination
-/
lemma c₄_of_char_two : W.c₄ = W.a₁ ^ 4 := by
  rw [c₄]; rw [b₂_of_char_two]
  linear_combination -12 * W.b₄ * CharP.cast_eq_zero R 2

/--
lemma `c₆_of_char_two` / 引理 `c₆_of_char_two`

English:
lemma c₆_of_char_two
  statement: W.c₆ = W.a₁ ^ 6
  proof: by
  rw [c₆]; rw [b₂_of_char_two]
  linear_combination (18 * W.a₁ ^ 2 * W.b₄ - 108 * W.b₆ - W.a₁ ^ 6) * CharP.cast_eq_zero R 2

中文:
引理 c₆_of_char_two
  结论: W.c₆ = W.a₁ ^ 6
  证明: by
  rw [c₆]; rw [b₂_of_char_two]
  linear_combination (18 * W.a₁ ^ 2 * W.b₄ - 108 * W.b₆ - W.a₁ ^ 6) * CharP.cast_eq_zero R 2

Depends on / 依赖: CharP.cast_eq_zero, cast_eq_zero, linear_combination
-/
lemma c₆_of_char_two : W.c₆ = W.a₁ ^ 6 := by
  rw [c₆]; rw [b₂_of_char_two]
  linear_combination (18 * W.a₁ ^ 2 * W.b₄ - 108 * W.b₆ - W.a₁ ^ 6) * CharP.cast_eq_zero R 2

/--
lemma `Δ_of_char_two` / 引理 `Δ_of_char_two`

English:
lemma Δ_of_char_two
  statement: W.Δ = W.a₁ ^ 4 * W.b₈ + W.a₃ ^ 4 + W.a₁ ^ 3 * W.a₃ ^ 3
  proof: by
  rw [Δ]; rw [b₂_of_char_two]; rw [b₄_of_char_two]; rw [b₆_of_char_two]
  linear_combination (-W.a₁ ^ 4 * W.b₈ - 14 * W.a₃ ^ 4) * CharP.cast_eq_zero R 2

中文:
引理 Δ_of_char_two
  结论: W.Δ = W.a₁ ^ 4 * W.b₈ + W.a₃ ^ 4 + W.a₁ ^ 3 * W.a₃ ^ 3
  证明: by
  rw [Δ]; rw [b₂_of_char_two]; rw [b₄_of_char_two]; rw [b₆_of_char_two]
  linear_combination (-W.a₁ ^ 4 * W.b₈ - 14 * W.a₃ ^ 4) * CharP.cast_eq_zero R 2

Depends on / 依赖: CharP.cast_eq_zero, cast_eq_zero, linear_combination
-/
lemma Δ_of_char_two : W.Δ = W.a₁ ^ 4 * W.b₈ + W.a₃ ^ 4 + W.a₁ ^ 3 * W.a₃ ^ 3 := by
  rw [Δ]; rw [b₂_of_char_two]; rw [b₄_of_char_two]; rw [b₆_of_char_two]
  linear_combination (-W.a₁ ^ 4 * W.b₈ - 14 * W.a₃ ^ 4) * CharP.cast_eq_zero R 2

/--
lemma `b_relation_of_char_two` / 引理 `b_relation_of_char_two`

English:
lemma b_relation_of_char_two
  statement: W.b₂ * W.b₆ = W.b₄ ^ 2
  proof: by
  linear_combination -W.b_relation + 2 * W.b₈ * CharP.cast_eq_zero R 2

中文:
引理 b_relation_of_char_two
  结论: W.b₂ * W.b₆ = W.b₄ ^ 2
  证明: by
  linear_combination -W.b_relation + 2 * W.b₈ * CharP.cast_eq_zero R 2

Depends on / 依赖: CharP.cast_eq_zero, W.b_relation, b_relation, cast_eq_zero, linear_combination
-/
lemma b_relation_of_char_two : W.b₂ * W.b₆ = W.b₄ ^ 2 := by
  linear_combination -W.b_relation + 2 * W.b₈ * CharP.cast_eq_zero R 2

/--
lemma `c_relation_of_char_two` / 引理 `c_relation_of_char_two`

English:
lemma c_relation_of_char_two
  statement: W.c₄ ^ 3 = W.c₆ ^ 2
  proof: by
  linear_combination -W.c_relation + 864 * W.Δ * CharP.cast_eq_zero R 2

中文:
引理 c_relation_of_char_two
  结论: W.c₄ ^ 3 = W.c₆ ^ 2
  证明: by
  linear_combination -W.c_relation + 864 * W.Δ * CharP.cast_eq_zero R 2

Depends on / 依赖: CharP.cast_eq_zero, W.c_relation, c_relation, cast_eq_zero, linear_combination
-/
lemma c_relation_of_char_two : W.c₄ ^ 3 = W.c₆ ^ 2 := by
  linear_combination -W.c_relation + 864 * W.Δ * CharP.cast_eq_zero R 2

end CharTwo

section CharThree

variable [CharP R 3]

/--
lemma `b₂_of_char_three` / 引理 `b₂_of_char_three`

English:
lemma b₂_of_char_three
  statement: W.b₂ = W.a₁ ^ 2 + W.a₂
  proof: by
  rw [b₂]
  linear_combination W.a₂ * CharP.cast_eq_zero R 3

中文:
引理 b₂_of_char_three
  结论: W.b₂ = W.a₁ ^ 2 + W.a₂
  证明: by
  rw [b₂]
  linear_combination W.a₂ * CharP.cast_eq_zero R 3

Depends on / 依赖: CharP.cast_eq_zero, cast_eq_zero, linear_combination
-/
lemma b₂_of_char_three : W.b₂ = W.a₁ ^ 2 + W.a₂ := by
  rw [b₂]
  linear_combination W.a₂ * CharP.cast_eq_zero R 3

/--
lemma `b₄_of_char_three` / 引理 `b₄_of_char_three`

English:
lemma b₄_of_char_three
  statement: W.b₄ = -W.a₄ + W.a₁ * W.a₃
  proof: by
  rw [b₄]
  linear_combination W.a₄ * CharP.cast_eq_zero R 3

中文:
引理 b₄_of_char_three
  结论: W.b₄ = -W.a₄ + W.a₁ * W.a₃
  证明: by
  rw [b₄]
  linear_combination W.a₄ * CharP.cast_eq_zero R 3

Depends on / 依赖: CharP.cast_eq_zero, cast_eq_zero, linear_combination
-/
lemma b₄_of_char_three : W.b₄ = -W.a₄ + W.a₁ * W.a₃ := by
  rw [b₄]
  linear_combination W.a₄ * CharP.cast_eq_zero R 3

/--
lemma `b₆_of_char_three` / 引理 `b₆_of_char_three`

English:
lemma b₆_of_char_three
  statement: W.b₆ = W.a₃ ^ 2 + W.a₆
  proof: by
  rw [b₆]
  linear_combination W.a₆ * CharP.cast_eq_zero R 3

中文:
引理 b₆_of_char_three
  结论: W.b₆ = W.a₃ ^ 2 + W.a₆
  证明: by
  rw [b₆]
  linear_combination W.a₆ * CharP.cast_eq_zero R 3

Depends on / 依赖: CharP.cast_eq_zero, cast_eq_zero, linear_combination
-/
lemma b₆_of_char_three : W.b₆ = W.a₃ ^ 2 + W.a₆ := by
  rw [b₆]
  linear_combination W.a₆ * CharP.cast_eq_zero R 3

/--
lemma `b₈_of_char_three` / 引理 `b₈_of_char_three`

English:
lemma b₈_of_char_three
  proof: by
  rw [b₈]
  linear_combination W.a₂ * W.a₆ * CharP.cast_eq_zero R 3

中文:
引理 b₈_of_char_three
  证明: by
  rw [b₈]
  linear_combination W.a₂ * W.a₆ * CharP.cast_eq_zero R 3

Depends on / 依赖: CharP.cast_eq_zero, cast_eq_zero, linear_combination
-/
lemma b₈_of_char_three :
    W.b₈ = W.a₁ ^ 2 * W.a₆ + W.a₂ * W.a₆ - W.a₁ * W.a₃ * W.a₄ + W.a₂ * W.a₃ ^ 2 - W.a₄ ^ 2 := by
  rw [b₈]
  linear_combination W.a₂ * W.a₆ * CharP.cast_eq_zero R 3

/--
lemma `c₄_of_char_three` / 引理 `c₄_of_char_three`

English:
lemma c₄_of_char_three
  statement: W.c₄ = W.b₂ ^ 2
  proof: by
  rw [c₄]
  linear_combination -8 * W.b₄ * CharP.cast_eq_zero R 3

中文:
引理 c₄_of_char_three
  结论: W.c₄ = W.b₂ ^ 2
  证明: by
  rw [c₄]
  linear_combination -8 * W.b₄ * CharP.cast_eq_zero R 3

Depends on / 依赖: CharP.cast_eq_zero, cast_eq_zero, linear_combination
-/
lemma c₄_of_char_three : W.c₄ = W.b₂ ^ 2 := by
  rw [c₄]
  linear_combination -8 * W.b₄ * CharP.cast_eq_zero R 3

/--
lemma `c₆_of_char_three` / 引理 `c₆_of_char_three`

English:
lemma c₆_of_char_three
  statement: W.c₆ = -W.b₂ ^ 3
  proof: by
  rw [c₆]
  linear_combination (12 * W.b₂ * W.b₄ - 72 * W.b₆) * CharP.cast_eq_zero R 3

中文:
引理 c₆_of_char_three
  结论: W.c₆ = -W.b₂ ^ 3
  证明: by
  rw [c₆]
  linear_combination (12 * W.b₂ * W.b₄ - 72 * W.b₆) * CharP.cast_eq_zero R 3

Depends on / 依赖: CharP.cast_eq_zero, cast_eq_zero, linear_combination
-/
lemma c₆_of_char_three : W.c₆ = -W.b₂ ^ 3 := by
  rw [c₆]
  linear_combination (12 * W.b₂ * W.b₄ - 72 * W.b₆) * CharP.cast_eq_zero R 3

/--
lemma `Δ_of_char_three` / 引理 `Δ_of_char_three`

English:
lemma Δ_of_char_three
  statement: W.Δ = -W.b₂ ^ 2 * W.b₈ - 8 * W.b₄ ^ 3
  proof: by
  rw [Δ]
  linear_combination (-9 * W.b₆ ^ 2 + 3 * W.b₂ * W.b₄ * W.b₆) * CharP.cast_eq_zero R 3

中文:
引理 Δ_of_char_three
  结论: W.Δ = -W.b₂ ^ 2 * W.b₈ - 8 * W.b₄ ^ 3
  证明: by
  rw [Δ]
  linear_combination (-9 * W.b₆ ^ 2 + 3 * W.b₂ * W.b₄ * W.b₆) * CharP.cast_eq_zero R 3

Depends on / 依赖: CharP.cast_eq_zero, cast_eq_zero, linear_combination
-/
lemma Δ_of_char_three : W.Δ = -W.b₂ ^ 2 * W.b₈ - 8 * W.b₄ ^ 3 := by
  rw [Δ]
  linear_combination (-9 * W.b₆ ^ 2 + 3 * W.b₂ * W.b₄ * W.b₆) * CharP.cast_eq_zero R 3

/--
lemma `b_relation_of_char_three` / 引理 `b_relation_of_char_three`

English:
lemma b_relation_of_char_three
  statement: W.b₈ = W.b₂ * W.b₆ - W.b₄ ^ 2
  proof: by
  linear_combination W.b_relation - W.b₈ * CharP.cast_eq_zero R 3

中文:
引理 b_relation_of_char_three
  结论: W.b₈ = W.b₂ * W.b₆ - W.b₄ ^ 2
  证明: by
  linear_combination W.b_relation - W.b₈ * CharP.cast_eq_zero R 3

Depends on / 依赖: CharP.cast_eq_zero, W.b_relation, b_relation, cast_eq_zero, linear_combination
-/
lemma b_relation_of_char_three : W.b₈ = W.b₂ * W.b₆ - W.b₄ ^ 2 := by
  linear_combination W.b_relation - W.b₈ * CharP.cast_eq_zero R 3

/--
lemma `c_relation_of_char_three` / 引理 `c_relation_of_char_three`

English:
lemma c_relation_of_char_three
  statement: W.c₄ ^ 3 = W.c₆ ^ 2
  proof: by
  linear_combination -W.c_relation + 576 * W.Δ * CharP.cast_eq_zero R 3

中文:
引理 c_relation_of_char_three
  结论: W.c₄ ^ 3 = W.c₆ ^ 2
  证明: by
  linear_combination -W.c_relation + 576 * W.Δ * CharP.cast_eq_zero R 3

Depends on / 依赖: CharP.cast_eq_zero, W.c_relation, c_relation, cast_eq_zero, linear_combination
-/
lemma c_relation_of_char_three : W.c₄ ^ 3 = W.c₆ ^ 2 := by
  linear_combination -W.c_relation + 576 * W.Δ * CharP.cast_eq_zero R 3

end CharThree

end Quantity

section BaseChange

/-! ### Maps and base changes -/

variable {A : Type v} [CommRing A] (f : R ->+* A)

/-- The Weierstrass curve mapped over a ring homomorphism `f : R →+* A`. -/
@[simps]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: : WeierstrassCurve A
  body: ⟨f W.a₁, f W.a₂, f W.a₃, f W.a₄, f W.a₆⟩

中文:
定义 map
  签名: : WeierstrassCurve A
  定义体: ⟨f W.a₁, f W.a₂, f W.a₃, f W.a₄, f W.a₆⟩
-/
def map : WeierstrassCurve A :=
  ⟨f W.a₁, f W.a₂, f W.a₃, f W.a₄, f W.a₆⟩

variable (A) in
/--
Definition of `baseChange` / `baseChange` 的定义

English:
definition baseChange
  signature: [Algebra R A]
  body: W.map algebraMap R A

中文:
定义 baseChange
  签名: [代数 R A]
  定义体: W.map algebraMap R A

Depends on / 依赖: W.map, algebraMap
-/
def baseChange [Algebra R A] : WeierstrassCurve A :=
W.map algebraMap R A

/-- The notation `\textf` for `WeierstrassCurve.baseChange W A`. -/
scoped notation:max (priority := low) W:max "⁄" A:max => baseChange W A

@[simp]
/--
lemma `map_b₂` / 引理 `map_b₂`

English:
lemma map_b₂
  statement: (W.map f).b₂ = f W.b₂
  proof: by
  simp only [b₂, map_a₁, map_a₂]
  map_simp

@[simp]

中文:
引理 map_b₂
  结论: (W.map f).b₂ = f W.b₂
  证明: by
  simp only [b₂, map_a₁, map_a₂]
  map_simp

@[simp]

Depends on / 依赖: map_simp
-/
lemma map_b₂ : (W.map f).b₂ = f W.b₂ := by
  simp only [b₂, map_a₁, map_a₂]
  map_simp

@[simp]
/--
lemma `map_b₄` / 引理 `map_b₄`

English:
lemma map_b₄
  statement: (W.map f).b₄ = f W.b₄
  proof: by
  simp only [b₄, map_a₁, map_a₃, map_a₄]
  map_simp

@[simp]

中文:
引理 map_b₄
  结论: (W.map f).b₄ = f W.b₄
  证明: by
  simp only [b₄, map_a₁, map_a₃, map_a₄]
  map_simp

@[simp]

Depends on / 依赖: map_simp
-/
lemma map_b₄ : (W.map f).b₄ = f W.b₄ := by
  simp only [b₄, map_a₁, map_a₃, map_a₄]
  map_simp

@[simp]
/--
lemma `map_b₆` / 引理 `map_b₆`

English:
lemma map_b₆
  statement: (W.map f).b₆ = f W.b₆
  proof: by
  simp only [b₆, map_a₃, map_a₆]
  map_simp

@[simp]

中文:
引理 map_b₆
  结论: (W.map f).b₆ = f W.b₆
  证明: by
  simp only [b₆, map_a₃, map_a₆]
  map_simp

@[simp]

Depends on / 依赖: map_simp
-/
lemma map_b₆ : (W.map f).b₆ = f W.b₆ := by
  simp only [b₆, map_a₃, map_a₆]
  map_simp

@[simp]
/--
lemma `map_b₈` / 引理 `map_b₈`

English:
lemma map_b₈
  statement: (W.map f).b₈ = f W.b₈
  proof: by
  simp only [b₈, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆]
  map_simp

@[simp]

中文:
引理 map_b₈
  结论: (W.map f).b₈ = f W.b₈
  证明: by
  simp only [b₈, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆]
  map_simp

@[simp]

Depends on / 依赖: map_simp
-/
lemma map_b₈ : (W.map f).b₈ = f W.b₈ := by
  simp only [b₈, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆]
  map_simp

@[simp]
/--
lemma `map_c₄` / 引理 `map_c₄`

English:
lemma map_c₄
  statement: (W.map f).c₄ = f W.c₄
  proof: by
  simp only [c₄, map_b₂, map_b₄]
  map_simp

@[simp]

中文:
引理 map_c₄
  结论: (W.map f).c₄ = f W.c₄
  证明: by
  simp only [c₄, map_b₂, map_b₄]
  map_simp

@[simp]

Depends on / 依赖: map_simp
-/
lemma map_c₄ : (W.map f).c₄ = f W.c₄ := by
  simp only [c₄, map_b₂, map_b₄]
  map_simp

@[simp]
/--
lemma `map_c₆` / 引理 `map_c₆`

English:
lemma map_c₆
  statement: (W.map f).c₆ = f W.c₆
  proof: by
  simp only [c₆, map_b₂, map_b₄, map_b₆]
  map_simp

@[simp]

中文:
引理 map_c₆
  结论: (W.map f).c₆ = f W.c₆
  证明: by
  simp only [c₆, map_b₂, map_b₄, map_b₆]
  map_simp

@[simp]

Depends on / 依赖: map_simp
-/
lemma map_c₆ : (W.map f).c₆ = f W.c₆ := by
  simp only [c₆, map_b₂, map_b₄, map_b₆]
  map_simp

@[simp]
/--
lemma `map_Δ` / 引理 `map_Δ`

English:
lemma map_Δ
  statement: (W.map f).Δ = f W.Δ
  proof: by
  simp only [Δ, map_b₂, map_b₄, map_b₆, map_b₈]
  map_simp

@[simp]

中文:
引理 map_Δ
  结论: (W.map f).Δ = f W.Δ
  证明: by
  simp only [Δ, map_b₂, map_b₄, map_b₆, map_b₈]
  map_simp

@[simp]

Depends on / 依赖: map_simp
-/
lemma map_Δ : (W.map f).Δ = f W.Δ := by
  simp only [Δ, map_b₂, map_b₄, map_b₆, map_b₈]
  map_simp

@[simp]
/--
lemma `map_id` / 引理 `map_id`

English:
lemma map_id
  statement: W.map (RingHom.id R) = W
  proof: rfl

中文:
引理 map_id
  结论: W.map (环态射.id R) = W
  证明: rfl

Depends on / 依赖: Finite, Finite.of_injective, f.toOrderHom.toFun, of_injective, toOrderHom
-/
lemma map_id : W.map (RingHom.id R) = W :=
  rfl

/--
lemma `map_map` / 引理 `map_map`

English:
lemma map_map
  given: {B : Type w} [CommRing B] (g : A ->+* B)
  statement: (W.map f).map g = W.map (g.comp f)
  proof: rfl

@[simp]

中文:
引理 map_map
  条件: {B : 类型 w} [交换环 B] (g : A ->+* B)
  结论: (W.map f).map g = W.map (g.comp f)
  证明: rfl

@[simp]
-/
lemma map_map {B : Type w} [CommRing B] (g : A ->+* B) : (W.map f).map g = W.map (g.comp f) :=
  rfl

@[simp]
/--
lemma `map_baseChange` / 引理 `map_baseChange`

English:
lemma map_baseChange
  statement: {S : Type s} [CommRing S] [Algebra R S] {A : Type v} [CommRing A] [Algebra R A]
  proof: congrArg W.map g.comp_algebraMap_of_tower R

中文:
引理 map_baseChange
  结论: {S : 类型 s} [交换环 S] [代数 R S] {A : 类型v} [交换环 A] [代数 R A]
  证明: congrArg W.map g.comp_algebraMap_of_tower R

Depends on / 依赖: W.map, comp_algebraMap_of_tower, g.comp_algebraMap_of_tower
-/
lemma map_baseChange {S : Type s} [CommRing S] [Algebra R S] {A : Type v} [CommRing A] [Algebra R A]
    [Algebra S A] [IsScalarTower R S A] {B : Type w} [CommRing B] [Algebra R B] [Algebra S B]
    [IsScalarTower R S B] (g : A ->ₐ[S] B) : (W⁄A).map g = W⁄B :=
congrArg W.map g.comp_algebraMap_of_tower R

variable {f} in
/--
lemma `map_injective` / 引理 `map_injective`

English:
lemma map_injective
  given: (hf : Function.Injective f)
  proof: fun _ _ h => by
  rcases mk.inj h with ⟨_, _, _, _, _⟩
  ext <;> apply_fun _ using hf <;> assumption

中文:
引理 map_injective
  条件: (hf : 函数.单射 f)
  证明: fun _ _ h => by
  rcases mk.inj h with ⟨_, _, _, _, _⟩
  ext <;> apply_fun _ using hf <;> assumption

Depends on / 依赖: apply_fun, mk.inj
-/
lemma map_injective (hf : Function.Injective f) :
Function.Injective map (f := f) := fun _ _ h => by
  rcases mk.inj h with ⟨_, _, _, _, _⟩
  ext <;> apply_fun _ using hf <;> assumption

end BaseChange

section TorsionPolynomial

/-! ### 2-torsion polynomials -/

/--
Definition of `twoTorsionPolynomial` / `twoTorsionPolynomial` 的定义

English:
definition twoTorsionPolynomial
  signature: : Cubic R
  body: ⟨4, W.b₂, 2 * W.b₄, W.b₆⟩

中文:
定义 twoTorsionPolynomial
  签名: : 三次 R
  定义体: ⟨4, W.b₂, 2 * W.b₄, W.b₆⟩
-/
def twoTorsionPolynomial : Cubic R :=
  ⟨4, W.b₂, 2 * W.b₄, W.b₆⟩

/--
lemma `twoTorsionPolynomial_discr` / 引理 `twoTorsionPolynomial_discr`

English:
lemma twoTorsionPolynomial_discr
  statement: W.twoTorsionPolynomial.discr = 16 * W.Δ
  proof: by
  simp only [b₂, b₄, b₆, b₈, Δ, twoTorsionPolynomial, Cubic.discr]
  ring1

中文:
引理 twoTorsionPolynomial_discr
  结论: W.twoTorsionPolynomial.discr = 16 * W.Δ
  证明: by
  simp only [b₂, b₄, b₆, b₈, Δ, twoTorsionPolynomial, Cubic.discr]
  ring1

Depends on / 依赖: Cubic.discr, twoTorsionPolynomial
-/
lemma twoTorsionPolynomial_discr : W.twoTorsionPolynomial.discr = 16 * W.Δ := by
  simp only [b₂, b₄, b₆, b₈, Δ, twoTorsionPolynomial, Cubic.discr]
  ring1

section CharTwo

variable [CharP R 2]

/--
lemma `twoTorsionPolynomial_of_char_two` / 引理 `twoTorsionPolynomial_of_char_two`

English:
lemma twoTorsionPolynomial_of_char_two
  statement: W.twoTorsionPolynomial = ⟨0, W.b₂, 0, W.b₆⟩
  proof: by
  rw [twoTorsionPolynomial]
  ext <;> dsimp
  · linear_combination 2 * CharP.cast_eq_zero R 2
  · linear_combination W.b₄ * CharP.cast_eq_zero R 2

中文:
引理 twoTorsionPolynomial_of_char_two
  结论: W.twoTorsionPolynomial = ⟨0, W.b₂, 0, W.b₆⟩
  证明: by
  rw [twoTorsionPolynomial]
  ext <;> dsimp
  · linear_combination 2 * CharP.cast_eq_zero R 2
  · linear_combination W.b₄ * CharP.cast_eq_zero R 2

Depends on / 依赖: CharP.cast_eq_zero, cast_eq_zero, linear_combination, twoTorsionPolynomial
-/
lemma twoTorsionPolynomial_of_char_two : W.twoTorsionPolynomial = ⟨0, W.b₂, 0, W.b₆⟩ := by
  rw [twoTorsionPolynomial]
  ext <;> dsimp
  · linear_combination 2 * CharP.cast_eq_zero R 2
  · linear_combination W.b₄ * CharP.cast_eq_zero R 2

/--
lemma `twoTorsionPolynomial_discr_of_char_two` / 引理 `twoTorsionPolynomial_discr_of_char_two`

English:
lemma twoTorsionPolynomial_discr_of_char_two
  statement: W.twoTorsionPolynomial.discr = 0
  proof: by
  linear_combination W.twoTorsionPolynomial_discr + 8 * W.Δ * CharP.cast_eq_zero R 2

中文:
引理 twoTorsionPolynomial_discr_of_char_two
  结论: W.twoTorsionPolynomial.discr = 0
  证明: by
  linear_combination W.twoTorsionPolynomial_discr + 8 * W.Δ * CharP.cast_eq_zero R 2

Depends on / 依赖: CharP.cast_eq_zero, W.twoTorsionPolynomial_discr, cast_eq_zero, linear_combination, twoTorsionPolynomial_discr
-/
lemma twoTorsionPolynomial_discr_of_char_two : W.twoTorsionPolynomial.discr = 0 := by
  linear_combination W.twoTorsionPolynomial_discr + 8 * W.Δ * CharP.cast_eq_zero R 2

end CharTwo

section CharThree

variable [CharP R 3]

/--
lemma `twoTorsionPolynomial_of_char_three` / 引理 `twoTorsionPolynomial_of_char_three`

English:
lemma twoTorsionPolynomial_of_char_three
  statement: W.twoTorsionPolynomial = ⟨1, W.b₂, -W.b₄, W.b₆⟩
  proof: by
  rw [twoTorsionPolynomial]
  ext <;> dsimp
  · linear_combination CharP.cast_eq_zero R 3
  · linear_combination W.b₄ * CharP.cast_eq_zero R 3

中文:
引理 twoTorsionPolynomial_of_char_three
  结论: W.twoTorsionPolynomial = ⟨1, W.b₂, -W.b₄, W.b₆⟩
  证明: by
  rw [twoTorsionPolynomial]
  ext <;> dsimp
  · linear_combination CharP.cast_eq_zero R 3
  · linear_combination W.b₄ * CharP.cast_eq_zero R 3

Depends on / 依赖: CharP.cast_eq_zero, cast_eq_zero, linear_combination, twoTorsionPolynomial
-/
lemma twoTorsionPolynomial_of_char_three : W.twoTorsionPolynomial = ⟨1, W.b₂, -W.b₄, W.b₆⟩ := by
  rw [twoTorsionPolynomial]
  ext <;> dsimp
  · linear_combination CharP.cast_eq_zero R 3
  · linear_combination W.b₄ * CharP.cast_eq_zero R 3

/--
lemma `twoTorsionPolynomial_discr_of_char_three` / 引理 `twoTorsionPolynomial_discr_of_char_three`

English:
lemma twoTorsionPolynomial_discr_of_char_three
  statement: W.twoTorsionPolynomial.discr = W.Δ
  proof: by
  linear_combination W.twoTorsionPolynomial_discr + 5 * W.Δ * CharP.cast_eq_zero R 3

中文:
引理 twoTorsionPolynomial_discr_of_char_three
  结论: W.twoTorsionPolynomial.discr = W.Δ
  证明: by
  linear_combination W.twoTorsionPolynomial_discr + 5 * W.Δ * CharP.cast_eq_zero R 3

Depends on / 依赖: CharP.cast_eq_zero, W.twoTorsionPolynomial_discr, cast_eq_zero, linear_combination, twoTorsionPolynomial_discr
-/
lemma twoTorsionPolynomial_discr_of_char_three : W.twoTorsionPolynomial.discr = W.Δ := by
  linear_combination W.twoTorsionPolynomial_discr + 5 * W.Δ * CharP.cast_eq_zero R 3

end CharThree

-- TODO: change to `[IsUnit ...]` once https://github.com/leanprover-community/mathlib4/issues/17458 is merged
/--
lemma `twoTorsionPolynomial_discr_isUnit` / 引理 `twoTorsionPolynomial_discr_isUnit`

English:
lemma twoTorsionPolynomial_discr_isUnit
  given: (hu : IsUnit (2 : R))
  proof: by
  rw [twoTorsionPolynomial_discr]; rw [IsUnit.mul_iff]; rw [show (16 : R) = 2 ^ 4 by norm_num1]
exact and_iff_right hu.pow 4

中文:
引理 twoTorsionPolynomial_discr_isUnit
  条件: (hu : 是单位 (2 : R))
  证明: by
  rw [twoTorsionPolynomial_discr]; rw [IsUnit.mul_iff]; rw [show (16 : R) = 2 ^ 4 by norm_num1]
exact and_iff_right hu.pow 4

Depends on / 依赖: IsUnit, IsUnit.mul_iff, and_iff_right, hu.pow, mul_iff, norm_num1, twoTorsionPolynomial_discr
-/
lemma twoTorsionPolynomial_discr_isUnit (hu : IsUnit (2 : R)) :
    IsUnit W.twoTorsionPolynomial.discr ↔ IsUnit W.Δ := by
  rw [twoTorsionPolynomial_discr]; rw [IsUnit.mul_iff]; rw [show (16 : R) = 2 ^ 4 by norm_num1]
exact and_iff_right hu.pow 4

-- TODO: change to `[IsUnit ...]` once https://github.com/leanprover-community/mathlib4/issues/17458 is merged
-- TODO: In this case `IsUnit W.Δ` is just `W.IsElliptic`, consider removing/rephrasing this result
/--
lemma `twoTorsionPolynomial_discr_ne_zero` / 引理 `twoTorsionPolynomial_discr_ne_zero`

English:
lemma twoTorsionPolynomial_discr_ne_zero
  given: [Nontrivial R] (hu : IsUnit (2 : R)) (hΔ : IsUnit W.Δ)
  proof: ((W.twoTorsionPolynomial_discr_isUnit hu).mpr hΔ).ne_zero

中文:
引理 twoTorsionPolynomial_discr_ne_zero
  条件: [非平凡 R] (hu : 是单位 (2 : R)) (hΔ : 是单位 W.Δ)
  证明: ((W.twoTorsionPolynomial_discr_isUnit hu).mpr hΔ).ne_zero

Depends on / 依赖: W.twoTorsionPolynomial_discr_isUnit, ne_zero, twoTorsionPolynomial_discr_isUnit
-/
lemma twoTorsionPolynomial_discr_ne_zero [Nontrivial R] (hu : IsUnit (2 : R)) (hΔ : IsUnit W.Δ) :
    W.twoTorsionPolynomial.discr != 0 :=
  ((W.twoTorsionPolynomial_discr_isUnit hu).mpr hΔ).ne_zero

end TorsionPolynomial

/-! ## Elliptic curves -/

-- TODO: change to `protected abbrev IsElliptic := IsUnit W.Δ` once https://github.com/leanprover-community/mathlib4/issues/17458 is merged
/-- `WeierstrassCurve.IsElliptic` is a typeclass which asserts that a Weierstrass curve is an
elliptic curve: that its discriminant is a unit. Note that this definition is only mathematically
accurate for certain rings whose Picard group has trivial 12-torsion, such as a field or a PID. -/
@[mk_iff]
/--
Definition of `IsElliptic` / `IsElliptic` 的定义

English:
class IsElliptic
  parameters: : Prop where
  axioms and operations (1):
    - isUnit : IsUnit W.Δ

中文:
类 是Elliptic
  参数: : 命题 where
  公理与运算 (1 个):
    - isUnit : 是单位 W.Δ
-/
protected class IsElliptic : Prop where
  isUnit : IsUnit W.Δ

variable [W.IsElliptic]

/--
lemma `isUnit_Δ` / 引理 `isUnit_Δ`

English:
lemma isUnit_Δ
  statement: IsUnit W.Δ
  proof: IsElliptic.isUnit

中文:
引理 isUnit_Δ
  结论: 是单位 W.Δ
  证明: IsElliptic.isUnit

Depends on / 依赖: IsElliptic, IsElliptic.isUnit, isUnit
-/
lemma isUnit_Δ : IsUnit W.Δ := IsElliptic.isUnit

/--
Definition of `Δ'` / `Δ'` 的定义

English:
definition Δ'
  signature: : Rˣ
  body: W.isUnit_Δ.unit

中文:
定义 Δ'
  签名: : Rˣ
  定义体: W.isUnit_Δ.unit

Depends on / 依赖: W.isUnit_
-/
noncomputable def Δ' : Rˣ :=
  W.isUnit_Δ.unit

/-- The discriminant `Δ'` of an elliptic curve is equal to the
discriminant `Δ` of it as a Weierstrass curve. -/
@[simp]
/--
lemma `coe_Δ'` / 引理 `coe_Δ'`

English:
lemma coe_Δ'
  statement: W.Δ' = W.Δ
  proof: rfl

中文:
引理 coe_Δ'
  结论: W.Δ' = W.Δ
  证明: rfl
-/
lemma coe_Δ' : W.Δ' = W.Δ :=
  rfl

/--
Definition of `j` / `j` 的定义

English:
definition j
  signature: : R
  body: W.Δ'⁻¹ * W.c₄ ^ 3

中文:
定义 j
  签名: : R
  定义体: W.Δ'⁻¹ * W.c₄ ^ 3
-/
noncomputable def j : R :=
  W.Δ'⁻¹ * W.c₄ ^ 3

/--
lemma `j_eq_zero_iff'` / 引理 `j_eq_zero_iff'`

English:
lemma j_eq_zero_iff'
  statement: W.j = 0 ↔ W.c₄ ^ 3 = 0
  proof: by
  rw [j]; rw [Units.mul_right_eq_zero]

中文:
引理 j_eq_zero_iff'
  结论: W.j = 0 ↔ W.c₄ ^ 3 = 0
  证明: by
  rw [j]; rw [Units.mul_right_eq_zero]

Depends on / 依赖: Units.mul_right_eq_zero, mul_right_eq_zero
-/
lemma j_eq_zero_iff' : W.j = 0 ↔ W.c₄ ^ 3 = 0 := by
  rw [j]; rw [Units.mul_right_eq_zero]

/--
lemma `j_eq_zero` / 引理 `j_eq_zero`

English:
lemma j_eq_zero
  given: (h : W.c₄ = 0)
  statement: W.j = 0
  proof: by
  rw [j_eq_zero_iff']; rw [h]; rw [zero_pow three_ne_zero]

中文:
引理 j_eq_zero
  条件: (h : W.c₄ = 0)
  结论: W.j = 0
  证明: by
  rw [j_eq_zero_iff']; rw [h]; rw [zero_pow three_ne_zero]

Depends on / 依赖: j_eq_zero_iff, three_ne_zero, zero_pow
-/
lemma j_eq_zero (h : W.c₄ = 0) : W.j = 0 := by
  rw [j_eq_zero_iff']; rw [h]; rw [zero_pow three_ne_zero]

/--
lemma `j_eq_zero_iff` / 引理 `j_eq_zero_iff`

English:
lemma j_eq_zero_iff
  given: [IsReduced R]
  statement: W.j = 0 ↔ W.c₄ = 0
  proof: by
  rw [j_eq_zero_iff']; rw [pow_eq_zero_iff three_ne_zero]

中文:
引理 j_eq_zero_iff
  条件: [是既约 R]
  结论: W.j = 0 ↔ W.c₄ = 0
  证明: by
  rw [j_eq_zero_iff']; rw [pow_eq_zero_iff three_ne_zero]

Depends on / 依赖: j_eq_zero_iff, pow_eq_zero_iff, three_ne_zero
-/
lemma j_eq_zero_iff [IsReduced R] : W.j = 0 ↔ W.c₄ = 0 := by
  rw [j_eq_zero_iff']; rw [pow_eq_zero_iff three_ne_zero]

section CharTwo

variable [CharP R 2]

/--
lemma `j_of_char_two` / 引理 `j_of_char_two`

English:
lemma j_of_char_two
  statement: W.j = W.Δ'⁻¹ * W.a₁ ^ 12
  proof: by
  rw [j]; rw [W.c₄_of_char_two]; rw [← pow_mul]

中文:
引理 j_of_char_two
  结论: W.j = W.Δ'⁻¹ * W.a₁ ^ 12
  证明: by
  rw [j]; rw [W.c₄_of_char_two]; rw [← pow_mul]

Depends on / 依赖: pow_mul
-/
lemma j_of_char_two : W.j = W.Δ'⁻¹ * W.a₁ ^ 12 := by
  rw [j]; rw [W.c₄_of_char_two]; rw [← pow_mul]

/--
lemma `j_eq_zero_iff_of_char_two'` / 引理 `j_eq_zero_iff_of_char_two'`

English:
lemma j_eq_zero_iff_of_char_two'
  statement: W.j = 0 ↔ W.a₁ ^ 12 = 0
  proof: by
  rw [j_of_char_two]; rw [Units.mul_right_eq_zero]

中文:
引理 j_eq_zero_iff_of_char_two'
  结论: W.j = 0 ↔ W.a₁ ^ 12 = 0
  证明: by
  rw [j_of_char_two]; rw [Units.mul_right_eq_zero]

Depends on / 依赖: Units.mul_right_eq_zero, j_of_char_two, mul_right_eq_zero
-/
lemma j_eq_zero_iff_of_char_two' : W.j = 0 ↔ W.a₁ ^ 12 = 0 := by
  rw [j_of_char_two]; rw [Units.mul_right_eq_zero]

/--
lemma `j_eq_zero_of_char_two` / 引理 `j_eq_zero_of_char_two`

English:
lemma j_eq_zero_of_char_two
  given: (h : W.a₁ = 0)
  statement: W.j = 0
  proof: by
  rw [j_eq_zero_iff_of_char_two']; rw [h]; rw [zero_pow (Nat.succ_ne_zero _)]

中文:
引理 j_eq_zero_of_char_two
  条件: (h : W.a₁ = 0)
  结论: W.j = 0
  证明: by
  rw [j_eq_zero_iff_of_char_two']; rw [h]; rw [zero_pow (Nat.succ_ne_zero _)]

Depends on / 依赖: Nat.succ_ne_zero, j_eq_zero_iff_of_char_two, succ_ne_zero, zero_pow
-/
lemma j_eq_zero_of_char_two (h : W.a₁ = 0) : W.j = 0 := by
  rw [j_eq_zero_iff_of_char_two']; rw [h]; rw [zero_pow (Nat.succ_ne_zero _)]

/--
lemma `j_eq_zero_iff_of_char_two` / 引理 `j_eq_zero_iff_of_char_two`

English:
lemma j_eq_zero_iff_of_char_two
  given: [IsReduced R]
  statement: W.j = 0 ↔ W.a₁ = 0
  proof: by
  rw [j_eq_zero_iff_of_char_two']; rw [pow_eq_zero_iff (Nat.succ_ne_zero _)]

中文:
引理 j_eq_zero_iff_of_char_two
  条件: [是既约 R]
  结论: W.j = 0 ↔ W.a₁ = 0
  证明: by
  rw [j_eq_zero_iff_of_char_two']; rw [pow_eq_zero_iff (Nat.succ_ne_zero _)]

Depends on / 依赖: Nat.succ_ne_zero, j_eq_zero_iff_of_char_two, pow_eq_zero_iff, succ_ne_zero
-/
lemma j_eq_zero_iff_of_char_two [IsReduced R] : W.j = 0 ↔ W.a₁ = 0 := by
  rw [j_eq_zero_iff_of_char_two']; rw [pow_eq_zero_iff (Nat.succ_ne_zero _)]

end CharTwo

section CharThree

variable [CharP R 3]

/--
lemma `j_of_char_three` / 引理 `j_of_char_three`

English:
lemma j_of_char_three
  statement: W.j = W.Δ'⁻¹ * W.b₂ ^ 6
  proof: by
  rw [j]; rw [W.c₄_of_char_three]; rw [← pow_mul]

中文:
引理 j_of_char_three
  结论: W.j = W.Δ'⁻¹ * W.b₂ ^ 6
  证明: by
  rw [j]; rw [W.c₄_of_char_three]; rw [← pow_mul]

Depends on / 依赖: pow_mul
-/
lemma j_of_char_three : W.j = W.Δ'⁻¹ * W.b₂ ^ 6 := by
  rw [j]; rw [W.c₄_of_char_three]; rw [← pow_mul]

/--
lemma `j_eq_zero_iff_of_char_three'` / 引理 `j_eq_zero_iff_of_char_three'`

English:
lemma j_eq_zero_iff_of_char_three'
  statement: W.j = 0 ↔ W.b₂ ^ 6 = 0
  proof: by
  rw [j_of_char_three]; rw [Units.mul_right_eq_zero]

中文:
引理 j_eq_zero_iff_of_char_three'
  结论: W.j = 0 ↔ W.b₂ ^ 6 = 0
  证明: by
  rw [j_of_char_three]; rw [Units.mul_right_eq_zero]

Depends on / 依赖: Units.mul_right_eq_zero, j_of_char_three, mul_right_eq_zero
-/
lemma j_eq_zero_iff_of_char_three' : W.j = 0 ↔ W.b₂ ^ 6 = 0 := by
  rw [j_of_char_three]; rw [Units.mul_right_eq_zero]

/--
lemma `j_eq_zero_of_char_three` / 引理 `j_eq_zero_of_char_three`

English:
lemma j_eq_zero_of_char_three
  given: (h : W.b₂ = 0)
  statement: W.j = 0
  proof: by
  rw [j_eq_zero_iff_of_char_three']; rw [h]; rw [zero_pow (Nat.succ_ne_zero _)]

中文:
引理 j_eq_zero_of_char_three
  条件: (h : W.b₂ = 0)
  结论: W.j = 0
  证明: by
  rw [j_eq_zero_iff_of_char_three']; rw [h]; rw [zero_pow (Nat.succ_ne_zero _)]

Depends on / 依赖: Nat.succ_ne_zero, j_eq_zero_iff_of_char_three, succ_ne_zero, zero_pow
-/
lemma j_eq_zero_of_char_three (h : W.b₂ = 0) : W.j = 0 := by
  rw [j_eq_zero_iff_of_char_three']; rw [h]; rw [zero_pow (Nat.succ_ne_zero _)]

/--
lemma `j_eq_zero_iff_of_char_three` / 引理 `j_eq_zero_iff_of_char_three`

English:
lemma j_eq_zero_iff_of_char_three
  given: [IsReduced R]
  statement: W.j = 0 ↔ W.b₂ = 0
  proof: by
  rw [j_eq_zero_iff_of_char_three']; rw [pow_eq_zero_iff (Nat.succ_ne_zero _)]

中文:
引理 j_eq_zero_iff_of_char_three
  条件: [是既约 R]
  结论: W.j = 0 ↔ W.b₂ = 0
  证明: by
  rw [j_eq_zero_iff_of_char_three']; rw [pow_eq_zero_iff (Nat.succ_ne_zero _)]

Depends on / 依赖: Nat.succ_ne_zero, j_eq_zero_iff_of_char_three, pow_eq_zero_iff, succ_ne_zero
-/
lemma j_eq_zero_iff_of_char_three [IsReduced R] : W.j = 0 ↔ W.b₂ = 0 := by
  rw [j_eq_zero_iff_of_char_three']; rw [pow_eq_zero_iff (Nat.succ_ne_zero _)]

end CharThree

-- TODO: this is defeq to `twoTorsionPolynomial_discr_ne_zero` once https://github.com/leanprover-community/mathlib4/issues/17458 is merged,
-- TODO: consider removing/rephrasing this result
/--
lemma `twoTorsionPolynomial_discr_ne_zero_of_isElliptic` / 引理 `twoTorsionPolynomial_discr_ne_zero_of_isElliptic`

English:
lemma twoTorsionPolynomial_discr_ne_zero_of_isElliptic
  given: [Nontrivial R] (hu : IsUnit (2 : R))
  proof: W.twoTorsionPolynomial_discr_ne_zero hu W.isUnit_Δ

中文:
引理 twoTorsionPolynomial_discr_ne_zero_of_isElliptic
  条件: [非平凡 R] (hu : 是单位 (2 : R))
  证明: W.twoTorsionPolynomial_discr_ne_zero hu W.isUnit_Δ

Depends on / 依赖: Subsingleton, Subsingleton.elim, W.isUnit_, W.twoTorsionPolynomial_discr_ne_zero, twoTorsionPolynomial_discr_ne_zero
-/
lemma twoTorsionPolynomial_discr_ne_zero_of_isElliptic [Nontrivial R] (hu : IsUnit (2 : R)) :
    W.twoTorsionPolynomial.discr != 0 :=
  W.twoTorsionPolynomial_discr_ne_zero hu W.isUnit_Δ

section BaseChange

/-! ### Maps and base changes -/

variable {A : Type v} [CommRing A] (f : R ->+* A)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (W.map f).IsElliptic
  body: by
  simp only [isElliptic_iff, map_Δ, W.isUnit_Δ.map]

中文:
实例 :
  签名: (W.map f).是Elliptic
  定义体: by
  simp only [isElliptic_iff, map_Δ, W.isUnit_Δ.map]

Depends on / 依赖: W.isUnit_, isElliptic_iff
-/
instance : (W.map f).IsElliptic := by
  simp only [isElliptic_iff, map_Δ, W.isUnit_Δ.map]

set_option linter.docPrime false in
/--
lemma `coe_map_Δ'` / 引理 `coe_map_Δ'`

English:
lemma coe_map_Δ'
  statement: (W.map f).Δ' = f W.Δ'
  proof: by
  rw [coe_Δ']; rw [map_Δ]; rw [coe_Δ']

中文:
引理 coe_map_Δ'
  结论: (W.map f).Δ' = f W.Δ'
  证明: by
  rw [coe_Δ']; rw [map_Δ]; rw [coe_Δ']
-/
lemma coe_map_Δ' : (W.map f).Δ' = f W.Δ' := by
  rw [coe_Δ']; rw [map_Δ]; rw [coe_Δ']

set_option linter.docPrime false in
@[simp]
/--
lemma `map_Δ'` / 引理 `map_Δ'`

English:
lemma map_Δ'
  statement: (W.map f).Δ' = Units.map f W.Δ'
  proof: by
  ext
  exact W.coe_map_Δ' f

中文:
引理 map_Δ'
  结论: (W.map f).Δ' = 单位群.map f W.Δ'
  证明: by
  ext
  exact W.coe_map_Δ' f

Depends on / 依赖: W.coe_map_
-/
lemma map_Δ' : (W.map f).Δ' = Units.map f W.Δ' := by
  ext
  exact W.coe_map_Δ' f

set_option linter.docPrime false in
/--
lemma `coe_inv_map_Δ'` / 引理 `coe_inv_map_Δ'`

English:
lemma coe_inv_map_Δ'
  statement: (W.map f).Δ'⁻¹ = f ↑W.Δ'⁻¹
  proof: by
  simp

中文:
引理 coe_inv_map_Δ'
  结论: (W.map f).Δ'⁻¹ = f ↑W.Δ'⁻¹
  证明: by
  simp
-/
lemma coe_inv_map_Δ' : (W.map f).Δ'⁻¹ = f ↑W.Δ'⁻¹ := by
  simp

set_option linter.docPrime false in
/--
lemma `inv_map_Δ'` / 引理 `inv_map_Δ'`

English:
lemma inv_map_Δ'
  statement: (W.map f).Δ'⁻¹ = Units.map f W.Δ'⁻¹
  proof: by
  simp

@[simp]

中文:
引理 inv_map_Δ'
  结论: (W.map f).Δ'⁻¹ = 单位群.map f W.Δ'⁻¹
  证明: by
  simp

@[simp]
-/
lemma inv_map_Δ' : (W.map f).Δ'⁻¹ = Units.map f W.Δ'⁻¹ := by
  simp

@[simp]
/--
lemma `map_j` / 引理 `map_j`

English:
lemma map_j
  statement: (W.map f).j = f W.j
  proof: by
  rw [j]; rw [coe_inv_map_Δ']; rw [map_c₄]; rw [j]; rw [map_mul]; rw [map_pow]

中文:
引理 map_j
  结论: (W.map f).j = f W.j
  证明: by
  rw [j]; rw [coe_inv_map_Δ']; rw [map_c₄]; rw [j]; rw [map_mul]; rw [map_pow]

Depends on / 依赖: map_mul, map_pow
-/
lemma map_j : (W.map f).j = f W.j := by
  rw [j]; rw [coe_inv_map_Δ']; rw [map_c₄]; rw [j]; rw [map_mul]; rw [map_pow]

end BaseChange

end WeierstrassCurve
