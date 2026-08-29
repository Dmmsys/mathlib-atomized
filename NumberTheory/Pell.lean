/-
Copyright (c) 2023 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Geißer, Michael Stoll
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.DiophantineApproximation.Basic
public import Mathlib.NumberTheory.Zsqrtd.Basic
public import Mathlib.Tactic.Qify

/-!
# Pell's Equation

*Pell's Equation* is the equation $x^2 - d y^2 = 1$, where $d$ is a positive integer
that is not a square, and one is interested in solutions in integers $x$ and $y$.

In this file, we aim at providing all of the essential theory of Pell's Equation for general $d$
(as opposed to the contents of `NumberTheory.PellMatiyasevic`, which is specific to the case
$d = a^2 - 1$ for some $a > 1$).

We begin by defining a type `Pell.Solution₁ d` for solutions of the equation,
show that it has a natural structure as an abelian group, and prove some basic
properties.

We then prove the following

**Theorem.** Let $d$ be a positive integer that is not a square. Then the equation
$x^2 - d y^2 = 1$ has a nontrivial (i.e., with $y \ne 0$) solution in integers.

See `Pell.exists_of_not_isSquare` and `Pell.Solution₁.exists_nontrivial_of_not_isSquare`.

We then define the *fundamental solution* to be the solution
with smallest $x$ among all solutions satisfying $x > 1$ and $y > 0$.
We show that every solution is a power (in the sense of the group structure mentioned above)
of the fundamental solution up to a (common) sign,
see `Pell.IsFundamental.eq_zpow_or_neg_zpow`, and that a (positive) solution has this property
if and only if it is fundamental, see `Pell.pos_generator_iff_fundamental`.

## References

* [K. Ireland, M. Rosen, *A classical introduction to modern number theory* (Section 17.5)]
  [IrelandRosen1990]

## Tags

Pell's equation

## TODO

* Extend to `x ^ 2 - d * y ^ 2 = -1` and further generalizations.
* Connect solutions to the continued fraction expansion of `√d`.
-/

@[expose] public section


namespace Pell

/-!
### Group structure of the solution set

We define a structure of a commutative multiplicative group with distributive negation
on the set of all solutions to the Pell equation `x^2 - d*y^2 = 1`.

The type of such solutions is `Pell.Solution₁ d`. It corresponds to a pair of integers `x` and `y`
and a proof that `(x, y)` is indeed a solution.

The multiplication is given by `(x, y) * (x', y') = (x*x' + d*y*y', x*y' + y*x')`.
This is obtained by mapping `(x, y)` to `x + y*√d` and multiplying the results.
In fact, we define `Pell.Solution₁ d` to be `↥(unitary (ℤ√d))` and transport
the "commutative group with distributive negation" structure from `↥(unitary (ℤ√d))`.

We then set up an API for `Pell.Solution₁ d`.
-/


open CharZero Zsqrtd

/--
theorem `is_pell_solution_iff_mem_unitary` / 定理 `is_pell_solution_iff_mem_unitary`

English:
theorem is_pell_solution_iff_mem_unitary
  given: {d : Int} {a : Int√d}
  proof: by
  rw [← norm_eq_one_iff_mem_unitary]; rw [norm_def]; rw [sq]; rw [sq]; rw [← mul_assoc]

中文:
定理 is_pell_solution_iff_mem_unitary
  条件: {d : 整数} {a : 整数√d}
  证明: by
  rw [← norm_eq_one_iff_mem_unitary]; rw [norm_def]; rw [sq]; rw [sq]; rw [← mul_assoc]

Depends on / 依赖: mul_assoc, norm_def, norm_eq_one_iff_mem_unitary
-/
theorem is_pell_solution_iff_mem_unitary {d : Int} {a : Int√d} :
    a.re ^ 2 - d * a.im ^ 2 = 1 ↔ a in unitary (Int√d) := by
  rw [← norm_eq_one_iff_mem_unitary]; rw [norm_def]; rw [sq]; rw [sq]; rw [← mul_assoc]

-- We use `solution₁ d` to allow for a more general structure `solution d m` that
-- encodes solutions to `x^2 - d*y^2 = m` to be added later.
/--
Definition of `Solution₁` / `Solution₁` 的定义

English:
definition Solution₁
  signature: (d : Int)
  body: ↥(unitary (Int√d))

中文:
定义 Solution₁
  签名: (d : 整数)
  定义体: ↥(unitary (Int√d))

Depends on / 依赖: unitary
-/
def Solution₁ (d : Int) : Type :=
  ↥(unitary (Int√d))

namespace Solution₁

variable {d : Int}

/--
Instance `instCommGroup` / 实例 `instCommGroup`

English:
instance instCommGroup
  signature: : CommGroup (Solution₁ d)
  body: inferInstanceAs (CommGroup (unitary (Int√d)))

中文:
实例 instCommGroup
  签名: : 交换群 (Solution₁ d)
  定义体: inferInstanceAs (CommGroup (unitary (Int√d)))

Depends on / 依赖: CommGroup, unitary
-/
instance instCommGroup : CommGroup (Solution₁ d) :=
  inferInstanceAs (CommGroup (unitary (Int√d)))

/--
Instance `instHasDistribNeg` / 实例 `instHasDistribNeg`

English:
instance instHasDistribNeg
  signature: : HasDistribNeg (Solution₁ d)
  body: inferInstanceAs (HasDistribNeg (unitary (Int√d)))

中文:
实例 instHasDistribNeg
  签名: : 有DistribNeg (Solution₁ d)
  定义体: inferInstanceAs (HasDistribNeg (unitary (Int√d)))

Depends on / 依赖: HasDistribNeg, unitary
-/
instance instHasDistribNeg : HasDistribNeg (Solution₁ d) :=
  inferInstanceAs (HasDistribNeg (unitary (Int√d)))

/--
Instance `instInhabited` / 实例 `instInhabited`

English:
instance instInhabited
  signature: : Inhabited (Solution₁ d)
  body: inferInstanceAs (Inhabited (unitary (Int√d)))

中文:
实例 instInhabited
  签名: : 可居 (Solution₁ d)
  定义体: inferInstanceAs (Inhabited (unitary (Int√d)))

Depends on / 依赖: Inhabited, unitary
-/
instance instInhabited : Inhabited (Solution₁ d) :=
  inferInstanceAs (Inhabited (unitary (Int√d)))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe (Solution₁ d) (Int√d)
  body: Subtype.val

中文:
实例 :
  签名: Coe (Solution₁ d) (整数√d)
  定义体: Subtype.val

Depends on / 依赖: Subtype, Subtype.val
-/
instance : Coe (Solution₁ d) (Int√d) where coe := Subtype.val

/--
Definition of `x` / `x` 的定义

English:
definition x
  signature: (a : Solution₁ d)
  body: (a : Int√d).re

中文:
定义 x
  签名: (a : Solution₁ d)
  定义体: (a : Int√d).re
-/
protected def x (a : Solution₁ d) : Int :=
  (a : Int√d).re

/--
Definition of `y` / `y` 的定义

English:
definition y
  signature: (a : Solution₁ d)
  body: (a : Int√d).im

中文:
定义 y
  签名: (a : Solution₁ d)
  定义体: (a : Int√d).im
-/
protected def y (a : Solution₁ d) : Int :=
  (a : Int√d).im

/--
theorem `prop` / 定理 `prop`

English:
theorem prop
  given: (a : Solution₁ d)
  statement: a.x ^ 2 - d * a.y ^ 2 = 1
  proof: is_pell_solution_iff_mem_unitary.mpr a.property

中文:
定理 prop
  条件: (a : Solution₁ d)
  结论: a.x ^ 2 - d * a.y ^ 2 = 1
  证明: is_pell_solution_iff_mem_unitary.mpr a.property

Depends on / 依赖: a.property, is_pell_solution_iff_mem_unitary, is_pell_solution_iff_mem_unitary.mpr, property
-/
theorem prop (a : Solution₁ d) : a.x ^ 2 - d * a.y ^ 2 = 1 :=
  is_pell_solution_iff_mem_unitary.mpr a.property

/--
theorem `prop_x` / 定理 `prop_x`

English:
theorem prop_x
  given: (a : Solution₁ d)
  statement: a.x ^ 2 = 1 + d * a.y ^ 2
  proof: by rw [← a.prop]; ring

中文:
定理 prop_x
  条件: (a : Solution₁ d)
  结论: a.x ^ 2 = 1 + d * a.y ^ 2
  证明: by rw [← a.prop]; ring

Depends on / 依赖: a.prop
-/
theorem prop_x (a : Solution₁ d) : a.x ^ 2 = 1 + d * a.y ^ 2 := by rw [← a.prop]; ring

/--
theorem `prop_y` / 定理 `prop_y`

English:
theorem prop_y
  given: (a : Solution₁ d)
  statement: d * a.y ^ 2 = a.x ^ 2 - 1
  proof: by rw [← a.prop]; ring

中文:
定理 prop_y
  条件: (a : Solution₁ d)
  结论: d * a.y ^ 2 = a.x ^ 2 - 1
  证明: by rw [← a.prop]; ring

Depends on / 依赖: a.prop
-/
theorem prop_y (a : Solution₁ d) : d * a.y ^ 2 = a.x ^ 2 - 1 := by rw [← a.prop]; ring

/-- Two solutions are equal if their `x` and `y` components are equal. -/
@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {a b : Solution₁ d} (hx : a.x = b.x) (hy : a.y = b.y)
  statement: a = b
  proof: Subtype.ext Zsqrtd.ext hx hy

中文:
定理 ext
  条件: {a b : Solution₁ d} (hx : a.x = b.x) (hy : a.y = b.y)
  结论: a = b
  证明: Subtype.ext Zsqrtd.ext hx hy

Depends on / 依赖: Subtype, Subtype.ext, Zsqrtd, Zsqrtd.ext
-/
theorem ext {a b : Solution₁ d} (hx : a.x = b.x) (hy : a.y = b.y) : a = b :=
Subtype.ext Zsqrtd.ext hx hy

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: (x y : Int) (prop : x ^ 2 - d * y ^ 2 = 1)
  body: ⟨x, y⟩
  property := is_pell_solution_iff_mem_unitary.mp prop

@[simp]

中文:
定义 mk
  签名: (x y : 整数) (prop : x ^ 2 - d * y ^ 2 = 1)
  定义体: ⟨x, y⟩
  property := is_pell_solution_iff_mem_unitary.mp prop

@[simp]
-/
def mk (x y : Int) (prop : x ^ 2 - d * y ^ 2 = 1) : Solution₁ d where
  val := ⟨x, y⟩
  property := is_pell_solution_iff_mem_unitary.mp prop

@[simp]
/--
theorem `x_mk` / 定理 `x_mk`

English:
theorem x_mk
  given: (x y : Int) (prop : x ^ 2 - d * y ^ 2 = 1)
  statement: (mk x y prop).x = x
  proof: rfl

@[simp]

中文:
定理 x_mk
  条件: (x y : 整数) (prop : x ^ 2 - d * y ^ 2 = 1)
  结论: (mk x y prop).x = x
  证明: rfl

@[simp]
-/
theorem x_mk (x y : Int) (prop : x ^ 2 - d * y ^ 2 = 1) : (mk x y prop).x = x :=
  rfl

@[simp]
/--
theorem `y_mk` / 定理 `y_mk`

English:
theorem y_mk
  given: (x y : Int) (prop : x ^ 2 - d * y ^ 2 = 1)
  statement: (mk x y prop).y = y
  proof: rfl

@[simp]

中文:
定理 y_mk
  条件: (x y : 整数) (prop : x ^ 2 - d * y ^ 2 = 1)
  结论: (mk x y prop).y = y
  证明: rfl

@[simp]
-/
theorem y_mk (x y : Int) (prop : x ^ 2 - d * y ^ 2 = 1) : (mk x y prop).y = y :=
  rfl

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (x y : Int) (prop : x ^ 2 - d * y ^ 2 = 1)
  statement: (↑(mk x y prop) : Int√d) = ⟨x, y⟩
  proof: Zsqrtd.ext (x_mk x y prop) (y_mk x y prop)

@[simp]

中文:
定理 coe_mk
  条件: (x y : 整数) (prop : x ^ 2 - d * y ^ 2 = 1)
  结论: (↑(mk x y prop) : 整数√d) = ⟨x, y⟩
  证明: Zsqrtd.ext (x_mk x y prop) (y_mk x y prop)

@[simp]

Depends on / 依赖: Zsqrtd, Zsqrtd.ext, x_mk, y_mk
-/
theorem coe_mk (x y : Int) (prop : x ^ 2 - d * y ^ 2 = 1) : (↑(mk x y prop) : Int√d) = ⟨x, y⟩ :=
  Zsqrtd.ext (x_mk x y prop) (y_mk x y prop)

@[simp]
/--
theorem `x_one` / 定理 `x_one`

English:
theorem x_one
  statement: (1 : Solution₁ d).x = 1
  proof: rfl

@[simp]

中文:
定理 x_one
  结论: (1 : Solution₁ d).x = 1
  证明: rfl

@[simp]
-/
theorem x_one : (1 : Solution₁ d).x = 1 :=
  rfl

@[simp]
/--
theorem `y_one` / 定理 `y_one`

English:
theorem y_one
  statement: (1 : Solution₁ d).y = 0
  proof: rfl

@[simp]

中文:
定理 y_one
  结论: (1 : Solution₁ d).y = 0
  证明: rfl

@[simp]
-/
theorem y_one : (1 : Solution₁ d).y = 0 :=
  rfl

@[simp]
/--
theorem `x_mul` / 定理 `x_mul`

English:
theorem x_mul
  given: (a b : Solution₁ d)
  statement: (a * b).x = a.x * b.x + d * (a.y * b.y)
  proof: by
  rw [← mul_assoc]
  rfl

@[simp]

中文:
定理 x_mul
  条件: (a b : Solution₁ d)
  结论: (a * b).x = a.x * b.x + d * (a.y * b.y)
  证明: by
  rw [← mul_assoc]
  rfl

@[simp]

Depends on / 依赖: mul_assoc
-/
theorem x_mul (a b : Solution₁ d) : (a * b).x = a.x * b.x + d * (a.y * b.y) := by
  rw [← mul_assoc]
  rfl

@[simp]
/--
theorem `y_mul` / 定理 `y_mul`

English:
theorem y_mul
  given: (a b : Solution₁ d)
  statement: (a * b).y = a.x * b.y + a.y * b.x
  proof: rfl

@[simp]

中文:
定理 y_mul
  条件: (a b : Solution₁ d)
  结论: (a * b).y = a.x * b.y + a.y * b.x
  证明: rfl

@[simp]
-/
theorem y_mul (a b : Solution₁ d) : (a * b).y = a.x * b.y + a.y * b.x :=
  rfl

@[simp]
/--
theorem `x_inv` / 定理 `x_inv`

English:
theorem x_inv
  given: (a : Solution₁ d)
  statement: a⁻¹.x = a.x
  proof: rfl

@[simp]

中文:
定理 x_inv
  条件: (a : Solution₁ d)
  结论: a⁻¹.x = a.x
  证明: rfl

@[simp]
-/
theorem x_inv (a : Solution₁ d) : a⁻¹.x = a.x :=
  rfl

@[simp]
/--
theorem `y_inv` / 定理 `y_inv`

English:
theorem y_inv
  given: (a : Solution₁ d)
  statement: a⁻¹.y = -a.y
  proof: rfl

@[simp]

中文:
定理 y_inv
  条件: (a : Solution₁ d)
  结论: a⁻¹.y = -a.y
  证明: rfl

@[simp]
-/
theorem y_inv (a : Solution₁ d) : a⁻¹.y = -a.y :=
  rfl

@[simp]
/--
theorem `x_neg` / 定理 `x_neg`

English:
theorem x_neg
  given: (a : Solution₁ d)
  statement: (-a).x = -a.x
  proof: rfl

@[simp]

中文:
定理 x_neg
  条件: (a : Solution₁ d)
  结论: (-a).x = -a.x
  证明: rfl

@[simp]
-/
theorem x_neg (a : Solution₁ d) : (-a).x = -a.x :=
  rfl

@[simp]
/--
theorem `y_neg` / 定理 `y_neg`

English:
theorem y_neg
  given: (a : Solution₁ d)
  statement: (-a).y = -a.y
  proof: rfl

中文:
定理 y_neg
  条件: (a : Solution₁ d)
  结论: (-a).y = -a.y
  证明: rfl
-/
theorem y_neg (a : Solution₁ d) : (-a).y = -a.y :=
  rfl

/--
theorem `eq_zero_of_d_neg` / 定理 `eq_zero_of_d_neg`

English:
theorem eq_zero_of_d_neg
  given: (h₀ : d < 0) (a : Solution₁ d)
  statement: a.x = 0 ∨ a.y = 0
  proof: by
  have h := a.prop
  contrapose! h
  have h1 := sq_pos_of_ne_zero h.1
  have h2 := sq_pos_of_ne_zero h.2
  nlinarith

中文:
定理 eq_zero_of_d_neg
  条件: (h₀ : d < 0) (a : Solution₁ d)
  结论: a.x = 0 ∨ a.y = 0
  证明: by
  have h := a.prop
  contrapose! h
  have h1 := sq_pos_of_ne_zero h.1
  have h2 := sq_pos_of_ne_zero h.2
  nlinarith

Depends on / 依赖: a.prop, contrapose, sq_pos_of_ne_zero
-/
theorem eq_zero_of_d_neg (h₀ : d < 0) (a : Solution₁ d) : a.x = 0 ∨ a.y = 0 := by
  have h := a.prop
  contrapose! h
  have h1 := sq_pos_of_ne_zero h.1
  have h2 := sq_pos_of_ne_zero h.2
  nlinarith

/--
theorem `x_ne_zero` / 定理 `x_ne_zero`

English:
theorem x_ne_zero
  given: (h₀ : 0 <= d) (a : Solution₁ d)
  statement: a.x != 0
  proof: by
  intro hx
  have h : 0 <= d * a.y ^ 2 := mul_nonneg h₀ (sq_nonneg _)
  rw [a.prop_y]; rw [hx]; rw [sq]; rw [zero_mul]; rw [zero_sub] at h
  exact not_le.mpr (neg_one_lt_zero : (-1 : Int) < 0) h

中文:
定理 x_ne_zero
  条件: (h₀ : 0 <= d) (a : Solution₁ d)
  结论: a.x != 0
  证明: by
  intro hx
  have h : 0 <= d * a.y ^ 2 := mul_nonneg h₀ (sq_nonneg _)
  rw [a.prop_y]; rw [hx]; rw [sq]; rw [zero_mul]; rw [zero_sub] at h
  exact not_le.mpr (neg_one_lt_zero : (-1 : Int) < 0) h

Depends on / 依赖: a.prop_y, mul_nonneg, neg_one_lt_zero, not_le, not_le.mpr, prop_y, sq_nonneg, zero_mul, zero_sub
-/
theorem x_ne_zero (h₀ : 0 <= d) (a : Solution₁ d) : a.x != 0 := by
  intro hx
  have h : 0 <= d * a.y ^ 2 := mul_nonneg h₀ (sq_nonneg _)
  rw [a.prop_y]; rw [hx]; rw [sq]; rw [zero_mul]; rw [zero_sub] at h
  exact not_le.mpr (neg_one_lt_zero : (-1 : Int) < 0) h

/--
theorem `y_ne_zero_of_one_lt_x` / 定理 `y_ne_zero_of_one_lt_x`

English:
theorem y_ne_zero_of_one_lt_x
  given: {a : Solution₁ d} (ha : 1 < a.x)
  statement: a.y != 0
  proof: by
  intro hy
  have prop := a.prop
  rw [hy]; rw [sq (0 : Int)]; rw [zero_mul]; rw [mul_zero]; rw [sub_zero] at prop
  exact lt_irrefl _ (((one_lt_sq_iff₀ <| zero_le_one.trans ha.le).mpr ha).trans_eq prop)

中文:
定理 y_ne_zero_of_one_lt_x
  条件: {a : Solution₁ d} (ha : 1 < a.x)
  结论: a.y != 0
  证明: by
  intro hy
  have prop := a.prop
  rw [hy]; rw [sq (0 : Int)]; rw [zero_mul]; rw [mul_zero]; rw [sub_zero] at prop
  exact lt_irrefl _ (((one_lt_sq_iff₀ <| zero_le_one.trans ha.le).mpr ha).trans_eq prop)

Depends on / 依赖: a.prop, ha.le, lt_irrefl, mul_zero, sub_zero, trans_eq, zero_le_one, zero_le_one.trans, zero_mul
-/
theorem y_ne_zero_of_one_lt_x {a : Solution₁ d} (ha : 1 < a.x) : a.y != 0 := by
  intro hy
  have prop := a.prop
  rw [hy]; rw [sq (0 : Int)]; rw [zero_mul]; rw [mul_zero]; rw [sub_zero] at prop
  exact lt_irrefl _ (((one_lt_sq_iff₀ <| zero_le_one.trans ha.le).mpr ha).trans_eq prop)

/--
theorem `d_pos_of_one_lt_x` / 定理 `d_pos_of_one_lt_x`

English:
theorem d_pos_of_one_lt_x
  given: {a : Solution₁ d} (ha : 1 < a.x)
  statement: 0 < d
  proof: by
  refine pos_of_mul_pos_left ?_ (sq_nonneg a.y)
  rw [a.prop_y]; rw [sub_pos]
  exact one_lt_pow₀ ha two_ne_zero

中文:
定理 d_pos_of_one_lt_x
  条件: {a : Solution₁ d} (ha : 1 < a.x)
  结论: 0 < d
  证明: by
  refine pos_of_mul_pos_left ?_ (sq_nonneg a.y)
  rw [a.prop_y]; rw [sub_pos]
  exact one_lt_pow₀ ha two_ne_zero

Depends on / 依赖: a.prop_y, pos_of_mul_pos_left, prop_y, sq_nonneg, sub_pos, two_ne_zero
-/
theorem d_pos_of_one_lt_x {a : Solution₁ d} (ha : 1 < a.x) : 0 < d := by
  refine pos_of_mul_pos_left ?_ (sq_nonneg a.y)
  rw [a.prop_y]; rw [sub_pos]
  exact one_lt_pow₀ ha two_ne_zero

/--
theorem `d_nonsquare_of_one_lt_x` / 定理 `d_nonsquare_of_one_lt_x`

English:
theorem d_nonsquare_of_one_lt_x
  given: {a : Solution₁ d} (ha : 1 < a.x)
  statement: ¬IsSquare d
  proof: by
  have hp := a.prop
  rintro ⟨b, rfl⟩
  simp_rw [← sq, ← mul_pow, sq_sub_sq, Int.mul_eq_one_iff_eq_one_or_neg_one] at hp
  lia

中文:
定理 d_nonsquare_of_one_lt_x
  条件: {a : Solution₁ d} (ha : 1 < a.x)
  结论: ¬IsSquare d
  证明: by
  have hp := a.prop
  rintro ⟨b, rfl⟩
  simp_rw [← sq, ← mul_pow, sq_sub_sq, Int.mul_eq_one_iff_eq_one_or_neg_one] at hp
  lia

Depends on / 依赖: Int.mul_eq_one_iff_eq_one_or_neg_one, a.prop, mul_eq_one_iff_eq_one_or_neg_one, mul_pow, simp_rw, sq_sub_sq
-/
theorem d_nonsquare_of_one_lt_x {a : Solution₁ d} (ha : 1 < a.x) : ¬IsSquare d := by
  have hp := a.prop
  rintro ⟨b, rfl⟩
  simp_rw [← sq, ← mul_pow, sq_sub_sq, Int.mul_eq_one_iff_eq_one_or_neg_one] at hp
  lia

/--
theorem `eq_one_of_x_eq_one` / 定理 `eq_one_of_x_eq_one`

English:
theorem eq_one_of_x_eq_one
  given: (h₀ : d != 0) {a : Solution₁ d} (ha : a.x = 1)
  statement: a = 1
  proof: by
  have prop := a.prop_y
  rw [ha]; rw [one_pow]; rw [sub_self]; rw [mul_eq_zero]; rw [or_iff_right h₀]; rw [sq_eq_zero_iff] at prop
  exact ext ha prop

中文:
定理 eq_one_of_x_eq_one
  条件: (h₀ : d != 0) {a : Solution₁ d} (ha : a.x = 1)
  结论: a = 1
  证明: by
  have prop := a.prop_y
  rw [ha]; rw [one_pow]; rw [sub_self]; rw [mul_eq_zero]; rw [or_iff_right h₀]; rw [sq_eq_zero_iff] at prop
  exact ext ha prop

Depends on / 依赖: a.prop_y, mul_eq_zero, one_pow, or_iff_right, prop_y, sq_eq_zero_iff, sub_self
-/
theorem eq_one_of_x_eq_one (h₀ : d != 0) {a : Solution₁ d} (ha : a.x = 1) : a = 1 := by
  have prop := a.prop_y
  rw [ha]; rw [one_pow]; rw [sub_self]; rw [mul_eq_zero]; rw [or_iff_right h₀]; rw [sq_eq_zero_iff] at prop
  exact ext ha prop

/--
theorem `eq_one_or_neg_one_iff_y_eq_zero` / 定理 `eq_one_or_neg_one_iff_y_eq_zero`

English:
theorem eq_one_or_neg_one_iff_y_eq_zero
  given: {a : Solution₁ d}
  statement: a = 1 ∨ a = -1 ↔ a.y = 0
  proof: by
  refine ⟨fun H => H.elim (fun h => by simp [h]) fun h => by simp [h], fun H => ?_⟩
  have prop := a.prop
  rw [H]; rw [sq (0 : Int)]; rw [mul_zero]; rw [mul_zero]; rw [sub_zero]; rw [sq_eq_one_iff] at prop
  exact prop.imp (fun h => ext h H) fun h => ext h H

中文:
定理 eq_one_or_neg_one_iff_y_eq_zero
  条件: {a : Solution₁ d}
  结论: a = 1 ∨ a = -1 ↔ a.y = 0
  证明: by
  refine ⟨fun H => H.elim (fun h => by simp [h]) fun h => by simp [h], fun H => ?_⟩
  have prop := a.prop
  rw [H]; rw [sq (0 : Int)]; rw [mul_zero]; rw [mul_zero]; rw [sub_zero]; rw [sq_eq_one_iff] at prop
  exact prop.imp (fun h => ext h H) fun h => ext h H

Depends on / 依赖: H.elim, a.prop, mul_zero, prop.imp, sq_eq_one_iff, sub_zero
-/
theorem eq_one_or_neg_one_iff_y_eq_zero {a : Solution₁ d} : a = 1 ∨ a = -1 ↔ a.y = 0 := by
  refine ⟨fun H => H.elim (fun h => by simp [h]) fun h => by simp [h], fun H => ?_⟩
  have prop := a.prop
  rw [H]; rw [sq (0 : Int)]; rw [mul_zero]; rw [mul_zero]; rw [sub_zero]; rw [sq_eq_one_iff] at prop
  exact prop.imp (fun h => ext h H) fun h => ext h H

/--
theorem `x_mul_pos` / 定理 `x_mul_pos`

English:
theorem x_mul_pos
  given: {a b : Solution₁ d} (ha : 0 < a.x) (hb : 0 < b.x)
  statement: 0 < (a * b).x
  proof: by
  simp only [x_mul]
  refine neg_lt_iff_pos_add'.mp (abs_lt.mp ?_).1
  rw [← abs_of_pos ha]; rw [← abs_of_pos hb]; rw [← abs_mul]; rw [← sq_lt_sq]; rw [mul_pow a.x]; rw [a.prop_x]; rw [b.prop_x]; rw [←
    sub_pos]
  ring_nf
  rcases le_or_gt 0 d with h | h
  · positivity
  · rw [(eq_zero_of_d_neg h a).resolve_left ha.ne', (eq_zero_of_d_neg h b).resolve_left hb.ne']
    simp

中文:
定理 x_mul_pos
  条件: {a b : Solution₁ d} (ha : 0 < a.x) (hb : 0 < b.x)
  结论: 0 < (a * b).x
  证明: by
  simp only [x_mul]
  refine neg_lt_iff_pos_add'.mp (abs_lt.mp ?_).1
  rw [← abs_of_pos ha]; rw [← abs_of_pos hb]; rw [← abs_mul]; rw [← sq_lt_sq]; rw [mul_pow a.x]; rw [a.prop_x]; rw [b.prop_x]; rw [←
    sub_pos]
  ring_nf
  rcases le_or_gt 0 d with h | h
  · positivity
  · rw [(eq_zero_of_d_neg h a).resolve_left ha.ne', (eq_zero_of_d_neg h b).resolve_left hb.ne']
    simp

Depends on / 依赖: a.prop_x, abs_lt, abs_lt.mp, abs_mul, abs_of_pos, b.prop_x, eq_zero_of_d_neg, ha.ne, hb.ne, le_or_gt, mul_pow, neg_lt_iff_pos_add, prop_x, resolve_left, ring_nf, sq_lt_sq, sub_pos, x_mul
-/
theorem x_mul_pos {a b : Solution₁ d} (ha : 0 < a.x) (hb : 0 < b.x) : 0 < (a * b).x := by
  simp only [x_mul]
  refine neg_lt_iff_pos_add'.mp (abs_lt.mp ?_).1
  rw [← abs_of_pos ha]; rw [← abs_of_pos hb]; rw [← abs_mul]; rw [← sq_lt_sq]; rw [mul_pow a.x]; rw [a.prop_x]; rw [b.prop_x]; rw [←
    sub_pos]
  ring_nf
  rcases le_or_gt 0 d with h | h
  · positivity
  · rw [(eq_zero_of_d_neg h a).resolve_left ha.ne', (eq_zero_of_d_neg h b).resolve_left hb.ne']
    simp

/--
theorem `y_mul_pos` / 定理 `y_mul_pos`

English:
theorem y_mul_pos
  statement: {a b : Solution₁ d} (hax : 0 < a.x) (hay : 0 < a.y) (hbx : 0 < b.x)
  proof: by
  simp only [y_mul]
  positivity

中文:
定理 y_mul_pos
  结论: {a b : Solution₁ d} (hax : 0 < a.x) (hay : 0 < a.y) (hbx : 0 < b.x)
  证明: by
  simp only [y_mul]
  positivity

Depends on / 依赖: y_mul
-/
theorem y_mul_pos {a b : Solution₁ d} (hax : 0 < a.x) (hay : 0 < a.y) (hbx : 0 < b.x)
    (hby : 0 < b.y) : 0 < (a * b).y := by
  simp only [y_mul]
  positivity

/--
theorem `x_pow_pos` / 定理 `x_pow_pos`

English:
theorem x_pow_pos
  given: {a : Solution₁ d} (hax : 0 < a.x) (n : Nat)
  statement: 0 < (a ^ n).x
  proof: by
  induction n with
  | zero => simp only [pow_zero, x_one, zero_lt_one]
  | succ n ih => rw [pow_succ]; exact x_mul_pos ih hax

中文:
定理 x_pow_pos
  条件: {a : Solution₁ d} (hax : 0 < a.x) (n : 自然数)
  结论: 0 < (a ^ n).x
  证明: by
  induction n with
  | zero => simp only [pow_zero, x_one, zero_lt_one]
  | succ n ih => rw [pow_succ]; exact x_mul_pos ih hax

Depends on / 依赖: pow_succ, pow_zero, x_mul_pos, x_one, zero_lt_one
-/
theorem x_pow_pos {a : Solution₁ d} (hax : 0 < a.x) (n : Nat) : 0 < (a ^ n).x := by
  induction n with
  | zero => simp only [pow_zero, x_one, zero_lt_one]
  | succ n ih => rw [pow_succ]; exact x_mul_pos ih hax

/--
theorem `y_pow_succ_pos` / 定理 `y_pow_succ_pos`

English:
theorem y_pow_succ_pos
  given: {a : Solution₁ d} (hax : 0 < a.x) (hay : 0 < a.y) (n : Nat)
  proof: by
  induction n with
  | zero => simp only [pow_one, hay]
  | succ n ih => rw [pow_succ']; exact y_mul_pos hax hay (x_pow_pos hax _) ih

中文:
定理 y_pow_succ_pos
  条件: {a : Solution₁ d} (hax : 0 < a.x) (hay : 0 < a.y) (n : 自然数)
  证明: by
  induction n with
  | zero => simp only [pow_one, hay]
  | succ n ih => rw [pow_succ']; exact y_mul_pos hax hay (x_pow_pos hax _) ih

Depends on / 依赖: pow_one, pow_succ, x_pow_pos, y_mul_pos
-/
theorem y_pow_succ_pos {a : Solution₁ d} (hax : 0 < a.x) (hay : 0 < a.y) (n : Nat) :
    0 < (a ^ n.succ).y := by
  induction n with
  | zero => simp only [pow_one, hay]
  | succ n ih => rw [pow_succ']; exact y_mul_pos hax hay (x_pow_pos hax _) ih

/--
theorem `y_zpow_pos` / 定理 `y_zpow_pos`

English:
theorem y_zpow_pos
  given: {a : Solution₁ d} (hax : 0 < a.x) (hay : 0 < a.y) {n : Int} (hn : 0 < n)
  proof: by
  lift n to Nat using hn.le
  norm_cast at hn ⊢
  rw [← Nat.succ_pred_eq_of_pos hn]
  exact y_pow_succ_pos hax hay _

中文:
定理 y_zpow_pos
  条件: {a : Solution₁ d} (hax : 0 < a.x) (hay : 0 < a.y) {n : 整数} (hn : 0 < n)
  证明: by
  lift n to Nat using hn.le
  norm_cast at hn ⊢
  rw [← Nat.succ_pred_eq_of_pos hn]
  exact y_pow_succ_pos hax hay _

Depends on / 依赖: Nat.succ_pred_eq_of_pos, hn.le, succ_pred_eq_of_pos, y_pow_succ_pos
-/
theorem y_zpow_pos {a : Solution₁ d} (hax : 0 < a.x) (hay : 0 < a.y) {n : Int} (hn : 0 < n) :
    0 < (a ^ n).y := by
  lift n to Nat using hn.le
  norm_cast at hn ⊢
  rw [← Nat.succ_pred_eq_of_pos hn]
  exact y_pow_succ_pos hax hay _

/--
theorem `x_zpow_pos` / 定理 `x_zpow_pos`

English:
theorem x_zpow_pos
  given: {a : Solution₁ d} (hax : 0 < a.x) (n : Int)
  statement: 0 < (a ^ n).x
  proof: by
  cases n with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast]; rw [zpow_natCast]
    exact x_pow_pos hax n
  | negSucc n =>
    rw [zpow_negSucc]
    exact x_pow_pos hax (n + 1)

中文:
定理 x_zpow_pos
  条件: {a : Solution₁ d} (hax : 0 < a.x) (n : 整数)
  结论: 0 < (a ^ n).x
  证明: by
  cases n with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast]; rw [zpow_natCast]
    exact x_pow_pos hax n
  | negSucc n =>
    rw [zpow_negSucc]
    exact x_pow_pos hax (n + 1)

Depends on / 依赖: Int.ofNat_eq_natCast, negSucc, ofNat_eq_natCast, x_pow_pos, zpow_natCast, zpow_negSucc
-/
theorem x_zpow_pos {a : Solution₁ d} (hax : 0 < a.x) (n : Int) : 0 < (a ^ n).x := by
  cases n with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast]; rw [zpow_natCast]
    exact x_pow_pos hax n
  | negSucc n =>
    rw [zpow_negSucc]
    exact x_pow_pos hax (n + 1)

/--
theorem `sign_y_zpow_eq_sign_of_x_pos_of_y_pos` / 定理 `sign_y_zpow_eq_sign_of_x_pos_of_y_pos`

English:
theorem sign_y_zpow_eq_sign_of_x_pos_of_y_pos
  statement: {a : Solution₁ d} (hax : 0 < a.x) (hay : 0 < a.y)
  proof: by
  rcases n with ((_ | n) | n)
  · rfl
  · rw [Int.ofNat_eq_natCast, zpow_natCast]
    exact Int.sign_eq_one_of_pos (y_pow_succ_pos hax hay n)
  · rw [zpow_negSucc]
    exact Int.sign_eq_neg_one_of_neg (neg_neg_of_pos (y_pow_succ_pos hax hay n))

中文:
定理 sign_y_zpow_eq_sign_of_x_pos_of_y_pos
  结论: {a : Solution₁ d} (hax : 0 < a.x) (hay : 0 < a.y)
  证明: by
  rcases n with ((_ | n) | n)
  · rfl
  · rw [Int.ofNat_eq_natCast, zpow_natCast]
    exact Int.sign_eq_one_of_pos (y_pow_succ_pos hax hay n)
  · rw [zpow_negSucc]
    exact Int.sign_eq_neg_one_of_neg (neg_neg_of_pos (y_pow_succ_pos hax hay n))

Depends on / 依赖: Int.ofNat_eq_natCast, Int.sign_eq_neg_one_of_neg, Int.sign_eq_one_of_pos, neg_neg_of_pos, ofNat_eq_natCast, sign_eq_neg_one_of_neg, sign_eq_one_of_pos, y_pow_succ_pos, zpow_natCast, zpow_negSucc
-/
theorem sign_y_zpow_eq_sign_of_x_pos_of_y_pos {a : Solution₁ d} (hax : 0 < a.x) (hay : 0 < a.y)
    (n : Int) : (a ^ n).y.sign = n.sign := by
  rcases n with ((_ | n) | n)
  · rfl
  · rw [Int.ofNat_eq_natCast, zpow_natCast]
    exact Int.sign_eq_one_of_pos (y_pow_succ_pos hax hay n)
  · rw [zpow_negSucc]
    exact Int.sign_eq_neg_one_of_neg (neg_neg_of_pos (y_pow_succ_pos hax hay n))

/--
theorem `exists_pos_variant` / 定理 `exists_pos_variant`

English:
theorem exists_pos_variant
  given: (h₀ : 0 < d) (a : Solution₁ d)
  proof: by
  refine
        (lt_or_gt_of_ne (a.x_ne_zero h₀.le)).elim
          ((le_total 0 a.y).elim (fun hy hx => ⟨-a⁻¹, ?_, ?_, ?_⟩) fun hy hx => ⟨-a, ?_, ?_, ?_⟩)
          ((le_total 0 a.y).elim (fun hy hx => ⟨a, hx, hy, ?_⟩) fun hy hx => ⟨a⁻¹, hx, ?_, ?_⟩) <;>
      simp only [neg_neg, inv_inv, neg_inv, Set.mem_insert_iff, Set.mem_singleton_iff, true_or,
        x_neg, x_inv, y_neg, y_inv, neg_pos, neg_nonneg, or_true] <;>
    assumption

中文:
定理 存在_pos_variant
  条件: (h₀ : 0 < d) (a : Solution₁ d)
  证明: by
  refine
        (lt_or_gt_of_ne (a.x_ne_zero h₀.le)).elim
          ((le_total 0 a.y).elim (fun hy hx => ⟨-a⁻¹, ?_, ?_, ?_⟩) fun hy hx => ⟨-a, ?_, ?_, ?_⟩)
          ((le_total 0 a.y).elim (fun hy hx => ⟨a, hx, hy, ?_⟩) fun hy hx => ⟨a⁻¹, hx, ?_, ?_⟩) <;>
      simp only [neg_neg, inv_inv, neg_inv, Set.mem_insert_iff, Set.mem_singleton_iff, true_or,
        x_neg, x_inv, y_neg, y_inv, neg_pos, neg_nonneg, or_true] <;>
    assumption

Depends on / 依赖: Set.mem_insert_iff, Set.mem_singleton_iff, a.x_ne_zero, inv_inv, le_total, lt_or_gt_of_ne, mem_insert_iff, mem_singleton_iff, neg_inv, neg_neg, neg_nonneg, neg_pos, or_true, true_or, x_inv, x_ne_zero, x_neg, y_inv, y_neg
-/
theorem exists_pos_variant (h₀ : 0 < d) (a : Solution₁ d) :
    exists b : Solution₁ d, 0 < b.x ∧ 0 <= b.y ∧ a in ({b, b⁻¹, -b, -b⁻¹} : Set (Solution₁ d)) := by
  refine
        (lt_or_gt_of_ne (a.x_ne_zero h₀.le)).elim
          ((le_total 0 a.y).elim (fun hy hx => ⟨-a⁻¹, ?_, ?_, ?_⟩) fun hy hx => ⟨-a, ?_, ?_, ?_⟩)
          ((le_total 0 a.y).elim (fun hy hx => ⟨a, hx, hy, ?_⟩) fun hy hx => ⟨a⁻¹, hx, ?_, ?_⟩) <;>
      simp only [neg_neg, inv_inv, neg_inv, Set.mem_insert_iff, Set.mem_singleton_iff, true_or,
        x_neg, x_inv, y_neg, y_inv, neg_pos, neg_nonneg, or_true] <;>
    assumption

end Solution₁

section Existence

/-!
### Existence of nontrivial solutions
-/


variable {d : Int}

open Set Real

/--
theorem `exists_of_not_isSquare` / 定理 `exists_of_not_isSquare`

English:
theorem exists_of_not_isSquare
  given: (h₀ : 0 < d) (hd : ¬IsSquare d)
  proof: by
  let ξ : Real := √d
  have hξ : Irrational ξ := by
    refine irrational_nrt_of_notint_nrt 2 d (sq_sqrt <| Int.cast_nonneg h₀.le) ?_ two_pos
    rintro ⟨x, hx⟩
    refine hd ⟨x, @Int.cast_injective Real _ _ d (x * x) ?_⟩
    rw [← sq_sqrt <| Int.cast_nonneg h₀.le]; rw [Int.cast_mul]; rw [← hx]; rw [sq]
  obtain ⟨M, hM₁⟩ := exists_int_gt (2 * |ξ| + 1)
  have hM : {q : Rat | |q.1 ^ 2 - d * (q.2 : Int) ^ 2| < M}.Infinite := by
    refine Infinite.mono (fun q h => ?_) (infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational hξ)
    have h0 : 0 < (q.2 : Real) ^ 2 := pow_pos (Nat.cast_pos.mpr q.pos) 2
    have h1 : (q.num : Real) / (q.den : Real) = q := mod_cast q.num_div_den
    rw [mem_ofPred]; rw [abs_sub_comm]; rw [← @Int.cast_lt Real]; rw [← div_lt_div_iff_of_pos_right (abs_pos_of_pos h0)]
    push_cast
    rw [← abs_div]; rw [abs_sq]; rw [sub_div]; rw [mul_div_cancel_right₀ _ h0.ne']; rw [← div_pow]; rw [h1]; rw [←
      sq_sqrt (Int.cast_pos.mpr h₀).le]; rw [sq_sub_sq]; rw [abs_mul]; rw [← mul_one_div]
    refine mul_lt_mul'' (((abs_add_le ξ q).trans ?_).trans_lt hM₁) h (abs_nonneg _) (abs_nonneg _)
    rw [two_mul]; rw [add_assoc]; rw [add_le_add_iff_left]; rw [← sub_le_iff_le_add']
    rw [mem_ofPred]; rw [abs_sub_comm] at h
    refine (abs_sub_abs_le_abs_sub (q : Real) ξ).trans (h.le.trans ?_)
    rw [div_le_one h0]; rw [one_le_sq_iff_one_le_abs]; rw [Nat.abs_cast]; rw [Nat.one_le_cast]
    exact q.pos
  obtain ⟨m, hm⟩ : exists m : Int, {q : Rat | q.1 ^ 2 - d * (q.den : Int) ^ 2 = m}.Infinite := by
    contrapose! hM
    refine (congr_arg _ (ext fun x => ?_)).mp (Finite.biUnion (finite_Ioo (-M) M) fun m _ => hM m)
    simp only [abs_lt, mem_ofPred, mem_Ioo, mem_iUnion, exists_prop, exists_eq_right']
  have hm₀ : m != 0 := by
    rintro rfl
    obtain ⟨q, hq⟩ := hm.nonempty
    rw [mem_ofPred]; rw [sub_eq_zero]; rw [mul_comm] at hq
    obtain ⟨a, ha⟩ := (Int.pow_dvd_pow_iff two_ne_zero).mp ⟨d, hq⟩
    rw [ha]; rw [mul_pow]; rw [mul_right_inj' (pow_pos (Int.natCast_pos.mpr q.pos) 2).ne'] at hq
    exact hd ⟨a, sq a ▸ hq.symm⟩
  have := neZero_iff.mpr (Int.natAbs_ne_zero.mpr hm₀)
  let f : Rat -> ZMod m.natAbs × ZMod m.natAbs := fun q => (q.num, q.den)
  obtain ⟨q₁, h₁ : q₁.num ^ 2 - d * (q₁.den : Int) ^ 2 = m,
      q₂, h₂ : q₂.num ^ 2 - d * (q₂.den : Int) ^ 2 = m, hne, hqf⟩ :=
    hm.exists_ne_map_eq_of_mapsTo (mapsTo_univ f _) finite_univ
  obtain ⟨hq1 : (q₁.num : ZMod m.natAbs) = q₂.num, hq2 : (q₁.den : ZMod m.natAbs) = q₂.den⟩ :=
    Prod.ext_iff.mp hqf
  have hd₁ : m ∣ q₁.num * q₂.num - d * (q₁.den * q₂.den) := by
    rw [← Int.natAbs_dvd]; rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hq1]; rw [hq2]; rw [← sq]; rw [← sq]
    norm_cast
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; rw [Int.natAbs_dvd]; rw [Nat.cast_pow]; rw [← h₂]
  have hd₂ : m ∣ q₁.num * q₂.den - q₂.num * q₁.den := by
    rw [← Int.natAbs_dvd]; rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
    push_cast
    rw [hq1]; rw [hq2]
  replace hm₀ : (m : Rat) != 0 := Int.cast_ne_zero.mpr hm₀
  refine ⟨(q₁.num * q₂.num - d * (q₁.den * q₂.den)) / m, (q₁.num * q₂.den - q₂.num * q₁.den) / m,
      ?_, ?_⟩
  · qify [hd₁, hd₂]
    field_simp
    norm_cast
    grind
  · qify [hd₂]
    refine div_ne_zero_iff.mpr ⟨?_, hm₀⟩
    exact mod_cast mt sub_eq_zero.mp (mt Rat.eq_iff_mul_eq_mul.mpr hne)

中文:
定理 存在_of_not_isSquare
  条件: (h₀ : 0 < d) (hd : ¬IsSquare d)
  证明: by
  let ξ : Real := √d
  have hξ : Irrational ξ := by
    refine irrational_nrt_of_notint_nrt 2 d (sq_sqrt <| Int.cast_nonneg h₀.le) ?_ two_pos
    rintro ⟨x, hx⟩
    refine hd ⟨x, @Int.cast_injective Real _ _ d (x * x) ?_⟩
    rw [← sq_sqrt <| Int.cast_nonneg h₀.le]; rw [Int.cast_mul]; rw [← hx]; rw [sq]
  obtain ⟨M, hM₁⟩ := exists_int_gt (2 * |ξ| + 1)
  have hM : {q : Rat | |q.1 ^ 2 - d * (q.2 : Int) ^ 2| < M}.Infinite := by
    refine Infinite.mono (fun q h => ?_) (infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational hξ)
    have h0 : 0 < (q.2 : Real) ^ 2 := pow_pos (Nat.cast_pos.mpr q.pos) 2
    have h1 : (q.num : Real) / (q.den : Real) = q := mod_cast q.num_div_den
    rw [mem_ofPred]; rw [abs_sub_comm]; rw [← @Int.cast_lt Real]; rw [← div_lt_div_iff_of_pos_right (abs_pos_of_pos h0)]
    push_cast
    rw [← abs_div]; rw [abs_sq]; rw [sub_div]; rw [mul_div_cancel_right₀ _ h0.ne']; rw [← div_pow]; rw [h1]; rw [←
      sq_sqrt (Int.cast_pos.mpr h₀).le]; rw [sq_sub_sq]; rw [abs_mul]; rw [← mul_one_div]
    refine mul_lt_mul'' (((abs_add_le ξ q).trans ?_).trans_lt hM₁) h (abs_nonneg _) (abs_nonneg _)
    rw [two_mul]; rw [add_assoc]; rw [add_le_add_iff_left]; rw [← sub_le_iff_le_add']
    rw [mem_ofPred]; rw [abs_sub_comm] at h
    refine (abs_sub_abs_le_abs_sub (q : Real) ξ).trans (h.le.trans ?_)
    rw [div_le_one h0]; rw [one_le_sq_iff_one_le_abs]; rw [Nat.abs_cast]; rw [Nat.one_le_cast]
    exact q.pos
  obtain ⟨m, hm⟩ : exists m : Int, {q : Rat | q.1 ^ 2 - d * (q.den : Int) ^ 2 = m}.Infinite := by
    contrapose! hM
    refine (congr_arg _ (ext fun x => ?_)).mp (Finite.biUnion (finite_Ioo (-M) M) fun m _ => hM m)
    simp only [abs_lt, mem_ofPred, mem_Ioo, mem_iUnion, exists_prop, exists_eq_right']
  have hm₀ : m != 0 := by
    rintro rfl
    obtain ⟨q, hq⟩ := hm.nonempty
    rw [mem_ofPred]; rw [sub_eq_zero]; rw [mul_comm] at hq
    obtain ⟨a, ha⟩ := (Int.pow_dvd_pow_iff two_ne_zero).mp ⟨d, hq⟩
    rw [ha]; rw [mul_pow]; rw [mul_right_inj' (pow_pos (Int.natCast_pos.mpr q.pos) 2).ne'] at hq
    exact hd ⟨a, sq a ▸ hq.symm⟩
  have := neZero_iff.mpr (Int.natAbs_ne_zero.mpr hm₀)
  let f : Rat -> ZMod m.natAbs × ZMod m.natAbs := fun q => (q.num, q.den)
  obtain ⟨q₁, h₁ : q₁.num ^ 2 - d * (q₁.den : Int) ^ 2 = m,
      q₂, h₂ : q₂.num ^ 2 - d * (q₂.den : Int) ^ 2 = m, hne, hqf⟩ :=
    hm.exists_ne_map_eq_of_mapsTo (mapsTo_univ f _) finite_univ
  obtain ⟨hq1 : (q₁.num : ZMod m.natAbs) = q₂.num, hq2 : (q₁.den : ZMod m.natAbs) = q₂.den⟩ :=
    Prod.ext_iff.mp hqf
  have hd₁ : m ∣ q₁.num * q₂.num - d * (q₁.den * q₂.den) := by
    rw [← Int.natAbs_dvd]; rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hq1]; rw [hq2]; rw [← sq]; rw [← sq]
    norm_cast
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; rw [Int.natAbs_dvd]; rw [Nat.cast_pow]; rw [← h₂]
  have hd₂ : m ∣ q₁.num * q₂.den - q₂.num * q₁.den := by
    rw [← Int.natAbs_dvd]; rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
    push_cast
    rw [hq1]; rw [hq2]
  replace hm₀ : (m : Rat) != 0 := Int.cast_ne_zero.mpr hm₀
  refine ⟨(q₁.num * q₂.num - d * (q₁.den * q₂.den)) / m, (q₁.num * q₂.den - q₂.num * q₁.den) / m,
      ?_, ?_⟩
  · qify [hd₁, hd₂]
    field_simp
    norm_cast
    grind
  · qify [hd₂]
    refine div_ne_zero_iff.mpr ⟨?_, hm₀⟩
    exact mod_cast mt sub_eq_zero.mp (mt Rat.eq_iff_mul_eq_mul.mpr hne)

Depends on / 依赖: Infinite, Infinite.mono, Int.cast_injective, Int.cast_mul, Int.cast_nonneg, Irrational, cast_injective, cast_mul, cast_nonneg, exists_int_gt, infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational, irrational_nrt_of_notint_nrt, sq_sqrt, two_pos
-/
theorem exists_of_not_isSquare (h₀ : 0 < d) (hd : ¬IsSquare d) :
    exists x y : Int, x ^ 2 - d * y ^ 2 = 1 ∧ y != 0 := by
  let ξ : Real := √d
  have hξ : Irrational ξ := by
    refine irrational_nrt_of_notint_nrt 2 d (sq_sqrt <| Int.cast_nonneg h₀.le) ?_ two_pos
    rintro ⟨x, hx⟩
    refine hd ⟨x, @Int.cast_injective Real _ _ d (x * x) ?_⟩
    rw [← sq_sqrt <| Int.cast_nonneg h₀.le]; rw [Int.cast_mul]; rw [← hx]; rw [sq]
  obtain ⟨M, hM₁⟩ := exists_int_gt (2 * |ξ| + 1)
  have hM : {q : Rat | |q.1 ^ 2 - d * (q.2 : Int) ^ 2| < M}.Infinite := by
    refine Infinite.mono (fun q h => ?_) (infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational hξ)
    have h0 : 0 < (q.2 : Real) ^ 2 := pow_pos (Nat.cast_pos.mpr q.pos) 2
    have h1 : (q.num : Real) / (q.den : Real) = q := mod_cast q.num_div_den
    rw [mem_ofPred]; rw [abs_sub_comm]; rw [← @Int.cast_lt Real]; rw [← div_lt_div_iff_of_pos_right (abs_pos_of_pos h0)]
    push_cast
    rw [← abs_div]; rw [abs_sq]; rw [sub_div]; rw [mul_div_cancel_right₀ _ h0.ne']; rw [← div_pow]; rw [h1]; rw [←
      sq_sqrt (Int.cast_pos.mpr h₀).le]; rw [sq_sub_sq]; rw [abs_mul]; rw [← mul_one_div]
    refine mul_lt_mul'' (((abs_add_le ξ q).trans ?_).trans_lt hM₁) h (abs_nonneg _) (abs_nonneg _)
    rw [two_mul]; rw [add_assoc]; rw [add_le_add_iff_left]; rw [← sub_le_iff_le_add']
    rw [mem_ofPred]; rw [abs_sub_comm] at h
    refine (abs_sub_abs_le_abs_sub (q : Real) ξ).trans (h.le.trans ?_)
    rw [div_le_one h0]; rw [one_le_sq_iff_one_le_abs]; rw [Nat.abs_cast]; rw [Nat.one_le_cast]
    exact q.pos
  obtain ⟨m, hm⟩ : exists m : Int, {q : Rat | q.1 ^ 2 - d * (q.den : Int) ^ 2 = m}.Infinite := by
    contrapose! hM
    refine (congr_arg _ (ext fun x => ?_)).mp (Finite.biUnion (finite_Ioo (-M) M) fun m _ => hM m)
    simp only [abs_lt, mem_ofPred, mem_Ioo, mem_iUnion, exists_prop, exists_eq_right']
  have hm₀ : m != 0 := by
    rintro rfl
    obtain ⟨q, hq⟩ := hm.nonempty
    rw [mem_ofPred]; rw [sub_eq_zero]; rw [mul_comm] at hq
    obtain ⟨a, ha⟩ := (Int.pow_dvd_pow_iff two_ne_zero).mp ⟨d, hq⟩
    rw [ha]; rw [mul_pow]; rw [mul_right_inj' (pow_pos (Int.natCast_pos.mpr q.pos) 2).ne'] at hq
    exact hd ⟨a, sq a ▸ hq.symm⟩
  have := neZero_iff.mpr (Int.natAbs_ne_zero.mpr hm₀)
  let f : Rat -> ZMod m.natAbs × ZMod m.natAbs := fun q => (q.num, q.den)
  obtain ⟨q₁, h₁ : q₁.num ^ 2 - d * (q₁.den : Int) ^ 2 = m,
      q₂, h₂ : q₂.num ^ 2 - d * (q₂.den : Int) ^ 2 = m, hne, hqf⟩ :=
    hm.exists_ne_map_eq_of_mapsTo (mapsTo_univ f _) finite_univ
  obtain ⟨hq1 : (q₁.num : ZMod m.natAbs) = q₂.num, hq2 : (q₁.den : ZMod m.natAbs) = q₂.den⟩ :=
    Prod.ext_iff.mp hqf
  have hd₁ : m ∣ q₁.num * q₂.num - d * (q₁.den * q₂.den) := by
    rw [← Int.natAbs_dvd]; rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hq1]; rw [hq2]; rw [← sq]; rw [← sq]
    norm_cast
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; rw [Int.natAbs_dvd]; rw [Nat.cast_pow]; rw [← h₂]
  have hd₂ : m ∣ q₁.num * q₂.den - q₂.num * q₁.den := by
    rw [← Int.natAbs_dvd]; rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
    push_cast
    rw [hq1]; rw [hq2]
  replace hm₀ : (m : Rat) != 0 := Int.cast_ne_zero.mpr hm₀
  refine ⟨(q₁.num * q₂.num - d * (q₁.den * q₂.den)) / m, (q₁.num * q₂.den - q₂.num * q₁.den) / m,
      ?_, ?_⟩
  · qify [hd₁, hd₂]
    field_simp
    norm_cast
    grind
  · qify [hd₂]
    refine div_ne_zero_iff.mpr ⟨?_, hm₀⟩
    exact mod_cast mt sub_eq_zero.mp (mt Rat.eq_iff_mul_eq_mul.mpr hne)

/--
theorem `exists_iff_not_isSquare` / 定理 `exists_iff_not_isSquare`

English:
theorem exists_iff_not_isSquare
  given: (h₀ : 0 < d)
  proof: by
  refine ⟨?_, exists_of_not_isSquare h₀⟩
  rintro ⟨x, y, hxy, hy⟩ ⟨a, rfl⟩
  rw [← sq]; rw [← mul_pow]; rw [sq_sub_sq] at hxy
  simpa [hy, mul_self_pos.mp h₀, sub_eq_add_neg, eq_neg_self_iff] using Int.eq_of_mul_eq_one hxy

中文:
定理 存在_iff_not_isSquare
  条件: (h₀ : 0 < d)
  证明: by
  refine ⟨?_, exists_of_not_isSquare h₀⟩
  rintro ⟨x, y, hxy, hy⟩ ⟨a, rfl⟩
  rw [← sq]; rw [← mul_pow]; rw [sq_sub_sq] at hxy
  simpa [hy, mul_self_pos.mp h₀, sub_eq_add_neg, eq_neg_self_iff] using Int.eq_of_mul_eq_one hxy

Depends on / 依赖: Int.eq_of_mul_eq_one, eq_neg_self_iff, eq_of_mul_eq_one, exists_of_not_isSquare, mul_pow, mul_self_pos, mul_self_pos.mp, sq_sub_sq, sub_eq_add_neg
-/
theorem exists_iff_not_isSquare (h₀ : 0 < d) :
    (exists x y : Int, x ^ 2 - d * y ^ 2 = 1 ∧ y != 0) ↔ ¬IsSquare d := by
  refine ⟨?_, exists_of_not_isSquare h₀⟩
  rintro ⟨x, y, hxy, hy⟩ ⟨a, rfl⟩
  rw [← sq]; rw [← mul_pow]; rw [sq_sub_sq] at hxy
  simpa [hy, mul_self_pos.mp h₀, sub_eq_add_neg, eq_neg_self_iff] using Int.eq_of_mul_eq_one hxy

namespace Solution₁

/--
theorem `exists_nontrivial_of_not_isSquare` / 定理 `exists_nontrivial_of_not_isSquare`

English:
theorem exists_nontrivial_of_not_isSquare
  given: (h₀ : 0 < d) (hd : ¬IsSquare d)
  proof: by
  obtain ⟨x, y, prop, hy⟩ := exists_of_not_isSquare h₀ hd
  refine ⟨mk x y prop, fun H => ?_, fun H => ?_⟩ <;> apply_fun Solution₁.y at H <;>
    simp [hy] at H

中文:
定理 存在_nontrivial_of_not_isSquare
  条件: (h₀ : 0 < d) (hd : ¬IsSquare d)
  证明: by
  obtain ⟨x, y, prop, hy⟩ := exists_of_not_isSquare h₀ hd
  refine ⟨mk x y prop, fun H => ?_, fun H => ?_⟩ <;> apply_fun Solution₁.y at H <;>
    simp [hy] at H

Depends on / 依赖: apply_fun, exists_of_not_isSquare
-/
theorem exists_nontrivial_of_not_isSquare (h₀ : 0 < d) (hd : ¬IsSquare d) :
    exists a : Solution₁ d, a != 1 ∧ a != -1 := by
  obtain ⟨x, y, prop, hy⟩ := exists_of_not_isSquare h₀ hd
  refine ⟨mk x y prop, fun H => ?_, fun H => ?_⟩ <;> apply_fun Solution₁.y at H <;>
    simp [hy] at H

/--
theorem `exists_pos_of_not_isSquare` / 定理 `exists_pos_of_not_isSquare`

English:
theorem exists_pos_of_not_isSquare
  given: (h₀ : 0 < d) (hd : ¬IsSquare d)
  proof: by
  obtain ⟨x, y, h, hy⟩ := exists_of_not_isSquare h₀ hd
  refine ⟨mk |x| |y| (by rwa [sq_abs, sq_abs]), ?_, abs_pos.mpr hy⟩
  rw [x_mk]; rw [← one_lt_sq_iff_one_lt_abs]; rw [eq_add_of_sub_eq h]; rw [lt_add_iff_pos_right]
  exact mul_pos h₀ (sq_pos_of_ne_zero hy)

中文:
定理 存在_pos_of_not_isSquare
  条件: (h₀ : 0 < d) (hd : ¬IsSquare d)
  证明: by
  obtain ⟨x, y, h, hy⟩ := exists_of_not_isSquare h₀ hd
  refine ⟨mk |x| |y| (by rwa [sq_abs, sq_abs]), ?_, abs_pos.mpr hy⟩
  rw [x_mk]; rw [← one_lt_sq_iff_one_lt_abs]; rw [eq_add_of_sub_eq h]; rw [lt_add_iff_pos_right]
  exact mul_pos h₀ (sq_pos_of_ne_zero hy)

Depends on / 依赖: abs_pos, abs_pos.mpr, eq_add_of_sub_eq, exists_of_not_isSquare, lt_add_iff_pos_right, mul_pos, one_lt_sq_iff_one_lt_abs, sq_abs, sq_pos_of_ne_zero, x_mk
-/
theorem exists_pos_of_not_isSquare (h₀ : 0 < d) (hd : ¬IsSquare d) :
    exists a : Solution₁ d, 1 < a.x ∧ 0 < a.y := by
  obtain ⟨x, y, h, hy⟩ := exists_of_not_isSquare h₀ hd
  refine ⟨mk |x| |y| (by rwa [sq_abs, sq_abs]), ?_, abs_pos.mpr hy⟩
  rw [x_mk]; rw [← one_lt_sq_iff_one_lt_abs]; rw [eq_add_of_sub_eq h]; rw [lt_add_iff_pos_right]
  exact mul_pos h₀ (sq_pos_of_ne_zero hy)

end Solution₁

end Existence

/-! ### Fundamental solutions

We define the notion of a *fundamental solution* of Pell's equation and
show that it exists and is unique (when `d` is positive and non-square)
and generates the group of solutions up to sign.
-/


variable {d : Int}

/--
Definition of `IsFundamental` / `IsFundamental` 的定义

English:
definition IsFundamental
  signature: (a : Solution₁ d)
  body: 1 < a.x ∧ 0 < a.y ∧ forall {b : Solution₁ d}, 1 < b.x -> a.x <= b.x

中文:
定义 IsFundamental
  签名: (a : Solution₁ d)
  定义体: 1 < a.x ∧ 0 < a.y ∧ forall {b : Solution₁ d}, 1 < b.x -> a.x <= b.x
-/
def IsFundamental (a : Solution₁ d) : Prop :=
  1 < a.x ∧ 0 < a.y ∧ forall {b : Solution₁ d}, 1 < b.x -> a.x <= b.x

namespace IsFundamental

open Solution₁

/--
theorem `x_pos` / 定理 `x_pos`

English:
theorem x_pos
  given: {a : Solution₁ d} (h : IsFundamental a)
  statement: 0 < a.x
  proof: zero_lt_one.trans h.1

中文:
定理 x_pos
  条件: {a : Solution₁ d} (h : IsFundamental a)
  结论: 0 < a.x
  证明: zero_lt_one.trans h.1

Depends on / 依赖: zero_lt_one, zero_lt_one.trans
-/
theorem x_pos {a : Solution₁ d} (h : IsFundamental a) : 0 < a.x :=
  zero_lt_one.trans h.1

/--
theorem `d_pos` / 定理 `d_pos`

English:
theorem d_pos
  given: {a : Solution₁ d} (h : IsFundamental a)
  statement: 0 < d
  proof: d_pos_of_one_lt_x h.1

中文:
定理 d_pos
  条件: {a : Solution₁ d} (h : IsFundamental a)
  结论: 0 < d
  证明: d_pos_of_one_lt_x h.1

Depends on / 依赖: d_pos_of_one_lt_x
-/
theorem d_pos {a : Solution₁ d} (h : IsFundamental a) : 0 < d :=
  d_pos_of_one_lt_x h.1

/--
theorem `d_nonsquare` / 定理 `d_nonsquare`

English:
theorem d_nonsquare
  given: {a : Solution₁ d} (h : IsFundamental a)
  statement: ¬IsSquare d
  proof: d_nonsquare_of_one_lt_x h.1

中文:
定理 d_nonsquare
  条件: {a : Solution₁ d} (h : IsFundamental a)
  结论: ¬IsSquare d
  证明: d_nonsquare_of_one_lt_x h.1

Depends on / 依赖: d_nonsquare_of_one_lt_x
-/
theorem d_nonsquare {a : Solution₁ d} (h : IsFundamental a) : ¬IsSquare d :=
  d_nonsquare_of_one_lt_x h.1

/--
theorem `subsingleton` / 定理 `subsingleton`

English:
theorem subsingleton
  given: {a b : Solution₁ d} (ha : IsFundamental a) (hb : IsFundamental b)
  statement: a = b
  proof: by
  have hx := le_antisymm (ha.2.2 hb.1) (hb.2.2 ha.1)
  refine Solution₁.ext hx ?_
  have : d * a.y ^ 2 = d * b.y ^ 2 := by rw [a.prop_y, b.prop_y, hx]
  exact (sq_eq_sq₀ ha.2.1.le hb.2.1.le).mp (Int.eq_of_mul_eq_mul_left ha.d_pos.ne' this)

中文:
定理 subsingleton
  条件: {a b : Solution₁ d} (ha : IsFundamental a) (hb : IsFundamental b)
  结论: a = b
  证明: by
  have hx := le_antisymm (ha.2.2 hb.1) (hb.2.2 ha.1)
  refine Solution₁.ext hx ?_
  have : d * a.y ^ 2 = d * b.y ^ 2 := by rw [a.prop_y, b.prop_y, hx]
  exact (sq_eq_sq₀ ha.2.1.le hb.2.1.le).mp (Int.eq_of_mul_eq_mul_left ha.d_pos.ne' this)

Depends on / 依赖: Int.eq_of_mul_eq_mul_left, a.prop_y, b.prop_y, d_pos, eq_of_mul_eq_mul_left, ha.d_pos.ne, le_antisymm, prop_y
-/
theorem subsingleton {a b : Solution₁ d} (ha : IsFundamental a) (hb : IsFundamental b) : a = b := by
  have hx := le_antisymm (ha.2.2 hb.1) (hb.2.2 ha.1)
  refine Solution₁.ext hx ?_
  have : d * a.y ^ 2 = d * b.y ^ 2 := by rw [a.prop_y, b.prop_y, hx]
  exact (sq_eq_sq₀ ha.2.1.le hb.2.1.le).mp (Int.eq_of_mul_eq_mul_left ha.d_pos.ne' this)

/--
theorem `exists_of_not_isSquare` / 定理 `exists_of_not_isSquare`

English:
theorem exists_of_not_isSquare
  given: (h₀ : 0 < d) (hd : ¬IsSquare d)
  proof: by
  obtain ⟨a, ha₁, ha₂⟩ := exists_pos_of_not_isSquare h₀ hd
  -- convert to `x : ℕ` to be able to use `Nat.find`
  have P : exists x' : Nat, 1 < x' ∧ exists y' : Int, 0 < y' ∧ (x' : Int) ^ 2 - d * y' ^ 2 = 1 := by
    have hax := a.prop
    lift a.x to Nat using by positivity with ax
    norm_cast at ha₁
    exact ⟨ax, ha₁, a.y, ha₂, hax⟩
  classical
  -- to avoid having to show that the predicate is decidable
  let x₁ := Nat.find P
  obtain ⟨hx, y₁, hy₀, hy₁⟩ := Nat.find_spec P
  refine ⟨mk x₁ y₁ hy₁, by rw [x_mk]; exact mod_cast hx, hy₀, fun {b} hb => ?_⟩
  rw [x_mk]
  have hb' := (Int.toNat_of_nonneg <| zero_le_one.trans hb.le).symm
  have hb'' := hb
  rw [hb'] at hb ⊢
  norm_cast at hb ⊢
refine Nat.find_min' P ⟨hb, |b.y|, abs_pos.mpr y_ne_zero_of_one_lt_x hb'', ?_⟩
  rw [← hb']; rw [sq_abs]
  exact b.prop

中文:
定理 存在_of_not_isSquare
  条件: (h₀ : 0 < d) (hd : ¬IsSquare d)
  证明: by
  obtain ⟨a, ha₁, ha₂⟩ := exists_pos_of_not_isSquare h₀ hd
  -- convert to `x : ℕ` to be able to use `Nat.find`
  have P : exists x' : Nat, 1 < x' ∧ exists y' : Int, 0 < y' ∧ (x' : Int) ^ 2 - d * y' ^ 2 = 1 := by
    have hax := a.prop
    lift a.x to Nat using by positivity with ax
    norm_cast at ha₁
    exact ⟨ax, ha₁, a.y, ha₂, hax⟩
  classical
  -- to avoid having to show that the predicate is decidable
  let x₁ := Nat.find P
  obtain ⟨hx, y₁, hy₀, hy₁⟩ := Nat.find_spec P
  refine ⟨mk x₁ y₁ hy₁, by rw [x_mk]; exact mod_cast hx, hy₀, fun {b} hb => ?_⟩
  rw [x_mk]
  have hb' := (Int.toNat_of_nonneg <| zero_le_one.trans hb.le).symm
  have hb'' := hb
  rw [hb'] at hb ⊢
  norm_cast at hb ⊢
refine Nat.find_min' P ⟨hb, |b.y|, abs_pos.mpr y_ne_zero_of_one_lt_x hb'', ?_⟩
  rw [← hb']; rw [sq_abs]
  exact b.prop

Depends on / 依赖: exists_pos_of_not_isSquare
-/
theorem exists_of_not_isSquare (h₀ : 0 < d) (hd : ¬IsSquare d) :
    exists a : Solution₁ d, IsFundamental a := by
  obtain ⟨a, ha₁, ha₂⟩ := exists_pos_of_not_isSquare h₀ hd
  -- convert to `x : ℕ` to be able to use `Nat.find`
  have P : exists x' : Nat, 1 < x' ∧ exists y' : Int, 0 < y' ∧ (x' : Int) ^ 2 - d * y' ^ 2 = 1 := by
    have hax := a.prop
    lift a.x to Nat using by positivity with ax
    norm_cast at ha₁
    exact ⟨ax, ha₁, a.y, ha₂, hax⟩
  classical
  -- to avoid having to show that the predicate is decidable
  let x₁ := Nat.find P
  obtain ⟨hx, y₁, hy₀, hy₁⟩ := Nat.find_spec P
  refine ⟨mk x₁ y₁ hy₁, by rw [x_mk]; exact mod_cast hx, hy₀, fun {b} hb => ?_⟩
  rw [x_mk]
  have hb' := (Int.toNat_of_nonneg <| zero_le_one.trans hb.le).symm
  have hb'' := hb
  rw [hb'] at hb ⊢
  norm_cast at hb ⊢
refine Nat.find_min' P ⟨hb, |b.y|, abs_pos.mpr y_ne_zero_of_one_lt_x hb'', ?_⟩
  rw [← hb']; rw [sq_abs]
  exact b.prop

/--
theorem `y_strictMono` / 定理 `y_strictMono`

English:
theorem y_strictMono
  given: {a : Solution₁ d} (h : IsFundamental a)
  proof: by
  have H : forall n : Int, 0 <= n -> (a ^ n).y < (a ^ (n + 1)).y := by
    intro n hn
    rw [← sub_pos]; rw [zpow_add]; rw [zpow_one]; rw [y_mul]; rw [add_sub_assoc]
    rw [show (a ^ n).y * a.x - (a ^ n).y = (a ^ n).y * (a.x - 1) by ring]
    refine
      add_pos_of_pos_of_nonneg (mul_pos (x_zpow_pos h.x_pos _) h.2.1)
        (mul_nonneg ?_ (by rw [sub_nonneg]; exact h.1.le))
    rcases hn.eq_or_lt with (rfl | hn)
    · simp only [zpow_zero, y_one, le_refl]
    · exact (y_zpow_pos h.x_pos h.2.1 hn).le
  refine strictMono_int_of_lt_succ fun n => ?_
  rcases le_or_gt 0 n with hn | hn
  · exact H n hn
  · let m : Int := -n - 1
    have hm : n = -m - 1 := by simp only [m, neg_sub, sub_neg_eq_add, add_tsub_cancel_left]
    rw [hm]; rw [sub_add_cancel]; rw [← neg_add']; rw [zpow_neg]; rw [zpow_neg]; rw [y_inv]; rw [y_inv]; rw [neg_lt_neg_iff]
    exact H _ (by lia)

中文:
定理 y_strictMono
  条件: {a : Solution₁ d} (h : IsFundamental a)
  证明: by
  have H : forall n : Int, 0 <= n -> (a ^ n).y < (a ^ (n + 1)).y := by
    intro n hn
    rw [← sub_pos]; rw [zpow_add]; rw [zpow_one]; rw [y_mul]; rw [add_sub_assoc]
    rw [show (a ^ n).y * a.x - (a ^ n).y = (a ^ n).y * (a.x - 1) by ring]
    refine
      add_pos_of_pos_of_nonneg (mul_pos (x_zpow_pos h.x_pos _) h.2.1)
        (mul_nonneg ?_ (by rw [sub_nonneg]; exact h.1.le))
    rcases hn.eq_or_lt with (rfl | hn)
    · simp only [zpow_zero, y_one, le_refl]
    · exact (y_zpow_pos h.x_pos h.2.1 hn).le
  refine strictMono_int_of_lt_succ fun n => ?_
  rcases le_or_gt 0 n with hn | hn
  · exact H n hn
  · let m : Int := -n - 1
    have hm : n = -m - 1 := by simp only [m, neg_sub, sub_neg_eq_add, add_tsub_cancel_left]
    rw [hm]; rw [sub_add_cancel]; rw [← neg_add']; rw [zpow_neg]; rw [zpow_neg]; rw [y_inv]; rw [y_inv]; rw [neg_lt_neg_iff]
    exact H _ (by lia)

Depends on / 依赖: add_pos_of_pos_of_nonneg, add_sub_assoc, eq_or_lt, h.x_pos, hn.eq_or_lt, le_refl, mul_nonneg, mul_pos, strictMono_int_of_lt_succ, sub_nonneg, sub_pos, x_pos, x_zpow_pos, y_mul, y_one, y_zpow_pos, zpow_add, zpow_one, zpow_zero
-/
theorem y_strictMono {a : Solution₁ d} (h : IsFundamental a) :
    StrictMono fun n : Int => (a ^ n).y := by
  have H : forall n : Int, 0 <= n -> (a ^ n).y < (a ^ (n + 1)).y := by
    intro n hn
    rw [← sub_pos]; rw [zpow_add]; rw [zpow_one]; rw [y_mul]; rw [add_sub_assoc]
    rw [show (a ^ n).y * a.x - (a ^ n).y = (a ^ n).y * (a.x - 1) by ring]
    refine
      add_pos_of_pos_of_nonneg (mul_pos (x_zpow_pos h.x_pos _) h.2.1)
        (mul_nonneg ?_ (by rw [sub_nonneg]; exact h.1.le))
    rcases hn.eq_or_lt with (rfl | hn)
    · simp only [zpow_zero, y_one, le_refl]
    · exact (y_zpow_pos h.x_pos h.2.1 hn).le
  refine strictMono_int_of_lt_succ fun n => ?_
  rcases le_or_gt 0 n with hn | hn
  · exact H n hn
  · let m : Int := -n - 1
    have hm : n = -m - 1 := by simp only [m, neg_sub, sub_neg_eq_add, add_tsub_cancel_left]
    rw [hm]; rw [sub_add_cancel]; rw [← neg_add']; rw [zpow_neg]; rw [zpow_neg]; rw [y_inv]; rw [y_inv]; rw [neg_lt_neg_iff]
    exact H _ (by lia)

/--
theorem `zpow_y_lt_iff_lt` / 定理 `zpow_y_lt_iff_lt`

English:
theorem zpow_y_lt_iff_lt
  given: {a : Solution₁ d} (h : IsFundamental a) (m n : Int)
  proof: by
  refine ⟨fun H => ?_, fun H => h.y_strictMono H⟩
  contrapose! H
  exact h.y_strictMono.monotone H

中文:
定理 zpow_y_lt_iff_lt
  条件: {a : Solution₁ d} (h : IsFundamental a) (m n : 整数)
  证明: by
  refine ⟨fun H => ?_, fun H => h.y_strictMono H⟩
  contrapose! H
  exact h.y_strictMono.monotone H

Depends on / 依赖: contrapose, h.y_strictMono, h.y_strictMono.monotone, monotone, y_strictMono
-/
theorem zpow_y_lt_iff_lt {a : Solution₁ d} (h : IsFundamental a) (m n : Int) :
    (a ^ m).y < (a ^ n).y ↔ m < n := by
  refine ⟨fun H => ?_, fun H => h.y_strictMono H⟩
  contrapose! H
  exact h.y_strictMono.monotone H

/--
theorem `zpow_eq_one_iff` / 定理 `zpow_eq_one_iff`

English:
theorem zpow_eq_one_iff
  given: {a : Solution₁ d} (h : IsFundamental a) (n : Int)
  statement: a ^ n = 1 ↔ n = 0
  proof: by
  rw [← zpow_zero a]
  exact ⟨fun H => h.y_strictMono.injective (congr_arg Solution₁.y H), fun H => H ▸ rfl⟩

中文:
定理 zpow_eq_one_iff
  条件: {a : Solution₁ d} (h : IsFundamental a) (n : 整数)
  结论: a ^ n = 1 ↔ n = 0
  证明: by
  rw [← zpow_zero a]
  exact ⟨fun H => h.y_strictMono.injective (congr_arg Solution₁.y H), fun H => H ▸ rfl⟩

Depends on / 依赖: congr_arg, h.y_strictMono.injective, injective, y_strictMono, zpow_zero
-/
theorem zpow_eq_one_iff {a : Solution₁ d} (h : IsFundamental a) (n : Int) : a ^ n = 1 ↔ n = 0 := by
  rw [← zpow_zero a]
  exact ⟨fun H => h.y_strictMono.injective (congr_arg Solution₁.y H), fun H => H ▸ rfl⟩

/--
theorem `zpow_ne_neg_zpow` / 定理 `zpow_ne_neg_zpow`

English:
theorem zpow_ne_neg_zpow
  given: {a : Solution₁ d} (h : IsFundamental a) {n n' : Int}
  statement: a ^ n != -a ^ n'
  proof: by
  intro hf
  apply_fun Solution₁.x at hf
  have H := x_zpow_pos h.x_pos n
  rw [hf]; rw [x_neg]; rw [lt_neg]; rw [neg_zero] at H
  exact lt_irrefl _ ((x_zpow_pos h.x_pos n').trans H)

中文:
定理 zpow_ne_neg_zpow
  条件: {a : Solution₁ d} (h : IsFundamental a) {n n' : 整数}
  结论: a ^ n != -a ^ n'
  证明: by
  intro hf
  apply_fun Solution₁.x at hf
  have H := x_zpow_pos h.x_pos n
  rw [hf]; rw [x_neg]; rw [lt_neg]; rw [neg_zero] at H
  exact lt_irrefl _ ((x_zpow_pos h.x_pos n').trans H)

Depends on / 依赖: apply_fun, h.x_pos, lt_irrefl, lt_neg, neg_zero, x_neg, x_pos, x_zpow_pos
-/
theorem zpow_ne_neg_zpow {a : Solution₁ d} (h : IsFundamental a) {n n' : Int} : a ^ n != -a ^ n' := by
  intro hf
  apply_fun Solution₁.x at hf
  have H := x_zpow_pos h.x_pos n
  rw [hf]; rw [x_neg]; rw [lt_neg]; rw [neg_zero] at H
  exact lt_irrefl _ ((x_zpow_pos h.x_pos n').trans H)

/--
theorem `x_le_x` / 定理 `x_le_x`

English:
theorem x_le_x
  given: {a₁ : Solution₁ d} (h : IsFundamental a₁) {a : Solution₁ d} (hax : 1 < a.x)
  proof: h.2.2 hax

中文:
定理 x_le_x
  条件: {a₁ : Solution₁ d} (h : IsFundamental a₁) {a : Solution₁ d} (hax : 1 < a.x)
  证明: h.2.2 hax
-/
theorem x_le_x {a₁ : Solution₁ d} (h : IsFundamental a₁) {a : Solution₁ d} (hax : 1 < a.x) :
    a₁.x <= a.x :=
  h.2.2 hax

/--
theorem `y_le_y` / 定理 `y_le_y`

English:
theorem y_le_y
  statement: {a₁ : Solution₁ d} (h : IsFundamental a₁) {a : Solution₁ d} (hax : 1 < a.x)
  proof: by
  have H : d * (a₁.y ^ 2 - a.y ^ 2) = a₁.x ^ 2 - a.x ^ 2 := by rw [a.prop_x, a₁.prop_x]; ring
  rw [← abs_of_pos hay]; rw [← abs_of_pos h.2.1]; rw [← sq_le_sq]; rw [← mul_le_mul_iff_right₀ h.d_pos]; rw [← sub_nonpos]; rw [← mul_sub]; rw [H]; rw [sub_nonpos]; rw [sq_le_sq]; rw [abs_of_pos (zero_lt_one.trans h.1)]; rw [abs_of_pos (zero_lt_one.trans hax)]
  exact h.x_le_x hax

中文:
定理 y_le_y
  结论: {a₁ : Solution₁ d} (h : IsFundamental a₁) {a : Solution₁ d} (hax : 1 < a.x)
  证明: by
  have H : d * (a₁.y ^ 2 - a.y ^ 2) = a₁.x ^ 2 - a.x ^ 2 := by rw [a.prop_x, a₁.prop_x]; ring
  rw [← abs_of_pos hay]; rw [← abs_of_pos h.2.1]; rw [← sq_le_sq]; rw [← mul_le_mul_iff_right₀ h.d_pos]; rw [← sub_nonpos]; rw [← mul_sub]; rw [H]; rw [sub_nonpos]; rw [sq_le_sq]; rw [abs_of_pos (zero_lt_one.trans h.1)]; rw [abs_of_pos (zero_lt_one.trans hax)]
  exact h.x_le_x hax

Depends on / 依赖: a.prop_x, abs_of_pos, d_pos, h.d_pos, h.x_le_x, mul_sub, prop_x, sq_le_sq, sub_nonpos, x_le_x, zero_lt_one, zero_lt_one.trans
-/
theorem y_le_y {a₁ : Solution₁ d} (h : IsFundamental a₁) {a : Solution₁ d} (hax : 1 < a.x)
    (hay : 0 < a.y) : a₁.y <= a.y := by
  have H : d * (a₁.y ^ 2 - a.y ^ 2) = a₁.x ^ 2 - a.x ^ 2 := by rw [a.prop_x, a₁.prop_x]; ring
  rw [← abs_of_pos hay]; rw [← abs_of_pos h.2.1]; rw [← sq_le_sq]; rw [← mul_le_mul_iff_right₀ h.d_pos]; rw [← sub_nonpos]; rw [← mul_sub]; rw [H]; rw [sub_nonpos]; rw [sq_le_sq]; rw [abs_of_pos (zero_lt_one.trans h.1)]; rw [abs_of_pos (zero_lt_one.trans hax)]
  exact h.x_le_x hax

-- helper lemma for the next three results
/--
theorem `x_mul_y_le_y_mul_x` / 定理 `x_mul_y_le_y_mul_x`

English:
theorem x_mul_y_le_y_mul_x
  statement: {a₁ : Solution₁ d} (h : IsFundamental a₁) {a : Solution₁ d}
  proof: by
  rw [← abs_of_pos <| zero_lt_one.trans hax]; rw [← abs_of_pos hay]; rw [← abs_of_pos h.x_pos]; rw [←
    abs_of_pos h.2.1]; rw [← abs_mul]; rw [← abs_mul]; rw [← sq_le_sq]; rw [mul_pow]; rw [mul_pow]; rw [a.prop_x]; rw [a₁.prop_x]; rw [←
    sub_nonneg]
  ring_nf
  rw [sub_nonneg]; rw [sq_le_sq]; rw [abs_of_pos hay]; rw [abs_of_pos h.2.1]
  exact h.y_le_y hax hay

中文:
定理 x_mul_y_le_y_mul_x
  结论: {a₁ : Solution₁ d} (h : IsFundamental a₁) {a : Solution₁ d}
  证明: by
  rw [← abs_of_pos <| zero_lt_one.trans hax]; rw [← abs_of_pos hay]; rw [← abs_of_pos h.x_pos]; rw [←
    abs_of_pos h.2.1]; rw [← abs_mul]; rw [← abs_mul]; rw [← sq_le_sq]; rw [mul_pow]; rw [mul_pow]; rw [a.prop_x]; rw [a₁.prop_x]; rw [←
    sub_nonneg]
  ring_nf
  rw [sub_nonneg]; rw [sq_le_sq]; rw [abs_of_pos hay]; rw [abs_of_pos h.2.1]
  exact h.y_le_y hax hay

Depends on / 依赖: a.prop_x, abs_mul, abs_of_pos, h.x_pos, h.y_le_y, mul_pow, prop_x, ring_nf, sq_le_sq, sub_nonneg, x_pos, y_le_y, zero_lt_one, zero_lt_one.trans
-/
theorem x_mul_y_le_y_mul_x {a₁ : Solution₁ d} (h : IsFundamental a₁) {a : Solution₁ d}
    (hax : 1 < a.x) (hay : 0 < a.y) : a.x * a₁.y <= a.y * a₁.x := by
  rw [← abs_of_pos <| zero_lt_one.trans hax]; rw [← abs_of_pos hay]; rw [← abs_of_pos h.x_pos]; rw [←
    abs_of_pos h.2.1]; rw [← abs_mul]; rw [← abs_mul]; rw [← sq_le_sq]; rw [mul_pow]; rw [mul_pow]; rw [a.prop_x]; rw [a₁.prop_x]; rw [←
    sub_nonneg]
  ring_nf
  rw [sub_nonneg]; rw [sq_le_sq]; rw [abs_of_pos hay]; rw [abs_of_pos h.2.1]
  exact h.y_le_y hax hay

/--
theorem `mul_inv_y_nonneg` / 定理 `mul_inv_y_nonneg`

English:
theorem mul_inv_y_nonneg
  statement: {a₁ : Solution₁ d} (h : IsFundamental a₁) {a : Solution₁ d} (hax : 1 < a.x)
  proof: by
  simpa only [y_inv, mul_neg, y_mul, le_neg_add_iff_add_le, add_zero] using!
    h.x_mul_y_le_y_mul_x hax hay

中文:
定理 mul_inv_y_nonneg
  结论: {a₁ : Solution₁ d} (h : IsFundamental a₁) {a : Solution₁ d} (hax : 1 < a.x)
  证明: by
  simpa only [y_inv, mul_neg, y_mul, le_neg_add_iff_add_le, add_zero] using!
    h.x_mul_y_le_y_mul_x hax hay

Depends on / 依赖: add_zero, h.x_mul_y_le_y_mul_x, le_neg_add_iff_add_le, mul_neg, x_mul_y_le_y_mul_x, y_inv, y_mul
-/
theorem mul_inv_y_nonneg {a₁ : Solution₁ d} (h : IsFundamental a₁) {a : Solution₁ d} (hax : 1 < a.x)
    (hay : 0 < a.y) : 0 <= (a * a₁⁻¹).y := by
  simpa only [y_inv, mul_neg, y_mul, le_neg_add_iff_add_le, add_zero] using!
    h.x_mul_y_le_y_mul_x hax hay

/--
theorem `mul_inv_x_pos` / 定理 `mul_inv_x_pos`

English:
theorem mul_inv_x_pos
  statement: {a₁ : Solution₁ d} (h : IsFundamental a₁) {a : Solution₁ d} (hax : 1 < a.x)
  proof: by
  simp only [x_mul, x_inv, y_inv, mul_neg, lt_add_neg_iff_add_lt, zero_add]
refine lt_of_mul_lt_mul_left ?_ zero_le_one.trans hax.le
  calc a.x * (d * (a.y * a₁.y))
    _ = d * a.y * (a.x * a₁.y) := by ring
    _ <= d * a.y * (a.y * a₁.x) := by have := x_mul_y_le_y_mul_x h hax hay; have := h.d_pos; gcongr
    _ = (a.x ^ 2 - 1) * a₁.x := by rw [← a.prop_y]; ring
    _ < a.x * (a.x * a₁.x) := by linarith [h.1]

中文:
定理 mul_inv_x_pos
  结论: {a₁ : Solution₁ d} (h : IsFundamental a₁) {a : Solution₁ d} (hax : 1 < a.x)
  证明: by
  simp only [x_mul, x_inv, y_inv, mul_neg, lt_add_neg_iff_add_lt, zero_add]
refine lt_of_mul_lt_mul_left ?_ zero_le_one.trans hax.le
  calc a.x * (d * (a.y * a₁.y))
    _ = d * a.y * (a.x * a₁.y) := by ring
    _ <= d * a.y * (a.y * a₁.x) := by have := x_mul_y_le_y_mul_x h hax hay; have := h.d_pos; gcongr
    _ = (a.x ^ 2 - 1) * a₁.x := by rw [← a.prop_y]; ring
    _ < a.x * (a.x * a₁.x) := by linarith [h.1]

Depends on / 依赖: a.prop_y, d_pos, h.d_pos, hax.le, lt_add_neg_iff_add_lt, lt_of_mul_lt_mul_left, mul_neg, prop_y, x_inv, x_mul, x_mul_y_le_y_mul_x, y_inv, zero_add, zero_le_one, zero_le_one.trans
-/
theorem mul_inv_x_pos {a₁ : Solution₁ d} (h : IsFundamental a₁) {a : Solution₁ d} (hax : 1 < a.x)
    (hay : 0 < a.y) : 0 < (a * a₁⁻¹).x := by
  simp only [x_mul, x_inv, y_inv, mul_neg, lt_add_neg_iff_add_lt, zero_add]
refine lt_of_mul_lt_mul_left ?_ zero_le_one.trans hax.le
  calc a.x * (d * (a.y * a₁.y))
    _ = d * a.y * (a.x * a₁.y) := by ring
    _ <= d * a.y * (a.y * a₁.x) := by have := x_mul_y_le_y_mul_x h hax hay; have := h.d_pos; gcongr
    _ = (a.x ^ 2 - 1) * a₁.x := by rw [← a.prop_y]; ring
    _ < a.x * (a.x * a₁.x) := by linarith [h.1]

/--
theorem `mul_inv_x_lt_x` / 定理 `mul_inv_x_lt_x`

English:
theorem mul_inv_x_lt_x
  statement: {a₁ : Solution₁ d} (h : IsFundamental a₁) {a : Solution₁ d} (hax : 1 < a.x)
  proof: by
  simp only [x_mul, x_inv, y_inv, mul_neg, add_neg_lt_iff_le_add']
  refine lt_of_mul_lt_mul_left ?_ h.2.1.le
  calc a₁.y * (a.x * a₁.x)
    _ = a.x * a₁.y * a₁.x := by ring
    _ <= a.y * a₁.x * a₁.x := by have := h.1; have := x_mul_y_le_y_mul_x h hax hay; gcongr
  rw [mul_assoc]; rw [← sq]; rw [a₁.prop_x]; rw [← sub_neg]
  suffices a.y - a.x * a₁.y < 0 by convert! this using 1; ring
  rw [sub_neg]; rw [← abs_of_pos hay]; rw [← abs_of_pos h.2.1]; rw [← abs_of_pos <| zero_lt_one.trans hax]; rw [←
    abs_mul]; rw [← sq_lt_sq]; rw [mul_pow]; rw [a.prop_x]
  calc
    a.y ^ 2 = 1 * a.y ^ 2 := (one_mul _).symm
    _ <= d * a.y ^ 2 := (mul_le_mul_iff_left₀ <| sq_pos_of_pos hay).mpr h.d_pos
    _ < d * a.y ^ 2 + 1 := lt_add_one _
    _ = (1 + d * a.y ^ 2) * 1 := by rw [add_comm, mul_one]
    _ <= (1 + d * a.y ^ 2) * a₁.y ^ 2 :=
      (mul_le_mul_iff_right₀ (by have := h.d_pos; positivity)).mpr (sq_pos_of_pos h.2.1)

中文:
定理 mul_inv_x_lt_x
  结论: {a₁ : Solution₁ d} (h : IsFundamental a₁) {a : Solution₁ d} (hax : 1 < a.x)
  证明: by
  simp only [x_mul, x_inv, y_inv, mul_neg, add_neg_lt_iff_le_add']
  refine lt_of_mul_lt_mul_left ?_ h.2.1.le
  calc a₁.y * (a.x * a₁.x)
    _ = a.x * a₁.y * a₁.x := by ring
    _ <= a.y * a₁.x * a₁.x := by have := h.1; have := x_mul_y_le_y_mul_x h hax hay; gcongr
  rw [mul_assoc]; rw [← sq]; rw [a₁.prop_x]; rw [← sub_neg]
  suffices a.y - a.x * a₁.y < 0 by convert! this using 1; ring
  rw [sub_neg]; rw [← abs_of_pos hay]; rw [← abs_of_pos h.2.1]; rw [← abs_of_pos <| zero_lt_one.trans hax]; rw [←
    abs_mul]; rw [← sq_lt_sq]; rw [mul_pow]; rw [a.prop_x]
  calc
    a.y ^ 2 = 1 * a.y ^ 2 := (one_mul _).symm
    _ <= d * a.y ^ 2 := (mul_le_mul_iff_left₀ <| sq_pos_of_pos hay).mpr h.d_pos
    _ < d * a.y ^ 2 + 1 := lt_add_one _
    _ = (1 + d * a.y ^ 2) * 1 := by rw [add_comm, mul_one]
    _ <= (1 + d * a.y ^ 2) * a₁.y ^ 2 :=
      (mul_le_mul_iff_right₀ (by have := h.d_pos; positivity)).mpr (sq_pos_of_pos h.2.1)

Depends on / 依赖: abs_mul, abs_of_pos, add_neg_lt_iff_le_add, convert, lt_of_mul_lt_mul_left, mul_assoc, mul_neg, prop_x, sub_neg, x_inv, x_mul, x_mul_y_le_y_mul_x, y_inv, zero_lt_one, zero_lt_one.trans
-/
theorem mul_inv_x_lt_x {a₁ : Solution₁ d} (h : IsFundamental a₁) {a : Solution₁ d} (hax : 1 < a.x)
    (hay : 0 < a.y) : (a * a₁⁻¹).x < a.x := by
  simp only [x_mul, x_inv, y_inv, mul_neg, add_neg_lt_iff_le_add']
  refine lt_of_mul_lt_mul_left ?_ h.2.1.le
  calc a₁.y * (a.x * a₁.x)
    _ = a.x * a₁.y * a₁.x := by ring
    _ <= a.y * a₁.x * a₁.x := by have := h.1; have := x_mul_y_le_y_mul_x h hax hay; gcongr
  rw [mul_assoc]; rw [← sq]; rw [a₁.prop_x]; rw [← sub_neg]
  suffices a.y - a.x * a₁.y < 0 by convert! this using 1; ring
  rw [sub_neg]; rw [← abs_of_pos hay]; rw [← abs_of_pos h.2.1]; rw [← abs_of_pos <| zero_lt_one.trans hax]; rw [←
    abs_mul]; rw [← sq_lt_sq]; rw [mul_pow]; rw [a.prop_x]
  calc
    a.y ^ 2 = 1 * a.y ^ 2 := (one_mul _).symm
    _ <= d * a.y ^ 2 := (mul_le_mul_iff_left₀ <| sq_pos_of_pos hay).mpr h.d_pos
    _ < d * a.y ^ 2 + 1 := lt_add_one _
    _ = (1 + d * a.y ^ 2) * 1 := by rw [add_comm, mul_one]
    _ <= (1 + d * a.y ^ 2) * a₁.y ^ 2 :=
      (mul_le_mul_iff_right₀ (by have := h.d_pos; positivity)).mpr (sq_pos_of_pos h.2.1)

/--
theorem `eq_pow_of_nonneg` / 定理 `eq_pow_of_nonneg`

English:
theorem eq_pow_of_nonneg
  statement: {a₁ : Solution₁ d} (h : IsFundamental a₁) {a : Solution₁ d} (hax : 0 < a.x)
  proof: by
  lift a.x to Nat using hax.le with ax hax'
  induction ax using Nat.strong_induction_on generalizing a with | h x ih =>
  rcases hay.eq_or_lt with hy | hy
  · -- case 1: `a = 1`
    refine ⟨0, ?_⟩
    rcases eq_one_or_neg_one_iff_y_eq_zero.2 hy.symm with rfl | rfl
    · simp
    · simp at hax'
  · -- case 2: `a ≥ a₁`
    have hx₁ : 1 < a.x := by nlinarith [a.prop, h.d_pos]
    have hxx₁ := h.mul_inv_x_pos hx₁ hy
    have hxx₂ := h.mul_inv_x_lt_x hx₁ hy
    have hyy := h.mul_inv_y_nonneg hx₁ hy
    lift (a * a₁⁻¹).x to Nat using hxx₁.le with x' hx'
    obtain ⟨n, hn⟩ := ih x' (mod_cast hxx₂.trans_eq hax'.symm) hyy hx' hxx₁
    exact ⟨n + 1, by rw [pow_succ', ← hn, mul_comm a, ← mul_assoc, mul_inv_cancel, one_mul]⟩

中文:
定理 eq_pow_of_nonneg
  结论: {a₁ : Solution₁ d} (h : IsFundamental a₁) {a : Solution₁ d} (hax : 0 < a.x)
  证明: by
  lift a.x to Nat using hax.le with ax hax'
  induction ax using Nat.strong_induction_on generalizing a with | h x ih =>
  rcases hay.eq_or_lt with hy | hy
  · -- case 1: `a = 1`
    refine ⟨0, ?_⟩
    rcases eq_one_or_neg_one_iff_y_eq_zero.2 hy.symm with rfl | rfl
    · simp
    · simp at hax'
  · -- case 2: `a ≥ a₁`
    have hx₁ : 1 < a.x := by nlinarith [a.prop, h.d_pos]
    have hxx₁ := h.mul_inv_x_pos hx₁ hy
    have hxx₂ := h.mul_inv_x_lt_x hx₁ hy
    have hyy := h.mul_inv_y_nonneg hx₁ hy
    lift (a * a₁⁻¹).x to Nat using hxx₁.le with x' hx'
    obtain ⟨n, hn⟩ := ih x' (mod_cast hxx₂.trans_eq hax'.symm) hyy hx' hxx₁
    exact ⟨n + 1, by rw [pow_succ', ← hn, mul_comm a, ← mul_assoc, mul_inv_cancel, one_mul]⟩

Depends on / 依赖: Nat.strong_induction_on, a.prop, d_pos, eq_one_or_neg_one_iff_y_eq_zero, eq_or_lt, generalizing, h.d_pos, h.mul_inv_x_lt_x, h.mul_inv_x_pos, h.mul_inv_y_nonneg, hax.le, hay.eq_or_lt, hy.symm, mul_inv_x_lt_x, mul_inv_x_pos, mul_inv_y_nonneg, strong_induction_on
-/
theorem eq_pow_of_nonneg {a₁ : Solution₁ d} (h : IsFundamental a₁) {a : Solution₁ d} (hax : 0 < a.x)
    (hay : 0 <= a.y) : exists n : Nat, a = a₁ ^ n := by
  lift a.x to Nat using hax.le with ax hax'
  induction ax using Nat.strong_induction_on generalizing a with | h x ih =>
  rcases hay.eq_or_lt with hy | hy
  · -- case 1: `a = 1`
    refine ⟨0, ?_⟩
    rcases eq_one_or_neg_one_iff_y_eq_zero.2 hy.symm with rfl | rfl
    · simp
    · simp at hax'
  · -- case 2: `a ≥ a₁`
    have hx₁ : 1 < a.x := by nlinarith [a.prop, h.d_pos]
    have hxx₁ := h.mul_inv_x_pos hx₁ hy
    have hxx₂ := h.mul_inv_x_lt_x hx₁ hy
    have hyy := h.mul_inv_y_nonneg hx₁ hy
    lift (a * a₁⁻¹).x to Nat using hxx₁.le with x' hx'
    obtain ⟨n, hn⟩ := ih x' (mod_cast hxx₂.trans_eq hax'.symm) hyy hx' hxx₁
    exact ⟨n + 1, by rw [pow_succ', ← hn, mul_comm a, ← mul_assoc, mul_inv_cancel, one_mul]⟩

/--
theorem `eq_zpow_or_neg_zpow` / 定理 `eq_zpow_or_neg_zpow`

English:
theorem eq_zpow_or_neg_zpow
  given: {a₁ : Solution₁ d} (h : IsFundamental a₁) (a : Solution₁ d)
  proof: by
  obtain ⟨b, hbx, hby, hb⟩ := exists_pos_variant h.d_pos a
  obtain ⟨n, hn⟩ := h.eq_pow_of_nonneg hbx hby
  rcases hb with (rfl | rfl | rfl | hb)
  · exact ⟨n, Or.inl (mod_cast hn)⟩
  · exact ⟨-n, Or.inl (by simp [hn])⟩
  · exact ⟨n, Or.inr (by simp [hn])⟩
  · rw [Set.mem_singleton_iff] at hb
    rw [hb]
    exact ⟨-n, Or.inr (by simp [hn])⟩

中文:
定理 eq_zpow_or_neg_zpow
  条件: {a₁ : Solution₁ d} (h : IsFundamental a₁) (a : Solution₁ d)
  证明: by
  obtain ⟨b, hbx, hby, hb⟩ := exists_pos_variant h.d_pos a
  obtain ⟨n, hn⟩ := h.eq_pow_of_nonneg hbx hby
  rcases hb with (rfl | rfl | rfl | hb)
  · exact ⟨n, Or.inl (mod_cast hn)⟩
  · exact ⟨-n, Or.inl (by simp [hn])⟩
  · exact ⟨n, Or.inr (by simp [hn])⟩
  · rw [Set.mem_singleton_iff] at hb
    rw [hb]
    exact ⟨-n, Or.inr (by simp [hn])⟩

Depends on / 依赖: Or.inl, Or.inr, Set.mem_singleton_iff, d_pos, eq_pow_of_nonneg, exists_pos_variant, h.d_pos, h.eq_pow_of_nonneg, mem_singleton_iff, mod_cast
-/
theorem eq_zpow_or_neg_zpow {a₁ : Solution₁ d} (h : IsFundamental a₁) (a : Solution₁ d) :
    exists n : Int, a = a₁ ^ n ∨ a = -a₁ ^ n := by
  obtain ⟨b, hbx, hby, hb⟩ := exists_pos_variant h.d_pos a
  obtain ⟨n, hn⟩ := h.eq_pow_of_nonneg hbx hby
  rcases hb with (rfl | rfl | rfl | hb)
  · exact ⟨n, Or.inl (mod_cast hn)⟩
  · exact ⟨-n, Or.inl (by simp [hn])⟩
  · exact ⟨n, Or.inr (by simp [hn])⟩
  · rw [Set.mem_singleton_iff] at hb
    rw [hb]
    exact ⟨-n, Or.inr (by simp [hn])⟩

end IsFundamental

open Solution₁ IsFundamental

/--
theorem `existsUnique_pos_generator` / 定理 `existsUnique_pos_generator`

English:
theorem existsUnique_pos_generator
  given: (h₀ : 0 < d) (hd : ¬IsSquare d)
  proof: by
  obtain ⟨a₁, ha₁⟩ := IsFundamental.exists_of_not_isSquare h₀ hd
  refine ⟨a₁, ⟨ha₁.1, ha₁.2.1, ha₁.eq_zpow_or_neg_zpow⟩, fun a (H : 1 < _ ∧ _) => ?_⟩
  obtain ⟨Hx, Hy, H⟩ := H
  obtain ⟨n₁, hn₁⟩ := H a₁
  obtain ⟨n₂, hn₂⟩ := ha₁.eq_zpow_or_neg_zpow a
  rcases hn₂ with (rfl | rfl)
  · rw [← zpow_mul, eq_comm, @eq_comm _ a₁, ← mul_inv_eq_one, ← @mul_inv_eq_one _ _ _ a₁, ←
      zpow_neg_one, neg_mul, ← zpow_add, ← sub_eq_add_neg] at hn₁
    rcases hn₁ with hn₁ | hn₁
    · rcases Int.isUnit_iff.mp
          (.of_mul_eq_one _ <|
sub_eq_zero.mp (ha₁.zpow_eq_one_iff (n₂ * n₁ - 1)).mp hn₁) with
        (rfl | rfl)
      · rw [zpow_one]
      · rw [zpow_neg_one, y_inv, lt_neg, neg_zero] at Hy
        exact False.elim (lt_irrefl _ <| ha₁.2.1.trans Hy)
    · rw [← zpow_zero a₁, eq_comm] at hn₁
      exact False.elim (ha₁.zpow_ne_neg_zpow hn₁)
  · rw [x_neg, lt_neg] at Hx
    have := (x_zpow_pos (zero_lt_one.trans ha₁.1) n₂).trans Hx
    norm_num at this

中文:
定理 存在Unique_pos_generator
  条件: (h₀ : 0 < d) (hd : ¬IsSquare d)
  证明: by
  obtain ⟨a₁, ha₁⟩ := IsFundamental.exists_of_not_isSquare h₀ hd
  refine ⟨a₁, ⟨ha₁.1, ha₁.2.1, ha₁.eq_zpow_or_neg_zpow⟩, fun a (H : 1 < _ ∧ _) => ?_⟩
  obtain ⟨Hx, Hy, H⟩ := H
  obtain ⟨n₁, hn₁⟩ := H a₁
  obtain ⟨n₂, hn₂⟩ := ha₁.eq_zpow_or_neg_zpow a
  rcases hn₂ with (rfl | rfl)
  · rw [← zpow_mul, eq_comm, @eq_comm _ a₁, ← mul_inv_eq_one, ← @mul_inv_eq_one _ _ _ a₁, ←
      zpow_neg_one, neg_mul, ← zpow_add, ← sub_eq_add_neg] at hn₁
    rcases hn₁ with hn₁ | hn₁
    · rcases Int.isUnit_iff.mp
          (.of_mul_eq_one _ <|
sub_eq_zero.mp (ha₁.zpow_eq_one_iff (n₂ * n₁ - 1)).mp hn₁) with
        (rfl | rfl)
      · rw [zpow_one]
      · rw [zpow_neg_one, y_inv, lt_neg, neg_zero] at Hy
        exact False.elim (lt_irrefl _ <| ha₁.2.1.trans Hy)
    · rw [← zpow_zero a₁, eq_comm] at hn₁
      exact False.elim (ha₁.zpow_ne_neg_zpow hn₁)
  · rw [x_neg, lt_neg] at Hx
    have := (x_zpow_pos (zero_lt_one.trans ha₁.1) n₂).trans Hx
    norm_num at this

Depends on / 依赖: Int.isUnit_iff.mp, IsFundamental, IsFundamental.exists_of_not_isSquare, eq_comm, eq_zpow_or_neg_zpow, exists_of_not_isSquare, isUnit_iff, mul_inv_eq_one, neg_mul, of_mul_eq_one, sub_eq_add_neg, zpow_add, zpow_mul, zpow_neg_one
-/
theorem existsUnique_pos_generator (h₀ : 0 < d) (hd : ¬IsSquare d) :
    exists! a₁ : Solution₁ d,
      1 < a₁.x ∧ 0 < a₁.y ∧ forall a : Solution₁ d, exists n : Int, a = a₁ ^ n ∨ a = -a₁ ^ n := by
  obtain ⟨a₁, ha₁⟩ := IsFundamental.exists_of_not_isSquare h₀ hd
  refine ⟨a₁, ⟨ha₁.1, ha₁.2.1, ha₁.eq_zpow_or_neg_zpow⟩, fun a (H : 1 < _ ∧ _) => ?_⟩
  obtain ⟨Hx, Hy, H⟩ := H
  obtain ⟨n₁, hn₁⟩ := H a₁
  obtain ⟨n₂, hn₂⟩ := ha₁.eq_zpow_or_neg_zpow a
  rcases hn₂ with (rfl | rfl)
  · rw [← zpow_mul, eq_comm, @eq_comm _ a₁, ← mul_inv_eq_one, ← @mul_inv_eq_one _ _ _ a₁, ←
      zpow_neg_one, neg_mul, ← zpow_add, ← sub_eq_add_neg] at hn₁
    rcases hn₁ with hn₁ | hn₁
    · rcases Int.isUnit_iff.mp
          (.of_mul_eq_one _ <|
sub_eq_zero.mp (ha₁.zpow_eq_one_iff (n₂ * n₁ - 1)).mp hn₁) with
        (rfl | rfl)
      · rw [zpow_one]
      · rw [zpow_neg_one, y_inv, lt_neg, neg_zero] at Hy
        exact False.elim (lt_irrefl _ <| ha₁.2.1.trans Hy)
    · rw [← zpow_zero a₁, eq_comm] at hn₁
      exact False.elim (ha₁.zpow_ne_neg_zpow hn₁)
  · rw [x_neg, lt_neg] at Hx
    have := (x_zpow_pos (zero_lt_one.trans ha₁.1) n₂).trans Hx
    norm_num at this

/--
theorem `pos_generator_iff_fundamental` / 定理 `pos_generator_iff_fundamental`

English:
theorem pos_generator_iff_fundamental
  given: (a : Solution₁ d)
  proof: by
  refine ⟨fun h => ?_, fun H => ⟨H.1, H.2.1, H.eq_zpow_or_neg_zpow⟩⟩
  have h₀ := d_pos_of_one_lt_x h.1
  have hd := d_nonsquare_of_one_lt_x h.1
  obtain ⟨a₁, ha₁⟩ := IsFundamental.exists_of_not_isSquare h₀ hd
  obtain ⟨b, -, hb₂⟩ := existsUnique_pos_generator h₀ hd
  rwa [hb₂ a h, ← hb₂ a₁ ⟨ha₁.1, ha₁.2.1, ha₁.eq_zpow_or_neg_zpow⟩]

中文:
定理 pos_generator_iff_fundamental
  条件: (a : Solution₁ d)
  证明: by
  refine ⟨fun h => ?_, fun H => ⟨H.1, H.2.1, H.eq_zpow_or_neg_zpow⟩⟩
  have h₀ := d_pos_of_one_lt_x h.1
  have hd := d_nonsquare_of_one_lt_x h.1
  obtain ⟨a₁, ha₁⟩ := IsFundamental.exists_of_not_isSquare h₀ hd
  obtain ⟨b, -, hb₂⟩ := existsUnique_pos_generator h₀ hd
  rwa [hb₂ a h, ← hb₂ a₁ ⟨ha₁.1, ha₁.2.1, ha₁.eq_zpow_or_neg_zpow⟩]

Depends on / 依赖: H.eq_zpow_or_neg_zpow, IsFundamental, IsFundamental.exists_of_not_isSquare, d_nonsquare_of_one_lt_x, d_pos_of_one_lt_x, eq_zpow_or_neg_zpow, existsUnique_pos_generator, exists_of_not_isSquare
-/
theorem pos_generator_iff_fundamental (a : Solution₁ d) :
    (1 < a.x ∧ 0 < a.y ∧ forall b : Solution₁ d, exists n : Int, b = a ^ n ∨ b = -a ^ n) ↔ IsFundamental a := by
  refine ⟨fun h => ?_, fun H => ⟨H.1, H.2.1, H.eq_zpow_or_neg_zpow⟩⟩
  have h₀ := d_pos_of_one_lt_x h.1
  have hd := d_nonsquare_of_one_lt_x h.1
  obtain ⟨a₁, ha₁⟩ := IsFundamental.exists_of_not_isSquare h₀ hd
  obtain ⟨b, -, hb₂⟩ := existsUnique_pos_generator h₀ hd
  rwa [hb₂ a h, ← hb₂ a₁ ⟨ha₁.1, ha₁.2.1, ha₁.eq_zpow_or_neg_zpow⟩]

end Pell
