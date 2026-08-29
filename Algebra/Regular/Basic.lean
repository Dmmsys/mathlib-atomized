/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Commute.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Regular.Defs

/-!
# Regular elements

By definition, a regular element in a commutative ring is a non-zero divisor.
Lemma `IsRegular.of_ne_zero` implies that every non-zero element of an integral domain is regular.
Since it assumes that the ring is a cancellative `MonoidWithZero` it applies also,
for instance, to `ℕ`.

The lemmas in Section `MulZeroClass` show that the `0` element is (left/right-)regular if and
only if the `MulZeroClass` is trivial. This is useful when figuring out stopping conditions for
regular sequences: if `0` is ever an element of a regular sequence, then we can extend the sequence
by adding one further `0`.

The final goal is to develop part of the API to prove, eventually, results about non-zero-divisors.
-/

public section

variable {R : Type*}

section Mul

variable [Mul R]

/--
theorem `IsLeftRegular.right_of_commute` / 定理 `IsLeftRegular.right_of_commute`

English:
theorem IsLeftRegular.right_of_commute
  statement: {a : R}
  proof: fun x y xy => h (ca x).trans xy.trans (ca y).symm

中文:
定理 IsLeftRegular.right_of_commute
  结论: {a : R}
  证明: fun x y xy => h (ca x).trans xy.trans (ca y).symm
-/
@[to_additive] theorem IsLeftRegular.right_of_commute {a : R}
    (ca : forall b, Commute a b) (h : IsLeftRegular a) : IsRightRegular a :=
fun x y xy => h (ca x).trans xy.trans (ca y).symm

/--
theorem `IsRightRegular.left_of_commute` / 定理 `IsRightRegular.left_of_commute`

English:
theorem IsRightRegular.left_of_commute
  statement: {a : R}
  proof: by
  simp only [@Commute.symm_iff R _ a] at ca
exact fun x y xy => h (ca x).trans xy.trans (ca y).symm

中文:
定理 IsRightRegular.left_of_commute
  结论: {a : R}
  证明: by
  simp only [@Commute.symm_iff R _ a] at ca
exact fun x y xy => h (ca x).trans xy.trans (ca y).symm
-/
@[to_additive] theorem IsRightRegular.left_of_commute {a : R}
    (ca : forall b, Commute a b) (h : IsRightRegular a) : IsLeftRegular a := by
  simp only [@Commute.symm_iff R _ a] at ca
exact fun x y xy => h (ca x).trans xy.trans (ca y).symm

/--
theorem `Commute.isRightRegular_iff` / 定理 `Commute.isRightRegular_iff`

English:
theorem Commute.isRightRegular_iff
  given: {a : R} (ca : forall b, Commute a b)
  proof: ⟨IsRightRegular.left_of_commute ca, IsLeftRegular.right_of_commute ca⟩

@[to_additive]

中文:
定理 Commute.isRightRegular_iff
  条件: {a : R} (ca : 对任意 b, Commute a b)
  证明: ⟨IsRightRegular.left_of_commute ca, IsLeftRegular.right_of_commute ca⟩

@[to_additive]
-/
@[to_additive] theorem Commute.isRightRegular_iff {a : R} (ca : forall b, Commute a b) :
    IsRightRegular a ↔ IsLeftRegular a :=
  ⟨IsRightRegular.left_of_commute ca, IsLeftRegular.right_of_commute ca⟩

@[to_additive]
/--
theorem `Commute.isRegular_iff` / 定理 `Commute.isRegular_iff`

English:
theorem Commute.isRegular_iff
  given: {a : R} (ca : forall b, Commute a b)
  statement: IsRegular a ↔ IsLeftRegular a
  proof: ⟨fun h => h.left, fun h => ⟨h, h.right_of_commute ca⟩⟩

中文:
定理 Commute.isRegular_iff
  条件: {a : R} (ca : 对任意 b, Commute a b)
  结论: 是正则 a ↔ IsLeftRegular a
  证明: ⟨fun h => h.left, fun h => ⟨h, h.right_of_commute ca⟩⟩

Depends on / 依赖: h.left, h.right_of_commute, right_of_commute
-/
theorem Commute.isRegular_iff {a : R} (ca : forall b, Commute a b) : IsRegular a ↔ IsLeftRegular a :=
  ⟨fun h => h.left, fun h => ⟨h, h.right_of_commute ca⟩⟩

end Mul

section Semigroup

variable [Semigroup R] {a b : R}

/-- In a semigroup, the product of left-regular elements is left-regular. -/
@[to_additive
/-- In an additive semigroup, the sum of add-left-regular elements is add-left.regular. -/]
/--
theorem `IsLeftRegular.mul` / 定理 `IsLeftRegular.mul`

English:
theorem IsLeftRegular.mul
  given: (lra : IsLeftRegular a) (lrb : IsLeftRegular b)
  statement: IsLeftRegular (a * b)
  proof: show Function.Injective (((a * b) * ·)) from comp_mul_left a b ▸ lra.comp lrb

中文:
定理 IsLeftRegular.mul
  条件: (lra : IsLeftRegular a) (lrb : IsLeftRegular b)
  结论: IsLeftRegular (a * b)
  证明: show Function.Injective (((a * b) * ·)) from comp_mul_left a b ▸ lra.comp lrb

Depends on / 依赖: Function, Function.Injective, Injective, comp_mul_left, lra.comp
-/
theorem IsLeftRegular.mul (lra : IsLeftRegular a) (lrb : IsLeftRegular b) : IsLeftRegular (a * b) :=
  show Function.Injective (((a * b) * ·)) from comp_mul_left a b ▸ lra.comp lrb

/-- In a semigroup, the product of right-regular elements is right-regular. -/
@[to_additive
/-- In an additive semigroup, the sum of add-right-regular elements is add-right-regular. -/]
/--
theorem `IsRightRegular.mul` / 定理 `IsRightRegular.mul`

English:
theorem IsRightRegular.mul
  given: (rra : IsRightRegular a) (rrb : IsRightRegular b)
  proof: show Function.Injective (· * (a * b)) from comp_mul_right b a ▸ rrb.comp rra

中文:
定理 IsRightRegular.mul
  条件: (rra : IsRightRegular a) (rrb : IsRightRegular b)
  证明: show Function.Injective (· * (a * b)) from comp_mul_right b a ▸ rrb.comp rra

Depends on / 依赖: Function, Function.Injective, Injective, comp_mul_right, rrb.comp
-/
theorem IsRightRegular.mul (rra : IsRightRegular a) (rrb : IsRightRegular b) :
    IsRightRegular (a * b) :=
  show Function.Injective (· * (a * b)) from comp_mul_right b a ▸ rrb.comp rra

/-- In a semigroup, the product of regular elements is regular. -/
@[to_additive /-- In an additive semigroup, the sum of add-regular elements is add-regular. -/]
/--
theorem `IsRegular.mul` / 定理 `IsRegular.mul`

English:
theorem IsRegular.mul
  given: (rra : IsRegular a) (rrb : IsRegular b)
  proof: ⟨rra.left.mul rrb.left, rra.right.mul rrb.right⟩

中文:
定理 是正则.mul
  条件: (rra : 是正则 a) (rrb : 是正则 b)
  证明: ⟨rra.left.mul rrb.left, rra.right.mul rrb.right⟩

Depends on / 依赖: rra.left.mul, rra.right.mul, rrb.left, rrb.right
-/
theorem IsRegular.mul (rra : IsRegular a) (rrb : IsRegular b) :
    IsRegular (a * b) :=
  ⟨rra.left.mul rrb.left, rra.right.mul rrb.right⟩

/-- If an element `b` becomes left-regular after multiplying it on the left by a left-regular
element, then `b` is left-regular. -/
@[to_additive /-- If an element `b` becomes add-left-regular after adding to it on the left
an add-left-regular element, then `b` is add-left-regular. -/]
/--
theorem `IsLeftRegular.of_mul` / 定理 `IsLeftRegular.of_mul`

English:
theorem IsLeftRegular.of_mul
  given: (ab : IsLeftRegular (a * b))
  statement: IsLeftRegular b
  proof: Function.Injective.of_comp (f := (a * ·)) (by rwa [comp_mul_left a b])

中文:
定理 IsLeftRegular.of_mul
  条件: (ab : IsLeftRegular (a * b))
  结论: IsLeftRegular b
  证明: Function.Injective.of_comp (f := (a * ·)) (by rwa [comp_mul_left a b])

Depends on / 依赖: Function, Function.Injective.of_comp, Injective, comp_mul_left, of_comp
-/
theorem IsLeftRegular.of_mul (ab : IsLeftRegular (a * b)) : IsLeftRegular b :=
  Function.Injective.of_comp (f := (a * ·)) (by rwa [comp_mul_left a b])

/-- An element is left-regular if and only if multiplying it on the left by a left-regular element
is left-regular. -/
@[to_additive (attr := simp) /-- An element is add-left-regular if and only if adding to it on the
left an add-left-regular element is add-left-regular. -/]
/--
theorem `mul_isLeftRegular_iff` / 定理 `mul_isLeftRegular_iff`

English:
theorem mul_isLeftRegular_iff
  given: (b : R) (ha : IsLeftRegular a)
  proof: ⟨fun ab => IsLeftRegular.of_mul ab, fun ab => IsLeftRegular.mul ha ab⟩

中文:
定理 mul_isLeftRegular_iff
  条件: (b : R) (ha : IsLeftRegular a)
  证明: ⟨fun ab => IsLeftRegular.of_mul ab, fun ab => IsLeftRegular.mul ha ab⟩

Depends on / 依赖: IsLeftRegular, IsLeftRegular.mul, IsLeftRegular.of_mul, of_mul
-/
theorem mul_isLeftRegular_iff (b : R) (ha : IsLeftRegular a) :
    IsLeftRegular (a * b) ↔ IsLeftRegular b :=
  ⟨fun ab => IsLeftRegular.of_mul ab, fun ab => IsLeftRegular.mul ha ab⟩

/-- If an element `b` becomes right-regular after multiplying it on the right by a right-regular
element, then `b` is right-regular. -/
@[to_additive /-- If an element `b` becomes add-right-regular after adding to it on the right
an add-right-regular element, then `b` is add-right-regular. -/]
/--
theorem `IsRightRegular.of_mul` / 定理 `IsRightRegular.of_mul`

English:
theorem IsRightRegular.of_mul
  given: (ab : IsRightRegular (b * a))
  statement: IsRightRegular b
  proof: by
  refine fun x y xy => ab (?_ : x * (b * a) = y * (b * a))
  rw [← mul_assoc]; rw [← mul_assoc]
  exact congr_arg (· * a) xy

中文:
定理 IsRightRegular.of_mul
  条件: (ab : IsRightRegular (b * a))
  结论: IsRightRegular b
  证明: by
  refine fun x y xy => ab (?_ : x * (b * a) = y * (b * a))
  rw [← mul_assoc]; rw [← mul_assoc]
  exact congr_arg (· * a) xy

Depends on / 依赖: congr_arg, mul_assoc
-/
theorem IsRightRegular.of_mul (ab : IsRightRegular (b * a)) : IsRightRegular b := by
  refine fun x y xy => ab (?_ : x * (b * a) = y * (b * a))
  rw [← mul_assoc]; rw [← mul_assoc]
  exact congr_arg (· * a) xy

/-- An element is right-regular if and only if multiplying it on the right with a right-regular
element is right-regular. -/
@[to_additive (attr := simp)
/-- An element is add-right-regular if and only if adding it on the right to
an add-right-regular element is add-right-regular. -/]
/--
theorem `mul_isRightRegular_iff` / 定理 `mul_isRightRegular_iff`

English:
theorem mul_isRightRegular_iff
  given: (b : R) (ha : IsRightRegular a)
  proof: ⟨fun ab => IsRightRegular.of_mul ab, fun ab => IsRightRegular.mul ab ha⟩

中文:
定理 mul_isRightRegular_iff
  条件: (b : R) (ha : IsRightRegular a)
  证明: ⟨fun ab => IsRightRegular.of_mul ab, fun ab => IsRightRegular.mul ab ha⟩

Depends on / 依赖: IsRightRegular, IsRightRegular.mul, IsRightRegular.of_mul, of_mul
-/
theorem mul_isRightRegular_iff (b : R) (ha : IsRightRegular a) :
    IsRightRegular (b * a) ↔ IsRightRegular b :=
  ⟨fun ab => IsRightRegular.of_mul ab, fun ab => IsRightRegular.mul ab ha⟩

/-- Two elements `a` and `b` are regular if and only if both products `a * b` and `b * a`
are regular. -/
@[to_additive /-- Two elements `a` and `b` are add-regular if and only if both sums `a + b` and
`b + a` are add-regular. -/]
/--
theorem `isRegular_mul_and_mul_iff` / 定理 `isRegular_mul_and_mul_iff`

English:
theorem isRegular_mul_and_mul_iff
  proof: by
  refine ⟨?_, ?_⟩
  · rintro ⟨ab, ba⟩
    exact
      ⟨⟨IsLeftRegular.of_mul ba.left, IsRightRegular.of_mul ab.right⟩,
        ⟨IsLeftRegular.of_mul ab.left, IsRightRegular.of_mul ba.right⟩⟩
  · rintro ⟨ha, hb⟩
    exact ⟨ha.mul hb, hb.mul ha⟩

中文:
定理 isRegular_mul_and_mul_iff
  证明: by
  refine ⟨?_, ?_⟩
  · rintro ⟨ab, ba⟩
    exact
      ⟨⟨IsLeftRegular.of_mul ba.left, IsRightRegular.of_mul ab.right⟩,
        ⟨IsLeftRegular.of_mul ab.left, IsRightRegular.of_mul ba.right⟩⟩
  · rintro ⟨ha, hb⟩
    exact ⟨ha.mul hb, hb.mul ha⟩

Depends on / 依赖: IsLeftRegular, IsLeftRegular.of_mul, IsRightRegular, IsRightRegular.of_mul, ab.left, ab.right, ba.left, ba.right, ha.mul, hb.mul, of_mul
-/
theorem isRegular_mul_and_mul_iff :
    IsRegular (a * b) ∧ IsRegular (b * a) ↔ IsRegular a ∧ IsRegular b := by
  refine ⟨?_, ?_⟩
  · rintro ⟨ab, ba⟩
    exact
      ⟨⟨IsLeftRegular.of_mul ba.left, IsRightRegular.of_mul ab.right⟩,
        ⟨IsLeftRegular.of_mul ab.left, IsRightRegular.of_mul ba.right⟩⟩
  · rintro ⟨ha, hb⟩
    exact ⟨ha.mul hb, hb.mul ha⟩

/-- The "most used" implication of `mul_and_mul_iff`, with split hypotheses, instead of `∧`. -/
@[to_additive /-- The "most used" implication of `add_and_add_iff`, with split
hypotheses, instead of `∧`. -/]
/--
theorem `IsRegular.and_of_mul_of_mul` / 定理 `IsRegular.and_of_mul_of_mul`

English:
theorem IsRegular.and_of_mul_of_mul
  given: (ab : IsRegular (a * b)) (ba : IsRegular (b * a))
  proof: isRegular_mul_and_mul_iff.mp ⟨ab, ba⟩

中文:
定理 是正则.and_of_mul_of_mul
  条件: (ab : 是正则 (a * b)) (ba : 是正则 (b * a))
  证明: isRegular_mul_and_mul_iff.mp ⟨ab, ba⟩

Depends on / 依赖: isRegular_mul_and_mul_iff, isRegular_mul_and_mul_iff.mp
-/
theorem IsRegular.and_of_mul_of_mul (ab : IsRegular (a * b)) (ba : IsRegular (b * a)) :
    IsRegular a ∧ IsRegular b :=
  isRegular_mul_and_mul_iff.mp ⟨ab, ba⟩

end Semigroup


section MulOneClass

variable [MulOneClass R]

/-- If multiplying by `1` on either side is the identity, `1` is regular. -/
@[to_additive /-- If adding `0` on either side is the identity, `0` is regular. -/]
/--
theorem `isRegular_one` / 定理 `isRegular_one`

English:
theorem isRegular_one
  statement: IsRegular (1 : R)
  proof: ⟨fun a b ab => (one_mul a).symm.trans (Eq.trans ab (one_mul b)), fun a b ab =>
    (mul_one a).symm.trans (Eq.trans ab (mul_one b))⟩

中文:
定理 isRegular_one
  结论: 是正则 (1 : R)
  证明: ⟨fun a b ab => (one_mul a).symm.trans (Eq.trans ab (one_mul b)), fun a b ab =>
    (mul_one a).symm.trans (Eq.trans ab (mul_one b))⟩

Depends on / 依赖: Eq.trans, mul_one, one_mul, symm.trans
-/
theorem isRegular_one : IsRegular (1 : R) :=
  ⟨fun a b ab => (one_mul a).symm.trans (Eq.trans ab (one_mul b)), fun a b ab =>
    (mul_one a).symm.trans (Eq.trans ab (mul_one b))⟩

end MulOneClass

section CommSemigroup

variable [CommSemigroup R] {a b : R}

/-- A product is regular if and only if the factors are. -/
@[to_additive /-- A sum is add-regular if and only if the summands are. -/]
/--
theorem `isRegular_mul_iff` / 定理 `isRegular_mul_iff`

English:
theorem isRegular_mul_iff
  statement: IsRegular (a * b) ↔ IsRegular a ∧ IsRegular b
  proof: by
  refine Iff.trans ?_ isRegular_mul_and_mul_iff
  exact ⟨fun ab => ⟨ab, by rwa [mul_comm]⟩, fun rab => rab.1⟩

中文:
定理 isRegular_mul_iff
  结论: 是正则 (a * b) ↔ 是正则 a ∧ 是正则 b
  证明: by
  refine Iff.trans ?_ isRegular_mul_and_mul_iff
  exact ⟨fun ab => ⟨ab, by rwa [mul_comm]⟩, fun rab => rab.1⟩

Depends on / 依赖: Iff.trans, isRegular_mul_and_mul_iff, mul_comm
-/
theorem isRegular_mul_iff : IsRegular (a * b) ↔ IsRegular a ∧ IsRegular b := by
  refine Iff.trans ?_ isRegular_mul_and_mul_iff
  exact ⟨fun ab => ⟨ab, by rwa [mul_comm]⟩, fun rab => rab.1⟩

/-- If a product is regular, so is its left factor. -/
@[to_additive /-- If a sum is add-regular, so is its left summand. -/]
/--
theorem `IsRegular.of_mul_left` / 定理 `IsRegular.of_mul_left`

English:
theorem IsRegular.of_mul_left
  given: (h : IsRegular (a * b))
  statement: IsRegular a
  proof: (isRegular_mul_iff.mp h).1

中文:
定理 是正则.of_mul_left
  条件: (h : 是正则 (a * b))
  结论: 是正则 a
  证明: (isRegular_mul_iff.mp h).1

Depends on / 依赖: isRegular_mul_iff, isRegular_mul_iff.mp
-/
theorem IsRegular.of_mul_left (h : IsRegular (a * b)) : IsRegular a :=
  (isRegular_mul_iff.mp h).1

/-- If a product is regular, so is its right factor. -/
@[to_additive /-- If a sum is add-regular, so is its right summand. -/]
/--
theorem `IsRegular.of_mul_right` / 定理 `IsRegular.of_mul_right`

English:
theorem IsRegular.of_mul_right
  given: (h : IsRegular (a * b))
  statement: IsRegular b
  proof: (isRegular_mul_iff.mp h).2

中文:
定理 是正则.of_mul_right
  条件: (h : 是正则 (a * b))
  结论: 是正则 b
  证明: (isRegular_mul_iff.mp h).2

Depends on / 依赖: isRegular_mul_iff, isRegular_mul_iff.mp
-/
theorem IsRegular.of_mul_right (h : IsRegular (a * b)) : IsRegular b :=
  (isRegular_mul_iff.mp h).2

end CommSemigroup

section Monoid

variable [Monoid R] {a b : R} {n : Nat}

/-- An element admitting a left inverse is left-regular. -/
@[to_additive /-- An element admitting a left additive opposite is add-left-regular. -/]
/--
theorem `isLeftRegular_of_mul_eq_one` / 定理 `isLeftRegular_of_mul_eq_one`

English:
theorem isLeftRegular_of_mul_eq_one
  given: (h : b * a = 1)
  statement: IsLeftRegular a
  proof: IsLeftRegular.of_mul (a := b) (by rw [h]; exact isRegular_one.left)

中文:
定理 isLeftRegular_of_mul_eq_one
  条件: (h : b * a = 1)
  结论: IsLeftRegular a
  证明: IsLeftRegular.of_mul (a := b) (by rw [h]; exact isRegular_one.left)

Depends on / 依赖: IsLeftRegular, IsLeftRegular.of_mul, isRegular_one, isRegular_one.left, of_mul
-/
theorem isLeftRegular_of_mul_eq_one (h : b * a = 1) : IsLeftRegular a :=
  IsLeftRegular.of_mul (a := b) (by rw [h]; exact isRegular_one.left)

/-- An element admitting a right inverse is right-regular. -/
@[to_additive /-- An element admitting a right additive opposite is add-right-regular. -/]
/--
theorem `isRightRegular_of_mul_eq_one` / 定理 `isRightRegular_of_mul_eq_one`

English:
theorem isRightRegular_of_mul_eq_one
  given: (h : a * b = 1)
  statement: IsRightRegular a
  proof: IsRightRegular.of_mul (a := b) (by rw [h]; exact isRegular_one.right)

中文:
定理 isRightRegular_of_mul_eq_one
  条件: (h : a * b = 1)
  结论: IsRightRegular a
  证明: IsRightRegular.of_mul (a := b) (by rw [h]; exact isRegular_one.right)

Depends on / 依赖: IsRightRegular, IsRightRegular.of_mul, isRegular_one, isRegular_one.right, of_mul
-/
theorem isRightRegular_of_mul_eq_one (h : a * b = 1) : IsRightRegular a :=
  IsRightRegular.of_mul (a := b) (by rw [h]; exact isRegular_one.right)

/-- If `R` is a monoid, an element in `Rˣ` is regular. -/
@[to_additive /-- If `R` is an additive monoid, an element in `add_units R` is add-regular. -/]
/--
theorem `Units.isRegular` / 定理 `Units.isRegular`

English:
theorem Units.isRegular
  given: (a : Rˣ)
  statement: IsRegular (a : R)
  proof: ⟨isLeftRegular_of_mul_eq_one a.inv_mul, isRightRegular_of_mul_eq_one a.mul_inv⟩

中文:
定理 单位群.isRegular
  条件: (a : Rˣ)
  结论: 是正则 (a : R)
  证明: ⟨isLeftRegular_of_mul_eq_one a.inv_mul, isRightRegular_of_mul_eq_one a.mul_inv⟩

Depends on / 依赖: a.inv_mul, a.mul_inv, inv_mul, isLeftRegular_of_mul_eq_one, isRightRegular_of_mul_eq_one, mul_inv
-/
theorem Units.isRegular (a : Rˣ) : IsRegular (a : R) :=
  ⟨isLeftRegular_of_mul_eq_one a.inv_mul, isRightRegular_of_mul_eq_one a.mul_inv⟩

/-- A unit in a monoid is regular. -/
@[to_additive /-- An additive unit in an additive monoid is add-regular. -/]
/--
theorem `IsUnit.isRegular` / 定理 `IsUnit.isRegular`

English:
theorem IsUnit.isRegular
  given: (ua : IsUnit a)
  statement: IsRegular a
  proof: by
  rcases ua with ⟨a, rfl⟩
  exact Units.isRegular a

中文:
定理 是单位.isRegular
  条件: (ua : 是单位 a)
  结论: 是正则 a
  证明: by
  rcases ua with ⟨a, rfl⟩
  exact Units.isRegular a

Depends on / 依赖: Units.isRegular, isRegular
-/
theorem IsUnit.isRegular (ua : IsUnit a) : IsRegular a := by
  rcases ua with ⟨a, rfl⟩
  exact Units.isRegular a

/-- Any power of a left-regular element is left-regular. -/
@[to_additive]
/--
lemma `IsLeftRegular.pow` / 引理 `IsLeftRegular.pow`

English:
lemma IsLeftRegular.pow
  given: (n : Nat) (rla : IsLeftRegular a)
  statement: IsLeftRegular (a ^ n)
  proof: by
  simp only [IsLeftRegular, ← mul_left_iterate, rla.iterate n]

中文:
引理 IsLeftRegular.pow
  条件: (n : 自然数) (rla : IsLeftRegular a)
  结论: IsLeftRegular (a ^ n)
  证明: by
  simp only [IsLeftRegular, ← mul_left_iterate, rla.iterate n]

Depends on / 依赖: IsLeftRegular, iterate, mul_left_iterate, rla.iterate
-/
lemma IsLeftRegular.pow (n : Nat) (rla : IsLeftRegular a) : IsLeftRegular (a ^ n) := by
  simp only [IsLeftRegular, ← mul_left_iterate, rla.iterate n]

/-- Any power of a right-regular element is right-regular. -/
@[to_additive]
/--
lemma `IsRightRegular.pow` / 引理 `IsRightRegular.pow`

English:
lemma IsRightRegular.pow
  given: (n : Nat) (rra : IsRightRegular a)
  statement: IsRightRegular (a ^ n)
  proof: by
  rw [IsRightRegular]; rw [← mul_right_iterate]
  exact rra.iterate n

中文:
引理 IsRightRegular.pow
  条件: (n : 自然数) (rra : IsRightRegular a)
  结论: IsRightRegular (a ^ n)
  证明: by
  rw [IsRightRegular]; rw [← mul_right_iterate]
  exact rra.iterate n

Depends on / 依赖: IsRightRegular, iterate, mul_right_iterate, rra.iterate
-/
lemma IsRightRegular.pow (n : Nat) (rra : IsRightRegular a) : IsRightRegular (a ^ n) := by
  rw [IsRightRegular]; rw [← mul_right_iterate]
  exact rra.iterate n

/--
lemma `IsRegular.pow` / 引理 `IsRegular.pow`

English:
lemma IsRegular.pow
  given: (n : Nat) (ra : IsRegular a)
  statement: IsRegular (a ^ n)
  proof: ⟨IsLeftRegular.pow n ra.left, IsRightRegular.pow n ra.right⟩

中文:
引理 是正则.pow
  条件: (n : 自然数) (ra : 是正则 a)
  结论: 是正则 (a ^ n)
  证明: ⟨IsLeftRegular.pow n ra.left, IsRightRegular.pow n ra.right⟩
-/
@[to_additive] lemma IsRegular.pow (n : Nat) (ra : IsRegular a) : IsRegular (a ^ n) :=
  ⟨IsLeftRegular.pow n ra.left, IsRightRegular.pow n ra.right⟩

/-- An element `a` is left-regular if and only if a positive power of `a` is left-regular. -/
@[to_additive]
/--
lemma `IsLeftRegular.pow_iff` / 引理 `IsLeftRegular.pow_iff`

English:
lemma IsLeftRegular.pow_iff
  given: (n0 : 0 < n)
  statement: IsLeftRegular (a ^ n) ↔ IsLeftRegular a where
  proof: by rw [← Nat.succ_pred_eq_of_pos n0, pow_succ]; exact .of_mul
  mpr := .pow n

中文:
引理 IsLeftRegular.pow_iff
  条件: (n0 : 0 < n)
  结论: IsLeftRegular (a ^ n) ↔ IsLeftRegular a where
  证明: by rw [← Nat.succ_pred_eq_of_pos n0, pow_succ]; exact .of_mul
  mpr := .pow n

Depends on / 依赖: Nat.succ_pred_eq_of_pos, of_mul, pow_succ, succ_pred_eq_of_pos
-/
lemma IsLeftRegular.pow_iff (n0 : 0 < n) : IsLeftRegular (a ^ n) ↔ IsLeftRegular a where
  mp := by rw [← Nat.succ_pred_eq_of_pos n0, pow_succ]; exact .of_mul
  mpr := .pow n

/-- An element `a` is right-regular if and only if a positive power of `a` is right-regular. -/
@[to_additive]
/--
lemma `IsRightRegular.pow_iff` / 引理 `IsRightRegular.pow_iff`

English:
lemma IsRightRegular.pow_iff
  given: (n0 : 0 < n)
  statement: IsRightRegular (a ^ n) ↔ IsRightRegular a where
  proof: by rw [← Nat.succ_pred_eq_of_pos n0, pow_succ']; exact .of_mul
  mpr := .pow n

中文:
引理 IsRightRegular.pow_iff
  条件: (n0 : 0 < n)
  结论: IsRightRegular (a ^ n) ↔ IsRightRegular a where
  证明: by rw [← Nat.succ_pred_eq_of_pos n0, pow_succ']; exact .of_mul
  mpr := .pow n

Depends on / 依赖: Nat.succ_pred_eq_of_pos, of_mul, pow_succ, succ_pred_eq_of_pos
-/
lemma IsRightRegular.pow_iff (n0 : 0 < n) : IsRightRegular (a ^ n) ↔ IsRightRegular a where
  mp := by rw [← Nat.succ_pred_eq_of_pos n0, pow_succ']; exact .of_mul
  mpr := .pow n

/--
lemma `IsRegular.pow_iff` / 引理 `IsRegular.pow_iff`

English:
lemma IsRegular.pow_iff
  given: {n : Nat} (n0 : 0 < n)
  statement: IsRegular (a ^ n) ↔ IsRegular a where
  proof: ⟨(IsLeftRegular.pow_iff n0).mp h.left, (IsRightRegular.pow_iff n0).mp h.right⟩
  mpr h := ⟨.pow n h.left, .pow n h.right⟩

中文:
引理 是正则.pow_iff
  条件: {n : 自然数} (n0 : 0 < n)
  结论: 是正则 (a ^ n) ↔ 是正则 a where
  证明: ⟨(IsLeftRegular.pow_iff n0).mp h.left, (IsRightRegular.pow_iff n0).mp h.right⟩
  mpr h := ⟨.pow n h.left, .pow n h.right⟩
-/
@[to_additive] lemma IsRegular.pow_iff {n : Nat} (n0 : 0 < n) : IsRegular (a ^ n) ↔ IsRegular a where
  mp h := ⟨(IsLeftRegular.pow_iff n0).mp h.left, (IsRightRegular.pow_iff n0).mp h.right⟩
  mpr h := ⟨.pow n h.left, .pow n h.right⟩

/--
lemma `IsLeftRegular.mul_left_eq_self_iff` / 引理 `IsLeftRegular.mul_left_eq_self_iff`

English:
lemma IsLeftRegular.mul_left_eq_self_iff
  given: (ha : IsLeftRegular a)
  proof: ⟨fun h => by rwa [← ha.eq_iff, mul_one], fun h => by rw [h, mul_one]⟩

中文:
引理 IsLeftRegular.mul_left_eq_self_iff
  条件: (ha : IsLeftRegular a)
  证明: ⟨fun h => by rwa [← ha.eq_iff, mul_one], fun h => by rw [h, mul_one]⟩
-/
@[to_additive (attr := simp)] lemma IsLeftRegular.mul_left_eq_self_iff (ha : IsLeftRegular a) :
    a * b = a ↔ b = 1 :=
  ⟨fun h => by rwa [← ha.eq_iff, mul_one], fun h => by rw [h, mul_one]⟩

/--
lemma `IsRightRegular.mul_right_eq_self_iff` / 引理 `IsRightRegular.mul_right_eq_self_iff`

English:
lemma IsRightRegular.mul_right_eq_self_iff
  given: (ha : IsRightRegular a)
  proof: ⟨fun h => by rwa [← ha.eq_iff, one_mul], fun h => by rw [h, one_mul]⟩

中文:
引理 IsRightRegular.mul_right_eq_self_iff
  条件: (ha : IsRightRegular a)
  证明: ⟨fun h => by rwa [← ha.eq_iff, one_mul], fun h => by rw [h, one_mul]⟩
-/
@[to_additive (attr := simp)] lemma IsRightRegular.mul_right_eq_self_iff (ha : IsRightRegular a) :
    b * a = a ↔ b = 1 :=
  ⟨fun h => by rwa [← ha.eq_iff, one_mul], fun h => by rw [h, one_mul]⟩

namespace IsDedekindFiniteMonoid

/--
lemma `iff_isLeftRegular_of_mul_eq_one` / 引理 `iff_isLeftRegular_of_mul_eq_one`

English:
lemma iff_isLeftRegular_of_mul_eq_one
  proof: isLeftRegular_of_mul_eq_one (mul_eq_one_symm eq)
mpr h := ⟨fun eq => h _ _ eq by simp [← mul_assoc, eq]⟩

中文:
引理 iff_isLeftRegular_of_mul_eq_one
  证明: isLeftRegular_of_mul_eq_one (mul_eq_one_symm eq)
mpr h := ⟨fun eq => h _ _ eq by simp [← mul_assoc, eq]⟩
-/
@[to_additive] lemma iff_isLeftRegular_of_mul_eq_one :
    IsDedekindFiniteMonoid R ↔ forall x y : R, x * y = 1 -> IsLeftRegular x where
  mp _ x y eq := isLeftRegular_of_mul_eq_one (mul_eq_one_symm eq)
mpr h := ⟨fun eq => h _ _ eq by simp [← mul_assoc, eq]⟩

/--
lemma `iff_isRightRegular_of_mul_eq_one` / 引理 `iff_isRightRegular_of_mul_eq_one`

English:
lemma iff_isRightRegular_of_mul_eq_one
  proof: isRightRegular_of_mul_eq_one (mul_eq_one_symm eq)
mpr h := ⟨fun eq => h _ _ eq by simp [mul_assoc, eq]⟩

中文:
引理 iff_isRightRegular_of_mul_eq_one
  证明: isRightRegular_of_mul_eq_one (mul_eq_one_symm eq)
mpr h := ⟨fun eq => h _ _ eq by simp [mul_assoc, eq]⟩
-/
@[to_additive] lemma iff_isRightRegular_of_mul_eq_one :
    IsDedekindFiniteMonoid R ↔ forall x y : R, x * y = 1 -> IsRightRegular y where
  mp _ x y eq := isRightRegular_of_mul_eq_one (mul_eq_one_symm eq)
mpr h := ⟨fun eq => h _ _ eq by simp [mul_assoc, eq]⟩

end IsDedekindFiniteMonoid

end Monoid
