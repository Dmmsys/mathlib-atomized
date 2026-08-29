/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
-- Some proofs and docs came from mathlib3 `src/algebra/commute.lean` (c) Neil Strickland
module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Order.Defs.Unbundled

/-!
# Semiconjugate elements of a semigroup

## Main definitions

We say that `x` is semiconjugate to `y` by `a` (`SemiconjBy a x y`), if `a * x = y * a`.
In this file we provide operations on `SemiconjBy _ _ _`.

In the names of these operations, we treat `a` as the “left” argument, and both `x` and `y` as
“right” arguments. This way most names in this file agree with the names of the corresponding lemmas
for `Commute a b = SemiconjBy a b b`. As a side effect, some lemmas have only `_right` version.

Lean does not immediately recognise these terms as equations, so for rewriting we need syntax like
`rw [(h.pow_right 5).eq]` rather than just `rw [h.pow_right 5]`.

This file provides only basic operations (`mul_left`, `mul_right`, `inv_right` etc). Other
operations (`pow_right`, field inverse etc) are in the files that define corresponding notions.
-/

@[expose] public section

assert_not_exists MonoidWithZero DenselyOrdered

variable {S M G : Type*}

/-- `x` is semiconjugate to `y` by `a`, if `a * x = y * a`. -/
@[to_additive /-- `x` is additive semiconjugate to `y` by `a` if `a + x = y + a` -/]
/--
Definition of `SemiconjBy` / `SemiconjBy` 的定义

English:
definition SemiconjBy
  signature: [Mul M] (a x y : M)
  body: a * x = y * a

中文:
定义 SemiconjBy
  签名: [乘法 M] (a x y : M)
  定义体: a * x = y * a
-/
def SemiconjBy [Mul M] (a x y : M) : Prop :=
  a * x = y * a

namespace SemiconjBy

/-- Equality behind `SemiconjBy a x y`; useful for rewriting. -/
@[to_additive /-- Equality behind `AddSemiconjBy a x y`; useful for rewriting. -/]
/--
theorem `eq` / 定理 `eq`

English:
theorem eq
  given: [Mul S] {a x y : S} (h : SemiconjBy a x y)
  statement: a * x = y * a
  proof: h

中文:
定理 eq
  条件: [乘法 S] {a x y : S} (h : SemiconjBy a x y)
  结论: a * x = y * a
  证明: h
-/
protected theorem eq [Mul S] {a x y : S} (h : SemiconjBy a x y) : a * x = y * a :=
  h

section Semigroup

variable [Semigroup S] {a b x y z x' y' : S}

/-- If `a` semiconjugates `x` to `y` and `x'` to `y'`,
then it semiconjugates `x * x'` to `y * y'`. -/
@[to_additive (attr := simp) /-- If `a` semiconjugates `x` to `y` and `x'` to `y'`,
then it semiconjugates `x + x'` to `y + y'`. -/]
/--
theorem `mul_right` / 定理 `mul_right`

English:
theorem mul_right
  given: (h : SemiconjBy a x y) (h' : SemiconjBy a x' y')
  proof: by
  unfold SemiconjBy
  -- TODO this could be done using `assoc_rw` if/when this is ported to mathlib4
  rw [← mul_assoc]; rw [h.eq]; rw [mul_assoc]; rw [h'.eq]; rw [← mul_assoc]

中文:
定理 mul_right
  条件: (h : SemiconjBy a x y) (h' : SemiconjBy a x' y')
  证明: by
  unfold SemiconjBy
  -- TODO this could be done using `assoc_rw` if/when this is ported to mathlib4
  rw [← mul_assoc]; rw [h.eq]; rw [mul_assoc]; rw [h'.eq]; rw [← mul_assoc]

Depends on / 依赖: SemiconjBy
-/
theorem mul_right (h : SemiconjBy a x y) (h' : SemiconjBy a x' y') :
    SemiconjBy a (x * x') (y * y') := by
  unfold SemiconjBy
  -- TODO this could be done using `assoc_rw` if/when this is ported to mathlib4
  rw [← mul_assoc]; rw [h.eq]; rw [mul_assoc]; rw [h'.eq]; rw [← mul_assoc]

/-- If `b` semiconjugates `x` to `y` and `a` semiconjugates `y` to `z`, then `a * b`
semiconjugates `x` to `z`. -/
@[to_additive /-- If `b` semiconjugates `x` to `y` and `a` semiconjugates `y` to `z`, then `a + b`
semiconjugates `x` to `z`. -/]
/--
theorem `mul_left` / 定理 `mul_left`

English:
theorem mul_left
  given: (ha : SemiconjBy a y z) (hb : SemiconjBy b x y)
  statement: SemiconjBy (a * b) x z
  proof: by
  unfold SemiconjBy
  rw [mul_assoc]; rw [hb.eq]; rw [← mul_assoc]; rw [ha.eq]; rw [mul_assoc]

中文:
定理 mul_left
  条件: (ha : SemiconjBy a y z) (hb : SemiconjBy b x y)
  结论: SemiconjBy (a * b) x z
  证明: by
  unfold SemiconjBy
  rw [mul_assoc]; rw [hb.eq]; rw [← mul_assoc]; rw [ha.eq]; rw [mul_assoc]

Depends on / 依赖: SemiconjBy, ha.eq, hb.eq, mul_assoc
-/
theorem mul_left (ha : SemiconjBy a y z) (hb : SemiconjBy b x y) : SemiconjBy (a * b) x z := by
  unfold SemiconjBy
  rw [mul_assoc]; rw [hb.eq]; rw [← mul_assoc]; rw [ha.eq]; rw [mul_assoc]

/-- The relation “there exists an element that semiconjugates `a` to `b`” on a semigroup
is transitive. -/
@[to_additive /-- The relation “there exists an element that semiconjugates `a` to `b`” on an
additive semigroup is transitive. -/]
/--
theorem `isTrans` / 定理 `isTrans`

English:
theorem isTrans
  statement: IsTrans S fun a b => exists c, SemiconjBy c a b
  proof: ⟨fun _ _ _ ⟨x, hx⟩ ⟨y, hy⟩ => ⟨y * x, hy.mul_left hx⟩⟩

@[deprecated (since := "2026-02-20")]
protected alias _root_.AddSemiconjBy.transitive := AddSemiconjBy.isTrans
@[to_additive existing, deprecated (since := "2026-02-20")]
protected alias transitive := SemiconjBy.isTrans

中文:
定理 isTrans
  结论: 是Trans S fun a b => 存在 c, SemiconjBy c a b
  证明: ⟨fun _ _ _ ⟨x, hx⟩ ⟨y, hy⟩ => ⟨y * x, hy.mul_left hx⟩⟩

@[deprecated (since := "2026-02-20")]
protected alias _root_.AddSemiconjBy.transitive := AddSemiconjBy.isTrans
@[to_additive existing, deprecated (since := "2026-02-20")]
protected alias transitive := SemiconjBy.isTrans
-/
protected theorem isTrans : IsTrans S fun a b => exists c, SemiconjBy c a b :=
  ⟨fun _ _ _ ⟨x, hx⟩ ⟨y, hy⟩ => ⟨y * x, hy.mul_left hx⟩⟩

@[deprecated (since := "2026-02-20")]
protected alias _root_.AddSemiconjBy.transitive := AddSemiconjBy.isTrans
@[to_additive existing, deprecated (since := "2026-02-20")]
protected alias transitive := SemiconjBy.isTrans

end Semigroup

section MulOneClass

variable [MulOneClass M]

/-- Any element semiconjugates `1` to `1`. -/
@[to_additive (attr := simp) /-- Any element semiconjugates `0` to `0`. -/]
/--
theorem `one_right` / 定理 `one_right`

English:
theorem one_right
  given: (a : M)
  statement: SemiconjBy a 1 1
  proof: by rw [SemiconjBy, mul_one, one_mul]

中文:
定理 one_right
  条件: (a : M)
  结论: SemiconjBy a 1 1
  证明: by rw [SemiconjBy, mul_one, one_mul]

Depends on / 依赖: SemiconjBy, mul_one, one_mul
-/
theorem one_right (a : M) : SemiconjBy a 1 1 := by rw [SemiconjBy, mul_one, one_mul]

/-- One semiconjugates any element to itself. -/
@[to_additive (attr := simp) /-- Zero semiconjugates any element to itself. -/]
/--
theorem `one_left` / 定理 `one_left`

English:
theorem one_left
  given: (x : M)
  statement: SemiconjBy 1 x x
  proof: Eq.symm one_right x

中文:
定理 one_left
  条件: (x : M)
  结论: SemiconjBy 1 x x
  证明: Eq.symm one_right x

Depends on / 依赖: Eq.symm, one_right
-/
theorem one_left (x : M) : SemiconjBy 1 x x :=
Eq.symm one_right x

/-- The relation “there exists an element that semiconjugates `a` to `b`” on a monoid (or, more
generally, on `MulOneClass` type) is reflexive. -/
@[to_additive /-- The relation “there exists an element that semiconjugates `a` to `b`” on an
additive monoid (or, more generally, on an `AddZeroClass` type) is reflexive. -/]
/--
theorem `refl` / 定理 `refl`

English:
theorem refl
  statement: Std.Refl fun a b : M => exists c, SemiconjBy c a b where
  proof: ⟨1, one_left a⟩

@[deprecated (since := "2026-03-27")] protected alias reflexive := SemiconjBy.refl

中文:
定理 refl
  结论: Std.Refl fun a b : M => 存在 c, SemiconjBy c a b where
  证明: ⟨1, one_left a⟩

@[deprecated (since := "2026-03-27")] protected alias reflexive := SemiconjBy.refl
-/
protected theorem refl : Std.Refl fun a b : M => exists c, SemiconjBy c a b where
  refl a := ⟨1, one_left a⟩

@[deprecated (since := "2026-03-27")] protected alias reflexive := SemiconjBy.refl

end MulOneClass

section Monoid

variable [Monoid M]

@[to_additive (attr := simp)]
/--
theorem `pow_right` / 定理 `pow_right`

English:
theorem pow_right
  given: {a x y : M} (h : SemiconjBy a x y) (n : Nat)
  statement: SemiconjBy a (x ^ n) (y ^ n)
  proof: by
  induction n with
  | zero =>
    rw [pow_zero]; rw [pow_zero]
    exact SemiconjBy.one_right _
  | succ n ih =>
    rw [pow_succ]; rw [pow_succ]
    exact ih.mul_right h

中文:
定理 pow_right
  条件: {a x y : M} (h : SemiconjBy a x y) (n : 自然数)
  结论: SemiconjBy a (x ^ n) (y ^ n)
  证明: by
  induction n with
  | zero =>
    rw [pow_zero]; rw [pow_zero]
    exact SemiconjBy.one_right _
  | succ n ih =>
    rw [pow_succ]; rw [pow_succ]
    exact ih.mul_right h

Depends on / 依赖: SemiconjBy, SemiconjBy.one_right, ih.mul_right, mul_right, one_right, pow_succ, pow_zero
-/
theorem pow_right {a x y : M} (h : SemiconjBy a x y) (n : Nat) : SemiconjBy a (x ^ n) (y ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero]; rw [pow_zero]
    exact SemiconjBy.one_right _
  | succ n ih =>
    rw [pow_succ]; rw [pow_succ]
    exact ih.mul_right h

end Monoid

section Group

variable [Group G]

/-- `a` semiconjugates `x` to `a * x * a⁻¹`. -/
@[to_additive /-- `a` semiconjugates `x` to `a + x + -a`. -/]
/--
theorem `conj_mk` / 定理 `conj_mk`

English:
theorem conj_mk
  given: (a x : G)
  statement: SemiconjBy a x (a * x * a⁻¹)
  proof: by
  unfold SemiconjBy; rw [mul_assoc, inv_mul_cancel, mul_one]

@[to_additive (attr := simp)]

中文:
定理 conj_mk
  条件: (a x : G)
  结论: SemiconjBy a x (a * x * a⁻¹)
  证明: by
  unfold SemiconjBy; rw [mul_assoc, inv_mul_cancel, mul_one]

@[to_additive (attr := simp)]

Depends on / 依赖: SemiconjBy, inv_mul_cancel, mul_assoc, mul_one
-/
theorem conj_mk (a x : G) : SemiconjBy a x (a * x * a⁻¹) := by
  unfold SemiconjBy; rw [mul_assoc, inv_mul_cancel, mul_one]

@[to_additive (attr := simp)]
/--
theorem `conj_iff` / 定理 `conj_iff`

English:
theorem conj_iff
  given: {a x y b : G}
  proof: by
  unfold SemiconjBy
  simp only [← mul_assoc, inv_mul_cancel_right]
  repeat rw [mul_assoc]
  rw [mul_left_cancel_iff]; rw [← mul_assoc]; rw [← mul_assoc]; rw [mul_right_cancel_iff]

中文:
定理 conj_iff
  条件: {a x y b : G}
  证明: by
  unfold SemiconjBy
  simp only [← mul_assoc, inv_mul_cancel_right]
  repeat rw [mul_assoc]
  rw [mul_left_cancel_iff]; rw [← mul_assoc]; rw [← mul_assoc]; rw [mul_right_cancel_iff]

Depends on / 依赖: SemiconjBy, inv_mul_cancel_right, mul_assoc, mul_left_cancel_iff, mul_right_cancel_iff, repeat
-/
theorem conj_iff {a x y b : G} :
    SemiconjBy (b * a * b⁻¹) (b * x * b⁻¹) (b * y * b⁻¹) ↔ SemiconjBy a x y := by
  unfold SemiconjBy
  simp only [← mul_assoc, inv_mul_cancel_right]
  repeat rw [mul_assoc]
  rw [mul_left_cancel_iff]; rw [← mul_assoc]; rw [← mul_assoc]; rw [mul_right_cancel_iff]

end Group

end SemiconjBy

@[to_additive (attr := simp)]
/--
theorem `semiconjBy_iff_eq` / 定理 `semiconjBy_iff_eq`

English:
theorem semiconjBy_iff_eq
  given: [CancelCommMonoid M] {a x y : M}
  statement: SemiconjBy a x y ↔ x = y
  proof: ⟨fun h => mul_left_cancel (h.trans (mul_comm _ _)), fun h => by rw [h, SemiconjBy, mul_comm]⟩

中文:
定理 semiconjBy_iff_eq
  条件: [消去交换幺半群 M] {a x y : M}
  结论: SemiconjBy a x y ↔ x = y
  证明: ⟨fun h => mul_left_cancel (h.trans (mul_comm _ _)), fun h => by rw [h, SemiconjBy, mul_comm]⟩

Depends on / 依赖: SemiconjBy, h.trans, mul_comm, mul_left_cancel
-/
theorem semiconjBy_iff_eq [CancelCommMonoid M] {a x y : M} : SemiconjBy a x y ↔ x = y :=
  ⟨fun h => mul_left_cancel (h.trans (mul_comm _ _)), fun h => by rw [h, SemiconjBy, mul_comm]⟩
