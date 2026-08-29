/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.RingQuot
public import Mathlib.Algebra.Star.Basic

/-!
# The \*-ring structure on suitable quotients of a \*-ring.
-/

public section

namespace RingQuot

universe u

variable {R : Type u} [Semiring R] (r : R -> R -> Prop)

section StarRing

variable [StarRing R]

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
theorem `Rel.star` / 定理 `Rel.star`

English:
theorem Rel.star
  statement: (hr : forall a b, r a b -> r (star a) (star b))
  proof: by
  induction h with
  | of h => exact Rel.of (hr _ _ h)
  | add_left _ h => rw [star_add, star_add]
                     exact Rel.add_left h
  | mul_left _ h => rw [star_mul, star_mul]
                     exact Rel.mul_right h
  | mul_right _ h => rw [star_mul, star_mul]
                     exact Rel.mul_left h

中文:
定理 关系.star
  结论: (hr : 对任意 a b, r a b -> r (star a) (star b))
  证明: by
  induction h with
  | of h => exact Rel.of (hr _ _ h)
  | add_left _ h => rw [star_add, star_add]
                     exact Rel.add_left h
  | mul_left _ h => rw [star_mul, star_mul]
                     exact Rel.mul_right h
  | mul_right _ h => rw [star_mul, star_mul]
                     exact Rel.mul_left h

Depends on / 依赖: Rel.add_left, Rel.mul_left, Rel.mul_right, Rel.of, add_left, mul_left, mul_right, star_add, star_mul
-/
theorem Rel.star (hr : forall a b, r a b -> r (star a) (star b))
    ⦃a b : R⦄ (h : Rel r a b) : Rel r (star a) (star b) := by
  induction h with
  | of h => exact Rel.of (hr _ _ h)
  | add_left _ h => rw [star_add, star_add]
                     exact Rel.add_left h
  | mul_left _ h => rw [star_mul, star_mul]
                     exact Rel.mul_right h
  | mul_right _ h => rw [star_mul, star_mul]
                     exact Rel.mul_left h

/--
Definition of `star'` / `star'` 的定义

English:
definition star'
  signature: (hr : forall a b, r a b -> r (star a) (star b))

中文:
定义 star'
  签名: (hr : 对任意 a b, r a b -> r (star a) (star b))
-/
private def star' (hr : forall a b, r a b -> r (star a) (star b)) : RingQuot r -> RingQuot r
  | ⟨a⟩ => ⟨Quot.map (star : R -> R) (Rel.star r hr) a⟩

/--
theorem `star'_quot` / 定理 `star'_quot`

English:
theorem star'_quot
  given: (hr : forall a b, r a b -> r (star a) (star b)) {a}
  proof: rfl

中文:
定理 star'_quot
  条件: (hr : 对任意 a b, r a b -> r (star a) (star b)) {a}
  证明: rfl
-/
private theorem star'_quot (hr : forall a b, r a b -> r (star a) (star b)) {a} :
    (star' r hr ⟨Quot.mk _ a⟩ : RingQuot r) = ⟨Quot.mk _ (star a)⟩ := rfl

/-- Transfer a `StarRing` instance through a quotient, if the quotient is invariant to `star` -/
@[instance_reducible]
/--
Definition of `starRing` / `starRing` 的定义

English:
definition starRing
  signature: {R : Type u} [Semiring R] [StarRing R] (r : R -> R -> Prop)
  body: star' r hr
  star_involutive := by
    rintro ⟨⟨⟩⟩
    simp [star'_quot]
  star_mul := by
    rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩
    simp [star'_quot, mul_quot, star_mul]
  star_add := by
    rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩
    simp [star'_quot, add_quot, star_add]

中文:
定义 starRing
  签名: {R : 类型u} [半环 R] [对合环 R] (r : R -> R -> 命题)
  定义体: star' r hr
  star_involutive := by
    rintro ⟨⟨⟩⟩
    simp [star'_quot]
  star_mul := by
    rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩
    simp [star'_quot, mul_quot, star_mul]
  star_add := by
    rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩
    simp [star'_quot, add_quot, star_add]
-/
def starRing {R : Type u} [Semiring R] [StarRing R] (r : R -> R -> Prop)
    (hr : forall a b, r a b -> r (star a) (star b)) : StarRing (RingQuot r) where
  star := star' r hr
  star_involutive := by
    rintro ⟨⟨⟩⟩
    simp [star'_quot]
  star_mul := by
    rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩
    simp [star'_quot, mul_quot, star_mul]
  star_add := by
    rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩
    simp [star'_quot, add_quot, star_add]

end StarRing

end RingQuot
