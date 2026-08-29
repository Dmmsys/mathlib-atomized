/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.RingTheory.Congruence.Basic
public import Mathlib.Algebra.Star.Basic

/-!
# Helpers for working with star operators on quotients.

TODO: consider defining `Star` versions of `RingCon`.
-/

@[expose] public section

section Ring
variable {R : Type*} [NonUnitalNonAssocSemiring R] [StarRing R] {r : R -> R -> Prop}

/--
theorem `RingConGen.Rel.star` / 定理 `RingConGen.Rel.star`

English:
theorem RingConGen.Rel.star
  statement: (hr : forall a b, r a b -> r (star a) (star b))

中文:
定理 RingConGen.Rel.star
  结论: (hr : 对任意 a b, r a b -> r (star a) (star b))
-/
theorem RingConGen.Rel.star (hr : forall a b, r a b -> r (star a) (star b))
    ⦃a b : R⦄ : Rel r a b -> Rel r (star a) (star b)
  | refl _ => .refl _
| symm h => .symm h.star hr
  | trans h1 h2 => .trans (h1.star hr) (h2.star hr)
  | of _ _ h => .of _ _ (hr _ _ h)
  | mul h1 h2 => by
    rw [star_mul]; rw [star_mul]
    exact (h2.star hr).mul (h1.star hr)
  | add h1 h2 => by
    rw [star_add]; rw [star_add]
    exact (h1.star hr).add (h2.star hr)

/--
theorem `ringConGen_star` / 定理 `ringConGen_star`

English:
theorem ringConGen_star
  given: (hr : forall a b, r a b -> r (star a) (star b)) ⦃a b
  statement: R⦄ :
  proof: (RingConGen.Rel.star hr ·)

中文:
定理 ringConGen_star
  条件: (hr : 对任意 a b, r a b -> r (star a) (star b)) ⦃a b
  结论: R⦄ :
  证明: (RingConGen.Rel.star hr ·)

Depends on / 依赖: RingConGen, RingConGen.Rel.star
-/
theorem ringConGen_star (hr : forall a b, r a b -> r (star a) (star b)) ⦃a b : R⦄ :
    ringConGen r a b -> ringConGen r (star a) (star b) := (RingConGen.Rel.star hr ·)

end Ring
