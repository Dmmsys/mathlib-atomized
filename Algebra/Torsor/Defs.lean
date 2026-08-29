/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Action.Defs

/-!
# Torsors of group actions

This file defines torsors of additive and multiplicative group actions.

## Notation

The group elements are referred to as acting on points. This file
uses the notation `+ᵥ` for adding a group element to a point and
`-ᵥ` for subtracting two points to produce a group element, as well as `•` and `/ₛ` for the
corresponding operations in multiplicative torsors.

## Implementation notes

Affine spaces are a motivating example of additive torsors. Additional simply transitive
actions which give rise to torsors include the action of the Weyl group on Weyl chambers, the
action of non-zero scalars on the non-vanishing elements of the top exterior power of a
finite-dimensional vector space, the action of the general linear group of a vector space on the
bases of that space, and the monodromy action of the fundamental group of a space on a fibre of its
universal cover. Both the additive and multiplicative notation will be useful to formalise
such examples.

## Notation

* `v +ᵥ p` is a notation for `VAdd.vadd`, the left action of an additive monoid;
* `p₁ -ᵥ p₂` is a notation for `VSub.vsub`, the difference between two points in an additive torsor
  as an element of the corresponding additive group;
* `v • p` is a notation for `SMul.smul`, the left action of a multiplicative monoid;
* `p₁ /ₛ p₂` is a notation for `SDiv.sdiv`, the quotient of two points in a multiplicative
  torsor as an element of the corresponding multiplicative group;

## References

* https://en.wikipedia.org/wiki/Principal_homogeneous_space
* https://en.wikipedia.org/wiki/Affine_space

-/

@[expose] public section

assert_not_exists MonoidWithZero

/--
Definition of `AddTorsor` / `AddTorsor` 的定义

English:
class AddTorsor
  parameters: (G : outParam Type*) (P : Type*) [AddGroup G]
  extends: AddAction G P, 
  axioms and operations (3):
    - [nonempty : Nonempty P]
    - vsub_vadd' : forall p₁ p₂ : P, (p₁ -ᵥ p₂ : G) +ᵥ p₂ = p₁
    - vadd_vsub' : forall (g : G) (p : P), (g +ᵥ p) -ᵥ p = g

中文:
类 加法Torsor
  参数: (G : outParam 类型) (P : 类型) [加法群 G]
  继承: 加法作用 G P, 
  公理与运算 (3 个):
    - [nonempty : 非空 P]
    - vsub_vadd' : 对任意 p₁ p₂ : P, (p₁ -ᵥ p₂ : G) +ᵥ p₂ = p₁
    - vadd_vsub' : 对任意 (g : G) (p : P), (g +ᵥ p) -ᵥ p = g
-/
class AddTorsor (G : outParam Type*) (P : Type*) [AddGroup G] extends AddAction G P,
  VSub G P where
  [nonempty : Nonempty P]
  /-- Torsor subtraction and addition with the same element cancels out. -/
  vsub_vadd' : forall p₁ p₂ : P, (p₁ -ᵥ p₂ : G) +ᵥ p₂ = p₁
  /-- Torsor addition and subtraction with the same element cancels out. -/
  vadd_vsub' : forall (g : G) (p : P), (g +ᵥ p) -ᵥ p = g

/-- A `Torsor G P` gives a structure to the nonempty type `P`,
acted on by a `Group G` with a transitive and free action given
by the `•` operation and a corresponding division given by the
`/ₛ` operation. -/
@[to_additive existing]
/--
Definition of `Torsor` / `Torsor` 的定义

English:
class Torsor
  parameters: (G : outParam Type*) (P : Type*) [Group G]
  extends: MulAction G P, SDiv G P
  axioms and operations (3):
    - [nonempty : Nonempty P]
    - sdiv_smul' : forall p₁ p₂ : P, (p₁ /ₛ p₂ : G) • p₂ = p₁
    - smul_sdiv' : forall (g : G) (p : P), (g • p) /ₛ p = g

中文:
类 Torsor
  参数: (G : outParam 类型) (P : 类型) [群 G]
  继承: 乘法作用 G P, SDiv G P
  公理与运算 (3 个):
    - [nonempty : 非空 P]
    - sdiv_smul' : 对任意 p₁ p₂ : P, (p₁ /ₛ p₂ : G) • p₂ = p₁
    - smul_sdiv' : 对任意 (g : G) (p : P), (g • p) /ₛ p = g
-/
class Torsor (G : outParam Type*) (P : Type*) [Group G] extends MulAction G P, SDiv G P where
  [nonempty : Nonempty P]
  /-- Scalar division and multiplication with the same element cancels out. -/
  sdiv_smul' : forall p₁ p₂ : P, (p₁ /ₛ p₂ : G) • p₂ = p₁
  /-- Scalar multiplication and division with the same element cancels out. -/
  smul_sdiv' : forall (g : G) (p : P), (g • p) /ₛ p = g

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/12096): removed `nolint instance_priority`; lint not ported yet
attribute [instance 100] AddTorsor.nonempty
attribute [instance 100] Torsor.nonempty

/-- A `Group G` is a torsor for itself. -/
-- Porting note (https://github.com/leanprover-community/mathlib4/issues/12096): linter not ported yet
--@[nolint instance_priority]
@[to_additive /-- An `AddGroup G` is a torsor for itself.-/]
/--
Instance `Group.instTorsor` / 实例 `Group.instTorsor`

English:
instance Group.instTorsor
  signature: (G : Type*) [Group G]
  body: Div.div
  sdiv_smul' := div_mul_cancel
  smul_sdiv' := mul_div_cancel_right

@[deprecated (since := "2026-05-04")] alias addGroupIsAddTorsor := AddGroup.instAddTorsor

中文:
实例 群.instTorsor
  签名: (G : 类型) [群 G]
  定义体: Div.div
  sdiv_smul' := div_mul_cancel
  smul_sdiv' := mul_div_cancel_right

@[deprecated (since := "2026-05-04")] alias addGroupIsAddTorsor := AddGroup.instAddTorsor

Depends on / 依赖: Div.div
-/
instance Group.instTorsor (G : Type*) [Group G] : Torsor G G where
  sdiv := Div.div
  sdiv_smul' := div_mul_cancel
  smul_sdiv' := mul_div_cancel_right

@[deprecated (since := "2026-05-04")] alias addGroupIsAddTorsor := AddGroup.instAddTorsor

/-- Simplify division for a torsor for a `Group G` over itself. -/
@[to_additive (attr := simp) /-- Simplify subtraction for a torsor for an `AddGroup G` over
itself.-/]
/--
theorem `sdiv_eq_div` / 定理 `sdiv_eq_div`

English:
theorem sdiv_eq_div
  given: {G : Type*} [Group G] (g₁ g₂ : G)
  statement: g₁ /ₛ g₂ = g₁ / g₂
  proof: rfl

中文:
定理 sdiv_eq_div
  条件: {G : 类型} [群 G] (g₁ g₂ : G)
  结论: g₁ /ₛ g₂ = g₁ / g₂
  证明: rfl

Depends on / 依赖: IsClosedImmersion, IsPreimmersion, Scheme
-/
theorem sdiv_eq_div {G : Type*} [Group G] (g₁ g₂ : G) : g₁ /ₛ g₂ = g₁ / g₂ :=
  rfl

section General

variable {G : Type*} {P : Type*} [Group G] [T : Torsor G P]

/-- Scalar multiplying the result of dividing another point produces that point. -/
@[to_additive (attr := simp) /-- Adding the result of subtracting from another point produces that
point. -/]
/--
theorem `sdiv_smul` / 定理 `sdiv_smul`

English:
theorem sdiv_smul
  given: (p₁ p₂ : P)
  statement: (p₁ /ₛ p₂) • p₂ = p₁
  proof: Torsor.sdiv_smul' p₁ p₂

中文:
定理 sdiv_smul
  条件: (p₁ p₂ : P)
  结论: (p₁ /ₛ p₂) • p₂ = p₁
  证明: Torsor.sdiv_smul' p₁ p₂

Depends on / 依赖: Homeomorph, Homeomorph.isClosedEmbedding, TopCat, TopCat.homeoOfIso, Torsor, Torsor.sdiv_smul, f.base, homeoOfIso, isClosedEmbedding, sdiv_smul
-/
theorem sdiv_smul (p₁ p₂ : P) : (p₁ /ₛ p₂) • p₂ = p₁ :=
  Torsor.sdiv_smul' p₁ p₂

/-- Multiplying by a group element then dividing by the original point
produces that group element. -/
@[to_additive (attr := simp) /-- Adding a group element then subtracting the original point
produces that group element. -/]
/--
theorem `smul_sdiv` / 定理 `smul_sdiv`

English:
theorem smul_sdiv
  given: (g : G) (p : P)
  statement: (g • p) /ₛ p = g
  proof: Torsor.smul_sdiv' g p

中文:
定理 smul_sdiv
  条件: (g : G) (p : P)
  结论: (g • p) /ₛ p = g
  证明: Torsor.smul_sdiv' g p

Depends on / 依赖: IsClosedImmersion, IsEmpty, Scheme, Torsor, Torsor.smul_sdiv, smul_sdiv
-/
theorem smul_sdiv (g : G) (p : P) : (g • p) /ₛ p = g :=
  Torsor.smul_sdiv' g p

/-- If the same point multiplied with two group elements produces equal
results, those group elements are equal. -/
@[to_additive /-- If the same point added to two group elements produces equal
results, those group elements are equal. -/]
/--
theorem `smul_right_cancel` / 定理 `smul_right_cancel`

English:
theorem smul_right_cancel
  given: {g₁ g₂ : G} (p : P) (h : g₁ • p = g₂ • p)
  statement: g₁ = g₂
  proof: by
  rw [← smul_sdiv g₁ p]; rw [h]; rw [smul_sdiv]

@[to_additive (attr := simp)]

中文:
定理 smul_right_cancel
  条件: {g₁ g₂ : G} (p : P) (h : g₁ • p = g₂ • p)
  结论: g₁ = g₂
  证明: by
  rw [← smul_sdiv g₁ p]; rw [h]; rw [smul_sdiv]

@[to_additive (attr := simp)]

Depends on / 依赖: smul_sdiv
-/
theorem smul_right_cancel {g₁ g₂ : G} (p : P) (h : g₁ • p = g₂ • p) : g₁ = g₂ := by
  rw [← smul_sdiv g₁ p]; rw [h]; rw [smul_sdiv]

@[to_additive (attr := simp)]
/--
theorem `smul_right_cancel_iff` / 定理 `smul_right_cancel_iff`

English:
theorem smul_right_cancel_iff
  given: {g₁ g₂ : G} (p : P)
  statement: g₁ • p = g₂ • p ↔ g₁ = g₂
  proof: ⟨smul_right_cancel p, fun h => h ▸ rfl⟩

中文:
定理 smul_right_cancel_iff
  条件: {g₁ g₂ : G} (p : P)
  结论: g₁ • p = g₂ • p ↔ g₁ = g₂
  证明: ⟨smul_right_cancel p, fun h => h ▸ rfl⟩

Depends on / 依赖: smul_right_cancel
-/
theorem smul_right_cancel_iff {g₁ g₂ : G} (p : P) : g₁ • p = g₂ • p ↔ g₁ = g₂ :=
  ⟨smul_right_cancel p, fun h => h ▸ rfl⟩

/-- Multiplying a group element with the point `p` is an injective function. -/
@[to_additive vadd_right_injective /-- Adding a group element to the point `p` is an injective
function. -/]
/--
theorem `smul_right_injective'` / 定理 `smul_right_injective'`

English:
theorem smul_right_injective'
  given: (p : P)
  statement: Function.Injective ((· • p) : G -> P)
  proof: fun _ _ =>
  smul_right_cancel p

中文:
定理 smul_right_injective'
  条件: (p : P)
  结论: 函数.单射 ((· • p) : G -> P)
  证明: fun _ _ =>
  smul_right_cancel p
-/
theorem smul_right_injective' (p : P) : Function.Injective ((· • p) : G -> P) := fun _ _ =>
  smul_right_cancel p

/-- Multiplying a group element with a point, then dividing by another point,
produces the same result as dividing the points then multiplying the group element. -/
@[to_additive /-- Adding a group element to a point, then subtracting another point,
produces the same result as subtracting the points then adding the group element. -/]
/--
theorem `smul_sdiv_assoc` / 定理 `smul_sdiv_assoc`

English:
theorem smul_sdiv_assoc
  given: (g : G) (p₁ p₂ : P)
  statement: (g • p₁) /ₛ p₂ = g * (p₁ /ₛ p₂)
  proof: by
  apply smul_right_cancel p₂
  rw [sdiv_smul]; rw [mul_smul]; rw [sdiv_smul]

中文:
定理 smul_sdiv_assoc
  条件: (g : G) (p₁ p₂ : P)
  结论: (g • p₁) /ₛ p₂ = g * (p₁ /ₛ p₂)
  证明: by
  apply smul_right_cancel p₂
  rw [sdiv_smul]; rw [mul_smul]; rw [sdiv_smul]

Depends on / 依赖: I.range_subscheme, I.support.isClosed, isClosed, mul_smul, of_isPreimmersion, sdiv_smul, smul_right_cancel, support
-/
theorem smul_sdiv_assoc (g : G) (p₁ p₂ : P) : (g • p₁) /ₛ p₂ = g * (p₁ /ₛ p₂) := by
  apply smul_right_cancel p₂
  rw [sdiv_smul]; rw [mul_smul]; rw [sdiv_smul]

/-- Dividing a point by itself produces 1. -/
@[to_additive (attr := simp) /-- Subtracting a point from itself produces 0. -/]
/--
theorem `sdiv_self` / 定理 `sdiv_self`

English:
theorem sdiv_self
  given: (p : P)
  statement: p /ₛ p = (1 : G)
  proof: by
  rw [← one_mul (p /ₛ p)]; rw [← smul_sdiv_assoc]; rw [smul_sdiv]

中文:
定理 sdiv_self
  条件: (p : P)
  结论: p /ₛ p = (1 : G)
  证明: by
  rw [← one_mul (p /ₛ p)]; rw [← smul_sdiv_assoc]; rw [smul_sdiv]

Depends on / 依赖: one_mul, smul_sdiv, smul_sdiv_assoc
-/
theorem sdiv_self (p : P) : p /ₛ p = (1 : G) := by
  rw [← one_mul (p /ₛ p)]; rw [← smul_sdiv_assoc]; rw [smul_sdiv]

/-- If dividing two points produces 1, they are equal. -/
@[to_additive /-- If subtracting two points produces 0, they are equal. -/]
/--
theorem `eq_of_sdiv_eq_one` / 定理 `eq_of_sdiv_eq_one`

English:
theorem eq_of_sdiv_eq_one
  given: {p₁ p₂ : P} (h : p₁ /ₛ p₂ = (1 : G))
  statement: p₁ = p₂
  proof: by
  rw [← sdiv_smul p₁ p₂]; rw [h]; rw [one_smul]

中文:
定理 eq_of_sdiv_eq_one
  条件: {p₁ p₂ : P} (h : p₁ /ₛ p₂ = (1 : G))
  结论: p₁ = p₂
  证明: by
  rw [← sdiv_smul p₁ p₂]; rw [h]; rw [one_smul]

Depends on / 依赖: one_smul, sdiv_smul
-/
theorem eq_of_sdiv_eq_one {p₁ p₂ : P} (h : p₁ /ₛ p₂ = (1 : G)) : p₁ = p₂ := by
  rw [← sdiv_smul p₁ p₂]; rw [h]; rw [one_smul]

/-- Dividing two points produces 1 if and only if they are equal. -/
@[to_additive (attr := simp) /-- Subtracting two points produces 0 if and only if they are
equal. -/]
/--
theorem `sdiv_eq_one_iff_eq` / 定理 `sdiv_eq_one_iff_eq`

English:
theorem sdiv_eq_one_iff_eq
  given: {p₁ p₂ : P}
  statement: p₁ /ₛ p₂ = (1 : G) ↔ p₁ = p₂
  proof: Iff.intro eq_of_sdiv_eq_one fun h => h ▸ sdiv_self _

@[to_additive]

中文:
定理 sdiv_eq_one_iff_eq
  条件: {p₁ p₂ : P}
  结论: p₁ /ₛ p₂ = (1 : G) ↔ p₁ = p₂
  证明: Iff.intro eq_of_sdiv_eq_one fun h => h ▸ sdiv_self _

@[to_additive]

Depends on / 依赖: Iff.intro, eq_of_sdiv_eq_one, sdiv_self
-/
theorem sdiv_eq_one_iff_eq {p₁ p₂ : P} : p₁ /ₛ p₂ = (1 : G) ↔ p₁ = p₂ :=
  Iff.intro eq_of_sdiv_eq_one fun h => h ▸ sdiv_self _

@[to_additive]
/--
theorem `sdiv_ne_one` / 定理 `sdiv_ne_one`

English:
theorem sdiv_ne_one
  given: {p q : P}
  statement: p /ₛ q != (1 : G) ↔ p != q
  proof: not_congr sdiv_eq_one_iff_eq

中文:
定理 sdiv_ne_one
  条件: {p q : P}
  结论: p /ₛ q != (1 : G) ↔ p != q
  证明: not_congr sdiv_eq_one_iff_eq

Depends on / 依赖: not_congr, sdiv_eq_one_iff_eq
-/
theorem sdiv_ne_one {p q : P} : p /ₛ q != (1 : G) ↔ p != q :=
  not_congr sdiv_eq_one_iff_eq

/-- Cancellation multiplying the results of two divisions. -/
@[to_additive (attr := simp) /-- Cancellation adding the results of two subtractions. -/]
/--
theorem `sdiv_mul_sdiv_cancel` / 定理 `sdiv_mul_sdiv_cancel`

English:
theorem sdiv_mul_sdiv_cancel
  given: (p₁ p₂ p₃ : P)
  statement: (p₁ /ₛ p₂) * (p₂ /ₛ p₃) = p₁ /ₛ p₃
  proof: by
  apply smul_right_cancel p₃
  rw [mul_smul]; rw [sdiv_smul]; rw [sdiv_smul]; rw [sdiv_smul]

中文:
定理 sdiv_mul_sdiv_cancel
  条件: (p₁ p₂ p₃ : P)
  结论: (p₁ /ₛ p₂) * (p₂ /ₛ p₃) = p₁ /ₛ p₃
  证明: by
  apply smul_right_cancel p₃
  rw [mul_smul]; rw [sdiv_smul]; rw [sdiv_smul]; rw [sdiv_smul]

Depends on / 依赖: mul_smul, sdiv_smul, smul_right_cancel
-/
theorem sdiv_mul_sdiv_cancel (p₁ p₂ p₃ : P) : (p₁ /ₛ p₂) * (p₂ /ₛ p₃) = p₁ /ₛ p₃ := by
  apply smul_right_cancel p₃
  rw [mul_smul]; rw [sdiv_smul]; rw [sdiv_smul]; rw [sdiv_smul]

/-- Dividing two points in the reverse order produces the inverse of dividing them. -/
@[to_additive (attr := simp) /-- Subtracting two points in the reverse order produces the negation
of subtracting them. -/]
/--
theorem `inv_sdiv_eq_sdiv_rev` / 定理 `inv_sdiv_eq_sdiv_rev`

English:
theorem inv_sdiv_eq_sdiv_rev
  given: (p₁ p₂ : P)
  statement: (p₁ /ₛ p₂)⁻¹ = p₂ /ₛ p₁
  proof: by
  refine inv_eq_of_mul_eq_one_right (smul_right_cancel p₁ ?_)
  rw [sdiv_mul_sdiv_cancel]; rw [sdiv_self]

@[to_additive]

中文:
定理 inv_sdiv_eq_sdiv_rev
  条件: (p₁ p₂ : P)
  结论: (p₁ /ₛ p₂)⁻¹ = p₂ /ₛ p₁
  证明: by
  refine inv_eq_of_mul_eq_one_right (smul_right_cancel p₁ ?_)
  rw [sdiv_mul_sdiv_cancel]; rw [sdiv_self]

@[to_additive]

Depends on / 依赖: IsAffineHom, IsClosedImmersion, Scheme, inv_eq_of_mul_eq_one_right, sdiv_mul_sdiv_cancel, sdiv_self, smul_right_cancel
-/
theorem inv_sdiv_eq_sdiv_rev (p₁ p₂ : P) : (p₁ /ₛ p₂)⁻¹ = p₂ /ₛ p₁ := by
  refine inv_eq_of_mul_eq_one_right (smul_right_cancel p₁ ?_)
  rw [sdiv_mul_sdiv_cancel]; rw [sdiv_self]

@[to_additive]
/--
theorem `smul_sdiv_eq_div_sdiv` / 定理 `smul_sdiv_eq_div_sdiv`

English:
theorem smul_sdiv_eq_div_sdiv
  given: (g : G) (p q : P)
  statement: (g • p) /ₛ q = g / (q /ₛ p)
  proof: by
  rw [smul_sdiv_assoc]; rw [div_eq_mul_inv]; rw [inv_sdiv_eq_sdiv_rev]

中文:
定理 smul_sdiv_eq_div_sdiv
  条件: (g : G) (p q : P)
  结论: (g • p) /ₛ q = g / (q /ₛ p)
  证明: by
  rw [smul_sdiv_assoc]; rw [div_eq_mul_inv]; rw [inv_sdiv_eq_sdiv_rev]

Depends on / 依赖: IsHomeomorph, Scheme, Scheme.Hom.toImage_image, Set.range_eq_univ, TopCat, TopCat.isoOfHomeo, closure_eq, denseRange, div_eq_mul_inv, f.image, f.toImage, f.toImage.denseRange.closure_eq, f.toImage.isClosedEmbedding.isClosed_range.closure_eq, f.toImage.isEmbedding, homeomorph, infer_instance, inv_sdiv_eq_sdiv_rev, isClosedEmbedding, isClosed_range, isEmbedding
-/
theorem smul_sdiv_eq_div_sdiv (g : G) (p q : P) : (g • p) /ₛ q = g / (q /ₛ p) := by
  rw [smul_sdiv_assoc]; rw [div_eq_mul_inv]; rw [inv_sdiv_eq_sdiv_rev]

/-- Dividing by the result of multiplying with a group element produces the same result
as dividing the points and dividing by that group element. -/
@[to_additive /-- Subtracting the result of adding a group element produces the same result
as subtracting the points and subtracting that group element. -/]
/--
theorem `sdiv_smul_eq_sdiv_div` / 定理 `sdiv_smul_eq_sdiv_div`

English:
theorem sdiv_smul_eq_sdiv_div
  given: (p₁ p₂ : P) (g : G)
  statement: p₁ /ₛ (g • p₂) = (p₁ /ₛ p₂) / g
  proof: by
  rw [← mul_right_inj (p₂ /ₛ p₁ : G)]; rw [sdiv_mul_sdiv_cancel]; rw [← inv_sdiv_eq_sdiv_rev]; rw [smul_sdiv]; rw [←
    mul_div_assoc]; rw [← inv_sdiv_eq_sdiv_rev]; rw [inv_mul_cancel]; rw [one_div]

中文:
定理 sdiv_smul_eq_sdiv_div
  条件: (p₁ p₂ : P) (g : G)
  结论: p₁ /ₛ (g • p₂) = (p₁ /ₛ p₂) / g
  证明: by
  rw [← mul_right_inj (p₂ /ₛ p₁ : G)]; rw [sdiv_mul_sdiv_cancel]; rw [← inv_sdiv_eq_sdiv_rev]; rw [smul_sdiv]; rw [←
    mul_div_assoc]; rw [← inv_sdiv_eq_sdiv_rev]; rw [inv_mul_cancel]; rw [one_div]

Depends on / 依赖: inv_mul_cancel, inv_sdiv_eq_sdiv_rev, mul_div_assoc, mul_right_inj, one_div, sdiv_mul_sdiv_cancel, smul_sdiv
-/
theorem sdiv_smul_eq_sdiv_div (p₁ p₂ : P) (g : G) : p₁ /ₛ (g • p₂) = (p₁ /ₛ p₂) / g := by
  rw [← mul_right_inj (p₂ /ₛ p₁ : G)]; rw [sdiv_mul_sdiv_cancel]; rw [← inv_sdiv_eq_sdiv_rev]; rw [smul_sdiv]; rw [←
    mul_div_assoc]; rw [← inv_sdiv_eq_sdiv_rev]; rw [inv_mul_cancel]; rw [one_div]

/-- Cancellation dividing the results of two divisions. -/
@[to_additive (attr := simp) /-- Cancellation subtracting the results of two subtractions. -/]
/--
theorem `sdiv_div_sdiv_cancel_right` / 定理 `sdiv_div_sdiv_cancel_right`

English:
theorem sdiv_div_sdiv_cancel_right
  given: (p₁ p₂ p₃ : P)
  statement: (p₁ /ₛ p₃) / (p₂ /ₛ p₃) = p₁ /ₛ p₂
  proof: by
  rw [← sdiv_smul_eq_sdiv_div]; rw [sdiv_smul]

中文:
定理 sdiv_div_sdiv_cancel_right
  条件: (p₁ p₂ p₃ : P)
  结论: (p₁ /ₛ p₃) / (p₂ /ₛ p₃) = p₁ /ₛ p₂
  证明: by
  rw [← sdiv_smul_eq_sdiv_div]; rw [sdiv_smul]

Depends on / 依赖: sdiv_smul, sdiv_smul_eq_sdiv_div
-/
theorem sdiv_div_sdiv_cancel_right (p₁ p₂ p₃ : P) : (p₁ /ₛ p₃) / (p₂ /ₛ p₃) = p₁ /ₛ p₂ := by
  rw [← sdiv_smul_eq_sdiv_div]; rw [sdiv_smul]

/-- Convert between an equality with multiplying a group element with a point
and an equality of a division of two points with a group element. -/
@[to_additive /-- Convert between an equality with adding a group element to a point
and an equality of a subtraction of two points with a group element. -/]
/--
theorem `eq_smul_iff_sdiv_eq` / 定理 `eq_smul_iff_sdiv_eq`

English:
theorem eq_smul_iff_sdiv_eq
  given: (p₁ : P) (g : G) (p₂ : P)
  statement: p₁ = g • p₂ ↔ p₁ /ₛ p₂ = g
  proof: ⟨fun h => h.symm ▸ smul_sdiv _ _, fun h => h ▸ (sdiv_smul _ _).symm⟩

@[to_additive]

中文:
定理 eq_smul_iff_sdiv_eq
  条件: (p₁ : P) (g : G) (p₂ : P)
  结论: p₁ = g • p₂ ↔ p₁ /ₛ p₂ = g
  证明: ⟨fun h => h.symm ▸ smul_sdiv _ _, fun h => h ▸ (sdiv_smul _ _).symm⟩

@[to_additive]

Depends on / 依赖: h.symm, sdiv_smul, smul_sdiv
-/
theorem eq_smul_iff_sdiv_eq (p₁ : P) (g : G) (p₂ : P) : p₁ = g • p₂ ↔ p₁ /ₛ p₂ = g :=
  ⟨fun h => h.symm ▸ smul_sdiv _ _, fun h => h ▸ (sdiv_smul _ _).symm⟩

@[to_additive]
/--
theorem `smul_eq_smul_iff_inv_mul_eq_sdiv` / 定理 `smul_eq_smul_iff_inv_mul_eq_sdiv`

English:
theorem smul_eq_smul_iff_inv_mul_eq_sdiv
  given: {v₁ v₂ : G} {p₁ p₂ : P}
  proof: by
  rw [eq_smul_iff_sdiv_eq]; rw [smul_sdiv_assoc]; rw [← mul_right_inj v₁⁻¹]; rw [inv_mul_cancel_left]; rw [eq_comm]

@[to_additive (attr := simp)]

中文:
定理 smul_eq_smul_iff_inv_mul_eq_sdiv
  条件: {v₁ v₂ : G} {p₁ p₂ : P}
  证明: by
  rw [eq_smul_iff_sdiv_eq]; rw [smul_sdiv_assoc]; rw [← mul_right_inj v₁⁻¹]; rw [inv_mul_cancel_left]; rw [eq_comm]

@[to_additive (attr := simp)]

Depends on / 依赖: eq_comm, eq_smul_iff_sdiv_eq, inv_mul_cancel_left, mul_right_inj, smul_sdiv_assoc
-/
theorem smul_eq_smul_iff_inv_mul_eq_sdiv {v₁ v₂ : G} {p₁ p₂ : P} :
    v₁ • p₁ = v₂ • p₂ ↔ v₁⁻¹ * v₂ = p₁ /ₛ p₂ := by
  rw [eq_smul_iff_sdiv_eq]; rw [smul_sdiv_assoc]; rw [← mul_right_inj v₁⁻¹]; rw [inv_mul_cancel_left]; rw [eq_comm]

@[to_additive (attr := simp)]
/--
theorem `smul_sdiv_smul_cancel_right` / 定理 `smul_sdiv_smul_cancel_right`

English:
theorem smul_sdiv_smul_cancel_right
  given: (v₁ v₂ : G) (p : P)
  statement: (v₁ • p) /ₛ (v₂ • p) = v₁ / v₂
  proof: by
  rw [sdiv_smul_eq_sdiv_div]; rw [smul_sdiv_assoc]; rw [sdiv_self]; rw [mul_one]

中文:
定理 smul_sdiv_smul_cancel_right
  条件: (v₁ v₂ : G) (p : P)
  结论: (v₁ • p) /ₛ (v₂ • p) = v₁ / v₂
  证明: by
  rw [sdiv_smul_eq_sdiv_div]; rw [smul_sdiv_assoc]; rw [sdiv_self]; rw [mul_one]

Depends on / 依赖: mul_one, sdiv_self, sdiv_smul_eq_sdiv_div, smul_sdiv_assoc
-/
theorem smul_sdiv_smul_cancel_right (v₁ v₂ : G) (p : P) : (v₁ • p) /ₛ (v₂ • p) = v₁ / v₂ := by
  rw [sdiv_smul_eq_sdiv_div]; rw [smul_sdiv_assoc]; rw [sdiv_self]; rw [mul_one]

end General

namespace Equiv

variable {G : Type*} {P : Type*} [Group G] [Torsor G P]

/-- `v ↦ v • p` as an equivalence. -/
@[to_additive /-- `v ↦ v +ᵥ p` as an equivalence. -/]
/--
Definition of `smulConst` / `smulConst` 的定义

English:
definition smulConst
  signature: (p : P)
  body: v • p
  invFun p' := p' /ₛ p
  left_inv _ := smul_sdiv _ _
  right_inv _ := sdiv_smul _ _

@[to_additive (attr := simp)]

中文:
定义 smulConst
  签名: (p : P)
  定义体: v • p
  invFun p' := p' /ₛ p
  left_inv _ := smul_sdiv _ _
  right_inv _ := sdiv_smul _ _

@[to_additive (attr := simp)]
-/
def smulConst (p : P) : G ≃ P where
  toFun v := v • p
  invFun p' := p' /ₛ p
  left_inv _ := smul_sdiv _ _
  right_inv _ := sdiv_smul _ _

@[to_additive (attr := simp)]
/--
theorem `coe_smulConst` / 定理 `coe_smulConst`

English:
theorem coe_smulConst
  given: (p : P)
  statement: ⇑(smulConst p) = fun v => v • p
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_smulConst
  条件: (p : P)
  结论: ⇑(smulConst p) = fun v => v • p
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_smulConst (p : P) : ⇑(smulConst p) = fun v => v • p :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `coe_smulConst_symm` / 定理 `coe_smulConst_symm`

English:
theorem coe_smulConst_symm
  given: (p : P)
  statement: ⇑(smulConst p).symm = fun p' => p' /ₛ p
  proof: rfl

中文:
定理 coe_smulConst_symm
  条件: (p : P)
  结论: ⇑(smulConst p).symm = fun p' => p' /ₛ p
  证明: rfl
-/
theorem coe_smulConst_symm (p : P) : ⇑(smulConst p).symm = fun p' => p' /ₛ p :=
  rfl

/-- `p' ↦ p /ₛ p'` as an equivalence. -/
@[to_additive /-- `p' ↦ p -ᵥ p'` as an equivalence. -/]
/--
Definition of `constSDiv` / `constSDiv` 的定义

English:
definition constSDiv
  signature: (p : P)
  body: (p /ₛ ·)
  invFun := (·⁻¹ • p)
  left_inv p' := by simp
  right_inv v := by simp [sdiv_smul_eq_sdiv_div]

@[to_additive (attr := simp)]

中文:
定义 constSDiv
  签名: (p : P)
  定义体: (p /ₛ ·)
  invFun := (·⁻¹ • p)
  left_inv p' := by simp
  right_inv v := by simp [sdiv_smul_eq_sdiv_div]

@[to_additive (attr := simp)]
-/
def constSDiv (p : P) : P ≃ G where
  toFun := (p /ₛ ·)
  invFun := (·⁻¹ • p)
  left_inv p' := by simp
  right_inv v := by simp [sdiv_smul_eq_sdiv_div]

@[to_additive (attr := simp)]
/--
lemma `coe_constSDiv` / 引理 `coe_constSDiv`

English:
lemma coe_constSDiv
  given: (p : P)
  statement: ⇑(constSDiv p) = (p /ₛ ·)
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 coe_constSDiv
  条件: (p : P)
  结论: ⇑(constSDiv p) = (p /ₛ ·)
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma coe_constSDiv (p : P) : ⇑(constSDiv p) = (p /ₛ ·) := rfl

@[to_additive (attr := simp)]
/--
theorem `coe_constSDiv_symm` / 定理 `coe_constSDiv_symm`

English:
theorem coe_constSDiv_symm
  given: (p : P)
  statement: ⇑(constSDiv p).symm = fun (v : G) => v⁻¹ • p
  proof: rfl

中文:
定理 coe_constSDiv_symm
  条件: (p : P)
  结论: ⇑(constSDiv p).symm = fun (v : G) => v⁻¹ • p
  证明: rfl
-/
theorem coe_constSDiv_symm (p : P) : ⇑(constSDiv p).symm = fun (v : G) => v⁻¹ • p :=
  rfl

variable (P)

/-- The permutation given by `p ↦ v • p`. -/
@[to_additive /-- The permutation given by `p ↦ v +ᵥ p`. -/]
/--
Definition of `constSMul` / `constSMul` 的定义

English:
definition constSMul
  signature: (v : G)
  body: (v • ·)
  invFun := (v⁻¹ • ·)
  left_inv p := by simp [smul_smul]
  right_inv p := by simp [smul_smul]

@[to_additive (attr := simp)]

中文:
定义 constSMul
  签名: (v : G)
  定义体: (v • ·)
  invFun := (v⁻¹ • ·)
  left_inv p := by simp [smul_smul]
  right_inv p := by simp [smul_smul]

@[to_additive (attr := simp)]
-/
def constSMul (v : G) : Equiv.Perm P where
  toFun := (v • ·)
  invFun := (v⁻¹ • ·)
  left_inv p := by simp [smul_smul]
  right_inv p := by simp [smul_smul]

@[to_additive (attr := simp)]
/--
lemma `coe_constSMul` / 引理 `coe_constSMul`

English:
lemma coe_constSMul
  given: (v : G)
  statement: ⇑(constSMul P v) = (v • ·)
  proof: rfl

中文:
引理 coe_constSMul
  条件: (v : G)
  结论: ⇑(constSMul P v) = (v • ·)
  证明: rfl
-/
lemma coe_constSMul (v : G) : ⇑(constSMul P v) = (v • ·) := rfl

variable {G : Type*} {P : Type*} [AddGroup G] [AddTorsor G P]

open Function

/--
Definition of `pointReflection` / `pointReflection` 的定义

English:
definition pointReflection
  signature: (x : P)
  body: (constVSub x).trans (vaddConst x)

中文:
定义 pointReflection
  签名: (x : P)
  定义体: (constVSub x).trans (vaddConst x)

Depends on / 依赖: constVSub, vaddConst
-/
def pointReflection (x : P) : Perm P :=
  (constVSub x).trans (vaddConst x)

/--
theorem `pointReflection_apply` / 定理 `pointReflection_apply`

English:
theorem pointReflection_apply
  given: (x y : P)
  statement: pointReflection x y = (x -ᵥ y) +ᵥ x
  proof: rfl

@[simp]

中文:
定理 pointReflection_apply
  条件: (x y : P)
  结论: pointReflection x y = (x -ᵥ y) +ᵥ x
  证明: rfl

@[simp]
-/
theorem pointReflection_apply (x y : P) : pointReflection x y = (x -ᵥ y) +ᵥ x :=
  rfl

@[simp]
/--
theorem `pointReflection_vsub_left` / 定理 `pointReflection_vsub_left`

English:
theorem pointReflection_vsub_left
  given: (x y : P)
  statement: pointReflection x y -ᵥ x = x -ᵥ y
  proof: vadd_vsub ..

@[simp]

中文:
定理 pointReflection_vsub_left
  条件: (x y : P)
  结论: pointReflection x y -ᵥ x = x -ᵥ y
  证明: vadd_vsub ..

@[simp]

Depends on / 依赖: vadd_vsub
-/
theorem pointReflection_vsub_left (x y : P) : pointReflection x y -ᵥ x = x -ᵥ y :=
  vadd_vsub ..

@[simp]
/--
theorem `pointReflection_vsub_right` / 定理 `pointReflection_vsub_right`

English:
theorem pointReflection_vsub_right
  given: (x y : P)
  statement: pointReflection x y -ᵥ y = 2 • (x -ᵥ y)
  proof: by
  simp [pointReflection, two_nsmul, vadd_vsub_assoc]

@[simp]

中文:
定理 pointReflection_vsub_right
  条件: (x y : P)
  结论: pointReflection x y -ᵥ y = 2 • (x -ᵥ y)
  证明: by
  simp [pointReflection, two_nsmul, vadd_vsub_assoc]

@[simp]

Depends on / 依赖: pointReflection, two_nsmul, vadd_vsub_assoc
-/
theorem pointReflection_vsub_right (x y : P) : pointReflection x y -ᵥ y = 2 • (x -ᵥ y) := by
  simp [pointReflection, two_nsmul, vadd_vsub_assoc]

@[simp]
/--
theorem `pointReflection_symm` / 定理 `pointReflection_symm`

English:
theorem pointReflection_symm
  given: (x : P)
  statement: (pointReflection x).symm = pointReflection x
  proof: ext by simp [pointReflection]

@[simp]

中文:
定理 pointReflection_symm
  条件: (x : P)
  结论: (pointReflection x).symm = pointReflection x
  证明: ext by simp [pointReflection]

@[simp]

Depends on / 依赖: MorphismProperty, MorphismProperty.pullback_fst, pointReflection, pullback_fst
-/
theorem pointReflection_symm (x : P) : (pointReflection x).symm = pointReflection x :=
ext by simp [pointReflection]

@[simp]
/--
theorem `pointReflection_self` / 定理 `pointReflection_self`

English:
theorem pointReflection_self
  given: (x : P)
  statement: pointReflection x x = x
  proof: vsub_vadd _ _

中文:
定理 pointReflection_self
  条件: (x : P)
  结论: pointReflection x x = x
  证明: vsub_vadd _ _

Depends on / 依赖: MorphismProperty, MorphismProperty.pullback_snd, pullback_snd, vsub_vadd
-/
theorem pointReflection_self (x : P) : pointReflection x x = x :=
  vsub_vadd _ _

/--
theorem `pointReflection_involutive` / 定理 `pointReflection_involutive`

English:
theorem pointReflection_involutive
  given: (x : P)
  statement: Involutive (pointReflection x : P -> P)
  proof: fun y =>
(Equiv.eq_symm_apply _).1 by rw [pointReflection_symm]

中文:
定理 pointReflection_involutive
  条件: (x : P)
  结论: 对合 (pointReflection x : P -> P)
  证明: fun y =>
(Equiv.eq_symm_apply _).1 by rw [pointReflection_symm]

Depends on / 依赖: IsZariskiLocalAtTarget, IsZariskiLocalAtTarget.restrict, restrict
-/
theorem pointReflection_involutive (x : P) : Involutive (pointReflection x : P -> P) := fun y =>
(Equiv.eq_symm_apply _).1 by rw [pointReflection_symm]

end Equiv

@[to_additive]
/--
theorem `Torsor.subsingleton_iff` / 定理 `Torsor.subsingleton_iff`

English:
theorem Torsor.subsingleton_iff
  given: (G P : Type*) [Group G] [Torsor G P]
  proof: by
  inhabit P
  exact (Equiv.smulConst default).subsingleton_congr

中文:
定理 Torsor.subsingleton_iff
  条件: (G P : 类型) [群 G] [Torsor G P]
  证明: by
  inhabit P
  exact (Equiv.smulConst default).subsingleton_congr

Depends on / 依赖: Equiv.smulConst, IsClosedImmersion, Scheme, inhabit, smulConst, subsingleton_congr
-/
theorem Torsor.subsingleton_iff (G P : Type*) [Group G] [Torsor G P] :
    Subsingleton G ↔ Subsingleton P := by
  inhabit P
  exact (Equiv.smulConst default).subsingleton_congr
