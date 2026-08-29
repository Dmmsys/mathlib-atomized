/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Algebra.Group.Idempotent
public import Mathlib.Algebra.Ring.Idempotent

/-!
# Star projections

This file defines star projections, which are self-adjoint idempotents.

In star-ordered rings, star projections are non-negative.
(See `IsStarProjection.nonneg` in `Mathlib/Algebra/Order/Star/Basic.lean`.)
-/

public section

variable {R : Type*}

/-- A star projection is a self-adjoint idempotent. -/
@[mk_iff]
/--
Definition of `IsStarProjection` / `IsStarProjection` 的定义

English:
structure IsStarProjection
  parameters: [Mul R] [Star R] (p : R)
  axioms and operations (2):
    - isIdempotentElem : IsIdempotentElem p
    - isSelfAdjoint : IsSelfAdjoint p

中文:
结构 IsStarProjection
  参数: [Mul R] [Star R] (p : R)
  公理与运算 (2 个):
    - isIdempotentElem : IsIdempotentElem p
    - isSelfAdjoint : IsSelfAdjoint p
-/
structure IsStarProjection [Mul R] [Star R] (p : R) : Prop where
  protected isIdempotentElem : IsIdempotentElem p
  protected isSelfAdjoint : IsSelfAdjoint p

attribute [grind ->, aesop safe forward]
  IsStarProjection.isIdempotentElem IsStarProjection.isSelfAdjoint

namespace IsStarProjection

variable {p q : R}

/--
lemma `_root_.isStarProjection_iff'` / 引理 `_root_.isStarProjection_iff'`

English:
lemma _root_.isStarProjection_iff'
  given: [Mul R] [Star R]
  proof: isStarProjection_iff _

中文:
引理 _root_.isStarProjection_iff'
  条件: [Mul R] [Star R]
  证明: isStarProjection_iff _

Depends on / 依赖: isStarProjection_iff
-/
lemma _root_.isStarProjection_iff' [Mul R] [Star R] :
    IsStarProjection p ↔ p * p = p ∧ star p = p :=
  isStarProjection_iff _

/--
theorem `isStarNormal` / 定理 `isStarNormal`

English:
theorem isStarNormal
  statement: [Mul R] [Star R]
  proof: hp.isSelfAdjoint.isStarNormal

中文:
定理 isStarNormal
  结论: [Mul R] [Star R]
  证明: hp.isSelfAdjoint.isStarNormal

Depends on / 依赖: hp.isSelfAdjoint.isStarNormal, isSelfAdjoint, isStarNormal
-/
theorem isStarNormal [Mul R] [Star R]
    (hp : IsStarProjection p) : IsStarNormal p :=
  hp.isSelfAdjoint.isStarNormal

/--
theorem `map` / 定理 `map`

English:
theorem map
  statement: {A B : Type*} [Mul A] [Star A] [Mul B] [Star B]
  proof: hx.isIdempotentElem.map f
  isSelfAdjoint := hx.isSelfAdjoint.map f

中文:
定理 map
  结论: {A B : 类型} [Mul A] [Star A] [Mul B] [Star B]
  证明: hx.isIdempotentElem.map f
  isSelfAdjoint := hx.isSelfAdjoint.map f

Depends on / 依赖: Algebra, Algebra.TensorProduct.comm, Algebra.TensorProduct.includeLeftRingHom, Algebra.TensorProduct.includeRight, Category, Category.assoc, CommRingCat, CommRingCat.ofHom_comp, Iso.eq_comp_inv, Iso.inv_comp_eq, Iso.trans_hom, RingHo, RingHomClass, RingHomClass.toRingHom, Spec.map_comp, TensorProduct, eq_comp_inv, includeLeftRingHom, includeRight, inv_comp_eq
-/
protected theorem map {A B : Type*} [Mul A] [Star A] [Mul B] [Star B]
    {F : Type*} [FunLike F A B] [StarHomClass F A B] [MulHomClass F A B]
    {x : A} (hx : IsStarProjection x) (f : F) : IsStarProjection (f x) where
  isIdempotentElem := hx.isIdempotentElem.map f
  isSelfAdjoint := hx.isSelfAdjoint.map f

variable (R) in
@[simp]
/--
theorem `zero` / 定理 `zero`

English:
theorem zero
  given: [NonUnitalNonAssocSemiring R] [StarAddMonoid R]
  statement: IsStarProjection (0 : R)
  proof: ⟨.zero, .zero _⟩

中文:
定理 zero
  条件: [NonUnitalNonAssocSemiring R] [StarAddMonoid R]
  结论: IsStarProjection (0 : R)
  证明: ⟨.zero, .zero _⟩
-/
protected theorem zero [NonUnitalNonAssocSemiring R] [StarAddMonoid R] : IsStarProjection (0 : R) :=
  ⟨.zero, .zero _⟩

variable (R) in
@[simp]
/--
theorem `one` / 定理 `one`

English:
theorem one
  given: [MulOneClass R] [StarMul R]
  statement: IsStarProjection (1 : R)
  proof: ⟨.one, .one _⟩

中文:
定理 one
  条件: [MulOneClass R] [StarMul R]
  结论: IsStarProjection (1 : R)
  证明: ⟨.one, .one _⟩
-/
protected theorem one [MulOneClass R] [StarMul R] : IsStarProjection (1 : R) :=
  ⟨.one, .one _⟩

/--
theorem `pow_eq` / 定理 `pow_eq`

English:
theorem pow_eq
  given: [Monoid R] [Star R] (hp : IsStarProjection p) {n : Nat} (hn : n != 0)
  statement: p ^ n = p
  proof: hp.isIdempotentElem.pow_eq hn

中文:
定理 pow_eq
  条件: [Monoid R] [Star R] (hp : IsStarProjection p) {n : 自然数} (hn : n != 0)
  结论: p ^ n = p
  证明: hp.isIdempotentElem.pow_eq hn

Depends on / 依赖: hp.isIdempotentElem.pow_eq, isIdempotentElem, pow_eq
-/
theorem pow_eq [Monoid R] [Star R] (hp : IsStarProjection p) {n : Nat} (hn : n != 0) : p ^ n = p :=
  hp.isIdempotentElem.pow_eq hn

/--
theorem `pow_succ_eq` / 定理 `pow_succ_eq`

English:
theorem pow_succ_eq
  given: [Monoid R] [Star R] (hp : IsStarProjection p) (n : Nat)
  statement: p ^ (n + 1) = p
  proof: hp.isIdempotentElem.pow_succ_eq n

中文:
定理 pow_succ_eq
  条件: [Monoid R] [Star R] (hp : IsStarProjection p) (n : 自然数)
  结论: p ^ (n + 1) = p
  证明: hp.isIdempotentElem.pow_succ_eq n

Depends on / 依赖: hp.isIdempotentElem.pow_succ_eq, isIdempotentElem, pow_succ_eq
-/
theorem pow_succ_eq [Monoid R] [Star R] (hp : IsStarProjection p) (n : Nat) : p ^ (n + 1) = p :=
  hp.isIdempotentElem.pow_succ_eq n

section NonAssocRing
variable [NonAssocRing R]

/--
theorem `one_sub` / 定理 `one_sub`

English:
theorem one_sub
  given: [StarRing R] (hp : IsStarProjection p)
  statement: IsStarProjection (1 - p) where
  proof: hp.isIdempotentElem.one_sub
  isSelfAdjoint := .sub (.one _) hp.isSelfAdjoint

中文:
定理 one_sub
  条件: [StarRing R] (hp : IsStarProjection p)
  结论: IsStarProjection (1 - p) where
  证明: hp.isIdempotentElem.one_sub
  isSelfAdjoint := .sub (.one _) hp.isSelfAdjoint

Depends on / 依赖: hp.isIdempotentElem.one_sub, isIdempotentElem, one_sub
-/
theorem one_sub [StarRing R] (hp : IsStarProjection p) : IsStarProjection (1 - p) where
  isIdempotentElem := hp.isIdempotentElem.one_sub
  isSelfAdjoint := .sub (.one _) hp.isSelfAdjoint

/--
theorem `_root_.isStarProjection_one_sub_iff` / 定理 `_root_.isStarProjection_one_sub_iff`

English:
theorem _root_.isStarProjection_one_sub_iff
  given: [StarRing R]
  proof: ⟨fun h => sub_sub_cancel 1 p ▸ h.one_sub, .one_sub⟩

alias ⟨of_one_sub, _⟩ := isStarProjection_one_sub_iff

中文:
定理 _root_.isStarProjection_one_sub_iff
  条件: [StarRing R]
  证明: ⟨fun h => sub_sub_cancel 1 p ▸ h.one_sub, .one_sub⟩

alias ⟨of_one_sub, _⟩ := isStarProjection_one_sub_iff

Depends on / 依赖: h.one_sub, one_sub, sub_sub_cancel
-/
theorem _root_.isStarProjection_one_sub_iff [StarRing R] :
    IsStarProjection (1 - p) ↔ IsStarProjection p :=
  ⟨fun h => sub_sub_cancel 1 p ▸ h.one_sub, .one_sub⟩

alias ⟨of_one_sub, _⟩ := isStarProjection_one_sub_iff

/--
lemma `mul_one_sub_self` / 引理 `mul_one_sub_self`

English:
lemma mul_one_sub_self
  given: [Star R] (hp : IsStarProjection p)
  statement: p * (1 - p) = 0
  proof: hp.isIdempotentElem.mul_one_sub_self

中文:
引理 mul_one_sub_self
  条件: [Star R] (hp : IsStarProjection p)
  结论: p * (1 - p) = 0
  证明: hp.isIdempotentElem.mul_one_sub_self

Depends on / 依赖: hp.isIdempotentElem.mul_one_sub_self, isIdempotentElem, mul_one_sub_self
-/
lemma mul_one_sub_self [Star R] (hp : IsStarProjection p) : p * (1 - p) = 0 :=
  hp.isIdempotentElem.mul_one_sub_self

/--
lemma `one_sub_mul_self` / 引理 `one_sub_mul_self`

English:
lemma one_sub_mul_self
  given: [Star R] (hp : IsStarProjection p)
  statement: (1 - p) * p = 0
  proof: hp.isIdempotentElem.one_sub_mul_self

中文:
引理 one_sub_mul_self
  条件: [Star R] (hp : IsStarProjection p)
  结论: (1 - p) * p = 0
  证明: hp.isIdempotentElem.one_sub_mul_self

Depends on / 依赖: hp.isIdempotentElem.one_sub_mul_self, isIdempotentElem, one_sub_mul_self
-/
lemma one_sub_mul_self [Star R] (hp : IsStarProjection p) : (1 - p) * p = 0 :=
  hp.isIdempotentElem.one_sub_mul_self

end NonAssocRing

/--
theorem `add` / 定理 `add`

English:
theorem add
  statement: [NonUnitalNonAssocSemiring R] [StarRing R]
  proof: hp.isSelfAdjoint.add hq.isSelfAdjoint
isIdempotentElem := hp.isIdempotentElem.add hq.isIdempotentElem by
    rw [hpq]; rw [zero_add]
    simpa [hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq] using congr(star $(hpq))

中文:
定理 add
  结论: [NonUnitalNonAssocSemiring R] [StarRing R]
  证明: hp.isSelfAdjoint.add hq.isSelfAdjoint
isIdempotentElem := hp.isIdempotentElem.add hq.isIdempotentElem by
    rw [hpq]; rw [zero_add]
    simpa [hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq] using congr(star $(hpq))

Depends on / 依赖: hp.isSelfAdjoint.add, hq.isSelfAdjoint, isSelfAdjoint
-/
theorem add [NonUnitalNonAssocSemiring R] [StarRing R]
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : p * q = 0) :
    IsStarProjection (p + q) where
  isSelfAdjoint := hp.isSelfAdjoint.add hq.isSelfAdjoint
isIdempotentElem := hp.isIdempotentElem.add hq.isIdempotentElem by
    rw [hpq]; rw [zero_add]
    simpa [hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq] using congr(star $(hpq))

/--
theorem `mul` / 定理 `mul`

English:
theorem mul
  statement: [NonUnitalSemiring R] [StarRing R]
  proof: (IsSelfAdjoint.commute_iff hp.isSelfAdjoint hq.isSelfAdjoint).mp hpq
  isIdempotentElem := hp.isIdempotentElem.mul_of_commute hpq hq.isIdempotentElem

中文:
定理 mul
  结论: [NonUnitalSemiring R] [StarRing R]
  证明: (IsSelfAdjoint.commute_iff hp.isSelfAdjoint hq.isSelfAdjoint).mp hpq
  isIdempotentElem := hp.isIdempotentElem.mul_of_commute hpq hq.isIdempotentElem

Depends on / 依赖: IsSelfAdjoint, IsSelfAdjoint.commute_iff, commute_iff, hp.isSelfAdjoint, hq.isSelfAdjoint, isSelfAdjoint
-/
theorem mul [NonUnitalSemiring R] [StarRing R]
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpq : Commute p q) : IsStarProjection (p * q) where
  isSelfAdjoint := (IsSelfAdjoint.commute_iff hp.isSelfAdjoint hq.isSelfAdjoint).mp hpq
  isIdempotentElem := hp.isIdempotentElem.mul_of_commute hpq hq.isIdempotentElem

/--
theorem `sub_of_mul_eq_left` / 定理 `sub_of_mul_eq_left`

English:
theorem sub_of_mul_eq_left
  statement: [NonUnitalNonAssocRing R] [StarRing R]
  proof: hq.isSelfAdjoint.sub hp.isSelfAdjoint
  isIdempotentElem := hp.isIdempotentElem.sub
    hq.isIdempotentElem hpq
    (by simpa [hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq] using congr(star $(hpq)))

中文:
定理 sub_of_mul_eq_left
  结论: [NonUnitalNonAssocRing R] [StarRing R]
  证明: hq.isSelfAdjoint.sub hp.isSelfAdjoint
  isIdempotentElem := hp.isIdempotentElem.sub
    hq.isIdempotentElem hpq
    (by simpa [hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq] using congr(star $(hpq)))

Depends on / 依赖: hp.isSelfAdjoint, hq.isSelfAdjoint.sub, isSelfAdjoint
-/
theorem sub_of_mul_eq_left [NonUnitalNonAssocRing R] [StarRing R]
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : p * q = p) :
    IsStarProjection (q - p) where
  isSelfAdjoint := hq.isSelfAdjoint.sub hp.isSelfAdjoint
  isIdempotentElem := hp.isIdempotentElem.sub
    hq.isIdempotentElem hpq
    (by simpa [hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq] using congr(star $(hpq)))

/--
theorem `sub_of_mul_eq_right` / 定理 `sub_of_mul_eq_right`

English:
theorem sub_of_mul_eq_right
  statement: [NonUnitalNonAssocRing R] [StarRing R]
  proof: hp.sub_of_mul_eq_left hq
  (by simpa [hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq] using congr(star $(hqp)))

中文:
定理 sub_of_mul_eq_right
  结论: [NonUnitalNonAssocRing R] [StarRing R]
  证明: hp.sub_of_mul_eq_left hq
  (by simpa [hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq] using congr(star $(hqp)))

Depends on / 依赖: hp.sub_of_mul_eq_left, sub_of_mul_eq_left
-/
theorem sub_of_mul_eq_right [NonUnitalNonAssocRing R] [StarRing R]
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hqp : q * p = p) :
    IsStarProjection (q - p) := hp.sub_of_mul_eq_left hq
  (by simpa [hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq] using congr(star $(hqp)))

/--
theorem `sub_iff_mul_eq_left` / 定理 `sub_iff_mul_eq_left`

English:
theorem sub_iff_mul_eq_left
  statement: [NonUnitalRing R] [StarRing R] [IsAddTorsionFree R]
  proof: by
  rw [isStarProjection_iff]; rw [hp.isIdempotentElem.sub_iff hq.isIdempotentElem]
  simp_rw [hq.isSelfAdjoint.sub hp.isSelfAdjoint, and_true]
  nth_rw 3 [← hp.isSelfAdjoint]
  nth_rw 2 [← hq.isSelfAdjoint]
  rw [← star_mul]; rw [star_eq_iff_star_eq]; rw [hp.isSelfAdjoint]; rw [eq_comm]
  simp_rw 

中文:
定理 sub_iff_mul_eq_left
  结论: [NonUnitalRing R] [StarRing R] [IsAddTorsionFree R]
  证明: by
  rw [isStarProjection_iff]; rw [hp.isIdempotentElem.sub_iff hq.isIdempotentElem]
  simp_rw [hq.isSelfAdjoint.sub hp.isSelfAdjoint, and_true]
  nth_rw 3 [← hp.isSelfAdjoint]
  nth_rw 2 [← hq.isSelfAdjoint]
  rw [← star_mul]; rw [star_eq_iff_star_eq]; rw [hp.isSelfAdjoint]; rw [eq_comm]
  simp_rw 

Depends on / 依赖: and_self, and_true, eq_comm, hp.isIdempotentElem.sub_iff, hp.isSelfAdjoint, hq.isIdempotentElem, hq.isSelfAdjoint, hq.isSelfAdjoint.sub, isIdempotentElem, isSelfAdjoint, isStarProjection_iff, nth_rw, simp_rw, star_eq_iff_star_eq, star_mul, sub_iff
-/
theorem sub_iff_mul_eq_left [NonUnitalRing R] [StarRing R] [IsAddTorsionFree R]
    {p q : R} (hp : IsStarProjection p) (hq : IsStarProjection q) :
    IsStarProjection (q - p) ↔ p * q = p := by
  rw [isStarProjection_iff]; rw [hp.isIdempotentElem.sub_iff hq.isIdempotentElem]
  simp_rw [hq.isSelfAdjoint.sub hp.isSelfAdjoint, and_true]
  nth_rw 3 [← hp.isSelfAdjoint]
  nth_rw 2 [← hq.isSelfAdjoint]
  rw [← star_mul]; rw [star_eq_iff_star_eq]; rw [hp.isSelfAdjoint]; rw [eq_comm]
  simp_rw [and_self]

/--
theorem `sub_iff_mul_eq_right` / 定理 `sub_iff_mul_eq_right`

English:
theorem sub_iff_mul_eq_right
  statement: [NonUnitalRing R] [StarRing R] [IsAddTorsionFree R]
  proof: by
  rw [← star_inj]
  simp [star_mul, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq,
    sub_iff_mul_eq_left hp hq]

中文:
定理 sub_iff_mul_eq_right
  结论: [NonUnitalRing R] [StarRing R] [IsAddTorsionFree R]
  证明: by
  rw [← star_inj]
  simp [star_mul, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq,
    sub_iff_mul_eq_left hp hq]

Depends on / 依赖: hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq, isSelfAdjoint, star_eq, star_inj, star_mul, sub_iff_mul_eq_left
-/
theorem sub_iff_mul_eq_right [NonUnitalRing R] [StarRing R] [IsAddTorsionFree R]
    {p q : R} (hp : IsStarProjection p) (hq : IsStarProjection q) :
    IsStarProjection (q - p) ↔ q * p = p := by
  rw [← star_inj]
  simp [star_mul, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq,
    sub_iff_mul_eq_left hp hq]

/--
theorem `add_sub_mul_of_commute` / 定理 `add_sub_mul_of_commute`

English:
theorem add_sub_mul_of_commute
  statement: [NonUnitalRing R] [StarRing R]
  proof: hp.isIdempotentElem.add_sub_mul_of_commute hpq hq.isIdempotentElem
  isSelfAdjoint := .sub (hp.isSelfAdjoint.add hq.isSelfAdjoint)
    ((IsSelfAdjoint.commute_iff hp.isSelfAdjoint hq.isSelfAdjoint).mp hpq)

中文:
定理 add_sub_mul_of_commute
  结论: [NonUnitalRing R] [StarRing R]
  证明: hp.isIdempotentElem.add_sub_mul_of_commute hpq hq.isIdempotentElem
  isSelfAdjoint := .sub (hp.isSelfAdjoint.add hq.isSelfAdjoint)
    ((IsSelfAdjoint.commute_iff hp.isSelfAdjoint hq.isSelfAdjoint).mp hpq)

Depends on / 依赖: add_sub_mul_of_commute, hp.isIdempotentElem.add_sub_mul_of_commute, hq.isIdempotentElem, isIdempotentElem
-/
theorem add_sub_mul_of_commute [NonUnitalRing R] [StarRing R]
    (hpq : Commute p q) (hp : IsStarProjection p) (hq : IsStarProjection q) :
    IsStarProjection (p + q - p * q) where
  isIdempotentElem := hp.isIdempotentElem.add_sub_mul_of_commute hpq hq.isIdempotentElem
  isSelfAdjoint := .sub (hp.isSelfAdjoint.add hq.isSelfAdjoint)
    ((IsSelfAdjoint.commute_iff hp.isSelfAdjoint hq.isSelfAdjoint).mp hpq)

end IsStarProjection
