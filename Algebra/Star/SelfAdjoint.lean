/-
Copyright (c) 2021 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Star.Rat

/-!
# Self-adjoint, skew-adjoint and normal elements of a star additive group

This file defines `selfAdjoint R` (resp. `skewAdjoint R`), where `R` is a star additive group,
as the additive subgroup containing the elements that satisfy `star x = x` (resp. `star x = -x`).
This includes, for instance, (skew-)Hermitian operators on Hilbert spaces.

We also define `IsStarNormal R`, a `Prop` that states that an element `x` satisfies
`star x * x = x * star x`.

## Implementation notes

* When `R` is a `StarModule R₂ R`, then `selfAdjoint R` has a natural
  `Module (selfAdjoint R₂) (selfAdjoint R)` structure. However, doing this literally would be
  undesirable since in the main case of interest (`R₂ = ℂ`) we want `Module ℝ (selfAdjoint R)`
  and not `Module (selfAdjoint ℂ) (selfAdjoint R)`. We solve this issue by adding the typeclass
  `[TrivialStar R₃]`, of which `ℝ` is an instance (registered in `Data/Real/Basic`), and then
  add a `[Module R₃ (selfAdjoint R)]` instance whenever we have
  `[Module R₃ R] [TrivialStar R₃]`. (Another approach would have been to define
  `[StarInvariantScalars R₃ R]` to express the fact that `star (x • v) = x • star v`, but
  this typeclass would have the disadvantage of taking two type arguments.)

## TODO

* Define `IsSkewAdjoint` to match `IsSelfAdjoint`.
* Define `fun z x => z * x * star z` (i.e. conjugation by `z`) as a monoid action of `R` on `R`
  (similar to the existing `ConjAct` for groups), and then state the fact that `selfAdjoint R` is
  invariant under it.

-/

@[expose] public section

open Function

variable {R A : Type*}

/--
Definition of `IsSelfAdjoint` / `IsSelfAdjoint` 的定义

English:
definition IsSelfAdjoint
  signature: [Star R] (x : R)
  body: star x = x

中文:
定义 IsSelfAdjoint
  签名: [对合 R] (x : R)
  定义体: star x = x
-/
def IsSelfAdjoint [Star R] (x : R) : Prop :=
  star x = x

/-- An element of a star monoid is normal if it commutes with its adjoint. -/
@[mk_iff]
/--
Definition of `IsStarNormal` / `IsStarNormal` 的定义

English:
class IsStarNormal
  parameters: [Mul R] [Star R] (x : R)
  axioms and operations (1):
    - star_comm_self : Commute (star x) x

中文:
类 是StarNormal
  参数: [乘法 R] [对合 R] (x : R)
  公理与运算 (1 个):
    - star_comm_self : Commute (star x) x
-/
class IsStarNormal [Mul R] [Star R] (x : R) : Prop where
  /-- A normal element of a star monoid commutes with its adjoint. -/
  star_comm_self : Commute (star x) x

export IsStarNormal (star_comm_self)

attribute [grind ->] star_comm_self

/--
theorem `star_comm_self'` / 定理 `star_comm_self'`

English:
theorem star_comm_self'
  given: [Mul R] [Star R] (x : R) [IsStarNormal x]
  statement: star x * x = x * star x
  proof: IsStarNormal.star_comm_self

中文:
定理 star_comm_self'
  条件: [乘法 R] [对合 R] (x : R) [是StarNormal x]
  结论: star x * x = x * star x
  证明: IsStarNormal.star_comm_self

Depends on / 依赖: IsStarNormal, IsStarNormal.star_comm_self, star_comm_self
-/
theorem star_comm_self' [Mul R] [Star R] (x : R) [IsStarNormal x] : star x * x = x * star x :=
  IsStarNormal.star_comm_self

namespace IsSelfAdjoint

-- named to match `Commute.allₓ`
/--
theorem `all` / 定理 `all`

English:
theorem all
  given: [Star R] [TrivialStar R] (r : R)
  statement: IsSelfAdjoint r
  proof: star_trivial _

中文:
定理 all
  条件: [对合 R] [TrivialStar R] (r : R)
  结论: IsSelfAdjoint r
  证明: star_trivial _

Depends on / 依赖: star_trivial
-/
theorem all [Star R] [TrivialStar R] (r : R) : IsSelfAdjoint r :=
  star_trivial _

/--
theorem `star_eq` / 定理 `star_eq`

English:
theorem star_eq
  given: [Star R] {x : R} (hx : IsSelfAdjoint x)
  statement: star x = x
  proof: hx

grind_pattern star_eq => IsSelfAdjoint x, star x

中文:
定理 star_eq
  条件: [对合 R] {x : R} (hx : IsSelfAdjoint x)
  结论: star x = x
  证明: hx

grind_pattern star_eq => IsSelfAdjoint x, star x
-/
theorem star_eq [Star R] {x : R} (hx : IsSelfAdjoint x) : star x = x :=
  hx

grind_pattern star_eq => IsSelfAdjoint x, star x

/--
theorem `_root_.isSelfAdjoint_iff` / 定理 `_root_.isSelfAdjoint_iff`

English:
theorem _root_.isSelfAdjoint_iff
  given: [Star R] {x : R}
  statement: IsSelfAdjoint x ↔ star x = x
  proof: Iff.rfl

@[simp]

中文:
定理 _root_.isSelfAdjoint_iff
  条件: [对合 R] {x : R}
  结论: IsSelfAdjoint x ↔ star x = x
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem _root_.isSelfAdjoint_iff [Star R] {x : R} : IsSelfAdjoint x ↔ star x = x :=
  Iff.rfl

@[simp]
/--
theorem `star_iff` / 定理 `star_iff`

English:
theorem star_iff
  given: [InvolutiveStar R] {x : R}
  statement: IsSelfAdjoint (star x) ↔ IsSelfAdjoint x
  proof: by
  simpa only [IsSelfAdjoint, star_star] using eq_comm

@[simp]

中文:
定理 star_iff
  条件: [InvolutiveStar R] {x : R}
  结论: IsSelfAdjoint (star x) ↔ IsSelfAdjoint x
  证明: by
  simpa only [IsSelfAdjoint, star_star] using eq_comm

@[simp]

Depends on / 依赖: IsSelfAdjoint, eq_comm, star_star
-/
theorem star_iff [InvolutiveStar R] {x : R} : IsSelfAdjoint (star x) ↔ IsSelfAdjoint x := by
  simpa only [IsSelfAdjoint, star_star] using eq_comm

@[simp]
/--
theorem `star_mul_self` / 定理 `star_mul_self`

English:
theorem star_mul_self
  given: [Mul R] [StarMul R] (x : R)
  statement: IsSelfAdjoint (star x * x)
  proof: by
  simp only [IsSelfAdjoint, star_mul, star_star]

@[simp]

中文:
定理 star_mul_self
  条件: [乘法 R] [StarMul R] (x : R)
  结论: IsSelfAdjoint (star x * x)
  证明: by
  simp only [IsSelfAdjoint, star_mul, star_star]

@[simp]

Depends on / 依赖: IsSelfAdjoint, star_mul, star_star
-/
theorem star_mul_self [Mul R] [StarMul R] (x : R) : IsSelfAdjoint (star x * x) := by
  simp only [IsSelfAdjoint, star_mul, star_star]

@[simp]
/--
theorem `mul_star_self` / 定理 `mul_star_self`

English:
theorem mul_star_self
  given: [Mul R] [StarMul R] (x : R)
  statement: IsSelfAdjoint (x * star x)
  proof: by
  simpa only [star_star] using star_mul_self (star x)

中文:
定理 mul_star_self
  条件: [乘法 R] [StarMul R] (x : R)
  结论: IsSelfAdjoint (x * star x)
  证明: by
  simpa only [star_star] using star_mul_self (star x)

Depends on / 依赖: star_mul_self, star_star
-/
theorem mul_star_self [Mul R] [StarMul R] (x : R) : IsSelfAdjoint (x * star x) := by
  simpa only [star_star] using star_mul_self (star x)

/--
lemma `commute_iff` / 引理 `commute_iff`

English:
lemma commute_iff
  statement: {R : Type*} [Mul R] [StarMul R] {x y : R}
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [isSelfAdjoint_iff, star_mul, hx.star_eq, hy.star_eq, h.eq]
  · simpa only [star_mul, hx.star_eq, hy.star_eq] using! h.symm

中文:
引理 commute_iff
  结论: {R : 类型} [乘法 R] [StarMul R] {x y : R}
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [isSelfAdjoint_iff, star_mul, hx.star_eq, hy.star_eq, h.eq]
  · simpa only [star_mul, hx.star_eq, hy.star_eq] using! h.symm

Depends on / 依赖: h.eq, h.symm, hx.star_eq, hy.star_eq, isSelfAdjoint_iff, star_eq, star_mul
-/
lemma commute_iff {R : Type*} [Mul R] [StarMul R] {x y : R}
    (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) : Commute x y ↔ IsSelfAdjoint (x * y) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [isSelfAdjoint_iff, star_mul, hx.star_eq, hy.star_eq, h.eq]
  · simpa only [star_mul, hx.star_eq, hy.star_eq] using! h.symm

/--
lemma `commute_of_mul_eq_isSelfAdjoint` / 引理 `commute_of_mul_eq_isSelfAdjoint`

English:
lemma commute_of_mul_eq_isSelfAdjoint
  statement: {R : Type*} [Mul R] [StarMul R] (x y z : R)
  proof: by
  grind [commute_iff hx hy]

中文:
引理 commute_of_mul_eq_isSelfAdjoint
  结论: {R : 类型} [乘法 R] [StarMul R] (x y z : R)
  证明: by
  grind [commute_iff hx hy]

Depends on / 依赖: commute_iff
-/
lemma commute_of_mul_eq_isSelfAdjoint {R : Type*} [Mul R] [StarMul R] (x y z : R)
    (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) (hz : IsSelfAdjoint z) (hxyz : x * y = z) :
    Commute x y := by
  grind [commute_iff hx hy]

/-- Functions in a `StarHomClass` preserve self-adjoint elements. -/
@[aesop 10% apply]
/--
theorem `map` / 定理 `map`

English:
theorem map
  statement: {F R S : Type*} [Star R] [Star S] [FunLike F R S] [StarHomClass F R S]
  proof: show star (f x) = f x from map_star f x ▸ congr_arg f hx

中文:
定理 map
  结论: {F R S : 类型} [对合 R] [对合 S] [函数状 F R S] [对合态射类 F R S]
  证明: show star (f x) = f x from map_star f x ▸ congr_arg f hx

Depends on / 依赖: congr_arg, map_star
-/
theorem map {F R S : Type*} [Star R] [Star S] [FunLike F R S] [StarHomClass F R S]
    {x : R} (hx : IsSelfAdjoint x) (f : F) : IsSelfAdjoint (f x) :=
  show star (f x) = f x from map_star f x ▸ congr_arg f hx

/--
theorem `_root_.isSelfAdjoint_map` / 定理 `_root_.isSelfAdjoint_map`

English:
theorem _root_.isSelfAdjoint_map
  statement: {F R S : Type*} [Star R] [Star S] [FunLike F R S]
  proof: (IsSelfAdjoint.all x).map f

@[aesop 10% apply]

中文:
定理 _root_.isSelfAdjoint_map
  结论: {F R S : 类型} [对合 R] [对合 S] [函数状 F R S]
  证明: (IsSelfAdjoint.all x).map f

@[aesop 10% apply]

Depends on / 依赖: IsSelfAdjoint, IsSelfAdjoint.all
-/
theorem _root_.isSelfAdjoint_map {F R S : Type*} [Star R] [Star S] [FunLike F R S]
    [StarHomClass F R S] [TrivialStar R] (f : F) (x : R) : IsSelfAdjoint (f x) :=
  (IsSelfAdjoint.all x).map f

@[aesop 10% apply]
/--
theorem `isStarNormal` / 定理 `isStarNormal`

English:
theorem isStarNormal
  given: {R : Type*} [Mul R] [Star R] {x : R} (hx : IsSelfAdjoint x)
  proof: ⟨by simp only [Commute, SemiconjBy, hx.star_eq]⟩

中文:
定理 isStarNormal
  条件: {R : 类型} [乘法 R] [对合 R] {x : R} (hx : IsSelfAdjoint x)
  证明: ⟨by simp only [Commute, SemiconjBy, hx.star_eq]⟩

Depends on / 依赖: Commute, SemiconjBy, hx.star_eq, star_eq
-/
theorem isStarNormal {R : Type*} [Mul R] [Star R] {x : R} (hx : IsSelfAdjoint x) :
    IsStarNormal x := ⟨by simp only [Commute, SemiconjBy, hx.star_eq]⟩

section AddMonoid

variable [AddMonoid R] [StarAddMonoid R]

variable (R) in
/--
theorem `zero` / 定理 `zero`

English:
theorem zero
  statement: IsSelfAdjoint (0 : R)
  proof: star_zero R

@[aesop 90% apply]

中文:
定理 zero
  结论: IsSelfAdjoint (0 : R)
  证明: star_zero R

@[aesop 90% apply]
-/
@[simp, grind .] protected theorem zero : IsSelfAdjoint (0 : R) := star_zero R

@[aesop 90% apply]
/--
theorem `add` / 定理 `add`

English:
theorem add
  given: {x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y)
  statement: IsSelfAdjoint (x + y)
  proof: by
  simp only [isSelfAdjoint_iff, star_add, hx.star_eq, hy.star_eq]

中文:
定理 add
  条件: {x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y)
  结论: IsSelfAdjoint (x + y)
  证明: by
  simp only [isSelfAdjoint_iff, star_add, hx.star_eq, hy.star_eq]

Depends on / 依赖: hx.star_eq, hy.star_eq, isSelfAdjoint_iff, star_add, star_eq
-/
theorem add {x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) : IsSelfAdjoint (x + y) := by
  simp only [isSelfAdjoint_iff, star_add, hx.star_eq, hy.star_eq]

end AddMonoid

section AddGroup

variable [AddGroup R] [StarAddMonoid R]

@[aesop safe apply]
/--
theorem `neg` / 定理 `neg`

English:
theorem neg
  given: {x : R} (hx : IsSelfAdjoint x)
  statement: IsSelfAdjoint (-x)
  proof: by
  simp only [isSelfAdjoint_iff, star_neg, hx.star_eq]

@[aesop 90% apply]

中文:
定理 neg
  条件: {x : R} (hx : IsSelfAdjoint x)
  结论: IsSelfAdjoint (-x)
  证明: by
  simp only [isSelfAdjoint_iff, star_neg, hx.star_eq]

@[aesop 90% apply]

Depends on / 依赖: hx.star_eq, isSelfAdjoint_iff, star_eq, star_neg
-/
theorem neg {x : R} (hx : IsSelfAdjoint x) : IsSelfAdjoint (-x) := by
  simp only [isSelfAdjoint_iff, star_neg, hx.star_eq]

@[aesop 90% apply]
/--
theorem `sub` / 定理 `sub`

English:
theorem sub
  given: {x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y)
  statement: IsSelfAdjoint (x - y)
  proof: by
  simp only [isSelfAdjoint_iff, star_sub, hx.star_eq, hy.star_eq]

中文:
定理 sub
  条件: {x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y)
  结论: IsSelfAdjoint (x - y)
  证明: by
  simp only [isSelfAdjoint_iff, star_sub, hx.star_eq, hy.star_eq]

Depends on / 依赖: hx.star_eq, hy.star_eq, isSelfAdjoint_iff, star_eq, star_sub
-/
theorem sub {x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) : IsSelfAdjoint (x - y) := by
  simp only [isSelfAdjoint_iff, star_sub, hx.star_eq, hy.star_eq]

end AddGroup

section AddCommMonoid

variable [AddCommMonoid R] [StarAddMonoid R]

@[simp]
/--
theorem `add_star_self` / 定理 `add_star_self`

English:
theorem add_star_self
  given: (x : R)
  statement: IsSelfAdjoint (x + star x)
  proof: by
  simp only [isSelfAdjoint_iff, add_comm, star_add, star_star]

@[simp]

中文:
定理 add_star_self
  条件: (x : R)
  结论: IsSelfAdjoint (x + star x)
  证明: by
  simp only [isSelfAdjoint_iff, add_comm, star_add, star_star]

@[simp]

Depends on / 依赖: add_comm, isSelfAdjoint_iff, star_add, star_star
-/
theorem add_star_self (x : R) : IsSelfAdjoint (x + star x) := by
  simp only [isSelfAdjoint_iff, add_comm, star_add, star_star]

@[simp]
/--
theorem `star_add_self` / 定理 `star_add_self`

English:
theorem star_add_self
  given: (x : R)
  statement: IsSelfAdjoint (star x + x)
  proof: by
  simp only [isSelfAdjoint_iff, add_comm, star_add, star_star]

中文:
定理 star_add_self
  条件: (x : R)
  结论: IsSelfAdjoint (star x + x)
  证明: by
  simp only [isSelfAdjoint_iff, add_comm, star_add, star_star]

Depends on / 依赖: add_comm, isSelfAdjoint_iff, star_add, star_star
-/
theorem star_add_self (x : R) : IsSelfAdjoint (star x + x) := by
  simp only [isSelfAdjoint_iff, add_comm, star_add, star_star]

end AddCommMonoid

section Semigroup

variable [Semigroup R] [StarMul R]

@[aesop safe apply]
/--
theorem `conjugate` / 定理 `conjugate`

English:
theorem conjugate
  given: {x : R} (hx : IsSelfAdjoint x) (z : R)
  statement: IsSelfAdjoint (z * x * star z)
  proof: by
  simp only [isSelfAdjoint_iff, star_mul, star_star, mul_assoc, hx.star_eq]

@[aesop safe apply]

中文:
定理 conjugate
  条件: {x : R} (hx : IsSelfAdjoint x) (z : R)
  结论: IsSelfAdjoint (z * x * star z)
  证明: by
  simp only [isSelfAdjoint_iff, star_mul, star_star, mul_assoc, hx.star_eq]

@[aesop safe apply]

Depends on / 依赖: hx.star_eq, isSelfAdjoint_iff, mul_assoc, star_eq, star_mul, star_star
-/
theorem conjugate {x : R} (hx : IsSelfAdjoint x) (z : R) : IsSelfAdjoint (z * x * star z) := by
  simp only [isSelfAdjoint_iff, star_mul, star_star, mul_assoc, hx.star_eq]

@[aesop safe apply]
/--
theorem `conjugate'` / 定理 `conjugate'`

English:
theorem conjugate'
  given: {x : R} (hx : IsSelfAdjoint x) (z : R)
  statement: IsSelfAdjoint (star z * x * z)
  proof: by
  simp only [isSelfAdjoint_iff, star_mul, star_star, mul_assoc, hx.star_eq]

@[aesop 90% apply]

中文:
定理 conjugate'
  条件: {x : R} (hx : IsSelfAdjoint x) (z : R)
  结论: IsSelfAdjoint (star z * x * z)
  证明: by
  simp only [isSelfAdjoint_iff, star_mul, star_star, mul_assoc, hx.star_eq]

@[aesop 90% apply]

Depends on / 依赖: hx.star_eq, isSelfAdjoint_iff, mul_assoc, star_eq, star_mul, star_star
-/
theorem conjugate' {x : R} (hx : IsSelfAdjoint x) (z : R) : IsSelfAdjoint (star z * x * z) := by
  simp only [isSelfAdjoint_iff, star_mul, star_star, mul_assoc, hx.star_eq]

@[aesop 90% apply]
/--
theorem `conjugate_self` / 定理 `conjugate_self`

English:
theorem conjugate_self
  given: {x : R} (hx : IsSelfAdjoint x) {z : R} (hz : IsSelfAdjoint z)
  proof: by nth_rewrite 2 [← hz]; exact conjugate hx z

中文:
定理 conjugate_self
  条件: {x : R} (hx : IsSelfAdjoint x) {z : R} (hz : IsSelfAdjoint z)
  证明: by nth_rewrite 2 [← hz]; exact conjugate hx z

Depends on / 依赖: conjugate, nth_rewrite
-/
theorem conjugate_self {x : R} (hx : IsSelfAdjoint x) {z : R} (hz : IsSelfAdjoint z) :
    IsSelfAdjoint (z * x * z) := by nth_rewrite 2 [← hz]; exact conjugate hx z

end Semigroup

section MulOneClass

variable [MulOneClass R] [StarMul R]
variable (R)

/--
theorem `one` / 定理 `one`

English:
theorem one
  statement: IsSelfAdjoint (1 : R)
  proof: star_one R

中文:
定理 one
  结论: IsSelfAdjoint (1 : R)
  证明: star_one R
-/
@[simp, grind .] protected theorem one : IsSelfAdjoint (1 : R) :=
  star_one R

end MulOneClass

section Monoid

variable [Monoid R] [StarMul R]

@[aesop safe apply]
/--
theorem `pow` / 定理 `pow`

English:
theorem pow
  given: {x : R} (hx : IsSelfAdjoint x) (n : Nat)
  statement: IsSelfAdjoint (x ^ n)
  proof: by
  simp only [isSelfAdjoint_iff, star_pow, hx.star_eq]

@[simp]

中文:
定理 pow
  条件: {x : R} (hx : IsSelfAdjoint x) (n : 自然数)
  结论: IsSelfAdjoint (x ^ n)
  证明: by
  simp only [isSelfAdjoint_iff, star_pow, hx.star_eq]

@[simp]

Depends on / 依赖: hx.star_eq, isSelfAdjoint_iff, star_eq, star_pow
-/
theorem pow {x : R} (hx : IsSelfAdjoint x) (n : Nat) : IsSelfAdjoint (x ^ n) := by
  simp only [isSelfAdjoint_iff, star_pow, hx.star_eq]

@[simp]
/--
theorem `invOf_iff` / 定理 `invOf_iff`

English:
theorem invOf_iff
  given: (x : R) [Invertible x]
  statement: IsSelfAdjoint ⅟x ↔ IsSelfAdjoint x
  proof: by
  rw [isSelfAdjoint_iff]; rw [isSelfAdjoint_iff]; rw [star_invOf]; rw [invOf_inj]

alias ⟨_, invOf⟩ := invOf_iff

@[grind =]

中文:
定理 invOf_iff
  条件: (x : R) [可逆 x]
  结论: IsSelfAdjoint ⅟x ↔ IsSelfAdjoint x
  证明: by
  rw [isSelfAdjoint_iff]; rw [isSelfAdjoint_iff]; rw [star_invOf]; rw [invOf_inj]

alias ⟨_, invOf⟩ := invOf_iff

@[grind =]

Depends on / 依赖: invOf_inj, isSelfAdjoint_iff, star_invOf
-/
theorem invOf_iff (x : R) [Invertible x] : IsSelfAdjoint ⅟x ↔ IsSelfAdjoint x := by
  rw [isSelfAdjoint_iff]; rw [isSelfAdjoint_iff]; rw [star_invOf]; rw [invOf_inj]

alias ⟨_, invOf⟩ := invOf_iff

@[grind =]
/--
lemma `_root_.IsUnit.isSelfAdjoint_conjugate_iff` / 引理 `_root_.IsUnit.isSelfAdjoint_conjugate_iff`

English:
lemma _root_.IsUnit.isSelfAdjoint_conjugate_iff
  given: {a u : R} (hu : IsUnit u)
  proof: by
  simp [IsSelfAdjoint, mul_assoc, hu.mul_right_inj, hu.star.mul_left_inj]

@[grind =]

中文:
引理 _root_.是单位.isSelfAdjoint_conjugate_iff
  条件: {a u : R} (hu : 是单位 u)
  证明: by
  simp [IsSelfAdjoint, mul_assoc, hu.mul_right_inj, hu.star.mul_left_inj]

@[grind =]

Depends on / 依赖: IsSelfAdjoint, hu.mul_right_inj, hu.star.mul_left_inj, mul_assoc, mul_left_inj, mul_right_inj
-/
lemma _root_.IsUnit.isSelfAdjoint_conjugate_iff {a u : R} (hu : IsUnit u) :
    IsSelfAdjoint (u * a * star u) ↔ IsSelfAdjoint a := by
  simp [IsSelfAdjoint, mul_assoc, hu.mul_right_inj, hu.star.mul_left_inj]

@[grind =]
/--
lemma `_root_.IsUnit.isSelfAdjoint_conjugate_iff'` / 引理 `_root_.IsUnit.isSelfAdjoint_conjugate_iff'`

English:
lemma _root_.IsUnit.isSelfAdjoint_conjugate_iff'
  given: {a u : R} (hu : IsUnit u)
  proof: by
  simpa using hu.star.isSelfAdjoint_conjugate_iff

中文:
引理 _root_.是单位.isSelfAdjoint_conjugate_iff'
  条件: {a u : R} (hu : 是单位 u)
  证明: by
  simpa using hu.star.isSelfAdjoint_conjugate_iff

Depends on / 依赖: hu.star.isSelfAdjoint_conjugate_iff, isSelfAdjoint_conjugate_iff
-/
lemma _root_.IsUnit.isSelfAdjoint_conjugate_iff' {a u : R} (hu : IsUnit u) :
    IsSelfAdjoint (star u * a * u) ↔ IsSelfAdjoint a := by
  simpa using hu.star.isSelfAdjoint_conjugate_iff

end Monoid

section Semiring

open Ring

variable [NonAssocSemiring R] [StarRing R]

@[simp]
/--
theorem `natCast` / 定理 `natCast`

English:
theorem natCast
  given: (n : Nat)
  statement: IsSelfAdjoint (n : R)
  proof: star_natCast _

@[simp, grind .]

中文:
定理 natCast
  条件: (n : 自然数)
  结论: IsSelfAdjoint (n : R)
  证明: star_natCast _

@[simp, grind .]
-/
protected theorem natCast (n : Nat) : IsSelfAdjoint (n : R) :=
  star_natCast _

@[simp, grind .]
/--
theorem `ofNat` / 定理 `ofNat`

English:
theorem ofNat
  given: (n : Nat) [n.AtLeastTwo]
  statement: IsSelfAdjoint (ofNat(n) : R)
  proof: .natCast n

@[aesop safe apply, grind ←]

中文:
定理 of自然数
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: IsSelfAdjoint (of自然数(n) : R)
  证明: .natCast n

@[aesop safe apply, grind ←]
-/
protected theorem ofNat (n : Nat) [n.AtLeastTwo] : IsSelfAdjoint (ofNat(n) : R) :=
  .natCast n

@[aesop safe apply, grind ←]
/--
theorem `ringInverse` / 定理 `ringInverse`

English:
theorem ringInverse
  statement: {a : A} [Semiring A] [StarRing A]
  proof: by
  rw [isSelfAdjoint_iff]; rw [← Ring.inverse_star]; rw [ha.star_eq]

中文:
定理 ringInverse
  结论: {a : A} [半环 A] [对合环 A]
  证明: by
  rw [isSelfAdjoint_iff]; rw [← Ring.inverse_star]; rw [ha.star_eq]
-/
protected theorem ringInverse {a : A} [Semiring A] [StarRing A]
    (ha : IsSelfAdjoint a) : IsSelfAdjoint a⁻¹ʳ := by
  rw [isSelfAdjoint_iff]; rw [← Ring.inverse_star]; rw [ha.star_eq]

/--
theorem `_root_.isSelfAdjoint_ringInverse_iff` / 定理 `_root_.isSelfAdjoint_ringInverse_iff`

English:
theorem _root_.isSelfAdjoint_ringInverse_iff
  given: {a : A} [Semiring A] [StarRing A] (ha : IsUnit a)
  proof: ⟨fun h => by grind [h.ringInverse], fun h => h.ringInverse⟩

中文:
定理 _root_.isSelfAdjoint_ringInverse_iff
  条件: {a : A} [半环 A] [对合环 A] (ha : 是单位 a)
  证明: ⟨fun h => by grind [h.ringInverse], fun h => h.ringInverse⟩

Depends on / 依赖: h.ringInverse, ringInverse
-/
theorem _root_.isSelfAdjoint_ringInverse_iff {a : A} [Semiring A] [StarRing A] (ha : IsUnit a) :
    IsSelfAdjoint a⁻¹ʳ ↔ IsSelfAdjoint a :=
  ⟨fun h => by grind [h.ringInverse], fun h => h.ringInverse⟩

end Semiring

section CommSemigroup

variable [CommSemigroup R] [StarMul R]

/--
theorem `mul` / 定理 `mul`

English:
theorem mul
  given: {x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y)
  statement: IsSelfAdjoint (x * y)
  proof: by
  simp only [isSelfAdjoint_iff, star_mul', hx.star_eq, hy.star_eq]

中文:
定理 mul
  条件: {x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y)
  结论: IsSelfAdjoint (x * y)
  证明: by
  simp only [isSelfAdjoint_iff, star_mul', hx.star_eq, hy.star_eq]

Depends on / 依赖: hx.star_eq, hy.star_eq, isSelfAdjoint_iff, star_eq, star_mul
-/
theorem mul {x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) : IsSelfAdjoint (x * y) := by
  simp only [isSelfAdjoint_iff, star_mul', hx.star_eq, hy.star_eq]

end CommSemigroup

section CommSemiring
variable {α : Type*} [CommSemiring α] [StarRing α] {a : α}

open scoped ComplexConjugate

/--
lemma `conj_eq` / 引理 `conj_eq`

English:
lemma conj_eq
  given: (ha : IsSelfAdjoint a)
  statement: conj a = a
  proof: ha.star_eq

中文:
引理 conj_eq
  条件: (ha : IsSelfAdjoint a)
  结论: conj a = a
  证明: ha.star_eq

Depends on / 依赖: ha.star_eq, star_eq
-/
lemma conj_eq (ha : IsSelfAdjoint a) : conj a = a := ha.star_eq

end CommSemiring

section Ring

variable [Ring R] [StarRing R]

@[simp]
/--
theorem `intCast` / 定理 `intCast`

English:
theorem intCast
  given: (z : Int)
  statement: IsSelfAdjoint (z : R)
  proof: star_intCast _

中文:
定理 intCast
  条件: (z : 整数)
  结论: IsSelfAdjoint (z : R)
  证明: star_intCast _
-/
protected theorem intCast (z : Int) : IsSelfAdjoint (z : R) :=
  star_intCast _

end Ring

section Group

variable [Group R] [StarMul R]

@[aesop safe apply]
/--
theorem `inv` / 定理 `inv`

English:
theorem inv
  given: {x : R} (hx : IsSelfAdjoint x)
  statement: IsSelfAdjoint x⁻¹
  proof: by
  simp only [isSelfAdjoint_iff, star_inv, hx.star_eq]

@[simp]

中文:
定理 inv
  条件: {x : R} (hx : IsSelfAdjoint x)
  结论: IsSelfAdjoint x⁻¹
  证明: by
  simp only [isSelfAdjoint_iff, star_inv, hx.star_eq]

@[simp]

Depends on / 依赖: hx.star_eq, isSelfAdjoint_iff, star_eq, star_inv
-/
theorem inv {x : R} (hx : IsSelfAdjoint x) : IsSelfAdjoint x⁻¹ := by
  simp only [isSelfAdjoint_iff, star_inv, hx.star_eq]

@[simp]
/--
theorem `inv_iff` / 定理 `inv_iff`

English:
theorem inv_iff
  given: (x : R)
  statement: IsSelfAdjoint x⁻¹ ↔ IsSelfAdjoint x
  proof: by
  simp [isSelfAdjoint_iff]

@[aesop safe apply]

中文:
定理 inv_iff
  条件: (x : R)
  结论: IsSelfAdjoint x⁻¹ ↔ IsSelfAdjoint x
  证明: by
  simp [isSelfAdjoint_iff]

@[aesop safe apply]

Depends on / 依赖: isSelfAdjoint_iff
-/
theorem inv_iff (x : R) : IsSelfAdjoint x⁻¹ ↔ IsSelfAdjoint x := by
  simp [isSelfAdjoint_iff]

@[aesop safe apply]
/--
theorem `zpow` / 定理 `zpow`

English:
theorem zpow
  given: {x : R} (hx : IsSelfAdjoint x) (n : Int)
  statement: IsSelfAdjoint (x ^ n)
  proof: by
  simp only [isSelfAdjoint_iff, star_zpow, hx.star_eq]

中文:
定理 zpow
  条件: {x : R} (hx : IsSelfAdjoint x) (n : 整数)
  结论: IsSelfAdjoint (x ^ n)
  证明: by
  simp only [isSelfAdjoint_iff, star_zpow, hx.star_eq]

Depends on / 依赖: hx.star_eq, isSelfAdjoint_iff, star_eq, star_zpow
-/
theorem zpow {x : R} (hx : IsSelfAdjoint x) (n : Int) : IsSelfAdjoint (x ^ n) := by
  simp only [isSelfAdjoint_iff, star_zpow, hx.star_eq]

end Group

section GroupWithZero

variable [GroupWithZero R] [StarMul R]

@[aesop safe apply]
/--
theorem `inv₀` / 定理 `inv₀`

English:
theorem inv₀
  given: {x : R} (hx : IsSelfAdjoint x)
  statement: IsSelfAdjoint x⁻¹
  proof: by
  simp only [isSelfAdjoint_iff, star_inv₀, hx.star_eq]

@[simp]

中文:
定理 inv₀
  条件: {x : R} (hx : IsSelfAdjoint x)
  结论: IsSelfAdjoint x⁻¹
  证明: by
  simp only [isSelfAdjoint_iff, star_inv₀, hx.star_eq]

@[simp]

Depends on / 依赖: hx.star_eq, isSelfAdjoint_iff, star_eq
-/
theorem inv₀ {x : R} (hx : IsSelfAdjoint x) : IsSelfAdjoint x⁻¹ := by
  simp only [isSelfAdjoint_iff, star_inv₀, hx.star_eq]

@[simp]
/--
theorem `inv₀_iff` / 定理 `inv₀_iff`

English:
theorem inv₀_iff
  given: (x : R)
  statement: IsSelfAdjoint x⁻¹ ↔ IsSelfAdjoint x
  proof: by
  simp [isSelfAdjoint_iff]

@[aesop safe apply]

中文:
定理 inv₀_iff
  条件: (x : R)
  结论: IsSelfAdjoint x⁻¹ ↔ IsSelfAdjoint x
  证明: by
  simp [isSelfAdjoint_iff]

@[aesop safe apply]

Depends on / 依赖: isSelfAdjoint_iff
-/
theorem inv₀_iff (x : R) : IsSelfAdjoint x⁻¹ ↔ IsSelfAdjoint x := by
  simp [isSelfAdjoint_iff]

@[aesop safe apply]
/--
theorem `zpow₀` / 定理 `zpow₀`

English:
theorem zpow₀
  given: {x : R} (hx : IsSelfAdjoint x) (n : Int)
  statement: IsSelfAdjoint (x ^ n)
  proof: by
  simp only [isSelfAdjoint_iff, star_zpow₀, hx.star_eq]

中文:
定理 zpow₀
  条件: {x : R} (hx : IsSelfAdjoint x) (n : 整数)
  结论: IsSelfAdjoint (x ^ n)
  证明: by
  simp only [isSelfAdjoint_iff, star_zpow₀, hx.star_eq]

Depends on / 依赖: hx.star_eq, isSelfAdjoint_iff, star_eq
-/
theorem zpow₀ {x : R} (hx : IsSelfAdjoint x) (n : Int) : IsSelfAdjoint (x ^ n) := by
  simp only [isSelfAdjoint_iff, star_zpow₀, hx.star_eq]

end GroupWithZero

@[simp]
/--
lemma `nnratCast` / 引理 `nnratCast`

English:
lemma nnratCast
  given: [DivisionSemiring R] [StarRing R] (q : Rat>=0)
  proof: star_nnratCast _

中文:
引理 nnratCast
  条件: [除半环 R] [对合环 R] (q : 有理数>=0)
  证明: star_nnratCast _
-/
protected lemma nnratCast [DivisionSemiring R] [StarRing R] (q : Rat>=0) :
    IsSelfAdjoint (q : R) :=
  star_nnratCast _

section DivisionRing

variable [DivisionRing R] [StarRing R]

@[simp]
/--
theorem `ratCast` / 定理 `ratCast`

English:
theorem ratCast
  given: (x : Rat)
  statement: IsSelfAdjoint (x : R)
  proof: star_ratCast _

中文:
定理 ratCast
  条件: (x : 有理数)
  结论: IsSelfAdjoint (x : R)
  证明: star_ratCast _
-/
protected theorem ratCast (x : Rat) : IsSelfAdjoint (x : R) :=
  star_ratCast _

end DivisionRing

section Semifield

variable [Semifield R] [StarRing R]

/--
theorem `div` / 定理 `div`

English:
theorem div
  given: {x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y)
  statement: IsSelfAdjoint (x / y)
  proof: by
  simp only [isSelfAdjoint_iff, star_div₀, hx.star_eq, hy.star_eq]

中文:
定理 div
  条件: {x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y)
  结论: IsSelfAdjoint (x / y)
  证明: by
  simp only [isSelfAdjoint_iff, star_div₀, hx.star_eq, hy.star_eq]

Depends on / 依赖: hx.star_eq, hy.star_eq, isSelfAdjoint_iff, star_eq
-/
theorem div {x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) : IsSelfAdjoint (x / y) := by
  simp only [isSelfAdjoint_iff, star_div₀, hx.star_eq, hy.star_eq]

end Semifield

section SMul

@[aesop safe apply]
/--
theorem `smul` / 定理 `smul`

English:
theorem smul
  statement: [Star R] [Star A] [SMul R A] [StarModule R A]
  proof: by
  simp only [isSelfAdjoint_iff, star_smul, hr.star_eq, hx.star_eq]

中文:
定理 smul
  结论: [对合 R] [对合 A] [标量乘法 R A] [对合模 R A]
  证明: by
  simp only [isSelfAdjoint_iff, star_smul, hr.star_eq, hx.star_eq]

Depends on / 依赖: hr.star_eq, hx.star_eq, isSelfAdjoint_iff, star_eq, star_smul
-/
theorem smul [Star R] [Star A] [SMul R A] [StarModule R A]
    {r : R} (hr : IsSelfAdjoint r) {x : A} (hx : IsSelfAdjoint x) :
    IsSelfAdjoint (r • x) := by
  simp only [isSelfAdjoint_iff, star_smul, hr.star_eq, hx.star_eq]

/--
theorem `smul_iff` / 定理 `smul_iff`

English:
theorem smul_iff
  statement: [Monoid R] [StarMul R] [Star A]
  proof: by
  refine ⟨fun hrx => ?_, .smul hr⟩
  lift r to Rˣ using hu
  rw [← inv_smul_smul r x]
  replace hr : IsSelfAdjoint r := Units.ext hr.star_eq
  exact hr.inv.smul hrx

中文:
定理 smul_iff
  结论: [幺半群 R] [StarMul R] [对合 A]
  证明: by
  refine ⟨fun hrx => ?_, .smul hr⟩
  lift r to Rˣ using hu
  rw [← inv_smul_smul r x]
  replace hr : IsSelfAdjoint r := Units.ext hr.star_eq
  exact hr.inv.smul hrx

Depends on / 依赖: IsSelfAdjoint, Units.ext, hr.inv.smul, hr.star_eq, inv_smul_smul, replace, star_eq
-/
theorem smul_iff [Monoid R] [StarMul R] [Star A]
    [MulAction R A] [StarModule R A] {r : R} (hr : IsSelfAdjoint r) (hu : IsUnit r) {x : A} :
    IsSelfAdjoint (r • x) ↔ IsSelfAdjoint x := by
  refine ⟨fun hrx => ?_, .smul hr⟩
  lift r to Rˣ using hu
  rw [← inv_smul_smul r x]
  replace hr : IsSelfAdjoint r := Units.ext hr.star_eq
  exact hr.inv.smul hrx

end SMul

end IsSelfAdjoint

variable (R)

/--
Definition of `selfAdjoint` / `selfAdjoint` 的定义

English:
definition selfAdjoint
  signature: [AddGroup R] [StarAddMonoid R]
  body: { x | IsSelfAdjoint x }
  zero_mem' := star_zero R
  add_mem' hx := hx.add
  neg_mem' hx := hx.neg

中文:
定义 selfAdjoint
  签名: [加法群 R] [StarAdd幺半群 R]
  定义体: { x | IsSelfAdjoint x }
  zero_mem' := star_zero R
  add_mem' hx := hx.add
  neg_mem' hx := hx.neg

Depends on / 依赖: IsSelfAdjoint
-/
def selfAdjoint [AddGroup R] [StarAddMonoid R] : AddSubgroup R where
  carrier := { x | IsSelfAdjoint x }
  zero_mem' := star_zero R
  add_mem' hx := hx.add
  neg_mem' hx := hx.neg

/--
Definition of `skewAdjoint` / `skewAdjoint` 的定义

English:
definition skewAdjoint
  signature: [AddCommGroup R] [StarAddMonoid R]
  body: { x | star x = -x }
  zero_mem' := show star (0 : R) = -0 by simp only [star_zero, neg_zero]
  add_mem' := @fun x y (hx : star x = -x) (hy : star y = -y) =>
    show star (x + y) = -(x + y) by rw [star_add x y, hx, hy, neg_add]
  neg_mem' := @fun x (hx : star x = -x) => show star (-x) = - -x by simp only [hx, star_neg]

中文:
定义 skewAdjoint
  签名: [加法交换群 R] [StarAdd幺半群 R]
  定义体: { x | star x = -x }
  zero_mem' := show star (0 : R) = -0 by simp only [star_zero, neg_zero]
  add_mem' := @fun x y (hx : star x = -x) (hy : star y = -y) =>
    show star (x + y) = -(x + y) by rw [star_add x y, hx, hy, neg_add]
  neg_mem' := @fun x (hx : star x = -x) => show star (-x) = - -x by simp only [hx, star_neg]
-/
def skewAdjoint [AddCommGroup R] [StarAddMonoid R] : AddSubgroup R where
  carrier := { x | star x = -x }
  zero_mem' := show star (0 : R) = -0 by simp only [star_zero, neg_zero]
  add_mem' := @fun x y (hx : star x = -x) (hy : star y = -y) =>
    show star (x + y) = -(x + y) by rw [star_add x y, hx, hy, neg_add]
  neg_mem' := @fun x (hx : star x = -x) => show star (-x) = - -x by simp only [hx, star_neg]

variable {R}

namespace selfAdjoint

section AddGroup

variable [AddGroup R] [StarAddMonoid R]

/--
theorem `mem_iff` / 定理 `mem_iff`

English:
theorem mem_iff
  given: {x : R}
  statement: x in selfAdjoint R ↔ star x = x
  proof: by
  rw [← AddSubgroup.mem_carrier]
  exact Iff.rfl

@[simp, norm_cast]

中文:
定理 mem_iff
  条件: {x : R}
  结论: x in selfAdjoint R ↔ star x = x
  证明: by
  rw [← AddSubgroup.mem_carrier]
  exact Iff.rfl

@[simp, norm_cast]

Depends on / 依赖: AddSubgroup, AddSubgroup.mem_carrier, Iff.rfl, mem_carrier
-/
theorem mem_iff {x : R} : x in selfAdjoint R ↔ star x = x := by
  rw [← AddSubgroup.mem_carrier]
  exact Iff.rfl

@[simp, norm_cast]
/--
theorem `star_val_eq` / 定理 `star_val_eq`

English:
theorem star_val_eq
  given: {x : selfAdjoint R}
  statement: star (x : R) = x
  proof: x.prop

中文:
定理 star_val_eq
  条件: {x : selfAdjoint R}
  结论: star (x : R) = x
  证明: x.prop

Depends on / 依赖: x.prop
-/
theorem star_val_eq {x : selfAdjoint R} : star (x : R) = x :=
  x.prop

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (selfAdjoint R)
  body: ⟨0⟩

@[simp]

中文:
实例 :
  签名: 可居 (selfAdjoint R)
  定义体: ⟨0⟩

@[simp]
-/
instance : Inhabited (selfAdjoint R) :=
  ⟨0⟩

@[simp]
/--
lemma `isSelfAdjoint` / 引理 `isSelfAdjoint`

English:
lemma isSelfAdjoint
  given: {x : selfAdjoint R}
  statement: IsSelfAdjoint (x : R)
  proof: by simp [isSelfAdjoint_iff]

中文:
引理 isSelfAdjoint
  条件: {x : selfAdjoint R}
  结论: IsSelfAdjoint (x : R)
  证明: by simp [isSelfAdjoint_iff]

Depends on / 依赖: isSelfAdjoint_iff
-/
lemma isSelfAdjoint {x : selfAdjoint R} : IsSelfAdjoint (x : R) := by simp [isSelfAdjoint_iff]

end AddGroup

/--
Instance `isStarNormal` / 实例 `isStarNormal`

English:
instance isStarNormal
  signature: [NonUnitalRing R] [StarRing R] (x : selfAdjoint R)
  body: x.prop.isStarNormal

中文:
实例 isStarNormal
  签名: [非幺环 R] [对合环 R] (x : selfAdjoint R)
  定义体: x.prop.isStarNormal

Depends on / 依赖: isStarNormal, x.prop.isStarNormal
-/
instance isStarNormal [NonUnitalRing R] [StarRing R] (x : selfAdjoint R) :
    IsStarNormal (x : R) :=
  x.prop.isStarNormal

section Ring

variable [Ring R] [StarRing R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (selfAdjoint R)
  body: ⟨⟨1, .one R⟩⟩

@[simp, norm_cast]

中文:
实例 :
  签名: 幺 (selfAdjoint R)
  定义体: ⟨⟨1, .one R⟩⟩

@[simp, norm_cast]
-/
instance : One (selfAdjoint R) :=
  ⟨⟨1, .one R⟩⟩

@[simp, norm_cast]
/--
theorem `val_one` / 定理 `val_one`

English:
theorem val_one
  statement: ↑(1 : selfAdjoint R) = (1 : R)
  proof: rfl

中文:
定理 val_one
  结论: ↑(1 : selfAdjoint R) = (1 : R)
  证明: rfl
-/
theorem val_one : ↑(1 : selfAdjoint R) = (1 : R) :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: R] : Nontrivial (selfAdjoint R)
  body: ⟨⟨0, 1, ne_of_apply_ne Subtype.val zero_ne_one⟩⟩

中文:
实例 [非平凡
  签名: R] : 非平凡 (selfAdjoint R)
  定义体: ⟨⟨0, 1, ne_of_apply_ne Subtype.val zero_ne_one⟩⟩

Depends on / 依赖: Subtype, Subtype.val, ne_of_apply_ne, zero_ne_one
-/
instance [Nontrivial R] : Nontrivial (selfAdjoint R) :=
  ⟨⟨0, 1, ne_of_apply_ne Subtype.val zero_ne_one⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NatCast (selfAdjoint R)
  body: ⟨n, .natCast _⟩

中文:
实例 :
  签名: 自然数嵌入 (selfAdjoint R)
  定义体: ⟨n, .natCast _⟩

Depends on / 依赖: natCast
-/
instance : NatCast (selfAdjoint R) where
  natCast n := ⟨n, .natCast _⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IntCast (selfAdjoint R)
  body: ⟨n, .intCast _⟩

中文:
实例 :
  签名: 整数嵌入 (selfAdjoint R)
  定义体: ⟨n, .intCast _⟩

Depends on / 依赖: intCast
-/
instance : IntCast (selfAdjoint R) where
  intCast n := ⟨n, .intCast _⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Pow (selfAdjoint R) Nat
  body: ⟨(x : R) ^ n, x.prop.pow n⟩

@[simp, norm_cast]

中文:
实例 :
  签名: 幂 (selfAdjoint R) 自然数
  定义体: ⟨(x : R) ^ n, x.prop.pow n⟩

@[simp, norm_cast]

Depends on / 依赖: x.prop.pow
-/
instance : Pow (selfAdjoint R) Nat where
  pow x n := ⟨(x : R) ^ n, x.prop.pow n⟩

@[simp, norm_cast]
/--
theorem `val_pow` / 定理 `val_pow`

English:
theorem val_pow
  given: (x : selfAdjoint R) (n : Nat)
  statement: ↑(x ^ n) = (x : R) ^ n
  proof: rfl

中文:
定理 val_pow
  条件: (x : selfAdjoint R) (n : 自然数)
  结论: ↑(x ^ n) = (x : R) ^ n
  证明: rfl
-/
theorem val_pow (x : selfAdjoint R) (n : Nat) : ↑(x ^ n) = (x : R) ^ n :=
  rfl

end Ring

section NonUnitalCommRing

variable [NonUnitalCommRing R] [StarRing R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul (selfAdjoint R)
  body: ⟨(x : R) * y, x.prop.mul y.prop⟩

@[simp, norm_cast]

中文:
实例 :
  签名: 乘法 (selfAdjoint R)
  定义体: ⟨(x : R) * y, x.prop.mul y.prop⟩

@[simp, norm_cast]

Depends on / 依赖: x.prop.mul, y.prop
-/
instance : Mul (selfAdjoint R) where
  mul x y := ⟨(x : R) * y, x.prop.mul y.prop⟩

@[simp, norm_cast]
/--
theorem `val_mul` / 定理 `val_mul`

English:
theorem val_mul
  given: (x y : selfAdjoint R)
  statement: ↑(x * y) = (x : R) * y
  proof: rfl

中文:
定理 val_mul
  条件: (x y : selfAdjoint R)
  结论: ↑(x * y) = (x : R) * y
  证明: rfl
-/
theorem val_mul (x y : selfAdjoint R) : ↑(x * y) = (x : R) * y :=
  rfl

end NonUnitalCommRing

section CommRing

variable [CommRing R] [StarRing R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommRing (selfAdjoint R)
  body: Function.Injective.commRing _ Subtype.coe_injective (selfAdjoint R).coe_zero val_one
    (selfAdjoint R).coe_add val_mul (selfAdjoint R).coe_neg (selfAdjoint R).coe_sub
    (by intros; rfl) (by intros; rfl) val_pow
    (fun _ => rfl) fun _ => rfl

中文:
实例 :
  签名: 交换环 (selfAdjoint R)
  定义体: Function.Injective.commRing _ Subtype.coe_injective (selfAdjoint R).coe_zero val_one
    (selfAdjoint R).coe_add val_mul (selfAdjoint R).coe_neg (selfAdjoint R).coe_sub
    (by intros; rfl) (by intros; rfl) val_pow
    (fun _ => rfl) fun _ => rfl

Depends on / 依赖: Function, Function.Injective.commRing, Injective, Subtype, Subtype.coe_injective, coe_add, coe_injective, coe_neg, coe_sub, coe_zero, commRing, intros, selfAdjoint, val_mul, val_one, val_pow
-/
instance : CommRing (selfAdjoint R) :=
  Function.Injective.commRing _ Subtype.coe_injective (selfAdjoint R).coe_zero val_one
    (selfAdjoint R).coe_add val_mul (selfAdjoint R).coe_neg (selfAdjoint R).coe_sub
    (by intros; rfl) (by intros; rfl) val_pow
    (fun _ => rfl) fun _ => rfl

end CommRing

section Field

variable [Field R] [StarRing R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inv (selfAdjoint R)
  body: ⟨x.val⁻¹, x.prop.inv₀⟩

@[simp, norm_cast]

中文:
实例 :
  签名: 取逆 (selfAdjoint R)
  定义体: ⟨x.val⁻¹, x.prop.inv₀⟩

@[simp, norm_cast]

Depends on / 依赖: x.prop.inv, x.val
-/
instance : Inv (selfAdjoint R) where
  inv x := ⟨x.val⁻¹, x.prop.inv₀⟩

@[simp, norm_cast]
/--
theorem `val_inv` / 定理 `val_inv`

English:
theorem val_inv
  given: (x : selfAdjoint R)
  statement: ↑x⁻¹ = (x : R)⁻¹
  proof: rfl

中文:
定理 val_inv
  条件: (x : selfAdjoint R)
  结论: ↑x⁻¹ = (x : R)⁻¹
  证明: rfl
-/
theorem val_inv (x : selfAdjoint R) : ↑x⁻¹ = (x : R)⁻¹ :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Div (selfAdjoint R)
  body: ⟨x / y, x.prop.div y.prop⟩

@[simp, norm_cast]

中文:
实例 :
  签名: 除法 (selfAdjoint R)
  定义体: ⟨x / y, x.prop.div y.prop⟩

@[simp, norm_cast]

Depends on / 依赖: x.prop.div, y.prop
-/
instance : Div (selfAdjoint R) where
  div x y := ⟨x / y, x.prop.div y.prop⟩

@[simp, norm_cast]
/--
theorem `val_div` / 定理 `val_div`

English:
theorem val_div
  given: (x y : selfAdjoint R)
  statement: ↑(x / y) = (x / y : R)
  proof: rfl

中文:
定理 val_div
  条件: (x y : selfAdjoint R)
  结论: ↑(x / y) = (x / y : R)
  证明: rfl
-/
theorem val_div (x y : selfAdjoint R) : ↑(x / y) = (x / y : R) :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Pow (selfAdjoint R) Int
  body: ⟨(x : R) ^ z, x.prop.zpow₀ z⟩

@[simp, norm_cast]

中文:
实例 :
  签名: 幂 (selfAdjoint R) 整数
  定义体: ⟨(x : R) ^ z, x.prop.zpow₀ z⟩

@[simp, norm_cast]

Depends on / 依赖: x.prop.zpow
-/
instance : Pow (selfAdjoint R) Int where
  pow x z := ⟨(x : R) ^ z, x.prop.zpow₀ z⟩

@[simp, norm_cast]
/--
theorem `val_zpow` / 定理 `val_zpow`

English:
theorem val_zpow
  given: (x : selfAdjoint R) (z : Int)
  statement: ↑(x ^ z) = (x : R) ^ z
  proof: rfl

中文:
定理 val_zpow
  条件: (x : selfAdjoint R) (z : 整数)
  结论: ↑(x ^ z) = (x : R) ^ z
  证明: rfl
-/
theorem val_zpow (x : selfAdjoint R) (z : Int) : ↑(x ^ z) = (x : R) ^ z :=
  rfl

/--
Instance `instNNRatCast` / 实例 `instNNRatCast`

English:
instance instNNRatCast
  signature: : NNRatCast (selfAdjoint R) where
  body: ⟨q, .nnratCast q⟩

中文:
实例 instNNRatCast
  签名: : 非负有理数嵌入 (selfAdjoint R) where
  定义体: ⟨q, .nnratCast q⟩

Depends on / 依赖: nnratCast
-/
instance instNNRatCast : NNRatCast (selfAdjoint R) where
  nnratCast q := ⟨q, .nnratCast q⟩

/--
Instance `instRatCast` / 实例 `instRatCast`

English:
instance instRatCast
  signature: : RatCast (selfAdjoint R) where
  body: ⟨q, .ratCast q⟩

中文:
实例 instRatCast
  签名: : 有理数嵌入 (selfAdjoint R) where
  定义体: ⟨q, .ratCast q⟩

Depends on / 依赖: ratCast
-/
instance instRatCast : RatCast (selfAdjoint R) where
  ratCast q := ⟨q, .ratCast q⟩

/--
lemma `val_nnratCast` / 引理 `val_nnratCast`

English:
lemma val_nnratCast
  given: (q : Rat>=0)
  statement: (q : selfAdjoint R) = (q : R)
  proof: rfl

中文:
引理 val_nnratCast
  条件: (q : 有理数>=0)
  结论: (q : selfAdjoint R) = (q : R)
  证明: rfl
-/
@[simp, norm_cast] lemma val_nnratCast (q : Rat>=0) : (q : selfAdjoint R) = (q : R) := rfl
/--
lemma `val_ratCast` / 引理 `val_ratCast`

English:
lemma val_ratCast
  given: (q : Rat)
  statement: (q : selfAdjoint R) = (q : R)
  proof: rfl

中文:
引理 val_ratCast
  条件: (q : 有理数)
  结论: (q : selfAdjoint R) = (q : R)
  证明: rfl
-/
@[simp, norm_cast] lemma val_ratCast (q : Rat) : (q : selfAdjoint R) = (q : R) := rfl

/--
Instance `instSMulNNRat` / 实例 `instSMulNNRat`

English:
instance instSMulNNRat
  signature: : SMul Rat>=0 (selfAdjoint R) where
  body: ⟨a • (x : R), by rw [NNRat.smul_def]; exact .mul (.nnratCast a) x.prop⟩

中文:
实例 instSMulNNRat
  签名: : 标量乘法 有理数>=0 (selfAdjoint R) where
  定义体: ⟨a • (x : R), by rw [NNRat.smul_def]; exact .mul (.nnratCast a) x.prop⟩

Depends on / 依赖: NNRat.smul_def, nnratCast, smul_def, x.prop
-/
instance instSMulNNRat : SMul Rat>=0 (selfAdjoint R) where
  smul a x := ⟨a • (x : R), by rw [NNRat.smul_def]; exact .mul (.nnratCast a) x.prop⟩

/--
Instance `instSMulRat` / 实例 `instSMulRat`

English:
instance instSMulRat
  signature: : SMul Rat (selfAdjoint R) where
  body: ⟨a • (x : R), by rw [Rat.smul_def]; exact .mul (.ratCast a) x.prop⟩

中文:
实例 instSMulRat
  签名: : 标量乘法 有理数 (selfAdjoint R) where
  定义体: ⟨a • (x : R), by rw [Rat.smul_def]; exact .mul (.ratCast a) x.prop⟩

Depends on / 依赖: Rat.smul_def, ratCast, smul_def, x.prop
-/
instance instSMulRat : SMul Rat (selfAdjoint R) where
  smul a x := ⟨a • (x : R), by rw [Rat.smul_def]; exact .mul (.ratCast a) x.prop⟩

/--
lemma `val_nnqsmul` / 引理 `val_nnqsmul`

English:
lemma val_nnqsmul
  given: (q : Rat>=0) (x : selfAdjoint R)
  statement: ↑(q • x) = q • (x : R)
  proof: rfl

中文:
引理 val_nnqsmul
  条件: (q : 有理数>=0) (x : selfAdjoint R)
  结论: ↑(q • x) = q • (x : R)
  证明: rfl
-/
@[simp, norm_cast] lemma val_nnqsmul (q : Rat>=0) (x : selfAdjoint R) : ↑(q • x) = q • (x : R) := rfl
/--
lemma `val_qsmul` / 引理 `val_qsmul`

English:
lemma val_qsmul
  given: (q : Rat) (x : selfAdjoint R)
  statement: ↑(q • x) = q • (x : R)
  proof: rfl

中文:
引理 val_qsmul
  条件: (q : 有理数) (x : selfAdjoint R)
  结论: ↑(q • x) = q • (x : R)
  证明: rfl
-/
@[simp, norm_cast] lemma val_qsmul (q : Rat) (x : selfAdjoint R) : ↑(q • x) = q • (x : R) := rfl

/--
Instance `instField` / 实例 `instField`

English:
instance instField
  signature: : Field (selfAdjoint R)
  body: Subtype.coe_injective.field _ (selfAdjoint R).coe_zero val_one
    (selfAdjoint R).coe_add val_mul (selfAdjoint R).coe_neg (selfAdjoint R).coe_sub
    val_inv val_div (swap (selfAdjoint R).coe_nsmul) (by intros; rfl) val_nnqsmul
    val_qsmul val_pow val_zpow (fun _ => rfl) (fun _ => rfl) val_nnratCast val_ratCast

中文:
实例 instField
  签名: : 域 (selfAdjoint R)
  定义体: Subtype.coe_injective.field _ (selfAdjoint R).coe_zero val_one
    (selfAdjoint R).coe_add val_mul (selfAdjoint R).coe_neg (selfAdjoint R).coe_sub
    val_inv val_div (swap (selfAdjoint R).coe_nsmul) (by intros; rfl) val_nnqsmul
    val_qsmul val_pow val_zpow (fun _ => rfl) (fun _ => rfl) val_nnratCast val_ratCast

Depends on / 依赖: Subtype, Subtype.coe_injective.field, coe_add, coe_injective, coe_neg, coe_nsmul, coe_sub, coe_zero, intros, selfAdjoint, val_div, val_inv, val_mul, val_nnqsmul, val_nnratCast, val_one, val_pow, val_qsmul, val_ratCast, val_zpow
-/
instance instField : Field (selfAdjoint R) :=
  Subtype.coe_injective.field _ (selfAdjoint R).coe_zero val_one
    (selfAdjoint R).coe_add val_mul (selfAdjoint R).coe_neg (selfAdjoint R).coe_sub
    val_inv val_div (swap (selfAdjoint R).coe_nsmul) (by intros; rfl) val_nnqsmul
    val_qsmul val_pow val_zpow (fun _ => rfl) (fun _ => rfl) val_nnratCast val_ratCast

end Field

section SMul

variable [Star R] [TrivialStar R] [AddGroup A] [StarAddMonoid A]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: R A] [StarModule R A] : SMul R (selfAdjoint A) where
  body: ⟨r • (x : A), (IsSelfAdjoint.all _).smul x.prop⟩

@[simp, norm_cast]

中文:
实例 [标量乘法
  签名: R A] [对合模 R A] : 标量乘法 R (selfAdjoint A) where
  定义体: ⟨r • (x : A), (IsSelfAdjoint.all _).smul x.prop⟩

@[simp, norm_cast]

Depends on / 依赖: IsSelfAdjoint, IsSelfAdjoint.all, x.prop
-/
instance [SMul R A] [StarModule R A] : SMul R (selfAdjoint A) where
  smul r x := ⟨r • (x : A), (IsSelfAdjoint.all _).smul x.prop⟩

@[simp, norm_cast]
/--
theorem `val_smul` / 定理 `val_smul`

English:
theorem val_smul
  given: [SMul R A] [StarModule R A] (r : R) (x : selfAdjoint A)
  statement: ↑(r • x) = r • (x : A)
  proof: rfl

中文:
定理 val_smul
  条件: [标量乘法 R A] [对合模 R A] (r : R) (x : selfAdjoint A)
  结论: ↑(r • x) = r • (x : A)
  证明: rfl
-/
theorem val_smul [SMul R A] [StarModule R A] (r : R) (x : selfAdjoint A) : ↑(r • x) = r • (x : A) :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: R] [MulAction R A] [StarModule R A] : MulAction R (selfAdjoint A)
  body: Function.Injective.mulAction Subtype.val Subtype.coe_injective val_smul

中文:
实例 [幺半群
  签名: R] [乘法作用 R A] [对合模 R A] : 乘法作用 R (selfAdjoint A)
  定义体: Function.Injective.mulAction Subtype.val Subtype.coe_injective val_smul

Depends on / 依赖: Function, Function.Injective.mulAction, Injective, Subtype, Subtype.coe_injective, Subtype.val, coe_injective, mulAction, val_smul
-/
instance [Monoid R] [MulAction R A] [StarModule R A] : MulAction R (selfAdjoint A) :=
  Function.Injective.mulAction Subtype.val Subtype.coe_injective val_smul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: R] [DistribMulAction R A] [StarModule R A] : DistribMulAction R (selfAdjoint A)
  body: Function.Injective.distribMulAction (selfAdjoint A).subtype Subtype.coe_injective val_smul

中文:
实例 [幺半群
  签名: R] [分配乘法作用 R A] [对合模 R A] : 分配乘法作用 R (selfAdjoint A)
  定义体: Function.Injective.distribMulAction (selfAdjoint A).subtype Subtype.coe_injective val_smul

Depends on / 依赖: Function, Function.Injective.distribMulAction, Injective, Subtype, Subtype.coe_injective, coe_injective, distribMulAction, selfAdjoint, subtype, val_smul
-/
instance [Monoid R] [DistribMulAction R A] [StarModule R A] : DistribMulAction R (selfAdjoint A) :=
  Function.Injective.distribMulAction (selfAdjoint A).subtype Subtype.coe_injective val_smul

end SMul

section Module

variable [Star R] [TrivialStar R] [AddCommGroup A] [StarAddMonoid A]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semiring
  signature: R] [Module R A] [StarModule R A] : Module R (selfAdjoint A)
  body: Function.Injective.module R (selfAdjoint A).subtype Subtype.coe_injective val_smul

中文:
实例 [半环
  签名: R] [模 R A] [对合模 R A] : 模 R (selfAdjoint A)
  定义体: Function.Injective.module R (selfAdjoint A).subtype Subtype.coe_injective val_smul

Depends on / 依赖: Function, Function.Injective.module, Injective, Subtype, Subtype.coe_injective, coe_injective, module, selfAdjoint, subtype, val_smul
-/
instance [Semiring R] [Module R A] [StarModule R A] : Module R (selfAdjoint A) :=
  Function.Injective.module R (selfAdjoint A).subtype Subtype.coe_injective val_smul

end Module

end selfAdjoint

namespace skewAdjoint

section AddGroup

variable [AddCommGroup R] [StarAddMonoid R]

/--
theorem `mem_iff` / 定理 `mem_iff`

English:
theorem mem_iff
  given: {x : R}
  statement: x in skewAdjoint R ↔ star x = -x
  proof: by
  rw [← AddSubgroup.mem_carrier]
  exact Iff.rfl

@[simp, norm_cast]

中文:
定理 mem_iff
  条件: {x : R}
  结论: x in skewAdjoint R ↔ star x = -x
  证明: by
  rw [← AddSubgroup.mem_carrier]
  exact Iff.rfl

@[simp, norm_cast]

Depends on / 依赖: AddSubgroup, AddSubgroup.mem_carrier, Iff.rfl, mem_carrier
-/
theorem mem_iff {x : R} : x in skewAdjoint R ↔ star x = -x := by
  rw [← AddSubgroup.mem_carrier]
  exact Iff.rfl

@[simp, norm_cast]
/--
theorem `star_val_eq` / 定理 `star_val_eq`

English:
theorem star_val_eq
  given: {x : skewAdjoint R}
  statement: star (x : R) = -x
  proof: x.prop

中文:
定理 star_val_eq
  条件: {x : skewAdjoint R}
  结论: star (x : R) = -x
  证明: x.prop

Depends on / 依赖: x.prop
-/
theorem star_val_eq {x : skewAdjoint R} : star (x : R) = -x :=
  x.prop

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (skewAdjoint R)
  body: ⟨0⟩

中文:
实例 :
  签名: 可居 (skewAdjoint R)
  定义体: ⟨0⟩
-/
instance : Inhabited (skewAdjoint R) :=
  ⟨0⟩

end AddGroup

section Ring

variable [Ring R] [StarRing R]

/--
theorem `conjugate` / 定理 `conjugate`

English:
theorem conjugate
  given: {x : R} (hx : x in skewAdjoint R) (z : R)
  statement: z * x * star z in skewAdjoint R
  proof: by
  simp only [mem_iff, star_mul, star_star, mem_iff.mp hx, neg_mul, mul_neg, mul_assoc]

中文:
定理 conjugate
  条件: {x : R} (hx : x in skewAdjoint R) (z : R)
  结论: z * x * star z in skewAdjoint R
  证明: by
  simp only [mem_iff, star_mul, star_star, mem_iff.mp hx, neg_mul, mul_neg, mul_assoc]

Depends on / 依赖: mem_iff, mem_iff.mp, mul_assoc, mul_neg, neg_mul, star_mul, star_star
-/
theorem conjugate {x : R} (hx : x in skewAdjoint R) (z : R) : z * x * star z in skewAdjoint R := by
  simp only [mem_iff, star_mul, star_star, mem_iff.mp hx, neg_mul, mul_neg, mul_assoc]

/--
theorem `conjugate'` / 定理 `conjugate'`

English:
theorem conjugate'
  given: {x : R} (hx : x in skewAdjoint R) (z : R)
  statement: star z * x * z in skewAdjoint R
  proof: by
  simp only [mem_iff, star_mul, star_star, mem_iff.mp hx, neg_mul, mul_neg, mul_assoc]

中文:
定理 conjugate'
  条件: {x : R} (hx : x in skewAdjoint R) (z : R)
  结论: star z * x * z in skewAdjoint R
  证明: by
  simp only [mem_iff, star_mul, star_star, mem_iff.mp hx, neg_mul, mul_neg, mul_assoc]

Depends on / 依赖: mem_iff, mem_iff.mp, mul_assoc, mul_neg, neg_mul, star_mul, star_star
-/
theorem conjugate' {x : R} (hx : x in skewAdjoint R) (z : R) : star z * x * z in skewAdjoint R := by
  simp only [mem_iff, star_mul, star_star, mem_iff.mp hx, neg_mul, mul_neg, mul_assoc]

/--
theorem `isStarNormal_of_mem` / 定理 `isStarNormal_of_mem`

English:
theorem isStarNormal_of_mem
  given: {x : R} (hx : x in skewAdjoint R)
  statement: IsStarNormal x
  proof: ⟨by
    simp only [mem_iff] at hx
    simp only [hx, Commute.neg_left, Commute.refl]⟩

中文:
定理 isStarNormal_of_mem
  条件: {x : R} (hx : x in skewAdjoint R)
  结论: 是StarNormal x
  证明: ⟨by
    simp only [mem_iff] at hx
    simp only [hx, Commute.neg_left, Commute.refl]⟩

Depends on / 依赖: Commute, Commute.neg_left, Commute.refl, mem_iff, neg_left
-/
theorem isStarNormal_of_mem {x : R} (hx : x in skewAdjoint R) : IsStarNormal x :=
  ⟨by
    simp only [mem_iff] at hx
    simp only [hx, Commute.neg_left, Commute.refl]⟩

instance (x : skewAdjoint R) : IsStarNormal (x : R) :=
  isStarNormal_of_mem (SetLike.coe_mem _)

end Ring

section SMul

variable [Star R] [TrivialStar R] [AddCommGroup A] [StarAddMonoid A]

@[aesop 90% (rule_sets := [SetLike])]
/--
theorem `smul_mem` / 定理 `smul_mem`

English:
theorem smul_mem
  statement: [Monoid R] [DistribMulAction R A] [StarModule R A] (r : R) {x : A}
  proof: by
  rw [mem_iff]; rw [star_smul]; rw [star_trivial]; rw [mem_iff.mp h]; rw [smul_neg r]

中文:
定理 smul_mem
  结论: [幺半群 R] [分配乘法作用 R A] [对合模 R A] (r : R) {x : A}
  证明: by
  rw [mem_iff]; rw [star_smul]; rw [star_trivial]; rw [mem_iff.mp h]; rw [smul_neg r]

Depends on / 依赖: mem_iff, mem_iff.mp, smul_neg, star_smul, star_trivial
-/
theorem smul_mem [Monoid R] [DistribMulAction R A] [StarModule R A] (r : R) {x : A}
    (h : x in skewAdjoint A) : r • x in skewAdjoint A := by
  rw [mem_iff]; rw [star_smul]; rw [star_trivial]; rw [mem_iff.mp h]; rw [smul_neg r]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: R] [DistribMulAction R A] [StarModule R A] : SMul R (skewAdjoint A) where
  body: ⟨r • (x : A), smul_mem r x.prop⟩

@[simp, norm_cast]

中文:
实例 [幺半群
  签名: R] [分配乘法作用 R A] [对合模 R A] : 标量乘法 R (skewAdjoint A) where
  定义体: ⟨r • (x : A), smul_mem r x.prop⟩

@[simp, norm_cast]

Depends on / 依赖: smul_mem, x.prop
-/
instance [Monoid R] [DistribMulAction R A] [StarModule R A] : SMul R (skewAdjoint A) where
  smul r x := ⟨r • (x : A), smul_mem r x.prop⟩

@[simp, norm_cast]
/--
theorem `val_smul` / 定理 `val_smul`

English:
theorem val_smul
  given: [Monoid R] [DistribMulAction R A] [StarModule R A] (r : R) (x : skewAdjoint A)
  proof: rfl

中文:
定理 val_smul
  条件: [幺半群 R] [分配乘法作用 R A] [对合模 R A] (r : R) (x : skewAdjoint A)
  证明: rfl
-/
theorem val_smul [Monoid R] [DistribMulAction R A] [StarModule R A] (r : R) (x : skewAdjoint A) :
    ↑(r • x) = r • (x : A) :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: R] [DistribMulAction R A] [StarModule R A] : DistribMulAction R (skewAdjoint A)
  body: Function.Injective.distribMulAction (skewAdjoint A).subtype Subtype.coe_injective val_smul

中文:
实例 [幺半群
  签名: R] [分配乘法作用 R A] [对合模 R A] : 分配乘法作用 R (skewAdjoint A)
  定义体: Function.Injective.distribMulAction (skewAdjoint A).subtype Subtype.coe_injective val_smul

Depends on / 依赖: Function, Function.Injective.distribMulAction, Injective, Subtype, Subtype.coe_injective, coe_injective, distribMulAction, skewAdjoint, subtype, val_smul
-/
instance [Monoid R] [DistribMulAction R A] [StarModule R A] : DistribMulAction R (skewAdjoint A) :=
  Function.Injective.distribMulAction (skewAdjoint A).subtype Subtype.coe_injective val_smul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semiring
  signature: R] [Module R A] [StarModule R A] : Module R (skewAdjoint A)
  body: Function.Injective.module R (skewAdjoint A).subtype Subtype.coe_injective val_smul

中文:
实例 [半环
  签名: R] [模 R A] [对合模 R A] : 模 R (skewAdjoint A)
  定义体: Function.Injective.module R (skewAdjoint A).subtype Subtype.coe_injective val_smul

Depends on / 依赖: Function, Function.Injective.module, Injective, Subtype, Subtype.coe_injective, coe_injective, module, skewAdjoint, subtype, val_smul
-/
instance [Semiring R] [Module R A] [StarModule R A] : Module R (skewAdjoint A) :=
  Function.Injective.module R (skewAdjoint A).subtype Subtype.coe_injective val_smul

end SMul

end skewAdjoint

/--
theorem `IsSelfAdjoint.smul_mem_skewAdjoint` / 定理 `IsSelfAdjoint.smul_mem_skewAdjoint`

English:
theorem IsSelfAdjoint.smul_mem_skewAdjoint
  statement: [Ring R] [AddCommGroup A] [Module R A] [StarAddMonoid R]
  proof: (star_smul _ _).trans (congr_arg₂ _ hr ha).trans neg_smul _ _

中文:
定理 IsSelfAdjoint.smul_mem_skewAdjoint
  结论: [环 R] [加法交换群 A] [模 R A] [StarAdd幺半群 R]
  证明: (star_smul _ _).trans (congr_arg₂ _ hr ha).trans neg_smul _ _

Depends on / 依赖: neg_smul, star_smul
-/
theorem IsSelfAdjoint.smul_mem_skewAdjoint [Ring R] [AddCommGroup A] [Module R A] [StarAddMonoid R]
    [StarAddMonoid A] [StarModule R A] {r : R} (hr : r in skewAdjoint R) {a : A}
    (ha : IsSelfAdjoint a) : r • a in skewAdjoint A :=
(star_smul _ _).trans (congr_arg₂ _ hr ha).trans neg_smul _ _

/--
theorem `isSelfAdjoint_smul_of_mem_skewAdjoint` / 定理 `isSelfAdjoint_smul_of_mem_skewAdjoint`

English:
theorem isSelfAdjoint_smul_of_mem_skewAdjoint
  statement: [Ring R] [AddCommGroup A] [Module R A]
  proof: (star_smul _ _).trans (congr_arg₂ _ hr ha).trans neg_smul_neg _ _

中文:
定理 isSelfAdjoint_smul_of_mem_skewAdjoint
  结论: [环 R] [加法交换群 A] [模 R A]
  证明: (star_smul _ _).trans (congr_arg₂ _ hr ha).trans neg_smul_neg _ _

Depends on / 依赖: neg_smul_neg, star_smul
-/
theorem isSelfAdjoint_smul_of_mem_skewAdjoint [Ring R] [AddCommGroup A] [Module R A]
    [StarAddMonoid R] [StarAddMonoid A] [StarModule R A] {r : R} (hr : r in skewAdjoint R) {a : A}
    (ha : a in skewAdjoint A) : IsSelfAdjoint (r • a) :=
(star_smul _ _).trans (congr_arg₂ _ hr ha).trans neg_smul_neg _ _

/--
Instance `IsStarNormal.zero` / 实例 `IsStarNormal.zero`

English:
instance IsStarNormal.zero
  signature: [NonUnitalNonAssocSemiring R]
  body: ⟨by simp only [Commute.refl, star_zero]⟩

中文:
实例 是StarNormal.zero
  签名: [非幺非结合半环 R]
  定义体: ⟨by simp only [Commute.refl, star_zero]⟩
-/
protected instance IsStarNormal.zero [NonUnitalNonAssocSemiring R]
    [StarAddMonoid R] : IsStarNormal (0 : R) :=
  ⟨by simp only [Commute.refl, star_zero]⟩

/--
Instance `IsStarNormal.one` / 实例 `IsStarNormal.one`

English:
instance IsStarNormal.one
  signature: [MulOneClass R] [StarMul R]
  body: ⟨by simp only [Commute.refl, star_one]⟩

中文:
实例 是StarNormal.one
  签名: [MulOne类 R] [StarMul R]
  定义体: ⟨by simp only [Commute.refl, star_one]⟩
-/
protected instance IsStarNormal.one [MulOneClass R] [StarMul R] : IsStarNormal (1 : R) :=
  ⟨by simp only [Commute.refl, star_one]⟩

/--
Instance `IsStarNormal.star` / 实例 `IsStarNormal.star`

English:
instance IsStarNormal.star
  signature: [Mul R] [StarMul R] {x : R} [IsStarNormal x]
  body: ⟨show star (star x) * star x = star x * star (star x) by rw [star_star, star_comm_self']⟩

中文:
实例 是StarNormal.star
  签名: [乘法 R] [StarMul R] {x : R} [是StarNormal x]
  定义体: ⟨show star (star x) * star x = star x * star (star x) by rw [star_star, star_comm_self']⟩
-/
protected instance IsStarNormal.star [Mul R] [StarMul R] {x : R} [IsStarNormal x] :
    IsStarNormal (star x) :=
  ⟨show star (star x) * star x = star x * star (star x) by rw [star_star, star_comm_self']⟩

/--
Instance `IsStarNormal.neg` / 实例 `IsStarNormal.neg`

English:
instance IsStarNormal.neg
  signature: [NonUnitalNonAssocRing R]
  body: ⟨show star (-x) * -x = -x * star (-x) by simp_rw [star_neg, neg_mul_neg, star_comm_self']⟩

中文:
实例 是StarNormal.neg
  签名: [非幺非结合环 R]
  定义体: ⟨show star (-x) * -x = -x * star (-x) by simp_rw [star_neg, neg_mul_neg, star_comm_self']⟩
-/
protected instance IsStarNormal.neg [NonUnitalNonAssocRing R]
    [StarAddMonoid R] {x : R} [IsStarNormal x] : IsStarNormal (-x) :=
  ⟨show star (-x) * -x = -x * star (-x) by simp_rw [star_neg, neg_mul_neg, star_comm_self']⟩

/--
Instance `IsStarNormal.val_inv` / 实例 `IsStarNormal.val_inv`

English:
instance IsStarNormal.val_inv
  signature: [Monoid R] [StarMul R] {x : Rˣ} [IsStarNormal (x : R)]
  body: by simpa [← Units.coe_star_inv, -Commute.units_val_iff] using star_comm_self

中文:
实例 是StarNormal.val_inv
  签名: [幺半群 R] [StarMul R] {x : Rˣ} [是StarNormal (x : R)]
  定义体: by simpa [← Units.coe_star_inv, -Commute.units_val_iff] using star_comm_self
-/
protected instance IsStarNormal.val_inv [Monoid R] [StarMul R] {x : Rˣ} [IsStarNormal (x : R)] :
    IsStarNormal (↑x⁻¹ : R) where
  star_comm_self := by simpa [← Units.coe_star_inv, -Commute.units_val_iff] using star_comm_self

/--
Instance `IsStarNormal.map` / 实例 `IsStarNormal.map`

English:
instance IsStarNormal.map
  signature: {F R S : Type*} [Mul R] [Star R] [Mul S] [Star S]
  body: by simpa [map_star] using! congr(f $(hr.star_comm_self))

中文:
实例 是StarNormal.map
  签名: {F R S : 类型} [乘法 R] [对合 R] [乘法 S] [对合 S]
  定义体: by simpa [map_star] using! congr(f $(hr.star_comm_self))
-/
protected instance IsStarNormal.map {F R S : Type*} [Mul R] [Star R] [Mul S] [Star S]
    [FunLike F R S] [MulHomClass F R S] [StarHomClass F R S] (f : F) (r : R) [hr : IsStarNormal r] :
    IsStarNormal (f r) where
  star_comm_self := by simpa [map_star] using! congr(f $(hr.star_comm_self))

/--
Instance `IsStarNormal.smul` / 实例 `IsStarNormal.smul`

English:
instance IsStarNormal.smul
  signature: {R A : Type*} [SMul R A] [Star R] [Star A] [Mul A]
  body: star_smul r a ▸ ha.star_comm_self.smul_left (star r)

中文:
实例 是StarNormal.smul
  签名: {R A : 类型} [标量乘法 R A] [对合 R] [对合 A] [乘法 A]
  定义体: star_smul r a ▸ ha.star_comm_self.smul_left (star r)
-/
protected instance IsStarNormal.smul {R A : Type*} [SMul R A] [Star R] [Star A] [Mul A]
    [StarModule R A] [SMulCommClass R A A] [IsScalarTower R A A]
    (r : R) (a : A) [ha : IsStarNormal a] : IsStarNormal (r • a) where
.smul_right r star_comm_self := star_smul r a ▸ ha.star_comm_self.smul_left (star r)

-- see Note [lower instance priority]
instance (priority := 100) TrivialStar.isStarNormal [Mul R] [StarMul R] [TrivialStar R]
    {x : R} : IsStarNormal x :=
  ⟨by rw [star_trivial]⟩

-- see Note [lower instance priority]
instance (priority := 100) CommMonoid.isStarNormal [CommMonoid R] [StarMul R] {x : R} :
    IsStarNormal x :=
  ⟨mul_comm _ _⟩

/--
theorem `Commute.isStarNormal_add` / 定理 `Commute.isStarNormal_add`

English:
theorem Commute.isStarNormal_add
  statement: [NonUnitalNonAssocSemiring R] [StarRing R] {a b : R}
  proof: by
  rw [isStarNormal_iff] at ha hb ⊢
  have := _root_.star_star b ▸ hab.star_star
  simp only [star_add, commute_iff_eq, mul_add, add_mul]
  rw [ha.eq]; rw [hb.eq]; rw [add_add_add_comm]; rw [hab.eq]; rw [this.eq]

中文:
定理 Commute.isStarNormal_add
  结论: [非幺非结合半环 R] [对合环 R] {a b : R}
  证明: by
  rw [isStarNormal_iff] at ha hb ⊢
  have := _root_.star_star b ▸ hab.star_star
  simp only [star_add, commute_iff_eq, mul_add, add_mul]
  rw [ha.eq]; rw [hb.eq]; rw [add_add_add_comm]; rw [hab.eq]; rw [this.eq]

Depends on / 依赖: _root_, _root_.star_star, add_add_add_comm, add_mul, commute_iff_eq, ha.eq, hab.eq, hab.star_star, hb.eq, isStarNormal_iff, mul_add, star_add, star_star, this.eq
-/
theorem Commute.isStarNormal_add [NonUnitalNonAssocSemiring R] [StarRing R] {a b : R}
    (hab : Commute a (star b)) [ha : IsStarNormal a] [hb : IsStarNormal b] :
    IsStarNormal (a + b) := by
  rw [isStarNormal_iff] at ha hb ⊢
  have := _root_.star_star b ▸ hab.star_star
  simp only [star_add, commute_iff_eq, mul_add, add_mul]
  rw [ha.eq]; rw [hb.eq]; rw [add_add_add_comm]; rw [hab.eq]; rw [this.eq]

/--
theorem `Commute.isStarNormal_sub` / 定理 `Commute.isStarNormal_sub`

English:
theorem Commute.isStarNormal_sub
  statement: [NonUnitalNonAssocRing R] [StarRing R] {a b : R}
  proof: sub_eq_add_neg a b ▸ (star_neg b ▸ hab.neg_right).isStarNormal_add

中文:
定理 Commute.isStarNormal_sub
  结论: [非幺非结合环 R] [对合环 R] {a b : R}
  证明: sub_eq_add_neg a b ▸ (star_neg b ▸ hab.neg_right).isStarNormal_add

Depends on / 依赖: hab.neg_right, isStarNormal_add, neg_right, star_neg, sub_eq_add_neg
-/
theorem Commute.isStarNormal_sub [NonUnitalNonAssocRing R] [StarRing R] {a b : R}
    (hab : Commute a (star b)) [ha : IsStarNormal a] [hb : IsStarNormal b] :
    IsStarNormal (a - b) :=
  sub_eq_add_neg a b ▸ (star_neg b ▸ hab.neg_right).isStarNormal_add

/--
Instance `IsStarNormal.one_add` / 实例 `IsStarNormal.one_add`

English:
instance IsStarNormal.one_add
  signature: [NonAssocSemiring R] [StarRing R] {a : R}
  body: .isStarNormal_add Commute.one_left (star a)

中文:
实例 是StarNormal.one_add
  签名: [非结合半环 R] [对合环 R] {a : R}
  定义体: .isStarNormal_add Commute.one_left (star a)

Depends on / 依赖: Commute, Commute.one_left, isStarNormal_add, one_left
-/
instance IsStarNormal.one_add [NonAssocSemiring R] [StarRing R] {a : R}
    [ha : IsStarNormal a] : IsStarNormal (1 + a) :=
.isStarNormal_add Commute.one_left (star a)

/--
Instance `IsStarNormal.one_sub` / 实例 `IsStarNormal.one_sub`

English:
instance IsStarNormal.one_sub
  signature: [NonAssocRing R] [StarRing R] {a : R}
  body: .isStarNormal_sub Commute.one_left (star a)

中文:
实例 是StarNormal.one_sub
  签名: [非结合环 R] [对合环 R] {a : R}
  定义体: .isStarNormal_sub Commute.one_left (star a)

Depends on / 依赖: Commute, Commute.one_left, isStarNormal_sub, one_left
-/
instance IsStarNormal.one_sub [NonAssocRing R] [StarRing R] {a : R}
    [ha : IsStarNormal a] : IsStarNormal (1 - a) :=
.isStarNormal_sub Commute.one_left (star a)

/--
lemma `IsSelfAdjoint.commute_of_mul_eq_zero` / 引理 `IsSelfAdjoint.commute_of_mul_eq_zero`

English:
lemma IsSelfAdjoint.commute_of_mul_eq_zero
  statement: [NonUnitalNonAssocRing R] [StarRing R]
  proof: by
  have : b * a = 0 := by simpa [ha.star_eq, hb.star_eq] using congr(star $hab)
  grind [commute_iff_eq]

中文:
引理 IsSelfAdjoint.commute_of_mul_eq_zero
  结论: [非幺非结合环 R] [对合环 R]
  证明: by
  have : b * a = 0 := by simpa [ha.star_eq, hb.star_eq] using congr(star $hab)
  grind [commute_iff_eq]

Depends on / 依赖: commute_iff_eq, ha.star_eq, hb.star_eq, star_eq
-/
lemma IsSelfAdjoint.commute_of_mul_eq_zero [NonUnitalNonAssocRing R] [StarRing R]
    {a b : R} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) (hab : a * b = 0) :
    Commute a b := by
  have : b * a = 0 := by simpa [ha.star_eq, hb.star_eq] using congr(star $hab)
  grind [commute_iff_eq]

namespace Pi
variable {ι : Type*} {α : ι -> Type*} [forall i, Star (α i)] {f : forall i, α i}

/--
lemma `isSelfAdjoint` / 引理 `isSelfAdjoint`

English:
lemma isSelfAdjoint
  statement: IsSelfAdjoint f ↔ forall i, IsSelfAdjoint (f i)
  proof: funext_iff

alias ⟨_root_.IsSelfAdjoint.apply, _⟩ := Pi.isSelfAdjoint

中文:
引理 isSelfAdjoint
  结论: IsSelfAdjoint f ↔ 对任意 i, IsSelfAdjoint (f i)
  证明: funext_iff

alias ⟨_root_.IsSelfAdjoint.apply, _⟩ := Pi.isSelfAdjoint
-/
protected lemma isSelfAdjoint : IsSelfAdjoint f ↔ forall i, IsSelfAdjoint (f i) := funext_iff

alias ⟨_root_.IsSelfAdjoint.apply, _⟩ := Pi.isSelfAdjoint

end Pi
