/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Eric Wieser
-/
module

public import Mathlib.Algebra.Group.Submonoid.Finsupp
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.RingTheory.Adjoin.Basic
public import Mathlib.RingTheory.GradedAlgebra.FiniteType
public import Mathlib.RingTheory.GradedAlgebra.RingHom
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Homogeneous Localization

## Notation
- `ι` is a commutative monoid;
- `A` is a commutative ring;
- `σ` is a class of additive subgroups of `A`;
- `𝒜 : ι → σ` is the grading of `A`;
- `x : Submonoid A` is a submonoid

## Main definitions and results

This file constructs the subring of `Aₓ` where the numerator and denominator have the same grading,
i.e. `{a/b ∈ Aₓ | ∃ (i : ι), a ∈ 𝒜ᵢ ∧ b ∈ 𝒜ᵢ}`.

* `HomogeneousLocalization.NumDenSameDeg`: a structure with a numerator and denominator field
  where they are required to have the same grading.

However `NumDenSameDeg 𝒜 x` cannot have a ring structure for many reasons, for example if `c`
is a `NumDenSameDeg`, then generally, `c + (-c)` is not necessarily `0` for degree reasons ---
`0` is considered to have grade zero (see `deg_zero`) but `c + (-c)` has the same degree as `c`. To
circumvent this, we quotient `NumDenSameDeg 𝒜 x` by the kernel of `c ↦ c.num / c.den`.

* `HomogeneousLocalization.NumDenSameDeg.embedding`: for `x : Submonoid A` and any
  `c : NumDenSameDeg 𝒜 x`, or equivalent a numerator and a denominator of the same degree,
  we get an element `c.num / c.den` of `Aₓ`.
* `HomogeneousLocalization`: `NumDenSameDeg 𝒜 x` quotiented by kernel of `embedding 𝒜 x`.
* `HomogeneousLocalization.val`: if `f : HomogeneousLocalization 𝒜 x`, then `f.val` is an element
  of `Aₓ`. In another word, one can view `HomogeneousLocalization 𝒜 x` as a subring of `Aₓ`
  through `HomogeneousLocalization.val`.
* `HomogeneousLocalization.num`: if `f : HomogeneousLocalization 𝒜 x`, then `f.num : A` is the
  numerator of `f`.
* `HomogeneousLocalization.den`: if `f : HomogeneousLocalization 𝒜 x`, then `f.den : A` is the
  denominator of `f`.
* `HomogeneousLocalization.deg`: if `f : HomogeneousLocalization 𝒜 x`, then `f.deg : ι` is the
  degree of `f` such that `f.num ∈ 𝒜 f.deg` and `f.den ∈ 𝒜 f.deg`
  (see `HomogeneousLocalization.num_mem_deg` and `HomogeneousLocalization.den_mem_deg`).
* `HomogeneousLocalization.num_mem_deg`: if `f : HomogeneousLocalization 𝒜 x`, then
  `f.num_mem_deg` is a proof that `f.num ∈ 𝒜 f.deg`.
* `HomogeneousLocalization.den_mem_deg`: if `f : HomogeneousLocalization 𝒜 x`, then
  `f.den_mem_deg` is a proof that `f.den ∈ 𝒜 f.deg`.
* `HomogeneousLocalization.eq_num_div_den`: if `f : HomogeneousLocalization 𝒜 x`, then
  `f.val : Aₓ` is equal to `f.num / f.den`.

* `HomogeneousLocalization.isLocalRing`: `HomogeneousLocalization 𝒜 x` is a local ring when `x` is
  the complement of some prime ideals.

* `HomogeneousLocalization.map`: Let `A` and `B` be two graded rings and `g : A → B` a
  grading-preserving ring map. If `P ≤ A` and `Q ≤ B` are submonoids such that `P ≤ g⁻¹(Q)`, then
  `g` induces a ring map between the homogeneous localization of `A` at `P` and the homogeneous
  localization of `B` at `Q`.

## References

* [Robin Hartshorne, *Algebraic Geometry*][Har77]


-/

@[expose] public section


noncomputable section

open DirectSum Pointwise

open DirectSum SetLike

variable {ι A σ : Type*}
variable [CommRing A] [SetLike σ A]

local notation "at " x => Localization x

namespace HomogeneousLocalization

section

/--
Definition of `NumDenSameDeg` / `NumDenSameDeg` 的定义

English:
structure NumDenSameDeg
  parameters: (𝒜 : ι -> σ) (x : Submonoid A)
  axioms and operations (3):
    - deg : ι
    - (num(den) : 𝒜 deg)
    - den_mem : (den : A) in x

中文:
结构 NumDenSameDeg
  参数: (𝒜 : ι -> σ) (x : Submonoid A)
  公理与运算 (3 个):
    - deg : ι
    - (num(den) : 𝒜 deg)
    - den_mem : (den : A) in x
-/
structure NumDenSameDeg (𝒜 : ι -> σ) (x : Submonoid A) where
  deg : ι
  (num den : 𝒜 deg)
  den_mem : (den : A) in x

end

namespace NumDenSameDeg

open SetLike.GradedMonoid Submodule

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  statement: {𝒜 : ι -> σ} (x : Submonoid A)
  proof: by
  rcases c1 with ⟨i1, ⟨n1, hn1⟩, ⟨d1, hd1⟩, h1⟩
  rcases c2 with ⟨i2, ⟨n2, hn2⟩, ⟨d2, hd2⟩, h2⟩
  dsimp only [Subtype.coe_mk] at *
  subst hdeg hnum hden
  congr

中文:
定理 ext
  结论: {𝒜 : ι -> σ} (x : Submonoid A)
  证明: by
  rcases c1 with ⟨i1, ⟨n1, hn1⟩, ⟨d1, hd1⟩, h1⟩
  rcases c2 with ⟨i2, ⟨n2, hn2⟩, ⟨d2, hd2⟩, h2⟩
  dsimp only [Subtype.coe_mk] at *
  subst hdeg hnum hden
  congr

Depends on / 依赖: CharZero, Subtype, Subtype.coe_mk, coe_mk, return, toOption, trySynthInstanceQ, with_reducible
-/
theorem ext {𝒜 : ι -> σ} (x : Submonoid A)
    {c1 c2 : NumDenSameDeg 𝒜 x} (hdeg : c1.deg = c2.deg) (hnum : (c1.num : A) = c2.num)
    (hden : (c1.den : A) = c2.den) : c1 = c2 := by
  rcases c1 with ⟨i1, ⟨n1, hn1⟩, ⟨d1, hd1⟩, h1⟩
  rcases c2 with ⟨i2, ⟨n2, hn2⟩, ⟨d2, hd2⟩, h2⟩
  dsimp only [Subtype.coe_mk] at *
  subst hdeg hnum hden
  congr

section Neg
variable [NegMemClass σ A] {𝒜 : ι -> σ} (x : Submonoid A)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg (NumDenSameDeg 𝒜 x)
  body: ⟨c.deg, ⟨-c.num, neg_mem c.num.2⟩, c.den, c.den_mem⟩

@[simp]

中文:
实例 :
  签名: Neg (NumDenSameDeg 𝒜 x)
  定义体: ⟨c.deg, ⟨-c.num, neg_mem c.num.2⟩, c.den, c.den_mem⟩

@[simp]

Depends on / 依赖: c.deg, c.den, c.den_mem, c.num, den_mem, neg_mem
-/
instance : Neg (NumDenSameDeg 𝒜 x) where
  neg c := ⟨c.deg, ⟨-c.num, neg_mem c.num.2⟩, c.den, c.den_mem⟩

@[simp]
/--
theorem `deg_neg` / 定理 `deg_neg`

English:
theorem deg_neg
  given: (c : NumDenSameDeg 𝒜 x)
  statement: (-c).deg = c.deg
  proof: rfl

@[simp]

中文:
定理 deg_neg
  条件: (c : NumDenSameDeg 𝒜 x)
  结论: (-c).deg = c.deg
  证明: rfl

@[simp]
-/
theorem deg_neg (c : NumDenSameDeg 𝒜 x) : (-c).deg = c.deg :=
  rfl

@[simp]
/--
theorem `num_neg` / 定理 `num_neg`

English:
theorem num_neg
  given: (c : NumDenSameDeg 𝒜 x)
  statement: ((-c).num : A) = -c.num
  proof: rfl

@[simp]

中文:
定理 num_neg
  条件: (c : NumDenSameDeg 𝒜 x)
  结论: ((-c).num : A) = -c.num
  证明: rfl

@[simp]
-/
theorem num_neg (c : NumDenSameDeg 𝒜 x) : ((-c).num : A) = -c.num :=
  rfl

@[simp]
/--
theorem `den_neg` / 定理 `den_neg`

English:
theorem den_neg
  given: (c : NumDenSameDeg 𝒜 x)
  statement: ((-c).den : A) = c.den
  proof: rfl

中文:
定理 den_neg
  条件: (c : NumDenSameDeg 𝒜 x)
  结论: ((-c).den : A) = c.den
  证明: rfl
-/
theorem den_neg (c : NumDenSameDeg 𝒜 x) : ((-c).den : A) = c.den :=
  rfl

end Neg

section SMul

variable {𝒜 : ι -> σ} (x : Submonoid A) {α : Type*} [SMul α A] [SMulMemClass σ α A]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul α (NumDenSameDeg 𝒜 x)
  body: ⟨c.deg, m • c.num, c.den, c.den_mem⟩

@[simp]

中文:
实例 :
  签名: SMul α (NumDenSameDeg 𝒜 x)
  定义体: ⟨c.deg, m • c.num, c.den, c.den_mem⟩

@[simp]

Depends on / 依赖: c.deg, c.den, c.den_mem, c.num, den_mem
-/
instance : SMul α (NumDenSameDeg 𝒜 x) where
  smul m c := ⟨c.deg, m • c.num, c.den, c.den_mem⟩

@[simp]
/--
theorem `deg_smul` / 定理 `deg_smul`

English:
theorem deg_smul
  given: (c : NumDenSameDeg 𝒜 x) (m : α)
  statement: (m • c).deg = c.deg
  proof: rfl

@[simp]

中文:
定理 deg_smul
  条件: (c : NumDenSameDeg 𝒜 x) (m : α)
  结论: (m • c).deg = c.deg
  证明: rfl

@[simp]
-/
theorem deg_smul (c : NumDenSameDeg 𝒜 x) (m : α) : (m • c).deg = c.deg :=
  rfl

@[simp]
/--
theorem `num_smul` / 定理 `num_smul`

English:
theorem num_smul
  given: (c : NumDenSameDeg 𝒜 x) (m : α)
  statement: ((m • c).num : A) = m • c.num
  proof: rfl

@[simp]

中文:
定理 num_smul
  条件: (c : NumDenSameDeg 𝒜 x) (m : α)
  结论: ((m • c).num : A) = m • c.num
  证明: rfl

@[simp]
-/
theorem num_smul (c : NumDenSameDeg 𝒜 x) (m : α) : ((m • c).num : A) = m • c.num :=
  rfl

@[simp]
/--
theorem `den_smul` / 定理 `den_smul`

English:
theorem den_smul
  given: (c : NumDenSameDeg 𝒜 x) (m : α)
  statement: ((m • c).den : A) = c.den
  proof: rfl

中文:
定理 den_smul
  条件: (c : NumDenSameDeg 𝒜 x) (m : α)
  结论: ((m • c).den : A) = c.den
  证明: rfl
-/
theorem den_smul (c : NumDenSameDeg 𝒜 x) (m : α) : ((m • c).den : A) = c.den :=
  rfl

end SMul

variable [AddSubmonoidClass σ A] {𝒜 : ι -> σ} (x : Submonoid A)
variable [AddCommMonoid ι] [DecidableEq ι] [GradedRing 𝒜]

open GradedOne in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (NumDenSameDeg 𝒜 x)
  body: { deg := 0
      num := ⟨1, one_mem⟩
      den := ⟨1, one_mem⟩
      den_mem := one_mem _ }

@[simp]

中文:
实例 :
  签名: One (NumDenSameDeg 𝒜 x)
  定义体: { deg := 0
      num := ⟨1, one_mem⟩
      den := ⟨1, one_mem⟩
      den_mem := one_mem _ }

@[simp]

Depends on / 依赖: den_mem, one_mem
-/
instance : One (NumDenSameDeg 𝒜 x) where
  one :=
    { deg := 0
      num := ⟨1, one_mem⟩
      den := ⟨1, one_mem⟩
      den_mem := one_mem _ }

@[simp]
/--
theorem `deg_one` / 定理 `deg_one`

English:
theorem deg_one
  statement: (1 : NumDenSameDeg 𝒜 x).deg = 0
  proof: rfl

@[simp]

中文:
定理 deg_one
  结论: (1 : NumDenSameDeg 𝒜 x).deg = 0
  证明: rfl

@[simp]
-/
theorem deg_one : (1 : NumDenSameDeg 𝒜 x).deg = 0 :=
  rfl

@[simp]
/--
theorem `num_one` / 定理 `num_one`

English:
theorem num_one
  statement: ((1 : NumDenSameDeg 𝒜 x).num : A) = 1
  proof: rfl

@[simp]

中文:
定理 num_one
  结论: ((1 : NumDenSameDeg 𝒜 x).num : A) = 1
  证明: rfl

@[simp]
-/
theorem num_one : ((1 : NumDenSameDeg 𝒜 x).num : A) = 1 :=
  rfl

@[simp]
/--
theorem `den_one` / 定理 `den_one`

English:
theorem den_one
  statement: ((1 : NumDenSameDeg 𝒜 x).den : A) = 1
  proof: rfl

中文:
定理 den_one
  结论: ((1 : NumDenSameDeg 𝒜 x).den : A) = 1
  证明: rfl
-/
theorem den_one : ((1 : NumDenSameDeg 𝒜 x).den : A) = 1 :=
  rfl

open GradedOne in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (NumDenSameDeg 𝒜 x)
  body: ⟨0, 0, ⟨1, one_mem⟩, one_mem _⟩

@[simp]

中文:
实例 :
  签名: Zero (NumDenSameDeg 𝒜 x)
  定义体: ⟨0, 0, ⟨1, one_mem⟩, one_mem _⟩

@[simp]

Depends on / 依赖: one_mem
-/
instance : Zero (NumDenSameDeg 𝒜 x) where
  zero := ⟨0, 0, ⟨1, one_mem⟩, one_mem _⟩

@[simp]
/--
theorem `deg_zero` / 定理 `deg_zero`

English:
theorem deg_zero
  statement: (0 : NumDenSameDeg 𝒜 x).deg = 0
  proof: rfl

@[simp]

中文:
定理 deg_zero
  结论: (0 : NumDenSameDeg 𝒜 x).deg = 0
  证明: rfl

@[simp]
-/
theorem deg_zero : (0 : NumDenSameDeg 𝒜 x).deg = 0 :=
  rfl

@[simp]
/--
theorem `num_zero` / 定理 `num_zero`

English:
theorem num_zero
  statement: (0 : NumDenSameDeg 𝒜 x).num = 0
  proof: rfl

@[simp]

中文:
定理 num_zero
  结论: (0 : NumDenSameDeg 𝒜 x).num = 0
  证明: rfl

@[simp]
-/
theorem num_zero : (0 : NumDenSameDeg 𝒜 x).num = 0 :=
  rfl

@[simp]
/--
theorem `den_zero` / 定理 `den_zero`

English:
theorem den_zero
  statement: ((0 : NumDenSameDeg 𝒜 x).den : A) = 1
  proof: rfl

中文:
定理 den_zero
  结论: ((0 : NumDenSameDeg 𝒜 x).den : A) = 1
  证明: rfl
-/
theorem den_zero : ((0 : NumDenSameDeg 𝒜 x).den : A) = 1 :=
  rfl

open GradedMul in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul (NumDenSameDeg 𝒜 x)
  body: { deg := p.deg + q.deg
      num := ⟨p.num * q.num, mul_mem p.num.prop q.num.prop⟩
      den := ⟨p.den * q.den, mul_mem p.den.prop q.den.prop⟩
      den_mem := Submonoid.mul_mem _ p.den_mem q.den_mem }

@[simp]

中文:
实例 :
  签名: Mul (NumDenSameDeg 𝒜 x)
  定义体: { deg := p.deg + q.deg
      num := ⟨p.num * q.num, mul_mem p.num.prop q.num.prop⟩
      den := ⟨p.den * q.den, mul_mem p.den.prop q.den.prop⟩
      den_mem := Submonoid.mul_mem _ p.den_mem q.den_mem }

@[simp]

Depends on / 依赖: Submonoid, Submonoid.mul_mem, den_mem, mul_mem, p.deg, p.den, p.den.prop, p.den_mem, p.num, p.num.prop, q.deg, q.den, q.den.prop, q.den_mem, q.num, q.num.prop
-/
instance : Mul (NumDenSameDeg 𝒜 x) where
  mul p q :=
    { deg := p.deg + q.deg
      num := ⟨p.num * q.num, mul_mem p.num.prop q.num.prop⟩
      den := ⟨p.den * q.den, mul_mem p.den.prop q.den.prop⟩
      den_mem := Submonoid.mul_mem _ p.den_mem q.den_mem }

@[simp]
/--
theorem `deg_mul` / 定理 `deg_mul`

English:
theorem deg_mul
  given: (c1 c2 : NumDenSameDeg 𝒜 x)
  statement: (c1 * c2).deg = c1.deg + c2.deg
  proof: rfl

@[simp]

中文:
定理 deg_mul
  条件: (c1 c2 : NumDenSameDeg 𝒜 x)
  结论: (c1 * c2).deg = c1.deg + c2.deg
  证明: rfl

@[simp]
-/
theorem deg_mul (c1 c2 : NumDenSameDeg 𝒜 x) : (c1 * c2).deg = c1.deg + c2.deg :=
  rfl

@[simp]
/--
theorem `num_mul` / 定理 `num_mul`

English:
theorem num_mul
  given: (c1 c2 : NumDenSameDeg 𝒜 x)
  statement: ((c1 * c2).num : A) = c1.num * c2.num
  proof: rfl

@[simp]

中文:
定理 num_mul
  条件: (c1 c2 : NumDenSameDeg 𝒜 x)
  结论: ((c1 * c2).num : A) = c1.num * c2.num
  证明: rfl

@[simp]
-/
theorem num_mul (c1 c2 : NumDenSameDeg 𝒜 x) : ((c1 * c2).num : A) = c1.num * c2.num :=
  rfl

@[simp]
/--
theorem `den_mul` / 定理 `den_mul`

English:
theorem den_mul
  given: (c1 c2 : NumDenSameDeg 𝒜 x)
  statement: ((c1 * c2).den : A) = c1.den * c2.den
  proof: rfl

中文:
定理 den_mul
  条件: (c1 c2 : NumDenSameDeg 𝒜 x)
  结论: ((c1 * c2).den : A) = c1.den * c2.den
  证明: rfl
-/
theorem den_mul (c1 c2 : NumDenSameDeg 𝒜 x) : ((c1 * c2).den : A) = c1.den * c2.den :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add (NumDenSameDeg 𝒜 x)
  body: { deg := c1.deg + c2.deg
      num := ⟨c1.den * c2.num + c2.den * c1.num,
        add_mem (GradedMul.mul_mem c1.den.2 c2.num.2)
          (add_comm c2.deg c1.deg ▸ GradedMul.mul_mem c2.den.2 c1.num.2)⟩
      den := ⟨c1.den * c2.den, GradedMul.mul_mem c1.den.2 c2.den.2⟩
      den_mem := Submonoid.mul

中文:
实例 :
  签名: Add (NumDenSameDeg 𝒜 x)
  定义体: { deg := c1.deg + c2.deg
      num := ⟨c1.den * c2.num + c2.den * c1.num,
        add_mem (GradedMul.mul_mem c1.den.2 c2.num.2)
          (add_comm c2.deg c1.deg ▸ GradedMul.mul_mem c2.den.2 c1.num.2)⟩
      den := ⟨c1.den * c2.den, GradedMul.mul_mem c1.den.2 c2.den.2⟩
      den_mem := Submonoid.mul

Depends on / 依赖: GradedMul, GradedMul.mul_mem, Submonoid, Submonoid.mul_mem, add_comm, add_mem, c1.deg, c1.den, c1.den_mem, c1.num, c2.deg, c2.den, c2.den_mem, c2.num, den_mem, mul_mem
-/
instance : Add (NumDenSameDeg 𝒜 x) where
  add c1 c2 :=
    { deg := c1.deg + c2.deg
      num := ⟨c1.den * c2.num + c2.den * c1.num,
        add_mem (GradedMul.mul_mem c1.den.2 c2.num.2)
          (add_comm c2.deg c1.deg ▸ GradedMul.mul_mem c2.den.2 c1.num.2)⟩
      den := ⟨c1.den * c2.den, GradedMul.mul_mem c1.den.2 c2.den.2⟩
      den_mem := Submonoid.mul_mem _ c1.den_mem c2.den_mem }

@[simp]
/--
theorem `deg_add` / 定理 `deg_add`

English:
theorem deg_add
  given: (c1 c2 : NumDenSameDeg 𝒜 x)
  statement: (c1 + c2).deg = c1.deg + c2.deg
  proof: rfl

@[simp]

中文:
定理 deg_add
  条件: (c1 c2 : NumDenSameDeg 𝒜 x)
  结论: (c1 + c2).deg = c1.deg + c2.deg
  证明: rfl

@[simp]
-/
theorem deg_add (c1 c2 : NumDenSameDeg 𝒜 x) : (c1 + c2).deg = c1.deg + c2.deg :=
  rfl

@[simp]
/--
theorem `num_add` / 定理 `num_add`

English:
theorem num_add
  given: (c1 c2 : NumDenSameDeg 𝒜 x)
  proof: rfl

@[simp]

中文:
定理 num_add
  条件: (c1 c2 : NumDenSameDeg 𝒜 x)
  证明: rfl

@[simp]
-/
theorem num_add (c1 c2 : NumDenSameDeg 𝒜 x) :
    ((c1 + c2).num : A) = c1.den * c2.num + c2.den * c1.num :=
  rfl

@[simp]
/--
theorem `den_add` / 定理 `den_add`

English:
theorem den_add
  given: (c1 c2 : NumDenSameDeg 𝒜 x)
  statement: ((c1 + c2).den : A) = c1.den * c2.den
  proof: rfl

中文:
定理 den_add
  条件: (c1 c2 : NumDenSameDeg 𝒜 x)
  结论: ((c1 + c2).den : A) = c1.den * c2.den
  证明: rfl
-/
theorem den_add (c1 c2 : NumDenSameDeg 𝒜 x) : ((c1 + c2).den : A) = c1.den * c2.den :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommMonoid (NumDenSameDeg 𝒜 x)
  body: ext _ (add_assoc _ _ _) (mul_assoc _ _ _) (mul_assoc _ _ _)
  one_mul _ := ext _ (zero_add _) (one_mul _) (one_mul _)
  mul_one _ := ext _ (add_zero _) (mul_one _) (mul_one _)
  mul_comm _ _ := ext _ (add_comm _ _) (mul_comm _ _) (mul_comm _ _)

中文:
实例 :
  签名: CommMonoid (NumDenSameDeg 𝒜 x)
  定义体: ext _ (add_assoc _ _ _) (mul_assoc _ _ _) (mul_assoc _ _ _)
  one_mul _ := ext _ (zero_add _) (one_mul _) (one_mul _)
  mul_one _ := ext _ (add_zero _) (mul_one _) (mul_one _)
  mul_comm _ _ := ext _ (add_comm _ _) (mul_comm _ _) (mul_comm _ _)

Depends on / 依赖: add_assoc, mul_assoc
-/
instance : CommMonoid (NumDenSameDeg 𝒜 x) where
  mul_assoc _ _ _ := ext _ (add_assoc _ _ _) (mul_assoc _ _ _) (mul_assoc _ _ _)
  one_mul _ := ext _ (zero_add _) (one_mul _) (one_mul _)
  mul_one _ := ext _ (add_zero _) (mul_one _) (mul_one _)
  mul_comm _ _ := ext _ (add_comm _ _) (mul_comm _ _) (mul_comm _ _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Pow (NumDenSameDeg 𝒜 x) Nat
  body: ⟨n • c.deg, @GradedMonoid.GMonoid.gnpow _ (fun i => ↥(𝒜 i)) _ _ n _ c.num,
      @GradedMonoid.GMonoid.gnpow _ (fun i => ↥(𝒜 i)) _ _ n _ c.den, by
        induction n with
        | zero => simp only [coe_gnpow, pow_zero, one_mem]
        | succ n ih => simpa only [pow_succ, coe_gnpow] using x.mul_m

中文:
实例 :
  签名: Pow (NumDenSameDeg 𝒜 x) 自然数
  定义体: ⟨n • c.deg, @GradedMonoid.GMonoid.gnpow _ (fun i => ↥(𝒜 i)) _ _ n _ c.num,
      @GradedMonoid.GMonoid.gnpow _ (fun i => ↥(𝒜 i)) _ _ n _ c.den, by
        induction n with
        | zero => simp only [coe_gnpow, pow_zero, one_mem]
        | succ n ih => simpa only [pow_succ, coe_gnpow] using x.mul_m

Depends on / 依赖: GMonoid, GradedMonoid, GradedMonoid.GMonoid.gnpow, c.deg, c.den, c.den_mem, c.num, coe_gnpow, den_mem, mul_mem, one_mem, pow_succ, pow_zero, x.mul_mem
-/
instance : Pow (NumDenSameDeg 𝒜 x) Nat where
  pow c n :=
    ⟨n • c.deg, @GradedMonoid.GMonoid.gnpow _ (fun i => ↥(𝒜 i)) _ _ n _ c.num,
      @GradedMonoid.GMonoid.gnpow _ (fun i => ↥(𝒜 i)) _ _ n _ c.den, by
        induction n with
        | zero => simp only [coe_gnpow, pow_zero, one_mem]
        | succ n ih => simpa only [pow_succ, coe_gnpow] using x.mul_mem ih c.den_mem⟩

@[simp]
/--
theorem `deg_pow` / 定理 `deg_pow`

English:
theorem deg_pow
  given: (c : NumDenSameDeg 𝒜 x) (n : Nat)
  statement: (c ^ n).deg = n • c.deg
  proof: rfl

@[simp]

中文:
定理 deg_pow
  条件: (c : NumDenSameDeg 𝒜 x) (n : 自然数)
  结论: (c ^ n).deg = n • c.deg
  证明: rfl

@[simp]
-/
theorem deg_pow (c : NumDenSameDeg 𝒜 x) (n : Nat) : (c ^ n).deg = n • c.deg :=
  rfl

@[simp]
/--
theorem `num_pow` / 定理 `num_pow`

English:
theorem num_pow
  given: (c : NumDenSameDeg 𝒜 x) (n : Nat)
  statement: ((c ^ n).num : A) = (c.num : A) ^ n
  proof: rfl

@[simp]

中文:
定理 num_pow
  条件: (c : NumDenSameDeg 𝒜 x) (n : 自然数)
  结论: ((c ^ n).num : A) = (c.num : A) ^ n
  证明: rfl

@[simp]
-/
theorem num_pow (c : NumDenSameDeg 𝒜 x) (n : Nat) : ((c ^ n).num : A) = (c.num : A) ^ n :=
  rfl

@[simp]
/--
theorem `den_pow` / 定理 `den_pow`

English:
theorem den_pow
  given: (c : NumDenSameDeg 𝒜 x) (n : Nat)
  statement: ((c ^ n).den : A) = (c.den : A) ^ n
  proof: rfl

中文:
定理 den_pow
  条件: (c : NumDenSameDeg 𝒜 x) (n : 自然数)
  结论: ((c ^ n).den : A) = (c.den : A) ^ n
  证明: rfl
-/
theorem den_pow (c : NumDenSameDeg 𝒜 x) (n : Nat) : ((c ^ n).den : A) = (c.den : A) ^ n :=
  rfl

variable (𝒜)

/--
Definition of `embedding` / `embedding` 的定义

English:
definition embedding
  signature: (p : NumDenSameDeg 𝒜 x)
  body: Localization.mk p.num ⟨p.den, p.den_mem⟩

中文:
定义 embedding
  签名: (p : NumDenSameDeg 𝒜 x)
  定义体: Localization.mk p.num ⟨p.den, p.den_mem⟩

Depends on / 依赖: Localization, Localization.mk, den_mem, p.den, p.den_mem, p.num
-/
def embedding (p : NumDenSameDeg 𝒜 x) : at x :=
  Localization.mk p.num ⟨p.den, p.den_mem⟩

end NumDenSameDeg

end HomogeneousLocalization

/--
Definition of `HomogeneousLocalization` / `HomogeneousLocalization` 的定义

English:
definition HomogeneousLocalization
  signature: (𝒜 : ι -> σ) (x : Submonoid A)
  body: Quotient (Setoid.ker <| HomogeneousLocalization.NumDenSameDeg.embedding 𝒜 x)

中文:
定义 HomogeneousLocalization
  签名: (𝒜 : ι -> σ) (x : Submonoid A)
  定义体: Quotient (Setoid.ker <| HomogeneousLocalization.NumDenSameDeg.embedding 𝒜 x)

Depends on / 依赖: HomogeneousLocalization, HomogeneousLocalization.NumDenSameDeg.embedding, NumDenSameDeg, Quotient, Setoid, Setoid.ker, embedding
-/
def HomogeneousLocalization (𝒜 : ι -> σ) (x : Submonoid A) : Type _ :=
  Quotient (Setoid.ker <| HomogeneousLocalization.NumDenSameDeg.embedding 𝒜 x)

namespace HomogeneousLocalization

open HomogeneousLocalization HomogeneousLocalization.NumDenSameDeg

section
variable {𝒜 : ι -> σ} {x : Submonoid A}

/--
Definition of `mk` / `mk` 的定义

English:
abbreviation mk
  signature: (y : HomogeneousLocalization.NumDenSameDeg 𝒜 x)
  body: Quotient.mk'' y

中文:
缩写 mk
  签名: (y : HomogeneousLocalization.NumDenSameDeg 𝒜 x)
  定义体: Quotient.mk'' y

Depends on / 依赖: Quotient, Quotient.mk
-/
abbrev mk (y : HomogeneousLocalization.NumDenSameDeg 𝒜 x) : HomogeneousLocalization 𝒜 x :=
  Quotient.mk'' y

/--
lemma `mk_surjective` / 引理 `mk_surjective`

English:
lemma mk_surjective
  statement: Function.Surjective (mk (𝒜 := 𝒜) (x := x))
  proof: Quotient.mk''_surjective

中文:
引理 mk_surjective
  结论: Function.Surjective (mk (𝒜 := 𝒜) (x := x))
  证明: Quotient.mk''_surjective
-/
lemma mk_surjective : Function.Surjective (mk (𝒜 := 𝒜) (x := x)) :=
  Quotient.mk''_surjective

/--
Definition of `val` / `val` 的定义

English:
definition val
  signature: (y : HomogeneousLocalization 𝒜 x)
  body: Quotient.liftOn' y (NumDenSameDeg.embedding 𝒜 x) fun _ _ => id

@[simp]

中文:
定义 val
  签名: (y : HomogeneousLocalization 𝒜 x)
  定义体: Quotient.liftOn' y (NumDenSameDeg.embedding 𝒜 x) fun _ _ => id

@[simp]

Depends on / 依赖: NumDenSameDeg, NumDenSameDeg.embedding, Quotient, Quotient.liftOn, embedding, liftOn
-/
def val (y : HomogeneousLocalization 𝒜 x) : at x :=
  Quotient.liftOn' y (NumDenSameDeg.embedding 𝒜 x) fun _ _ => id

@[simp]
/--
theorem `val_mk` / 定理 `val_mk`

English:
theorem val_mk
  given: (i : NumDenSameDeg 𝒜 x)
  proof: rfl

中文:
定理 val_mk
  条件: (i : NumDenSameDeg 𝒜 x)
  证明: rfl
-/
theorem val_mk (i : NumDenSameDeg 𝒜 x) :
    val (mk i) = Localization.mk (i.num : A) ⟨i.den, i.den_mem⟩ :=
  rfl

variable (x)

@[ext]
/--
theorem `val_injective` / 定理 `val_injective`

English:
theorem val_injective
  statement: Function.Injective (HomogeneousLocalization.val (𝒜 := 𝒜) (x := x))
  proof: fun a b => Quotient.recOnSubsingleton₂' a b fun _ _ h => Quotient.sound' h

中文:
定理 val_injective
  结论: Function.Injective (HomogeneousLocalization.val (𝒜 := 𝒜) (x := x))
  证明: fun a b => Quotient.recOnSubsingleton₂' a b fun _ _ h => Quotient.sound' h
-/
theorem val_injective : Function.Injective (HomogeneousLocalization.val (𝒜 := 𝒜) (x := x)) :=
  fun a b => Quotient.recOnSubsingleton₂' a b fun _ _ h => Quotient.sound' h

variable (𝒜) {x} in
/--
lemma `subsingleton` / 引理 `subsingleton`

English:
lemma subsingleton
  given: (hx : 0 in x)
  statement: Subsingleton (HomogeneousLocalization 𝒜 x)
  proof: have := IsLocalization.subsingleton (S := at x) hx
  (HomogeneousLocalization.val_injective (𝒜 := 𝒜) (x := x)).subsingleton

中文:
引理 subsingleton
  条件: (hx : 0 in x)
  结论: Subsingleton (HomogeneousLocalization 𝒜 x)
  证明: have := IsLocalization.subsingleton (S := at x) hx
  (HomogeneousLocalization.val_injective (𝒜 := 𝒜) (x := x)).subsingleton

Depends on / 依赖: HomogeneousLocalization, HomogeneousLocalization.val_injective, IsLocalization, IsLocalization.subsingleton, subsingleton, val_injective
-/
lemma subsingleton (hx : 0 in x) : Subsingleton (HomogeneousLocalization 𝒜 x) :=
  have := IsLocalization.subsingleton (S := at x) hx
  (HomogeneousLocalization.val_injective (𝒜 := 𝒜) (x := x)).subsingleton

end

section SMul
variable {𝒜 : ι -> σ} (x : Submonoid A)
variable {α : Type*} [SMul α A] [IsScalarTower α A A] [SMulMemClass σ α A]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul α (HomogeneousLocalization 𝒜 x)
  body: Quotient.map' (m • ·) fun c1 c2 (h : Localization.mk _ _ = Localization.mk _ _) => by
    change Localization.mk _ _ = Localization.mk _ _
    simp only [num_smul, den_smul]
    convert! congr_arg (fun z : at x => m • z) h <;> rw [Localization.smul_mk]

中文:
实例 :
  签名: SMul α (HomogeneousLocalization 𝒜 x)
  定义体: Quotient.map' (m • ·) fun c1 c2 (h : Localization.mk _ _ = Localization.mk _ _) => by
    change Localization.mk _ _ = Localization.mk _ _
    simp only [num_smul, den_smul]
    convert! congr_arg (fun z : at x => m • z) h <;> rw [Localization.smul_mk]

Depends on / 依赖: Localization, Localization.mk, Localization.smul_mk, Quotient, Quotient.map, congr_arg, convert, den_smul, num_smul, smul_mk
-/
instance : SMul α (HomogeneousLocalization 𝒜 x) where
  smul m := Quotient.map' (m • ·) fun c1 c2 (h : Localization.mk _ _ = Localization.mk _ _) => by
    change Localization.mk _ _ = Localization.mk _ _
    simp only [num_smul, den_smul]
    convert! congr_arg (fun z : at x => m • z) h <;> rw [Localization.smul_mk]

/--
lemma `mk_smul` / 引理 `mk_smul`

English:
lemma mk_smul
  given: (i : NumDenSameDeg 𝒜 x) (m : α)
  statement: mk (m • i) = m • mk i
  proof: rfl

@[simp]

中文:
引理 mk_smul
  条件: (i : NumDenSameDeg 𝒜 x) (m : α)
  结论: mk (m • i) = m • mk i
  证明: rfl

@[simp]
-/
@[simp] lemma mk_smul (i : NumDenSameDeg 𝒜 x) (m : α) : mk (m • i) = m • mk i := rfl

@[simp]
/--
theorem `val_smul` / 定理 `val_smul`

English:
theorem val_smul
  given: (n : α)
  statement: forall y : HomogeneousLocalization 𝒜 x, (n • y).val = n • y.val
  proof: Quotient.ind' fun _ => by rw [← mk_smul, val_mk, val_mk, Localization.smul_mk, num_smul]; rfl

中文:
定理 val_smul
  条件: (n : α)
  结论: 对任意 y : HomogeneousLocalization 𝒜 x, (n • y).val = n • y.val
  证明: Quotient.ind' fun _ => by rw [← mk_smul, val_mk, val_mk, Localization.smul_mk, num_smul]; rfl

Depends on / 依赖: Localization, Localization.smul_mk, Quotient, Quotient.ind, mk_smul, num_smul, smul_mk, val_mk
-/
theorem val_smul (n : α) : forall y : HomogeneousLocalization 𝒜 x, (n • y).val = n • y.val :=
  Quotient.ind' fun _ => by rw [← mk_smul, val_mk, val_mk, Localization.smul_mk, num_smul]; rfl

end SMul

section nsmul
variable [AddSubmonoidClass σ A] {𝒜 : ι -> σ} (x : Submonoid A)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul Nat (HomogeneousLocalization 𝒜 x)
  body: haveI := AddSubmonoidClass.nsmulMemClass (S := σ) (M := A)
  HomogeneousLocalization.instSMul x

中文:
实例 :
  签名: SMul 自然数 (HomogeneousLocalization 𝒜 x)
  定义体: haveI := AddSubmonoidClass.nsmulMemClass (S := σ) (M := A)
  HomogeneousLocalization.instSMul x

Depends on / 依赖: AddSubmonoidClass, AddSubmonoidClass.nsmulMemClass, HomogeneousLocalization, HomogeneousLocalization.instSMul, instSMul, nsmulMemClass
-/
instance : SMul Nat (HomogeneousLocalization 𝒜 x) :=
  haveI := AddSubmonoidClass.nsmulMemClass (S := σ) (M := A)
  HomogeneousLocalization.instSMul x

/--
theorem `val_nsmul` / 定理 `val_nsmul`

English:
theorem val_nsmul
  given: (n : Nat) (y : HomogeneousLocalization 𝒜 x)
  statement: (n • y).val = n • y.val
  proof: by
  rw [val_smul]; rw [OreLocalization.nsmul_eq_nsmul]

中文:
定理 val_nsmul
  条件: (n : 自然数) (y : HomogeneousLocalization 𝒜 x)
  结论: (n • y).val = n • y.val
  证明: by
  rw [val_smul]; rw [OreLocalization.nsmul_eq_nsmul]

Depends on / 依赖: OreLocalization, OreLocalization.nsmul_eq_nsmul, nsmul_eq_nsmul, val_smul
-/
theorem val_nsmul (n : Nat) (y : HomogeneousLocalization 𝒜 x) : (n • y).val = n • y.val := by
  rw [val_smul]; rw [OreLocalization.nsmul_eq_nsmul]

end nsmul

section zsmul
variable [AddSubgroupClass σ A] {𝒜 : ι -> σ} (x : Submonoid A)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul Int (HomogeneousLocalization 𝒜 x)
  body: haveI := AddSubgroupClass.zsmulMemClass (S := σ) (M := A)
  HomogeneousLocalization.instSMul x

中文:
实例 :
  签名: SMul 整数 (HomogeneousLocalization 𝒜 x)
  定义体: haveI := AddSubgroupClass.zsmulMemClass (S := σ) (M := A)
  HomogeneousLocalization.instSMul x

Depends on / 依赖: AddSubgroupClass, AddSubgroupClass.zsmulMemClass, HomogeneousLocalization, HomogeneousLocalization.instSMul, instSMul, zsmulMemClass
-/
instance : SMul Int (HomogeneousLocalization 𝒜 x) :=
  haveI := AddSubgroupClass.zsmulMemClass (S := σ) (M := A)
  HomogeneousLocalization.instSMul x

/--
theorem `val_zsmul` / 定理 `val_zsmul`

English:
theorem val_zsmul
  given: (n : Int) (y : HomogeneousLocalization 𝒜 x)
  statement: (n • y).val = n • y.val
  proof: by
  rw [val_smul]; rw [OreLocalization.zsmul_eq_zsmul]

中文:
定理 val_zsmul
  条件: (n : 整数) (y : HomogeneousLocalization 𝒜 x)
  结论: (n • y).val = n • y.val
  证明: by
  rw [val_smul]; rw [OreLocalization.zsmul_eq_zsmul]

Depends on / 依赖: OreLocalization, OreLocalization.zsmul_eq_zsmul, val_smul, zsmul_eq_zsmul
-/
theorem val_zsmul (n : Int) (y : HomogeneousLocalization 𝒜 x) : (n • y).val = n • y.val := by
  rw [val_smul]; rw [OreLocalization.zsmul_eq_zsmul]

end zsmul

section Neg
variable [NegMemClass σ A] {𝒜 : ι -> σ} (x : Submonoid A)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg (HomogeneousLocalization 𝒜 x)
  body: Quotient.map' Neg.neg fun c1 c2 (h : Localization.mk _ _ = Localization.mk _ _) => by
    change Localization.mk _ _ = Localization.mk _ _
    simp only [num_neg, den_neg, ← Localization.neg_mk]
    exact congr_arg Neg.neg h

中文:
实例 :
  签名: Neg (HomogeneousLocalization 𝒜 x)
  定义体: Quotient.map' Neg.neg fun c1 c2 (h : Localization.mk _ _ = Localization.mk _ _) => by
    change Localization.mk _ _ = Localization.mk _ _
    simp only [num_neg, den_neg, ← Localization.neg_mk]
    exact congr_arg Neg.neg h

Depends on / 依赖: Localization, Localization.mk, Localization.neg_mk, Neg.neg, Quotient, Quotient.map, congr_arg, den_neg, neg_mk, num_neg
-/
instance : Neg (HomogeneousLocalization 𝒜 x) where
  neg := Quotient.map' Neg.neg fun c1 c2 (h : Localization.mk _ _ = Localization.mk _ _) => by
    change Localization.mk _ _ = Localization.mk _ _
    simp only [num_neg, den_neg, ← Localization.neg_mk]
    exact congr_arg Neg.neg h

/--
lemma `mk_neg` / 引理 `mk_neg`

English:
lemma mk_neg
  given: (i : NumDenSameDeg 𝒜 x)
  statement: mk (-i) = -mk i
  proof: rfl

@[simp]

中文:
引理 mk_neg
  条件: (i : NumDenSameDeg 𝒜 x)
  结论: mk (-i) = -mk i
  证明: rfl

@[simp]
-/
@[simp] lemma mk_neg (i : NumDenSameDeg 𝒜 x) : mk (-i) = -mk i := rfl

@[simp]
/--
theorem `val_neg` / 定理 `val_neg`

English:
theorem val_neg
  given: {x}
  statement: forall y : HomogeneousLocalization 𝒜 x, (-y).val = -y.val
  proof: Quotient.ind' fun y => by rw [← mk_neg, val_mk, val_mk, Localization.neg_mk]; rfl

中文:
定理 val_neg
  条件: {x}
  结论: 对任意 y : HomogeneousLocalization 𝒜 x, (-y).val = -y.val
  证明: Quotient.ind' fun y => by rw [← mk_neg, val_mk, val_mk, Localization.neg_mk]; rfl

Depends on / 依赖: Localization, Localization.neg_mk, Quotient, Quotient.ind, mk_neg, neg_mk, val_mk
-/
theorem val_neg {x} : forall y : HomogeneousLocalization 𝒜 x, (-y).val = -y.val :=
  Quotient.ind' fun y => by rw [← mk_neg, val_mk, val_mk, Localization.neg_mk]; rfl

end Neg

variable [AddSubgroupClass σ A] [AddCommMonoid ι] [DecidableEq ι]
variable {𝒜 : ι -> σ} [GradedRing 𝒜] (x : Submonoid A)

/--
Instance `hasPow` / 实例 `hasPow`

English:
instance hasPow
  signature: : Pow (HomogeneousLocalization 𝒜 x) Nat where
  body: (Quotient.map' (· ^ n) fun c1 c2 (h : Localization.mk _ _ = Localization.mk _ _) => by
          change Localization.mk _ _ = Localization.mk _ _
          simp only [num_pow, den_pow]
          convert! congr_arg (fun z : at x => z ^ n) h <;> rw [Localization.mk_pow] <;> rfl :
        HomogeneousLo

中文:
实例 hasPow
  签名: : Pow (HomogeneousLocalization 𝒜 x) 自然数 where
  定义体: (Quotient.map' (· ^ n) fun c1 c2 (h : Localization.mk _ _ = Localization.mk _ _) => by
          change Localization.mk _ _ = Localization.mk _ _
          simp only [num_pow, den_pow]
          convert! congr_arg (fun z : at x => z ^ n) h <;> rw [Localization.mk_pow] <;> rfl :
        HomogeneousLo

Depends on / 依赖: HomogeneousLocalization, Localization, Localization.mk, Localization.mk_pow, Quotient, Quotient.map, congr_arg, convert, den_pow, mk_pow, num_pow
-/
instance hasPow : Pow (HomogeneousLocalization 𝒜 x) Nat where
  pow z n :=
    (Quotient.map' (· ^ n) fun c1 c2 (h : Localization.mk _ _ = Localization.mk _ _) => by
          change Localization.mk _ _ = Localization.mk _ _
          simp only [num_pow, den_pow]
          convert! congr_arg (fun z : at x => z ^ n) h <;> rw [Localization.mk_pow] <;> rfl :
        HomogeneousLocalization 𝒜 x -> HomogeneousLocalization 𝒜 x)
      z

/--
lemma `mk_pow` / 引理 `mk_pow`

English:
lemma mk_pow
  given: (i : NumDenSameDeg 𝒜 x) (n : Nat)
  statement: mk (i ^ n) = mk i ^ n
  proof: rfl

中文:
引理 mk_pow
  条件: (i : NumDenSameDeg 𝒜 x) (n : 自然数)
  结论: mk (i ^ n) = mk i ^ n
  证明: rfl
-/
@[simp] lemma mk_pow (i : NumDenSameDeg 𝒜 x) (n : Nat) : mk (i ^ n) = mk i ^ n := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add (HomogeneousLocalization 𝒜 x)
  body: Quotient.map₂ (· + ·)
      fun c1 c2 (h : Localization.mk _ _ = Localization.mk _ _) c3 c4
        (h' : Localization.mk _ _ = Localization.mk _ _) => by
      change Localization.mk _ _ = Localization.mk _ _
      simp only [num_add, den_add]
      convert! congr_arg₂ (· + ·) h h' <;> rw [Localiza

中文:
实例 :
  签名: Add (HomogeneousLocalization 𝒜 x)
  定义体: Quotient.map₂ (· + ·)
      fun c1 c2 (h : Localization.mk _ _ = Localization.mk _ _) c3 c4
        (h' : Localization.mk _ _ = Localization.mk _ _) => by
      change Localization.mk _ _ = Localization.mk _ _
      simp only [num_add, den_add]
      convert! congr_arg₂ (· + ·) h h' <;> rw [Localiza

Depends on / 依赖: Localization, Localization.add_mk, Localization.mk, Quotient, Quotient.map, add_mk, convert, den_add, num_add
-/
instance : Add (HomogeneousLocalization 𝒜 x) where
  add :=
    Quotient.map₂ (· + ·)
      fun c1 c2 (h : Localization.mk _ _ = Localization.mk _ _) c3 c4
        (h' : Localization.mk _ _ = Localization.mk _ _) => by
      change Localization.mk _ _ = Localization.mk _ _
      simp only [num_add, den_add]
      convert! congr_arg₂ (· + ·) h h' <;> rw [Localization.add_mk] <;> rfl

/--
lemma `mk_add` / 引理 `mk_add`

English:
lemma mk_add
  given: (i j : NumDenSameDeg 𝒜 x)
  statement: mk (i + j) = mk i + mk j
  proof: rfl

中文:
引理 mk_add
  条件: (i j : NumDenSameDeg 𝒜 x)
  结论: mk (i + j) = mk i + mk j
  证明: rfl
-/
@[simp] lemma mk_add (i j : NumDenSameDeg 𝒜 x) : mk (i + j) = mk i + mk j := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Sub (HomogeneousLocalization 𝒜 x)
  body: z1 + -z2

中文:
实例 :
  签名: Sub (HomogeneousLocalization 𝒜 x)
  定义体: z1 + -z2

Depends on / 依赖: jacobiSymNat, jacobiSymNat.mod_left, jacobiSymNat.qr, mod_left
-/
instance : Sub (HomogeneousLocalization 𝒜 x) where sub z1 z2 := z1 + -z2

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul (HomogeneousLocalization 𝒜 x)
  body: Quotient.map₂ (· * ·)
      fun c1 c2 (h : Localization.mk _ _ = Localization.mk _ _) c3 c4
        (h' : Localization.mk _ _ = Localization.mk _ _) => by
      change Localization.mk _ _ = Localization.mk _ _
      simp only [num_mul, den_mul]
      convert! congr_arg₂ (· * ·) h h' <;> rw [Localiza

中文:
实例 :
  签名: Mul (HomogeneousLocalization 𝒜 x)
  定义体: Quotient.map₂ (· * ·)
      fun c1 c2 (h : Localization.mk _ _ = Localization.mk _ _) c3 c4
        (h' : Localization.mk _ _ = Localization.mk _ _) => by
      change Localization.mk _ _ = Localization.mk _ _
      simp only [num_mul, den_mul]
      convert! congr_arg₂ (· * ·) h h' <;> rw [Localiza

Depends on / 依赖: Localization, Localization.mk, Localization.mk_mul, Quotient, Quotient.map, convert, den_mul, mk_mul, num_mul
-/
instance : Mul (HomogeneousLocalization 𝒜 x) where
  mul :=
    Quotient.map₂ (· * ·)
      fun c1 c2 (h : Localization.mk _ _ = Localization.mk _ _) c3 c4
        (h' : Localization.mk _ _ = Localization.mk _ _) => by
      change Localization.mk _ _ = Localization.mk _ _
      simp only [num_mul, den_mul]
      convert! congr_arg₂ (· * ·) h h' <;> rw [Localization.mk_mul] <;> rfl

/--
lemma `mk_mul` / 引理 `mk_mul`

English:
lemma mk_mul
  given: (i j : NumDenSameDeg 𝒜 x)
  statement: mk (i * j) = mk i * mk j
  proof: rfl

中文:
引理 mk_mul
  条件: (i j : NumDenSameDeg 𝒜 x)
  结论: mk (i * j) = mk i * mk j
  证明: rfl
-/
@[simp] lemma mk_mul (i j : NumDenSameDeg 𝒜 x) : mk (i * j) = mk i * mk j := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (HomogeneousLocalization 𝒜 x)
  body: Quotient.mk'' 1

中文:
实例 :
  签名: One (HomogeneousLocalization 𝒜 x)
  定义体: Quotient.mk'' 1

Depends on / 依赖: Quotient, Quotient.mk
-/
instance : One (HomogeneousLocalization 𝒜 x) where one := Quotient.mk'' 1

/--
lemma `mk_one` / 引理 `mk_one`

English:
lemma mk_one
  statement: mk (1 : NumDenSameDeg 𝒜 x) = 1
  proof: rfl

中文:
引理 mk_one
  结论: mk (1 : NumDenSameDeg 𝒜 x) = 1
  证明: rfl
-/
@[simp] lemma mk_one : mk (1 : NumDenSameDeg 𝒜 x) = 1 := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (HomogeneousLocalization 𝒜 x)
  body: Quotient.mk'' 0

中文:
实例 :
  签名: Zero (HomogeneousLocalization 𝒜 x)
  定义体: Quotient.mk'' 0

Depends on / 依赖: Quotient, Quotient.mk
-/
instance : Zero (HomogeneousLocalization 𝒜 x) where zero := Quotient.mk'' 0

/--
lemma `mk_zero` / 引理 `mk_zero`

English:
lemma mk_zero
  statement: mk (0 : NumDenSameDeg 𝒜 x) = 0
  proof: rfl

中文:
引理 mk_zero
  结论: mk (0 : NumDenSameDeg 𝒜 x) = 0
  证明: rfl
-/
@[simp] lemma mk_zero : mk (0 : NumDenSameDeg 𝒜 x) = 0 := rfl

/--
theorem `zero_eq` / 定理 `zero_eq`

English:
theorem zero_eq
  statement: (0 : HomogeneousLocalization 𝒜 x) = Quotient.mk'' 0
  proof: rfl

中文:
定理 zero_eq
  结论: (0 : HomogeneousLocalization 𝒜 x) = Quotient.mk'' 0
  证明: rfl
-/
theorem zero_eq : (0 : HomogeneousLocalization 𝒜 x) = Quotient.mk'' 0 :=
  rfl

/--
theorem `one_eq` / 定理 `one_eq`

English:
theorem one_eq
  statement: (1 : HomogeneousLocalization 𝒜 x) = Quotient.mk'' 1
  proof: rfl

中文:
定理 one_eq
  结论: (1 : HomogeneousLocalization 𝒜 x) = Quotient.mk'' 1
  证明: rfl
-/
theorem one_eq : (1 : HomogeneousLocalization 𝒜 x) = Quotient.mk'' 1 :=
  rfl

variable {x}

@[simp]
/--
theorem `val_zero` / 定理 `val_zero`

English:
theorem val_zero
  statement: (0 : HomogeneousLocalization 𝒜 x).val = 0
  proof: Localization.mk_zero _

@[simp]

中文:
定理 val_zero
  结论: (0 : HomogeneousLocalization 𝒜 x).val = 0
  证明: Localization.mk_zero _

@[simp]

Depends on / 依赖: Localization, Localization.mk_zero, mk_zero
-/
theorem val_zero : (0 : HomogeneousLocalization 𝒜 x).val = 0 :=
  Localization.mk_zero _

@[simp]
/--
theorem `val_one` / 定理 `val_one`

English:
theorem val_one
  statement: (1 : HomogeneousLocalization 𝒜 x).val = 1
  proof: Localization.mk_one

@[simp]

中文:
定理 val_one
  结论: (1 : HomogeneousLocalization 𝒜 x).val = 1
  证明: Localization.mk_one

@[simp]

Depends on / 依赖: Localization, Localization.mk_one, mk_one
-/
theorem val_one : (1 : HomogeneousLocalization 𝒜 x).val = 1 :=
  Localization.mk_one

@[simp]
/--
theorem `val_add` / 定理 `val_add`

English:
theorem val_add
  statement: forall y1 y2 : HomogeneousLocalization 𝒜 x, (y1 + y2).val = y1.val + y2.val
  proof: Quotient.ind₂' fun y1 y2 => by rw [← mk_add, val_mk, val_mk, val_mk, Localization.add_mk]; rfl

@[simp]

中文:
定理 val_add
  结论: 对任意 y1 y2 : HomogeneousLocalization 𝒜 x, (y1 + y2).val = y1.val + y2.val
  证明: Quotient.ind₂' fun y1 y2 => by rw [← mk_add, val_mk, val_mk, val_mk, Localization.add_mk]; rfl

@[simp]

Depends on / 依赖: Localization, Localization.add_mk, Quotient, Quotient.ind, add_mk, mk_add, val_mk
-/
theorem val_add : forall y1 y2 : HomogeneousLocalization 𝒜 x, (y1 + y2).val = y1.val + y2.val :=
  Quotient.ind₂' fun y1 y2 => by rw [← mk_add, val_mk, val_mk, val_mk, Localization.add_mk]; rfl

@[simp]
/--
theorem `val_mul` / 定理 `val_mul`

English:
theorem val_mul
  statement: forall y1 y2 : HomogeneousLocalization 𝒜 x, (y1 * y2).val = y1.val * y2.val
  proof: Quotient.ind₂' fun y1 y2 => by rw [← mk_mul, val_mk, val_mk, val_mk, Localization.mk_mul]; rfl

@[simp]

中文:
定理 val_mul
  结论: 对任意 y1 y2 : HomogeneousLocalization 𝒜 x, (y1 * y2).val = y1.val * y2.val
  证明: Quotient.ind₂' fun y1 y2 => by rw [← mk_mul, val_mk, val_mk, val_mk, Localization.mk_mul]; rfl

@[simp]

Depends on / 依赖: Localization, Localization.mk_mul, Quotient, Quotient.ind, mk_mul, val_mk
-/
theorem val_mul : forall y1 y2 : HomogeneousLocalization 𝒜 x, (y1 * y2).val = y1.val * y2.val :=
  Quotient.ind₂' fun y1 y2 => by rw [← mk_mul, val_mk, val_mk, val_mk, Localization.mk_mul]; rfl

@[simp]
/--
theorem `val_sub` / 定理 `val_sub`

English:
theorem val_sub
  given: (y1 y2 : HomogeneousLocalization 𝒜 x)
  statement: (y1 - y2).val = y1.val - y2.val
  proof: by
  rw [sub_eq_add_neg]; rw [← val_neg]; rw [← val_add]; rfl

@[simp]

中文:
定理 val_sub
  条件: (y1 y2 : HomogeneousLocalization 𝒜 x)
  结论: (y1 - y2).val = y1.val - y2.val
  证明: by
  rw [sub_eq_add_neg]; rw [← val_neg]; rw [← val_add]; rfl

@[simp]

Depends on / 依赖: sub_eq_add_neg, val_add, val_neg
-/
theorem val_sub (y1 y2 : HomogeneousLocalization 𝒜 x) : (y1 - y2).val = y1.val - y2.val := by
  rw [sub_eq_add_neg]; rw [← val_neg]; rw [← val_add]; rfl

@[simp]
/--
theorem `val_pow` / 定理 `val_pow`

English:
theorem val_pow
  statement: forall (y : HomogeneousLocalization 𝒜 x) (n : Nat), (y ^ n).val = y.val ^ n
  proof: Quotient.ind' fun y n => by rw [← mk_pow, val_mk, val_mk, Localization.mk_pow]; rfl

中文:
定理 val_pow
  结论: 对任意 (y : HomogeneousLocalization 𝒜 x) (n : 自然数), (y ^ n).val = y.val ^ n
  证明: Quotient.ind' fun y n => by rw [← mk_pow, val_mk, val_mk, Localization.mk_pow]; rfl

Depends on / 依赖: Localization, Localization.mk_pow, Quotient, Quotient.ind, mk_pow, val_mk
-/
theorem val_pow : forall (y : HomogeneousLocalization 𝒜 x) (n : Nat), (y ^ n).val = y.val ^ n :=
  Quotient.ind' fun y n => by rw [← mk_pow, val_mk, val_mk, Localization.mk_pow]; rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NatCast (HomogeneousLocalization 𝒜 x)
  body: ⟨Nat.unaryCast⟩

中文:
实例 :
  签名: 自然数Cast (HomogeneousLocalization 𝒜 x)
  定义体: ⟨Nat.unaryCast⟩

Depends on / 依赖: Nat.unaryCast, unaryCast
-/
instance : NatCast (HomogeneousLocalization 𝒜 x) :=
  ⟨Nat.unaryCast⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IntCast (HomogeneousLocalization 𝒜 x)
  body: ⟨Int.castDef⟩

@[simp]

中文:
实例 :
  签名: 整数Cast (HomogeneousLocalization 𝒜 x)
  定义体: ⟨Int.castDef⟩

@[simp]

Depends on / 依赖: Int.castDef, castDef
-/
instance : IntCast (HomogeneousLocalization 𝒜 x) :=
  ⟨Int.castDef⟩

@[simp]
/--
theorem `val_natCast` / 定理 `val_natCast`

English:
theorem val_natCast
  given: (n : Nat)
  statement: (n : HomogeneousLocalization 𝒜 x).val = n
  proof: show val (Nat.unaryCast n) = _ by induction n <;> simp [Nat.unaryCast, *]

@[simp]

中文:
定理 val_natCast
  条件: (n : 自然数)
  结论: (n : HomogeneousLocalization 𝒜 x).val = n
  证明: show val (Nat.unaryCast n) = _ by induction n <;> simp [Nat.unaryCast, *]

@[simp]

Depends on / 依赖: Nat.unaryCast, unaryCast
-/
theorem val_natCast (n : Nat) : (n : HomogeneousLocalization 𝒜 x).val = n :=
  show val (Nat.unaryCast n) = _ by induction n <;> simp [Nat.unaryCast, *]

@[simp]
/--
theorem `val_intCast` / 定理 `val_intCast`

English:
theorem val_intCast
  given: (n : Int)
  statement: (n : HomogeneousLocalization 𝒜 x).val = n
  proof: show val (Int.castDef n) = _ by cases n <;> simp [Int.castDef, *]

中文:
定理 val_intCast
  条件: (n : 整数)
  结论: (n : HomogeneousLocalization 𝒜 x).val = n
  证明: show val (Int.castDef n) = _ by cases n <;> simp [Int.castDef, *]

Depends on / 依赖: Int.castDef, castDef
-/
theorem val_intCast (n : Int) : (n : HomogeneousLocalization 𝒜 x).val = n :=
  show val (Int.castDef n) = _ by cases n <;> simp [Int.castDef, *]

/--
Instance `homogeneousLocalizationCommRing` / 实例 `homogeneousLocalizationCommRing`

English:
instance homogeneousLocalizationCommRing
  signature: : CommRing (HomogeneousLocalization 𝒜 x)
  body: (HomogeneousLocalization.val_injective x).commRing _ val_zero val_one val_add val_mul val_neg
    val_sub (val_nsmul x · ·) (val_zsmul x · ·) val_pow val_natCast val_intCast

中文:
实例 homogeneousLocalizationCommRing
  签名: : CommRing (HomogeneousLocalization 𝒜 x)
  定义体: (HomogeneousLocalization.val_injective x).commRing _ val_zero val_one val_add val_mul val_neg
    val_sub (val_nsmul x · ·) (val_zsmul x · ·) val_pow val_natCast val_intCast

Depends on / 依赖: HomogeneousLocalization, HomogeneousLocalization.val_injective, commRing, val_add, val_injective, val_intCast, val_mul, val_natCast, val_neg, val_nsmul, val_one, val_pow, val_sub, val_zero, val_zsmul
-/
instance homogeneousLocalizationCommRing : CommRing (HomogeneousLocalization 𝒜 x) :=
  (HomogeneousLocalization.val_injective x).commRing _ val_zero val_one val_add val_mul val_neg
    val_sub (val_nsmul x · ·) (val_zsmul x · ·) val_pow val_natCast val_intCast

/--
Instance `homogeneousLocalizationAlgebra` / 实例 `homogeneousLocalizationAlgebra`

English:
instance homogeneousLocalizationAlgebra
  signature: :
  body: p.val * q
  algebraMap :=
  { toFun := val
    map_one' := val_one
    map_mul' := val_mul
    map_zero' := val_zero
    map_add' := val_add }
  commutes' _ _ := mul_comm _ _
  smul_def' _ _ := rfl

中文:
实例 homogeneousLocalizationAlgebra
  签名: :
  定义体: p.val * q
  algebraMap :=
  { toFun := val
    map_one' := val_one
    map_mul' := val_mul
    map_zero' := val_zero
    map_add' := val_add }
  commutes' _ _ := mul_comm _ _
  smul_def' _ _ := rfl

Depends on / 依赖: p.val
-/
instance homogeneousLocalizationAlgebra :
    Algebra (HomogeneousLocalization 𝒜 x) (Localization x) where
  smul p q := p.val * q
  algebraMap :=
  { toFun := val
    map_one' := val_one
    map_mul' := val_mul
    map_zero' := val_zero
    map_add' := val_add }
  commutes' _ _ := mul_comm _ _
  smul_def' _ _ := rfl

/--
lemma `algebraMap_apply` / 引理 `algebraMap_apply`

English:
lemma algebraMap_apply
  given: (y)
  proof: rfl

中文:
引理 algebraMap_apply
  条件: (y)
  证明: rfl
-/
@[simp] lemma algebraMap_apply (y) :
    algebraMap (HomogeneousLocalization 𝒜 x) (Localization x) y = y.val := rfl

/--
lemma `mk_eq_zero_of_num` / 引理 `mk_eq_zero_of_num`

English:
lemma mk_eq_zero_of_num
  given: (f : NumDenSameDeg 𝒜 x) (h : f.num = 0)
  statement: mk f = 0
  proof: by
  apply val_injective
  simp only [val_mk, val_zero, h, ZeroMemClass.coe_zero, Localization.mk_zero]

中文:
引理 mk_eq_zero_of_num
  条件: (f : NumDenSameDeg 𝒜 x) (h : f.num = 0)
  结论: mk f = 0
  证明: by
  apply val_injective
  simp only [val_mk, val_zero, h, ZeroMemClass.coe_zero, Localization.mk_zero]

Depends on / 依赖: Localization, Localization.mk_zero, ZeroMemClass, ZeroMemClass.coe_zero, coe_zero, mk_zero, val_injective, val_mk, val_zero
-/
lemma mk_eq_zero_of_num (f : NumDenSameDeg 𝒜 x) (h : f.num = 0) : mk f = 0 := by
  apply val_injective
  simp only [val_mk, val_zero, h, ZeroMemClass.coe_zero, Localization.mk_zero]

/--
lemma `mk_eq_zero_of_den` / 引理 `mk_eq_zero_of_den`

English:
lemma mk_eq_zero_of_den
  given: (f : NumDenSameDeg 𝒜 x) (h : f.den = 0)
  statement: mk f = 0
  proof: by
  have := subsingleton 𝒜 (h ▸ f.den_mem)
  exact Subsingleton.elim _ _

中文:
引理 mk_eq_zero_of_den
  条件: (f : NumDenSameDeg 𝒜 x) (h : f.den = 0)
  结论: mk f = 0
  证明: by
  have := subsingleton 𝒜 (h ▸ f.den_mem)
  exact Subsingleton.elim _ _

Depends on / 依赖: Subsingleton, Subsingleton.elim, den_mem, f.den_mem, subsingleton
-/
lemma mk_eq_zero_of_den (f : NumDenSameDeg 𝒜 x) (h : f.den = 0) : mk f = 0 := by
  have := subsingleton 𝒜 (h ▸ f.den_mem)
  exact Subsingleton.elim _ _

variable (𝒜 x) in
/--
Definition of `fromZeroRingHom` / `fromZeroRingHom` 的定义

English:
definition fromZeroRingHom
  signature: : 𝒜 0 ->+* HomogeneousLocalization 𝒜 x where
  body: .mk ⟨0, f, 1, one_mem _⟩
  map_one' := rfl
  map_mul' f g := by ext; simp [Localization.mk_mul]
  map_zero' := rfl
  map_add' f g := by ext; simp [Localization.add_mk, add_comm f.1 g.1]

中文:
定义 fromZeroRingHom
  签名: : 𝒜 0 ->+* HomogeneousLocalization 𝒜 x where
  定义体: .mk ⟨0, f, 1, one_mem _⟩
  map_one' := rfl
  map_mul' f g := by ext; simp [Localization.mk_mul]
  map_zero' := rfl
  map_add' f g := by ext; simp [Localization.add_mk, add_comm f.1 g.1]

Depends on / 依赖: one_mem
-/
def fromZeroRingHom : 𝒜 0 ->+* HomogeneousLocalization 𝒜 x where
  toFun f := .mk ⟨0, f, 1, one_mem _⟩
  map_one' := rfl
  map_mul' f g := by ext; simp [Localization.mk_mul]
  map_zero' := rfl
  map_add' f g := by ext; simp [Localization.add_mk, add_comm f.1 g.1]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra (𝒜 0) (HomogeneousLocalization 𝒜 x)
  body: (fromZeroRingHom 𝒜 x).toAlgebra

中文:
实例 :
  签名: Algebra (𝒜 0) (HomogeneousLocalization 𝒜 x)
  定义体: (fromZeroRingHom 𝒜 x).toAlgebra

Depends on / 依赖: fromZeroRingHom, toAlgebra
-/
instance : Algebra (𝒜 0) (HomogeneousLocalization 𝒜 x) :=
  (fromZeroRingHom 𝒜 x).toAlgebra

/--
lemma `algebraMap_eq` / 引理 `algebraMap_eq`

English:
lemma algebraMap_eq
  statement: algebraMap (𝒜 0) (HomogeneousLocalization 𝒜 x) = fromZeroRingHom 𝒜 x
  proof: rfl

中文:
引理 algebraMap_eq
  结论: algebraMap (𝒜 0) (HomogeneousLocalization 𝒜 x) = fromZeroRingHom 𝒜 x
  证明: rfl
-/
lemma algebraMap_eq : algebraMap (𝒜 0) (HomogeneousLocalization 𝒜 x) = fromZeroRingHom 𝒜 x := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsScalarTower (𝒜 0) (HomogeneousLocalization 𝒜 x) (Localization x)
  body: .of_algebraMap_eq' rfl

中文:
实例 :
  签名: IsScalarTower (𝒜 0) (HomogeneousLocalization 𝒜 x) (Localization x)
  定义体: .of_algebraMap_eq' rfl

Depends on / 依赖: of_algebraMap_eq
-/
instance : IsScalarTower (𝒜 0) (HomogeneousLocalization 𝒜 x) (Localization x) :=
  .of_algebraMap_eq' rfl

end HomogeneousLocalization

namespace HomogeneousLocalization

open HomogeneousLocalization HomogeneousLocalization.NumDenSameDeg

section
variable {𝒜 : ι -> σ} {x : Submonoid A}

/--
Definition of `num` / `num` 的定义

English:
definition num
  signature: (f : HomogeneousLocalization 𝒜 x)
  body: (Quotient.out f).num

中文:
定义 num
  签名: (f : HomogeneousLocalization 𝒜 x)
  定义体: (Quotient.out f).num

Depends on / 依赖: Quotient, Quotient.out
-/
def num (f : HomogeneousLocalization 𝒜 x) : A :=
  (Quotient.out f).num

/--
Definition of `den` / `den` 的定义

English:
definition den
  signature: (f : HomogeneousLocalization 𝒜 x)
  body: (Quotient.out f).den

中文:
定义 den
  签名: (f : HomogeneousLocalization 𝒜 x)
  定义体: (Quotient.out f).den

Depends on / 依赖: Quotient, Quotient.out
-/
def den (f : HomogeneousLocalization 𝒜 x) : A :=
  (Quotient.out f).den

/--
Definition of `deg` / `deg` 的定义

English:
definition deg
  signature: (f : HomogeneousLocalization 𝒜 x)
  body: (Quotient.out f).deg

中文:
定义 deg
  签名: (f : HomogeneousLocalization 𝒜 x)
  定义体: (Quotient.out f).deg

Depends on / 依赖: Quotient, Quotient.out
-/
def deg (f : HomogeneousLocalization 𝒜 x) : ι :=
  (Quotient.out f).deg

/--
theorem `den_mem` / 定理 `den_mem`

English:
theorem den_mem
  given: (f : HomogeneousLocalization 𝒜 x)
  statement: f.den in x
  proof: (Quotient.out f).den_mem

中文:
定理 den_mem
  条件: (f : HomogeneousLocalization 𝒜 x)
  结论: f.den in x
  证明: (Quotient.out f).den_mem

Depends on / 依赖: Quotient, Quotient.out, den_mem
-/
theorem den_mem (f : HomogeneousLocalization 𝒜 x) : f.den in x :=
  (Quotient.out f).den_mem

/--
theorem `num_mem_deg` / 定理 `num_mem_deg`

English:
theorem num_mem_deg
  given: (f : HomogeneousLocalization 𝒜 x)
  statement: f.num in 𝒜 f.deg
  proof: (Quotient.out f).num.2

中文:
定理 num_mem_deg
  条件: (f : HomogeneousLocalization 𝒜 x)
  结论: f.num in 𝒜 f.deg
  证明: (Quotient.out f).num.2

Depends on / 依赖: Quotient, Quotient.out
-/
theorem num_mem_deg (f : HomogeneousLocalization 𝒜 x) : f.num in 𝒜 f.deg :=
  (Quotient.out f).num.2

/--
theorem `den_mem_deg` / 定理 `den_mem_deg`

English:
theorem den_mem_deg
  given: (f : HomogeneousLocalization 𝒜 x)
  statement: f.den in 𝒜 f.deg
  proof: (Quotient.out f).den.2

中文:
定理 den_mem_deg
  条件: (f : HomogeneousLocalization 𝒜 x)
  结论: f.den in 𝒜 f.deg
  证明: (Quotient.out f).den.2

Depends on / 依赖: Quotient, Quotient.out
-/
theorem den_mem_deg (f : HomogeneousLocalization 𝒜 x) : f.den in 𝒜 f.deg :=
  (Quotient.out f).den.2

/--
theorem `eq_num_div_den` / 定理 `eq_num_div_den`

English:
theorem eq_num_div_den
  given: (f : HomogeneousLocalization 𝒜 x)
  proof: congr_arg HomogeneousLocalization.val (Quotient.out_eq' f).symm

中文:
定理 eq_num_div_den
  条件: (f : HomogeneousLocalization 𝒜 x)
  证明: congr_arg HomogeneousLocalization.val (Quotient.out_eq' f).symm

Depends on / 依赖: HomogeneousLocalization, HomogeneousLocalization.val, Quotient, Quotient.out_eq, congr_arg, out_eq
-/
theorem eq_num_div_den (f : HomogeneousLocalization 𝒜 x) :
    f.val = Localization.mk f.num ⟨f.den, f.den_mem⟩ :=
  congr_arg HomogeneousLocalization.val (Quotient.out_eq' f).symm

/--
theorem `den_smul_val` / 定理 `den_smul_val`

English:
theorem den_smul_val
  given: (f : HomogeneousLocalization 𝒜 x)
  proof: by
  rw [eq_num_div_den]; rw [Localization.mk_eq_mk']; rw [IsLocalization.smul_mk']
  exact IsLocalization.mk'_mul_cancel_left _ ⟨_, _⟩

中文:
定理 den_smul_val
  条件: (f : HomogeneousLocalization 𝒜 x)
  证明: by
  rw [eq_num_div_den]; rw [Localization.mk_eq_mk']; rw [IsLocalization.smul_mk']
  exact IsLocalization.mk'_mul_cancel_left _ ⟨_, _⟩

Depends on / 依赖: IsLocalization, IsLocalization.mk, IsLocalization.smul_mk, Localization, Localization.mk_eq_mk, _mul_cancel_left, eq_num_div_den, mk_eq_mk, smul_mk
-/
theorem den_smul_val (f : HomogeneousLocalization 𝒜 x) :
    f.den • f.val = algebraMap _ _ f.num := by
  rw [eq_num_div_den]; rw [Localization.mk_eq_mk']; rw [IsLocalization.smul_mk']
  exact IsLocalization.mk'_mul_cancel_left _ ⟨_, _⟩

/--
theorem `ext_iff_val` / 定理 `ext_iff_val`

English:
theorem ext_iff_val
  given: (f g : HomogeneousLocalization 𝒜 x)
  statement: f = g ↔ f.val = g.val
  proof: ⟨congr_arg val, fun e => val_injective x e⟩

中文:
定理 ext_iff_val
  条件: (f g : HomogeneousLocalization 𝒜 x)
  结论: f = g ↔ f.val = g.val
  证明: ⟨congr_arg val, fun e => val_injective x e⟩

Depends on / 依赖: congr_arg, val_injective
-/
theorem ext_iff_val (f g : HomogeneousLocalization 𝒜 x) : f = g ↔ f.val = g.val :=
  ⟨congr_arg val, fun e => val_injective x e⟩

end

section

variable [AddSubgroupClass σ A] {𝒜 : ι -> σ} {x : Submonoid A}
variable [AddCommMonoid ι] [DecidableEq ι] [GradedRing 𝒜]
variable (𝒜) (𝔭 : Ideal A) [Ideal.IsPrime 𝔭]

/--
Definition of `AtPrime` / `AtPrime` 的定义

English:
abbreviation AtPrime
  body: HomogeneousLocalization 𝒜 𝔭.primeCompl

中文:
缩写 AtPrime
  定义体: HomogeneousLocalization 𝒜 𝔭.primeCompl

Depends on / 依赖: HomogeneousLocalization, primeCompl
-/
abbrev AtPrime :=
  HomogeneousLocalization 𝒜 𝔭.primeCompl

/--
theorem `isUnit_iff_isUnit_val` / 定理 `isUnit_iff_isUnit_val`

English:
theorem isUnit_iff_isUnit_val
  given: (f : HomogeneousLocalization.AtPrime 𝒜 𝔭)
  proof: by
  refine ⟨fun h1 => ?_, IsUnit.map (algebraMap _ _)⟩
  rcases h1 with ⟨⟨a, b, eq0, eq1⟩, rfl : a = f.val⟩
  obtain ⟨f, rfl⟩ := mk_surjective f
  obtain ⟨b, s, rfl⟩ := IsLocalization.exists_mk'_eq 𝔭.primeCompl b
  rw [val_mk]; rw [Localization.mk_eq_mk']; rw [← IsLocalization.mk'_mul]; rw [IsLocal

中文:
定理 isUnit_iff_isUnit_val
  条件: (f : HomogeneousLocalization.AtPrime 𝒜 𝔭)
  证明: by
  refine ⟨fun h1 => ?_, IsUnit.map (algebraMap _ _)⟩
  rcases h1 with ⟨⟨a, b, eq0, eq1⟩, rfl : a = f.val⟩
  obtain ⟨f, rfl⟩ := mk_surjective f
  obtain ⟨b, s, rfl⟩ := IsLocalization.exists_mk'_eq 𝔭.primeCompl b
  rw [val_mk]; rw [Localization.mk_eq_mk']; rw [← IsLocalization.mk'_mul]; rw [IsLocal

Depends on / 依赖: IsLocalization, IsLocalization.eq_iff_exists, IsLocalization.exists_mk, IsLocalization.mk, IsUnit, IsUnit.map, Localization, Localization.mk_eq_mk, _eq_iff_eq_mul, _mul, algebraMap, eq_iff_exists, exists_mk, f.den, f.num, f.val, mk_eq_mk, mk_surjective, mul_, mul_mem
-/
theorem isUnit_iff_isUnit_val (f : HomogeneousLocalization.AtPrime 𝒜 𝔭) :
    IsUnit f.val ↔ IsUnit f := by
  refine ⟨fun h1 => ?_, IsUnit.map (algebraMap _ _)⟩
  rcases h1 with ⟨⟨a, b, eq0, eq1⟩, rfl : a = f.val⟩
  obtain ⟨f, rfl⟩ := mk_surjective f
  obtain ⟨b, s, rfl⟩ := IsLocalization.exists_mk'_eq 𝔭.primeCompl b
  rw [val_mk]; rw [Localization.mk_eq_mk']; rw [← IsLocalization.mk'_mul]; rw [IsLocalization.mk'_eq_iff_eq_mul]; rw [one_mul]; rw [IsLocalization.eq_iff_exists (M := 𝔭.primeCompl)] at eq0
  obtain ⟨c, hc : _ = c.1 * (f.den.1 * s.1)⟩ := eq0
  have : f.num.1 ∉ 𝔭 := by
    exact fun h => mul_mem c.2 (mul_mem f.den_mem s.2)
      (hc ▸ Ideal.mul_mem_left _ c.1 (Ideal.mul_mem_right b _ h))
  refine .of_mul_eq_one (Quotient.mk'' ⟨f.1, f.3, f.2, this⟩) ?_
  rw [← mk_mul]; rw [ext_iff_val]; rw [val_mk]
  simp [mul_comm f.den.1]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Nontrivial (HomogeneousLocalization.AtPrime 𝒜 𝔭)
  body: ⟨⟨0, 1, fun r => by simp [ext_iff_val, val_zero, val_one, zero_ne_one] at r⟩⟩

中文:
实例 :
  签名: Nontrivial (HomogeneousLocalization.AtPrime 𝒜 𝔭)
  定义体: ⟨⟨0, 1, fun r => by simp [ext_iff_val, val_zero, val_one, zero_ne_one] at r⟩⟩

Depends on / 依赖: ext_iff_val, val_one, val_zero, zero_ne_one
-/
instance : Nontrivial (HomogeneousLocalization.AtPrime 𝒜 𝔭) :=
  ⟨⟨0, 1, fun r => by simp [ext_iff_val, val_zero, val_one, zero_ne_one] at r⟩⟩

/--
Instance `isLocalRing` / 实例 `isLocalRing`

English:
instance isLocalRing
  signature: : IsLocalRing (HomogeneousLocalization.AtPrime 𝒜 𝔭)
  body: IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    simpa only [← isUnit_iff_isUnit_val, val_sub, val_one]
      using IsLocalRing.isUnit_or_isUnit_one_sub_self _

中文:
实例 isLocalRing
  签名: : IsLocalRing (HomogeneousLocalization.AtPrime 𝒜 𝔭)
  定义体: IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    simpa only [← isUnit_iff_isUnit_val, val_sub, val_one]
      using IsLocalRing.isUnit_or_isUnit_one_sub_self _

Depends on / 依赖: IsLocalRing, IsLocalRing.isUnit_or_isUnit_one_sub_self, IsLocalRing.of_isUnit_or_isUnit_one_sub_self, isUnit_iff_isUnit_val, isUnit_or_isUnit_one_sub_self, of_isUnit_or_isUnit_one_sub_self, val_one, val_sub
-/
instance isLocalRing : IsLocalRing (HomogeneousLocalization.AtPrime 𝒜 𝔭) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    simpa only [← isUnit_iff_isUnit_val, val_sub, val_one]
      using IsLocalRing.isUnit_or_isUnit_one_sub_self _

end

section

/--
Definition of `Away` / `Away` 的定义

English:
abbreviation Away
  signature: (𝒜 : ι -> σ) (f : A)
  body: HomogeneousLocalization 𝒜 (Submonoid.powers f)

中文:
缩写 Away
  签名: (𝒜 : ι -> σ) (f : A)
  定义体: HomogeneousLocalization 𝒜 (Submonoid.powers f)

Depends on / 依赖: HomogeneousLocalization, Submonoid, Submonoid.powers, powers
-/
abbrev Away (𝒜 : ι -> σ) (f : A) :=
  HomogeneousLocalization 𝒜 (Submonoid.powers f)

variable [AddSubgroupClass σ A] [AddCommMonoid ι] [DecidableEq ι]
variable (𝒜 : ι -> σ) [GradedRing 𝒜] {f : A}

/--
Definition of `Away.mk` / `Away.mk` 的定义

English:
definition Away.mk
  signature: {d : ι} (hf : f in 𝒜 d) (n : Nat) (x : A) (hx : x in 𝒜 (n • d))
  body: HomogeneousLocalization.mk ⟨n • d, ⟨x, hx⟩, ⟨f ^ n, SetLike.pow_mem_graded n hf⟩, ⟨n, rfl⟩⟩

@[simp]

中文:
定义 Away.mk
  签名: {d : ι} (hf : f in 𝒜 d) (n : 自然数) (x : A) (hx : x in 𝒜 (n • d))
  定义体: HomogeneousLocalization.mk ⟨n • d, ⟨x, hx⟩, ⟨f ^ n, SetLike.pow_mem_graded n hf⟩, ⟨n, rfl⟩⟩

@[simp]
-/
protected def Away.mk {d : ι} (hf : f in 𝒜 d) (n : Nat) (x : A) (hx : x in 𝒜 (n • d)) : Away 𝒜 f :=
  HomogeneousLocalization.mk ⟨n • d, ⟨x, hx⟩, ⟨f ^ n, SetLike.pow_mem_graded n hf⟩, ⟨n, rfl⟩⟩

@[simp]
/--
lemma `Away.val_mk` / 引理 `Away.val_mk`

English:
lemma Away.val_mk
  given: {d : ι} (n : Nat) (hf : f in 𝒜 d) (x : A) (hx : x in 𝒜 (n • d))
  proof: rfl

protected

中文:
引理 Away.val_mk
  条件: {d : ι} (n : 自然数) (hf : f in 𝒜 d) (x : A) (hx : x in 𝒜 (n • d))
  证明: rfl

protected
-/
lemma Away.val_mk {d : ι} (n : Nat) (hf : f in 𝒜 d) (x : A) (hx : x in 𝒜 (n • d)) :
    (Away.mk 𝒜 hf n x hx).val = Localization.mk x ⟨f ^ n, by use n⟩ :=
  rfl

protected
/--
lemma `Away.mk_surjective` / 引理 `Away.mk_surjective`

English:
lemma Away.mk_surjective
  given: {d : ι} (hf : f in 𝒜 d) (x : Away 𝒜 f)
  proof: by
  obtain ⟨⟨N, ⟨s, hs⟩, ⟨b, hn⟩, ⟨n, (rfl : _ = b)⟩⟩, rfl⟩ := mk_surjective x
  by_cases hfn : f ^ n = 0
  · have := HomogeneousLocalization.subsingleton 𝒜 (x := .powers f) ⟨n, hfn⟩
    exact ⟨0, 0, zero_mem _, Subsingleton.elim _ _⟩
  obtain rfl := DirectSum.degree_eq_of_mem_mem 𝒜 hn (SetLike.pow

中文:
引理 Away.mk_surjective
  条件: {d : ι} (hf : f in 𝒜 d) (x : Away 𝒜 f)
  证明: by
  obtain ⟨⟨N, ⟨s, hs⟩, ⟨b, hn⟩, ⟨n, (rfl : _ = b)⟩⟩, rfl⟩ := mk_surjective x
  by_cases hfn : f ^ n = 0
  · have := HomogeneousLocalization.subsingleton 𝒜 (x := .powers f) ⟨n, hfn⟩
    exact ⟨0, 0, zero_mem _, Subsingleton.elim _ _⟩
  obtain rfl := DirectSum.degree_eq_of_mem_mem 𝒜 hn (SetLike.pow

Depends on / 依赖: DirectSum, DirectSum.degree_eq_of_mem_mem, HomogeneousLocalization, HomogeneousLocalization.subsingleton, SetLike, SetLike.pow_mem_graded, Subsingleton, Subsingleton.elim, degree_eq_of_mem_mem, mk_surjective, pow_mem_graded, powers, subsingleton, zero_mem
-/
lemma Away.mk_surjective {d : ι} (hf : f in 𝒜 d) (x : Away 𝒜 f) :
    exists n a ha, Away.mk 𝒜 hf n a ha = x := by
  obtain ⟨⟨N, ⟨s, hs⟩, ⟨b, hn⟩, ⟨n, (rfl : _ = b)⟩⟩, rfl⟩ := mk_surjective x
  by_cases hfn : f ^ n = 0
  · have := HomogeneousLocalization.subsingleton 𝒜 (x := .powers f) ⟨n, hfn⟩
    exact ⟨0, 0, zero_mem _, Subsingleton.elim _ _⟩
  obtain rfl := DirectSum.degree_eq_of_mem_mem 𝒜 hn (SetLike.pow_mem_graded n hf) hfn
  exact ⟨n, s, hs, by ext; simp⟩

variable {𝒜}

/--
theorem `Away.eventually_smul_mem` / 定理 `Away.eventually_smul_mem`

English:
theorem Away.eventually_smul_mem
  given: {m} (hf : f in 𝒜 m) (z : Away 𝒜 f)
  proof: by
  obtain ⟨k, hk : f ^ k = _⟩ := z.den_mem
  apply Filter.mem_of_superset (Filter.Ici_mem_atTop k)
  rintro k' (hk' : k <= k')
  simp only [Set.mem_image, SetLike.mem_coe, Set.mem_ofPred_eq]
  by_cases hfk : f ^ k = 0
  · refine ⟨0, zero_mem _, ?_⟩
    rw [← tsub_add_cancel_of_le hk']; rw [map_zer

中文:
定理 Away.eventually_smul_mem
  条件: {m} (hf : f in 𝒜 m) (z : Away 𝒜 f)
  证明: by
  obtain ⟨k, hk : f ^ k = _⟩ := z.den_mem
  apply Filter.mem_of_superset (Filter.Ici_mem_atTop k)
  rintro k' (hk' : k <= k')
  simp only [Set.mem_image, SetLike.mem_coe, Set.mem_ofPred_eq]
  by_cases hfk : f ^ k = 0
  · refine ⟨0, zero_mem _, ?_⟩
    rw [← tsub_add_cancel_of_le hk']; rw [map_zer

Depends on / 依赖: Algebra, Algebra.smul_def, Filter, Filter.Ici_mem_atTop, Filter.mem_of_superset, Ici_mem_atTop, Set.mem_image, Set.mem_ofPred_eq, SetLike, SetLike.mem_coe, add_s, den_mem, den_smul_val, map_mul, map_zero, mem_coe, mem_image, mem_ofPred_eq, mem_of_superset, mul_smul
-/
theorem Away.eventually_smul_mem {m} (hf : f in 𝒜 m) (z : Away 𝒜 f) :
    forallᶠ n in Filter.atTop, f ^ n • z.val in algebraMap _ _ '' (𝒜 (n • m) : Set A) := by
  obtain ⟨k, hk : f ^ k = _⟩ := z.den_mem
  apply Filter.mem_of_superset (Filter.Ici_mem_atTop k)
  rintro k' (hk' : k <= k')
  simp only [Set.mem_image, SetLike.mem_coe, Set.mem_ofPred_eq]
  by_cases hfk : f ^ k = 0
  · refine ⟨0, zero_mem _, ?_⟩
    rw [← tsub_add_cancel_of_le hk']; rw [map_zero]; rw [pow_add]; rw [hfk]; rw [mul_zero]; rw [zero_smul]
  rw [← tsub_add_cancel_of_le hk']; rw [pow_add]; rw [mul_smul]; rw [hk]; rw [den_smul_val]; rw [Algebra.smul_def]; rw [← map_mul]
  rw [← smul_eq_mul]; rw [add_smul]; rw [DirectSum.degree_eq_of_mem_mem 𝒜 (SetLike.pow_mem_graded _ hf) (hk.symm ▸ z.den_mem_deg) hfk]
  exact ⟨_, SetLike.mul_mem_graded (SetLike.pow_mem_graded _ hf) z.num_mem_deg, rfl⟩

end

section

variable [AddSubgroupClass σ A] [AddCommMonoid ι] [DecidableEq ι]
variable {𝒜 : ι -> σ} [GradedRing 𝒜]
variable {B τ : Type*} [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
variable {ℬ : ι -> τ} [GradedRing ℬ]
variable {C ψ : Type*} [CommRing C] [SetLike ψ C] [AddSubgroupClass ψ C]
variable {𝒞 : ι -> ψ} [GradedRing 𝒞]
variable {P : Submonoid A} {Q : Submonoid B}

open Graded

/--
Definition of `NumDenSameDeg.map` / `NumDenSameDeg.map` 的定义

English:
definition NumDenSameDeg.map
  signature: (f : 𝒜 ->+*ᵍ ℬ) {W₁ : Submonoid A} {W₂ : Submonoid B}
  body: c.deg
  den := f.gradedAddHom _ c.den
  num := f.gradedAddHom _ c.num
  den_mem := hw c.den_mem

中文:
定义 NumDenSameDeg.map
  签名: (f : 𝒜 ->+*ᵍ ℬ) {W₁ : Submonoid A} {W₂ : Submonoid B}
  定义体: c.deg
  den := f.gradedAddHom _ c.den
  num := f.gradedAddHom _ c.num
  den_mem := hw c.den_mem
-/
@[simps] def NumDenSameDeg.map (f : 𝒜 ->+*ᵍ ℬ) {W₁ : Submonoid A} {W₂ : Submonoid B}
    (hw : W₁ <= W₂.comap f) (c : NumDenSameDeg 𝒜 W₁) : NumDenSameDeg ℬ W₂ where
  deg := c.deg
  den := f.gradedAddHom _ c.den
  num := f.gradedAddHom _ c.num
  den_mem := hw c.den_mem

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (g : 𝒜 ->+*ᵍ ℬ) (comap_le : P <= Q.comap g)
  body: Quotient.map'
    (fun x => ⟨x.1, ⟨_, map_mem g x.2.2⟩, ⟨_, map_mem g x.3.2⟩, comap_le x.4⟩)
    fun x y (e : x.embedding = y.embedding) => by
      apply_fun IsLocalization.map (Localization Q) g.toRingHom comap_le at e
      simp_rw [HomogeneousLocalization.NumDenSameDeg.embedding, Localization.mk

中文:
定义 map
  签名: (g : 𝒜 ->+*ᵍ ℬ) (comap_le : P <= Q.comap g)
  定义体: Quotient.map'
    (fun x => ⟨x.1, ⟨_, map_mem g x.2.2⟩, ⟨_, map_mem g x.3.2⟩, comap_le x.4⟩)
    fun x y (e : x.embedding = y.embedding) => by
      apply_fun IsLocalization.map (Localization Q) g.toRingHom comap_le at e
      simp_rw [HomogeneousLocalization.NumDenSameDeg.embedding, Localization.mk

Depends on / 依赖: Quotient, Quotient.map
-/
def map (g : 𝒜 ->+*ᵍ ℬ) (comap_le : P <= Q.comap g) :
    HomogeneousLocalization 𝒜 P ->+* HomogeneousLocalization ℬ Q where
  toFun := Quotient.map'
    (fun x => ⟨x.1, ⟨_, map_mem g x.2.2⟩, ⟨_, map_mem g x.3.2⟩, comap_le x.4⟩)
    fun x y (e : x.embedding = y.embedding) => by
      apply_fun IsLocalization.map (Localization Q) g.toRingHom comap_le at e
      simp_rw [HomogeneousLocalization.NumDenSameDeg.embedding, Localization.mk_eq_mk',
        IsLocalization.map_mk', ← Localization.mk_eq_mk'] at e
      exact e
  map_add' := Quotient.ind₂' fun x y => by
    simp only [← mk_add, Quotient.map'_mk'', num_add, map_add, map_mul, den_add]; rfl
  map_mul' := Quotient.ind₂' fun x y => by
    simp only [← mk_mul, Quotient.map'_mk'', num_mul, map_mul, den_mul]; rfl
  map_zero' := by simp only [← mk_zero (𝒜 := 𝒜), Quotient.map'_mk'', deg_zero,
    num_zero, ZeroMemClass.coe_zero, map_zero, den_zero, map_one]; rfl
  map_one' := by simp only [← mk_one (𝒜 := 𝒜), Quotient.map'_mk'',
    num_one, den_one, map_one]; rfl

variable (𝒜) in
/--
Definition of `mapId` / `mapId` 的定义

English:
abbreviation mapId
  signature: {P Q : Submonoid A} (h : P <= Q)
  body: map (.id _) h

中文:
缩写 mapId
  签名: {P Q : Submonoid A} (h : P <= Q)
  定义体: map (.id _) h
-/
abbrev mapId {P Q : Submonoid A} (h : P <= Q) :
    HomogeneousLocalization 𝒜 P ->+* HomogeneousLocalization 𝒜 Q :=
  map (.id _) h

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `map_mk` / 引理 `map_mk`

English:
lemma map_mk
  given: (g : 𝒜 ->+*ᵍ ℬ) (comap_le : P <= Q.comap g) (x)
  proof: rfl

中文:
引理 map_mk
  条件: (g : 𝒜 ->+*ᵍ ℬ) (comap_le : P <= Q.comap g) (x)
  证明: rfl
-/
lemma map_mk (g : 𝒜 ->+*ᵍ ℬ) (comap_le : P <= Q.comap g) (x) :
    map g comap_le (mk x) = mk ⟨x.1, ⟨_, map_mem g x.2.2⟩, ⟨_, map_mem g x.3.2⟩, comap_le x.4⟩ :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
variable (𝒜) in
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  given: (P : Submonoid A)
  statement: map (.id 𝒜) (P := P) (Q := P) le_rfl = .id _
  proof: by
  ext x
  obtain ⟨c, rfl⟩ := x.mk_surjective
  simp [map_mk]

中文:
定理 map_id
  条件: (P : Submonoid A)
  结论: map (.id 𝒜) (P := P) (Q := P) le_rfl = .id _
  证明: by
  ext x
  obtain ⟨c, rfl⟩ := x.mk_surjective
  simp [map_mk]
-/
@[simp] theorem map_id (P : Submonoid A) : map (.id 𝒜) (P := P) (Q := P) le_rfl = .id _ := by
  ext x
  obtain ⟨c, rfl⟩ := x.mk_surjective
  simp [map_mk]

/--
theorem `map_comp` / 定理 `map_comp`

English:
theorem map_comp
  statement: {f : 𝒜 ->+*ᵍ ℬ} {g : ℬ ->+*ᵍ 𝒞}
  proof: by
  ext x
  obtain ⟨c, rfl⟩ := x.mk_surjective
  simp [map_mk]

中文:
定理 map_comp
  结论: {f : 𝒜 ->+*ᵍ ℬ} {g : ℬ ->+*ᵍ 𝒞}
  证明: by
  ext x
  obtain ⟨c, rfl⟩ := x.mk_surjective
  simp [map_mk]

Depends on / 依赖: map_mk, mk_surjective, x.mk_surjective
-/
theorem map_comp {f : 𝒜 ->+*ᵍ ℬ} {g : ℬ ->+*ᵍ 𝒞}
    {P : Submonoid A} {Q : Submonoid B} {R : Submonoid C}
    (hpq : P <= Q.comap f) (hqr : Q <= R.comap g) :
    map (g.comp f) (hpq.trans <| Submonoid.monotone_comap hqr) = (map g hqr).comp (map f hpq) := by
  ext x
  obtain ⟨c, rfl⟩ := x.mk_surjective
  simp [map_mk]

/--
theorem `map_map` / 定理 `map_map`

English:
theorem map_map
  statement: {f : 𝒜 ->+*ᵍ ℬ} {g : ℬ ->+*ᵍ 𝒞}
  proof: congr($(map_comp hpq hqr |>.symm) x)

中文:
定理 map_map
  结论: {f : 𝒜 ->+*ᵍ ℬ} {g : ℬ ->+*ᵍ 𝒞}
  证明: congr($(map_comp hpq hqr |>.symm) x)

Depends on / 依赖: map_comp
-/
theorem map_map {f : 𝒜 ->+*ᵍ ℬ} {g : ℬ ->+*ᵍ 𝒞}
    {P : Submonoid A} {Q : Submonoid B} {R : Submonoid C}
    (hpq : P <= Q.comap f) (hqr : Q <= R.comap g) (x : HomogeneousLocalization 𝒜 P) :
    map g hqr (map f hpq x) = map (g.comp f) (hpq.trans <| Submonoid.monotone_comap hqr) x :=
  congr($(map_comp hpq hqr |>.symm) x)

/--
Definition of `Away.map` / `Away.map` 的定义

English:
definition Away.map
  signature: (g : 𝒜 ->+*ᵍ ℬ) (f : A)
  body: map g by rintro _ ⟨n, rfl⟩; exact ⟨n, by simp⟩

中文:
定义 Away.map
  签名: (g : 𝒜 ->+*ᵍ ℬ) (f : A)
  定义体: map g by rintro _ ⟨n, rfl⟩; exact ⟨n, by simp⟩
-/
protected def Away.map (g : 𝒜 ->+*ᵍ ℬ) (f : A) : Away 𝒜 f ->+* Away ℬ (g f) :=
map g by rintro _ ⟨n, rfl⟩; exact ⟨n, by simp⟩

/--
lemma `Away.map_mk` / 引理 `Away.map_mk`

English:
lemma Away.map_mk
  statement: {d : ι} (g : 𝒜 ->+*ᵍ ℬ) (f : A) (hf : f in 𝒜 d) (n : Nat) (x : A)
  proof: by
  simp [Away.map, Away.mk, HomogeneousLocalization.map_mk]

中文:
引理 Away.map_mk
  结论: {d : ι} (g : 𝒜 ->+*ᵍ ℬ) (f : A) (hf : f in 𝒜 d) (n : 自然数) (x : A)
  证明: by
  simp [Away.map, Away.mk, HomogeneousLocalization.map_mk]
-/
@[simp] lemma Away.map_mk {d : ι} (g : 𝒜 ->+*ᵍ ℬ) (f : A) (hf : f in 𝒜 d) (n : Nat) (x : A)
    (hx : x in 𝒜 (n • d)) :
    Away.map g f (.mk 𝒜 hf n x hx) = .mk ℬ (map_mem g hf) n (g x) (map_mem g hx) := by
  simp [Away.map, Away.mk, HomogeneousLocalization.map_mk]

variable (𝒜) in
/--
lemma `Away.map_id` / 引理 `Away.map_id`

English:
lemma Away.map_id
  given: (f : A)
  statement: Away.map (.id 𝒜) f = .id _
  proof: HomogeneousLocalization.map_id ..

中文:
引理 Away.map_id
  条件: (f : A)
  结论: Away.map (.id 𝒜) f = .id _
  证明: HomogeneousLocalization.map_id ..
-/
@[simp] lemma Away.map_id (f : A) : Away.map (.id 𝒜) f = .id _ :=
  HomogeneousLocalization.map_id ..

/--
lemma `Away.map_comp` / 引理 `Away.map_comp`

English:
lemma Away.map_comp
  given: (f : 𝒜 ->+*ᵍ ℬ) (g : ℬ ->+*ᵍ 𝒞) (s : A)
  proof: HomogeneousLocalization.map_comp ..

中文:
引理 Away.map_comp
  条件: (f : 𝒜 ->+*ᵍ ℬ) (g : ℬ ->+*ᵍ 𝒞) (s : A)
  证明: HomogeneousLocalization.map_comp ..
-/
@[simp] lemma Away.map_comp (f : 𝒜 ->+*ᵍ ℬ) (g : ℬ ->+*ᵍ 𝒞) (s : A) :
    Away.map (g.comp f) s = (Away.map g (f s)).comp (Away.map f s) :=
  HomogeneousLocalization.map_comp ..

/--
theorem `Away.map_map` / 定理 `Away.map_map`

English:
theorem Away.map_map
  given: (f : 𝒜 ->+*ᵍ ℬ) (g : ℬ ->+*ᵍ 𝒞) (s : A) (x : Away 𝒜 s)
  proof: HomogeneousLocalization.map_map ..

中文:
定理 Away.map_map
  条件: (f : 𝒜 ->+*ᵍ ℬ) (g : ℬ ->+*ᵍ 𝒞) (s : A) (x : Away 𝒜 s)
  证明: HomogeneousLocalization.map_map ..

Depends on / 依赖: HomogeneousLocalization, HomogeneousLocalization.map_map, map_map
-/
theorem Away.map_map (f : 𝒜 ->+*ᵍ ℬ) (g : ℬ ->+*ᵍ 𝒞) (s : A) (x : Away 𝒜 s) :
    Away.map g (f s) (Away.map f s x) = Away.map (g.comp f) s x :=
  HomogeneousLocalization.map_map ..

section AtPrime

variable (f : 𝒜 ->+*ᵍ ℬ) (I : Ideal A) [I.IsPrime] (J : Ideal B) [J.IsPrime] (hIJ : I = J.comap f)

-- NB: this is to be consistent with `Localization.localRingHom`. We might change both to
-- `AtPrime.map` one day.
/--
Definition of `localRingHom` / `localRingHom` 的定义

English:
definition localRingHom
  signature: : AtPrime 𝒜 I ->+* AtPrime ℬ J
  body: map f Localization.le_comap_primeCompl_iff.mpr hIJ ▸ le_rfl

中文:
定义 localRingHom
  签名: : AtPrime 𝒜 I ->+* AtPrime ℬ J
  定义体: map f Localization.le_comap_primeCompl_iff.mpr hIJ ▸ le_rfl

Depends on / 依赖: Localization, Localization.le_comap_primeCompl_iff.mpr, le_comap_primeCompl_iff, le_rfl
-/
noncomputable def localRingHom : AtPrime 𝒜 I ->+* AtPrime ℬ J :=
map f Localization.le_comap_primeCompl_iff.mpr hIJ ▸ le_rfl

variable {f I J hIJ}

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `val_localRingHom` / 引理 `val_localRingHom`

English:
lemma val_localRingHom
  given: (x : AtPrime 𝒜 I)
  proof: by
  obtain ⟨⟨i, x, s, hs⟩, rfl⟩ := x.mk_surjective
  simp [localRingHom, map_mk]

中文:
引理 val_localRingHom
  条件: (x : AtPrime 𝒜 I)
  证明: by
  obtain ⟨⟨i, x, s, hs⟩, rfl⟩ := x.mk_surjective
  simp [localRingHom, map_mk]
-/
@[simp] lemma val_localRingHom (x : AtPrime 𝒜 I) :
    (localRingHom f I J hIJ x).val = Localization.localRingHom _ _ f hIJ x.val := by
  obtain ⟨⟨i, x, s, hs⟩, rfl⟩ := x.mk_surjective
  simp [localRingHom, map_mk]

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsLocalHom (localRingHom f I J hIJ)
  body: by
    rw [← isUnit_iff_isUnit_val] at hx ⊢
    rw [val_localRingHom] at hx
    exact IsLocalHom.map_nonunit _ hx

中文:
实例 :
  签名: IsLocalHom (localRingHom f I J hIJ)
  定义体: by
    rw [← isUnit_iff_isUnit_val] at hx ⊢
    rw [val_localRingHom] at hx
    exact IsLocalHom.map_nonunit _ hx

Depends on / 依赖: IsLocalHom, IsLocalHom.map_nonunit, isUnit_iff_isUnit_val, map_nonunit, val_localRingHom
-/
instance : IsLocalHom (localRingHom f I J hIJ) where
  map_nonunit x hx := by
    rw [← isUnit_iff_isUnit_val] at hx ⊢
    rw [val_localRingHom] at hx
    exact IsLocalHom.map_nonunit _ hx

end AtPrime

end

section mapAway

variable [AddSubgroupClass σ A] [AddCommMonoid ι] [DecidableEq ι]
variable (𝒜 : ι -> σ) [GradedRing 𝒜]
variable {e : ι} {f : A} {g : A} (hg : g in 𝒜 e) {x : A} (hx : x = f * g)

set_option backward.privateInPublic true in
/--
Definition of `awayMapAux` / `awayMapAux` 的定义

English:
definition awayMapAux
  signature: (hx : f ∣ x)
  body: (Localization.awayLift (algebraMap A _) _
    (isUnit_of_dvd_unit (map_dvd _ hx) (IsLocalization.Away.algebraMap_isUnit x))).comp
      (algebraMap (Away 𝒜 f) (Localization.Away f))

中文:
定义 awayMapAux
  签名: (hx : f ∣ x)
  定义体: (Localization.awayLift (algebraMap A _) _
    (isUnit_of_dvd_unit (map_dvd _ hx) (IsLocalization.Away.algebraMap_isUnit x))).comp
      (algebraMap (Away 𝒜 f) (Localization.Away f))
-/
private def awayMapAux (hx : f ∣ x) : Away 𝒜 f ->+* Localization.Away x :=
  (Localization.awayLift (algebraMap A _) _
    (isUnit_of_dvd_unit (map_dvd _ hx) (IsLocalization.Away.algebraMap_isUnit x))).comp
      (algebraMap (Away 𝒜 f) (Localization.Away f))

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
lemma `awayMapAux_mk` / 引理 `awayMapAux_mk`

English:
lemma awayMapAux_mk
  given: (n a i hi)
  proof: by
  have : algebraMap A (Localization.Away x) f *
    (Localization.mk g ⟨f * g, (Submonoid.mem_powers_iff _ _).mpr ⟨1, by simp [hx]⟩⟩) = 1 := by
    rw [← Algebra.smul_def]; rw [Localization.smul_mk]
    exact Localization.mk_self ⟨f*g, _⟩
  simp only [awayMapAux, RingHom.coe_comp, Function.comp_a

中文:
引理 awayMapAux_mk
  条件: (n a i hi)
  证明: by
  have : algebraMap A (Localization.Away x) f *
    (Localization.mk g ⟨f * g, (Submonoid.mem_powers_iff _ _).mpr ⟨1, by simp [hx]⟩⟩) = 1 := by
    rw [← Algebra.smul_def]; rw [Localization.smul_mk]
    exact Localization.mk_self ⟨f*g, _⟩
  simp only [awayMapAux, RingHom.coe_comp, Function.comp_a

Depends on / 依赖: Algebra, Algebra.smul_def, Function, Function.comp_apply, Localization, Localization.Away, Localization.awayLift_mk, Localization.mk, Localization.mk_pow, Localization.mk_self, Localization.smul_mk, RingHom, RingHom.coe_comp, Submonoid, Submonoid.mem_powers_iff, algebraMap, algebraMap_apply, awayLift_mk, awayMapAux, coe_comp
-/
lemma awayMapAux_mk (n a i hi) :
    awayMapAux 𝒜 ⟨_, hx⟩ (mk ⟨n, a, ⟨f ^ i, hi⟩, ⟨i, rfl⟩⟩) =
      Localization.mk (a * g ^ i) ⟨x ^ i, (Submonoid.mem_powers_iff _ _).mpr ⟨i, rfl⟩⟩ := by
  have : algebraMap A (Localization.Away x) f *
    (Localization.mk g ⟨f * g, (Submonoid.mem_powers_iff _ _).mpr ⟨1, by simp [hx]⟩⟩) = 1 := by
    rw [← Algebra.smul_def]; rw [Localization.smul_mk]
    exact Localization.mk_self ⟨f*g, _⟩
  simp only [awayMapAux, RingHom.coe_comp, Function.comp_apply, algebraMap_apply, val_mk]
  rw [Localization.awayLift_mk (hv := this)]; rw [← Algebra.smul_def]; rw [Localization.mk_pow]; rw [Localization.smul_mk]
  subst hx
  rfl

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
include hg in
/--
lemma `range_awayMapAux_subset` / 引理 `range_awayMapAux_subset`

English:
lemma range_awayMapAux_subset
  proof: by
  rintro _ ⟨z, rfl⟩
  obtain ⟨⟨n, ⟨a, ha⟩, ⟨b, hb'⟩, j, rfl : _ = b⟩, rfl⟩ := mk_surjective z
  use mk ⟨n+j•e,⟨a*g^j, ?_⟩, ⟨x^j, ?_⟩, j, rfl⟩
  · simp [awayMapAux_mk 𝒜 (hx := hx)]
  · apply SetLike.mul_mem_graded ha
    exact SetLike.pow_mem_graded _ hg
  · rw [hx, mul_pow]
    apply SetLike.mul_

中文:
引理 range_awayMapAux_subset
  证明: by
  rintro _ ⟨z, rfl⟩
  obtain ⟨⟨n, ⟨a, ha⟩, ⟨b, hb'⟩, j, rfl : _ = b⟩, rfl⟩ := mk_surjective z
  use mk ⟨n+j•e,⟨a*g^j, ?_⟩, ⟨x^j, ?_⟩, j, rfl⟩
  · simp [awayMapAux_mk 𝒜 (hx := hx)]
  · apply SetLike.mul_mem_graded ha
    exact SetLike.pow_mem_graded _ hg
  · rw [hx, mul_pow]
    apply SetLike.mul_

Depends on / 依赖: Set.range, SetLike, SetLike.mul_mem_graded, SetLike.pow_mem_graded, awayMapAux_mk, mk_surjective, mul_mem_graded, mul_pow, pow_mem_graded, subseteq
-/
lemma range_awayMapAux_subset :
    Set.range (awayMapAux 𝒜 (f := f) ⟨_, hx⟩) subseteq Set.range (val (𝒜 := 𝒜)) := by
  rintro _ ⟨z, rfl⟩
  obtain ⟨⟨n, ⟨a, ha⟩, ⟨b, hb'⟩, j, rfl : _ = b⟩, rfl⟩ := mk_surjective z
  use mk ⟨n+j•e,⟨a*g^j, ?_⟩, ⟨x^j, ?_⟩, j, rfl⟩
  · simp [awayMapAux_mk 𝒜 (hx := hx)]
  · apply SetLike.mul_mem_graded ha
    exact SetLike.pow_mem_graded _ hg
  · rw [hx, mul_pow]
    apply SetLike.mul_mem_graded hb'
    exact SetLike.pow_mem_graded _ hg

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `awayMap` / `awayMap` 的定义

English:
definition awayMap
  signature: : Away 𝒜 f ->+* Away 𝒜 x
  body: by
  let e := RingEquiv.ofLeftInverse (f := algebraMap (Away 𝒜 x) (Localization.Away x))
    (h := (val_injective _).hasLeftInverse.choose_spec)
  refine RingHom.comp (e.symm.toRingHom.comp (Subring.inclusion ?_))
    (awayMapAux 𝒜 (f := f) ⟨_, hx⟩).rangeRestrict
  exact range_awayMapAux_subset 𝒜 hg

中文:
定义 awayMap
  签名: : Away 𝒜 f ->+* Away 𝒜 x
  定义体: by
  let e := RingEquiv.ofLeftInverse (f := algebraMap (Away 𝒜 x) (Localization.Away x))
    (h := (val_injective _).hasLeftInverse.choose_spec)
  refine RingHom.comp (e.symm.toRingHom.comp (Subring.inclusion ?_))
    (awayMapAux 𝒜 (f := f) ⟨_, hx⟩).rangeRestrict
  exact range_awayMapAux_subset 𝒜 hg

Depends on / 依赖: Localization, Localization.Away, RingEquiv, RingEquiv.ofLeftInverse, RingHom, RingHom.comp, Subring, Subring.inclusion, algebraMap, awayMapAux, choose_spec, e.symm.toRingHom.comp, hasLeftInverse, hasLeftInverse.choose_spec, inclusion, ofLeftInverse, rangeRestrict, range_awayMapAux_subset, toRingHom, val_injective
-/
def awayMap : Away 𝒜 f ->+* Away 𝒜 x := by
  let e := RingEquiv.ofLeftInverse (f := algebraMap (Away 𝒜 x) (Localization.Away x))
    (h := (val_injective _).hasLeftInverse.choose_spec)
  refine RingHom.comp (e.symm.toRingHom.comp (Subring.inclusion ?_))
    (awayMapAux 𝒜 (f := f) ⟨_, hx⟩).rangeRestrict
  exact range_awayMapAux_subset 𝒜 hg hx

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
lemma `val_awayMap_eq_aux` / 引理 `val_awayMap_eq_aux`

English:
lemma val_awayMap_eq_aux
  given: (a)
  statement: (awayMap 𝒜 hg hx a).val = awayMapAux 𝒜 ⟨_, hx⟩ a
  proof: by
  let e := RingEquiv.ofLeftInverse (f := algebraMap (Away 𝒜 x) (Localization.Away x))
    (h := (val_injective _).hasLeftInverse.choose_spec)
  dsimp [awayMap]
  convert_to! (e (e.symm ⟨awayMapAux 𝒜 (f := f) ⟨_, hx⟩ a,
    range_awayMapAux_subset 𝒜 hg hx ⟨_, rfl⟩⟩)).1 = _
  rw [e.apply_symm_apply

中文:
引理 val_awayMap_eq_aux
  条件: (a)
  结论: (awayMap 𝒜 hg hx a).val = awayMapAux 𝒜 ⟨_, hx⟩ a
  证明: by
  let e := RingEquiv.ofLeftInverse (f := algebraMap (Away 𝒜 x) (Localization.Away x))
    (h := (val_injective _).hasLeftInverse.choose_spec)
  dsimp [awayMap]
  convert_to! (e (e.symm ⟨awayMapAux 𝒜 (f := f) ⟨_, hx⟩ a,
    range_awayMapAux_subset 𝒜 hg hx ⟨_, rfl⟩⟩)).1 = _
  rw [e.apply_symm_apply

Depends on / 依赖: Localization, Localization.Away, RingEquiv, RingEquiv.ofLeftInverse, algebraMap, apply_symm_apply, awayMap, awayMapAux, choose_spec, convert_to, e.apply_symm_apply, e.symm, hasLeftInverse, hasLeftInverse.choose_spec, ofLeftInverse, range_awayMapAux_subset, val_injective
-/
lemma val_awayMap_eq_aux (a) : (awayMap 𝒜 hg hx a).val = awayMapAux 𝒜 ⟨_, hx⟩ a := by
  let e := RingEquiv.ofLeftInverse (f := algebraMap (Away 𝒜 x) (Localization.Away x))
    (h := (val_injective _).hasLeftInverse.choose_spec)
  dsimp [awayMap]
  convert_to! (e (e.symm ⟨awayMapAux 𝒜 (f := f) ⟨_, hx⟩ a,
    range_awayMapAux_subset 𝒜 hg hx ⟨_, rfl⟩⟩)).1 = _
  rw [e.apply_symm_apply]

/--
lemma `val_awayMap` / 引理 `val_awayMap`

English:
lemma val_awayMap
  given: (a)
  statement: (awayMap 𝒜 hg hx a).val = Localization.awayLift (algebraMap A _) _
  proof: by
  rw [val_awayMap_eq_aux]
  rfl

中文:
引理 val_awayMap
  条件: (a)
  结论: (awayMap 𝒜 hg hx a).val = Localization.awayLift (algebraMap A _) _
  证明: by
  rw [val_awayMap_eq_aux]
  rfl

Depends on / 依赖: val_awayMap_eq_aux
-/
lemma val_awayMap (a) : (awayMap 𝒜 hg hx a).val = Localization.awayLift (algebraMap A _) _
    (isUnit_of_dvd_unit (map_dvd _ ⟨_, hx⟩) (IsLocalization.Away.algebraMap_isUnit x)) a.val := by
  rw [val_awayMap_eq_aux]
  rfl

/--
lemma `awayMap_fromZeroRingHom` / 引理 `awayMap_fromZeroRingHom`

English:
lemma awayMap_fromZeroRingHom
  given: (a)
  proof: by
  ext
  simp only [fromZeroRingHom, val_awayMap]
  convert! IsLocalization.lift_eq _ _

中文:
引理 awayMap_fromZeroRingHom
  条件: (a)
  证明: by
  ext
  simp only [fromZeroRingHom, val_awayMap]
  convert! IsLocalization.lift_eq _ _

Depends on / 依赖: IsLocalization, IsLocalization.lift_eq, convert, fromZeroRingHom, lift_eq, val_awayMap
-/
lemma awayMap_fromZeroRingHom (a) :
    awayMap 𝒜 hg hx (fromZeroRingHom 𝒜 _ a) = fromZeroRingHom 𝒜 _ a := by
  ext
  simp only [fromZeroRingHom, val_awayMap]
  convert! IsLocalization.lift_eq _ _

/--
lemma `val_awayMap_mk` / 引理 `val_awayMap_mk`

English:
lemma val_awayMap_mk
  given: (n a i hi)
  statement: (awayMap 𝒜 hg hx (mk ⟨n, a, ⟨f ^ i, hi⟩, ⟨i, rfl⟩⟩)).val =
  proof: by
  rw [val_awayMap_eq_aux]; rw [awayMapAux_mk 𝒜 (hx := hx)]

中文:
引理 val_awayMap_mk
  条件: (n a i hi)
  结论: (awayMap 𝒜 hg hx (mk ⟨n, a, ⟨f ^ i, hi⟩, ⟨i, rfl⟩⟩)).val =
  证明: by
  rw [val_awayMap_eq_aux]; rw [awayMapAux_mk 𝒜 (hx := hx)]

Depends on / 依赖: awayMapAux_mk, val_awayMap_eq_aux
-/
lemma val_awayMap_mk (n a i hi) : (awayMap 𝒜 hg hx (mk ⟨n, a, ⟨f ^ i, hi⟩, ⟨i, rfl⟩⟩)).val =
    Localization.mk (a * g ^ i) ⟨x ^ i, (Submonoid.mem_powers_iff _ _).mpr ⟨i, rfl⟩⟩ := by
  rw [val_awayMap_eq_aux]; rw [awayMapAux_mk 𝒜 (hx := hx)]

/--
Definition of `awayMapₐ` / `awayMapₐ` 的定义

English:
definition awayMapₐ
  signature: : Away 𝒜 f ->ₐ[𝒜 0] Away 𝒜 x where
  body: awayMap 𝒜 hg hx
  commutes' _ := awayMap_fromZeroRingHom ..

中文:
定义 awayMapₐ
  签名: : Away 𝒜 f ->ₐ[𝒜 0] Away 𝒜 x where
  定义体: awayMap 𝒜 hg hx
  commutes' _ := awayMap_fromZeroRingHom ..

Depends on / 依赖: awayMap
-/
def awayMapₐ : Away 𝒜 f ->ₐ[𝒜 0] Away 𝒜 x where
  __ := awayMap 𝒜 hg hx
  commutes' _ := awayMap_fromZeroRingHom ..

/--
lemma `awayMapₐ_apply` / 引理 `awayMapₐ_apply`

English:
lemma awayMapₐ_apply
  given: (a)
  statement: awayMapₐ 𝒜 hg hx a = awayMap 𝒜 hg hx a
  proof: rfl

中文:
引理 awayMapₐ_apply
  条件: (a)
  结论: awayMapₐ 𝒜 hg hx a = awayMap 𝒜 hg hx a
  证明: rfl
-/
@[simp] lemma awayMapₐ_apply (a) : awayMapₐ 𝒜 hg hx a = awayMap 𝒜 hg hx a := rfl

open SetLike in
@[simp]
/--
lemma `awayMap_mk` / 引理 `awayMap_mk`

English:
lemma awayMap_mk
  given: {d : ι} (n : Nat) (hf : f in 𝒜 d) (a : A) (ha : a in 𝒜 (n • d))
  proof: by
  ext
  exact val_awayMap_mk ..

中文:
引理 awayMap_mk
  条件: {d : ι} (n : 自然数) (hf : f in 𝒜 d) (a : A) (ha : a in 𝒜 (n • d))
  证明: by
  ext
  exact val_awayMap_mk ..

Depends on / 依赖: val_awayMap_mk
-/
lemma awayMap_mk {d : ι} (n : Nat) (hf : f in 𝒜 d) (a : A) (ha : a in 𝒜 (n • d)) :
    awayMap 𝒜 hg hx (Away.mk 𝒜 hf n a ha) = Away.mk 𝒜 (hx ▸ mul_mem_graded hf hg) n
      (a * g ^ n) (by rw [smul_add]; exact mul_mem_graded ha (pow_mem_graded n hg)) := by
  ext
  exact val_awayMap_mk ..

end mapAway

section isLocalization

variable [AddSubgroupClass σ A] {𝒜 : Nat -> σ} [GradedRing 𝒜]
variable {e d : Nat} {f : A} (hf : f in 𝒜 d) {g : A} (hg : g in 𝒜 e)

/--
Definition of `Away.isLocalizationElem` / `Away.isLocalizationElem` 的定义

English:
abbreviation Away.isLocalizationElem
  signature: : Away 𝒜 f
  body: Away.mk 𝒜 hf e (g ^ d) (by convert! SetLike.pow_mem_graded d hg using 2; exact mul_comm _ _)

中文:
缩写 Away.isLocalizationElem
  签名: : Away 𝒜 f
  定义体: Away.mk 𝒜 hf e (g ^ d) (by convert! SetLike.pow_mem_graded d hg using 2; exact mul_comm _ _)

Depends on / 依赖: Away.mk, SetLike, SetLike.pow_mem_graded, convert, mul_comm, pow_mem_graded
-/
abbrev Away.isLocalizationElem : Away 𝒜 f :=
  Away.mk 𝒜 hf e (g ^ d) (by convert! SetLike.pow_mem_graded d hg using 2; exact mul_comm _ _)

variable {x : A} (hx : x = f * g)

/--
theorem `Away.isLocalization_mul` / 定理 `Away.isLocalization_mul`

English:
theorem Away.isLocalization_mul
  given: (hd : d != 0)
  proof: (awayMap 𝒜 hg hx).toAlgebra
    IsLocalization.Away (isLocalizationElem hf hg) (Away 𝒜 x) := by
  let := (awayMap 𝒜 hg hx).toAlgebra
  constructor; constructor
  · rintro ⟨r, n, rfl⟩
    rw [map_pow]; rw [RingHom.algebraMap_toAlgebra]
    let z : Away 𝒜 x := Away.mk 𝒜 (hx ▸ SetLike.mul_mem_graded hf

中文:
定理 Away.isLocalization_mul
  条件: (hd : d != 0)
  证明: (awayMap 𝒜 hg hx).toAlgebra
    IsLocalization.Away (isLocalizationElem hf hg) (Away 𝒜 x) := by
  let := (awayMap 𝒜 hg hx).toAlgebra
  constructor; constructor
  · rintro ⟨r, n, rfl⟩
    rw [map_pow]; rw [RingHom.algebraMap_toAlgebra]
    let z : Away 𝒜 x := Away.mk 𝒜 (hx ▸ SetLike.mul_mem_graded hf

Depends on / 依赖: awayMap, toAlgebra
-/
theorem Away.isLocalization_mul (hd : d != 0) :
    letI := (awayMap 𝒜 hg hx).toAlgebra
    IsLocalization.Away (isLocalizationElem hf hg) (Away 𝒜 x) := by
  let := (awayMap 𝒜 hg hx).toAlgebra
  constructor; constructor
  · rintro ⟨r, n, rfl⟩
    rw [map_pow]; rw [RingHom.algebraMap_toAlgebra]
    let z : Away 𝒜 x := Away.mk 𝒜 (hx ▸ SetLike.mul_mem_graded hf hg) (d + e)
(g ^ e * f ^ (2 * e + d)) by
      convert!
        SetLike.mul_mem_graded (SetLike.pow_mem_graded e hg)
          (SetLike.pow_mem_graded (2 * e + d) hf) using 2
      ring
    refine (isUnit_iff_exists_inv.mpr ⟨z, ?_⟩).pow _
    ext
    simp only [val_mul, val_one, awayMap_mk, Away.val_mk, z, Localization.mk_mul]
    rw [← Localization.mk_one]; rw [Localization.mk_eq_mk_iff]; rw [Localization.r_iff_exists]
    use 1
    simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul, mul_one, hx]
    ring
  · intro z
    obtain ⟨n, s, hs, rfl⟩ := Away.mk_surjective 𝒜 (hx ▸ SetLike.mul_mem_graded hf hg) z
    rcases d with - | d
    · contradiction
let t : Away 𝒜 f := Away.mk 𝒜 hf (n * (e + 1)) (s * g ^ (n * d)) by
      convert! SetLike.mul_mem_graded hs (SetLike.pow_mem_graded _ hg) using 2; simp; ring
    refine ⟨⟨t, ⟨_, ⟨n, rfl⟩⟩⟩, ?_⟩
    ext
    simp only [RingHom.algebraMap_toAlgebra, map_pow, awayMap_mk, val_mul, val_mk, val_pow,
      Localization.mk_pow, Localization.mk_mul, t]
    rw [Localization.mk_eq_mk_iff]; rw [Localization.r_iff_exists]
    exact ⟨1, by simp; ring⟩
  · intro a b e
    obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hf a
    obtain ⟨m, b, hb, rfl⟩ := Away.mk_surjective 𝒜 hf b
    replace e := congr_arg val e
    simp only [RingHom.algebraMap_toAlgebra, awayMap_mk, val_mk,
      Localization.mk_eq_mk_iff, Localization.r_iff_exists] at e
    obtain ⟨⟨_, k, rfl⟩, hc⟩ := e
    refine ⟨⟨_, k + m + n, rfl⟩, ?_⟩
    ext
    simp only [val_mul, val_pow, val_mk, Localization.mk_pow,
      Localization.mk_eq_mk_iff, Localization.r_iff_exists, Submonoid.coe_mul, Localization.mk_mul,
      SubmonoidClass.coe_pow, Subtype.exists, exists_prop]
    refine ⟨_, ⟨k, rfl⟩, ?_⟩
    rcases d with - | d
    · contradiction
    subst hx
    convert! congr(f ^ (e * (k + m + n)) * g ^ (d * (k + m + n)) * $hc) using 1 <;> ring

end isLocalization

section span

set_option backward.isDefEq.respectTransparency.types false in
variable [AddSubgroupClass σ A] [AddCommMonoid ι] [DecidableEq ι] {𝒜 : ι -> σ} [GradedRing 𝒜] in
/--
theorem `Away.span_mk_prod_pow_eq_top` / 定理 `Away.span_mk_prod_pow_eq_top`

English:
theorem Away.span_mk_prod_pow_eq_top
  statement: {f : A} {d : ι} (hf : f in 𝒜 d)
  proof: by
  by_cases HH : Subsingleton (HomogeneousLocalization.Away 𝒜 f)
  · exact Subsingleton.elim _ _
  rw [← top_le_iff]
  rintro x -
  obtain ⟨⟨n, ⟨a, ha⟩, ⟨b, hb'⟩, ⟨j, (rfl : _ = b)⟩⟩, rfl⟩ := mk_surjective x
  by_cases hfj : f ^ j = 0
  · exact (HH (HomogeneousLocalization.subsingleton _ ⟨_, hfj⟩)

中文:
定理 Away.span_mk_prod_pow_eq_top
  结论: {f : A} {d : ι} (hf : f in 𝒜 d)
  证明: by
  by_cases HH : Subsingleton (HomogeneousLocalization.Away 𝒜 f)
  · exact Subsingleton.elim _ _
  rw [← top_le_iff]
  rintro x -
  obtain ⟨⟨n, ⟨a, ha⟩, ⟨b, hb'⟩, ⟨j, (rfl : _ = b)⟩⟩, rfl⟩ := mk_surjective x
  by_cases hfj : f ^ j = 0
  · exact (HH (HomogeneousLocalization.subsingleton _ ⟨_, hfj⟩)

Depends on / 依赖: DirectSum, DirectSum.decompose, DirectSum.decompose_of_mem_same, HomogeneousLocalization, HomogeneousLocalization.Away, HomogeneousLocalization.subsingleton, Set.range, Submodule, Submodule.span, Submonoid, Submonoid.closure, Subsingleton, Subsingleton.elim, Subtype, Subtype.ext, closure, decompose, decompose_of_mem_same, mk_surjective, simp_rw
-/
theorem Away.span_mk_prod_pow_eq_top {f : A} {d : ι} (hf : f in 𝒜 d)
    {ι' : Type*} [Fintype ι'] (v : ι' -> A)
    (hx : Algebra.adjoin (𝒜 0) (Set.range v) = ⊤) (dv : ι' -> ι) (hxd : forall i, v i in 𝒜 (dv i)) :
    Submodule.span (𝒜 0) { (Away.mk 𝒜 hf a (∏ i, v i ^ ai i)
      (hai ▸ SetLike.prod_pow_mem_graded _ _ _ _ fun i _ => hxd i) : Away 𝒜 f) |
        (a : Nat) (ai : ι' -> Nat) (hai : ∑ i, ai i • dv i = a • d) } = ⊤ := by
  by_cases HH : Subsingleton (HomogeneousLocalization.Away 𝒜 f)
  · exact Subsingleton.elim _ _
  rw [← top_le_iff]
  rintro x -
  obtain ⟨⟨n, ⟨a, ha⟩, ⟨b, hb'⟩, ⟨j, (rfl : _ = b)⟩⟩, rfl⟩ := mk_surjective x
  by_cases hfj : f ^ j = 0
  · exact (HH (HomogeneousLocalization.subsingleton _ ⟨_, hfj⟩)).elim
  have : DirectSum.decompose 𝒜 a n = ⟨a, ha⟩ := Subtype.ext (DirectSum.decompose_of_mem_same 𝒜 ha)
  simp_rw [← this]
  clear this ha
  have : a in Submodule.span (𝒜 0) (Submonoid.closure (Set.range v)) := by
    rw [← Algebra.adjoin_eq_span]; rw [hx]
    trivial
  induction this using Submodule.span_induction with
  | mem a ha' =>
    obtain ⟨ai, rfl⟩ := Submonoid.exists_of_mem_closure_range _ _ ha'
    clear ha'
    by_cases H : ∑ i, ai i • dv i = n
    · apply Submodule.subset_span
      refine ⟨j, ai, H.trans ?_, ?_⟩
      · exact DirectSum.degree_eq_of_mem_mem 𝒜 hb'
          (SetLike.pow_mem_graded j hf) hfj
      · ext
        simp only [val_mk, Away.val_mk]
        congr
        refine (DirectSum.decompose_of_mem_same _ ?_).symm
        exact H ▸ SetLike.prod_pow_mem_graded _ _ _ _ fun i _ => hxd i
    · convert! zero_mem (Submodule.span (𝒜 0) _)
      ext
      have : (DirectSum.decompose 𝒜 (∏ i : ι', v i ^ ai i) n).1 = 0 := by
        refine DirectSum.decompose_of_mem_ne _ ?_ H
        exact SetLike.prod_pow_mem_graded _ _ _ _ fun i _ => hxd i
      simp [this, Localization.mk_zero]
  | zero =>
    convert! zero_mem (Submodule.span (𝒜 0) _)
    ext; simp [Localization.mk_zero]
  | add s t hs ht hs' ht' =>
    convert! add_mem hs' ht'
    ext; simp [← Localization.add_mk_self]
  | smul r x hx hx' =>
    convert! Submodule.smul_mem _ r hx'
    ext
    simp [Algebra.smul_def, algebraMap_eq, fromZeroRingHom, Localization.mk_mul,
      -decompose_mul, coe_decompose_mul_of_left_mem_zero 𝒜 r.2]

variable [AddSubgroupClass σ A] {𝒜 : Nat -> σ} [GradedRing 𝒜] in
/-- This is strictly weaker than `Away.adjoin_mk_prod_pow_eq_top`. -/
private
/--
theorem `Away.adjoin_mk_prod_pow_eq_top_of_pos` / 定理 `Away.adjoin_mk_prod_pow_eq_top_of_pos`

English:
theorem Away.adjoin_mk_prod_pow_eq_top_of_pos
  statement: {f : A} {d : Nat} (hf : f in 𝒜 d)
  proof: by
  rw [← top_le_iff]
  change ⊤ <= (Algebra.adjoin (𝒜 0) _).toSubmodule
  rw [← HomogeneousLocalization.Away.span_mk_prod_pow_eq_top hf v hx dv hxd]; rw [Submodule.span_le]
  rintro _ ⟨a, ai, hai, rfl⟩
  have H₀ : (a - ∑ i : ι', dv i * (ai i / d)) • d = ∑ k : ι', (ai k % d) • dv k := by
    rw [sm

中文:
定理 Away.adjoin_mk_prod_pow_eq_top_of_pos
  结论: {f : A} {d : 自然数} (hf : f in 𝒜 d)
  证明: by
  rw [← top_le_iff]
  change ⊤ <= (Algebra.adjoin (𝒜 0) _).toSubmodule
  rw [← HomogeneousLocalization.Away.span_mk_prod_pow_eq_top hf v hx dv hxd]; rw [Submodule.span_le]
  rintro _ ⟨a, ai, hai, rfl⟩
  have H₀ : (a - ∑ i : ι', dv i * (ai i / d)) • d = ∑ k : ι', (ai k % d) • dv k := by
    rw [sm

Depends on / 依赖: Algebra, Algebra.adjoin, Finset, Finset.mul_sum, Finset.sum_add_distrib, HomogeneousLocalization, HomogeneousLocalization.Away.span_mk_prod_pow_eq_top, Nat.mod_add_div, Submodule, Submodule.span_le, add_mul, adjoin, mod_add_div, mul_assoc, mul_comm, mul_sum, simp_rw, smul_eq_mul, span_le, span_mk_prod_pow_eq_top
-/
theorem Away.adjoin_mk_prod_pow_eq_top_of_pos {f : A} {d : Nat} (hf : f in 𝒜 d)
    {ι' : Type*} [Fintype ι'] (v : ι' -> A)
    (hx : Algebra.adjoin (𝒜 0) (Set.range v) = ⊤) (dv : ι' -> Nat)
    (hxd : forall i, v i in 𝒜 (dv i)) (hxd' : forall i, 0 < dv i) :
    Algebra.adjoin (𝒜 0) { Away.mk 𝒜 hf a (∏ i, v i ^ ai i)
      (hai ▸ SetLike.prod_pow_mem_graded _ _ _ _ fun i _ => hxd i) |
        (a : Nat) (ai : ι' -> Nat) (hai : ∑ i, ai i • dv i = a • d) (_ : forall i, ai i <= d) } = ⊤ := by
  rw [← top_le_iff]
  change ⊤ <= (Algebra.adjoin (𝒜 0) _).toSubmodule
  rw [← HomogeneousLocalization.Away.span_mk_prod_pow_eq_top hf v hx dv hxd]; rw [Submodule.span_le]
  rintro _ ⟨a, ai, hai, rfl⟩
  have H₀ : (a - ∑ i : ι', dv i * (ai i / d)) • d = ∑ k : ι', (ai k % d) • dv k := by
    rw [smul_eq_mul]; rw [tsub_mul]; rw [← smul_eq_mul]; rw [← hai]
    conv => enter [1, 1, 2, i]; rw [← Nat.mod_add_div (ai i) d]
    simp_rw [smul_eq_mul, add_mul, Finset.sum_add_distrib,
      mul_assoc, ← Finset.mul_sum, mul_comm d, mul_comm (_ / _)]
    simp only [add_tsub_cancel_right]
  have H : Away.mk 𝒜 hf a (∏ i, v i ^ ai i)
      (hai ▸ SetLike.prod_pow_mem_graded _ _ _ _ fun i _ => hxd i) =
      Away.mk 𝒜 hf (a - ∑ i : ι', dv i * (ai i / d)) (∏ i, v i ^ (ai i % d))
      (H₀ ▸ SetLike.prod_pow_mem_graded _ _ _ _ fun i _ => hxd i) *
      ∏ i, Away.isLocalizationElem hf (hxd i) ^ (ai i / d) := by
    apply (show Function.Injective (algebraMap (Away 𝒜 f) (Localization.Away f))
      from val_injective _)
    simp only [map_pow, map_prod, map_mul]
    simp only [HomogeneousLocalization.algebraMap_apply, val_mk,
      Localization.mk_pow, Localization.mk_prod, Localization.mk_mul,
      ← Finset.prod_mul_distrib, ← pow_add, ← pow_mul]
    congr
    · ext i
      congr
      exact Eq.symm (Nat.mod_add_div (ai i) d)
    · simp only [SubmonoidClass.coe_finsetProd, ← pow_add, ← pow_mul,
        Finset.prod_pow_eq_pow_sum, SubmonoidClass.coe_pow]
      rw [tsub_add_cancel_of_le]
      rcases d.eq_zero_or_pos with hd | hd
      · simp [hd]
      rw [← mul_le_mul_iff_of_pos_right hd]; rw [← smul_eq_mul (a := a)]; rw [← hai]; rw [Finset.sum_mul]
      simp_rw [smul_eq_mul, mul_comm (ai _), mul_assoc]
      gcongr
      exact Nat.div_mul_le_self (ai _) d
  rw [H]; rw [SetLike.mem_coe]
  apply (Algebra.adjoin (𝒜 0) _).mul_mem
  · apply Algebra.subset_adjoin
    refine ⟨a - ∑ i : ι', dv i * (ai i / d), (ai · % d), H₀.symm, ?_, rfl⟩
    rcases d.eq_zero_or_pos with hd | hd
    · have : forall (x : ι'), ai x = 0 := by simpa [hd, fun i => (hxd' i).ne'] using hai
      simp [this]
    exact fun i => (Nat.mod_lt _ hd).le
  apply prod_mem
  · classical
    rintro j -
    apply pow_mem
    apply Algebra.subset_adjoin
    refine ⟨dv j, Pi.single j d, ?_, ?_, ?_⟩
    · simp [Pi.single_apply, mul_comm]
    · aesop (add simp Pi.single_apply)
    ext
    simp [Pi.single_apply]

variable [AddSubgroupClass σ A] {𝒜 : Nat -> σ} [GradedRing 𝒜] in
/--
theorem `Away.adjoin_mk_prod_pow_eq_top` / 定理 `Away.adjoin_mk_prod_pow_eq_top`

English:
theorem Away.adjoin_mk_prod_pow_eq_top
  statement: {f : A} {d : Nat} (hf : f in 𝒜 d)
  proof: by
  classical
  let s := Finset.univ.filter (0 < dv ·)
  have := Away.adjoin_mk_prod_pow_eq_top_of_pos hf (ι' := s) (v ∘ Subtype.val) ?_
    (dv ∘ Subtype.val) (fun _ => hxd _) (by simp [s])
  swap
  · rw [← top_le_iff, ← hx, Algebra.adjoin_le_iff, Set.range_subset_iff]
    intro i
    rcases (dv i

中文:
定理 Away.adjoin_mk_prod_pow_eq_top
  结论: {f : A} {d : 自然数} (hf : f in 𝒜 d)
  证明: by
  classical
  let s := Finset.univ.filter (0 < dv ·)
  have := Away.adjoin_mk_prod_pow_eq_top_of_pos hf (ι' := s) (v ∘ Subtype.val) ?_
    (dv ∘ Subtype.val) (fun _ => hxd _) (by simp [s])
  swap
  · rw [← top_le_iff, ← hx, Algebra.adjoin_le_iff, Set.range_subset_iff]
    intro i
    rcases (dv i

Depends on / 依赖: Algebra, Algebra.adjoin_le_iff, Algebra.adjoin_mono, Algebra.subset_adjoin, Away.adjoin_mk_prod_pow_eq_top_of_pos, Finset, Finset.univ.filter, Set.range_subset_iff, Subtype, Subtype.val, adjoin_le_iff, adjoin_mk_prod_pow_eq_top_of_pos, adjoin_mono, algebraMap_mem, classical, eq_zero_or_pos, filter, range_subset_iff, subset_adjoin, top_le_iff
-/
theorem Away.adjoin_mk_prod_pow_eq_top {f : A} {d : Nat} (hf : f in 𝒜 d)
    (ι' : Type*) [Fintype ι'] (v : ι' -> A)
    (hx : Algebra.adjoin (𝒜 0) (Set.range v) = ⊤) (dv : ι' -> Nat) (hxd : forall i, v i in 𝒜 (dv i)) :
    Algebra.adjoin (𝒜 0) { Away.mk 𝒜 hf a (∏ i, v i ^ ai i)
      (hai ▸ SetLike.prod_pow_mem_graded _ _ _ _ fun i _ => hxd i) |
        (a : Nat) (ai : ι' -> Nat) (hai : ∑ i, ai i • dv i = a • d) (_ : forall i, ai i <= d) } = ⊤ := by
  classical
  let s := Finset.univ.filter (0 < dv ·)
  have := Away.adjoin_mk_prod_pow_eq_top_of_pos hf (ι' := s) (v ∘ Subtype.val) ?_
    (dv ∘ Subtype.val) (fun _ => hxd _) (by simp [s])
  swap
  · rw [← top_le_iff, ← hx, Algebra.adjoin_le_iff, Set.range_subset_iff]
    intro i
    rcases (dv i).eq_zero_or_pos with hi | hi
    · exact algebraMap_mem (R := 𝒜 0) _ ⟨v i, hi ▸ hxd i⟩
    exact Algebra.subset_adjoin ⟨⟨i, by simpa [s] using hi⟩, rfl⟩
  rw [← top_le_iff]; rw [← this]
  apply Algebra.adjoin_mono
  rintro _ ⟨a, ai, hai : ∑ x in s.attach, _ = _, h, rfl⟩
  refine ⟨a, fun i => if hi : i in s then ai ⟨i, hi⟩ else 0, ?_, ?_, ?_⟩
  · simpa [Finset.sum_attach_eq_sum_dite] using hai
  · simp [apply_dite, dite_apply, h]
  · congr 1
    change _ = ∏ x in s.attach, _
    simp [Finset.prod_attach_eq_prod_dite]

variable [AddSubgroupClass σ A] {𝒜 : Nat -> σ} [GradedRing 𝒜] [Algebra.FiniteType (𝒜 0) A] in
/--
lemma `Away.finiteType` / 引理 `Away.finiteType`

English:
lemma Away.finiteType
  given: (f : A) (d : Nat) (hf : f in 𝒜 d)
  proof: by
  constructor
  obtain ⟨s, hs, hs'⟩ := GradedAlgebra.exists_finset_adjoin_eq_top_and_homogeneous_ne_zero 𝒜
  choose dx hdx hxd using Subtype.forall'.mp hs'
  simp_rw [Subalgebra.fg_def, ← top_le_iff,
    ← Away.adjoin_mk_prod_pow_eq_top hf (ι' := s) Subtype.val (by simpa) dx hxd]
  rcases d.eq_ze

中文:
引理 Away.finiteType
  条件: (f : A) (d : 自然数) (hf : f in 𝒜 d)
  证明: by
  constructor
  obtain ⟨s, hs, hs'⟩ := GradedAlgebra.exists_finset_adjoin_eq_top_and_homogeneous_ne_zero 𝒜
  choose dx hdx hxd using Subtype.forall'.mp hs'
  simp_rw [Subalgebra.fg_def, ← top_le_iff,
    ← Away.adjoin_mk_prod_pow_eq_top hf (ι' := s) Subtype.val (by simpa) dx hxd]
  rcases d.eq_ze

Depends on / 依赖: Algebra, Algebra.adjoin_le_iff, Away.adjoin_mk_prod_pow_eq_top, Away.mk, GradedAlgebra, GradedAlgebra.exists_finset_adjoin_eq_top_and_homogeneous_ne_zero, GradedOne, GradedOne.one_mem, Set.finite_singleton, Subalgebra, Subalgebra.fg_def, Subtype, Subtype.forall, Subtype.val, adjoin_le_iff, adjoin_mk_prod_pow_eq_top, d.eq_zero_or_pos, eq_zero_or_pos, exists_finset_adjoin_eq_top_and_homogeneous_ne_zero, fg_def
-/
lemma Away.finiteType (f : A) (d : Nat) (hf : f in 𝒜 d) :
    Algebra.FiniteType (𝒜 0) (Away 𝒜 f) := by
  constructor
  obtain ⟨s, hs, hs'⟩ := GradedAlgebra.exists_finset_adjoin_eq_top_and_homogeneous_ne_zero 𝒜
  choose dx hdx hxd using Subtype.forall'.mp hs'
  simp_rw [Subalgebra.fg_def, ← top_le_iff,
    ← Away.adjoin_mk_prod_pow_eq_top hf (ι' := s) Subtype.val (by simpa) dx hxd]
  rcases d.eq_zero_or_pos with hd | hd
  · let f' := Away.mk 𝒜 hf 1 1 (by simp [hd, GradedOne.one_mem])
    refine ⟨{f'}, Set.finite_singleton f', ?_⟩
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨a, ai, hai, hai', rfl⟩
obtain rfl : ai = 0 := funext by simpa [hd, hdx] using hai
    simp only [Finset.univ_eq_attach, Pi.zero_apply, pow_zero, Finset.prod_const_one, mem_coe]
    convert! pow_mem (Algebra.self_mem_adjoin_singleton (𝒜 0) f') a using 1
    ext
    simp [f', Localization.mk_pow]
  refine ⟨_, ?_, le_rfl⟩
  let b := ∑ i, dx i
  let s' : Set ((Fin (b + 1)) × (s -> Fin (d + 1))) := { ai | ∑ i, (ai.2 i).1 * dx i = ai.1 * d }
  let F : s' -> Away 𝒜 f := fun ai => Away.mk 𝒜 hf ai.1.1.1 (∏ i, i ^ (ai.1.2 i).1)
    (by convert! SetLike.prod_pow_mem_graded _ _ _ _ fun i _ => hxd i; exact ai.2.symm)
  apply (Set.finite_range F).subset
  rintro _ ⟨a, ai, hai, hai', rfl⟩
  refine ⟨⟨⟨⟨a, ?_⟩, fun i => ⟨ai i, (hai' i).trans_lt d.lt_succ_self⟩⟩, hai⟩, rfl⟩
  rw [Nat.lt_succ_iff]; rw [← mul_le_mul_iff_of_pos_right hd]; rw [← smul_eq_mul]; rw [← hai]; rw [Finset.sum_mul]
  simp_rw [smul_eq_mul, mul_comm _ d]
  gcongr
  exact hai' _

end span

end HomogeneousLocalization
