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

/-- Let `x` be a submonoid of `A`, then `NumDenSameDeg 𝒜 x` is a structure with a numerator and a
denominator with same grading such that the denominator is contained in `x`.
-/
/-
**HomogeneousLocalization.NumDenSameDeg** 是 Mathlib 中的一个归纳类型，位于命名空间 `Homogeneous
Localization`。
形式化陈述：{ι : Type u_1} →   {A : Type u_2} → {σ : Type u_3} → [inst : CommRing A] →
 [SetLike σ A] → (ι → σ) → Submonoid A → Type (max u_1 u_2)
参数：ι → σ；max u_1 u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `x` be a submonoid of `A`, then `NumDenSameDeg 𝒜 x` is a structure with a nu
merator and a
denominator with same grading such that the denominator is contained in `x`.
-/
structure NumDenSameDeg (𝒜 : ι → σ) (x : Submonoid A) where
  deg : ι
  (num den : 𝒜 deg)
  den_mem : (den : A) ∈ x

end

namespace NumDenSameDeg

open SetLike.GradedMonoid Submodule

@[ext]
/-
**HomogeneousLocalization.NumDenSameDeg.ext** 是 Mathlib 中的一个定理，位于命名空间 `Homogeneo
usLocalization.NumDenSameDeg`。
形式化陈述：ext {𝒜 : ι -> σ} (x : Submonoid A) {c1 c2 : NumDenSameDeg 𝒜 x} (hdeg : c1.
deg = c2.deg) (hnum : (c1.num : A) = c2.num) (hden : (c1.den : A) = c2.den) : c1
 = c2
参数：x : Submonoid A；hdeg : c1.deg = c2.deg；hnum : (c1.num : A) = c2.num；hden : (c
1.den : A) = c2.den。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ext {𝒜 : ι → σ} (x : Submonoid A)
    {c1 c2 : NumDenSameDeg 𝒜 x} (hdeg : c1.deg = c2.deg) (hnum : (c1.num : A) = c2.num)
    (hden : (c1.den : A) = c2.den) : c1 = c2 := by
  rcases c1 with ⟨i1, ⟨n1, hn1⟩, ⟨d1, hd1⟩, h1⟩
  rcases c2 with ⟨i2, ⟨n2, hn2⟩, ⟨d2, hd2⟩, h2⟩
  dsimp only [Subtype.coe_mk] at *
  subst hdeg hnum hden
  congr

section Neg
variable [NegMemClass σ A] {𝒜 : ι → σ} (x : Submonoid A)

/-
**HomogeneousLocalization.NumDenSameDeg.** 是 Mathlib 中的一个实例，位于命名空间 `HomogeneousL
ocalization.NumDenSameDeg`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Neg (NumDenSameDeg 𝒜 x) where
  neg c := ⟨c.deg, ⟨-c.num, neg_mem c.num.2⟩, c.den, c.den_mem⟩

@[simp]
/-
**HomogeneousLocalization.NumDenSameDeg.deg_neg** 是 Mathlib 中的一个定理，位于命名空间 `Homog
eneousLocalization.NumDenSameDeg`。
形式化陈述：deg_neg (c : NumDenSameDeg 𝒜 x) : (-c).deg = c.deg
参数：c : NumDenSameDeg 𝒜 x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem deg_neg (c : NumDenSameDeg 𝒜 x) : (-c).deg = c.deg :=
  rfl

@[simp]
/-
**HomogeneousLocalization.NumDenSameDeg.num_neg** 是 Mathlib 中的一个定理，位于命名空间 `Homog
eneousLocalization.NumDenSameDeg`。
形式化陈述：num_neg (c : NumDenSameDeg 𝒜 x) : ((-c).num : A) = -c.num
参数：c : NumDenSameDeg 𝒜 x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem num_neg (c : NumDenSameDeg 𝒜 x) : ((-c).num : A) = -c.num :=
  rfl

@[simp]
/-
**HomogeneousLocalization.NumDenSameDeg.den_neg** 是 Mathlib 中的一个定理，位于命名空间 `Homog
eneousLocalization.NumDenSameDeg`。
形式化陈述：den_neg (c : NumDenSameDeg 𝒜 x) : ((-c).den : A) = c.den
参数：c : NumDenSameDeg 𝒜 x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem den_neg (c : NumDenSameDeg 𝒜 x) : ((-c).den : A) = c.den :=
  rfl

end Neg

section SMul

variable {𝒜 : ι → σ} (x : Submonoid A) {α : Type*} [SMul α A] [SMulMemClass σ α A]

/-
**HomogeneousLocalization.NumDenSameDeg.** 是 Mathlib 中的一个实例，位于命名空间 `HomogeneousL
ocalization.NumDenSameDeg`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul α (NumDenSameDeg 𝒜 x) where
  smul m c := ⟨c.deg, m • c.num, c.den, c.den_mem⟩

@[simp]
/-
**HomogeneousLocalization.NumDenSameDeg.deg_smul** 是 Mathlib 中的一个定理，位于命名空间 `Homo
geneousLocalization.NumDenSameDeg`。
形式化陈述：deg_smul (c : NumDenSameDeg 𝒜 x) (m : α) : (m • c).deg = c.deg
参数：c : NumDenSameDeg 𝒜 x；m : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem deg_smul (c : NumDenSameDeg 𝒜 x) (m : α) : (m • c).deg = c.deg :=
  rfl

@[simp]
/-
**HomogeneousLocalization.NumDenSameDeg.num_smul** 是 Mathlib 中的一个定理，位于命名空间 `Homo
geneousLocalization.NumDenSameDeg`。
形式化陈述：num_smul (c : NumDenSameDeg 𝒜 x) (m : α) : ((m • c).num : A) = m • c.num
参数：c : NumDenSameDeg 𝒜 x；m : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem num_smul (c : NumDenSameDeg 𝒜 x) (m : α) : ((m • c).num : A) = m • c.num :=
  rfl

@[simp]
/-
**HomogeneousLocalization.NumDenSameDeg.den_smul** 是 Mathlib 中的一个定理，位于命名空间 `Homo
geneousLocalization.NumDenSameDeg`。
形式化陈述：den_smul (c : NumDenSameDeg 𝒜 x) (m : α) : ((m • c).den : A) = c.den
参数：c : NumDenSameDeg 𝒜 x；m : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem den_smul (c : NumDenSameDeg 𝒜 x) (m : α) : ((m • c).den : A) = c.den :=
  rfl

end SMul

variable [AddSubmonoidClass σ A] {𝒜 : ι → σ} (x : Submonoid A)
variable [AddCommMonoid ι] [DecidableEq ι] [GradedRing 𝒜]

open GradedOne in
/-
**HomogeneousLocalization.NumDenSameDeg.** 是 Mathlib 中的一个实例，位于命名空间 `HomogeneousL
ocalization.NumDenSameDeg`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One (NumDenSameDeg 𝒜 x) where
  one :=
    { deg := 0
      num := ⟨1, one_mem⟩
      den := ⟨1, one_mem⟩
      den_mem := one_mem _ }

@[simp]
/-
**HomogeneousLocalization.NumDenSameDeg.deg_one** 是 Mathlib 中的一个定理，位于命名空间 `Homog
eneousLocalization.NumDenSameDeg`。
形式化陈述：deg_one : (1 : NumDenSameDeg 𝒜 x).deg = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem deg_one : (1 : NumDenSameDeg 𝒜 x).deg = 0 :=
  rfl

@[simp]
/-
**HomogeneousLocalization.NumDenSameDeg.num_one** 是 Mathlib 中的一个定理，位于命名空间 `Homog
eneousLocalization.NumDenSameDeg`。
形式化陈述：num_one : ((1 : NumDenSameDeg 𝒜 x).num : A) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem num_one : ((1 : NumDenSameDeg 𝒜 x).num : A) = 1 :=
  rfl

@[simp]
/-
**HomogeneousLocalization.NumDenSameDeg.den_one** 是 Mathlib 中的一个定理，位于命名空间 `Homog
eneousLocalization.NumDenSameDeg`。
形式化陈述：den_one : ((1 : NumDenSameDeg 𝒜 x).den : A) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem den_one : ((1 : NumDenSameDeg 𝒜 x).den : A) = 1 :=
  rfl

open GradedOne in
/-
**HomogeneousLocalization.NumDenSameDeg.** 是 Mathlib 中的一个实例，位于命名空间 `HomogeneousL
ocalization.NumDenSameDeg`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero (NumDenSameDeg 𝒜 x) where
  zero := ⟨0, 0, ⟨1, one_mem⟩, one_mem _⟩

@[simp]
/-
**HomogeneousLocalization.NumDenSameDeg.deg_zero** 是 Mathlib 中的一个定理，位于命名空间 `Homo
geneousLocalization.NumDenSameDeg`。
形式化陈述：deg_zero : (0 : NumDenSameDeg 𝒜 x).deg = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem deg_zero : (0 : NumDenSameDeg 𝒜 x).deg = 0 :=
  rfl

@[simp]
/-
**HomogeneousLocalization.NumDenSameDeg.num_zero** 是 Mathlib 中的一个定理，位于命名空间 `Homo
geneousLocalization.NumDenSameDeg`。
形式化陈述：num_zero : (0 : NumDenSameDeg 𝒜 x).num = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem num_zero : (0 : NumDenSameDeg 𝒜 x).num = 0 :=
  rfl

@[simp]
/-
**HomogeneousLocalization.NumDenSameDeg.den_zero** 是 Mathlib 中的一个定理，位于命名空间 `Homo
geneousLocalization.NumDenSameDeg`。
形式化陈述：den_zero : ((0 : NumDenSameDeg 𝒜 x).den : A) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem den_zero : ((0 : NumDenSameDeg 𝒜 x).den : A) = 1 :=
  rfl

open GradedMul in
/-
**HomogeneousLocalization.NumDenSameDeg.** 是 Mathlib 中的一个实例，位于命名空间 `HomogeneousL
ocalization.NumDenSameDeg`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mul (NumDenSameDeg 𝒜 x) where
  mul p q :=
    { deg := p.deg + q.deg
      num := ⟨p.num * q.num, mul_mem p.num.prop q.num.prop⟩
      den := ⟨p.den * q.den, mul_mem p.den.prop q.den.prop⟩
      den_mem := Submonoid.mul_mem _ p.den_mem q.den_mem }

@[simp]
/-
**HomogeneousLocalization.NumDenSameDeg.deg_mul** 是 Mathlib 中的一个定理，位于命名空间 `Homog
eneousLocalization.NumDenSameDeg`。
形式化陈述：deg_mul (c1 c2 : NumDenSameDeg 𝒜 x) : (c1 * c2).deg = c1.deg + c2.deg
参数：c1 c2 : NumDenSameDeg 𝒜 x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem deg_mul (c1 c2 : NumDenSameDeg 𝒜 x) : (c1 * c2).deg = c1.deg + c2.deg :=
  rfl

@[simp]
/-
**HomogeneousLocalization.NumDenSameDeg.num_mul** 是 Mathlib 中的一个定理，位于命名空间 `Homog
eneousLocalization.NumDenSameDeg`。
形式化陈述：num_mul (c1 c2 : NumDenSameDeg 𝒜 x) : ((c1 * c2).num : A) = c1.num * c2.nu
m
参数：c1 c2 : NumDenSameDeg 𝒜 x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem num_mul (c1 c2 : NumDenSameDeg 𝒜 x) : ((c1 * c2).num : A) = c1.num * c2.num :=
  rfl

@[simp]
/-
**HomogeneousLocalization.NumDenSameDeg.den_mul** 是 Mathlib 中的一个定理，位于命名空间 `Homog
eneousLocalization.NumDenSameDeg`。
形式化陈述：den_mul (c1 c2 : NumDenSameDeg 𝒜 x) : ((c1 * c2).den : A) = c1.den * c2.de
n
参数：c1 c2 : NumDenSameDeg 𝒜 x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem den_mul (c1 c2 : NumDenSameDeg 𝒜 x) : ((c1 * c2).den : A) = c1.den * c2.den :=
  rfl
/-
**HomogeneousLocalization.NumDenSameDeg.** 是 Mathlib 中的一个实例，位于命名空间 `HomogeneousL
ocalization.NumDenSameDeg`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**HomogeneousLocalization.NumDenSameDeg.deg_add** 是 Mathlib 中的一个定理，位于命名空间 `Homog
eneousLocalization.NumDenSameDeg`。
形式化陈述：deg_add (c1 c2 : NumDenSameDeg 𝒜 x) : (c1 + c2).deg = c1.deg + c2.deg
参数：c1 c2 : NumDenSameDeg 𝒜 x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem deg_add (c1 c2 : NumDenSameDeg 𝒜 x) : (c1 + c2).deg = c1.deg + c2.deg :=
  rfl

@[simp]
/-
**HomogeneousLocalization.NumDenSameDeg.num_add** 是 Mathlib 中的一个定理，位于命名空间 `Homog
eneousLocalization.NumDenSameDeg`。
形式化陈述：num_add (c1 c2 : NumDenSameDeg 𝒜 x) : ((c1 + c2).num : A) = c1.den * c2.nu
m + c2.den * c1.num
参数：c1 c2 : NumDenSameDeg 𝒜 x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem num_add (c1 c2 : NumDenSameDeg 𝒜 x) :
    ((c1 + c2).num : A) = c1.den * c2.num + c2.den * c1.num :=
  rfl

@[simp]
/-
**HomogeneousLocalization.NumDenSameDeg.den_add** 是 Mathlib 中的一个定理，位于命名空间 `Homog
eneousLocalization.NumDenSameDeg`。
形式化陈述：den_add (c1 c2 : NumDenSameDeg 𝒜 x) : ((c1 + c2).den : A) = c1.den * c2.de
n
参数：c1 c2 : NumDenSameDeg 𝒜 x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem den_add (c1 c2 : NumDenSameDeg 𝒜 x) : ((c1 + c2).den : A) = c1.den * c2.den :=
  rfl
/-
**HomogeneousLocalization.NumDenSameDeg.** 是 Mathlib 中的一个实例，位于命名空间 `HomogeneousL
ocalization.NumDenSameDeg`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CommMonoid (NumDenSameDeg 𝒜 x) where
  mul_assoc _ _ _ := ext _ (add_assoc _ _ _) (mul_assoc _ _ _) (mul_assoc _ _ _)
  one_mul _ := ext _ (zero_add _) (one_mul _) (one_mul _)
  mul_one _ := ext _ (add_zero _) (mul_one _) (mul_one _)
  mul_comm _ _ := ext _ (add_comm _ _) (mul_comm _ _) (mul_comm _ _)
/-
**HomogeneousLocalization.NumDenSameDeg.** 是 Mathlib 中的一个实例，位于命名空间 `HomogeneousL
ocalization.NumDenSameDeg`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Pow (NumDenSameDeg 𝒜 x) ℕ where
  pow c n :=
    ⟨n • c.deg, @GradedMonoid.GMonoid.gnpow _ (fun i => ↥(𝒜 i)) _ _ n _ c.num,
      @GradedMonoid.GMonoid.gnpow _ (fun i => ↥(𝒜 i)) _ _ n _ c.den, by
        induction n with
        | zero => simp only [coe_gnpow, pow_zero, one_mem]
        | succ n ih => simpa only [pow_succ, coe_gnpow] using x.mul_mem ih c.den_mem⟩

@[simp]
/-
**HomogeneousLocalization.NumDenSameDeg.deg_pow** 是 Mathlib 中的一个定理，位于命名空间 `Homog
eneousLocalization.NumDenSameDeg`。
形式化陈述：deg_pow (c : NumDenSameDeg 𝒜 x) (n : Nat) : (c ^ n).deg = n • c.deg
参数：c : NumDenSameDeg 𝒜 x；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem deg_pow (c : NumDenSameDeg 𝒜 x) (n : ℕ) : (c ^ n).deg = n • c.deg :=
  rfl

@[simp]
/-
**HomogeneousLocalization.NumDenSameDeg.num_pow** 是 Mathlib 中的一个定理，位于命名空间 `Homog
eneousLocalization.NumDenSameDeg`。
形式化陈述：num_pow (c : NumDenSameDeg 𝒜 x) (n : Nat) : ((c ^ n).num : A) = (c.num : A
) ^ n
参数：c : NumDenSameDeg 𝒜 x；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem num_pow (c : NumDenSameDeg 𝒜 x) (n : ℕ) : ((c ^ n).num : A) = (c.num : A) ^ n :=
  rfl

@[simp]
/-
**HomogeneousLocalization.NumDenSameDeg.den_pow** 是 Mathlib 中的一个定理，位于命名空间 `Homog
eneousLocalization.NumDenSameDeg`。
形式化陈述：den_pow (c : NumDenSameDeg 𝒜 x) (n : Nat) : ((c ^ n).den : A) = (c.den : A
) ^ n
参数：c : NumDenSameDeg 𝒜 x；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem den_pow (c : NumDenSameDeg 𝒜 x) (n : ℕ) : ((c ^ n).den : A) = (c.den : A) ^ n :=
  rfl

variable (𝒜)

/-- For `x : prime ideal of A` and any `p : NumDenSameDeg 𝒜 x`, or equivalent a numerator and a
denominator of the same degree, we get an element `p.num / p.den` of `Aₓ`.
-/
/-
**HomogeneousLocalization.NumDenSameDeg.embedding** 是 Mathlib 中的一个定义，位于命名空间 `Hom
ogeneousLocalization.NumDenSameDeg`。
形式化陈述：embedding (p : NumDenSameDeg 𝒜 x) : at x
参数：p : NumDenSameDeg 𝒜 x。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HomogeneousLocalization.NumDenSameDeg.den_mem`：∀ {ι : Type u_1} {A : Typ
e u_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A] {𝒜 : ι → σ} {x 
: Submonoid A}   (self : Homogeneou…

--- 原说明 ---
For `x : prime ideal of A` and any `p : NumDenSameDeg 𝒜 x`, or equivalent a nume
rator and a
denominator of the same degree, we get an element `p.num / p.den` of `Aₓ`.
-/
def embedding (p : NumDenSameDeg 𝒜 x) : at x :=
  Localization.mk p.num ⟨p.den, p.den_mem⟩

end NumDenSameDeg

end HomogeneousLocalization

/-- For `x : prime ideal of A`, `HomogeneousLocalization 𝒜 x` is `NumDenSameDeg 𝒜 x` modulo the
kernel of `embedding 𝒜 x`. This is essentially the subring of `Aₓ` where the numerator and
denominator share the same grading.
-/
/-
**HomogeneousLocalization** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：HomogeneousLocalization (𝒜 : ι -> σ) (x : Submonoid A) : Type _
参数：𝒜 : ι -> σ；x : Submonoid A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `x : prime ideal of A`, `HomogeneousLocalization 𝒜 x` is `NumDenSameDeg 𝒜 x`
 modulo the
kernel of `embedding 𝒜 x`. This is essentially the subring of `Aₓ` where the num
erator and
denominator share the same grading.
-/
def HomogeneousLocalization (𝒜 : ι → σ) (x : Submonoid A) : Type _ :=
  Quotient (Setoid.ker <| HomogeneousLocalization.NumDenSameDeg.embedding 𝒜 x)

namespace HomogeneousLocalization

open HomogeneousLocalization HomogeneousLocalization.NumDenSameDeg

section
variable {𝒜 : ι → σ} {x : Submonoid A}

/-- Construct an element of `HomogeneousLocalization 𝒜 x` from a homogeneous fraction. -/
/-
**HomogeneousLocalization.mk** 是 Mathlib 中的一个缩写定义，位于命名空间 `HomogeneousLocalizatio
n`。
形式化陈述：mk (y : HomogeneousLocalization.NumDenSameDeg 𝒜 x) : HomogeneousLocalizati
on 𝒜 x
参数：y : HomogeneousLocalization.NumDenSameDeg 𝒜 x。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)

--- 原说明 ---
Construct an element of `HomogeneousLocalization 𝒜 x` from a homogeneous fractio
n.
-/
abbrev mk (y : HomogeneousLocalization.NumDenSameDeg 𝒜 x) : HomogeneousLocalization 𝒜 x :=
  Quotient.mk'' y
/-
**HomogeneousLocalization.mk_surjective** 是 Mathlib 中的一个引理，位于命名空间 `HomogeneousLo
calization`。
形式化陈述：mk_surjective : Function.Surjective (mk (𝒜
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''_surjective`：∀ {α : Sort u_1} {s₁ : Setoid α}, Function.Sur
jective Quotient.mk''
-/
lemma mk_surjective : Function.Surjective (mk (𝒜 := 𝒜) (x := x)) :=
  Quotient.mk''_surjective

/-- View an element of `HomogeneousLocalization 𝒜 x` as an element of `Aₓ` by forgetting that the
numerator and denominator are of the same grading.
-/
/-
**HomogeneousLocalization.val** 是 Mathlib 中的一个定义，位于命名空间 `HomogeneousLocalization
`。
形式化陈述：val (y : HomogeneousLocalization 𝒜 x) : at x
参数：y : HomogeneousLocalization 𝒜 x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
View an element of `HomogeneousLocalization 𝒜 x` as an element of `Aₓ` by forget
ting that the
numerator and denominator are of the same grading.
-/
def val (y : HomogeneousLocalization 𝒜 x) : at x :=
  Quotient.liftOn' y (NumDenSameDeg.embedding 𝒜 x) fun _ _ => id

@[simp]
/-
**HomogeneousLocalization.val_mk** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousLocalizat
ion`。
形式化陈述：val_mk (i : NumDenSameDeg 𝒜 x) : val (mk i) = Localization.mk (i.num : A) 
⟨i.den, i.den_mem⟩
参数：i : NumDenSameDeg 𝒜 x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem val_mk (i : NumDenSameDeg 𝒜 x) :
    val (mk i) = Localization.mk (i.num : A) ⟨i.den, i.den_mem⟩ :=
  rfl

variable (x)

@[ext]
/-
**HomogeneousLocalization.val_injective** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousLo
calization`。
形式化陈述：val_injective : Function.Injective (HomogeneousLocalization.val (𝒜
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `instSubsingleton`：∀ (p : Prop), Subsingleton p
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `Quotient.sound'`：sound' {a b : α} : s₁ a b -> @Quotient.mk'' α s₁ a = Qu
otient.mk'' b
-/
theorem val_injective : Function.Injective (HomogeneousLocalization.val (𝒜 := 𝒜) (x := x)) :=
  fun a b => Quotient.recOnSubsingleton₂' a b fun _ _ h => Quotient.sound' h

variable (𝒜) {x} in
/-
**HomogeneousLocalization.subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `HomogeneousLoc
alization`。
形式化陈述：subsingleton (hx : 0 in x) : Subsingleton (HomogeneousLocalization 𝒜 x)
参数：hx : 0 in x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.subsingleton`：subsingleton (h : 0 in M) : Subsingleton S
· 使用定理 `Function.Injective.subsingleton`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β}, Function.Injective f → ∀ [Subsingleton β], Subsingleton α
· 使用定理 `HomogeneousLocalization.val_injective`：val_injective : Function.Injectiv
e (HomogeneousLocalization.val (𝒜
-/
lemma subsingleton (hx : 0 ∈ x) : Subsingleton (HomogeneousLocalization 𝒜 x) :=
  have := IsLocalization.subsingleton (S := at x) hx
  (HomogeneousLocalization.val_injective (𝒜 := 𝒜) (x := x)).subsingleton

end

section SMul
variable {𝒜 : ι → σ} (x : Submonoid A)
variable {α : Type*} [SMul α A] [IsScalarTower α A A] [SMulMemClass σ α A]

/-
**HomogeneousLocalization.** 是 Mathlib 中的一个实例，位于命名空间 `HomogeneousLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul α (HomogeneousLocalization 𝒜 x) where
  smul m := Quotient.map' (m • ·) fun c1 c2 (h : Localization.mk _ _ = Localization.mk _ _) => by
    change Localization.mk _ _ = Localization.mk _ _
    simp only [num_smul, den_smul]
    convert! congr_arg (fun z : at x => m • z) h <;> rw [Localization.smul_mk]
/-
**HomogeneousLocalization.mk_smul** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousLocaliza
tion`。
形式化陈述：∀ {ι : Type u_1} {A : Type u_2} {σ : Type u_3} [inst : CommRing A] [inst_1
 : SetLike σ A] {𝒜 : ι → σ} (x : Submonoid A)   {α : Type u_4} [inst_2 : SMul α 
A] [inst_3 : IsScalarTower α A A] [inst_4 : SMulMemClass σ α A]   (i : Homogeneo
usLocalization.NumDenSameDeg 𝒜 x) (m : α),   HomogeneousLocalization.mk (m • i) 
= m • HomogeneousLocalization.mk i
参数：x : Submonoid A；i : HomogeneousLocalization.NumDenSameDeg 𝒜 x；m : α；m • i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mk_smul (i : NumDenSameDeg 𝒜 x) (m : α) : mk (m • i) = m • mk i := rfl

@[simp]
/-
**HomogeneousLocalization.val_smul** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousLocaliz
ation`。
形式化陈述：val_smul (n : α) : forall y : HomogeneousLocalization 𝒜 x, (n • y).val = n
 • y.val
参数：n : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.ind'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁ → Prop}
, (∀ (a : α), p (Quotient.mk'' a)) → ∀ (q : Quotient s₁), p q
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HomogeneousLocalization.mk_smul`：∀ {ι : Type u_1} {A : Type u_2} {σ : Ty
pe u_3} [inst : CommRing A] [inst_1 : SetLike σ A] {𝒜 : ι → σ} (x : Submonoid A)
   {α : Type u_4} [in…
· 使用定理 `HomogeneousLocalization.NumDenSameDeg.den_mem`：∀ {ι : Type u_1} {A : Typ
e u_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A] {𝒜 : ι → σ} {x 
: Submonoid A}   (self : Homogeneou…
· 使用定理 `HomogeneousLocalization.val_mk`：val_mk (i : NumDenSameDeg 𝒜 x) : val (mk
 i) = Localization.mk (i.num : A) ⟨i.den, i.den_mem⟩
· 使用定理 `Localization.smul_mk`：smul_mk [SMul R M] [IsScalarTower R M M] (c : R) (
a b) : c • (mk a b : Localization S) = mk (c • a) b
· 使用定理 `HomogeneousLocalization.NumDenSameDeg.num_smul`：num_smul (c : NumDenSame
Deg 𝒜 x) (m : α) : ((m • c).num : A) = m • c.num
-/
theorem val_smul (n : α) : ∀ y : HomogeneousLocalization 𝒜 x, (n • y).val = n • y.val :=
  Quotient.ind' fun _ ↦ by rw [← mk_smul, val_mk, val_mk, Localization.smul_mk, num_smul]; rfl

end SMul

section nsmul
variable [AddSubmonoidClass σ A] {𝒜 : ι → σ} (x : Submonoid A)

/-
**HomogeneousLocalization.** 是 Mathlib 中的一个实例，位于命名空间 `HomogeneousLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul ℕ (HomogeneousLocalization 𝒜 x) :=
  haveI := AddSubmonoidClass.nsmulMemClass (S := σ) (M := A)
  HomogeneousLocalization.instSMul x
/-
**HomogeneousLocalization.val_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousLocali
zation`。
形式化陈述：val_nsmul (n : Nat) (y : HomogeneousLocalization 𝒜 x) : (n • y).val = n • 
y.val
参数：n : Nat；y : HomogeneousLocalization 𝒜 x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomogeneousLocalization.val_smul`：val_smul (n : α) : forall y : Homogene
ousLocalization 𝒜 x, (n • y).val = n • y.val
· 使用引理 `OreLocalization.nsmul_eq_nsmul`：nsmul_eq_nsmul (n : Nat) (x : X[S⁻¹]) : 
letI inst
-/
theorem val_nsmul (n : ℕ) (y : HomogeneousLocalization 𝒜 x) : (n • y).val = n • y.val := by
  rw [val_smul, OreLocalization.nsmul_eq_nsmul]

end nsmul

section zsmul
variable [AddSubgroupClass σ A] {𝒜 : ι → σ} (x : Submonoid A)

/-
**HomogeneousLocalization.** 是 Mathlib 中的一个实例，位于命名空间 `HomogeneousLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul ℤ (HomogeneousLocalization 𝒜 x) :=
  haveI := AddSubgroupClass.zsmulMemClass (S := σ) (M := A)
  HomogeneousLocalization.instSMul x
/-
**HomogeneousLocalization.val_zsmul** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousLocali
zation`。
形式化陈述：val_zsmul (n : Int) (y : HomogeneousLocalization 𝒜 x) : (n • y).val = n • 
y.val
参数：n : Int；y : HomogeneousLocalization 𝒜 x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomogeneousLocalization.val_smul`：val_smul (n : α) : forall y : Homogene
ousLocalization 𝒜 x, (n • y).val = n • y.val
· 使用引理 `OreLocalization.zsmul_eq_zsmul`：zsmul_eq_zsmul (n : Int) (x : X[S⁻¹]) : 
letI inst
-/
theorem val_zsmul (n : ℤ) (y : HomogeneousLocalization 𝒜 x) : (n • y).val = n • y.val := by
  rw [val_smul, OreLocalization.zsmul_eq_zsmul]

end zsmul

section Neg
variable [NegMemClass σ A] {𝒜 : ι → σ} (x : Submonoid A)

/-
**HomogeneousLocalization.** 是 Mathlib 中的一个实例，位于命名空间 `HomogeneousLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Neg (HomogeneousLocalization 𝒜 x) where
  neg := Quotient.map' Neg.neg fun c1 c2 (h : Localization.mk _ _ = Localization.mk _ _) => by
    change Localization.mk _ _ = Localization.mk _ _
    simp only [num_neg, den_neg, ← Localization.neg_mk]
    exact congr_arg Neg.neg h
/-
**HomogeneousLocalization.mk_neg** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousLocalizat
ion`。
形式化陈述：∀ {ι : Type u_1} {A : Type u_2} {σ : Type u_3} [inst : CommRing A] [inst_1
 : SetLike σ A] [inst_2 : NegMemClass σ A]   {𝒜 : ι → σ} (x : Submonoid A) (i : 
HomogeneousLocalization.NumDenSameDeg 𝒜 x),   HomogeneousLocalization.mk (-i) = 
-HomogeneousLocalization.mk i
参数：x : Submonoid A；i : HomogeneousLocalization.NumDenSameDeg 𝒜 x；-i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mk_neg (i : NumDenSameDeg 𝒜 x) : mk (-i) = -mk i := rfl

@[simp]
/-
**HomogeneousLocalization.val_neg** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousLocaliza
tion`。
形式化陈述：val_neg {x} : forall y : HomogeneousLocalization 𝒜 x, (-y).val = -y.val
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.ind'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁ → Prop}
, (∀ (a : α), p (Quotient.mk'' a)) → ∀ (q : Quotient s₁), p q
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HomogeneousLocalization.mk_neg`：∀ {ι : Type u_1} {A : Type u_2} {σ : Typ
e u_3} [inst : CommRing A] [inst_1 : SetLike σ A] [inst_2 : NegMemClass σ A]   {
𝒜 : ι → σ} (x : Subm…
· 使用定理 `HomogeneousLocalization.NumDenSameDeg.den_mem`：∀ {ι : Type u_1} {A : Typ
e u_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A] {𝒜 : ι → σ} {x 
: Submonoid A}   (self : Homogeneou…
· 使用定理 `HomogeneousLocalization.val_mk`：val_mk (i : NumDenSameDeg 𝒜 x) : val (mk
 i) = Localization.mk (i.num : A) ⟨i.den, i.den_mem⟩
· 使用定理 `Localization.neg_mk`：neg_mk (a b) : -(mk a b : Localization M) = mk (-a)
 b
-/
theorem val_neg {x} : ∀ y : HomogeneousLocalization 𝒜 x, (-y).val = -y.val :=
  Quotient.ind' fun y ↦ by rw [← mk_neg, val_mk, val_mk, Localization.neg_mk]; rfl

end Neg

variable [AddSubgroupClass σ A] [AddCommMonoid ι] [DecidableEq ι]
variable {𝒜 : ι → σ} [GradedRing 𝒜] (x : Submonoid A)

/-
**HomogeneousLocalization.hasPow** 是 Mathlib 中的一个实例，位于命名空间 `HomogeneousLocalizat
ion`。
形式化陈述：hasPow : Pow (HomogeneousLocalization 𝒜 x) Nat where pow z n
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.map'`：map'_mk'' (f : α -> β) (h) (x : α) : (Quotient.mk'' x : Q
uotient s₁).map' f h = (Quotient.mk'' (f x) : Quotient s₂)
· 使用定理 `HomogeneousLocalization.NumDenSameDeg.den_mem`：∀ {ι : Type u_1} {A : Typ
e u_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A] {𝒜 : ι → σ} {x 
: Submonoid A}   (self : Homogeneou…
-/
instance hasPow : Pow (HomogeneousLocalization 𝒜 x) ℕ where
  pow z n :=
    (Quotient.map' (· ^ n) fun c1 c2 (h : Localization.mk _ _ = Localization.mk _ _) => by
          change Localization.mk _ _ = Localization.mk _ _
          simp only [num_pow, den_pow]
          convert! congr_arg (fun z : at x => z ^ n) h <;> rw [Localization.mk_pow] <;> rfl :
        HomogeneousLocalization 𝒜 x → HomogeneousLocalization 𝒜 x)
      z
/-
**HomogeneousLocalization.mk_pow** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousLocalizat
ion`。
形式化陈述：∀ {ι : Type u_1} {A : Type u_2} {σ : Type u_3} [inst : CommRing A] [inst_1
 : SetLike σ A]   [inst_2 : AddSubgroupClass σ A] [inst_3 : AddCommMonoid ι] [in
st_4 : DecidableEq ι] {𝒜 : ι → σ}   [inst_5 : GradedRing 𝒜] (x : Submonoid A) (i
 : HomogeneousLocalization.NumDenSameDeg 𝒜 x) (n : ℕ),   HomogeneousLocalization
.mk (i ^ n) = HomogeneousLocalization.mk i ^ n
参数：x : Submonoid A；i : HomogeneousLocalization.NumDenSameDeg 𝒜 x；n : ℕ；i ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
-/
@[simp] lemma mk_pow (i : NumDenSameDeg 𝒜 x) (n : ℕ) : mk (i ^ n) = mk i ^ n := rfl
/-
**HomogeneousLocalization.** 是 Mathlib 中的一个实例，位于命名空间 `HomogeneousLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add (HomogeneousLocalization 𝒜 x) where
  add :=
    Quotient.map₂ (· + ·)
      fun c1 c2 (h : Localization.mk _ _ = Localization.mk _ _) c3 c4
        (h' : Localization.mk _ _ = Localization.mk _ _) => by
      change Localization.mk _ _ = Localization.mk _ _
      simp only [num_add, den_add]
      convert! congr_arg₂ (· + ·) h h' <;> rw [Localization.add_mk] <;> rfl
/-
**HomogeneousLocalization.mk_add** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousLocalizat
ion`。
形式化陈述：∀ {ι : Type u_1} {A : Type u_2} {σ : Type u_3} [inst : CommRing A] [inst_1
 : SetLike σ A]   [inst_2 : AddSubgroupClass σ A] [inst_3 : AddCommMonoid ι] [in
st_4 : DecidableEq ι] {𝒜 : ι → σ}   [inst_5 : GradedRing 𝒜] (x : Submonoid A) (i
 j : HomogeneousLocalization.NumDenSameDeg 𝒜 x),   HomogeneousLocalization.mk (i
 + j) = HomogeneousLocalization.mk i + HomogeneousLocalization.mk j
参数：x : Submonoid A；i j : HomogeneousLocalization.NumDenSameDeg 𝒜 x；i + j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
-/
@[simp] lemma mk_add (i j : NumDenSameDeg 𝒜 x) : mk (i + j) = mk i + mk j := rfl
/-
**HomogeneousLocalization.** 是 Mathlib 中的一个实例，位于命名空间 `HomogeneousLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Sub (HomogeneousLocalization 𝒜 x) where sub z1 z2 := z1 + -z2
/-
**HomogeneousLocalization.** 是 Mathlib 中的一个实例，位于命名空间 `HomogeneousLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mul (HomogeneousLocalization 𝒜 x) where
  mul :=
    Quotient.map₂ (· * ·)
      fun c1 c2 (h : Localization.mk _ _ = Localization.mk _ _) c3 c4
        (h' : Localization.mk _ _ = Localization.mk _ _) => by
      change Localization.mk _ _ = Localization.mk _ _
      simp only [num_mul, den_mul]
      convert! congr_arg₂ (· * ·) h h' <;> rw [Localization.mk_mul] <;> rfl
/-
**HomogeneousLocalization.mk_mul** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousLocalizat
ion`。
形式化陈述：∀ {ι : Type u_1} {A : Type u_2} {σ : Type u_3} [inst : CommRing A] [inst_1
 : SetLike σ A]   [inst_2 : AddSubgroupClass σ A] [inst_3 : AddCommMonoid ι] [in
st_4 : DecidableEq ι] {𝒜 : ι → σ}   [inst_5 : GradedRing 𝒜] (x : Submonoid A) (i
 j : HomogeneousLocalization.NumDenSameDeg 𝒜 x),   HomogeneousLocalization.mk (i
 * j) = HomogeneousLocalization.mk i * HomogeneousLocalization.mk j
参数：x : Submonoid A；i j : HomogeneousLocalization.NumDenSameDeg 𝒜 x；i * j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
-/
@[simp] lemma mk_mul (i j : NumDenSameDeg 𝒜 x) : mk (i * j) = mk i * mk j := rfl
/-
**HomogeneousLocalization.** 是 Mathlib 中的一个实例，位于命名空间 `HomogeneousLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One (HomogeneousLocalization 𝒜 x) where one := Quotient.mk'' 1
/-
**HomogeneousLocalization.mk_one** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousLocalizat
ion`。
形式化陈述：∀ {ι : Type u_1} {A : Type u_2} {σ : Type u_3} [inst : CommRing A] [inst_1
 : SetLike σ A]   [inst_2 : AddSubgroupClass σ A] [inst_3 : AddCommMonoid ι] [in
st_4 : DecidableEq ι] {𝒜 : ι → σ}   [inst_5 : GradedRing 𝒜] (x : Submonoid A), H
omogeneousLocalization.mk 1 = 1
参数：x : Submonoid A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
-/
@[simp] lemma mk_one : mk (1 : NumDenSameDeg 𝒜 x) = 1 := rfl
/-
**HomogeneousLocalization.** 是 Mathlib 中的一个实例，位于命名空间 `HomogeneousLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero (HomogeneousLocalization 𝒜 x) where zero := Quotient.mk'' 0
/-
**HomogeneousLocalization.mk_zero** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousLocaliza
tion`。
形式化陈述：∀ {ι : Type u_1} {A : Type u_2} {σ : Type u_3} [inst : CommRing A] [inst_1
 : SetLike σ A]   [inst_2 : AddSubgroupClass σ A] [inst_3 : AddCommMonoid ι] [in
st_4 : DecidableEq ι] {𝒜 : ι → σ}   [inst_5 : GradedRing 𝒜] (x : Submonoid A), H
omogeneousLocalization.mk 0 = 0
参数：x : Submonoid A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
-/
@[simp] lemma mk_zero : mk (0 : NumDenSameDeg 𝒜 x) = 0 := rfl
/-
**HomogeneousLocalization.zero_eq** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousLocaliza
tion`。
形式化陈述：zero_eq : (0 : HomogeneousLocalization 𝒜 x) = Quotient.mk'' 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
-/
theorem zero_eq : (0 : HomogeneousLocalization 𝒜 x) = Quotient.mk'' 0 :=
  rfl
/-
**HomogeneousLocalization.one_eq** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousLocalizat
ion`。
形式化陈述：one_eq : (1 : HomogeneousLocalization 𝒜 x) = Quotient.mk'' 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
-/
theorem one_eq : (1 : HomogeneousLocalization 𝒜 x) = Quotient.mk'' 1 :=
  rfl

variable {x}

@[simp]
/-
**HomogeneousLocalization.val_zero** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousLocaliz
ation`。
形式化陈述：val_zero : (0 : HomogeneousLocalization 𝒜 x).val = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `Localization.mk_zero`：mk_zero (x : S) : mk 0 (x : S) = 0
· 使用定理 `HomogeneousLocalization.NumDenSameDeg.den_mem`：∀ {ι : Type u_1} {A : Typ
e u_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A] {𝒜 : ι → σ} {x 
: Submonoid A}   (self : Homogeneou…
-/
theorem val_zero : (0 : HomogeneousLocalization 𝒜 x).val = 0 :=
  Localization.mk_zero _

@[simp]
/-
**HomogeneousLocalization.val_one** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousLocaliza
tion`。
形式化陈述：val_one : (1 : HomogeneousLocalization 𝒜 x).val = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `Localization.mk_one`：mk_one : mk 1 (1 : S) = 1
-/
theorem val_one : (1 : HomogeneousLocalization 𝒜 x).val = 1 :=
  Localization.mk_one

@[simp]
/-
**HomogeneousLocalization.val_add** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousLocaliza
tion`。
形式化陈述：val_add : forall y1 y2 : HomogeneousLocalization 𝒜 x, (y1 + y2).val = y1.v
al + y2.val
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `Quotient.ind₂'`：∀ {α : Sort u_1} {β : Sort u_2} {s₁ : Setoid α} {s₂ : Se
toid β} {p : Quotient s₁ → Quotient s₂ → Prop},   (∀ (a₁ : α) (a₂ : β), p (Quoti
ent.…
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HomogeneousLocalization.mk_add`：∀ {ι : Type u_1} {A : Type u_2} {σ : Typ
e u_3} [inst : CommRing A] [inst_1 : SetLike σ A]   [inst_2 : AddSubgroupClass σ
 A] [inst_3 : AddCom…
· 使用定理 `HomogeneousLocalization.NumDenSameDeg.den_mem`：∀ {ι : Type u_1} {A : Typ
e u_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A] {𝒜 : ι → σ} {x 
: Submonoid A}   (self : Homogeneou…
· 使用定理 `HomogeneousLocalization.val_mk`：val_mk (i : NumDenSameDeg 𝒜 x) : val (mk
 i) = Localization.mk (i.num : A) ⟨i.den, i.den_mem⟩
· 使用定理 `Localization.add_mk`：add_mk (a b c d) : (mk a b : Localization M) + mk c
 d = mk ((b : R) * c + (d : R) * a) (b * d)
-/
theorem val_add : ∀ y1 y2 : HomogeneousLocalization 𝒜 x, (y1 + y2).val = y1.val + y2.val :=
  Quotient.ind₂' fun y1 y2 ↦ by rw [← mk_add, val_mk, val_mk, val_mk, Localization.add_mk]; rfl

@[simp]
/-
**HomogeneousLocalization.val_mul** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousLocaliza
tion`。
形式化陈述：val_mul : forall y1 y2 : HomogeneousLocalization 𝒜 x, (y1 * y2).val = y1.v
al * y2.val
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `Quotient.ind₂'`：∀ {α : Sort u_1} {β : Sort u_2} {s₁ : Setoid α} {s₂ : Se
toid β} {p : Quotient s₁ → Quotient s₂ → Prop},   (∀ (a₁ : α) (a₂ : β), p (Quoti
ent.…
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HomogeneousLocalization.mk_mul`：∀ {ι : Type u_1} {A : Type u_2} {σ : Typ
e u_3} [inst : CommRing A] [inst_1 : SetLike σ A]   [inst_2 : AddSubgroupClass σ
 A] [inst_3 : AddCom…
· 使用定理 `HomogeneousLocalization.NumDenSameDeg.den_mem`：∀ {ι : Type u_1} {A : Typ
e u_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A] {𝒜 : ι → σ} {x 
: Submonoid A}   (self : Homogeneou…
· 使用定理 `HomogeneousLocalization.val_mk`：val_mk (i : NumDenSameDeg 𝒜 x) : val (mk
 i) = Localization.mk (i.num : A) ⟨i.den, i.den_mem⟩
· 使用定理 `Localization.mk_mul`：mk_mul (a c : M) (b d : S) : mk a b * mk c d = mk (
a * c) (b * d)
-/
theorem val_mul : ∀ y1 y2 : HomogeneousLocalization 𝒜 x, (y1 * y2).val = y1.val * y2.val :=
  Quotient.ind₂' fun y1 y2 ↦ by rw [← mk_mul, val_mk, val_mk, val_mk, Localization.mk_mul]; rfl

@[simp]
/-
**HomogeneousLocalization.val_sub** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousLocaliza
tion`。
形式化陈述：val_sub (y1 y2 : HomogeneousLocalization 𝒜 x) : (y1 - y2).val = y1.val - y
2.val
参数：y1 y2 : HomogeneousLocalization 𝒜 x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `AddSubgroupClass.toNegMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass S G],
   NegMemClass S G
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HomogeneousLocalization.val_neg`：val_neg {x} : forall y : HomogeneousLoc
alization 𝒜 x, (-y).val = -y.val
· 使用定理 `HomogeneousLocalization.val_add`：val_add : forall y1 y2 : HomogeneousLoc
alization 𝒜 x, (y1 + y2).val = y1.val + y2.val
-/
theorem val_sub (y1 y2 : HomogeneousLocalization 𝒜 x) : (y1 - y2).val = y1.val - y2.val := by
  rw [sub_eq_add_neg, ← val_neg, ← val_add]; rfl

@[simp]
/-
**HomogeneousLocalization.val_pow** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousLocaliza
tion`。
形式化陈述：val_pow : forall (y : HomogeneousLocalization 𝒜 x) (n : Nat), (y ^ n).val 
= y.val ^ n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `Quotient.ind'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁ → Prop}
, (∀ (a : α), p (Quotient.mk'' a)) → ∀ (q : Quotient s₁), p q
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HomogeneousLocalization.mk_pow`：∀ {ι : Type u_1} {A : Type u_2} {σ : Typ
e u_3} [inst : CommRing A] [inst_1 : SetLike σ A]   [inst_2 : AddSubgroupClass σ
 A] [inst_3 : AddCom…
· 使用定理 `HomogeneousLocalization.NumDenSameDeg.den_mem`：∀ {ι : Type u_1} {A : Typ
e u_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A] {𝒜 : ι → σ} {x 
: Submonoid A}   (self : Homogeneou…
· 使用定理 `HomogeneousLocalization.val_mk`：val_mk (i : NumDenSameDeg 𝒜 x) : val (mk
 i) = Localization.mk (i.num : A) ⟨i.den, i.den_mem⟩
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `Localization.mk_pow`：mk_pow (n : Nat) (a : M) (b : S) : mk a b ^ n = mk 
(a ^ n) (b ^ n)
-/
theorem val_pow : ∀ (y : HomogeneousLocalization 𝒜 x) (n : ℕ), (y ^ n).val = y.val ^ n :=
  Quotient.ind' fun y n ↦ by rw [← mk_pow, val_mk, val_mk, Localization.mk_pow]; rfl
/-
**HomogeneousLocalization.** 是 Mathlib 中的一个实例，位于命名空间 `HomogeneousLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NatCast (HomogeneousLocalization 𝒜 x) :=
  ⟨Nat.unaryCast⟩
/-
**HomogeneousLocalization.** 是 Mathlib 中的一个实例，位于命名空间 `HomogeneousLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IntCast (HomogeneousLocalization 𝒜 x) :=
  ⟨Int.castDef⟩

@[simp]
/-
**HomogeneousLocalization.val_natCast** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousLoca
lization`。
形式化陈述：val_natCast (n : Nat) : (n : HomogeneousLocalization 𝒜 x).val = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomogeneousLocalization.val_zero`：val_zero : (0 : HomogeneousLocalizatio
n 𝒜 x).val = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HomogeneousLocalization.val_add`：val_add : forall y1 y2 : HomogeneousLoc
alization 𝒜 x, (y1 + y2).val = y1.val + y2.val
· 使用定理 `HomogeneousLocalization.val_one`：val_one : (1 : HomogeneousLocalization 
𝒜 x).val = 1
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
-/
theorem val_natCast (n : ℕ) : (n : HomogeneousLocalization 𝒜 x).val = n :=
  show val (Nat.unaryCast n) = _ by induction n <;> simp [Nat.unaryCast, *]

@[simp]
/-
**HomogeneousLocalization.val_intCast** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousLoca
lization`。
形式化陈述：val_intCast (n : Int) : (n : HomogeneousLocalization 𝒜 x).val = n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomogeneousLocalization.val_natCast`：val_natCast (n : Nat) : (n : Homoge
neousLocalization 𝒜 x).val = n
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HomogeneousLocalization.val_neg`：val_neg {x} : forall y : HomogeneousLoc
alization 𝒜 x, (-y).val = -y.val
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `Int.cast_negSucc`：cast_negSucc (n : Nat) : (-[n+1] : R) = -(n + 1 : Nat)
-/
theorem val_intCast (n : ℤ) : (n : HomogeneousLocalization 𝒜 x).val = n :=
  show val (Int.castDef n) = _ by cases n <;> simp [Int.castDef, *]
/-
**HomogeneousLocalization.homogeneousLocalizationCommRing** 是 Mathlib 中的一个实例，位于命
名空间 `HomogeneousLocalization`。
形式化陈述：homogeneousLocalizationCommRing : CommRing (HomogeneousLocalization 𝒜 x)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `HomogeneousLocalization.val_injective`：val_injective : Function.Injectiv
e (HomogeneousLocalization.val (𝒜
· 使用定理 `HomogeneousLocalization.val_zero`：val_zero : (0 : HomogeneousLocalizatio
n 𝒜 x).val = 0
· 使用定理 `HomogeneousLocalization.val_one`：val_one : (1 : HomogeneousLocalization 
𝒜 x).val = 1
· 使用定理 `HomogeneousLocalization.val_add`：val_add : forall y1 y2 : HomogeneousLoc
alization 𝒜 x, (y1 + y2).val = y1.val + y2.val
· 使用定理 `HomogeneousLocalization.val_mul`：val_mul : forall y1 y2 : HomogeneousLoc
alization 𝒜 x, (y1 * y2).val = y1.val * y2.val
· 使用定理 `HomogeneousLocalization.val_sub`：val_sub (y1 y2 : HomogeneousLocalizatio
n 𝒜 x) : (y1 - y2).val = y1.val - y2.val
· 使用定理 `HomogeneousLocalization.val_zsmul`：val_zsmul (n : Int) (y : HomogeneousL
ocalization 𝒜 x) : (n • y).val = n • y.val
· 使用定理 `HomogeneousLocalization.val_pow`：val_pow : forall (y : HomogeneousLocali
zation 𝒜 x) (n : Nat), (y ^ n).val = y.val ^ n
· 使用定理 `HomogeneousLocalization.val_natCast`：val_natCast (n : Nat) : (n : Homoge
neousLocalization 𝒜 x).val = n
· 使用定理 `HomogeneousLocalization.val_intCast`：val_intCast (n : Int) : (n : Homoge
neousLocalization 𝒜 x).val = n
-/
instance homogeneousLocalizationCommRing : CommRing (HomogeneousLocalization 𝒜 x) :=
  (HomogeneousLocalization.val_injective x).commRing _ val_zero val_one val_add val_mul val_neg
    val_sub (val_nsmul x · ·) (val_zsmul x · ·) val_pow val_natCast val_intCast
/-
**HomogeneousLocalization.homogeneousLocalizationAlgebra** 是 Mathlib 中的一个实例，位于命名
空间 `HomogeneousLocalization`。
形式化陈述：homogeneousLocalizationAlgebra : Algebra (HomogeneousLocalization 𝒜 x) (Lo
calization x) where smul p q
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `HomogeneousLocalization.val_one`：val_one : (1 : HomogeneousLocalization 
𝒜 x).val = 1
· 使用定理 `HomogeneousLocalization.val_mul`：val_mul : forall y1 y2 : HomogeneousLoc
alization 𝒜 x, (y1 * y2).val = y1.val * y2.val
· 使用定理 `HomogeneousLocalization.val_zero`：val_zero : (0 : HomogeneousLocalizatio
n 𝒜 x).val = 0
· 使用定理 `HomogeneousLocalization.val_add`：val_add : forall y1 y2 : HomogeneousLoc
alization 𝒜 x, (y1 + y2).val = y1.val + y2.val
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
/-
**HomogeneousLocalization.algebraMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `Homogeneou
sLocalization`。
形式化陈述：∀ {ι : Type u_1} {A : Type u_2} {σ : Type u_3} [inst : CommRing A] [inst_1
 : SetLike σ A]   [inst_2 : AddSubgroupClass σ A] [inst_3 : AddCommMonoid ι] [in
st_4 : DecidableEq ι] {𝒜 : ι → σ}   [inst_5 : GradedRing 𝒜] {x : Submonoid A} (y
 : HomogeneousLocalization 𝒜 x),   (algebraMap (HomogeneousLocalization 𝒜 x) (Lo
calization x)) y = y.val
参数：y : HomogeneousLocalization 𝒜 x；algebraMap (HomogeneousLocalization 𝒜 x) (Loc
alization x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
-/
@[simp] lemma algebraMap_apply (y) :
    algebraMap (HomogeneousLocalization 𝒜 x) (Localization x) y = y.val := rfl
/-
**HomogeneousLocalization.mk_eq_zero_of_num** 是 Mathlib 中的一个引理，位于命名空间 `Homogeneo
usLocalization`。
形式化陈述：mk_eq_zero_of_num (f : NumDenSameDeg 𝒜 x) (h : f.num = 0) : mk f = 0
参数：f : NumDenSameDeg 𝒜 x；h : f.num = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `HomogeneousLocalization.val_injective`：val_injective : Function.Injectiv
e (HomogeneousLocalization.val (𝒜
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomogeneousLocalization.NumDenSameDeg.den_mem`：∀ {ι : Type u_1} {A : Typ
e u_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A] {𝒜 : ι → σ} {x 
: Submonoid A}   (self : Homogeneou…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Localization.mk_zero`：mk_zero (x : S) : mk 0 (x : S) = 0
· 使用定理 `HomogeneousLocalization.val_zero`：val_zero : (0 : HomogeneousLocalizatio
n 𝒜 x).val = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mk_eq_zero_of_num (f : NumDenSameDeg 𝒜 x) (h : f.num = 0) : mk f = 0 := by
  apply val_injective
  simp only [val_mk, val_zero, h, ZeroMemClass.coe_zero, Localization.mk_zero]
/-
**HomogeneousLocalization.mk_eq_zero_of_den** 是 Mathlib 中的一个引理，位于命名空间 `Homogeneo
usLocalization`。
形式化陈述：mk_eq_zero_of_den (f : NumDenSameDeg 𝒜 x) (h : f.den = 0) : mk f = 0
参数：f : NumDenSameDeg 𝒜 x；h : f.den = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用引理 `HomogeneousLocalization.subsingleton`：subsingleton (hx : 0 in x) : Subsi
ngleton (HomogeneousLocalization 𝒜 x)
· 使用定理 `HomogeneousLocalization.NumDenSameDeg.den_mem`：∀ {ι : Type u_1} {A : Typ
e u_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A] {𝒜 : ι → σ} {x 
: Submonoid A}   (self : Homogeneou…
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
lemma mk_eq_zero_of_den (f : NumDenSameDeg 𝒜 x) (h : f.den = 0) : mk f = 0 := by
  have := subsingleton 𝒜 (h ▸ f.den_mem)
  exact Subsingleton.elim _ _

variable (𝒜 x) in
/-- The map from `𝒜 0` to the degree `0` part of `𝒜ₓ` sending `f ↦ f/1`. -/
/-
**HomogeneousLocalization.fromZeroRingHom** 是 Mathlib 中的一个定义，位于命名空间 `Homogeneous
Localization`。
形式化陈述：fromZeroRingHom : 𝒜 0 ->+* HomogeneousLocalization 𝒜 x where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map from `𝒜 0` to the degree `0` part of `𝒜ₓ` sending `f ↦ f/1`.
-/
def fromZeroRingHom : 𝒜 0 →+* HomogeneousLocalization 𝒜 x where
  toFun f := .mk ⟨0, f, 1, one_mem _⟩
  map_one' := rfl
  map_mul' f g := by ext; simp [Localization.mk_mul]
  map_zero' := rfl
  map_add' f g := by ext; simp [Localization.add_mk, add_comm f.1 g.1]
/-
**HomogeneousLocalization.** 是 Mathlib 中的一个实例，位于命名空间 `HomogeneousLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Algebra (𝒜 0) (HomogeneousLocalization 𝒜 x) :=
  (fromZeroRingHom 𝒜 x).toAlgebra
/-
**HomogeneousLocalization.algebraMap_eq** 是 Mathlib 中的一个引理，位于命名空间 `HomogeneousLo
calization`。
形式化陈述：algebraMap_eq : algebraMap (𝒜 0) (HomogeneousLocalization 𝒜 x) = fromZeroR
ingHom 𝒜 x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
-/
lemma algebraMap_eq : algebraMap (𝒜 0) (HomogeneousLocalization 𝒜 x) = fromZeroRingHom 𝒜 x := rfl
/-
**HomogeneousLocalization.** 是 Mathlib 中的一个实例，位于命名空间 `HomogeneousLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsScalarTower (𝒜 0) (HomogeneousLocalization 𝒜 x) (Localization x) :=
  .of_algebraMap_eq' rfl

end HomogeneousLocalization

namespace HomogeneousLocalization

open HomogeneousLocalization HomogeneousLocalization.NumDenSameDeg

section
variable {𝒜 : ι → σ} {x : Submonoid A}

/-- Numerator of an element in `HomogeneousLocalization x`. -/
/-
**HomogeneousLocalization.num** 是 Mathlib 中的一个定义，位于命名空间 `HomogeneousLocalization
`。
形式化陈述：num (f : HomogeneousLocalization 𝒜 x) : A
参数：f : HomogeneousLocalization 𝒜 x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Numerator of an element in `HomogeneousLocalization x`.
-/
def num (f : HomogeneousLocalization 𝒜 x) : A :=
  (Quotient.out f).num

/-- Denominator of an element in `HomogeneousLocalization x`. -/
/-
**HomogeneousLocalization.den** 是 Mathlib 中的一个定义，位于命名空间 `HomogeneousLocalization
`。
形式化陈述：den (f : HomogeneousLocalization 𝒜 x) : A
参数：f : HomogeneousLocalization 𝒜 x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Denominator of an element in `HomogeneousLocalization x`.
-/
def den (f : HomogeneousLocalization 𝒜 x) : A :=
  (Quotient.out f).den

/-- For an element in `HomogeneousLocalization x`, degree is the natural number `i` such that
  `𝒜 i` contains both numerator and denominator. -/
/-
**HomogeneousLocalization.deg** 是 Mathlib 中的一个定义，位于命名空间 `HomogeneousLocalization
`。
形式化陈述：deg (f : HomogeneousLocalization 𝒜 x) : ι
参数：f : HomogeneousLocalization 𝒜 x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For an element in `HomogeneousLocalization x`, degree is the natural number `i` 
such that
  `𝒜 i` contains both numerator and denominator.
-/
def deg (f : HomogeneousLocalization 𝒜 x) : ι :=
  (Quotient.out f).deg
/-
**HomogeneousLocalization.den_mem** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousLocaliza
tion`。
形式化陈述：den_mem (f : HomogeneousLocalization 𝒜 x) : f.den in x
参数：f : HomogeneousLocalization 𝒜 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomogeneousLocalization.NumDenSameDeg.den_mem`：∀ {ι : Type u_1} {A : Typ
e u_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A] {𝒜 : ι → σ} {x 
: Submonoid A}   (self : Homogeneou…
-/
theorem den_mem (f : HomogeneousLocalization 𝒜 x) : f.den ∈ x :=
  (Quotient.out f).den_mem
/-
**HomogeneousLocalization.num_mem_deg** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousLoca
lization`。
形式化陈述：num_mem_deg (f : HomogeneousLocalization 𝒜 x) : f.num in 𝒜 f.deg
参数：f : HomogeneousLocalization 𝒜 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem num_mem_deg (f : HomogeneousLocalization 𝒜 x) : f.num ∈ 𝒜 f.deg :=
  (Quotient.out f).num.2
/-
**HomogeneousLocalization.den_mem_deg** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousLoca
lization`。
形式化陈述：den_mem_deg (f : HomogeneousLocalization 𝒜 x) : f.den in 𝒜 f.deg
参数：f : HomogeneousLocalization 𝒜 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem den_mem_deg (f : HomogeneousLocalization 𝒜 x) : f.den ∈ 𝒜 f.deg :=
  (Quotient.out f).den.2
/-
**HomogeneousLocalization.eq_num_div_den** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousL
ocalization`。
形式化陈述：eq_num_div_den (f : HomogeneousLocalization 𝒜 x) : f.val = Localization.mk
 f.num ⟨f.den, f.den_mem⟩
参数：f : HomogeneousLocalization 𝒜 x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Quotient.out_eq'`：out_eq' (q : Quotient s₁) : Quotient.mk'' q.out = q
-/
theorem eq_num_div_den (f : HomogeneousLocalization 𝒜 x) :
    f.val = Localization.mk f.num ⟨f.den, f.den_mem⟩ :=
  congr_arg HomogeneousLocalization.val (Quotient.out_eq' f).symm
/-
**HomogeneousLocalization.den_smul_val** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousLoc
alization`。
形式化陈述：den_smul_val (f : HomogeneousLocalization 𝒜 x) : f.den • f.val = algebraMa
p _ _ f.num
参数：f : HomogeneousLocalization 𝒜 x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `HomogeneousLocalization.den_mem`：den_mem (f : HomogeneousLocalization 𝒜 
x) : f.den in x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomogeneousLocalization.eq_num_div_den`：eq_num_div_den (f : HomogeneousL
ocalization 𝒜 x) : f.val = Localization.mk f.num ⟨f.den, f.den_mem⟩
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `Localization.mk_eq_mk'`：mk_eq_mk'_apply (x y) : mk x y = IsLocalization.
mk' (Localization M) x y
· 使用定理 `IsLocalization.smul_mk'`：smul_mk' (x y : R) (m : M) : x • mk' S y m = mk
' S (x * y) m
· 使用定理 `IsLocalization.mk'_mul_cancel_left`：∀ {R : Type u_1} [inst : CommSemirin
g R] {M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Alge
bra R S] [inst_3 : IsLoc…
-/
theorem den_smul_val (f : HomogeneousLocalization 𝒜 x) :
    f.den • f.val = algebraMap _ _ f.num := by
  rw [eq_num_div_den, Localization.mk_eq_mk', IsLocalization.smul_mk']
  exact IsLocalization.mk'_mul_cancel_left _ ⟨_, _⟩
/-
**HomogeneousLocalization.ext_iff_val** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousLoca
lization`。
形式化陈述：ext_iff_val (f g : HomogeneousLocalization 𝒜 x) : f = g ↔ f.val = g.val
参数：f g : HomogeneousLocalization 𝒜 x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `HomogeneousLocalization.val_injective`：val_injective : Function.Injectiv
e (HomogeneousLocalization.val (𝒜
-/
theorem ext_iff_val (f g : HomogeneousLocalization 𝒜 x) : f = g ↔ f.val = g.val :=
  ⟨congr_arg val, fun e ↦ val_injective x e⟩

end

section

variable [AddSubgroupClass σ A] {𝒜 : ι → σ} {x : Submonoid A}
variable [AddCommMonoid ι] [DecidableEq ι] [GradedRing 𝒜]
variable (𝒜) (𝔭 : Ideal A) [Ideal.IsPrime 𝔭]

/-- Localizing a ring homogeneously at a prime ideal. -/
/-
**HomogeneousLocalization.AtPrime** 是 Mathlib 中的一个缩写定义，位于命名空间 `HomogeneousLocali
zation`。
形式化陈述：AtPrime
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Localizing a ring homogeneously at a prime ideal.
-/
abbrev AtPrime :=
  HomogeneousLocalization 𝒜 𝔭.primeCompl
/-
**HomogeneousLocalization.isUnit_iff_isUnit_val** 是 Mathlib 中的一个定理，位于命名空间 `Homog
eneousLocalization`。
形式化陈述：isUnit_iff_isUnit_val (f : HomogeneousLocalization.AtPrime 𝒜 𝔭) : IsUnit f
.val ↔ IsUnit f
参数：f : HomogeneousLocalization.AtPrime 𝒜 𝔭。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用引理 `HomogeneousLocalization.mk_surjective`：mk_surjective : Function.Surjecti
ve (mk (𝒜
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.exists_mk'_eq`：∀ {R : Type u_1} [inst : CommSemiring R] (
M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用定理 `HomogeneousLocalization.NumDenSameDeg.den_mem`：∀ {ι : Type u_1} {A : Typ
e u_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A] {𝒜 : ι → σ} {x 
: Submonoid A}   (self : Homogeneou…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.eq_iff_exists`：eq_iff_exists {x y} : algebraMap R S x = a
lgebraMap R S y ↔ exists c : M, ↑c * x = ↑c * y
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `IsLocalization.mk'_eq_iff_eq_mul`：∀ {R : Type u_1} [inst : CommSemiring 
R] {M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebr
a R S] [inst_3 : IsLoc…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalization.mk'_mul`：∀ {R : Type u_1} [inst : CommSemiring R] {M : Su
bmonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [in
st_3 : IsLoc…
· 使用定理 `Localization.mk_eq_mk'`：mk_eq_mk'_apply (x y) : mk x y = IsLocalization.
mk' (Localization M) x y
· 使用定理 `HomogeneousLocalization.val_mk`：val_mk (i : NumDenSameDeg 𝒜 x) : val (mk
 i) = Localization.mk (i.num : A) ⟨i.den, i.den_mem⟩
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Ideal.mul_mem_left`：mul_mem_left : b in I -> a * b in I
· 使用定理 `Ideal.mul_mem_right`：mul_mem_right {α} {a : α} (b : α) [Semiring α] (I :
 Ideal α) [I.IsTwoSided] (h : a in I) : a * b in I
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `IsUnit.of_mul_eq_one`：IsUnit.of_mul_eq_one [Monoid M] [IsDedekindFiniteM
onoid M] {a : M} (b : M) (h : a * b = 1) : IsUnit a
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `HomogeneousLocalization.mk_mul`：∀ {ι : Type u_1} {A : Type u_2} {σ : Typ
e u_3} [inst : CommRing A] [inst_1 : SetLike σ A]   [inst_2 : AddSubgroupClass σ
 A] [inst_3 : AddCom…
· 使用定理 `HomogeneousLocalization.ext_iff_val`：ext_iff_val (f g : HomogeneousLocal
ization 𝒜 x) : f = g ↔ f.val = g.val
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
（共 36 条，此处仅展示前 30 条）
-/
theorem isUnit_iff_isUnit_val (f : HomogeneousLocalization.AtPrime 𝒜 𝔭) :
    IsUnit f.val ↔ IsUnit f := by
  refine ⟨fun h1 ↦ ?_, IsUnit.map (algebraMap _ _)⟩
  rcases h1 with ⟨⟨a, b, eq0, eq1⟩, rfl : a = f.val⟩
  obtain ⟨f, rfl⟩ := mk_surjective f
  obtain ⟨b, s, rfl⟩ := IsLocalization.exists_mk'_eq 𝔭.primeCompl b
  rw [val_mk, Localization.mk_eq_mk', ← IsLocalization.mk'_mul, IsLocalization.mk'_eq_iff_eq_mul,
    one_mul, IsLocalization.eq_iff_exists (M := 𝔭.primeCompl)] at eq0
  obtain ⟨c, hc : _ = c.1 * (f.den.1 * s.1)⟩ := eq0
  have : f.num.1 ∉ 𝔭 := by
    exact fun h ↦ mul_mem c.2 (mul_mem f.den_mem s.2)
      (hc ▸ Ideal.mul_mem_left _ c.1 (Ideal.mul_mem_right b _ h))
  refine .of_mul_eq_one (Quotient.mk'' ⟨f.1, f.3, f.2, this⟩) ?_
  rw [← mk_mul, ext_iff_val, val_mk]
  simp [mul_comm f.den.1]
/-
**HomogeneousLocalization.** 是 Mathlib 中的一个实例，位于命名空间 `HomogeneousLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Nontrivial (HomogeneousLocalization.AtPrime 𝒜 𝔭) :=
  ⟨⟨0, 1, fun r => by simp [ext_iff_val, val_zero, val_one, zero_ne_one] at r⟩⟩
/-
**HomogeneousLocalization.isLocalRing** 是 Mathlib 中的一个实例，位于命名空间 `HomogeneousLoca
lization`。
形式化陈述：isLocalRing : IsLocalRing (HomogeneousLocalization.AtPrime 𝒜 𝔭)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `IsLocalRing.of_isUnit_or_isUnit_one_sub_self`：of_isUnit_or_isUnit_one_su
b_self [Nontrivial R] (h : forall a : R, IsUnit a ∨ IsUnit (1 - a)) : IsLocalRin
g R
· 使用定理 `HomogeneousLocalization.instNontrivialAtPrime`：∀ {ι : Type u_1} {A : Typ
e u_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A]   [inst_2 : Add
SubgroupClass σ A] (𝒜 : ι → σ) [ins…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `HomogeneousLocalization.val_sub`：val_sub (y1 y2 : HomogeneousLocalizatio
n 𝒜 x) : (y1 - y2).val = y1.val - y2.val
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `HomogeneousLocalization.val_one`：val_one : (1 : HomogeneousLocalization 
𝒜 x).val = 1
· 使用定理 `IsLocalRing.isUnit_or_isUnit_one_sub_self`：isUnit_or_isUnit_one_sub_self
 (a : R) : IsUnit a ∨ IsUnit (1 - a)
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
-/
instance isLocalRing : IsLocalRing (HomogeneousLocalization.AtPrime 𝒜 𝔭) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    simpa only [← isUnit_iff_isUnit_val, val_sub, val_one]
      using IsLocalRing.isUnit_or_isUnit_one_sub_self _

end

section

/-- Localizing away from powers of `f` homogeneously. -/
/-
**HomogeneousLocalization.Away** 是 Mathlib 中的一个缩写定义，位于命名空间 `HomogeneousLocalizat
ion`。
形式化陈述：Away (𝒜 : ι -> σ) (f : A)
参数：𝒜 : ι -> σ；f : A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Localizing away from powers of `f` homogeneously.
-/
abbrev Away (𝒜 : ι → σ) (f : A) :=
  HomogeneousLocalization 𝒜 (Submonoid.powers f)

variable [AddSubgroupClass σ A] [AddCommMonoid ι] [DecidableEq ι]
variable (𝒜 : ι → σ) [GradedRing 𝒜] {f : A}

/-- This is a convenient constructor for `Away 𝒜 f` when `f` is homogeneous.
`Away.mk 𝒜 hf n x hx` is the fraction `x / f ^ n`. -/
/-
**HomogeneousLocalization.Away.mk** 是 Mathlib 中的一个定义，位于命名空间 `HomogeneousLocaliza
tion.Away`。
形式化陈述：{ι : Type u_1} →   {A : Type u_2} →     {σ : Type u_3} →       [inst : Com
mRing A] →         [inst_1 : SetLike σ A] →           [inst_2 : AddSubgroupClass
 σ A] →             [inst_3 : AddCommMonoid ι] →               [inst_4 : Decidab
leEq ι] →                 (𝒜 : ι → σ) →                   [GradedRing 𝒜] →      
               {f : A} → {d : ι} → f ∈ 𝒜 d → (n : ℕ) → (x : A) → x ∈ 𝒜 (n • d) →
 HomogeneousLocalization.Away 𝒜 f
参数：𝒜 : ι → σ；n : ℕ；x : A；n • d。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is a convenient constructor for `Away 𝒜 f` when `f` is homogeneous.
`Away.mk 𝒜 hf n x hx` is the fraction `x / f ^ n`.
-/
protected def Away.mk {d : ι} (hf : f ∈ 𝒜 d) (n : ℕ) (x : A) (hx : x ∈ 𝒜 (n • d)) : Away 𝒜 f :=
  HomogeneousLocalization.mk ⟨n • d, ⟨x, hx⟩, ⟨f ^ n, SetLike.pow_mem_graded n hf⟩, ⟨n, rfl⟩⟩

@[simp]
/-
**HomogeneousLocalization.Away.val_mk** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousLoca
lization.Away`。
形式化陈述：∀ {ι : Type u_1} {A : Type u_2} {σ : Type u_3} [inst : CommRing A] [inst_1
 : SetLike σ A]   [inst_2 : AddSubgroupClass σ A] [inst_3 : AddCommMonoid ι] [in
st_4 : DecidableEq ι] (𝒜 : ι → σ)   [inst_5 : GradedRing 𝒜] {f : A} {d : ι} (n :
 ℕ) (hf : f ∈ 𝒜 d) (x : A) (hx : x ∈ 𝒜 (n • d)),   HomogeneousLocalization.val (
HomogeneousLocalization.Away.mk 𝒜 hf n x hx) = Localization.mk x ⟨f ^ n, ⋯⟩
参数：𝒜 : ι → σ；n : ℕ；hf : f ∈ 𝒜 d；x : A；hx : x ∈ 𝒜 (n • d)；HomogeneousLocalization
.Away.mk 𝒜 hf n x hx。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
-/
lemma Away.val_mk {d : ι} (n : ℕ) (hf : f ∈ 𝒜 d) (x : A) (hx : x ∈ 𝒜 (n • d)) :
    (Away.mk 𝒜 hf n x hx).val = Localization.mk x ⟨f ^ n, by use n⟩ :=
  rfl

protected
/-
**HomogeneousLocalization.Away.mk_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Homogene
ousLocalization.Away`。
形式化陈述：∀ {ι : Type u_1} {A : Type u_2} {σ : Type u_3} [inst : CommRing A] [inst_1
 : SetLike σ A]   [inst_2 : AddSubgroupClass σ A] [inst_3 : AddCommMonoid ι] [in
st_4 : DecidableEq ι] (𝒜 : ι → σ)   [inst_5 : GradedRing 𝒜] {f : A} {d : ι} (hf 
: f ∈ 𝒜 d) (x : HomogeneousLocalization.Away 𝒜 f),   ∃ n a, ∃ (ha : a ∈ 𝒜 (n • d
)), HomogeneousLocalization.Away.mk 𝒜 hf n a ha = x
参数：𝒜 : ι → σ；hf : f ∈ 𝒜 d；x : HomogeneousLocalization.Away 𝒜 f；ha : a ∈ 𝒜 (n • d
)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用引理 `HomogeneousLocalization.mk_surjective`：mk_surjective : Function.Surjecti
ve (mk (𝒜
· 使用引理 `HomogeneousLocalization.subsingleton`：subsingleton (hx : 0 in x) : Subsi
ngleton (HomogeneousLocalization 𝒜 x)
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `HomogeneousLocalization.val_injective`：val_injective : Function.Injectiv
e (HomogeneousLocalization.val (𝒜
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DirectSum.degree_eq_of_mem_mem`：degree_eq_of_mem_mem {x : M} {i j : ι} (
hxi : x in ℳ i) (hxj : x in ℳ j) (hx : x != 0) : i = j
· 使用定理 `SetLike.pow_mem_graded`：pow_mem_graded (n : Nat) {r : R} {i : ι} (h : r 
in A i) : r ^ n in A (n • i)
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
-/
lemma Away.mk_surjective {d : ι} (hf : f ∈ 𝒜 d) (x : Away 𝒜 f) :
    ∃ n a ha, Away.mk 𝒜 hf n a ha = x := by
  obtain ⟨⟨N, ⟨s, hs⟩, ⟨b, hn⟩, ⟨n, (rfl : _ = b)⟩⟩, rfl⟩ := mk_surjective x
  by_cases hfn : f ^ n = 0
  · have := HomogeneousLocalization.subsingleton 𝒜 (x := .powers f) ⟨n, hfn⟩
    exact ⟨0, 0, zero_mem _, Subsingleton.elim _ _⟩
  obtain rfl := DirectSum.degree_eq_of_mem_mem 𝒜 hn (SetLike.pow_mem_graded n hf) hfn
  exact ⟨n, s, hs, by ext; simp⟩

variable {𝒜}
/-
**HomogeneousLocalization.Away.eventually_smul_mem** 是 Mathlib 中的一个定理，位于命名空间 `Ho
mogeneousLocalization.Away`。
形式化陈述：∀ {ι : Type u_1} {A : Type u_2} {σ : Type u_3} [inst : CommRing A] [inst_1
 : SetLike σ A]   [inst_2 : AddSubgroupClass σ A] [inst_3 : AddCommMonoid ι] [in
st_4 : DecidableEq ι] {𝒜 : ι → σ} [GradedRing 𝒜] {f : A}   {m : ι},   f ∈ 𝒜 m → 
    ∀ (z : HomogeneousLocalization.Away 𝒜 f),       ∀ᶠ (n : ℕ) in Filter.atTop, 
        f ^ n • HomogeneousLocalization.val z ∈ ⇑(algebraMap A (Localization (Su
bmonoid.powers f))) '' ↑(𝒜 (n • m))
参数：z : HomogeneousLocalization.Away 𝒜 f；n : ℕ；algebraMap A (Localization (Submon
oid.powers f))；𝒜 (n • m)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `HomogeneousLocalization.den_mem`：den_mem (f : HomogeneousLocalization 𝒜 
x) : f.den in x
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Filter.Ici_mem_atTop`：Ici_mem_atTop [Preorder α] (a : α) : Ici a in (atT
op : Filter α)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `HomogeneousLocalization.den_smul_val`：den_smul_val (f : HomogeneousLocal
ization 𝒜 x) : f.den • f.val = algebraMap _ _ f.num
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `DirectSum.degree_eq_of_mem_mem`：degree_eq_of_mem_mem {x : M} {i j : ι} (
hxi : x in ℳ i) (hxj : x in ℳ j) (hx : x != 0) : i = j
（共 36 条，此处仅展示前 30 条）
-/
theorem Away.eventually_smul_mem {m} (hf : f ∈ 𝒜 m) (z : Away 𝒜 f) :
    ∀ᶠ n in Filter.atTop, f ^ n • z.val ∈ algebraMap _ _ '' (𝒜 (n • m) : Set A) := by
  obtain ⟨k, hk : f ^ k = _⟩ := z.den_mem
  apply Filter.mem_of_superset (Filter.Ici_mem_atTop k)
  rintro k' (hk' : k ≤ k')
  simp only [Set.mem_image, SetLike.mem_coe, Set.mem_ofPred_eq]
  by_cases hfk : f ^ k = 0
  · refine ⟨0, zero_mem _, ?_⟩
    rw [← tsub_add_cancel_of_le hk', map_zero, pow_add, hfk, mul_zero, zero_smul]
  rw [← tsub_add_cancel_of_le hk', pow_add, mul_smul, hk, den_smul_val,
    Algebra.smul_def, ← map_mul]
  rw [← smul_eq_mul, add_smul,
    DirectSum.degree_eq_of_mem_mem 𝒜 (SetLike.pow_mem_graded _ hf) (hk.symm ▸ z.den_mem_deg) hfk]
  exact ⟨_, SetLike.mul_mem_graded (SetLike.pow_mem_graded _ hf) z.num_mem_deg, rfl⟩

end

section

variable [AddSubgroupClass σ A] [AddCommMonoid ι] [DecidableEq ι]
variable {𝒜 : ι → σ} [GradedRing 𝒜]
variable {B τ : Type*} [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
variable {ℬ : ι → τ} [GradedRing ℬ]
variable {C ψ : Type*} [CommRing C] [SetLike ψ C] [AddSubgroupClass ψ C]
variable {𝒞 : ι → ψ} [GradedRing 𝒞]
variable {P : Submonoid A} {Q : Submonoid B}

open Graded

/-- Map `NumDenSameDeg` along a graded ring hom. -/
/-
**HomogeneousLocalization.NumDenSameDeg.map** 是 Mathlib 中的一个定义，位于命名空间 `Homogeneo
usLocalization.NumDenSameDeg`。
形式化陈述：{ι : Type u_1} →   {A : Type u_2} →     {σ : Type u_3} →       [inst : Com
mRing A] →         [inst_1 : SetLike σ A] →           [AddSubgroupClass σ A] →  
           {𝒜 : ι → σ} →               {B : Type u_4} →                 {τ : Typ
e u_5} →                   [inst_3 : CommRing B] →                     [inst_4 :
 SetLike τ B] →                       [AddSubgroupClass τ B] →                  
       {ℬ : ι → τ} →                           (f : 𝒜 →+*ᵍ ℬ) →                 
            {W₁ : Submonoid A} →                               {W₂ : Submonoid B
} →                                 W₁ ≤ Submonoid.comap f W₂ →                 
                  HomogeneousLocalization.NumDenSameDeg 𝒜 W₁ →                  
                   HomogeneousLocalization.NumDenSameDeg ℬ W₂
参数：f : 𝒜 →+*ᵍ ℬ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Map `NumDenSameDeg` along a graded ring hom.
-/
@[simps] def NumDenSameDeg.map (f : 𝒜 →+*ᵍ ℬ) {W₁ : Submonoid A} {W₂ : Submonoid B}
    (hw : W₁ ≤ W₂.comap f) (c : NumDenSameDeg 𝒜 W₁) : NumDenSameDeg ℬ W₂ where
  deg := c.deg
  den := f.gradedAddHom _ c.den
  num := f.gradedAddHom _ c.num
  den_mem := hw c.den_mem

set_option backward.isDefEq.respectTransparency.types false in
/--
Let `A, B` be two graded rings with the same indexing set and `g : 𝒜 →+*ᵍ ℬ` be a graded ring
homomorphism. Let `P ≤ A` be a submonoid and `Q ≤ B` be a submonoid such that `P ≤ g⁻¹ Q`, then `g`
induces a map from the homogeneous localization `A⁰_P` to the homogeneous localization `B⁰_Q`.
-/
/-
**HomogeneousLocalization.map** 是 Mathlib 中的一个定义，位于命名空间 `HomogeneousLocalization
`。
形式化陈述：map (g : 𝒜 ->+*ᵍ ℬ) (comap_le : P <= Q.comap g) : HomogeneousLocalization 
𝒜 P ->+* HomogeneousLocalization ℬ Q where toFun
参数：g : 𝒜 ->+*ᵍ ℬ；comap_le : P <= Q.comap g。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.map'`：map'_mk'' (f : α -> β) (h) (x : α) : (Quotient.mk'' x : Q
uotient s₁).map' f h = (Quotient.mk'' (f x) : Quotient s₂)

--- 原说明 ---
Let `A, B` be two graded rings with the same indexing set and `g : 𝒜 →+*ᵍ ℬ` be 
a graded ring
homomorphism. Let `P ≤ A` be a submonoid and `Q ≤ B` be a submonoid such that `P
 ≤ g⁻¹ Q`, then `g`
induces a map from the homogeneous localization `A⁰_P` to the homogeneous locali
zation `B⁰_Q`.
-/
def map (g : 𝒜 →+*ᵍ ℬ) (comap_le : P ≤ Q.comap g) :
    HomogeneousLocalization 𝒜 P →+* HomogeneousLocalization ℬ Q where
  toFun := Quotient.map'
    (fun x ↦ ⟨x.1, ⟨_, map_mem g x.2.2⟩, ⟨_, map_mem g x.3.2⟩, comap_le x.4⟩)
    fun x y (e : x.embedding = y.embedding) ↦ by
      apply_fun IsLocalization.map (Localization Q) g.toRingHom comap_le at e
      simp_rw [HomogeneousLocalization.NumDenSameDeg.embedding, Localization.mk_eq_mk',
        IsLocalization.map_mk', ← Localization.mk_eq_mk'] at e
      exact e
  map_add' := Quotient.ind₂' fun x y ↦ by
    simp only [← mk_add, Quotient.map'_mk'', num_add, map_add, map_mul, den_add]; rfl
  map_mul' := Quotient.ind₂' fun x y ↦ by
    simp only [← mk_mul, Quotient.map'_mk'', num_mul, map_mul, den_mul]; rfl
  map_zero' := by simp only [← mk_zero (𝒜 := 𝒜), Quotient.map'_mk'', deg_zero,
    num_zero, ZeroMemClass.coe_zero, map_zero, den_zero, map_one]; rfl
  map_one' := by simp only [← mk_one (𝒜 := 𝒜), Quotient.map'_mk'',
    num_one, den_one, map_one]; rfl

variable (𝒜) in
/--
Let `A` be a graded ring and `P ≤ Q` be two submonoids, then the homogeneous localization of `A`
at `P` embeds into the homogeneous localization of `A` at `Q`.
-/
/-
**HomogeneousLocalization.mapId** 是 Mathlib 中的一个缩写定义，位于命名空间 `HomogeneousLocaliza
tion`。
形式化陈述：mapId {P Q : Submonoid A} (h : P <= Q) : HomogeneousLocalization 𝒜 P ->+* 
HomogeneousLocalization 𝒜 Q
参数：h : P <= Q。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `A` be a graded ring and `P ≤ Q` be two submonoids, then the homogeneous loc
alization of `A`
at `P` embeds into the homogeneous localization of `A` at `Q`.
-/
abbrev mapId {P Q : Submonoid A} (h : P ≤ Q) :
    HomogeneousLocalization 𝒜 P →+* HomogeneousLocalization 𝒜 Q :=
  map (.id _) h

set_option backward.isDefEq.respectTransparency.types false in
/-
**HomogeneousLocalization.map_mk** 是 Mathlib 中的一个引理，位于命名空间 `HomogeneousLocalizat
ion`。
形式化陈述：map_mk (g : 𝒜 ->+*ᵍ ℬ) (comap_le : P <= Q.comap g) (x) : map g comap_le (m
k x) = mk ⟨x.1, ⟨_, map_mem g x.2.2⟩, ⟨_, map_mem g x.3.2⟩, comap_le x.4⟩
参数：g : 𝒜 ->+*ᵍ ℬ；comap_le : P <= Q.comap g；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `GradedRingHom.instRingHomClass`：∀ {ι : Type u_1} {A : Type u_2} {B : Typ
e u_3} {σ : Type u_6} {τ : Type u_7} [inst : Semiring A] [inst_1 : Semiring B]  
 [inst_2 : SetLike σ…
-/
lemma map_mk (g : 𝒜 →+*ᵍ ℬ) (comap_le : P ≤ Q.comap g) (x) :
    map g comap_le (mk x) = mk ⟨x.1, ⟨_, map_mem g x.2.2⟩, ⟨_, map_mem g x.3.2⟩, comap_le x.4⟩ :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
variable (𝒜) in
/-
**HomogeneousLocalization.map_id** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousLocalizat
ion`。
形式化陈述：∀ {ι : Type u_1} {A : Type u_2} {σ : Type u_3} [inst : CommRing A] [inst_1
 : SetLike σ A]   [inst_2 : AddSubgroupClass σ A] [inst_3 : AddCommMonoid ι] [in
st_4 : DecidableEq ι] (𝒜 : ι → σ)   [inst_5 : GradedRing 𝒜] (P : Submonoid A),  
 HomogeneousLocalization.map (GradedRingHom.id 𝒜) ⋯ = RingHom.id (HomogeneousLoc
alization 𝒜 P)
参数：𝒜 : ι → σ；P : Submonoid A；GradedRingHom.id 𝒜；HomogeneousLocalization 𝒜 P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `HomogeneousLocalization.val_injective`：val_injective : Function.Injectiv
e (HomogeneousLocalization.val (𝒜
· 使用引理 `HomogeneousLocalization.mk_surjective`：mk_surjective : Function.Surjecti
ve (mk (𝒜
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `HomogeneousLocalization.NumDenSameDeg.den_mem`：∀ {ι : Type u_1} {A : Typ
e u_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A] {𝒜 : ι → σ} {x 
: Submonoid A}   (self : Homogeneou…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Graded.map_mem`：Graded.map_mem (f : F) {i x} (h : x in 𝒜 i) : f x in ℬ i
· 使用定理 `GradedRingHom.instGradedFunLike`：∀ {ι : Type u_1} {A : Type u_2} {B : Ty
pe u_3} {σ : Type u_6} {τ : Type u_7} [inst : Semiring A] [inst_1 : Semiring B] 
  [inst_2 : SetLike σ…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomogeneousLocalization.NumDenSameDeg.mk.congr_simp`：∀ {ι : Type u_1} {A
 : Type u_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A] {𝒜 : ι → 
σ} {x : Submonoid A}   (deg : ι) (num num…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem map_id (P : Submonoid A) : map (.id 𝒜) (P := P) (Q := P) le_rfl = .id _ := by
  ext x
  obtain ⟨c, rfl⟩ := x.mk_surjective
  simp [map_mk]
/-
**HomogeneousLocalization.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousLocaliz
ation`。
形式化陈述：map_comp {f : 𝒜 ->+*ᵍ ℬ} {g : ℬ ->+*ᵍ 𝒞} {P : Submonoid A} {Q : Submonoid 
B} {R : Submonoid C} (hpq : P <= Q.comap f) (hqr : Q <= R.comap g) : map (g.comp
 f) (hpq.trans <| Submonoid.monotone_comap hqr) = (map g hqr).comp (map f hpq)
参数：hpq : P <= Q.comap f；hqr : Q <= R.comap g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `GradedRingHom.instRingHomClass`：∀ {ι : Type u_1} {A : Type u_2} {B : Typ
e u_3} {σ : Type u_6} {τ : Type u_7} [inst : Semiring A] [inst_1 : Semiring B]  
 [inst_2 : SetLike σ…
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Submonoid.monotone_comap`：monotone_comap {f : F} : Monotone (comap f)
· 使用定理 `HomogeneousLocalization.val_injective`：val_injective : Function.Injectiv
e (HomogeneousLocalization.val (𝒜
· 使用引理 `HomogeneousLocalization.mk_surjective`：mk_surjective : Function.Surjecti
ve (mk (𝒜
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `HomogeneousLocalization.NumDenSameDeg.den_mem`：∀ {ι : Type u_1} {A : Typ
e u_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A] {𝒜 : ι → σ} {x 
: Submonoid A}   (self : Homogeneou…
· 使用引理 `Graded.map_mem`：Graded.map_mem (f : F) {i x} (h : x in 𝒜 i) : f x in ℬ i
· 使用定理 `GradedRingHom.instGradedFunLike`：∀ {ι : Type u_1} {A : Type u_2} {B : Ty
pe u_3} {σ : Type u_6} {τ : Type u_7} [inst : Semiring A] [inst_1 : Semiring B] 
  [inst_2 : SetLike σ…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_comp {f : 𝒜 →+*ᵍ ℬ} {g : ℬ →+*ᵍ 𝒞}
    {P : Submonoid A} {Q : Submonoid B} {R : Submonoid C}
    (hpq : P ≤ Q.comap f) (hqr : Q ≤ R.comap g) :
    map (g.comp f) (hpq.trans <| Submonoid.monotone_comap hqr) = (map g hqr).comp (map f hpq) := by
  ext x
  obtain ⟨c, rfl⟩ := x.mk_surjective
  simp [map_mk]
/-
**HomogeneousLocalization.map_map** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousLocaliza
tion`。
形式化陈述：map_map {f : 𝒜 ->+*ᵍ ℬ} {g : ℬ ->+*ᵍ 𝒞} {P : Submonoid A} {Q : Submonoid B
} {R : Submonoid C} (hpq : P <= Q.comap f) (hqr : Q <= R.comap g) (x : Homogeneo
usLocalization 𝒜 P) : map g hqr (map f hpq x) = map (g.comp f) (hpq.trans <| Sub
monoid.monotone_comap hqr) x
参数：hpq : P <= Q.comap f；hqr : Q <= R.comap g；x : HomogeneousLocalization 𝒜 P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `GradedRingHom.instRingHomClass`：∀ {ι : Type u_1} {A : Type u_2} {B : Typ
e u_3} {σ : Type u_6} {τ : Type u_7} [inst : Semiring A] [inst_1 : Semiring B]  
 [inst_2 : SetLike σ…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Submonoid.monotone_comap`：monotone_comap {f : F} : Monotone (comap f)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HomogeneousLocalization.map_comp`：map_comp {f : 𝒜 ->+*ᵍ ℬ} {g : ℬ ->+*ᵍ 
𝒞} {P : Submonoid A} {Q : Submonoid B} {R : Submonoid C} (hpq : P <= Q.comap f) 
(hqr : Q <= R.comap g)…
-/
theorem map_map {f : 𝒜 →+*ᵍ ℬ} {g : ℬ →+*ᵍ 𝒞}
    {P : Submonoid A} {Q : Submonoid B} {R : Submonoid C}
    (hpq : P ≤ Q.comap f) (hqr : Q ≤ R.comap g) (x : HomogeneousLocalization 𝒜 P) :
    map g hqr (map f hpq x) = map (g.comp f) (hpq.trans <| Submonoid.monotone_comap hqr) x :=
  congr($(map_comp hpq hqr |>.symm) x)

/-- If `g : 𝒜 →+*ᵍ ℬ` is a graded ring homomorphism and `f : A` then we have a map
`Away 𝒜 f →+* Away ℬ (g f)`. -/
/-
**HomogeneousLocalization.Away.map** 是 Mathlib 中的一个定义，位于命名空间 `HomogeneousLocaliz
ation.Away`。
形式化陈述：{ι : Type u_1} →   {A : Type u_2} →     {σ : Type u_3} →       [inst : Com
mRing A] →         [inst_1 : SetLike σ A] →           [inst_2 : AddSubgroupClass
 σ A] →             [inst_3 : AddCommMonoid ι] →               [inst_4 : Decidab
leEq ι] →                 {𝒜 : ι → σ} →                   [inst_5 : GradedRing 𝒜
] →                     {B : Type u_4} →                       {τ : Type u_5} → 
                        [inst_6 : CommRing B] →                           [inst_
7 : SetLike τ B] →                             [inst_8 : AddSubgroupClass τ B] →
                               {ℬ : ι → τ} →                                 [in
st_9 : GradedRing ℬ] →                                   (g : 𝒜 →+*ᵍ ℬ) →       
                              (f : A) → HomogeneousLocalization.Away 𝒜 f →+* Hom
ogeneousLocalization.Away ℬ (g f)
参数：g : 𝒜 →+*ᵍ ℬ；f : A；g f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `g : 𝒜 →+*ᵍ ℬ` is a graded ring homomorphism and `f : A` then we have a map
`Away 𝒜 f →+* Away ℬ (g f)`.
-/
protected def Away.map (g : 𝒜 →+*ᵍ ℬ) (f : A) : Away 𝒜 f →+* Away ℬ (g f) :=
  map g <| by rintro _ ⟨n, rfl⟩; exact ⟨n, by simp⟩
/-
**HomogeneousLocalization.Away.map_mk** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousLoca
lization.Away`。
形式化陈述：∀ {ι : Type u_1} {A : Type u_2} {σ : Type u_3} [inst : CommRing A] [inst_1
 : SetLike σ A]   [inst_2 : AddSubgroupClass σ A] [inst_3 : AddCommMonoid ι] [in
st_4 : DecidableEq ι] {𝒜 : ι → σ}   [inst_5 : GradedRing 𝒜] {B : Type u_4} {τ : 
Type u_5} [inst_6 : CommRing B] [inst_7 : SetLike τ B]   [inst_8 : AddSubgroupCl
ass τ B] {ℬ : ι → τ} [inst_9 : GradedRing ℬ] {d : ι} (g : 𝒜 →+*ᵍ ℬ) (f : A) (hf 
: f ∈ 𝒜 d)   (n : ℕ) (x : A) (hx : x ∈ 𝒜 (n • d)),   (HomogeneousLocalization.Aw
ay.map g f) (HomogeneousLocalization.Away.mk 𝒜 hf n x hx) =     HomogeneousLocal
ization.Away.mk ℬ ⋯ n (g x) ⋯
参数：g : 𝒜 →+*ᵍ ℬ；f : A；hf : f ∈ 𝒜 d；n : ℕ；x : A；hx : x ∈ 𝒜 (n • d)；HomogeneousLoc
alization.Away.map g f；HomogeneousLocalization.Away.mk 𝒜 hf n x hx；g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Graded.map_mem`：Graded.map_mem (f : F) {i x} (h : x in 𝒜 i) : f x in ℬ i
· 使用定理 `GradedRingHom.instGradedFunLike`：∀ {ι : Type u_1} {A : Type u_2} {B : Ty
pe u_3} {σ : Type u_6} {τ : Type u_7} [inst : Semiring A] [inst_1 : Semiring B] 
  [inst_2 : SetLike σ…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `GradedRingHom.instRingHomClass`：∀ {ι : Type u_1} {A : Type u_2} {B : Typ
e u_3} {σ : Type u_6} {τ : Type u_7} [inst : Semiring A] [inst_1 : Semiring B]  
 [inst_2 : SetLike σ…
· 使用定理 `HomogeneousLocalization.NumDenSameDeg.den_mem`：∀ {ι : Type u_1} {A : Typ
e u_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A] {𝒜 : ι → σ} {x 
: Submonoid A}   (self : Homogeneou…
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomogeneousLocalization.NumDenSameDeg.mk.congr_simp`：∀ {ι : Type u_1} {A
 : Type u_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A] {𝒜 : ι → 
σ} {x : Submonoid A}   (deg : ι) (num num…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma Away.map_mk {d : ι} (g : 𝒜 →+*ᵍ ℬ) (f : A) (hf : f ∈ 𝒜 d) (n : ℕ) (x : A)
    (hx : x ∈ 𝒜 (n • d)) :
    Away.map g f (.mk 𝒜 hf n x hx) = .mk ℬ (map_mem g hf) n (g x) (map_mem g hx) := by
  simp [Away.map, Away.mk, HomogeneousLocalization.map_mk]

variable (𝒜) in
/-
**HomogeneousLocalization.Away.map_id** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousLoca
lization.Away`。
形式化陈述：∀ {ι : Type u_1} {A : Type u_2} {σ : Type u_3} [inst : CommRing A] [inst_1
 : SetLike σ A]   [inst_2 : AddSubgroupClass σ A] [inst_3 : AddCommMonoid ι] [in
st_4 : DecidableEq ι] (𝒜 : ι → σ)   [inst_5 : GradedRing 𝒜] (f : A),   Homogeneo
usLocalization.Away.map (GradedRingHom.id 𝒜) f = RingHom.id (HomogeneousLocaliza
tion.Away 𝒜 f)
参数：𝒜 : ι → σ；f : A；GradedRingHom.id 𝒜；HomogeneousLocalization.Away 𝒜 f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `HomogeneousLocalization.map_id`：∀ {ι : Type u_1} {A : Type u_2} {σ : Typ
e u_3} [inst : CommRing A] [inst_1 : SetLike σ A]   [inst_2 : AddSubgroupClass σ
 A] [inst_3 : AddCom…
-/
@[simp] lemma Away.map_id (f : A) : Away.map (.id 𝒜) f = .id _ :=
  HomogeneousLocalization.map_id ..
/-
**HomogeneousLocalization.Away.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousLo
calization.Away`。
形式化陈述：∀ {ι : Type u_1} {A : Type u_2} {σ : Type u_3} [inst : CommRing A] [inst_1
 : SetLike σ A]   [inst_2 : AddSubgroupClass σ A] [inst_3 : AddCommMonoid ι] [in
st_4 : DecidableEq ι] {𝒜 : ι → σ}   [inst_5 : GradedRing 𝒜] {B : Type u_4} {τ : 
Type u_5} [inst_6 : CommRing B] [inst_7 : SetLike τ B]   [inst_8 : AddSubgroupCl
ass τ B] {ℬ : ι → τ} [inst_9 : GradedRing ℬ] {C : Type u_6} {ψ : Type u_7}   [in
st_10 : CommRing C] [inst_11 : SetLike ψ C] [inst_12 : AddSubgroupClass ψ C] {𝒞 
: ι → ψ} [inst_13 : GradedRing 𝒞]   (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒞) (s : A),   Hom
ogeneousLocalization.Away.map (g.comp f) s =     (HomogeneousLocalization.Away.m
ap g (f s)).comp (HomogeneousLocalization.Away.map f s)
参数：f : 𝒜 →+*ᵍ ℬ；g : ℬ →+*ᵍ 𝒞；s : A；g.comp f；HomogeneousLocalization.Away.map g (
f s)；HomogeneousLocalization.Away.map f s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `HomogeneousLocalization.map_comp`：map_comp {f : 𝒜 ->+*ᵍ ℬ} {g : ℬ ->+*ᵍ 
𝒞} {P : Submonoid A} {Q : Submonoid B} {R : Submonoid C} (hpq : P <= Q.comap f) 
(hqr : Q <= R.comap g)…
-/
@[simp] lemma Away.map_comp (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒞) (s : A) :
    Away.map (g.comp f) s = (Away.map g (f s)).comp (Away.map f s) :=
  HomogeneousLocalization.map_comp ..
/-
**HomogeneousLocalization.Away.map_map** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousLoc
alization.Away`。
形式化陈述：∀ {ι : Type u_1} {A : Type u_2} {σ : Type u_3} [inst : CommRing A] [inst_1
 : SetLike σ A]   [inst_2 : AddSubgroupClass σ A] [inst_3 : AddCommMonoid ι] [in
st_4 : DecidableEq ι] {𝒜 : ι → σ}   [inst_5 : GradedRing 𝒜] {B : Type u_4} {τ : 
Type u_5} [inst_6 : CommRing B] [inst_7 : SetLike τ B]   [inst_8 : AddSubgroupCl
ass τ B] {ℬ : ι → τ} [inst_9 : GradedRing ℬ] {C : Type u_6} {ψ : Type u_7}   [in
st_10 : CommRing C] [inst_11 : SetLike ψ C] [inst_12 : AddSubgroupClass ψ C] {𝒞 
: ι → ψ} [inst_13 : GradedRing 𝒞]   (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒞) (s : A) (x : H
omogeneousLocalization.Away 𝒜 s),   (HomogeneousLocalization.Away.map g (f s)) (
(HomogeneousLocalization.Away.map f s) x) =     (HomogeneousLocalization.Away.ma
p (g.comp f) s) x
参数：f : 𝒜 →+*ᵍ ℬ；g : ℬ →+*ᵍ 𝒞；s : A；x : HomogeneousLocalization.Away 𝒜 s；Homogene
ousLocalization.Away.map g (f s)；(HomogeneousLocalization.Away.map f s) x；Homoge
neousLocalization.Away.map (g.comp f) s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `HomogeneousLocalization.map_map`：map_map {f : 𝒜 ->+*ᵍ ℬ} {g : ℬ ->+*ᵍ 𝒞}
 {P : Submonoid A} {Q : Submonoid B} {R : Submonoid C} (hpq : P <= Q.comap f) (h
qr : Q <= R.comap g) …
-/
theorem Away.map_map (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒞) (s : A) (x : Away 𝒜 s) :
    Away.map g (f s) (Away.map f s x) = Away.map (g.comp f) s x :=
  HomogeneousLocalization.map_map ..

section AtPrime

variable (f : 𝒜 →+*ᵍ ℬ) (I : Ideal A) [I.IsPrime] (J : Ideal B) [J.IsPrime] (hIJ : I = J.comap f)

-- NB: this is to be consistent with `Localization.localRingHom`. We might change both to
-- `AtPrime.map` one day.
/-- If `f : 𝒜 →+*ᵍ ℬ` is a graded ring homomorphism and `I` is a prime ideal of `A` and
`J` is a prime ideal of `B` and `f⁻¹ J = I` then we have a map `AtPrime 𝒜 I →+* AtPrime ℬ J`. -/
/-
**HomogeneousLocalization.localRingHom** 是 Mathlib 中的一个定义，位于命名空间 `HomogeneousLoc
alization`。
形式化陈述：localRingHom : AtPrime 𝒜 I ->+* AtPrime ℬ J
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f : 𝒜 →+*ᵍ ℬ` is a graded ring homomorphism and `I` is a prime ideal of `A` 
and
`J` is a prime ideal of `B` and `f⁻¹ J = I` then we have a map `AtPrime 𝒜 I →+* 
AtPrime ℬ J`.
-/
noncomputable def localRingHom : AtPrime 𝒜 I →+* AtPrime ℬ J :=
  map f <| Localization.le_comap_primeCompl_iff.mpr <| hIJ ▸ le_rfl

variable {f I J hIJ}

set_option backward.isDefEq.respectTransparency.types false in
/-
**HomogeneousLocalization.val_localRingHom** 是 Mathlib 中的一个定理，位于命名空间 `Homogeneou
sLocalization`。
形式化陈述：∀ {ι : Type u_1} {A : Type u_2} {σ : Type u_3} [inst : CommRing A] [inst_1
 : SetLike σ A]   [inst_2 : AddSubgroupClass σ A] [inst_3 : AddCommMonoid ι] [in
st_4 : DecidableEq ι] {𝒜 : ι → σ}   [inst_5 : GradedRing 𝒜] {B : Type u_4} {τ : 
Type u_5} [inst_6 : CommRing B] [inst_7 : SetLike τ B]   [inst_8 : AddSubgroupCl
ass τ B] {ℬ : ι → τ} [inst_9 : GradedRing ℬ] {f : 𝒜 →+*ᵍ ℬ} {I : Ideal A} [inst_
10 : I.IsPrime]   {J : Ideal B} [inst_11 : J.IsPrime] {hIJ : I = Ideal.comap f J
} (x : HomogeneousLocalization.AtPrime 𝒜 I),   HomogeneousLocalization.val ((Hom
ogeneousLocalization.localRingHom f I J hIJ) x) =     (Localization.localRingHom
 I J (↑f) hIJ) (HomogeneousLocalization.val x)
参数：x : HomogeneousLocalization.AtPrime 𝒜 I；(HomogeneousLocalization.localRingHom
 f I J hIJ) x；Localization.localRingHom I J (↑f) hIJ；HomogeneousLocalization.val
 x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `GradedRingHom.instRingHomClass`：∀ {ι : Type u_1} {A : Type u_2} {B : Typ
e u_3} {σ : Type u_6} {τ : Type u_7} [inst : Semiring A] [inst_1 : Semiring B]  
 [inst_2 : SetLike σ…
· 使用引理 `HomogeneousLocalization.mk_surjective`：mk_surjective : Function.Surjecti
ve (mk (𝒜
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `HomogeneousLocalization.NumDenSameDeg.den_mem`：∀ {ι : Type u_1} {A : Typ
e u_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A] {𝒜 : ι → σ} {x 
: Submonoid A}   (self : Homogeneou…
· 使用引理 `Graded.map_mem`：Graded.map_mem (f : F) {i x} (h : x in 𝒜 i) : f x in ℬ i
· 使用定理 `GradedRingHom.instGradedFunLike`：∀ {ι : Type u_1} {A : Type u_2} {B : Ty
pe u_3} {σ : Type u_6} {τ : Type u_7} [inst : Semiring A] [inst_1 : Semiring B] 
  [inst_2 : SetLike σ…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Localization.localRingHom_mk`：localRingHom_mk (J : Ideal P) [J.IsPrime] 
(f : R ->+* P) (hIJ : I = J.comap f) (x : R) (y : I.primeCompl) : localRingHom I
 J f hIJ (mk x y) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma val_localRingHom (x : AtPrime 𝒜 I) :
    (localRingHom f I J hIJ x).val = Localization.localRingHom _ _ f hIJ x.val := by
  obtain ⟨⟨i, x, s, hs⟩, rfl⟩ := x.mk_surjective
  simp [localRingHom, map_mk]

set_option backward.isDefEq.respectTransparency.types false in
/-
**HomogeneousLocalization.** 是 Mathlib 中的一个实例，位于命名空间 `HomogeneousLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
variable (𝒜 : ι → σ) [GradedRing 𝒜]
variable {e : ι} {f : A} {g : A} (hg : g ∈ 𝒜 e) {x : A} (hx : x = f * g)

set_option backward.privateInPublic true in
/-- Given `f ∣ x`, this is the map `A_{(f)} → A_f → A_x`. We will lift this to a map
`A_{(f)} → A_{(x)}` in `awayMap`. -/
/-
**HomogeneousLocalization.awayMapAux** 是 Mathlib 中的一个定义，位于命名空间 `HomogeneousLocal
ization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `f ∣ x`, this is the map `A_{(f)} → A_f → A_x`. We will lift this to a map
`A_{(f)} → A_{(x)}` in `awayMap`.
-/
private def awayMapAux (hx : f ∣ x) : Away 𝒜 f →+* Localization.Away x :=
  (Localization.awayLift (algebraMap A _) _
    (isUnit_of_dvd_unit (map_dvd _ hx) (IsLocalization.Away.algebraMap_isUnit x))).comp
      (algebraMap (Away 𝒜 f) (Localization.Away f))

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**HomogeneousLocalization.awayMapAux_mk** 是 Mathlib 中的一个引理，位于命名空间 `HomogeneousLo
calization`。
形式化陈述：awayMapAux_mk (n a i hi) : awayMapAux 𝒜 ⟨_, hx⟩ (mk ⟨n, a, ⟨f ^ i, hi⟩, ⟨i
, rfl⟩⟩) = Localization.mk (a * g ^ i) ⟨x ^ i, (Submonoid.mem_powers_iff _ _).mp
r ⟨i, rfl⟩⟩
参数：n a i hi。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submonoid.mem_powers_iff`：mem_powers_iff (x z : M) : x in powers z ↔ exi
sts n : Nat, z ^ n = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Localization.smul_mk`：smul_mk [SMul R M] [IsScalarTower R M M] (c : R) (
a b) : c • (mk a b : Localization S) = mk (c • a) b
· 使用定理 `Localization.mk_self`：mk_self (a : S) : mk (a : M) a = 1
· 使用定理 `HomogeneousLocalization.NumDenSameDeg.den_mem`：∀ {ι : Type u_1} {A : Typ
e u_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A] {𝒜 : ι → σ} {x 
: Submonoid A}   (self : Homogeneou…
· 使用定理 `isUnit_iff_exists_inv`：isUnit_iff_exists_inv [Monoid M] [IsDedekindFinit
eMonoid M] {a : M} : IsUnit a ↔ exists b, a * b = 1
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用引理 `Localization.awayLift_mk`：awayLift_mk {A : Type*} [CommSemiring A] (f : 
R ->+* A) (r : R) (a : R) (v : A) (hv : f r * v = 1) (j : Nat) : Localization.aw
ayLift f r (is…
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `Localization.mk_pow`：mk_pow (n : Nat) (a : M) (b : S) : mk a b ^ n = mk 
(a ^ n) (b ^ n)
-/
lemma awayMapAux_mk (n a i hi) :
    awayMapAux 𝒜 ⟨_, hx⟩ (mk ⟨n, a, ⟨f ^ i, hi⟩, ⟨i, rfl⟩⟩) =
      Localization.mk (a * g ^ i) ⟨x ^ i, (Submonoid.mem_powers_iff _ _).mpr ⟨i, rfl⟩⟩ := by
  have : algebraMap A (Localization.Away x) f *
    (Localization.mk g ⟨f * g, (Submonoid.mem_powers_iff _ _).mpr ⟨1, by simp [hx]⟩⟩) = 1 := by
    rw [← Algebra.smul_def, Localization.smul_mk]
    exact Localization.mk_self ⟨f*g, _⟩
  simp only [awayMapAux, RingHom.coe_comp, Function.comp_apply, algebraMap_apply, val_mk]
  rw [Localization.awayLift_mk (hv := this), ← Algebra.smul_def,
    Localization.mk_pow, Localization.smul_mk]
  subst hx
  rfl

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
include hg in
/-
**HomogeneousLocalization.range_awayMapAux_subset** 是 Mathlib 中的一个引理，位于命名空间 `Hom
ogeneousLocalization`。
形式化陈述：range_awayMapAux_subset : Set.range (awayMapAux 𝒜 (f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用引理 `HomogeneousLocalization.mk_surjective`：mk_surjective : Function.Surjecti
ve (mk (𝒜
· 使用定理 `SetLike.mul_mem_graded`：SetLike.mul_mem_graded {S : Type*} [SetLike S R]
 [Mul R] [Add ι] {A : ι -> S} [SetLike.GradedMul A] ⦃i j⦄ {gi gj} (hi : gi in A 
i) (hj : gj …
· 使用定理 `SetLike.GradedMonoid.toGradedMul`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
· 使用定理 `SetLike.pow_mem_graded`：pow_mem_graded (n : Nat) {r : R} {i : ι} (h : r 
in A i) : r ^ n in A (n • i)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `HomogeneousLocalization.NumDenSameDeg.den_mem`：∀ {ι : Type u_1} {A : Typ
e u_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A] {𝒜 : ι → σ} {x 
: Submonoid A}   (self : Homogeneou…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submonoid.mem_powers_iff`：mem_powers_iff (x z : M) : x in powers z ↔ exi
sts n : Nat, z ^ n = x
· 使用引理 `HomogeneousLocalization.awayMapAux_mk`：awayMapAux_mk (n a i hi) : awayMa
pAux 𝒜 ⟨_, hx⟩ (mk ⟨n, a, ⟨f ^ i, hi⟩, ⟨i, rfl⟩⟩) = Localization.mk (a * g ^ i) 
⟨x ^ i, (Submonoid.mem_powe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma range_awayMapAux_subset :
    Set.range (awayMapAux 𝒜 (f := f) ⟨_, hx⟩) ⊆ Set.range (val (𝒜 := 𝒜)) := by
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
/-- Given `x = f * g` with `g` homogeneous of positive degree,
this is the map `A_{(f)} → A_{(x)}` taking `a/f^i` to `ag^i/(fg)^i`. -/
/-
**HomogeneousLocalization.awayMap** 是 Mathlib 中的一个定义，位于命名空间 `HomogeneousLocaliza
tion`。
形式化陈述：awayMap : Away 𝒜 f ->+* Away 𝒜 x
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `HomogeneousLocalization.range_awayMapAux_subset`：range_awayMapAux_subset
 : Set.range (awayMapAux 𝒜 (f

--- 原说明 ---
Given `x = f * g` with `g` homogeneous of positive degree,
this is the map `A_{(f)} → A_{(x)}` taking `a/f^i` to `ag^i/(fg)^i`.
-/
def awayMap : Away 𝒜 f →+* Away 𝒜 x := by
  let e := RingEquiv.ofLeftInverse (f := algebraMap (Away 𝒜 x) (Localization.Away x))
    (h := (val_injective _).hasLeftInverse.choose_spec)
  refine RingHom.comp (e.symm.toRingHom.comp (Subring.inclusion ?_))
    (awayMapAux 𝒜 (f := f) ⟨_, hx⟩).rangeRestrict
  exact range_awayMapAux_subset 𝒜 hg hx

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**HomogeneousLocalization.val_awayMap_eq_aux** 是 Mathlib 中的一个引理，位于命名空间 `Homogene
ousLocalization`。
形式化陈述：val_awayMap_eq_aux (a) : (awayMap 𝒜 hg hx a).val = awayMapAux 𝒜 ⟨_, hx⟩ a
参数：a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `Function.Injective.hasLeftInverse`：∀ {α : Sort u_1} {β : Sort u_2} [None
mpty α] {f : α → β}, Function.Injective f → Function.HasLeftInverse f
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `HomogeneousLocalization.val_injective`：val_injective : Function.Injectiv
e (HomogeneousLocalization.val (𝒜
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用引理 `HomogeneousLocalization.range_awayMapAux_subset`：range_awayMapAux_subset
 : Set.range (awayMapAux 𝒜 (f
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingEquiv.apply_symm_apply`：apply_symm_apply (e : R ≃+* S) : forall x, e
 (e.symm x) = x
-/
lemma val_awayMap_eq_aux (a) : (awayMap 𝒜 hg hx a).val = awayMapAux 𝒜 ⟨_, hx⟩ a := by
  let e := RingEquiv.ofLeftInverse (f := algebraMap (Away 𝒜 x) (Localization.Away x))
    (h := (val_injective _).hasLeftInverse.choose_spec)
  dsimp [awayMap]
  convert_to! (e (e.symm ⟨awayMapAux 𝒜 (f := f) ⟨_, hx⟩ a,
    range_awayMapAux_subset 𝒜 hg hx ⟨_, rfl⟩⟩)).1 = _
  rw [e.apply_symm_apply]
/-
**HomogeneousLocalization.val_awayMap** 是 Mathlib 中的一个引理，位于命名空间 `HomogeneousLoca
lization`。
形式化陈述：val_awayMap (a) : (awayMap 𝒜 hg hx a).val = Localization.awayLift (algebra
Map A _) _ (isUnit_of_dvd_unit (map_dvd _ ⟨_, hx⟩) (IsLocalization.Away.algebraM
ap_isUnit x)) a.val
参数：a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `isUnit_of_dvd_unit`：isUnit_of_dvd_unit {x y : α} (xy : x ∣ y) (hu : IsUn
it y) : IsUnit x
· 使用定理 `map_dvd`：∀ {M : Type u_1} {N : Type u_2} [inst : Semigroup M] [inst_1 : 
Semigroup N] {F : Type u_3} [inst_2 : FunLike F M N]   [MulHomClass F M N] (f…
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用引理 `IsLocalization.Away.algebraMap_isUnit`：algebraMap_isUnit : IsUnit (algeb
raMap R S x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomogeneousLocalization.val_awayMap_eq_aux`：val_awayMap_eq_aux (a) : (aw
ayMap 𝒜 hg hx a).val = awayMapAux 𝒜 ⟨_, hx⟩ a
-/
lemma val_awayMap (a) : (awayMap 𝒜 hg hx a).val = Localization.awayLift (algebraMap A _) _
    (isUnit_of_dvd_unit (map_dvd _ ⟨_, hx⟩) (IsLocalization.Away.algebraMap_isUnit x)) a.val := by
  rw [val_awayMap_eq_aux]
  rfl
/-
**HomogeneousLocalization.awayMap_fromZeroRingHom** 是 Mathlib 中的一个引理，位于命名空间 `Hom
ogeneousLocalization`。
形式化陈述：awayMap_fromZeroRingHom (a) : awayMap 𝒜 hg hx (fromZeroRingHom 𝒜 _ a) = fr
omZeroRingHom 𝒜 _ a
参数：a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `HomogeneousLocalization.val_injective`：val_injective : Function.Injectiv
e (HomogeneousLocalization.val (𝒜
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
· 使用定理 `isUnit_of_dvd_unit`：isUnit_of_dvd_unit {x y : α} (xy : x ∣ y) (hu : IsUn
it y) : IsUnit x
· 使用定理 `map_dvd`：∀ {M : Type u_1} {N : Type u_2} [inst : Semigroup M] [inst_1 : 
Semigroup N] {F : Type u_3} [inst_2 : FunLike F M N]   [MulHomClass F M N] (f…
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用引理 `IsLocalization.Away.algebraMap_isUnit`：algebraMap_isUnit : IsUnit (algeb
raMap R S x)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomogeneousLocalization.val_awayMap`：val_awayMap (a) : (awayMap 𝒜 hg hx 
a).val = Localization.awayLift (algebraMap A _) _ (isUnit_of_dvd_unit (map_dvd _
 ⟨_, hx⟩) (IsLocalization…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `IsLocalization.lift_eq`：lift_eq (x : R) : lift hg ((algebraMap R S) x) =
 g x
-/
lemma awayMap_fromZeroRingHom (a) :
    awayMap 𝒜 hg hx (fromZeroRingHom 𝒜 _ a) = fromZeroRingHom 𝒜 _ a := by
  ext
  simp only [fromZeroRingHom, val_awayMap]
  convert! IsLocalization.lift_eq _ _
/-
**HomogeneousLocalization.val_awayMap_mk** 是 Mathlib 中的一个引理，位于命名空间 `HomogeneousL
ocalization`。
形式化陈述：val_awayMap_mk (n a i hi) : (awayMap 𝒜 hg hx (mk ⟨n, a, ⟨f ^ i, hi⟩, ⟨i, r
fl⟩⟩)).val = Localization.mk (a * g ^ i) ⟨x ^ i, (Submonoid.mem_powers_iff _ _).
mpr ⟨i, rfl⟩⟩
参数：n a i hi。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submonoid.mem_powers_iff`：mem_powers_iff (x z : M) : x in powers z ↔ exi
sts n : Nat, z ^ n = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomogeneousLocalization.val_awayMap_eq_aux`：val_awayMap_eq_aux (a) : (aw
ayMap 𝒜 hg hx a).val = awayMapAux 𝒜 ⟨_, hx⟩ a
· 使用引理 `HomogeneousLocalization.awayMapAux_mk`：awayMapAux_mk (n a i hi) : awayMa
pAux 𝒜 ⟨_, hx⟩ (mk ⟨n, a, ⟨f ^ i, hi⟩, ⟨i, rfl⟩⟩) = Localization.mk (a * g ^ i) 
⟨x ^ i, (Submonoid.mem_powe…
-/
lemma val_awayMap_mk (n a i hi) : (awayMap 𝒜 hg hx (mk ⟨n, a, ⟨f ^ i, hi⟩, ⟨i, rfl⟩⟩)).val =
    Localization.mk (a * g ^ i) ⟨x ^ i, (Submonoid.mem_powers_iff _ _).mpr ⟨i, rfl⟩⟩ := by
  rw [val_awayMap_eq_aux, awayMapAux_mk 𝒜 (hx := hx)]

/-- Given `x = f * g` with `g` homogeneous of positive degree,
this is the map `A_{(f)} → A_{(x)}` taking `a/f^i` to `ag^i/(fg)^i`. -/
/-
**HomogeneousLocalization.awayMap** 是 Mathlib 中的一个定义，位于命名空间 `HomogeneousLocaliza
tion`。
形式化陈述：awayMap : Away 𝒜 f ->+* Away 𝒜 x
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `HomogeneousLocalization.range_awayMapAux_subset`：range_awayMapAux_subset
 : Set.range (awayMapAux 𝒜 (f

--- 原说明 ---
Given `x = f * g` with `g` homogeneous of positive degree,
this is the map `A_{(f)} → A_{(x)}` taking `a/f^i` to `ag^i/(fg)^i`.
-/
def awayMapₐ : Away 𝒜 f →ₐ[𝒜 0] Away 𝒜 x where
  __ := awayMap 𝒜 hg hx
  commutes' _ := awayMap_fromZeroRingHom ..
/-
**HomogeneousLocalization.awayMap** 是 Mathlib 中的一个定义，位于命名空间 `HomogeneousLocaliza
tion`。
形式化陈述：awayMap : Away 𝒜 f ->+* Away 𝒜 x
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `HomogeneousLocalization.range_awayMapAux_subset`：range_awayMapAux_subset
 : Set.range (awayMapAux 𝒜 (f
-/
@[simp] lemma awayMapₐ_apply (a) : awayMapₐ 𝒜 hg hx a = awayMap 𝒜 hg hx a := rfl

open SetLike in
@[simp]
/-
**HomogeneousLocalization.awayMap_mk** 是 Mathlib 中的一个引理，位于命名空间 `HomogeneousLocal
ization`。
形式化陈述：awayMap_mk {d : ι} (n : Nat) (hf : f in 𝒜 d) (a : A) (ha : a in 𝒜 (n • d))
 : awayMap 𝒜 hg hx (Away.mk 𝒜 hf n a ha) = Away.mk 𝒜 (hx ▸ mul_mem_graded hf hg)
 n (a * g ^ n) (by rw [smul_add]; exact mul_mem_graded ha (pow_mem_graded n hg))
参数：n : Nat；hf : f in 𝒜 d；a : A；ha : a in 𝒜 (n • d)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `HomogeneousLocalization.val_injective`：val_injective : Function.Injectiv
e (HomogeneousLocalization.val (𝒜
· 使用定理 `SetLike.mul_mem_graded`：SetLike.mul_mem_graded {S : Type*} [SetLike S R]
 [Mul R] [Add ι] {A : ι -> S} [SetLike.GradedMul A] ⦃i j⦄ {gi gj} (hi : gi in A 
i) (hj : gj …
· 使用定理 `SetLike.GradedMonoid.toGradedMul`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `HomogeneousLocalization.val_awayMap_mk`：val_awayMap_mk (n a i hi) : (awa
yMap 𝒜 hg hx (mk ⟨n, a, ⟨f ^ i, hi⟩, ⟨i, rfl⟩⟩)).val = Localization.mk (a * g ^ 
i) ⟨x ^ i, (Submonoid.mem_po…
-/
lemma awayMap_mk {d : ι} (n : ℕ) (hf : f ∈ 𝒜 d) (a : A) (ha : a ∈ 𝒜 (n • d)) :
    awayMap 𝒜 hg hx (Away.mk 𝒜 hf n a ha) = Away.mk 𝒜 (hx ▸ mul_mem_graded hf hg) n
      (a * g ^ n) (by rw [smul_add]; exact mul_mem_graded ha (pow_mem_graded n hg)) := by
  ext
  exact val_awayMap_mk ..

end mapAway

section isLocalization

variable [AddSubgroupClass σ A] {𝒜 : ℕ → σ} [GradedRing 𝒜]
variable {e d : ℕ} {f : A} (hf : f ∈ 𝒜 d) {g : A} (hg : g ∈ 𝒜 e)

/-- The element `t := g ^ d / f ^ e` such that `A_{(fg)} = A_{(f)}[1/t]`. -/
/-
**HomogeneousLocalization.Away.isLocalizationElem** 是 Mathlib 中的一个定义，位于命名空间 `Hom
ogeneousLocalization.Away`。
形式化陈述：{A : Type u_2} →   {σ : Type u_3} →     [inst : CommRing A] →       [inst_
1 : SetLike σ A] →         [inst_2 : AddSubgroupClass σ A] →           {𝒜 : ℕ → 
σ} →             [GradedRing 𝒜] → {e d : ℕ} → {f : A} → f ∈ 𝒜 d → {g : A} → g ∈ 
𝒜 e → HomogeneousLocalization.Away 𝒜 f
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The element `t := g ^ d / f ^ e` such that `A_{(fg)} = A_{(f)}[1/t]`.
-/
abbrev Away.isLocalizationElem : Away 𝒜 f :=
  Away.mk 𝒜 hf e (g ^ d) (by convert! SetLike.pow_mem_graded d hg using 2; exact mul_comm _ _)

variable {x : A} (hx : x = f * g)

/-- Let `t := g ^ d / f ^ e`, then `A_{(fg)} = A_{(f)}[1/t]`. -/
/-
**HomogeneousLocalization.Away.isLocalization_mul** 是 Mathlib 中的一个定理，位于命名空间 `Hom
ogeneousLocalization.Away`。
形式化陈述：∀ {A : Type u_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A]
 [inst_2 : AddSubgroupClass σ A] {𝒜 : ℕ → σ}   [inst_3 : GradedRing 𝒜] {e d : ℕ}
 {f : A} (hf : f ∈ 𝒜 d) {g : A} (hg : g ∈ 𝒜 e) {x : A} (hx : x = f * g),   d ≠ 0
 → IsLocalization.Away (HomogeneousLocalization.Away.isLocalizationElem hf hg) (
HomogeneousLocalization.Away 𝒜 x)
参数：hf : f ∈ 𝒜 d；hg : g ∈ 𝒜 e；hx : x = f * g；HomogeneousLocalization.Away.isLocal
izationElem hf hg；HomogeneousLocalization.Away 𝒜 x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `RingHom.algebraMap_toAlgebra`：RingHom.algebraMap_toAlgebra {R S} [CommSe
miring R] [CommSemiring S] (i : R ->+* S) : @algebraMap R S _ _ i.toAlgebra = i
· 使用定理 `SetLike.mul_mem_graded`：SetLike.mul_mem_graded {S : Type*} [SetLike S R]
 [Mul R] [Add ι] {A : ι -> S} [SetLike.GradedMul A] ⦃i j⦄ {gi gj} (hi : gi in A 
i) (hj : gj …
· 使用定理 `SetLike.GradedMonoid.toGradedMul`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.smul_congr`：∀ {R : Type u_2} {α : Type u_3} [
inst : CommSemiring α] [inst_1 : SMul R α] {r : R} {a b t c : α},   a = b → (∀ (
x : α), r • x = t * x) → t …
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.smul_eq_mul`：∀ {α : Type u_2} [inst : Mul α] {a a' :
 α}, a = a' → ∀ (b : α), a • b = a' * b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pp_pf_overlap`：∀ {R : Type u_1} [inst : C
ommSemiring R] {a₂ b₂ c : R} {ea eb e : ℕ} (x : R),   ea + eb = e → a₂ * b₂ = c 
→ x ^ ea * a₂ * (x ^ eb * b₂) = x …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
（共 70 条，此处仅展示前 30 条）

--- 原说明 ---
Let `t := g ^ d / f ^ e`, then `A_{(fg)} = A_{(f)}[1/t]`.
-/
theorem Away.isLocalization_mul (hd : d ≠ 0) :
    letI := (awayMap 𝒜 hg hx).toAlgebra
    IsLocalization.Away (isLocalizationElem hf hg) (Away 𝒜 x) := by
  let := (awayMap 𝒜 hg hx).toAlgebra
  constructor; constructor
  · rintro ⟨r, n, rfl⟩
    rw [map_pow, RingHom.algebraMap_toAlgebra]
    let z : Away 𝒜 x := Away.mk 𝒜 (hx ▸ SetLike.mul_mem_graded hf hg) (d + e)
        (g ^ e * f ^ (2 * e + d)) <| by
      convert!
        SetLike.mul_mem_graded (SetLike.pow_mem_graded e hg)
          (SetLike.pow_mem_graded (2 * e + d) hf) using 2
      ring
    refine (isUnit_iff_exists_inv.mpr ⟨z, ?_⟩).pow _
    ext
    simp only [val_mul, val_one, awayMap_mk, Away.val_mk, z, Localization.mk_mul]
    rw [← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    use 1
    simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul, mul_one, hx]
    ring
  · intro z
    obtain ⟨n, s, hs, rfl⟩ := Away.mk_surjective 𝒜 (hx ▸ SetLike.mul_mem_graded hf hg) z
    rcases d with - | d
    · contradiction
    let t : Away 𝒜 f := Away.mk 𝒜 hf (n * (e + 1)) (s * g ^ (n * d)) <| by
      convert! SetLike.mul_mem_graded hs (SetLike.pow_mem_graded _ hg) using 2; simp; ring
    refine ⟨⟨t, ⟨_, ⟨n, rfl⟩⟩⟩, ?_⟩
    ext
    simp only [RingHom.algebraMap_toAlgebra, map_pow, awayMap_mk, val_mul, val_mk, val_pow,
      Localization.mk_pow, Localization.mk_mul, t]
    rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
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
variable [AddSubgroupClass σ A] [AddCommMonoid ι] [DecidableEq ι] {𝒜 : ι → σ} [GradedRing 𝒜] in
/--
Let `𝒜` be a graded ring, finitely generated (as an algebra) over `𝒜₀` by `{ vᵢ }`,
where `vᵢ` has degree `dvᵢ`.
If `f : A` has degree `d`, then `𝒜_(f)` is generated (as a module) over `𝒜₀` by
elements of the form `(∏ i, vᵢ ^ aᵢ) / fᵃ` such that `∑ aᵢ • dvᵢ = a • d`.
-/
/-
**HomogeneousLocalization.Away.span_mk_prod_pow_eq_top** 是 Mathlib 中的一个定理，位于命名空间
 `HomogeneousLocalization.Away`。
形式化陈述：∀ {ι : Type u_1} {A : Type u_2} {σ : Type u_3} [inst : CommRing A] [inst_1
 : SetLike σ A]   [inst_2 : AddSubgroupClass σ A] [inst_3 : AddCommMonoid ι] [in
st_4 : DecidableEq ι] {𝒜 : ι → σ}   [inst_5 : GradedRing 𝒜] {f : A} {d : ι} (hf 
: f ∈ 𝒜 d) {ι' : Type u_4} [inst_6 : Fintype ι'] (v : ι' → A),   Algebra.adjoin 
(↥(𝒜 0)) (Set.range v) = ⊤ →     ∀ (dv : ι' → ι) (hxd : ∀ (i : ι'), v i ∈ 𝒜 (dv 
i)),       Submodule.span ↥(𝒜 0)           {x |             ∃ a ai,             
  ∃ (hai : ∑ i, ai i • dv i = a • d), HomogeneousLocalization.Away.mk 𝒜 hf a (∏ 
i, v i ^ ai i) ⋯ = x} =         ⊤
参数：hf : f ∈ 𝒜 d；v : ι' → A；↥(𝒜 0)；Set.range v；dv : ι' → ι；hxd : ∀ (i : ι'), v i 
∈ 𝒜 (dv i)；𝒜 0；hai : ∑ i, ai i • dv i = a • d；∏ i, v i ^ ai i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
· 使用定理 `SetLike.prod_pow_mem_graded`：prod_pow_mem_graded (n : κ -> Nat) (hF : fo
rall k in F, g k in A (i k)) : ∏ k in F, g k ^ n k in A (∑ k in F, n k • i k)
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用引理 `HomogeneousLocalization.mk_surjective`：mk_surjective : Function.Surjecti
ve (mk (𝒜
· 使用引理 `HomogeneousLocalization.subsingleton`：subsingleton (hx : 0 in x) : Subsi
ngleton (HomogeneousLocalization 𝒜 x)
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `DirectSum.decompose_of_mem_same`：decompose_of_mem_same {x : M} {i : ι} (
hx : x in ℳ i) : (decompose ℳ x i : M) = x
· 使用定理 `HomogeneousLocalization.NumDenSameDeg.mk.congr_simp`：∀ {ι : Type u_1} {A
 : Type u_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A] {𝒜 : ι → 
σ} {x : Submonoid A}   (deg : ι) (num num…
· 使用定理 `Algebra.adjoin_eq_span`：adjoin_eq_span : Subalgebra.toSubmodule (adjoin 
R s) = span R (Submonoid.closure s)
· 使用定理 `Submodule.span_induction`：span_induction {p : (x : M) -> x in span R s -
> Prop} (mem : forall (x) (h : x in s), p x (subset_span h)) (zero : p 0 (Submod
ule.zero_mem _…
· 使用定理 `Submonoid.exists_of_mem_closure_range`：exists_of_mem_closure_range [Fint
ype ι] (hx : x in closure (Set.range f)) : exists a : ι -> Nat, x = ∏ i, f i ^ a
 i
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `DirectSum.degree_eq_of_mem_mem`：degree_eq_of_mem_mem {x : M} {i j : ι} (
hxi : x in ℳ i) (hxj : x in ℳ j) (hx : x != 0) : i = j
· 使用定理 `SetLike.pow_mem_graded`：pow_mem_graded (n : Nat) {r : R} {i : ι} (h : r 
in A i) : r ^ n in A (n • i)
· 使用定理 `HomogeneousLocalization.val_injective`：val_injective : Function.Injectiv
e (HomogeneousLocalization.val (𝒜
· 使用定理 `HomogeneousLocalization.NumDenSameDeg.den_mem`：∀ {ι : Type u_1} {A : Typ
e u_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A] {𝒜 : ι → σ} {x 
: Submonoid A}   (self : Homogeneou…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `DirectSum.decompose_of_mem_ne`：decompose_of_mem_ne {x : M} {i j : ι} (hx
 : x in ℳ i) (hij : i != j) : (decompose ℳ x j : M) = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Localization.mk_zero`：mk_zero (x : S) : mk 0 (x : S) = 0
· 使用定理 `HomogeneousLocalization.val_zero`：val_zero : (0 : HomogeneousLocalizatio
n 𝒜 x).val = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 47 条，此处仅展示前 30 条）

--- 原说明 ---
Let `𝒜` be a graded ring, finitely generated (as an algebra) over `𝒜₀` by `{ vᵢ 
}`,
where `vᵢ` has degree `dvᵢ`.
If `f : A` has degree `d`, then `𝒜_(f)` is generated (as a module) over `𝒜₀` by
elements of the form `(∏ i, vᵢ ^ aᵢ) / fᵃ` such that `∑ aᵢ • dvᵢ = a • d`.
-/
theorem Away.span_mk_prod_pow_eq_top {f : A} {d : ι} (hf : f ∈ 𝒜 d)
    {ι' : Type*} [Fintype ι'] (v : ι' → A)
    (hx : Algebra.adjoin (𝒜 0) (Set.range v) = ⊤) (dv : ι' → ι) (hxd : ∀ i, v i ∈ 𝒜 (dv i)) :
    Submodule.span (𝒜 0) { (Away.mk 𝒜 hf a (∏ i, v i ^ ai i)
      (hai ▸ SetLike.prod_pow_mem_graded _ _ _ _ fun i _ ↦ hxd i) : Away 𝒜 f) |
        (a : ℕ) (ai : ι' → ℕ) (hai : ∑ i, ai i • dv i = a • d) } = ⊤ := by
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
  have : a ∈ Submodule.span (𝒜 0) (Submonoid.closure (Set.range v)) := by
    rw [← Algebra.adjoin_eq_span, hx]
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
        exact H ▸ SetLike.prod_pow_mem_graded _ _ _ _ fun i _ ↦ hxd i
    · convert! zero_mem (Submodule.span (𝒜 0) _)
      ext
      have : (DirectSum.decompose 𝒜 (∏ i : ι', v i ^ ai i) n).1 = 0 := by
        refine DirectSum.decompose_of_mem_ne _ ?_ H
        exact SetLike.prod_pow_mem_graded _ _ _ _ fun i _ ↦ hxd i
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

variable [AddSubgroupClass σ A] {𝒜 : ℕ → σ} [GradedRing 𝒜] in
/-- This is strictly weaker than `Away.adjoin_mk_prod_pow_eq_top`. -/
private
/-
**HomogeneousLocalization.Away.adjoin_mk_prod_pow_eq_top_of_pos** 是 Mathlib 中的一个
定理，位于命名空间 `HomogeneousLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Away.adjoin_mk_prod_pow_eq_top_of_pos {f : A} {d : ℕ} (hf : f ∈ 𝒜 d)
    {ι' : Type*} [Fintype ι'] (v : ι' → A)
    (hx : Algebra.adjoin (𝒜 0) (Set.range v) = ⊤) (dv : ι' → ℕ)
    (hxd : ∀ i, v i ∈ 𝒜 (dv i)) (hxd' : ∀ i, 0 < dv i) :
    Algebra.adjoin (𝒜 0) { Away.mk 𝒜 hf a (∏ i, v i ^ ai i)
      (hai ▸ SetLike.prod_pow_mem_graded _ _ _ _ fun i _ ↦ hxd i) |
        (a : ℕ) (ai : ι' → ℕ) (hai : ∑ i, ai i • dv i = a • d) (_ : ∀ i, ai i ≤ d) } = ⊤ := by
  rw [← top_le_iff]
  change ⊤ ≤ (Algebra.adjoin (𝒜 0) _).toSubmodule
  rw [← HomogeneousLocalization.Away.span_mk_prod_pow_eq_top hf v hx dv hxd, Submodule.span_le]
  rintro _ ⟨a, ai, hai, rfl⟩
  have H₀ : (a - ∑ i : ι', dv i * (ai i / d)) • d = ∑ k : ι', (ai k % d) • dv k := by
    rw [smul_eq_mul, tsub_mul, ← smul_eq_mul, ← hai]
    conv => enter [1, 1, 2, i]; rw [← Nat.mod_add_div (ai i) d]
    simp_rw [smul_eq_mul, add_mul, Finset.sum_add_distrib,
      mul_assoc, ← Finset.mul_sum, mul_comm d, mul_comm (_ / _)]
    simp only [add_tsub_cancel_right]
  have H : Away.mk 𝒜 hf a (∏ i, v i ^ ai i)
      (hai ▸ SetLike.prod_pow_mem_graded _ _ _ _ fun i _ ↦ hxd i) =
      Away.mk 𝒜 hf (a - ∑ i : ι', dv i * (ai i / d)) (∏ i, v i ^ (ai i % d))
      (H₀ ▸ SetLike.prod_pow_mem_graded _ _ _ _ fun i _ ↦ hxd i) *
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
      rw [← mul_le_mul_iff_of_pos_right hd, ← smul_eq_mul (a := a), ← hai, Finset.sum_mul]
      simp_rw [smul_eq_mul, mul_comm (ai _), mul_assoc]
      gcongr
      exact Nat.div_mul_le_self (ai _) d
  rw [H, SetLike.mem_coe]
  apply (Algebra.adjoin (𝒜 0) _).mul_mem
  · apply Algebra.subset_adjoin
    refine ⟨a - ∑ i : ι', dv i * (ai i / d), (ai · % d), H₀.symm, ?_, rfl⟩
    rcases d.eq_zero_or_pos with hd | hd
    · have : ∀ (x : ι'), ai x = 0 := by simpa [hd, fun i ↦ (hxd' i).ne'] using hai
      simp [this]
    exact fun i ↦ (Nat.mod_lt _ hd).le
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

variable [AddSubgroupClass σ A] {𝒜 : ℕ → σ} [GradedRing 𝒜] in
/--
Let `𝒜` be a graded ring, finitely generated (as an algebra) over `𝒜₀` by `{ vᵢ }`,
where `vᵢ` has degree `dvᵢ`.
If `f : A` has degree `d`, then `𝒜_(f)` is generated (as an algebra) over `𝒜₀` by
elements of the form `(∏ i, vᵢ ^ aᵢ) / fᵃ` such that `∑ aᵢ • dvᵢ = a • d` and `∀ i, aᵢ ≤ d`.
-/
/-
**HomogeneousLocalization.Away.adjoin_mk_prod_pow_eq_top** 是 Mathlib 中的一个定理，位于命名
空间 `HomogeneousLocalization.Away`。
形式化陈述：∀ {A : Type u_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A]
 [inst_2 : AddSubgroupClass σ A] {𝒜 : ℕ → σ}   [inst_3 : GradedRing 𝒜] {f : A} {
d : ℕ} (hf : f ∈ 𝒜 d) (ι' : Type u_4) [inst_4 : Fintype ι'] (v : ι' → A),   Alge
bra.adjoin (↥(𝒜 0)) (Set.range v) = ⊤ →     ∀ (dv : ι' → ℕ) (hxd : ∀ (i : ι'), v
 i ∈ 𝒜 (dv i)),       Algebra.adjoin ↥(𝒜 0)           {x |             ∃ a ai,  
             ∃ (hai : ∑ i, ai i • dv i = a • d) (_ : ∀ (i : ι'), ai i ≤ d),     
            HomogeneousLocalization.Away.mk 𝒜 hf a (∏ i, v i ^ ai i) ⋯ = x} =   
      ⊤
参数：hf : f ∈ 𝒜 d；ι' : Type u_4；v : ι' → A；↥(𝒜 0)；Set.range v；dv : ι' → ℕ；hxd : ∀ 
(i : ι'), v i ∈ 𝒜 (dv i)；𝒜 0；hai : ∑ i, ai i • dv i = a • d；_ : ∀ (i : ι'), ai i
 ≤ d；∏ i, v i ^ ai i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
· 使用定理 `SetLike.prod_pow_mem_graded`：prod_pow_mem_graded (n : κ -> Nat) (hF : fo
rall k in F, g k in A (i k)) : ∏ k in F, g k ^ n k in A (∑ k in F, n k • i k)
· 使用定理 `_private.Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization.0.Homo
geneousLocalization.Away.adjoin_mk_prod_pow_eq_top_of_pos`：∀ {A : Type u_2} {σ :
 Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A] [inst_2 : AddSubgroupClass
 σ A] {𝒜 : ℕ → σ}   [inst_3 : GradedRin…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `Algebra.adjoin_le_iff`：adjoin_le_iff {S : Subalgebra R A} : adjoin R s <
= S ↔ s subseteq S
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `algebraMap_mem`：∀ {S : Type u_1} {R : Type u_2} {A : Type u_3} [inst : C
ommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : SetLike 
S A]…
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Algebra.adjoin_mono`：adjoin_mono (H : s subseteq t) : adjoin R s <= adjo
in R t
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `dite_mul`：dite_mul (a : P -> α) (b : ¬P -> α) (c : α) : (if h : P then a
 h else b h) * c = if h : P then a h * c else b h * c
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Finset.sum_attach_eq_sum_dite`：∀ {ι : Type u_1} {M : Type u_3} [inst : A
ddCommMonoid M] [inst_1 : Fintype ι] (s : Finset ι) (f : ↥s → M)   [inst_2 : Dec
idablePred fun x =>…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
Let `𝒜` be a graded ring, finitely generated (as an algebra) over `𝒜₀` by `{ vᵢ 
}`,
where `vᵢ` has degree `dvᵢ`.
If `f : A` has degree `d`, then `𝒜_(f)` is generated (as an algebra) over `𝒜₀` b
y
elements of the form `(∏ i, vᵢ ^ aᵢ) / fᵃ` such that `∑ aᵢ • dvᵢ = a • d` and `∀
 i, aᵢ ≤ d`.
-/
theorem Away.adjoin_mk_prod_pow_eq_top {f : A} {d : ℕ} (hf : f ∈ 𝒜 d)
    (ι' : Type*) [Fintype ι'] (v : ι' → A)
    (hx : Algebra.adjoin (𝒜 0) (Set.range v) = ⊤) (dv : ι' → ℕ) (hxd : ∀ i, v i ∈ 𝒜 (dv i)) :
    Algebra.adjoin (𝒜 0) { Away.mk 𝒜 hf a (∏ i, v i ^ ai i)
      (hai ▸ SetLike.prod_pow_mem_graded _ _ _ _ fun i _ ↦ hxd i) |
        (a : ℕ) (ai : ι' → ℕ) (hai : ∑ i, ai i • dv i = a • d) (_ : ∀ i, ai i ≤ d) } = ⊤ := by
  classical
  let s := Finset.univ.filter (0 < dv ·)
  have := Away.adjoin_mk_prod_pow_eq_top_of_pos hf (ι' := s) (v ∘ Subtype.val) ?_
    (dv ∘ Subtype.val) (fun _ ↦ hxd _) (by simp [s])
  swap
  · rw [← top_le_iff, ← hx, Algebra.adjoin_le_iff, Set.range_subset_iff]
    intro i
    rcases (dv i).eq_zero_or_pos with hi | hi
    · exact algebraMap_mem (R := 𝒜 0) _ ⟨v i, hi ▸ hxd i⟩
    exact Algebra.subset_adjoin ⟨⟨i, by simpa [s] using hi⟩, rfl⟩
  rw [← top_le_iff, ← this]
  apply Algebra.adjoin_mono
  rintro _ ⟨a, ai, hai : ∑ x ∈ s.attach, _ = _, h, rfl⟩
  refine ⟨a, fun i ↦ if hi : i ∈ s then ai ⟨i, hi⟩ else 0, ?_, ?_, ?_⟩
  · simpa [Finset.sum_attach_eq_sum_dite] using hai
  · simp [apply_dite, dite_apply, h]
  · congr 1
    change _ = ∏ x ∈ s.attach, _
    simp [Finset.prod_attach_eq_prod_dite]

variable [AddSubgroupClass σ A] {𝒜 : ℕ → σ} [GradedRing 𝒜] [Algebra.FiniteType (𝒜 0) A] in
/-
**HomogeneousLocalization.Away.finiteType** 是 Mathlib 中的一个定理，位于命名空间 `Homogeneous
Localization.Away`。
形式化陈述：∀ {A : Type u_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A]
 [inst_2 : AddSubgroupClass σ A] {𝒜 : ℕ → σ}   [inst_3 : GradedRing 𝒜] [Algebra.
FiniteType (↥(𝒜 0)) A] (f : A) (d : ℕ),   f ∈ 𝒜 d → Algebra.FiniteType (↥(𝒜 0)) 
(HomogeneousLocalization.Away 𝒜 f)
参数：↥(𝒜 0)；f : A；d : ℕ；↥(𝒜 0)；HomogeneousLocalization.Away 𝒜 f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
· 使用定理 `GradedAlgebra.exists_finset_adjoin_eq_top_and_homogeneous_ne_zero`：exist
s_finset_adjoin_eq_top_and_homogeneous_ne_zero : exists s : Finset S, Algebra.ad
join (A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SetLike.prod_pow_mem_graded`：prod_pow_mem_graded (n : κ -> Nat) (hF : fo
rall k in F, g k in A (i k)) : ∏ k in F, g k ^ n k in A (∑ k in F, n k • i k)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HomogeneousLocalization.Away.adjoin_mk_prod_pow_eq_top`：∀ {A : Type u_2}
 {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A] [inst_2 : AddSubgroup
Class σ A] {𝒜 : ℕ → σ}   [inst_3 : GradedRin…
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `nsmul_zero`：∀ {M : Type u_2} [inst : AddMonoid M] (n : ℕ), n • 0 = 0
· 使用定理 `SetLike.GradedMonoid.toGradedOne`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `Set.finite_singleton`：finite_singleton (a : α) : ({a} : Set α).Finite
· 使用定理 `Algebra.adjoin_le_iff`：adjoin_le_iff {S : Subalgebra R A} : adjoin R s <
= S ↔ s subseteq S
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `HomogeneousLocalization.Away.mk.congr_simp`：∀ {ι : Type u_1} {A : Type u
_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A]   [inst_2 : AddSub
groupClass σ A] [inst_3 : AddCom…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `HomogeneousLocalization.val_injective`：val_injective : Function.Injectiv
e (HomogeneousLocalization.val (𝒜
· 使用定理 `pow_mem`：∀ {M : Type u_3} {A : Type u_4} [inst : Monoid M] [inst_1 : Set
Like A M] [SubmonoidClass A M] {S : A} {x : M},   x ∈ S → ∀ (n : ℕ), x ^ n ∈ …
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `HomogeneousLocalization.val_pow`：val_pow : forall (y : HomogeneousLocali
zation 𝒜 x) (n : Nat), (y ^ n).val = y.val ^ n
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Localization.mk_pow`：mk_pow (n : Nat) (a : M) (b : S) : mk a b ^ n = mk 
(a ^ n) (b ^ n)
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
（共 68 条，此处仅展示前 30 条）
-/
lemma Away.finiteType (f : A) (d : ℕ) (hf : f ∈ 𝒜 d) :
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
    obtain rfl : ai = 0 := funext <| by simpa [hd, hdx] using hai
    simp only [Finset.univ_eq_attach, Pi.zero_apply, pow_zero, Finset.prod_const_one, mem_coe]
    convert! pow_mem (Algebra.self_mem_adjoin_singleton (𝒜 0) f') a using 1
    ext
    simp [f', Localization.mk_pow]
  refine ⟨_, ?_, le_rfl⟩
  let b := ∑ i, dx i
  let s' : Set ((Fin (b + 1)) × (s → Fin (d + 1))) := { ai | ∑ i, (ai.2 i).1 * dx i = ai.1 * d }
  let F : s' → Away 𝒜 f := fun ai ↦ Away.mk 𝒜 hf ai.1.1.1 (∏ i, i ^ (ai.1.2 i).1)
    (by convert! SetLike.prod_pow_mem_graded _ _ _ _ fun i _ ↦ hxd i; exact ai.2.symm)
  apply (Set.finite_range F).subset
  rintro _ ⟨a, ai, hai, hai', rfl⟩
  refine ⟨⟨⟨⟨a, ?_⟩, fun i ↦ ⟨ai i, (hai' i).trans_lt d.lt_succ_self⟩⟩, hai⟩, rfl⟩
  rw [Nat.lt_succ_iff, ← mul_le_mul_iff_of_pos_right hd, ← smul_eq_mul, ← hai, Finset.sum_mul]
  simp_rw [smul_eq_mul, mul_comm _ d]
  gcongr
  exact hai' _

end span

end HomogeneousLocalization

