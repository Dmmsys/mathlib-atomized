/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Filippo A. E. Nuccio
-/
module

public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.RingTheory.Localization.Submodule

/-!
# Fractional ideals

This file defines fractional ideals of an integral domain and proves basic facts about them.

## Main definitions
Let `S` be a submonoid of an integral domain `R` and `P` the localization of `R` at `S`.
* `IsFractional` defines which `R`-submodules of `P` are fractional ideals
* `FractionalIdeal S P` is the type of fractional ideals in `P`
* a coercion `coeIdeal : Ideal R → FractionalIdeal S P`
* `CommSemiring (FractionalIdeal S P)` instance:
  the typical ideal operations generalized to fractional ideals
* `Lattice (FractionalIdeal S P)` instance

## Main statements

  * the `MulLeftMono` and `MulRightMono` instances state that ideal multiplication is monotone
  * `mul_div_self_cancel_iff` states that `1 / I` is the inverse of `I` if one exists

## Implementation notes

Fractional ideals are considered equal when they contain the same elements,
independent of the denominator `a : R` such that `a I ⊆ R`.
Thus, we define `FractionalIdeal` to be the subtype of the predicate `IsFractional`,
instead of having `FractionalIdeal` be a structure of which `a` is a field.

Most definitions in this file specialize operations from submodules to fractional ideals,
proving that the result of this operation is fractional if the input is fractional.
Exceptions to this rule are defining `(+) := (⊔)` and `⊥ := 0`,
in order to reuse their respective proof terms.
We can still use `simp` to show `↑I + ↑J = ↑(I + J)` and `↑⊥ = ↑0`.

Many results in fact do not need that `P` is a localization, only that `P` is an
`R`-algebra. We omit the `IsLocalization` parameter whenever this is practical.
Similarly, we don't assume that the localization is a field until we need it to
define ideal quotients. When this assumption is needed, we replace `S` with `R⁰`,
making the localization a field.

## References

  * https://en.wikipedia.org/wiki/Fractional_ideal

## Tags

fractional ideal, fractional ideals, invertible ideal
-/

@[expose] public section


open IsLocalization Pointwise nonZeroDivisors

section Defs

variable {R : Type*} [CommRing R] {S : Submonoid R} {P : Type*} [CommRing P]
variable [Algebra R P]
variable (S)

/--
Definition of `IsFractional` / `IsFractional` 的定义

English:
definition IsFractional
  signature: (I : Submodule R P)
  body: exists a in S, forall b in I, IsInteger R (a • b)

中文:
定义 IsFractional
  签名: (I : 子模 R P)
  定义体: exists a in S, forall b in I, IsInteger R (a • b)

Depends on / 依赖: IsInteger
-/
def IsFractional (I : Submodule R P) :=
  exists a in S, forall b in I, IsInteger R (a • b)

variable (P)

/-- The fractional ideals of a domain `R` are ideals of `R` divided by some `a ∈ R`.

More precisely, let `P` be a localization of `R` at some submonoid `S`,
then a fractional ideal `I ⊆ P` is an `R`-submodule of `P`,
such that there is an `a ∈ S` with `a I ⊆ R`.
-/
@[wikidata Q1497184]
/--
Definition of `FractionalIdeal` / `FractionalIdeal` 的定义

English:
definition FractionalIdeal
  body: { I : Submodule R P // IsFractional S I }

中文:
定义 FractionalIdeal
  定义体: { I : Submodule R P // IsFractional S I }

Depends on / 依赖: IsFractional, Submodule
-/
def FractionalIdeal :=
  { I : Submodule R P // IsFractional S I }

end Defs

namespace FractionalIdeal

open Set Submodule

variable {R : Type*} [CommRing R] {S : Submonoid R} {P : Type*} [CommRing P]
variable [Algebra R P]

/-- Map a fractional ideal `I` to a submodule by forgetting that `∃ a, a I ⊆ R`.

This implements the coercion `FractionalIdeal S P → Submodule R P`.
-/
@[coe]
/--
Definition of `coeToSubmodule` / `coeToSubmodule` 的定义

English:
definition coeToSubmodule
  signature: (I : FractionalIdeal S P)
  body: I.val

中文:
定义 coeToSubmodule
  签名: (I : FractionalIdeal S P)
  定义体: I.val

Depends on / 依赖: I.val
-/
def coeToSubmodule (I : FractionalIdeal S P) : Submodule R P :=
  I.val

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeOut (FractionalIdeal S P) (Submodule R P)
  body: ⟨coeToSubmodule⟩

中文:
实例 :
  签名: CoeOut (FractionalIdeal S P) (子模 R P)
  定义体: ⟨coeToSubmodule⟩

Depends on / 依赖: coeToSubmodule
-/
instance : CoeOut (FractionalIdeal S P) (Submodule R P) :=
  ⟨coeToSubmodule⟩

/--
theorem `isFractional` / 定理 `isFractional`

English:
theorem isFractional
  given: (I : FractionalIdeal S P)
  statement: IsFractional S (I : Submodule R P)
  proof: I.prop

中文:
定理 isFractional
  条件: (I : FractionalIdeal S P)
  结论: IsFractional S (I : 子模 R P)
  证明: I.prop
-/
protected theorem isFractional (I : FractionalIdeal S P) : IsFractional S (I : Submodule R P) :=
  I.prop

/--
Definition of `den` / `den` 的定义

English:
definition den
  signature: (I : FractionalIdeal S P)
  body: ⟨I.2.choose, I.2.choose_spec.1⟩

中文:
定义 den
  签名: (I : FractionalIdeal S P)
  定义体: ⟨I.2.choose, I.2.choose_spec.1⟩

Depends on / 依赖: choose_spec
-/
noncomputable def den (I : FractionalIdeal S P) : S :=
  ⟨I.2.choose, I.2.choose_spec.1⟩

/--
Definition of `num` / `num` 的定义

English:
definition num
  signature: (I : FractionalIdeal S P)
  body: (I.den • (I : Submodule R P)).comap (Algebra.linearMap R P)

中文:
定义 num
  签名: (I : FractionalIdeal S P)
  定义体: (I.den • (I : Submodule R P)).comap (Algebra.linearMap R P)

Depends on / 依赖: Algebra, Algebra.linearMap, I.den, Submodule, linearMap
-/
noncomputable def num (I : FractionalIdeal S P) : Ideal R :=
  (I.den • (I : Submodule R P)).comap (Algebra.linearMap R P)

/--
theorem `den_mul_self_eq_num` / 定理 `den_mul_self_eq_num`

English:
theorem den_mul_self_eq_num
  given: (I : FractionalIdeal S P)
  proof: by
  rw [den]; rw [num]; rw [Submodule.map_comap_eq]
  refine (inf_of_le_right ?_).symm
  rintro _ ⟨a, ha, rfl⟩
  exact I.2.choose_spec.2 a ha

中文:
定理 den_mul_self_eq_num
  条件: (I : FractionalIdeal S P)
  证明: by
  rw [den]; rw [num]; rw [Submodule.map_comap_eq]
  refine (inf_of_le_right ?_).symm
  rintro _ ⟨a, ha, rfl⟩
  exact I.2.choose_spec.2 a ha

Depends on / 依赖: Submodule, Submodule.map_comap_eq, choose_spec, inf_of_le_right, map_comap_eq
-/
theorem den_mul_self_eq_num (I : FractionalIdeal S P) :
    I.den • (I : Submodule R P) = Submodule.map (Algebra.linearMap R P) I.num := by
  rw [den]; rw [num]; rw [Submodule.map_comap_eq]
  refine (inf_of_le_right ?_).symm
  rintro _ ⟨a, ha, rfl⟩
  exact I.2.choose_spec.2 a ha

/--
Definition of `equivNumOfIsSMulRegular` / `equivNumOfIsSMulRegular` 的定义

English:
abbreviation equivNumOfIsSMulRegular
  signature: [FaithfulSMul R P] {I : FractionalIdeal S P}
  body: by
  refine LinearEquiv.trans
    (LinearEquiv.ofBijective ((DistribSMul.toLinearMap R P I.den).restrict fun _ hx => ?_)
      ⟨fun _ _ hxy => ?_, fun ⟨y, hy⟩ => ?_⟩)
    (Submodule.equivMapOfInjective (Algebra.linearMap R P)
      (FaithfulSMul.algebraMap_injective R P) (num I)).symm
  · rw [← den_mul_self_eq_num]
    exact Submodule.smul_mem_pointwise_smul _ _ _ hx
  · simpa [LinearMap.restrict_apply, reg.eq_iff] using hxy
  · rw [← den_mul_self_eq_num] at hy
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨⟨x, hx⟩, by simp_rw [LinearMap.restrict_apply, Subtype.ext_iff, ← hxy]; rfl⟩

中文:
缩写 equivNumOfIsSMulRegular
  签名: [忠实标量乘法 R P] {I : FractionalIdeal S P}
  定义体: by
  refine LinearEquiv.trans
    (LinearEquiv.ofBijective ((DistribSMul.toLinearMap R P I.den).restrict fun _ hx => ?_)
      ⟨fun _ _ hxy => ?_, fun ⟨y, hy⟩ => ?_⟩)
    (Submodule.equivMapOfInjective (Algebra.linearMap R P)
      (FaithfulSMul.algebraMap_injective R P) (num I)).symm
  · rw [← den_mul_self_eq_num]
    exact Submodule.smul_mem_pointwise_smul _ _ _ hx
  · simpa [LinearMap.restrict_apply, reg.eq_iff] using hxy
  · rw [← den_mul_self_eq_num] at hy
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨⟨x, hx⟩, by simp_rw [LinearMap.restrict_apply, Subtype.ext_iff, ← hxy]; rfl⟩

Depends on / 依赖: Algebra, Algebra.linearMap, DistribSMul, DistribSMul.toLinearMap, FaithfulSMul, FaithfulSMul.algebraMap_injective, I.den, LinearEquiv, LinearEquiv.ofBijective, LinearEquiv.trans, LinearMap, LinearMap.re, LinearMap.restrict_apply, Submodule, Submodule.equivMapOfInjective, Submodule.smul_mem_pointwise_smul, algebraMap_injective, den_mul_self_eq_num, eq_iff, equivMapOfInjective
-/
noncomputable abbrev equivNumOfIsSMulRegular [FaithfulSMul R P] {I : FractionalIdeal S P}
    (reg : IsSMulRegular P I.den) : I ≃ₗ[R] I.num := by
  refine LinearEquiv.trans
    (LinearEquiv.ofBijective ((DistribSMul.toLinearMap R P I.den).restrict fun _ hx => ?_)
      ⟨fun _ _ hxy => ?_, fun ⟨y, hy⟩ => ?_⟩)
    (Submodule.equivMapOfInjective (Algebra.linearMap R P)
      (FaithfulSMul.algebraMap_injective R P) (num I)).symm
  · rw [← den_mul_self_eq_num]
    exact Submodule.smul_mem_pointwise_smul _ _ _ hx
  · simpa [LinearMap.restrict_apply, reg.eq_iff] using hxy
  · rw [← den_mul_self_eq_num] at hy
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨⟨x, hx⟩, by simp_rw [LinearMap.restrict_apply, Subtype.ext_iff, ← hxy]; rfl⟩

/--
Definition of `equivNum` / `equivNum` 的定义

English:
definition equivNum
  signature: [IsDomain R] [Module.IsTorsionFree R P] [Nontrivial P]
  body: equivNumOfIsSMulRegular (smul_right_injective P h_nz)

中文:
定义 equivNum
  签名: [是整环 R] [模.是无挠 R P] [非平凡 P]
  定义体: equivNumOfIsSMulRegular (smul_right_injective P h_nz)

Depends on / 依赖: equivNumOfIsSMulRegular, h_nz, smul_right_injective
-/
noncomputable def equivNum [IsDomain R] [Module.IsTorsionFree R P] [Nontrivial P]
    {I : FractionalIdeal S P} (h_nz : (I.den : R) != 0) : I ≃ₗ[R] I.num :=
  equivNumOfIsSMulRegular (smul_right_injective P h_nz)

/--
Definition of `equivNumOfIsLocalization` / `equivNumOfIsLocalization` 的定义

English:
definition equivNumOfIsLocalization
  signature: [FaithfulSMul R P] [IsLocalization S P]
  body: equivNumOfIsSMulRegular (smul_bijective ..).1

中文:
定义 equivNumOfIsLocalization
  签名: [忠实标量乘法 R P] [是Localization S P]
  定义体: equivNumOfIsSMulRegular (smul_bijective ..).1

Depends on / 依赖: equivNumOfIsSMulRegular, smul_bijective
-/
noncomputable def equivNumOfIsLocalization [FaithfulSMul R P] [IsLocalization S P]
    (I : FractionalIdeal S P) : I ≃ₗ[R] I.num :=
  equivNumOfIsSMulRegular (smul_bijective ..).1

section SetLike

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetLike (FractionalIdeal S P) P
  body: ↑(I : Submodule R P)
  coe_injective := SetLike.coe_injective.comp Subtype.coe_injective

中文:
实例 :
  签名: 集合状 (FractionalIdeal S P) P
  定义体: ↑(I : Submodule R P)
  coe_injective := SetLike.coe_injective.comp Subtype.coe_injective

Depends on / 依赖: Submodule
-/
instance : SetLike (FractionalIdeal S P) P where
  coe I := ↑(I : Submodule R P)
  coe_injective := SetLike.coe_injective.comp Subtype.coe_injective

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (FractionalIdeal S P)
  body: .ofSetLike (FractionalIdeal S P) P

@[simp]

中文:
实例 :
  签名: 偏序 (FractionalIdeal S P)
  定义体: .ofSetLike (FractionalIdeal S P) P

@[simp]

Depends on / 依赖: FractionalIdeal, ofSetLike
-/
instance : PartialOrder (FractionalIdeal S P) := .ofSetLike (FractionalIdeal S P) P

@[simp]
/--
theorem `mem_coe` / 定理 `mem_coe`

English:
theorem mem_coe
  given: {I : FractionalIdeal S P} {x : P}
  statement: x in (I : Submodule R P) ↔ x in I
  proof: Iff.rfl

中文:
定理 mem_coe
  条件: {I : FractionalIdeal S P} {x : P}
  结论: x in (I : 子模 R P) ↔ x in I
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_coe {I : FractionalIdeal S P} {x : P} : x in (I : Submodule R P) ↔ x in I :=
  Iff.rfl

/--
theorem `coe_ext` / 定理 `coe_ext`

English:
theorem coe_ext
  given: {I J : FractionalIdeal S P}
  statement: (I : Submodule R P) = (J : Submodule R P) -> I = J
  proof: Subtype.ext

中文:
定理 coe_ext
  条件: {I J : FractionalIdeal S P}
  结论: (I : 子模 R P) = (J : 子模 R P) -> I = J
  证明: Subtype.ext

Depends on / 依赖: Subtype, Subtype.ext
-/
theorem coe_ext {I J : FractionalIdeal S P} : (I : Submodule R P) = (J : Submodule R P) -> I = J :=
  Subtype.ext

/--
theorem `coe_ext_iff` / 定理 `coe_ext_iff`

English:
theorem coe_ext_iff
  given: {I J : FractionalIdeal S P}
  proof: Subtype.ext_iff

@[ext]

中文:
定理 coe_ext_iff
  条件: {I J : FractionalIdeal S P}
  证明: Subtype.ext_iff

@[ext]

Depends on / 依赖: Subtype, Subtype.ext_iff, ext_iff
-/
theorem coe_ext_iff {I J : FractionalIdeal S P} :
    I = J ↔ (I : Submodule R P) = (J : Submodule R P) :=
  Subtype.ext_iff

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {I J : FractionalIdeal S P}
  statement: (forall x, x in I ↔ x in J) -> I = J
  proof: SetLike.ext

中文:
定理 ext
  条件: {I J : FractionalIdeal S P}
  结论: (对任意 x, x in I ↔ x in J) -> I = J
  证明: SetLike.ext

Depends on / 依赖: SetLike, SetLike.ext
-/
theorem ext {I J : FractionalIdeal S P} : (forall x, x in I ↔ x in J) -> I = J :=
  SetLike.ext

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `equivNum_apply` / 定理 `equivNum_apply`

English:
theorem equivNum_apply
  statement: [IsDomain R] [Module.IsTorsionFree R P] [Nontrivial P]
  proof: by
  change Algebra.linearMap R P _ = _
  rw [equivNum]; rw [LinearEquiv.trans_apply]; rw [LinearEquiv.ofBijective_apply]; rw [LinearMap.restrict_apply]; rw [Submodule.map_equivMapOfInjective_symm_apply]; rw [Subtype.coe_mk]; rw [DistribSMul.toLinearMap_apply]

中文:
定理 equivNum_apply
  结论: [是整环 R] [模.是无挠 R P] [非平凡 P]
  证明: by
  change Algebra.linearMap R P _ = _
  rw [equivNum]; rw [LinearEquiv.trans_apply]; rw [LinearEquiv.ofBijective_apply]; rw [LinearMap.restrict_apply]; rw [Submodule.map_equivMapOfInjective_symm_apply]; rw [Subtype.coe_mk]; rw [DistribSMul.toLinearMap_apply]

Depends on / 依赖: Algebra, Algebra.linearMap, DistribSMul, DistribSMul.toLinearMap_apply, LinearEquiv, LinearEquiv.ofBijective_apply, LinearEquiv.trans_apply, LinearMap, LinearMap.restrict_apply, Submodule, Submodule.map_equivMapOfInjective_symm_apply, Subtype, Subtype.coe_mk, coe_mk, equivNum, linearMap, map_equivMapOfInjective_symm_apply, ofBijective_apply, restrict_apply, toLinearMap_apply
-/
theorem equivNum_apply [IsDomain R] [Module.IsTorsionFree R P] [Nontrivial P]
    {I : FractionalIdeal S P} (h_nz : (I.den : R) != 0) (x : I) :
    algebraMap R P (equivNum h_nz x) = I.den • x := by
  change Algebra.linearMap R P _ = _
  rw [equivNum]; rw [LinearEquiv.trans_apply]; rw [LinearEquiv.ofBijective_apply]; rw [LinearMap.restrict_apply]; rw [Submodule.map_equivMapOfInjective_symm_apply]; rw [Subtype.coe_mk]; rw [DistribSMul.toLinearMap_apply]

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (p : FractionalIdeal S P) (s : Set P) (hs : s = ↑p)
  body: ⟨Submodule.copy p s hs, by
    convert! p.isFractional
    ext
    simp only [hs]
    rfl⟩

@[simp]

中文:
定义 copy
  签名: (p : FractionalIdeal S P) (s : 集合 P) (hs : s = ↑p)
  定义体: ⟨Submodule.copy p s hs, by
    convert! p.isFractional
    ext
    simp only [hs]
    rfl⟩

@[simp]
-/
protected def copy (p : FractionalIdeal S P) (s : Set P) (hs : s = ↑p) : FractionalIdeal S P :=
  ⟨Submodule.copy p s hs, by
    convert! p.isFractional
    ext
    simp only [hs]
    rfl⟩

@[simp]
/--
theorem `coe_copy` / 定理 `coe_copy`

English:
theorem coe_copy
  given: (p : FractionalIdeal S P) (s : Set P) (hs : s = ↑p)
  statement: ↑(p.copy s hs) = s
  proof: rfl

中文:
定理 coe_copy
  条件: (p : FractionalIdeal S P) (s : 集合 P) (hs : s = ↑p)
  结论: ↑(p.copy s hs) = s
  证明: rfl
-/
theorem coe_copy (p : FractionalIdeal S P) (s : Set P) (hs : s = ↑p) : ↑(p.copy s hs) = s :=
  rfl

/--
theorem `coe_eq` / 定理 `coe_eq`

English:
theorem coe_eq
  given: (p : FractionalIdeal S P) (s : Set P) (hs : s = ↑p)
  statement: p.copy s hs = p
  proof: SetLike.coe_injective hs

中文:
定理 coe_eq
  条件: (p : FractionalIdeal S P) (s : 集合 P) (hs : s = ↑p)
  结论: p.copy s hs = p
  证明: SetLike.coe_injective hs

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem coe_eq (p : FractionalIdeal S P) (s : Set P) (hs : s = ↑p) : p.copy s hs = p :=
  SetLike.coe_injective hs

end SetLike

/--
lemma `zero_mem` / 引理 `zero_mem`

English:
lemma zero_mem
  given: (I : FractionalIdeal S P)
  statement: 0 in I
  proof: I.coeToSubmodule.zero_mem

@[simp]

中文:
引理 zero_mem
  条件: (I : FractionalIdeal S P)
  结论: 0 in I
  证明: I.coeToSubmodule.zero_mem

@[simp]

Depends on / 依赖: I.coeToSubmodule.zero_mem, coeToSubmodule, zero_mem
-/
lemma zero_mem (I : FractionalIdeal S P) : 0 in I := I.coeToSubmodule.zero_mem

@[simp]
/--
theorem `val_eq_coe` / 定理 `val_eq_coe`

English:
theorem val_eq_coe
  given: (I : FractionalIdeal S P)
  statement: I.val = I
  proof: rfl

@[simp, norm_cast]

中文:
定理 val_eq_coe
  条件: (I : FractionalIdeal S P)
  结论: I.val = I
  证明: rfl

@[simp, norm_cast]
-/
theorem val_eq_coe (I : FractionalIdeal S P) : I.val = I :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (I : Submodule R P) (hI : IsFractional S I)
  proof: rfl

中文:
定理 coe_mk
  条件: (I : 子模 R P) (hI : IsFractional S I)
  证明: rfl
-/
theorem coe_mk (I : Submodule R P) (hI : IsFractional S I) :
    coeToSubmodule ⟨I, hI⟩ = I :=
  rfl

/--
theorem `coeToSet_coeToSubmodule` / 定理 `coeToSet_coeToSubmodule`

English:
theorem coeToSet_coeToSubmodule
  given: (I : FractionalIdeal S P)
  proof: rfl

中文:
定理 coeToSet_coeToSubmodule
  条件: (I : FractionalIdeal S P)
  证明: rfl
-/
theorem coeToSet_coeToSubmodule (I : FractionalIdeal S P) :
    ((I : Submodule R P) : Set P) = I :=
  rfl

/-! Transfer instances from `Submodule R P` to `FractionalIdeal S P`. -/

instance (I : FractionalIdeal S P) : Module R I :=
  Submodule.module (I : Submodule R P)

/--
theorem `coeToSubmodule_injective` / 定理 `coeToSubmodule_injective`

English:
theorem coeToSubmodule_injective
  proof: Subtype.coe_injective

中文:
定理 coeToSubmodule_injective
  证明: Subtype.coe_injective

Depends on / 依赖: Subtype, Subtype.coe_injective, coe_injective
-/
theorem coeToSubmodule_injective :
    Function.Injective (fun (I : FractionalIdeal S P) => (I : Submodule R P)) :=
  Subtype.coe_injective

/--
theorem `coeToSubmodule_inj` / 定理 `coeToSubmodule_inj`

English:
theorem coeToSubmodule_inj
  given: {I J : FractionalIdeal S P}
  statement: (I : Submodule R P) = J ↔ I = J
  proof: coeToSubmodule_injective.eq_iff

中文:
定理 coeToSubmodule_inj
  条件: {I J : FractionalIdeal S P}
  结论: (I : 子模 R P) = J ↔ I = J
  证明: coeToSubmodule_injective.eq_iff

Depends on / 依赖: coeToSubmodule_injective, coeToSubmodule_injective.eq_iff, eq_iff
-/
theorem coeToSubmodule_inj {I J : FractionalIdeal S P} : (I : Submodule R P) = J ↔ I = J :=
  coeToSubmodule_injective.eq_iff

/--
theorem `isFractional_of_le_one` / 定理 `isFractional_of_le_one`

English:
theorem isFractional_of_le_one
  given: (I : Submodule R P) (h : I <= 1)
  statement: IsFractional S I
  proof: by
  use 1, S.one_mem
  intro b hb
  rw [one_smul]
  obtain ⟨b', b'_mem, rfl⟩ := mem_one.mp (h hb)
  exact Set.mem_range_self b'

中文:
定理 isFractional_of_le_one
  条件: (I : 子模 R P) (h : I <= 1)
  结论: IsFractional S I
  证明: by
  use 1, S.one_mem
  intro b hb
  rw [one_smul]
  obtain ⟨b', b'_mem, rfl⟩ := mem_one.mp (h hb)
  exact Set.mem_range_self b'

Depends on / 依赖: S.one_mem, Set.mem_range_self, _mem, mem_one, mem_one.mp, mem_range_self, one_mem, one_smul
-/
theorem isFractional_of_le_one (I : Submodule R P) (h : I <= 1) : IsFractional S I := by
  use 1, S.one_mem
  intro b hb
  rw [one_smul]
  obtain ⟨b', b'_mem, rfl⟩ := mem_one.mp (h hb)
  exact Set.mem_range_self b'

/--
theorem `isFractional_of_le` / 定理 `isFractional_of_le`

English:
theorem isFractional_of_le
  given: {I : Submodule R P} {J : FractionalIdeal S P} (hIJ : I <= J)
  proof: by
  obtain ⟨a, a_mem, ha⟩ := J.isFractional
  use a, a_mem
  intro b b_mem
  exact ha b (hIJ b_mem)

中文:
定理 isFractional_of_le
  条件: {I : 子模 R P} {J : FractionalIdeal S P} (hIJ : I <= J)
  证明: by
  obtain ⟨a, a_mem, ha⟩ := J.isFractional
  use a, a_mem
  intro b b_mem
  exact ha b (hIJ b_mem)

Depends on / 依赖: J.isFractional, a_mem, b_mem, isFractional
-/
theorem isFractional_of_le {I : Submodule R P} {J : FractionalIdeal S P} (hIJ : I <= J) :
    IsFractional S I := by
  obtain ⟨a, a_mem, ha⟩ := J.isFractional
  use a, a_mem
  intro b b_mem
  exact ha b (hIJ b_mem)

/-- Map an ideal `I` to a fractional ideal by forgetting `I` is integral.

This is the function that implements the coercion `Ideal R → FractionalIdeal S P`. -/
@[coe]
/--
Definition of `coeIdeal` / `coeIdeal` 的定义

English:
definition coeIdeal
  signature: (I : Ideal R)
  body: ⟨coeSubmodule P I,
isFractional_of_le_one _ by simpa using coeSubmodule_mono P (le_top : I <= ⊤)⟩

中文:
定义 coeIdeal
  签名: (I : 理想 R)
  定义体: ⟨coeSubmodule P I,
isFractional_of_le_one _ by simpa using coeSubmodule_mono P (le_top : I <= ⊤)⟩

Depends on / 依赖: coeSubmodule, coeSubmodule_mono, isFractional_of_le_one, le_top
-/
def coeIdeal (I : Ideal R) : FractionalIdeal S P :=
  ⟨coeSubmodule P I,
isFractional_of_le_one _ by simpa using coeSubmodule_mono P (le_top : I <= ⊤)⟩

-- Is a `CoeTC` rather than `Coe` to speed up failing inference, see library note [use has_coe_t]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeTC (Ideal R) (FractionalIdeal S P)
  body: ⟨fun I => coeIdeal I⟩

@[simp, norm_cast]

中文:
实例 :
  签名: CoeTC (理想 R) (FractionalIdeal S P)
  定义体: ⟨fun I => coeIdeal I⟩

@[simp, norm_cast]

Depends on / 依赖: coeIdeal
-/
instance : CoeTC (Ideal R) (FractionalIdeal S P) :=
  ⟨fun I => coeIdeal I⟩

@[simp, norm_cast]
/--
theorem `coe_coeIdeal` / 定理 `coe_coeIdeal`

English:
theorem coe_coeIdeal
  given: (I : Ideal R)
  proof: rfl

中文:
定理 coe_coeIdeal
  条件: (I : 理想 R)
  证明: rfl
-/
theorem coe_coeIdeal (I : Ideal R) :
    ((I : FractionalIdeal S P) : Submodule R P) = coeSubmodule P I :=
  rfl

variable (S)

@[simp]
/--
theorem `mem_coeIdeal` / 定理 `mem_coeIdeal`

English:
theorem mem_coeIdeal
  given: {x : P} {I : Ideal R}
  proof: mem_coeSubmodule _ _

@[simp] -- Ensure `simp` is confluent for `x ∈ ((I : Ideal R) : FractionalIdeal S P)`.

中文:
定理 mem_coeIdeal
  条件: {x : P} {I : 理想 R}
  证明: mem_coeSubmodule _ _

@[simp] -- Ensure `simp` is confluent for `x ∈ ((I : Ideal R) : FractionalIdeal S P)`.

Depends on / 依赖: mem_coeSubmodule
-/
theorem mem_coeIdeal {x : P} {I : Ideal R} :
    x in (I : FractionalIdeal S P) ↔ exists x', x' in I ∧ algebraMap R P x' = x :=
  mem_coeSubmodule _ _

@[simp] -- Ensure `simp` is confluent for `x ∈ ((I : Ideal R) : FractionalIdeal S P)`.
/--
theorem `mem_coeSubmodule` / 定理 `mem_coeSubmodule`

English:
theorem mem_coeSubmodule
  given: {x : P} {I : Ideal R}
  proof: Iff.rfl

中文:
定理 mem_coeSubmodule
  条件: {x : P} {I : 理想 R}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_coeSubmodule {x : P} {I : Ideal R} :
    x in coeSubmodule P I ↔ exists x', x' in I ∧ algebraMap R P x' = x :=
  Iff.rfl

/--
theorem `mem_coeIdeal_of_mem` / 定理 `mem_coeIdeal_of_mem`

English:
theorem mem_coeIdeal_of_mem
  given: {x : R} {I : Ideal R} (hx : x in I)
  proof: (mem_coeIdeal S).mpr ⟨x, hx, rfl⟩

中文:
定理 mem_coeIdeal_of_mem
  条件: {x : R} {I : 理想 R} (hx : x in I)
  证明: (mem_coeIdeal S).mpr ⟨x, hx, rfl⟩

Depends on / 依赖: mem_coeIdeal
-/
theorem mem_coeIdeal_of_mem {x : R} {I : Ideal R} (hx : x in I) :
    algebraMap R P x in (I : FractionalIdeal S P) :=
  (mem_coeIdeal S).mpr ⟨x, hx, rfl⟩

/--
theorem `coeIdeal_le_coeIdeal'` / 定理 `coeIdeal_le_coeIdeal'`

English:
theorem coeIdeal_le_coeIdeal'
  given: [IsLocalization S P] (h : S <= nonZeroDivisors R) {I J : Ideal R}
  proof: coeSubmodule_le_coeSubmodule h

@[simp, gcongr]

中文:
定理 coeIdeal_le_coeIdeal'
  条件: [是Localization S P] (h : S <= nonZeroDivisors R) {I J : 理想 R}
  证明: coeSubmodule_le_coeSubmodule h

@[simp, gcongr]

Depends on / 依赖: coeSubmodule_le_coeSubmodule
-/
theorem coeIdeal_le_coeIdeal' [IsLocalization S P] (h : S <= nonZeroDivisors R) {I J : Ideal R} :
    (I : FractionalIdeal S P) <= J ↔ I <= J :=
  coeSubmodule_le_coeSubmodule h

@[simp, gcongr]
/--
theorem `coeIdeal_le_coeIdeal` / 定理 `coeIdeal_le_coeIdeal`

English:
theorem coeIdeal_le_coeIdeal
  statement: (K : Type*) [CommRing K] [Algebra R K] [IsFractionRing R K]
  proof: IsFractionRing.coeSubmodule_le_coeSubmodule

中文:
定理 coeIdeal_le_coeIdeal
  结论: (K : 类型) [交换环 K] [代数 R K] [IsFractionRing R K]
  证明: IsFractionRing.coeSubmodule_le_coeSubmodule

Depends on / 依赖: IsFractionRing, IsFractionRing.coeSubmodule_le_coeSubmodule, coeSubmodule_le_coeSubmodule
-/
theorem coeIdeal_le_coeIdeal (K : Type*) [CommRing K] [Algebra R K] [IsFractionRing R K]
    {I J : Ideal R} : (I : FractionalIdeal R⁰ K) <= J ↔ I <= J :=
  IsFractionRing.coeSubmodule_le_coeSubmodule

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (FractionalIdeal S P)
  body: ⟨(0 : Ideal R)⟩

@[simp]

中文:
实例 :
  签名: 零 (FractionalIdeal S P)
  定义体: ⟨(0 : Ideal R)⟩

@[simp]
-/
instance : Zero (FractionalIdeal S P) :=
  ⟨(0 : Ideal R)⟩

@[simp]
/--
theorem `mem_zero_iff` / 定理 `mem_zero_iff`

English:
theorem mem_zero_iff
  given: {x : P}
  statement: x in (0 : FractionalIdeal S P) ↔ x = 0
  proof: ⟨fun ⟨x', x'_mem_zero, x'_eq_x⟩ => by
    have x'_eq_zero : x' = 0 := x'_mem_zero
    simp [x'_eq_x.symm, x'_eq_zero], fun hx => ⟨0, rfl, by simp [hx]⟩⟩

中文:
定理 mem_zero_iff
  条件: {x : P}
  结论: x in (0 : FractionalIdeal S P) ↔ x = 0
  证明: ⟨fun ⟨x', x'_mem_zero, x'_eq_x⟩ => by
    have x'_eq_zero : x' = 0 := x'_mem_zero
    simp [x'_eq_x.symm, x'_eq_zero], fun hx => ⟨0, rfl, by simp [hx]⟩⟩

Depends on / 依赖: _eq_x, _eq_x.symm, _eq_zero, _mem_zero
-/
theorem mem_zero_iff {x : P} : x in (0 : FractionalIdeal S P) ↔ x = 0 :=
  ⟨fun ⟨x', x'_mem_zero, x'_eq_x⟩ => by
    have x'_eq_zero : x' = 0 := x'_mem_zero
    simp [x'_eq_x.symm, x'_eq_zero], fun hx => ⟨0, rfl, by simp [hx]⟩⟩

variable {S}

@[simp, norm_cast]
/--
theorem `coe_zero` / 定理 `coe_zero`

English:
theorem coe_zero
  statement: ↑(0 : FractionalIdeal S P) = (⊥ : Submodule R P)
  proof: Submodule.ext fun _ => mem_zero_iff S

@[simp, norm_cast]

中文:
定理 coe_zero
  结论: ↑(0 : FractionalIdeal S P) = (⊥ : 子模 R P)
  证明: Submodule.ext fun _ => mem_zero_iff S

@[simp, norm_cast]

Depends on / 依赖: Submodule, Submodule.ext, mem_zero_iff
-/
theorem coe_zero : ↑(0 : FractionalIdeal S P) = (⊥ : Submodule R P) :=
  Submodule.ext fun _ => mem_zero_iff S

@[simp, norm_cast]
/--
theorem `coeIdeal_bot` / 定理 `coeIdeal_bot`

English:
theorem coeIdeal_bot
  statement: ((⊥ : Ideal R) : FractionalIdeal S P) = 0
  proof: rfl

中文:
定理 coeIdeal_bot
  结论: ((⊥ : 理想 R) : FractionalIdeal S P) = 0
  证明: rfl
-/
theorem coeIdeal_bot : ((⊥ : Ideal R) : FractionalIdeal S P) = 0 :=
  rfl

section
variable [loc : IsLocalization S P]

variable (P) in
-- Cannot be @[simp] because `S` cannot be inferred by `simp`.
/--
theorem `exists_mem_algebraMap_eq` / 定理 `exists_mem_algebraMap_eq`

English:
theorem exists_mem_algebraMap_eq
  given: {x : R} {I : Ideal R} (h : S <= nonZeroDivisors R)
  proof: ⟨fun ⟨_, hx', Eq⟩ => IsLocalization.injective _ h Eq ▸ hx', fun h => ⟨x, h, rfl⟩⟩

中文:
定理 存在_mem_algebraMap_eq
  条件: {x : R} {I : 理想 R} (h : S <= nonZeroDivisors R)
  证明: ⟨fun ⟨_, hx', Eq⟩ => IsLocalization.injective _ h Eq ▸ hx', fun h => ⟨x, h, rfl⟩⟩

Depends on / 依赖: IsLocalization, IsLocalization.injective, injective
-/
theorem exists_mem_algebraMap_eq {x : R} {I : Ideal R} (h : S <= nonZeroDivisors R) :
    (exists x', x' in I ∧ algebraMap R P x' = algebraMap R P x) ↔ x in I :=
  ⟨fun ⟨_, hx', Eq⟩ => IsLocalization.injective _ h Eq ▸ hx', fun h => ⟨x, h, rfl⟩⟩

/--
theorem `coeIdeal_injective'` / 定理 `coeIdeal_injective'`

English:
theorem coeIdeal_injective'
  given: (h : S <= nonZeroDivisors R)
  proof: fun _ _ h' =>
  ((coeIdeal_le_coeIdeal' S h).mp h'.le).antisymm ((coeIdeal_le_coeIdeal' S h).mp
    h'.ge)

中文:
定理 coeIdeal_injective'
  条件: (h : S <= nonZeroDivisors R)
  证明: fun _ _ h' =>
  ((coeIdeal_le_coeIdeal' S h).mp h'.le).antisymm ((coeIdeal_le_coeIdeal' S h).mp
    h'.ge)
-/
theorem coeIdeal_injective' (h : S <= nonZeroDivisors R) :
    Function.Injective (fun (I : Ideal R) => (I : FractionalIdeal S P)) := fun _ _ h' =>
  ((coeIdeal_le_coeIdeal' S h).mp h'.le).antisymm ((coeIdeal_le_coeIdeal' S h).mp
    h'.ge)

/--
theorem `coeIdeal_inj'` / 定理 `coeIdeal_inj'`

English:
theorem coeIdeal_inj'
  given: (h : S <= nonZeroDivisors R) {I J : Ideal R}
  proof: (coeIdeal_injective' h).eq_iff

中文:
定理 coeIdeal_inj'
  条件: (h : S <= nonZeroDivisors R) {I J : 理想 R}
  证明: (coeIdeal_injective' h).eq_iff

Depends on / 依赖: coeIdeal_injective, eq_iff
-/
theorem coeIdeal_inj' (h : S <= nonZeroDivisors R) {I J : Ideal R} :
    (I : FractionalIdeal S P) = J ↔ I = J :=
  (coeIdeal_injective' h).eq_iff

-- Not `@[simp]` because `coeIdeal_eq_zero` (in `Operations.lean`) will prove this.
/--
theorem `coeIdeal_eq_zero'` / 定理 `coeIdeal_eq_zero'`

English:
theorem coeIdeal_eq_zero'
  given: {I : Ideal R} (h : S <= nonZeroDivisors R)
  proof: coeIdeal_inj' h

中文:
定理 coeIdeal_eq_zero'
  条件: {I : 理想 R} (h : S <= nonZeroDivisors R)
  证明: coeIdeal_inj' h

Depends on / 依赖: coeIdeal_inj
-/
theorem coeIdeal_eq_zero' {I : Ideal R} (h : S <= nonZeroDivisors R) :
    (I : FractionalIdeal S P) = 0 ↔ I = (⊥ : Ideal R) :=
  coeIdeal_inj' h

/--
theorem `coeIdeal_ne_zero'` / 定理 `coeIdeal_ne_zero'`

English:
theorem coeIdeal_ne_zero'
  given: {I : Ideal R} (h : S <= nonZeroDivisors R)
  proof: not_iff_not.mpr coeIdeal_eq_zero' h

中文:
定理 coeIdeal_ne_zero'
  条件: {I : 理想 R} (h : S <= nonZeroDivisors R)
  证明: not_iff_not.mpr coeIdeal_eq_zero' h

Depends on / 依赖: coeIdeal_eq_zero, not_iff_not, not_iff_not.mpr
-/
theorem coeIdeal_ne_zero' {I : Ideal R} (h : S <= nonZeroDivisors R) :
    (I : FractionalIdeal S P) != 0 ↔ I != (⊥ : Ideal R) :=
not_iff_not.mpr coeIdeal_eq_zero' h

end

/--
theorem `coeToSubmodule_eq_bot` / 定理 `coeToSubmodule_eq_bot`

English:
theorem coeToSubmodule_eq_bot
  given: {I : FractionalIdeal S P}
  statement: (I : Submodule R P) = ⊥ ↔ I = 0
  proof: ⟨fun h => coeToSubmodule_injective (by simp [h]), fun h => by simp [h]⟩

中文:
定理 coeToSubmodule_eq_bot
  条件: {I : FractionalIdeal S P}
  结论: (I : 子模 R P) = ⊥ ↔ I = 0
  证明: ⟨fun h => coeToSubmodule_injective (by simp [h]), fun h => by simp [h]⟩

Depends on / 依赖: coeToSubmodule_injective
-/
theorem coeToSubmodule_eq_bot {I : FractionalIdeal S P} : (I : Submodule R P) = ⊥ ↔ I = 0 :=
  ⟨fun h => coeToSubmodule_injective (by simp [h]), fun h => by simp [h]⟩

/--
theorem `coeToSubmodule_ne_bot` / 定理 `coeToSubmodule_ne_bot`

English:
theorem coeToSubmodule_ne_bot
  given: {I : FractionalIdeal S P}
  statement: ↑I != (⊥ : Submodule R P) ↔ I != 0
  proof: not_iff_not.mpr coeToSubmodule_eq_bot

中文:
定理 coeToSubmodule_ne_bot
  条件: {I : FractionalIdeal S P}
  结论: ↑I != (⊥ : 子模 R P) ↔ I != 0
  证明: not_iff_not.mpr coeToSubmodule_eq_bot

Depends on / 依赖: coeToSubmodule_eq_bot, not_iff_not, not_iff_not.mpr
-/
theorem coeToSubmodule_ne_bot {I : FractionalIdeal S P} : ↑I != (⊥ : Submodule R P) ↔ I != 0 :=
  not_iff_not.mpr coeToSubmodule_eq_bot

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (FractionalIdeal S P)
  body: ⟨0⟩

中文:
实例 :
  签名: 可居 (FractionalIdeal S P)
  定义体: ⟨0⟩
-/
instance : Inhabited (FractionalIdeal S P) :=
  ⟨0⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (FractionalIdeal S P)
  body: ⟨(⊤ : Ideal R)⟩

中文:
实例 :
  签名: 幺 (FractionalIdeal S P)
  定义体: ⟨(⊤ : Ideal R)⟩
-/
instance : One (FractionalIdeal S P) :=
  ⟨(⊤ : Ideal R)⟩

/--
theorem `zero_of_num_eq_bot` / 定理 `zero_of_num_eq_bot`

English:
theorem zero_of_num_eq_bot
  statement: [IsDomain R] [Module.IsTorsionFree R P] (hS : 0 ∉ S)
  proof: by
  rw [← coeToSubmodule_eq_bot]; rw [eq_bot_iff]
  intro x hx
  suffices (den I : R) • x = 0 from
    (smul_eq_zero.mp this).resolve_left (ne_of_mem_of_not_mem (SetLike.coe_mem _) hS)
  have h_eq : I.den • (I : Submodule R P) = ⊥ := by rw [den_mul_self_eq_num, hI, Submodule.map_bot]
  exact (Submodule.eq_bot_iff _).mp h_eq (den I • x) ⟨x, hx, rfl⟩

中文:
定理 zero_of_num_eq_bot
  结论: [是整环 R] [模.是无挠 R P] (hS : 0 ∉ S)
  证明: by
  rw [← coeToSubmodule_eq_bot]; rw [eq_bot_iff]
  intro x hx
  suffices (den I : R) • x = 0 from
    (smul_eq_zero.mp this).resolve_left (ne_of_mem_of_not_mem (SetLike.coe_mem _) hS)
  have h_eq : I.den • (I : Submodule R P) = ⊥ := by rw [den_mul_self_eq_num, hI, Submodule.map_bot]
  exact (Submodule.eq_bot_iff _).mp h_eq (den I • x) ⟨x, hx, rfl⟩

Depends on / 依赖: I.den, SetLike, SetLike.coe_mem, Submodule, Submodule.eq_bot_iff, Submodule.map_bot, coeToSubmodule_eq_bot, coe_mem, den_mul_self_eq_num, eq_bot_iff, h_eq, map_bot, ne_of_mem_of_not_mem, resolve_left, smul_eq_zero, smul_eq_zero.mp
-/
theorem zero_of_num_eq_bot [IsDomain R] [Module.IsTorsionFree R P] (hS : 0 ∉ S)
    {I : FractionalIdeal S P} (hI : I.num = ⊥) : I = 0 := by
  rw [← coeToSubmodule_eq_bot]; rw [eq_bot_iff]
  intro x hx
  suffices (den I : R) • x = 0 from
    (smul_eq_zero.mp this).resolve_left (ne_of_mem_of_not_mem (SetLike.coe_mem _) hS)
  have h_eq : I.den • (I : Submodule R P) = ⊥ := by rw [den_mul_self_eq_num, hI, Submodule.map_bot]
  exact (Submodule.eq_bot_iff _).mp h_eq (den I • x) ⟨x, hx, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `num_zero_eq` / 定理 `num_zero_eq`

English:
theorem num_zero_eq
  given: (h_inj : Function.Injective (algebraMap R P))
  proof: by
  simpa [num, LinearMap.ker_eq_bot] using! h_inj

中文:
定理 num_zero_eq
  条件: (h_inj : 函数.单射 (algebraMap R P))
  证明: by
  simpa [num, LinearMap.ker_eq_bot] using! h_inj

Depends on / 依赖: LinearMap, LinearMap.ker_eq_bot, h_inj, ker_eq_bot
-/
theorem num_zero_eq (h_inj : Function.Injective (algebraMap R P)) :
    num (0 : FractionalIdeal S P) = 0 := by
  simpa [num, LinearMap.ker_eq_bot] using! h_inj

variable (S)

@[simp, norm_cast]
/--
theorem `coeIdeal_top` / 定理 `coeIdeal_top`

English:
theorem coeIdeal_top
  statement: ((⊤ : Ideal R) : FractionalIdeal S P) = 1
  proof: rfl

@[simp]

中文:
定理 coeIdeal_top
  结论: ((⊤ : 理想 R) : FractionalIdeal S P) = 1
  证明: rfl

@[simp]
-/
theorem coeIdeal_top : ((⊤ : Ideal R) : FractionalIdeal S P) = 1 :=
  rfl

@[simp]
/--
theorem `mem_one_iff` / 定理 `mem_one_iff`

English:
theorem mem_one_iff
  given: {x : P}
  statement: x in (1 : FractionalIdeal S P) ↔ exists x' : R, algebraMap R P x' = x
  proof: Iff.intro (fun ⟨x', _, h⟩ => ⟨x', h⟩) fun ⟨x', h⟩ => ⟨x', ⟨⟩, h⟩

中文:
定理 mem_one_iff
  条件: {x : P}
  结论: x in (1 : FractionalIdeal S P) ↔ 存在 x' : R, algebraMap R P x' = x
  证明: Iff.intro (fun ⟨x', _, h⟩ => ⟨x', h⟩) fun ⟨x', h⟩ => ⟨x', ⟨⟩, h⟩

Depends on / 依赖: Iff.intro
-/
theorem mem_one_iff {x : P} : x in (1 : FractionalIdeal S P) ↔ exists x' : R, algebraMap R P x' = x :=
  Iff.intro (fun ⟨x', _, h⟩ => ⟨x', h⟩) fun ⟨x', h⟩ => ⟨x', ⟨⟩, h⟩

/--
theorem `coe_mem_one` / 定理 `coe_mem_one`

English:
theorem coe_mem_one
  given: (x : R)
  statement: algebraMap R P x in (1 : FractionalIdeal S P)
  proof: by simp

中文:
定理 coe_mem_one
  条件: (x : R)
  结论: algebraMap R P x in (1 : FractionalIdeal S P)
  证明: by simp
-/
theorem coe_mem_one (x : R) : algebraMap R P x in (1 : FractionalIdeal S P) := by simp

/--
theorem `one_mem_one` / 定理 `one_mem_one`

English:
theorem one_mem_one
  statement: (1 : P) in (1 : FractionalIdeal S P)
  proof: (mem_one_iff S).mpr ⟨1, map_one _⟩

中文:
定理 one_mem_one
  结论: (1 : P) in (1 : FractionalIdeal S P)
  证明: (mem_one_iff S).mpr ⟨1, map_one _⟩

Depends on / 依赖: map_one, mem_one_iff
-/
theorem one_mem_one : (1 : P) in (1 : FractionalIdeal S P) :=
  (mem_one_iff S).mpr ⟨1, map_one _⟩

variable {S}

/--
theorem `coe_one_eq_coeSubmodule_top` / 定理 `coe_one_eq_coeSubmodule_top`

English:
theorem coe_one_eq_coeSubmodule_top
  statement: ↑(1 : FractionalIdeal S P) = coeSubmodule P (⊤ : Ideal R)
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_one_eq_coeSubmodule_top
  结论: ↑(1 : FractionalIdeal S P) = coeSubmodule P (⊤ : 理想 R)
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_one_eq_coeSubmodule_top : ↑(1 : FractionalIdeal S P) = coeSubmodule P (⊤ : Ideal R) :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: (↑(1 : FractionalIdeal S P) : Submodule R P) = 1
  proof: by
  rw [coe_one_eq_coeSubmodule_top]; rw [coeSubmodule_top]

中文:
定理 coe_one
  结论: (↑(1 : FractionalIdeal S P) : 子模 R P) = 1
  证明: by
  rw [coe_one_eq_coeSubmodule_top]; rw [coeSubmodule_top]

Depends on / 依赖: coeSubmodule_top, coe_one_eq_coeSubmodule_top
-/
theorem coe_one : (↑(1 : FractionalIdeal S P) : Submodule R P) = 1 := by
  rw [coe_one_eq_coeSubmodule_top]; rw [coeSubmodule_top]

section Lattice

/-!
### `Lattice` section

Defines the order on fractional ideals as inclusion of their underlying sets,
and ports the lattice structure on submodules to fractional ideals.
-/


@[simp]
/--
theorem `coe_le_coe` / 定理 `coe_le_coe`

English:
theorem coe_le_coe
  given: {I J : FractionalIdeal S P}
  proof: Iff.rfl

中文:
定理 coe_le_coe
  条件: {I J : FractionalIdeal S P}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem coe_le_coe {I J : FractionalIdeal S P} :
    (I : Submodule R P) <= (J : Submodule R P) ↔ I <= J :=
  Iff.rfl

/--
theorem `zero_le` / 定理 `zero_le`

English:
theorem zero_le
  given: (I : FractionalIdeal S P)
  statement: 0 <= I
  proof: by
  intro x hx
  convert! zero_mem I
  rw [(mem_zero_iff _).mp hx]

中文:
定理 zero_le
  条件: (I : FractionalIdeal S P)
  结论: 0 <= I
  证明: by
  intro x hx
  convert! zero_mem I
  rw [(mem_zero_iff _).mp hx]

Depends on / 依赖: convert, mem_zero_iff, zero_mem
-/
theorem zero_le (I : FractionalIdeal S P) : 0 <= I := by
  intro x hx
  convert! zero_mem I
  rw [(mem_zero_iff _).mp hx]

/--
Instance `orderBot` / 实例 `orderBot`

English:
instance orderBot
  signature: : OrderBot (FractionalIdeal S P) where
  body: 0
  bot_le := zero_le

@[simp]

中文:
实例 orderBot
  签名: : 有底序 (FractionalIdeal S P) where
  定义体: 0
  bot_le := zero_le

@[simp]
-/
instance orderBot : OrderBot (FractionalIdeal S P) where
  bot := 0
  bot_le := zero_le

@[simp]
/--
theorem `bot_eq_zero` / 定理 `bot_eq_zero`

English:
theorem bot_eq_zero
  statement: (⊥ : FractionalIdeal S P) = 0
  proof: rfl

中文:
定理 bot_eq_zero
  结论: (⊥ : FractionalIdeal S P) = 0
  证明: rfl
-/
theorem bot_eq_zero : (⊥ : FractionalIdeal S P) = 0 :=
  rfl

/--
theorem `le_zero_iff` / 定理 `le_zero_iff`

English:
theorem le_zero_iff
  given: {I : FractionalIdeal S P}
  statement: I <= 0 ↔ I = 0
  proof: le_bot_iff

中文:
定理 le_zero_iff
  条件: {I : FractionalIdeal S P}
  结论: I <= 0 ↔ I = 0
  证明: le_bot_iff

Depends on / 依赖: le_bot_iff
-/
theorem le_zero_iff {I : FractionalIdeal S P} : I <= 0 ↔ I = 0 :=
  le_bot_iff

/--
theorem `eq_zero_iff` / 定理 `eq_zero_iff`

English:
theorem eq_zero_iff
  given: {I : FractionalIdeal S P}
  statement: I = 0 ↔ forall x in I, x = (0 : P)
  proof: ⟨fun h x hx => by simpa [h, mem_zero_iff] using hx, fun h =>
    le_bot_iff.mp fun x hx => (mem_zero_iff S).mpr (h x hx)⟩

中文:
定理 eq_zero_iff
  条件: {I : FractionalIdeal S P}
  结论: I = 0 ↔ 对任意 x in I, x = (0 : P)
  证明: ⟨fun h x hx => by simpa [h, mem_zero_iff] using hx, fun h =>
    le_bot_iff.mp fun x hx => (mem_zero_iff S).mpr (h x hx)⟩

Depends on / 依赖: le_bot_iff, le_bot_iff.mp, mem_zero_iff
-/
theorem eq_zero_iff {I : FractionalIdeal S P} : I = 0 ↔ forall x in I, x = (0 : P) :=
  ⟨fun h x hx => by simpa [h, mem_zero_iff] using hx, fun h =>
    le_bot_iff.mp fun x hx => (mem_zero_iff S).mpr (h x hx)⟩

/--
theorem `_root_.IsFractional.sup` / 定理 `_root_.IsFractional.sup`

English:
theorem _root_.IsFractional.sup
  given: {I J : Submodule R P}

中文:
定理 _root_.IsFractional.上确界
  条件: {I J : 子模 R P}
-/
theorem _root_.IsFractional.sup {I J : Submodule R P} :
    IsFractional S I -> IsFractional S J -> IsFractional S (I ⊔ J)
  | ⟨aI, haI, hI⟩, ⟨aJ, haJ, hJ⟩ =>
    ⟨aI * aJ, S.mul_mem haI haJ, fun b hb => by
      rcases mem_sup.mp hb with ⟨bI, hbI, bJ, hbJ, rfl⟩
      rw [smul_add]
      apply isInteger_add
      · rw [mul_smul, smul_comm]
        exact isInteger_smul (hI bI hbI)
      · rw [mul_smul]
        exact isInteger_smul (hJ bJ hbJ)⟩

/--
theorem `_root_.IsFractional.inf_right` / 定理 `_root_.IsFractional.inf_right`

English:
theorem _root_.IsFractional.inf_right
  given: {I : Submodule R P}

中文:
定理 _root_.IsFractional.inf_right
  条件: {I : 子模 R P}
-/
theorem _root_.IsFractional.inf_right {I : Submodule R P} :
    IsFractional S I -> forall J, IsFractional S (I ⊓ J)
  | ⟨aI, haI, hI⟩, J =>
    ⟨aI, haI, fun b hb => by
      rcases mem_inf.mp hb with ⟨hbI, _⟩
      exact hI b hbI⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Min (FractionalIdeal S P)
  body: ⟨fun I J => ⟨I ⊓ J, I.isFractional.inf_right J⟩⟩

@[simp, norm_cast]

中文:
实例 :
  签名: 最小值 (FractionalIdeal S P)
  定义体: ⟨fun I J => ⟨I ⊓ J, I.isFractional.inf_right J⟩⟩

@[simp, norm_cast]

Depends on / 依赖: I.isFractional.inf_right, inf_right, isFractional
-/
instance : Min (FractionalIdeal S P) :=
  ⟨fun I J => ⟨I ⊓ J, I.isFractional.inf_right J⟩⟩

@[simp, norm_cast]
/--
theorem `coe_inf` / 定理 `coe_inf`

English:
theorem coe_inf
  given: (I J : FractionalIdeal S P)
  statement: ↑(I ⊓ J) = (I ⊓ J : Submodule R P)
  proof: rfl

中文:
定理 coe_inf
  条件: (I J : FractionalIdeal S P)
  结论: ↑(I ⊓ J) = (I ⊓ J : 子模 R P)
  证明: rfl
-/
theorem coe_inf (I J : FractionalIdeal S P) : ↑(I ⊓ J) = (I ⊓ J : Submodule R P) :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Max (FractionalIdeal S P)
  body: ⟨fun I J => ⟨I ⊔ J, I.isFractional.sup J.isFractional⟩⟩

@[norm_cast]

中文:
实例 :
  签名: 最大值 (FractionalIdeal S P)
  定义体: ⟨fun I J => ⟨I ⊔ J, I.isFractional.sup J.isFractional⟩⟩

@[norm_cast]

Depends on / 依赖: I.isFractional.sup, J.isFractional, isFractional
-/
instance : Max (FractionalIdeal S P) :=
  ⟨fun I J => ⟨I ⊔ J, I.isFractional.sup J.isFractional⟩⟩

@[norm_cast]
/--
theorem `coe_sup` / 定理 `coe_sup`

English:
theorem coe_sup
  given: (I J : FractionalIdeal S P)
  statement: ↑(I ⊔ J) = (I ⊔ J : Submodule R P)
  proof: rfl

中文:
定理 coe_sup
  条件: (I J : FractionalIdeal S P)
  结论: ↑(I ⊔ J) = (I ⊔ J : 子模 R P)
  证明: rfl
-/
theorem coe_sup (I J : FractionalIdeal S P) : ↑(I ⊔ J) = (I ⊔ J : Submodule R P) :=
  rfl

/--
Instance `lattice` / 实例 `lattice`

English:
instance lattice
  signature: : Lattice (FractionalIdeal S P)
  body: Function.Injective.lattice _ Subtype.coe_injective .rfl .rfl coe_sup coe_inf

中文:
实例 lattice
  签名: : 格 (FractionalIdeal S P)
  定义体: Function.Injective.lattice _ Subtype.coe_injective .rfl .rfl coe_sup coe_inf

Depends on / 依赖: Function, Function.Injective.lattice, Injective, Subtype, Subtype.coe_injective, coe_inf, coe_injective, coe_sup, lattice
-/
instance lattice : Lattice (FractionalIdeal S P) :=
  Function.Injective.lattice _ Subtype.coe_injective .rfl .rfl coe_sup coe_inf

end Lattice

section Semiring

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add (FractionalIdeal S P)
  body: ⟨(· ⊔ ·)⟩

@[simp]

中文:
实例 :
  签名: 加法 (FractionalIdeal S P)
  定义体: ⟨(· ⊔ ·)⟩

@[simp]
-/
instance : Add (FractionalIdeal S P) :=
  ⟨(· ⊔ ·)⟩

@[simp]
/--
theorem `sup_eq_add` / 定理 `sup_eq_add`

English:
theorem sup_eq_add
  given: (I J : FractionalIdeal S P)
  statement: I ⊔ J = I + J
  proof: rfl

@[simp, norm_cast]

中文:
定理 sup_eq_add
  条件: (I J : FractionalIdeal S P)
  结论: I ⊔ J = I + J
  证明: rfl

@[simp, norm_cast]
-/
theorem sup_eq_add (I J : FractionalIdeal S P) : I ⊔ J = I + J :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_add` / 定理 `coe_add`

English:
theorem coe_add
  given: (I J : FractionalIdeal S P)
  statement: (↑(I + J) : Submodule R P) = I + J
  proof: rfl

中文:
定理 coe_add
  条件: (I J : FractionalIdeal S P)
  结论: (↑(I + J) : 子模 R P) = I + J
  证明: rfl
-/
theorem coe_add (I J : FractionalIdeal S P) : (↑(I + J) : Submodule R P) = I + J :=
  rfl

/--
theorem `mem_add` / 定理 `mem_add`

English:
theorem mem_add
  given: (I J : FractionalIdeal S P) (x : P)
  proof: by
  rw [← mem_coe]; rw [coe_add]; rw [Submodule.add_eq_sup]; exact Submodule.mem_sup

@[simp, norm_cast]

中文:
定理 mem_add
  条件: (I J : FractionalIdeal S P) (x : P)
  证明: by
  rw [← mem_coe]; rw [coe_add]; rw [Submodule.add_eq_sup]; exact Submodule.mem_sup

@[simp, norm_cast]

Depends on / 依赖: Submodule, Submodule.add_eq_sup, Submodule.mem_sup, add_eq_sup, coe_add, mem_coe, mem_sup
-/
theorem mem_add (I J : FractionalIdeal S P) (x : P) :
    x in I + J ↔ exists i in I, exists j in J, i + j = x := by
  rw [← mem_coe]; rw [coe_add]; rw [Submodule.add_eq_sup]; exact Submodule.mem_sup

@[simp, norm_cast]
/--
lemma `coeIdeal_inf` / 引理 `coeIdeal_inf`

English:
lemma coeIdeal_inf
  given: [FaithfulSMul R P] (I J : Ideal R)
  proof: by
  apply coeToSubmodule_injective
  exact Submodule.map_inf (Algebra.linearMap R P) (FaithfulSMul.algebraMap_injective R P)

@[simp, norm_cast]

中文:
引理 coeIdeal_inf
  条件: [忠实标量乘法 R P] (I J : 理想 R)
  证明: by
  apply coeToSubmodule_injective
  exact Submodule.map_inf (Algebra.linearMap R P) (FaithfulSMul.algebraMap_injective R P)

@[simp, norm_cast]

Depends on / 依赖: Algebra, Algebra.linearMap, FaithfulSMul, FaithfulSMul.algebraMap_injective, Submodule, Submodule.map_inf, algebraMap_injective, coeToSubmodule_injective, linearMap, map_inf
-/
lemma coeIdeal_inf [FaithfulSMul R P] (I J : Ideal R) :
    (↑(I ⊓ J) : FractionalIdeal S P) = ↑I ⊓ ↑J := by
  apply coeToSubmodule_injective
  exact Submodule.map_inf (Algebra.linearMap R P) (FaithfulSMul.algebraMap_injective R P)

@[simp, norm_cast]
/--
theorem `coeIdeal_sup` / 定理 `coeIdeal_sup`

English:
theorem coeIdeal_sup
  given: (I J : Ideal R)
  statement: ↑(I ⊔ J) = (I + J : FractionalIdeal S P)
  proof: coeToSubmodule_injective coeSubmodule_sup _ _ _

中文:
定理 coeIdeal_sup
  条件: (I J : 理想 R)
  结论: ↑(I ⊔ J) = (I + J : FractionalIdeal S P)
  证明: coeToSubmodule_injective coeSubmodule_sup _ _ _

Depends on / 依赖: coeSubmodule_sup, coeToSubmodule_injective
-/
theorem coeIdeal_sup (I J : Ideal R) : ↑(I ⊔ J) = (I + J : FractionalIdeal S P) :=
coeToSubmodule_injective coeSubmodule_sup _ _ _

/--
theorem `_root_.IsFractional.nsmul` / 定理 `_root_.IsFractional.nsmul`

English:
theorem _root_.IsFractional.nsmul
  given: {I : Submodule R P}

中文:
定理 _root_.IsFractional.nsmul
  条件: {I : 子模 R P}
-/
theorem _root_.IsFractional.nsmul {I : Submodule R P} :
    forall n : Nat, IsFractional S I -> IsFractional S (n • I : Submodule R P)
  | 0, _ => by
    rw [zero_smul]
    convert! ((0 : Ideal R) : FractionalIdeal S P).isFractional
    simp
  | n + 1, h => by
    rw [succ_nsmul]
    exact (IsFractional.nsmul n h).sup h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul Nat (FractionalIdeal S P)
  body: ⟨n • ↑I, I.isFractional.nsmul n⟩

@[norm_cast]

中文:
实例 :
  签名: 标量乘法 自然数 (FractionalIdeal S P)
  定义体: ⟨n • ↑I, I.isFractional.nsmul n⟩

@[norm_cast]

Depends on / 依赖: I.isFractional.nsmul, isFractional
-/
instance : SMul Nat (FractionalIdeal S P) where smul n I := ⟨n • ↑I, I.isFractional.nsmul n⟩

@[norm_cast]
/--
theorem `coe_nsmul` / 定理 `coe_nsmul`

English:
theorem coe_nsmul
  given: (n : Nat) (I : FractionalIdeal S P)
  proof: rfl

中文:
定理 coe_nsmul
  条件: (n : 自然数) (I : FractionalIdeal S P)
  证明: rfl
-/
theorem coe_nsmul (n : Nat) (I : FractionalIdeal S P) :
    (↑(n • I) : Submodule R P) = n • (I : Submodule R P) :=
  rfl

/--
theorem `_root_.IsFractional.mul` / 定理 `_root_.IsFractional.mul`

English:
theorem _root_.IsFractional.mul
  given: {I J : Submodule R P}
  proof: hJ n hn
        rw [mul_smul]; rw [mul_comm m]; rw [← smul_mul_assoc]; rw [← hn']; rw [← Algebra.smul_def]
        apply hI
        exact Submodule.smul_mem _ _ hm
      · intro x y hx hy
        rw [smul_add]
        apply isInteger_add hx hy⟩

中文:
定理 _root_.IsFractional.mul
  条件: {I J : 子模 R P}
  证明: hJ n hn
        rw [mul_smul]; rw [mul_comm m]; rw [← smul_mul_assoc]; rw [← hn']; rw [← Algebra.smul_def]
        apply hI
        exact Submodule.smul_mem _ _ hm
      · intro x y hx hy
        rw [smul_add]
        apply isInteger_add hx hy⟩
-/
theorem _root_.IsFractional.mul {I J : Submodule R P} :
    IsFractional S I -> IsFractional S J -> IsFractional S (I * J : Submodule R P)
  | ⟨aI, haI, hI⟩, ⟨aJ, haJ, hJ⟩ =>
    ⟨aI * aJ, S.mul_mem haI haJ, fun b hb => by
      refine Submodule.mul_induction_on hb ?_ ?_
      · intro m hm n hn
        obtain ⟨n', hn'⟩ := hJ n hn
        rw [mul_smul]; rw [mul_comm m]; rw [← smul_mul_assoc]; rw [← hn']; rw [← Algebra.smul_def]
        apply hI
        exact Submodule.smul_mem _ _ hm
      · intro x y hx hy
        rw [smul_add]
        apply isInteger_add hx hy⟩

/--
theorem `_root_.IsFractional.pow` / 定理 `_root_.IsFractional.pow`

English:
theorem _root_.IsFractional.pow
  given: {I : Submodule R P} (h : IsFractional S I)

中文:
定理 _root_.IsFractional.pow
  条件: {I : 子模 R P} (h : IsFractional S I)

Depends on / 依赖: FractionalIdeal, mul_def
-/
theorem _root_.IsFractional.pow {I : Submodule R P} (h : IsFractional S I) :
    forall n : Nat, IsFractional S (I ^ n : Submodule R P)
  | 0 => isFractional_of_le_one _ (pow_zero _).le
  | n + 1 => (pow_succ I n).symm ▸ (IsFractional.pow h n).mul h

/-- `FractionalIdeal.mul` is the product of two fractional ideals,
used to define the `Mul` instance.

This is only an auxiliary definition: the preferred way of writing `I.mul J` is `I * J`.

Elaborated terms involving `FractionalIdeal` tend to grow quite large,
so by making definitions irreducible, we hope to avoid deep unfolds.
-/
irreducible_def mul (lemma := mul_def') (I J : FractionalIdeal S P) : FractionalIdeal S P :=
  ⟨I * J, I.isFractional.mul J.isFractional⟩

-- local attribute [semireducible] mul
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul (FractionalIdeal S P)
  body: ⟨fun I J => mul I J⟩

@[simp]

中文:
实例 :
  签名: 乘法 (FractionalIdeal S P)
  定义体: ⟨fun I J => mul I J⟩

@[simp]
-/
instance : Mul (FractionalIdeal S P) :=
  ⟨fun I J => mul I J⟩

@[simp]
/--
theorem `mul_eq_mul` / 定理 `mul_eq_mul`

English:
theorem mul_eq_mul
  given: (I J : FractionalIdeal S P)
  statement: mul I J = I * J
  proof: rfl

中文:
定理 mul_eq_mul
  条件: (I J : FractionalIdeal S P)
  结论: mul I J = I * J
  证明: rfl
-/
theorem mul_eq_mul (I J : FractionalIdeal S P) : mul I J = I * J :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `mul_def` / 定理 `mul_def`

English:
theorem mul_def
  given: (I J : FractionalIdeal S P)
  proof: by simp only [← mul_eq_mul, mul_def']

@[simp, norm_cast]

中文:
定理 mul_def
  条件: (I J : FractionalIdeal S P)
  证明: by simp only [← mul_eq_mul, mul_def']

@[simp, norm_cast]

Depends on / 依赖: mul_def, mul_eq_mul
-/
theorem mul_def (I J : FractionalIdeal S P) :
    I * J = ⟨I * J, I.isFractional.mul J.isFractional⟩ := by simp only [← mul_eq_mul, mul_def']

@[simp, norm_cast]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: (I J : FractionalIdeal S P)
  statement: (↑(I * J) : Submodule R P) = I * J
  proof: by
  simp only [mul_def, coe_mk]

@[simp, norm_cast]

中文:
定理 coe_mul
  条件: (I J : FractionalIdeal S P)
  结论: (↑(I * J) : 子模 R P) = I * J
  证明: by
  simp only [mul_def, coe_mk]

@[simp, norm_cast]

Depends on / 依赖: coe_mk, mul_def
-/
theorem coe_mul (I J : FractionalIdeal S P) : (↑(I * J) : Submodule R P) = I * J := by
  simp only [mul_def, coe_mk]

@[simp, norm_cast]
/--
theorem `coeIdeal_mul` / 定理 `coeIdeal_mul`

English:
theorem coeIdeal_mul
  given: (I J : Ideal R)
  statement: (↑(I * J) : FractionalIdeal S P) = I * J
  proof: by
  simp only [mul_def]
  exact coeToSubmodule_injective (coeSubmodule_mul _ _ _)

中文:
定理 coeIdeal_mul
  条件: (I J : 理想 R)
  结论: (↑(I * J) : FractionalIdeal S P) = I * J
  证明: by
  simp only [mul_def]
  exact coeToSubmodule_injective (coeSubmodule_mul _ _ _)

Depends on / 依赖: coeSubmodule_mul, coeToSubmodule_injective, mul_def
-/
theorem coeIdeal_mul (I J : Ideal R) : (↑(I * J) : FractionalIdeal S P) = I * J := by
  simp only [mul_def]
  exact coeToSubmodule_injective (coeSubmodule_mul _ _ _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulLeftMono (FractionalIdeal S P)
  body: by simpa only [mul_def] using! mul_le.mpr fun x hx y hy => mul_mem_mul hx (h hy)

中文:
实例 :
  签名: MulLeftMono (FractionalIdeal S P)
  定义体: by simpa only [mul_def] using! mul_le.mpr fun x hx y hy => mul_mem_mul hx (h hy)

Depends on / 依赖: mul_def, mul_le, mul_le.mpr, mul_mem_mul
-/
instance : MulLeftMono (FractionalIdeal S P) where
  elim I J J' h := by simpa only [mul_def] using! mul_le.mpr fun x hx y hy => mul_mem_mul hx (h hy)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulRightMono (FractionalIdeal S P)
  body: by simpa only [mul_def] using! mul_le.mpr fun x hx y hy => mul_mem_mul (h hx) hy

中文:
实例 :
  签名: MulRightMono (FractionalIdeal S P)
  定义体: by simpa only [mul_def] using! mul_le.mpr fun x hx y hy => mul_mem_mul (h hx) hy

Depends on / 依赖: mul_def, mul_le, mul_le.mpr, mul_mem_mul
-/
instance : MulRightMono (FractionalIdeal S P) where
  elim I J J' h := by simpa only [mul_def] using! mul_le.mpr fun x hx y hy => mul_mem_mul (h hx) hy

/--
theorem `mul_mem_mul` / 定理 `mul_mem_mul`

English:
theorem mul_mem_mul
  given: {I J : FractionalIdeal S P} {i j : P} (hi : i in I) (hj : j in J)
  proof: by
  simp only [mul_def]
  exact Submodule.mul_mem_mul hi hj

中文:
定理 mul_mem_mul
  条件: {I J : FractionalIdeal S P} {i j : P} (hi : i in I) (hj : j in J)
  证明: by
  simp only [mul_def]
  exact Submodule.mul_mem_mul hi hj

Depends on / 依赖: Submodule, Submodule.mul_mem_mul, mul_def, mul_mem_mul
-/
theorem mul_mem_mul {I J : FractionalIdeal S P} {i j : P} (hi : i in I) (hj : j in J) :
    i * j in I * J := by
  simp only [mul_def]
  exact Submodule.mul_mem_mul hi hj

/--
theorem `mul_le` / 定理 `mul_le`

English:
theorem mul_le
  given: {I J K : FractionalIdeal S P}
  statement: I * J <= K ↔ forall i in I, forall j in J, i * j in K
  proof: by
  simp only [mul_def]
  exact Submodule.mul_le

中文:
定理 mul_le
  条件: {I J K : FractionalIdeal S P}
  结论: I * J <= K ↔ 对任意 i in I, 对任意 j in J, i * j in K
  证明: by
  simp only [mul_def]
  exact Submodule.mul_le

Depends on / 依赖: Submodule, Submodule.mul_le, mul_def, mul_le
-/
theorem mul_le {I J K : FractionalIdeal S P} : I * J <= K ↔ forall i in I, forall j in J, i * j in K := by
  simp only [mul_def]
  exact Submodule.mul_le

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Pow (FractionalIdeal S P) Nat
  body: ⟨fun I n => ⟨(I : Submodule R P) ^ n, I.isFractional.pow n⟩⟩

@[simp, norm_cast]

中文:
实例 :
  签名: 幂 (FractionalIdeal S P) 自然数
  定义体: ⟨fun I n => ⟨(I : Submodule R P) ^ n, I.isFractional.pow n⟩⟩

@[simp, norm_cast]

Depends on / 依赖: I.isFractional.pow, Submodule, isFractional
-/
instance : Pow (FractionalIdeal S P) Nat :=
  ⟨fun I n => ⟨(I : Submodule R P) ^ n, I.isFractional.pow n⟩⟩

@[simp, norm_cast]
/--
theorem `coe_pow` / 定理 `coe_pow`

English:
theorem coe_pow
  given: (I : FractionalIdeal S P) (n : Nat)
  statement: ↑(I ^ n) = (I : Submodule R P) ^ n
  proof: rfl

@[elab_as_elim]

中文:
定理 coe_pow
  条件: (I : FractionalIdeal S P) (n : 自然数)
  结论: ↑(I ^ n) = (I : 子模 R P) ^ n
  证明: rfl

@[elab_as_elim]
-/
theorem coe_pow (I : FractionalIdeal S P) (n : Nat) : ↑(I ^ n) = (I : Submodule R P) ^ n :=
  rfl

@[elab_as_elim]
/--
theorem `mul_induction_on` / 定理 `mul_induction_on`

English:
theorem mul_induction_on
  statement: {I J : FractionalIdeal S P} {C : P -> Prop} {r : P}
  proof: by
  simp only [mul_def] at hr
  exact Submodule.mul_induction_on hr hm ha

中文:
定理 mul_induction_on
  结论: {I J : FractionalIdeal S P} {C : P -> 命题} {r : P}
  证明: by
  simp only [mul_def] at hr
  exact Submodule.mul_induction_on hr hm ha
-/
protected theorem mul_induction_on {I J : FractionalIdeal S P} {C : P -> Prop} {r : P}
    (hr : r in I * J) (hm : forall i in I, forall j in J, C (i * j)) (ha : forall x y, C x -> C y -> C (x + y)) :
    C r := by
  simp only [mul_def] at hr
  exact Submodule.mul_induction_on hr hm ha

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NatCast (FractionalIdeal S P)
  body: ⟨Nat.unaryCast⟩

中文:
实例 :
  签名: 自然数嵌入 (FractionalIdeal S P)
  定义体: ⟨Nat.unaryCast⟩

Depends on / 依赖: Nat.unaryCast, unaryCast
-/
instance : NatCast (FractionalIdeal S P) :=
  ⟨Nat.unaryCast⟩

/--
theorem `coe_natCast` / 定理 `coe_natCast`

English:
theorem coe_natCast
  given: (n : Nat)
  statement: ((n : FractionalIdeal S P) : Submodule R P) = n
  proof: show ((n.unaryCast : FractionalIdeal S P) : Submodule R P) = n
  by induction n <;> simp [*, Nat.unaryCast]

中文:
定理 coe_natCast
  条件: (n : 自然数)
  结论: ((n : FractionalIdeal S P) : 子模 R P) = n
  证明: show ((n.unaryCast : FractionalIdeal S P) : Submodule R P) = n
  by induction n <;> simp [*, Nat.unaryCast]

Depends on / 依赖: FractionalIdeal, Nat.unaryCast, Submodule, n.unaryCast, unaryCast
-/
theorem coe_natCast (n : Nat) : ((n : FractionalIdeal S P) : Submodule R P) = n :=
  show ((n.unaryCast : FractionalIdeal S P) : Submodule R P) = n
  by induction n <;> simp [*, Nat.unaryCast]

/--
Instance `commSemiring` / 实例 `commSemiring`

English:
instance commSemiring
  signature: : CommSemiring (FractionalIdeal S P)
  body: Function.Injective.commSemiring _ Subtype.coe_injective coe_zero coe_one coe_add coe_mul
    (fun _ _ => coe_nsmul _ _) coe_pow coe_natCast

中文:
实例 commSemiring
  签名: : 交换半环 (FractionalIdeal S P)
  定义体: Function.Injective.commSemiring _ Subtype.coe_injective coe_zero coe_one coe_add coe_mul
    (fun _ _ => coe_nsmul _ _) coe_pow coe_natCast

Depends on / 依赖: Function, Function.Injective.commSemiring, Injective, Subtype, Subtype.coe_injective, coe_add, coe_injective, coe_mul, coe_natCast, coe_nsmul, coe_one, coe_pow, coe_zero, commSemiring
-/
instance commSemiring : CommSemiring (FractionalIdeal S P) :=
  Function.Injective.commSemiring _ Subtype.coe_injective coe_zero coe_one coe_add coe_mul
    (fun _ _ => coe_nsmul _ _) coe_pow coe_natCast

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CanonicallyOrderedAdd (FractionalIdeal S P)
  body: ⟨_, (sup_eq_right.mpr h).symm⟩
  le_add_self _ _ := le_sup_right
  le_self_add _ _ := le_sup_left

中文:
实例 :
  签名: 典范有序加法 (FractionalIdeal S P)
  定义体: ⟨_, (sup_eq_right.mpr h).symm⟩
  le_add_self _ _ := le_sup_right
  le_self_add _ _ := le_sup_left

Depends on / 依赖: sup_eq_right, sup_eq_right.mpr
-/
instance : CanonicallyOrderedAdd (FractionalIdeal S P) where
  exists_add_of_le h := ⟨_, (sup_eq_right.mpr h).symm⟩
  le_add_self _ _ := le_sup_right
  le_self_add _ _ := le_sup_left

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsOrderedRing (FractionalIdeal S P)
  body: CanonicallyOrderedAdd.toIsOrderedRing

中文:
实例 :
  签名: 是Ordered环 (FractionalIdeal S P)
  定义体: CanonicallyOrderedAdd.toIsOrderedRing

Depends on / 依赖: CanonicallyOrderedAdd, CanonicallyOrderedAdd.toIsOrderedRing, toIsOrderedRing
-/
instance : IsOrderedRing (FractionalIdeal S P) :=
  CanonicallyOrderedAdd.toIsOrderedRing

end Semiring

variable (S P)

/-- `FractionalIdeal.coeToSubmodule` as a bundled `RingHom`. -/
@[simps]
/--
Definition of `coeSubmoduleHom` / `coeSubmoduleHom` 的定义

English:
definition coeSubmoduleHom
  signature: : FractionalIdeal S P ->+* Submodule R P where
  body: coeToSubmodule
  map_one' := coe_one
  map_mul' := coe_mul
  map_zero' := coe_zero (S := S)
  map_add' := coe_add

中文:
定义 coeSubmoduleHom
  签名: : FractionalIdeal S P ->+* 子模 R P where
  定义体: coeToSubmodule
  map_one' := coe_one
  map_mul' := coe_mul
  map_zero' := coe_zero (S := S)
  map_add' := coe_add

Depends on / 依赖: coeToSubmodule
-/
def coeSubmoduleHom : FractionalIdeal S P ->+* Submodule R P where
  toFun := coeToSubmodule
  map_one' := coe_one
  map_mul' := coe_mul
  map_zero' := coe_zero (S := S)
  map_add' := coe_add

variable {S P}

section Order

/--
theorem `coeIdeal_le_one` / 定理 `coeIdeal_le_one`

English:
theorem coeIdeal_le_one
  given: {I : Ideal R}
  statement: (I : FractionalIdeal S P) <= 1
  proof: fun _ hx =>
  let ⟨y, _, hy⟩ := (mem_coeIdeal S).mp hx
  (mem_one_iff S).mpr ⟨y, hy⟩

中文:
定理 coeIdeal_le_one
  条件: {I : 理想 R}
  结论: (I : FractionalIdeal S P) <= 1
  证明: fun _ hx =>
  let ⟨y, _, hy⟩ := (mem_coeIdeal S).mp hx
  (mem_one_iff S).mpr ⟨y, hy⟩
-/
theorem coeIdeal_le_one {I : Ideal R} : (I : FractionalIdeal S P) <= 1 := fun _ hx =>
  let ⟨y, _, hy⟩ := (mem_coeIdeal S).mp hx
  (mem_one_iff S).mpr ⟨y, hy⟩

/--
theorem `le_one_iff_exists_coeIdeal` / 定理 `le_one_iff_exists_coeIdeal`

English:
theorem le_one_iff_exists_coeIdeal
  given: {J : FractionalIdeal S P}
  proof: by
  constructor
  · intro hJ
    refine ⟨⟨⟨⟨{ x : R | algebraMap R P x in J }, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · intro a b ha hb
      rw [mem_ofPred]; rw [map_add]
      exact J.val.add_mem ha hb
    · rw [mem_ofPred, map_zero]
      exact J.zero_mem
    · intro c x hx
      rw [smul_eq_mul]; rw [mem_ofPred]; rw [map_mul]; rw [← Algebra.smul_def]
      exact J.val.smul_mem c hx
    · ext x
      constructor
      · rintro ⟨y, hy, eq_y⟩
        rwa [← eq_y]
      · intro hx
        obtain ⟨y, rfl⟩ := (mem_one_iff S).mp (hJ hx)
        exact mem_ofPred.mpr ⟨y, hx, rfl⟩
  · rintro ⟨I, hI⟩
    rw [← hI]
    apply coeIdeal_le_one

@[simp]

中文:
定理 le_one_iff_存在_coeIdeal
  条件: {J : FractionalIdeal S P}
  证明: by
  constructor
  · intro hJ
    refine ⟨⟨⟨⟨{ x : R | algebraMap R P x in J }, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · intro a b ha hb
      rw [mem_ofPred]; rw [map_add]
      exact J.val.add_mem ha hb
    · rw [mem_ofPred, map_zero]
      exact J.zero_mem
    · intro c x hx
      rw [smul_eq_mul]; rw [mem_ofPred]; rw [map_mul]; rw [← Algebra.smul_def]
      exact J.val.smul_mem c hx
    · ext x
      constructor
      · rintro ⟨y, hy, eq_y⟩
        rwa [← eq_y]
      · intro hx
        obtain ⟨y, rfl⟩ := (mem_one_iff S).mp (hJ hx)
        exact mem_ofPred.mpr ⟨y, hx, rfl⟩
  · rintro ⟨I, hI⟩
    rw [← hI]
    apply coeIdeal_le_one

@[simp]

Depends on / 依赖: Algebra, Algebra.smul_def, J.val.add_mem, J.val.smul_mem, J.zero_mem, add_mem, algebraMap, eq_y, map_add, map_mul, map_zero, mem_ofPred, mem_ofPred.mpr, mem_one_iff, smul_def, smul_eq_mul, smul_mem, zero_mem
-/
theorem le_one_iff_exists_coeIdeal {J : FractionalIdeal S P} :
    J <= (1 : FractionalIdeal S P) ↔ exists I : Ideal R, ↑I = J := by
  constructor
  · intro hJ
    refine ⟨⟨⟨⟨{ x : R | algebraMap R P x in J }, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · intro a b ha hb
      rw [mem_ofPred]; rw [map_add]
      exact J.val.add_mem ha hb
    · rw [mem_ofPred, map_zero]
      exact J.zero_mem
    · intro c x hx
      rw [smul_eq_mul]; rw [mem_ofPred]; rw [map_mul]; rw [← Algebra.smul_def]
      exact J.val.smul_mem c hx
    · ext x
      constructor
      · rintro ⟨y, hy, eq_y⟩
        rwa [← eq_y]
      · intro hx
        obtain ⟨y, rfl⟩ := (mem_one_iff S).mp (hJ hx)
        exact mem_ofPred.mpr ⟨y, hx, rfl⟩
  · rintro ⟨I, hI⟩
    rw [← hI]
    apply coeIdeal_le_one

@[simp]
/--
theorem `one_le` / 定理 `one_le`

English:
theorem one_le
  given: {I : FractionalIdeal S P}
  statement: 1 <= I ↔ (1 : P) in I
  proof: by
  rw [← coe_le_coe]; rw [coe_one]; rw [Submodule.one_le]; rw [mem_coe]

中文:
定理 one_le
  条件: {I : FractionalIdeal S P}
  结论: 1 <= I ↔ (1 : P) in I
  证明: by
  rw [← coe_le_coe]; rw [coe_one]; rw [Submodule.one_le]; rw [mem_coe]

Depends on / 依赖: Submodule, Submodule.one_le, coe_le_coe, coe_one, finishing, mem_coe, one_le, resolved, tactic
-/
theorem one_le {I : FractionalIdeal S P} : 1 <= I ↔ (1 : P) in I := by
  rw [← coe_le_coe]; rw [coe_one]; rw [Submodule.one_le]; rw [mem_coe]

variable (S P)

/-- `coeIdealHom (S : Submonoid R) P` is `(↑) : Ideal R → FractionalIdeal S P` as a ring hom -/
@[simps]
/--
Definition of `coeIdealHom` / `coeIdealHom` 的定义

English:
definition coeIdealHom
  signature: : Ideal R ->+* FractionalIdeal S P where
  body: coeIdeal
  map_add' := coeIdeal_sup
  map_mul' := coeIdeal_mul
  map_one' := by rw [Ideal.one_eq_top, coeIdeal_top]
  map_zero' := coeIdeal_bot

中文:
定义 coeIdealHom
  签名: : 理想 R ->+* FractionalIdeal S P where
  定义体: coeIdeal
  map_add' := coeIdeal_sup
  map_mul' := coeIdeal_mul
  map_one' := by rw [Ideal.one_eq_top, coeIdeal_top]
  map_zero' := coeIdeal_bot

Depends on / 依赖: coeIdeal
-/
def coeIdealHom : Ideal R ->+* FractionalIdeal S P where
  toFun := coeIdeal
  map_add' := coeIdeal_sup
  map_mul' := coeIdeal_mul
  map_one' := by rw [Ideal.one_eq_top, coeIdeal_top]
  map_zero' := coeIdeal_bot

/--
theorem `coeIdeal_pow` / 定理 `coeIdeal_pow`

English:
theorem coeIdeal_pow
  given: (I : Ideal R) (n : Nat)
  statement: ↑(I ^ n) = (I : FractionalIdeal S P) ^ n
  proof: (coeIdealHom S P).map_pow _ n

中文:
定理 coeIdeal_pow
  条件: (I : 理想 R) (n : 自然数)
  结论: ↑(I ^ n) = (I : FractionalIdeal S P) ^ n
  证明: (coeIdealHom S P).map_pow _ n

Depends on / 依赖: coeIdealHom, map_pow
-/
theorem coeIdeal_pow (I : Ideal R) (n : Nat) : ↑(I ^ n) = (I : FractionalIdeal S P) ^ n :=
  (coeIdealHom S P).map_pow _ n

/--
theorem `coeIdeal_finprod` / 定理 `coeIdeal_finprod`

English:
theorem coeIdeal_finprod
  statement: [IsLocalization S P] {α : Sort*} {f : α -> Ideal R}
  proof: MonoidHom.map_finprod_of_injective (coeIdealHom S P).toMonoidHom (coeIdeal_injective' hS) f

中文:
定理 coeIdeal_finprod
  结论: [是Localization S P] {α : 类型层*} {f : α -> 理想 R}
  证明: MonoidHom.map_finprod_of_injective (coeIdealHom S P).toMonoidHom (coeIdeal_injective' hS) f

Depends on / 依赖: MonoidHom, MonoidHom.map_finprod_of_injective, coeIdealHom, coeIdeal_injective, map_finprod_of_injective, toMonoidHom
-/
theorem coeIdeal_finprod [IsLocalization S P] {α : Sort*} {f : α -> Ideal R}
    (hS : S <= nonZeroDivisors R) :
    ((∏ᶠ a : α, f a : Ideal R) : FractionalIdeal S P) = ∏ᶠ a : α, (f a : FractionalIdeal S P) :=
  MonoidHom.map_finprod_of_injective (coeIdealHom S P).toMonoidHom (coeIdeal_injective' hS) f

end Order

section FG

variable {R : Type*} [CommRing R] [IsDomain R] {S : Submonoid R}
variable {P : Type*} [Nontrivial P] [CommRing P] [Algebra R P] [Module.IsTorsionFree R P]

/--
lemma `fg_of_isNoetherianRing` / 引理 `fg_of_isNoetherianRing`

English:
lemma fg_of_isNoetherianRing
  given: [hR : IsNoetherianRing R] (hS : S <= R⁰) (I : FractionalIdeal S P)
  proof: by
  have := hR.noetherian I.num
  rw [← Module.Finite.iff_fg] at this ⊢
  exact .equiv (I.equivNum <| coe_ne_zero ⟨(I.den : R), hS (SetLike.coe_mem I.den)⟩).symm

中文:
引理 fg_of_isNoetherianRing
  条件: [hR : 是Noether环 R] (hS : S <= R⁰) (I : FractionalIdeal S P)
  证明: by
  have := hR.noetherian I.num
  rw [← Module.Finite.iff_fg] at this ⊢
  exact .equiv (I.equivNum <| coe_ne_zero ⟨(I.den : R), hS (SetLike.coe_mem I.den)⟩).symm

Depends on / 依赖: Finite, I.den, I.equivNum, I.num, Module, Module.Finite.iff_fg, SetLike, SetLike.coe_mem, coe_mem, coe_ne_zero, equivNum, hR.noetherian, iff_fg, noetherian
-/
lemma fg_of_isNoetherianRing [hR : IsNoetherianRing R] (hS : S <= R⁰) (I : FractionalIdeal S P) :
    FG I.coeToSubmodule := by
  have := hR.noetherian I.num
  rw [← Module.Finite.iff_fg] at this ⊢
  exact .equiv (I.equivNum <| coe_ne_zero ⟨(I.den : R), hS (SetLike.coe_mem I.den)⟩).symm

end FG

end FractionalIdeal
