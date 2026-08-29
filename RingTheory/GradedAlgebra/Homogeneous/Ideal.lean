/-
Copyright (c) 2021 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.Finsupp.SumProd
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Basic
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Submodule

/-!
# Homogeneous ideals of a graded algebra

This file defines homogeneous ideals of `GradedRing 𝒜` where `𝒜 : ι → Submodule R A` and
operations on them.

## Main definitions

For any `I : Ideal A`:
* `Ideal.IsHomogeneous 𝒜 I`: The property that an ideal is closed under `GradedRing.proj`.
* `HomogeneousIdeal 𝒜`: The structure extending ideals which satisfy `Ideal.IsHomogeneous`.
* `Ideal.homogeneousCore I 𝒜`: The largest homogeneous ideal smaller than `I`.
* `Ideal.homogeneousHull I 𝒜`: The smallest homogeneous ideal larger than `I`.

## Main statements

* `HomogeneousIdeal.completeLattice`: `Ideal.IsHomogeneous` is preserved by `⊥`, `⊤`, `⊔`, `⊓`,
  `⨆`, `⨅`, and so the subtype of homogeneous ideals inherits a complete lattice structure.
* `Ideal.homogeneousCore.gi`: `Ideal.homogeneousCore` forms a Galois insertion with coercion.
* `Ideal.homogeneousHull.gi`: `Ideal.homogeneousHull` forms a Galois insertion with coercion.

## Implementation notes

We introduce `Ideal.homogeneousCore'` earlier than might be expected so that we can get access
to `Ideal.IsHomogeneous.iff_exists` as quickly as possible.

## Tags

graded algebra, homogeneous
-/

@[expose] public section

open SetLike DirectSum Set
open scoped Pointwise

variable {ι σ A : Type*}

section HomogeneousDef

variable [Semiring A]
variable [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι -> σ)
variable [DecidableEq ι] [AddMonoid ι] [GradedRing 𝒜]
variable (I : Ideal A)

/--
Definition of `Ideal.IsHomogeneous` / `Ideal.IsHomogeneous` 的定义

English:
abbreviation Ideal.IsHomogeneous
  signature: : Prop
  body: Submodule.IsHomogeneous I 𝒜

中文:
缩写 理想.IsHomogeneous
  签名: : 命题
  定义体: Submodule.IsHomogeneous I 𝒜

Depends on / 依赖: IsHomogeneous, Submodule, Submodule.IsHomogeneous
-/
abbrev Ideal.IsHomogeneous : Prop := Submodule.IsHomogeneous I 𝒜

/--
theorem `Ideal.IsHomogeneous.mem_iff` / 定理 `Ideal.IsHomogeneous.mem_iff`

English:
theorem Ideal.IsHomogeneous.mem_iff
  given: {I} (hI : Ideal.IsHomogeneous 𝒜 I) {x}
  proof: AddSubmonoidClass.IsHomogeneous.mem_iff 𝒜 _ hI

中文:
定理 理想.IsHomogeneous.mem_iff
  条件: {I} (hI : 理想.IsHomogeneous 𝒜 I) {x}
  证明: AddSubmonoidClass.IsHomogeneous.mem_iff 𝒜 _ hI

Depends on / 依赖: AddSubmonoidClass, AddSubmonoidClass.IsHomogeneous.mem_iff, IsHomogeneous, mem_iff
-/
theorem Ideal.IsHomogeneous.mem_iff {I} (hI : Ideal.IsHomogeneous 𝒜 I) {x} :
    x in I ↔ forall i, (decompose 𝒜 x i : A) in I :=
  AddSubmonoidClass.IsHomogeneous.mem_iff 𝒜 _ hI

/--
Definition of `HomogeneousIdeal` / `HomogeneousIdeal` 的定义

English:
abbreviation HomogeneousIdeal
  body: HomogeneousSubmodule 𝒜 𝒜

中文:
缩写 HomogeneousIdeal
  定义体: HomogeneousSubmodule 𝒜 𝒜

Depends on / 依赖: HomogeneousSubmodule
-/
abbrev HomogeneousIdeal := HomogeneousSubmodule 𝒜 𝒜

variable {𝒜}

/--
Definition of `HomogeneousIdeal.toIdeal` / `HomogeneousIdeal.toIdeal` 的定义

English:
abbreviation HomogeneousIdeal.toIdeal
  signature: (I : HomogeneousIdeal 𝒜)
  body: I.toSubmodule

中文:
缩写 HomogeneousIdeal.toIdeal
  签名: (I : HomogeneousIdeal 𝒜)
  定义体: I.toSubmodule

Depends on / 依赖: I.toSubmodule, toSubmodule
-/
abbrev HomogeneousIdeal.toIdeal (I : HomogeneousIdeal 𝒜) : Ideal A :=
  I.toSubmodule

/--
lemma `coe_toIdeal` / 引理 `coe_toIdeal`

English:
lemma coe_toIdeal
  given: (I : HomogeneousIdeal 𝒜)
  statement: (I.toIdeal : Set A) = I
  proof: rfl

中文:
引理 coe_toIdeal
  条件: (I : HomogeneousIdeal 𝒜)
  结论: (I.toIdeal : 集合 A) = I
  证明: rfl
-/
@[simp] lemma coe_toIdeal (I : HomogeneousIdeal 𝒜) : (I.toIdeal : Set A) = I := rfl

/--
theorem `HomogeneousIdeal.isHomogeneous` / 定理 `HomogeneousIdeal.isHomogeneous`

English:
theorem HomogeneousIdeal.isHomogeneous
  given: (I : HomogeneousIdeal 𝒜)
  proof: I.is_homogeneous'

中文:
定理 HomogeneousIdeal.isHomogeneous
  条件: (I : HomogeneousIdeal 𝒜)
  证明: I.is_homogeneous'

Depends on / 依赖: I.is_homogeneous, is_homogeneous
-/
theorem HomogeneousIdeal.isHomogeneous (I : HomogeneousIdeal 𝒜) :
    I.toIdeal.IsHomogeneous 𝒜 := I.is_homogeneous'

/--
theorem `HomogeneousIdeal.toIdeal_injective` / 定理 `HomogeneousIdeal.toIdeal_injective`

English:
theorem HomogeneousIdeal.toIdeal_injective
  proof: HomogeneousSubmodule.toSubmodule_injective 𝒜 𝒜

中文:
定理 HomogeneousIdeal.toIdeal_injective
  证明: HomogeneousSubmodule.toSubmodule_injective 𝒜 𝒜

Depends on / 依赖: HomogeneousSubmodule, HomogeneousSubmodule.toSubmodule_injective, toSubmodule_injective
-/
theorem HomogeneousIdeal.toIdeal_injective :
    Function.Injective (HomogeneousIdeal.toIdeal : HomogeneousIdeal 𝒜 -> Ideal A) :=
  HomogeneousSubmodule.toSubmodule_injective 𝒜 𝒜

/--
lemma `toIdeal_le_toIdeal_iff` / 引理 `toIdeal_le_toIdeal_iff`

English:
lemma toIdeal_le_toIdeal_iff
  given: {I J : HomogeneousIdeal 𝒜}
  proof: Iff.rfl

中文:
引理 toIdeal_le_toIdeal_iff
  条件: {I J : HomogeneousIdeal 𝒜}
  证明: Iff.rfl
-/
@[simp] lemma toIdeal_le_toIdeal_iff {I J : HomogeneousIdeal 𝒜} :
    I.toIdeal <= J.toIdeal ↔ I <= J := Iff.rfl

/--
Instance `HomogeneousIdeal.setLike` / 实例 `HomogeneousIdeal.setLike`

English:
instance HomogeneousIdeal.setLike
  signature: : SetLike (HomogeneousIdeal 𝒜) A
  body: HomogeneousSubmodule.setLike 𝒜 𝒜

中文:
实例 HomogeneousIdeal.setLike
  签名: : 集合状 (HomogeneousIdeal 𝒜) A
  定义体: HomogeneousSubmodule.setLike 𝒜 𝒜

Depends on / 依赖: HomogeneousSubmodule, HomogeneousSubmodule.setLike, setLike
-/
instance HomogeneousIdeal.setLike : SetLike (HomogeneousIdeal 𝒜) A :=
  HomogeneousSubmodule.setLike 𝒜 𝒜

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (HomogeneousIdeal 𝒜)
  body: .ofSetLike (HomogeneousIdeal 𝒜) A

@[ext]

中文:
实例 :
  签名: 偏序 (HomogeneousIdeal 𝒜)
  定义体: .ofSetLike (HomogeneousIdeal 𝒜) A

@[ext]

Depends on / 依赖: HomogeneousIdeal, ofSetLike
-/
instance : PartialOrder (HomogeneousIdeal 𝒜) := .ofSetLike (HomogeneousIdeal 𝒜) A

@[ext]
/--
theorem `HomogeneousIdeal.ext` / 定理 `HomogeneousIdeal.ext`

English:
theorem HomogeneousIdeal.ext
  given: {I J : HomogeneousIdeal 𝒜} (h : I.toIdeal = J.toIdeal)
  statement: I = J
  proof: HomogeneousIdeal.toIdeal_injective h

中文:
定理 HomogeneousIdeal.ext
  条件: {I J : HomogeneousIdeal 𝒜} (h : I.toIdeal = J.toIdeal)
  结论: I = J
  证明: HomogeneousIdeal.toIdeal_injective h

Depends on / 依赖: HomogeneousIdeal, HomogeneousIdeal.toIdeal_injective, toIdeal_injective
-/
theorem HomogeneousIdeal.ext {I J : HomogeneousIdeal 𝒜} (h : I.toIdeal = J.toIdeal) : I = J :=
  HomogeneousIdeal.toIdeal_injective h

/--
theorem `HomogeneousIdeal.ext'` / 定理 `HomogeneousIdeal.ext'`

English:
theorem HomogeneousIdeal.ext'
  given: {I J : HomogeneousIdeal 𝒜} (h : forall i, forall x in 𝒜 i, x in I ↔ x in J)
  proof: HomogeneousSubmodule.ext' 𝒜 𝒜 h

@[simp high]

中文:
定理 HomogeneousIdeal.ext'
  条件: {I J : HomogeneousIdeal 𝒜} (h : 对任意 i, 对任意 x in 𝒜 i, x in I ↔ x in J)
  证明: HomogeneousSubmodule.ext' 𝒜 𝒜 h

@[simp high]

Depends on / 依赖: HomogeneousSubmodule, HomogeneousSubmodule.ext
-/
theorem HomogeneousIdeal.ext' {I J : HomogeneousIdeal 𝒜} (h : forall i, forall x in 𝒜 i, x in I ↔ x in J) :
    I = J := HomogeneousSubmodule.ext' 𝒜 𝒜 h

@[simp high]
/--
theorem `HomogeneousIdeal.mem_iff` / 定理 `HomogeneousIdeal.mem_iff`

English:
theorem HomogeneousIdeal.mem_iff
  given: {I : HomogeneousIdeal 𝒜} {x : A}
  statement: x in I.toIdeal ↔ x in I
  proof: Iff.rfl

中文:
定理 HomogeneousIdeal.mem_iff
  条件: {I : HomogeneousIdeal 𝒜} {x : A}
  结论: x in I.toIdeal ↔ x in I
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem HomogeneousIdeal.mem_iff {I : HomogeneousIdeal 𝒜} {x : A} : x in I.toIdeal ↔ x in I :=
  Iff.rfl

end HomogeneousDef

section HomogeneousCore

variable [Semiring A]
variable [SetLike σ A] (𝒜 : ι -> σ)
variable (I : Ideal A)

/--
Definition of `Ideal.homogeneousCore'` / `Ideal.homogeneousCore'` 的定义

English:
definition Ideal.homogeneousCore'
  signature: (I : Ideal A)
  body: Ideal.span ((↑) '' (((↑) : Subtype (SetLike.IsHomogeneousElem 𝒜) -> A) ⁻¹' I))

中文:
定义 理想.homogeneousCore'
  签名: (I : 理想 A)
  定义体: Ideal.span ((↑) '' (((↑) : Subtype (SetLike.IsHomogeneousElem 𝒜) -> A) ⁻¹' I))

Depends on / 依赖: Ideal.span, IsHomogeneousElem, SetLike, SetLike.IsHomogeneousElem, Subtype
-/
def Ideal.homogeneousCore' (I : Ideal A) : Ideal A :=
  Ideal.span ((↑) '' (((↑) : Subtype (SetLike.IsHomogeneousElem 𝒜) -> A) ⁻¹' I))

/--
theorem `Ideal.homogeneousCore'_mono` / 定理 `Ideal.homogeneousCore'_mono`

English:
theorem Ideal.homogeneousCore'_mono
  statement: Monotone (Ideal.homogeneousCore' 𝒜)
  proof: fun _ _ I_le_J => Ideal.span_mono Set.image_mono fun _ => @I_le_J _

中文:
定理 理想.homogeneousCore'_mono
  结论: 递增 (理想.homogeneousCore' 𝒜)
  证明: fun _ _ I_le_J => Ideal.span_mono Set.image_mono fun _ => @I_le_J _
-/
theorem Ideal.homogeneousCore'_mono : Monotone (Ideal.homogeneousCore' 𝒜) :=
fun _ _ I_le_J => Ideal.span_mono Set.image_mono fun _ => @I_le_J _

/--
theorem `Ideal.homogeneousCore'_le` / 定理 `Ideal.homogeneousCore'_le`

English:
theorem Ideal.homogeneousCore'_le
  statement: I.homogeneousCore' 𝒜 <= I
  proof: Ideal.span_le.2 image_preimage_subset _ _

中文:
定理 理想.homogeneousCore'_le
  结论: I.homogeneousCore' 𝒜 <= I
  证明: Ideal.span_le.2 image_preimage_subset _ _
-/
theorem Ideal.homogeneousCore'_le : I.homogeneousCore' 𝒜 <= I :=
Ideal.span_le.2 image_preimage_subset _ _

end HomogeneousCore

section IsHomogeneousIdealDefs

variable [Semiring A]
variable [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι -> σ)
variable [DecidableEq ι] [AddMonoid ι] [GradedRing 𝒜]
variable (I : Ideal A)

/--
theorem `Ideal.isHomogeneous_iff_forall_subset` / 定理 `Ideal.isHomogeneous_iff_forall_subset`

English:
theorem Ideal.isHomogeneous_iff_forall_subset
  proof: Iff.rfl

中文:
定理 理想.isHomogeneous_iff_对任意_subset
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem Ideal.isHomogeneous_iff_forall_subset :
    I.IsHomogeneous 𝒜 ↔ forall i, (I : Set A) subseteq GradedRing.proj 𝒜 i ⁻¹' I :=
  Iff.rfl

/--
theorem `Ideal.isHomogeneous_iff_subset_iInter` / 定理 `Ideal.isHomogeneous_iff_subset_iInter`

English:
theorem Ideal.isHomogeneous_iff_subset_iInter
  proof: subset_iInter_iff.symm

中文:
定理 理想.isHomogeneous_iff_subset_i整数er
  证明: subset_iInter_iff.symm

Depends on / 依赖: subset_iInter_iff, subset_iInter_iff.symm
-/
theorem Ideal.isHomogeneous_iff_subset_iInter :
    I.IsHomogeneous 𝒜 ↔ (I : Set A) subseteq ⋂ i, GradedRing.proj 𝒜 i ⁻¹' ↑I :=
  subset_iInter_iff.symm

/--
theorem `Ideal.mul_homogeneous_element_mem_of_mem` / 定理 `Ideal.mul_homogeneous_element_mem_of_mem`

English:
theorem Ideal.mul_homogeneous_element_mem_of_mem
  proof: by
  classical
  rw [← DirectSum.sum_support_decompose 𝒜 r]; rw [Finset.sum_mul]; rw [map_sum]
  apply Ideal.sum_mem
  intro k _
  obtain ⟨i, hi⟩ := hx₁
  have mem₁ : (DirectSum.decompose 𝒜 r k : A) * x in 𝒜 (k + i) :=
    GradedMul.mul_mem (SetLike.coe_mem _) hi
  rw [GradedRing.proj_apply]; rw [Di

中文:
定理 理想.mul_homogeneous_element_mem_of_mem
  证明: by
  classical
  rw [← DirectSum.sum_support_decompose 𝒜 r]; rw [Finset.sum_mul]; rw [map_sum]
  apply Ideal.sum_mem
  intro k _
  obtain ⟨i, hi⟩ := hx₁
  have mem₁ : (DirectSum.decompose 𝒜 r k : A) * x in 𝒜 (k + i) :=
    GradedMul.mul_mem (SetLike.coe_mem _) hi
  rw [GradedRing.proj_apply]; rw [Di

Depends on / 依赖: DirectSum, DirectSum.decompose, DirectSum.decompose_of_mem, DirectSum.sum_support_decompose, Finset, Finset.sum_mul, GradedMul, GradedMul.mul_mem, GradedRing, GradedRing.proj_apply, I.mul_mem_left, I.zero_mem, Ideal.sum_mem, SetLike, SetLike.coe_mem, classical, coe_mem, coe_of_apply, decompose, decompose_of_mem
-/
theorem Ideal.mul_homogeneous_element_mem_of_mem
    {I : Ideal A} (r x : A) (hx₁ : SetLike.IsHomogeneousElem 𝒜 x)
    (hx₂ : x in I) (j : ι) : GradedRing.proj 𝒜 j (r * x) in I := by
  classical
  rw [← DirectSum.sum_support_decompose 𝒜 r]; rw [Finset.sum_mul]; rw [map_sum]
  apply Ideal.sum_mem
  intro k _
  obtain ⟨i, hi⟩ := hx₁
  have mem₁ : (DirectSum.decompose 𝒜 r k : A) * x in 𝒜 (k + i) :=
    GradedMul.mul_mem (SetLike.coe_mem _) hi
  rw [GradedRing.proj_apply]; rw [DirectSum.decompose_of_mem 𝒜 mem₁]; rw [coe_of_apply]
  split_ifs
  · exact I.mul_mem_left _ hx₂
  · exact I.zero_mem

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Ideal.homogeneous_span` / 定理 `Ideal.homogeneous_span`

English:
theorem Ideal.homogeneous_span
  given: (s : Set A) (h : forall x in s, SetLike.IsHomogeneousElem 𝒜 x)
  proof: by
  rintro i r hr
  rw [Ideal.span]; rw [Finsupp.span_eq_range_linearCombination] at hr
  rw [LinearMap.mem_range] at hr
  obtain ⟨s, rfl⟩ := hr
  rw [Finsupp.linearCombination_apply]; rw [Finsupp.sum]; rw [decompose_sum]; rw [DFinsupp.finsetSum_apply]; rw [AddSubmonoidClass.coe_finsetSum]
  refine

中文:
定理 理想.homogeneous_span
  条件: (s : 集合 A) (h : 对任意 x in s, 集合状.IsHomogeneousElem 𝒜 x)
  证明: by
  rintro i r hr
  rw [Ideal.span]; rw [Finsupp.span_eq_range_linearCombination] at hr
  rw [LinearMap.mem_range] at hr
  obtain ⟨s, rfl⟩ := hr
  rw [Finsupp.linearCombination_apply]; rw [Finsupp.sum]; rw [decompose_sum]; rw [DFinsupp.finsetSum_apply]; rw [AddSubmonoidClass.coe_finsetSum]
  refine

Depends on / 依赖: AddSubmonoidClass, AddSubmonoidClass.coe_finsetSum, DFinsupp, DFinsupp.finsetSum_apply, Finsupp, Finsupp.linearCombination_apply, Finsupp.span_eq_range_linearCombination, Finsupp.sum, Ideal.mul_homogeneous_element_mem_of_mem, Ideal.span, Ideal.subset_span, Ideal.sum_mem, LinearMap, LinearMap.mem_range, coe_finsetSum, decompose_sum, finsetSum_apply, linearCombination_apply, mem_range, mul_homogeneous_element_mem_of_mem
-/
theorem Ideal.homogeneous_span (s : Set A) (h : forall x in s, SetLike.IsHomogeneousElem 𝒜 x) :
    (Ideal.span s).IsHomogeneous 𝒜 := by
  rintro i r hr
  rw [Ideal.span]; rw [Finsupp.span_eq_range_linearCombination] at hr
  rw [LinearMap.mem_range] at hr
  obtain ⟨s, rfl⟩ := hr
  rw [Finsupp.linearCombination_apply]; rw [Finsupp.sum]; rw [decompose_sum]; rw [DFinsupp.finsetSum_apply]; rw [AddSubmonoidClass.coe_finsetSum]
  refine Ideal.sum_mem _ ?_
  rintro z hz1
  rw [smul_eq_mul]
  refine Ideal.mul_homogeneous_element_mem_of_mem 𝒜 (s z) z ?_ ?_ i
  · rcases z with ⟨z, hz2⟩
    apply h _ hz2
  · exact Ideal.subset_span z.2

/--
Definition of `Ideal.homogeneousCore` / `Ideal.homogeneousCore` 的定义

English:
definition Ideal.homogeneousCore
  signature: : HomogeneousIdeal 𝒜
  body: ⟨Ideal.homogeneousCore' 𝒜 I,
    Ideal.homogeneous_span _ _ fun _ h => by
      have := Subtype.image_preimage_coe (Set.ofPred (SetLike.IsHomogeneousElem 𝒜)) (I : Set A)
      exact (cast congr(_ in $this) h).1⟩

中文:
定义 理想.homogeneousCore
  签名: : HomogeneousIdeal 𝒜
  定义体: ⟨Ideal.homogeneousCore' 𝒜 I,
    Ideal.homogeneous_span _ _ fun _ h => by
      have := Subtype.image_preimage_coe (Set.ofPred (SetLike.IsHomogeneousElem 𝒜)) (I : Set A)
      exact (cast congr(_ in $this) h).1⟩

Depends on / 依赖: Ideal.homogeneousCore, Ideal.homogeneous_span, IsHomogeneousElem, Set.ofPred, SetLike, SetLike.IsHomogeneousElem, Subtype, Subtype.image_preimage_coe, homogeneousCore, homogeneous_span, image_preimage_coe, ofPred
-/
def Ideal.homogeneousCore : HomogeneousIdeal 𝒜 :=
  ⟨Ideal.homogeneousCore' 𝒜 I,
    Ideal.homogeneous_span _ _ fun _ h => by
      have := Subtype.image_preimage_coe (Set.ofPred (SetLike.IsHomogeneousElem 𝒜)) (I : Set A)
      exact (cast congr(_ in $this) h).1⟩

/--
theorem `Ideal.homogeneousCore_mono` / 定理 `Ideal.homogeneousCore_mono`

English:
theorem Ideal.homogeneousCore_mono
  statement: Monotone (Ideal.homogeneousCore 𝒜)
  proof: Ideal.homogeneousCore'_mono 𝒜

中文:
定理 理想.homogeneousCore_mono
  结论: 递增 (理想.homogeneousCore 𝒜)
  证明: Ideal.homogeneousCore'_mono 𝒜

Depends on / 依赖: Ideal.homogeneousCore, _mono, homogeneousCore
-/
theorem Ideal.homogeneousCore_mono : Monotone (Ideal.homogeneousCore 𝒜) :=
  Ideal.homogeneousCore'_mono 𝒜

/--
theorem `Ideal.toIdeal_homogeneousCore_le` / 定理 `Ideal.toIdeal_homogeneousCore_le`

English:
theorem Ideal.toIdeal_homogeneousCore_le
  statement: (I.homogeneousCore 𝒜).toIdeal <= I
  proof: Ideal.homogeneousCore'_le 𝒜 I

中文:
定理 理想.toIdeal_homogeneousCore_le
  结论: (I.homogeneousCore 𝒜).toIdeal <= I
  证明: Ideal.homogeneousCore'_le 𝒜 I

Depends on / 依赖: Ideal.homogeneousCore, homogeneousCore
-/
theorem Ideal.toIdeal_homogeneousCore_le : (I.homogeneousCore 𝒜).toIdeal <= I :=
  Ideal.homogeneousCore'_le 𝒜 I

variable {𝒜 I}

/--
theorem `Ideal.mem_homogeneousCore_of_homogeneous_of_mem` / 定理 `Ideal.mem_homogeneousCore_of_homogeneous_of_mem`

English:
theorem Ideal.mem_homogeneousCore_of_homogeneous_of_mem
  statement: {x : A} (h : SetLike.IsHomogeneousElem 𝒜 x)
  proof: Ideal.subset_span ⟨⟨x, h⟩, hmem, rfl⟩

中文:
定理 理想.mem_homogeneousCore_of_homogeneous_of_mem
  结论: {x : A} (h : 集合状.IsHomogeneousElem 𝒜 x)
  证明: Ideal.subset_span ⟨⟨x, h⟩, hmem, rfl⟩

Depends on / 依赖: Ideal.subset_span, subset_span
-/
theorem Ideal.mem_homogeneousCore_of_homogeneous_of_mem {x : A} (h : SetLike.IsHomogeneousElem 𝒜 x)
    (hmem : x in I) : x in I.homogeneousCore 𝒜 :=
  Ideal.subset_span ⟨⟨x, h⟩, hmem, rfl⟩

/--
theorem `Ideal.IsHomogeneous.toIdeal_homogeneousCore_eq_self` / 定理 `Ideal.IsHomogeneous.toIdeal_homogeneousCore_eq_self`

English:
theorem Ideal.IsHomogeneous.toIdeal_homogeneousCore_eq_self
  given: (h : I.IsHomogeneous 𝒜)
  proof: by
  apply le_antisymm (I.homogeneousCore'_le 𝒜) _
  intro x hx
  classical
  rw [← DirectSum.sum_support_decompose 𝒜 x]
  exact Ideal.sum_mem _ fun j _ => Ideal.subset_span ⟨⟨_, isHomogeneousElem_coe _⟩, h _ hx, rfl⟩

@[simp]

中文:
定理 理想.IsHomogeneous.toIdeal_homogeneousCore_eq_self
  条件: (h : I.IsHomogeneous 𝒜)
  证明: by
  apply le_antisymm (I.homogeneousCore'_le 𝒜) _
  intro x hx
  classical
  rw [← DirectSum.sum_support_decompose 𝒜 x]
  exact Ideal.sum_mem _ fun j _ => Ideal.subset_span ⟨⟨_, isHomogeneousElem_coe _⟩, h _ hx, rfl⟩

@[simp]

Depends on / 依赖: DirectSum, DirectSum.sum_support_decompose, I.homogeneousCore, Ideal.subset_span, Ideal.sum_mem, classical, homogeneousCore, isHomogeneousElem_coe, le_antisymm, subset_span, sum_mem, sum_support_decompose
-/
theorem Ideal.IsHomogeneous.toIdeal_homogeneousCore_eq_self (h : I.IsHomogeneous 𝒜) :
    (I.homogeneousCore 𝒜).toIdeal = I := by
  apply le_antisymm (I.homogeneousCore'_le 𝒜) _
  intro x hx
  classical
  rw [← DirectSum.sum_support_decompose 𝒜 x]
  exact Ideal.sum_mem _ fun j _ => Ideal.subset_span ⟨⟨_, isHomogeneousElem_coe _⟩, h _ hx, rfl⟩

@[simp]
/--
theorem `HomogeneousIdeal.toIdeal_homogeneousCore_eq_self` / 定理 `HomogeneousIdeal.toIdeal_homogeneousCore_eq_self`

English:
theorem HomogeneousIdeal.toIdeal_homogeneousCore_eq_self
  given: (I : HomogeneousIdeal 𝒜)
  proof: by
  ext1
  convert! Ideal.IsHomogeneous.toIdeal_homogeneousCore_eq_self I.isHomogeneous

中文:
定理 HomogeneousIdeal.toIdeal_homogeneousCore_eq_self
  条件: (I : HomogeneousIdeal 𝒜)
  证明: by
  ext1
  convert! Ideal.IsHomogeneous.toIdeal_homogeneousCore_eq_self I.isHomogeneous

Depends on / 依赖: I.isHomogeneous, Ideal.IsHomogeneous.toIdeal_homogeneousCore_eq_self, IsHomogeneous, convert, isHomogeneous, toIdeal_homogeneousCore_eq_self
-/
theorem HomogeneousIdeal.toIdeal_homogeneousCore_eq_self (I : HomogeneousIdeal 𝒜) :
    I.toIdeal.homogeneousCore 𝒜 = I := by
  ext1
  convert! Ideal.IsHomogeneous.toIdeal_homogeneousCore_eq_self I.isHomogeneous

variable (𝒜 I)

/--
theorem `Ideal.IsHomogeneous.iff_eq` / 定理 `Ideal.IsHomogeneous.iff_eq`

English:
theorem Ideal.IsHomogeneous.iff_eq
  statement: I.IsHomogeneous 𝒜 ↔ (I.homogeneousCore 𝒜).toIdeal = I
  proof: ⟨fun hI => hI.toIdeal_homogeneousCore_eq_self, fun hI => hI ▸ (Ideal.homogeneousCore 𝒜 I).2⟩

中文:
定理 理想.IsHomogeneous.iff_eq
  结论: I.IsHomogeneous 𝒜 ↔ (I.homogeneousCore 𝒜).toIdeal = I
  证明: ⟨fun hI => hI.toIdeal_homogeneousCore_eq_self, fun hI => hI ▸ (Ideal.homogeneousCore 𝒜 I).2⟩

Depends on / 依赖: Ideal.homogeneousCore, hI.toIdeal_homogeneousCore_eq_self, homogeneousCore, toIdeal_homogeneousCore_eq_self
-/
theorem Ideal.IsHomogeneous.iff_eq : I.IsHomogeneous 𝒜 ↔ (I.homogeneousCore 𝒜).toIdeal = I :=
  ⟨fun hI => hI.toIdeal_homogeneousCore_eq_self, fun hI => hI ▸ (Ideal.homogeneousCore 𝒜 I).2⟩

/--
theorem `Ideal.IsHomogeneous.iff_exists` / 定理 `Ideal.IsHomogeneous.iff_exists`

English:
theorem Ideal.IsHomogeneous.iff_exists
  proof: by
  rw [Ideal.IsHomogeneous.iff_eq]; rw [eq_comm]
  exact ((Set.image_preimage.compose (Submodule.gi _ _).gc).exists_eq_l _).symm

中文:
定理 理想.IsHomogeneous.iff_存在
  证明: by
  rw [Ideal.IsHomogeneous.iff_eq]; rw [eq_comm]
  exact ((Set.image_preimage.compose (Submodule.gi _ _).gc).exists_eq_l _).symm

Depends on / 依赖: Ideal.IsHomogeneous.iff_eq, IsHomogeneous, Set.image_preimage.compose, Submodule, Submodule.gi, compose, eq_comm, exists_eq_l, iff_eq, image_preimage
-/
theorem Ideal.IsHomogeneous.iff_exists :
    I.IsHomogeneous 𝒜 ↔ exists S : Set (homogeneousSubmonoid 𝒜), I = Ideal.span ((↑) '' S) := by
  rw [Ideal.IsHomogeneous.iff_eq]; rw [eq_comm]
  exact ((Set.image_preimage.compose (Submodule.gi _ _).gc).exists_eq_l _).symm

end IsHomogeneousIdealDefs

/-! ### Operations

In this section, we show that `Ideal.IsHomogeneous` is preserved by various notations, then use
these results to provide these notation typeclasses for `HomogeneousIdeal`. -/


section Operations

section Semiring

variable [Semiring A] [DecidableEq ι] [AddMonoid ι]
variable [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι -> σ) [GradedRing 𝒜]

namespace Ideal.IsHomogeneous

/--
theorem `bot` / 定理 `bot`

English:
theorem bot
  statement: Ideal.IsHomogeneous 𝒜 ⊥
  proof: fun i r hr => by
  simp only [Ideal.mem_bot] at hr
  rw [hr]; rw [decompose_zero]; rw [zero_apply]
  apply Ideal.zero_mem

中文:
定理 bot
  结论: 理想.IsHomogeneous 𝒜 ⊥
  证明: fun i r hr => by
  simp only [Ideal.mem_bot] at hr
  rw [hr]; rw [decompose_zero]; rw [zero_apply]
  apply Ideal.zero_mem

Depends on / 依赖: Ideal.mem_bot, Ideal.zero_mem, decompose_zero, mem_bot, zero_apply, zero_mem
-/
theorem bot : Ideal.IsHomogeneous 𝒜 ⊥ := fun i r hr => by
  simp only [Ideal.mem_bot] at hr
  rw [hr]; rw [decompose_zero]; rw [zero_apply]
  apply Ideal.zero_mem

/--
theorem `top` / 定理 `top`

English:
theorem top
  statement: Ideal.IsHomogeneous 𝒜 ⊤
  proof: fun i r _ => by simp only [Submodule.mem_top]

中文:
定理 top
  结论: 理想.IsHomogeneous 𝒜 ⊤
  证明: fun i r _ => by simp only [Submodule.mem_top]

Depends on / 依赖: Submodule, Submodule.mem_top, mem_top
-/
theorem top : Ideal.IsHomogeneous 𝒜 ⊤ := fun i r _ => by simp only [Submodule.mem_top]

variable {𝒜}

/--
theorem `inf` / 定理 `inf`

English:
theorem inf
  given: {I J : Ideal A} (HI : I.IsHomogeneous 𝒜) (HJ : J.IsHomogeneous 𝒜)
  proof: fun _ _ hr => ⟨HI _ hr.1, HJ _ hr.2⟩

中文:
定理 下确界
  条件: {I J : 理想 A} (HI : I.IsHomogeneous 𝒜) (HJ : J.IsHomogeneous 𝒜)
  证明: fun _ _ hr => ⟨HI _ hr.1, HJ _ hr.2⟩
-/
theorem inf {I J : Ideal A} (HI : I.IsHomogeneous 𝒜) (HJ : J.IsHomogeneous 𝒜) :
    (I ⊓ J).IsHomogeneous 𝒜 :=
  fun _ _ hr => ⟨HI _ hr.1, HJ _ hr.2⟩

/--
theorem `sup` / 定理 `sup`

English:
theorem sup
  given: {I J : Ideal A} (HI : I.IsHomogeneous 𝒜) (HJ : J.IsHomogeneous 𝒜)
  proof: by
  rw [iff_exists] at HI HJ ⊢
  obtain ⟨⟨s₁, rfl⟩, ⟨s₂, rfl⟩⟩ := HI, HJ
  refine ⟨s₁ union s₂, ?_⟩
  rw [Set.image_union]
  exact (Submodule.span_union _ _).symm

中文:
定理 上确界
  条件: {I J : 理想 A} (HI : I.IsHomogeneous 𝒜) (HJ : J.IsHomogeneous 𝒜)
  证明: by
  rw [iff_exists] at HI HJ ⊢
  obtain ⟨⟨s₁, rfl⟩, ⟨s₂, rfl⟩⟩ := HI, HJ
  refine ⟨s₁ union s₂, ?_⟩
  rw [Set.image_union]
  exact (Submodule.span_union _ _).symm

Depends on / 依赖: Set.image_union, Submodule, Submodule.span_union, iff_exists, image_union, span_union
-/
theorem sup {I J : Ideal A} (HI : I.IsHomogeneous 𝒜) (HJ : J.IsHomogeneous 𝒜) :
    (I ⊔ J).IsHomogeneous 𝒜 := by
  rw [iff_exists] at HI HJ ⊢
  obtain ⟨⟨s₁, rfl⟩, ⟨s₂, rfl⟩⟩ := HI, HJ
  refine ⟨s₁ union s₂, ?_⟩
  rw [Set.image_union]
  exact (Submodule.span_union _ _).symm

/--
theorem `iSup` / 定理 `iSup`

English:
theorem iSup
  given: {κ : Sort*} {f : κ -> Ideal A} (h : forall i, (f i).IsHomogeneous 𝒜)
  proof: by
  simp_rw [iff_exists] at h ⊢
  choose s hs using h
  refine ⟨⋃ i, s i, ?_⟩
  simp_rw [Set.image_iUnion, Ideal.span_iUnion]
  congr
  exact funext hs

中文:
定理 iSup
  条件: {κ : 类型层*} {f : κ -> 理想 A} (h : 对任意 i, (f i).IsHomogeneous 𝒜)
  证明: by
  simp_rw [iff_exists] at h ⊢
  choose s hs using h
  refine ⟨⋃ i, s i, ?_⟩
  simp_rw [Set.image_iUnion, Ideal.span_iUnion]
  congr
  exact funext hs
-/
protected theorem iSup {κ : Sort*} {f : κ -> Ideal A} (h : forall i, (f i).IsHomogeneous 𝒜) :
    (⨆ i, f i).IsHomogeneous 𝒜 := by
  simp_rw [iff_exists] at h ⊢
  choose s hs using h
  refine ⟨⋃ i, s i, ?_⟩
  simp_rw [Set.image_iUnion, Ideal.span_iUnion]
  congr
  exact funext hs

/--
theorem `iInf` / 定理 `iInf`

English:
theorem iInf
  given: {κ : Sort*} {f : κ -> Ideal A} (h : forall i, (f i).IsHomogeneous 𝒜)
  proof: by
  intro i x hx
  simp only [Ideal.mem_iInf] at hx ⊢
  exact fun j => h _ _ (hx j)

中文:
定理 iInf
  条件: {κ : 类型层*} {f : κ -> 理想 A} (h : 对任意 i, (f i).IsHomogeneous 𝒜)
  证明: by
  intro i x hx
  simp only [Ideal.mem_iInf] at hx ⊢
  exact fun j => h _ _ (hx j)
-/
protected theorem iInf {κ : Sort*} {f : κ -> Ideal A} (h : forall i, (f i).IsHomogeneous 𝒜) :
    (⨅ i, f i).IsHomogeneous 𝒜 := by
  intro i x hx
  simp only [Ideal.mem_iInf] at hx ⊢
  exact fun j => h _ _ (hx j)

/--
theorem `iSup₂` / 定理 `iSup₂`

English:
theorem iSup₂
  statement: {κ : Sort*} {κ' : κ -> Sort*} {f : forall i, κ' i -> Ideal A}
  proof: IsHomogeneous.iSup fun i => IsHomogeneous.iSup h i

中文:
定理 iSup₂
  结论: {κ : 类型层*} {κ' : κ -> 类型层*} {f : 对任意 i, κ' i -> 理想 A}
  证明: IsHomogeneous.iSup fun i => IsHomogeneous.iSup h i

Depends on / 依赖: IsHomogeneous, IsHomogeneous.iSup
-/
theorem iSup₂ {κ : Sort*} {κ' : κ -> Sort*} {f : forall i, κ' i -> Ideal A}
    (h : forall i j, (f i j).IsHomogeneous 𝒜) : (⨆ (i) (j), f i j).IsHomogeneous 𝒜 :=
IsHomogeneous.iSup fun i => IsHomogeneous.iSup h i

/--
theorem `iInf₂` / 定理 `iInf₂`

English:
theorem iInf₂
  statement: {κ : Sort*} {κ' : κ -> Sort*} {f : forall i, κ' i -> Ideal A}
  proof: IsHomogeneous.iInf fun i => IsHomogeneous.iInf h i

中文:
定理 iInf₂
  结论: {κ : 类型层*} {κ' : κ -> 类型层*} {f : 对任意 i, κ' i -> 理想 A}
  证明: IsHomogeneous.iInf fun i => IsHomogeneous.iInf h i

Depends on / 依赖: IsHomogeneous, IsHomogeneous.iInf
-/
theorem iInf₂ {κ : Sort*} {κ' : κ -> Sort*} {f : forall i, κ' i -> Ideal A}
    (h : forall i j, (f i j).IsHomogeneous 𝒜) : (⨅ (i) (j), f i j).IsHomogeneous 𝒜 :=
IsHomogeneous.iInf fun i => IsHomogeneous.iInf h i

/--
theorem `sSup` / 定理 `sSup`

English:
theorem sSup
  given: {ℐ : Set (Ideal A)} (h : forall I in ℐ, Ideal.IsHomogeneous 𝒜 I)
  proof: by
  rw [sSup_eq_iSup]
  exact iSup₂ h

中文:
定理 sSup
  条件: {ℐ : 集合 (理想 A)} (h : 对任意 I in ℐ, 理想.IsHomogeneous 𝒜 I)
  证明: by
  rw [sSup_eq_iSup]
  exact iSup₂ h

Depends on / 依赖: sSup_eq_iSup
-/
theorem sSup {ℐ : Set (Ideal A)} (h : forall I in ℐ, Ideal.IsHomogeneous 𝒜 I) :
    (sSup ℐ).IsHomogeneous 𝒜 := by
  rw [sSup_eq_iSup]
  exact iSup₂ h

/--
theorem `sInf` / 定理 `sInf`

English:
theorem sInf
  given: {ℐ : Set (Ideal A)} (h : forall I in ℐ, Ideal.IsHomogeneous 𝒜 I)
  proof: by
  rw [sInf_eq_iInf]
  exact iInf₂ h

中文:
定理 sInf
  条件: {ℐ : 集合 (理想 A)} (h : 对任意 I in ℐ, 理想.IsHomogeneous 𝒜 I)
  证明: by
  rw [sInf_eq_iInf]
  exact iInf₂ h

Depends on / 依赖: sInf_eq_iInf
-/
theorem sInf {ℐ : Set (Ideal A)} (h : forall I in ℐ, Ideal.IsHomogeneous 𝒜 I) :
    (sInf ℐ).IsHomogeneous 𝒜 := by
  rw [sInf_eq_iInf]
  exact iInf₂ h

end Ideal.IsHomogeneous

variable {𝒜}

namespace HomogeneousIdeal

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Top (HomogeneousIdeal 𝒜)
  body: ⟨⟨⊤, Ideal.IsHomogeneous.top 𝒜⟩⟩

中文:
实例 :
  签名: 顶元素 (HomogeneousIdeal 𝒜)
  定义体: ⟨⟨⊤, Ideal.IsHomogeneous.top 𝒜⟩⟩

Depends on / 依赖: Ideal.IsHomogeneous.top, IsHomogeneous
-/
instance : Top (HomogeneousIdeal 𝒜) :=
  ⟨⟨⊤, Ideal.IsHomogeneous.top 𝒜⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bot (HomogeneousIdeal 𝒜)
  body: ⟨⟨⊥, Ideal.IsHomogeneous.bot 𝒜⟩⟩

中文:
实例 :
  签名: 底元素 (HomogeneousIdeal 𝒜)
  定义体: ⟨⟨⊥, Ideal.IsHomogeneous.bot 𝒜⟩⟩

Depends on / 依赖: Ideal.IsHomogeneous.bot, IsHomogeneous
-/
instance : Bot (HomogeneousIdeal 𝒜) :=
  ⟨⟨⊥, Ideal.IsHomogeneous.bot 𝒜⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Max (HomogeneousIdeal 𝒜)
  body: ⟨fun I J => ⟨_, I.isHomogeneous.sup J.isHomogeneous⟩⟩

中文:
实例 :
  签名: 最大值 (HomogeneousIdeal 𝒜)
  定义体: ⟨fun I J => ⟨_, I.isHomogeneous.sup J.isHomogeneous⟩⟩

Depends on / 依赖: I.isHomogeneous.sup, J.isHomogeneous, isHomogeneous
-/
instance : Max (HomogeneousIdeal 𝒜) :=
  ⟨fun I J => ⟨_, I.isHomogeneous.sup J.isHomogeneous⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Min (HomogeneousIdeal 𝒜)
  body: ⟨fun I J => ⟨_, I.isHomogeneous.inf J.isHomogeneous⟩⟩

中文:
实例 :
  签名: 最小值 (HomogeneousIdeal 𝒜)
  定义体: ⟨fun I J => ⟨_, I.isHomogeneous.inf J.isHomogeneous⟩⟩

Depends on / 依赖: I.isHomogeneous.inf, J.isHomogeneous, isHomogeneous
-/
instance : Min (HomogeneousIdeal 𝒜) :=
  ⟨fun I J => ⟨_, I.isHomogeneous.inf J.isHomogeneous⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SupSet (HomogeneousIdeal 𝒜)
  body: ⟨fun S => ⟨⨆ s in S, toIdeal s, Ideal.IsHomogeneous.iSup₂ fun s _ => s.isHomogeneous⟩⟩

中文:
实例 :
  签名: 上确界集 (HomogeneousIdeal 𝒜)
  定义体: ⟨fun S => ⟨⨆ s in S, toIdeal s, Ideal.IsHomogeneous.iSup₂ fun s _ => s.isHomogeneous⟩⟩

Depends on / 依赖: Ideal.IsHomogeneous.iSup, IsHomogeneous, isHomogeneous, s.isHomogeneous, toIdeal
-/
instance : SupSet (HomogeneousIdeal 𝒜) :=
  ⟨fun S => ⟨⨆ s in S, toIdeal s, Ideal.IsHomogeneous.iSup₂ fun s _ => s.isHomogeneous⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InfSet (HomogeneousIdeal 𝒜)
  body: ⟨fun S => ⟨⨅ s in S, toIdeal s, Ideal.IsHomogeneous.iInf₂ fun s _ => s.isHomogeneous⟩⟩

@[simp]

中文:
实例 :
  签名: 下确界集 (HomogeneousIdeal 𝒜)
  定义体: ⟨fun S => ⟨⨅ s in S, toIdeal s, Ideal.IsHomogeneous.iInf₂ fun s _ => s.isHomogeneous⟩⟩

@[simp]

Depends on / 依赖: Ideal.IsHomogeneous.iInf, IsHomogeneous, isHomogeneous, s.isHomogeneous, toIdeal
-/
instance : InfSet (HomogeneousIdeal 𝒜) :=
  ⟨fun S => ⟨⨅ s in S, toIdeal s, Ideal.IsHomogeneous.iInf₂ fun s _ => s.isHomogeneous⟩⟩

@[simp]
/--
theorem `coe_top` / 定理 `coe_top`

English:
theorem coe_top
  statement: ((⊤ : HomogeneousIdeal 𝒜) : Set A) = univ
  proof: rfl

@[simp]

中文:
定理 coe_top
  结论: ((⊤ : HomogeneousIdeal 𝒜) : 集合 A) = univ
  证明: rfl

@[simp]
-/
theorem coe_top : ((⊤ : HomogeneousIdeal 𝒜) : Set A) = univ :=
  rfl

@[simp]
/--
theorem `coe_bot` / 定理 `coe_bot`

English:
theorem coe_bot
  statement: ((⊥ : HomogeneousIdeal 𝒜) : Set A) = 0
  proof: rfl

@[simp]

中文:
定理 coe_bot
  结论: ((⊥ : HomogeneousIdeal 𝒜) : 集合 A) = 0
  证明: rfl

@[simp]
-/
theorem coe_bot : ((⊥ : HomogeneousIdeal 𝒜) : Set A) = 0 :=
  rfl

@[simp]
/--
theorem `coe_sup` / 定理 `coe_sup`

English:
theorem coe_sup
  given: (I J : HomogeneousIdeal 𝒜)
  statement: ↑(I ⊔ J) = (I + J : Set A)
  proof: Submodule.coe_sup _ _

@[simp]

中文:
定理 coe_sup
  条件: (I J : HomogeneousIdeal 𝒜)
  结论: ↑(I ⊔ J) = (I + J : 集合 A)
  证明: Submodule.coe_sup _ _

@[simp]

Depends on / 依赖: Submodule, Submodule.coe_sup, coe_sup
-/
theorem coe_sup (I J : HomogeneousIdeal 𝒜) : ↑(I ⊔ J) = (I + J : Set A) :=
  Submodule.coe_sup _ _

@[simp]
/--
theorem `coe_inf` / 定理 `coe_inf`

English:
theorem coe_inf
  given: (I J : HomogeneousIdeal 𝒜)
  statement: (↑(I ⊓ J) : Set A) = ↑I inter ↑J
  proof: rfl

@[simp]

中文:
定理 coe_inf
  条件: (I J : HomogeneousIdeal 𝒜)
  结论: (↑(I ⊓ J) : 集合 A) = ↑I inter ↑J
  证明: rfl

@[simp]
-/
theorem coe_inf (I J : HomogeneousIdeal 𝒜) : (↑(I ⊓ J) : Set A) = ↑I inter ↑J :=
  rfl

@[simp]
/--
theorem `toIdeal_top` / 定理 `toIdeal_top`

English:
theorem toIdeal_top
  statement: (⊤ : HomogeneousIdeal 𝒜).toIdeal = (⊤ : Ideal A)
  proof: rfl

@[simp]

中文:
定理 toIdeal_top
  结论: (⊤ : HomogeneousIdeal 𝒜).toIdeal = (⊤ : 理想 A)
  证明: rfl

@[simp]
-/
theorem toIdeal_top : (⊤ : HomogeneousIdeal 𝒜).toIdeal = (⊤ : Ideal A) :=
  rfl

@[simp]
/--
theorem `toIdeal_bot` / 定理 `toIdeal_bot`

English:
theorem toIdeal_bot
  statement: (⊥ : HomogeneousIdeal 𝒜).toIdeal = (⊥ : Ideal A)
  proof: rfl

@[simp]

中文:
定理 toIdeal_bot
  结论: (⊥ : HomogeneousIdeal 𝒜).toIdeal = (⊥ : 理想 A)
  证明: rfl

@[simp]
-/
theorem toIdeal_bot : (⊥ : HomogeneousIdeal 𝒜).toIdeal = (⊥ : Ideal A) :=
  rfl

@[simp]
/--
theorem `toIdeal_sup` / 定理 `toIdeal_sup`

English:
theorem toIdeal_sup
  given: (I J : HomogeneousIdeal 𝒜)
  statement: (I ⊔ J).toIdeal = I.toIdeal ⊔ J.toIdeal
  proof: rfl

@[simp]

中文:
定理 toIdeal_sup
  条件: (I J : HomogeneousIdeal 𝒜)
  结论: (I ⊔ J).toIdeal = I.toIdeal ⊔ J.toIdeal
  证明: rfl

@[simp]
-/
theorem toIdeal_sup (I J : HomogeneousIdeal 𝒜) : (I ⊔ J).toIdeal = I.toIdeal ⊔ J.toIdeal :=
  rfl

@[simp]
/--
theorem `toIdeal_inf` / 定理 `toIdeal_inf`

English:
theorem toIdeal_inf
  given: (I J : HomogeneousIdeal 𝒜)
  statement: (I ⊓ J).toIdeal = I.toIdeal ⊓ J.toIdeal
  proof: rfl

@[simp]

中文:
定理 toIdeal_inf
  条件: (I J : HomogeneousIdeal 𝒜)
  结论: (I ⊓ J).toIdeal = I.toIdeal ⊓ J.toIdeal
  证明: rfl

@[simp]
-/
theorem toIdeal_inf (I J : HomogeneousIdeal 𝒜) : (I ⊓ J).toIdeal = I.toIdeal ⊓ J.toIdeal :=
  rfl

@[simp]
/--
theorem `toIdeal_sSup` / 定理 `toIdeal_sSup`

English:
theorem toIdeal_sSup
  given: (ℐ : Set (HomogeneousIdeal 𝒜))
  statement: (sSup ℐ).toIdeal = ⨆ s in ℐ, toIdeal s
  proof: rfl

@[simp]

中文:
定理 toIdeal_sSup
  条件: (ℐ : 集合 (HomogeneousIdeal 𝒜))
  结论: (sSup ℐ).toIdeal = ⨆ s in ℐ, toIdeal s
  证明: rfl

@[simp]
-/
theorem toIdeal_sSup (ℐ : Set (HomogeneousIdeal 𝒜)) : (sSup ℐ).toIdeal = ⨆ s in ℐ, toIdeal s :=
  rfl

@[simp]
/--
theorem `toIdeal_sInf` / 定理 `toIdeal_sInf`

English:
theorem toIdeal_sInf
  given: (ℐ : Set (HomogeneousIdeal 𝒜))
  statement: (sInf ℐ).toIdeal = ⨅ s in ℐ, toIdeal s
  proof: rfl

@[simp]

中文:
定理 toIdeal_sInf
  条件: (ℐ : 集合 (HomogeneousIdeal 𝒜))
  结论: (sInf ℐ).toIdeal = ⨅ s in ℐ, toIdeal s
  证明: rfl

@[simp]
-/
theorem toIdeal_sInf (ℐ : Set (HomogeneousIdeal 𝒜)) : (sInf ℐ).toIdeal = ⨅ s in ℐ, toIdeal s :=
  rfl

@[simp]
/--
theorem `toIdeal_iSup` / 定理 `toIdeal_iSup`

English:
theorem toIdeal_iSup
  given: {κ : Sort*} (s : κ -> HomogeneousIdeal 𝒜)
  proof: by
  rw [iSup]; rw [toIdeal_sSup]; rw [iSup_range]

@[simp]

中文:
定理 toIdeal_iSup
  条件: {κ : 类型层*} (s : κ -> HomogeneousIdeal 𝒜)
  证明: by
  rw [iSup]; rw [toIdeal_sSup]; rw [iSup_range]

@[simp]

Depends on / 依赖: iSup_range, toIdeal_sSup
-/
theorem toIdeal_iSup {κ : Sort*} (s : κ -> HomogeneousIdeal 𝒜) :
    (⨆ i, s i).toIdeal = ⨆ i, (s i).toIdeal := by
  rw [iSup]; rw [toIdeal_sSup]; rw [iSup_range]

@[simp]
/--
theorem `toIdeal_iInf` / 定理 `toIdeal_iInf`

English:
theorem toIdeal_iInf
  given: {κ : Sort*} (s : κ -> HomogeneousIdeal 𝒜)
  proof: by
  rw [iInf]; rw [toIdeal_sInf]; rw [iInf_range]

中文:
定理 toIdeal_iInf
  条件: {κ : 类型层*} (s : κ -> HomogeneousIdeal 𝒜)
  证明: by
  rw [iInf]; rw [toIdeal_sInf]; rw [iInf_range]

Depends on / 依赖: iInf_range, toIdeal_sInf
-/
theorem toIdeal_iInf {κ : Sort*} (s : κ -> HomogeneousIdeal 𝒜) :
    (⨅ i, s i).toIdeal = ⨅ i, (s i).toIdeal := by
  rw [iInf]; rw [toIdeal_sInf]; rw [iInf_range]

/--
theorem `toIdeal_iSup₂` / 定理 `toIdeal_iSup₂`

English:
theorem toIdeal_iSup₂
  given: {κ : Sort*} {κ' : κ -> Sort*} (s : forall i, κ' i -> HomogeneousIdeal 𝒜)
  proof: by
  simp_rw [toIdeal_iSup]

中文:
定理 toIdeal_iSup₂
  条件: {κ : 类型层*} {κ' : κ -> 类型层*} (s : 对任意 i, κ' i -> HomogeneousIdeal 𝒜)
  证明: by
  simp_rw [toIdeal_iSup]

Depends on / 依赖: simp_rw, toIdeal_iSup
-/
theorem toIdeal_iSup₂ {κ : Sort*} {κ' : κ -> Sort*} (s : forall i, κ' i -> HomogeneousIdeal 𝒜) :
    (⨆ (i) (j), s i j).toIdeal = ⨆ (i) (j), (s i j).toIdeal := by
  simp_rw [toIdeal_iSup]

/--
theorem `toIdeal_iInf₂` / 定理 `toIdeal_iInf₂`

English:
theorem toIdeal_iInf₂
  given: {κ : Sort*} {κ' : κ -> Sort*} (s : forall i, κ' i -> HomogeneousIdeal 𝒜)
  proof: by
  simp_rw [toIdeal_iInf]

@[simp]

中文:
定理 toIdeal_iInf₂
  条件: {κ : 类型层*} {κ' : κ -> 类型层*} (s : 对任意 i, κ' i -> HomogeneousIdeal 𝒜)
  证明: by
  simp_rw [toIdeal_iInf]

@[simp]

Depends on / 依赖: simp_rw, toIdeal_iInf
-/
theorem toIdeal_iInf₂ {κ : Sort*} {κ' : κ -> Sort*} (s : forall i, κ' i -> HomogeneousIdeal 𝒜) :
    (⨅ (i) (j), s i j).toIdeal = ⨅ (i) (j), (s i j).toIdeal := by
  simp_rw [toIdeal_iInf]

@[simp]
/--
theorem `eq_top_iff` / 定理 `eq_top_iff`

English:
theorem eq_top_iff
  given: (I : HomogeneousIdeal 𝒜)
  statement: I = ⊤ ↔ I.toIdeal = ⊤
  proof: toIdeal_injective.eq_iff.symm

@[simp]

中文:
定理 eq_top_iff
  条件: (I : HomogeneousIdeal 𝒜)
  结论: I = ⊤ ↔ I.toIdeal = ⊤
  证明: toIdeal_injective.eq_iff.symm

@[simp]

Depends on / 依赖: eq_iff, toIdeal_injective, toIdeal_injective.eq_iff.symm
-/
theorem eq_top_iff (I : HomogeneousIdeal 𝒜) : I = ⊤ ↔ I.toIdeal = ⊤ :=
  toIdeal_injective.eq_iff.symm

@[simp]
/--
theorem `eq_bot_iff` / 定理 `eq_bot_iff`

English:
theorem eq_bot_iff
  given: (I : HomogeneousIdeal 𝒜)
  statement: I = ⊥ ↔ I.toIdeal = ⊥
  proof: toIdeal_injective.eq_iff.symm

中文:
定理 eq_bot_iff
  条件: (I : HomogeneousIdeal 𝒜)
  结论: I = ⊥ ↔ I.toIdeal = ⊥
  证明: toIdeal_injective.eq_iff.symm

Depends on / 依赖: eq_iff, toIdeal_injective, toIdeal_injective.eq_iff.symm
-/
theorem eq_bot_iff (I : HomogeneousIdeal 𝒜) : I = ⊥ ↔ I.toIdeal = ⊥ :=
  toIdeal_injective.eq_iff.symm

/--
Instance `completeLattice` / 实例 `completeLattice`

English:
instance completeLattice
  signature: : CompleteLattice (HomogeneousIdeal 𝒜)
  body: toIdeal_injective.completeLattice _ .rfl .rfl toIdeal_sup toIdeal_inf toIdeal_sSup toIdeal_sInf
    toIdeal_top toIdeal_bot

中文:
实例 completeLattice
  签名: : 完备格 (HomogeneousIdeal 𝒜)
  定义体: toIdeal_injective.completeLattice _ .rfl .rfl toIdeal_sup toIdeal_inf toIdeal_sSup toIdeal_sInf
    toIdeal_top toIdeal_bot

Depends on / 依赖: completeLattice, toIdeal_bot, toIdeal_inf, toIdeal_injective, toIdeal_injective.completeLattice, toIdeal_sInf, toIdeal_sSup, toIdeal_sup, toIdeal_top
-/
instance completeLattice : CompleteLattice (HomogeneousIdeal 𝒜) :=
  toIdeal_injective.completeLattice _ .rfl .rfl toIdeal_sup toIdeal_inf toIdeal_sSup toIdeal_sInf
    toIdeal_top toIdeal_bot

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add (HomogeneousIdeal 𝒜)
  body: ⟨(· ⊔ ·)⟩

@[simp]

中文:
实例 :
  签名: 加法 (HomogeneousIdeal 𝒜)
  定义体: ⟨(· ⊔ ·)⟩

@[simp]
-/
instance : Add (HomogeneousIdeal 𝒜) :=
  ⟨(· ⊔ ·)⟩

@[simp]
/--
theorem `toIdeal_add` / 定理 `toIdeal_add`

English:
theorem toIdeal_add
  given: (I J : HomogeneousIdeal 𝒜)
  statement: (I + J).toIdeal = I.toIdeal + J.toIdeal
  proof: rfl

中文:
定理 toIdeal_add
  条件: (I J : HomogeneousIdeal 𝒜)
  结论: (I + J).toIdeal = I.toIdeal + J.toIdeal
  证明: rfl
-/
theorem toIdeal_add (I J : HomogeneousIdeal 𝒜) : (I + J).toIdeal = I.toIdeal + J.toIdeal :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (HomogeneousIdeal 𝒜)
  body: ⊥

中文:
实例 :
  签名: 可居 (HomogeneousIdeal 𝒜)
  定义体: ⊥
-/
instance : Inhabited (HomogeneousIdeal 𝒜) where default := ⊥

end HomogeneousIdeal

end Semiring

section CommSemiring

variable [CommSemiring A]
variable [DecidableEq ι] [AddMonoid ι]
variable [SetLike σ A] [AddSubmonoidClass σ A] {𝒜 : ι -> σ} [GradedRing 𝒜]
variable (I : Ideal A)

/--
theorem `Ideal.IsHomogeneous.mul` / 定理 `Ideal.IsHomogeneous.mul`

English:
theorem Ideal.IsHomogeneous.mul
  given: {I J : Ideal A} (HI : I.IsHomogeneous 𝒜) (HJ : J.IsHomogeneous 𝒜)
  proof: by
  rw [Ideal.IsHomogeneous.iff_exists] at HI HJ ⊢
  obtain ⟨⟨s₁, rfl⟩, ⟨s₂, rfl⟩⟩ := HI, HJ
  rw [Ideal.span_mul_span']
exact ⟨s₁ * s₂, congr_arg _ (Set.image_mul (homogeneousSubmonoid 𝒜).subtype).symm⟩

中文:
定理 理想.IsHomogeneous.mul
  条件: {I J : 理想 A} (HI : I.IsHomogeneous 𝒜) (HJ : J.IsHomogeneous 𝒜)
  证明: by
  rw [Ideal.IsHomogeneous.iff_exists] at HI HJ ⊢
  obtain ⟨⟨s₁, rfl⟩, ⟨s₂, rfl⟩⟩ := HI, HJ
  rw [Ideal.span_mul_span']
exact ⟨s₁ * s₂, congr_arg _ (Set.image_mul (homogeneousSubmonoid 𝒜).subtype).symm⟩

Depends on / 依赖: Ideal.IsHomogeneous.iff_exists, Ideal.span_mul_span, IsHomogeneous, Set.image_mul, congr_arg, homogeneousSubmonoid, iff_exists, image_mul, span_mul_span, subtype
-/
theorem Ideal.IsHomogeneous.mul {I J : Ideal A} (HI : I.IsHomogeneous 𝒜) (HJ : J.IsHomogeneous 𝒜) :
    (I * J).IsHomogeneous 𝒜 := by
  rw [Ideal.IsHomogeneous.iff_exists] at HI HJ ⊢
  obtain ⟨⟨s₁, rfl⟩, ⟨s₂, rfl⟩⟩ := HI, HJ
  rw [Ideal.span_mul_span']
exact ⟨s₁ * s₂, congr_arg _ (Set.image_mul (homogeneousSubmonoid 𝒜).subtype).symm⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul (HomogeneousIdeal 𝒜)
  body: ⟨I.toIdeal * J.toIdeal, I.isHomogeneous.mul J.isHomogeneous⟩

@[simp]

中文:
实例 :
  签名: 乘法 (HomogeneousIdeal 𝒜)
  定义体: ⟨I.toIdeal * J.toIdeal, I.isHomogeneous.mul J.isHomogeneous⟩

@[simp]

Depends on / 依赖: I.isHomogeneous.mul, I.toIdeal, J.isHomogeneous, J.toIdeal, isHomogeneous, toIdeal
-/
instance : Mul (HomogeneousIdeal 𝒜) where
  mul I J := ⟨I.toIdeal * J.toIdeal, I.isHomogeneous.mul J.isHomogeneous⟩

@[simp]
/--
theorem `HomogeneousIdeal.toIdeal_mul` / 定理 `HomogeneousIdeal.toIdeal_mul`

English:
theorem HomogeneousIdeal.toIdeal_mul
  given: (I J : HomogeneousIdeal 𝒜)
  proof: rfl

中文:
定理 HomogeneousIdeal.toIdeal_mul
  条件: (I J : HomogeneousIdeal 𝒜)
  证明: rfl
-/
theorem HomogeneousIdeal.toIdeal_mul (I J : HomogeneousIdeal 𝒜) :
    (I * J).toIdeal = I.toIdeal * J.toIdeal :=
  rfl

end CommSemiring

end Operations

/-! ### Homogeneous core

Note that many results about the homogeneous core came earlier in this file, as they are helpful
for building the lattice structure. -/


section homogeneousCore

open HomogeneousIdeal

variable [Semiring A] [DecidableEq ι] [AddMonoid ι]
variable [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι -> σ) [GradedRing 𝒜]
variable (I : Ideal A)

/--
theorem `Ideal.homogeneousCore.gc` / 定理 `Ideal.homogeneousCore.gc`

English:
theorem Ideal.homogeneousCore.gc
  statement: GaloisConnection toIdeal (Ideal.homogeneousCore 𝒜)
  proof: fun I _ =>
  ⟨fun H => I.toIdeal_homogeneousCore_eq_self ▸ Ideal.homogeneousCore_mono 𝒜 H,
    fun H => le_trans H (Ideal.homogeneousCore'_le _ _)⟩

中文:
定理 理想.homogeneousCore.gc
  结论: GaloisConnection toIdeal (理想.homogeneousCore 𝒜)
  证明: fun I _ =>
  ⟨fun H => I.toIdeal_homogeneousCore_eq_self ▸ Ideal.homogeneousCore_mono 𝒜 H,
    fun H => le_trans H (Ideal.homogeneousCore'_le _ _)⟩
-/
theorem Ideal.homogeneousCore.gc : GaloisConnection toIdeal (Ideal.homogeneousCore 𝒜) := fun I _ =>
  ⟨fun H => I.toIdeal_homogeneousCore_eq_self ▸ Ideal.homogeneousCore_mono 𝒜 H,
    fun H => le_trans H (Ideal.homogeneousCore'_le _ _)⟩

/--
Definition of `Ideal.homogeneousCore.gi` / `Ideal.homogeneousCore.gi` 的定义

English:
definition Ideal.homogeneousCore.gi
  signature: : GaloisCoinsertion toIdeal (Ideal.homogeneousCore 𝒜) where
  body: ⟨I, le_antisymm (I.toIdeal_homogeneousCore_le 𝒜) HI ▸ HomogeneousIdeal.isHomogeneous _⟩
  gc := Ideal.homogeneousCore.gc 𝒜
  u_l_le _ := Ideal.homogeneousCore'_le _ _
  choice_eq I H := le_antisymm H (I.toIdeal_homogeneousCore_le _)

中文:
定义 理想.homogeneousCore.gi
  签名: : Galois余嵌入 toIdeal (理想.homogeneousCore 𝒜) where
  定义体: ⟨I, le_antisymm (I.toIdeal_homogeneousCore_le 𝒜) HI ▸ HomogeneousIdeal.isHomogeneous _⟩
  gc := Ideal.homogeneousCore.gc 𝒜
  u_l_le _ := Ideal.homogeneousCore'_le _ _
  choice_eq I H := le_antisymm H (I.toIdeal_homogeneousCore_le _)

Depends on / 依赖: HomogeneousIdeal, HomogeneousIdeal.isHomogeneous, I.toIdeal_homogeneousCore_le, Ideal.homogeneousCore, Ideal.homogeneousCore.gc, choice_eq, homogeneousCore, isHomogeneous, le_antisymm, toIdeal_homogeneousCore_le, u_l_le
-/
def Ideal.homogeneousCore.gi : GaloisCoinsertion toIdeal (Ideal.homogeneousCore 𝒜) where
  choice I HI :=
    ⟨I, le_antisymm (I.toIdeal_homogeneousCore_le 𝒜) HI ▸ HomogeneousIdeal.isHomogeneous _⟩
  gc := Ideal.homogeneousCore.gc 𝒜
  u_l_le _ := Ideal.homogeneousCore'_le _ _
  choice_eq I H := le_antisymm H (I.toIdeal_homogeneousCore_le _)

/--
theorem `Ideal.homogeneousCore_eq_sSup` / 定理 `Ideal.homogeneousCore_eq_sSup`

English:
theorem Ideal.homogeneousCore_eq_sSup
  proof: Eq.symm IsLUB.sSup_eq (Ideal.homogeneousCore.gc 𝒜).isGreatest_u.isLUB

中文:
定理 理想.homogeneousCore_eq_sSup
  证明: Eq.symm IsLUB.sSup_eq (Ideal.homogeneousCore.gc 𝒜).isGreatest_u.isLUB

Depends on / 依赖: Eq.symm, Ideal.homogeneousCore.gc, IsLUB.sSup_eq, homogeneousCore, isGreatest_u, isGreatest_u.isLUB, sSup_eq
-/
theorem Ideal.homogeneousCore_eq_sSup :
    I.homogeneousCore 𝒜 = sSup { J : HomogeneousIdeal 𝒜 | J.toIdeal <= I } :=
Eq.symm IsLUB.sSup_eq (Ideal.homogeneousCore.gc 𝒜).isGreatest_u.isLUB

/--
theorem `Ideal.homogeneousCore'_eq_sSup` / 定理 `Ideal.homogeneousCore'_eq_sSup`

English:
theorem Ideal.homogeneousCore'_eq_sSup
  proof: by
  refine (IsLUB.sSup_eq ?_).symm
  apply IsGreatest.isLUB
  have coe_mono : Monotone (toIdeal : HomogeneousIdeal 𝒜 -> Ideal A) := fun x y => id
  convert! coe_mono.map_isGreatest (Ideal.homogeneousCore.gc 𝒜).isGreatest_u using 1
  ext x
  rw [mem_image]; rw [mem_ofPred_eq]
  refine ⟨fun hI => ⟨⟨x

中文:
定理 理想.homogeneousCore'_eq_sSup
  证明: by
  refine (IsLUB.sSup_eq ?_).symm
  apply IsGreatest.isLUB
  have coe_mono : Monotone (toIdeal : HomogeneousIdeal 𝒜 -> Ideal A) := fun x y => id
  convert! coe_mono.map_isGreatest (Ideal.homogeneousCore.gc 𝒜).isGreatest_u using 1
  ext x
  rw [mem_image]; rw [mem_ofPred_eq]
  refine ⟨fun hI => ⟨⟨x
-/
theorem Ideal.homogeneousCore'_eq_sSup :
    I.homogeneousCore' 𝒜 = sSup { J : Ideal A | J.IsHomogeneous 𝒜 ∧ J <= I } := by
  refine (IsLUB.sSup_eq ?_).symm
  apply IsGreatest.isLUB
  have coe_mono : Monotone (toIdeal : HomogeneousIdeal 𝒜 -> Ideal A) := fun x y => id
  convert! coe_mono.map_isGreatest (Ideal.homogeneousCore.gc 𝒜).isGreatest_u using 1
  ext x
  rw [mem_image]; rw [mem_ofPred_eq]
  refine ⟨fun hI => ⟨⟨x, hI.1⟩, ⟨hI.2, rfl⟩⟩, ?_⟩
  rintro ⟨x, ⟨hx, rfl⟩⟩
  exact ⟨x.isHomogeneous, hx⟩

end homogeneousCore

/-! ### Homogeneous hulls -/


section HomogeneousHull

open HomogeneousIdeal

variable [Semiring A] [DecidableEq ι] [AddMonoid ι]
variable [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι -> σ) [GradedRing 𝒜]
variable (I : Ideal A)

/--
Definition of `Ideal.homogeneousHull` / `Ideal.homogeneousHull` 的定义

English:
definition Ideal.homogeneousHull
  signature: : HomogeneousIdeal 𝒜
  body: ⟨Ideal.span { r : A | exists (i : ι) (x : I), (DirectSum.decompose 𝒜 (x : A) i : A) = r }, by
    refine Ideal.homogeneous_span _ _ fun x hx => ?_
    obtain ⟨i, x, rfl⟩ := hx
    apply SetLike.isHomogeneousElem_coe⟩

中文:
定义 理想.homogeneousHull
  签名: : HomogeneousIdeal 𝒜
  定义体: ⟨Ideal.span { r : A | exists (i : ι) (x : I), (DirectSum.decompose 𝒜 (x : A) i : A) = r }, by
    refine Ideal.homogeneous_span _ _ fun x hx => ?_
    obtain ⟨i, x, rfl⟩ := hx
    apply SetLike.isHomogeneousElem_coe⟩

Depends on / 依赖: DirectSum, DirectSum.decompose, Ideal.homogeneous_span, Ideal.span, SetLike, SetLike.isHomogeneousElem_coe, decompose, homogeneous_span, isHomogeneousElem_coe
-/
def Ideal.homogeneousHull : HomogeneousIdeal 𝒜 :=
  ⟨Ideal.span { r : A | exists (i : ι) (x : I), (DirectSum.decompose 𝒜 (x : A) i : A) = r }, by
    refine Ideal.homogeneous_span _ _ fun x hx => ?_
    obtain ⟨i, x, rfl⟩ := hx
    apply SetLike.isHomogeneousElem_coe⟩

/--
theorem `Ideal.le_toIdeal_homogeneousHull` / 定理 `Ideal.le_toIdeal_homogeneousHull`

English:
theorem Ideal.le_toIdeal_homogeneousHull
  statement: I <= (Ideal.homogeneousHull 𝒜 I).toIdeal
  proof: by
  intro r hr
  classical
  rw [← DirectSum.sum_support_decompose 𝒜 r]
  refine Ideal.sum_mem _ ?_
  intro j _
  apply Ideal.subset_span
  use j
  use ⟨r, hr⟩

中文:
定理 理想.le_toIdeal_homogeneousHull
  结论: I <= (理想.homogeneousHull 𝒜 I).toIdeal
  证明: by
  intro r hr
  classical
  rw [← DirectSum.sum_support_decompose 𝒜 r]
  refine Ideal.sum_mem _ ?_
  intro j _
  apply Ideal.subset_span
  use j
  use ⟨r, hr⟩

Depends on / 依赖: DirectSum, DirectSum.sum_support_decompose, Ideal.subset_span, Ideal.sum_mem, classical, subset_span, sum_mem, sum_support_decompose
-/
theorem Ideal.le_toIdeal_homogeneousHull : I <= (Ideal.homogeneousHull 𝒜 I).toIdeal := by
  intro r hr
  classical
  rw [← DirectSum.sum_support_decompose 𝒜 r]
  refine Ideal.sum_mem _ ?_
  intro j _
  apply Ideal.subset_span
  use j
  use ⟨r, hr⟩

/--
theorem `Ideal.homogeneousHull_mono` / 定理 `Ideal.homogeneousHull_mono`

English:
theorem Ideal.homogeneousHull_mono
  statement: Monotone (Ideal.homogeneousHull 𝒜)
  proof: fun I J I_le_J => by
  apply Ideal.span_mono
  rintro r ⟨hr1, ⟨x, hx⟩, rfl⟩
  exact ⟨hr1, ⟨⟨x, I_le_J hx⟩, rfl⟩⟩

中文:
定理 理想.homogeneousHull_mono
  结论: 递增 (理想.homogeneousHull 𝒜)
  证明: fun I J I_le_J => by
  apply Ideal.span_mono
  rintro r ⟨hr1, ⟨x, hx⟩, rfl⟩
  exact ⟨hr1, ⟨⟨x, I_le_J hx⟩, rfl⟩⟩

Depends on / 依赖: I_le_J, Ideal.span_mono, span_mono
-/
theorem Ideal.homogeneousHull_mono : Monotone (Ideal.homogeneousHull 𝒜) := fun I J I_le_J => by
  apply Ideal.span_mono
  rintro r ⟨hr1, ⟨x, hx⟩, rfl⟩
  exact ⟨hr1, ⟨⟨x, I_le_J hx⟩, rfl⟩⟩

variable {I 𝒜}

/--
theorem `Ideal.IsHomogeneous.toIdeal_homogeneousHull_eq_self` / 定理 `Ideal.IsHomogeneous.toIdeal_homogeneousHull_eq_self`

English:
theorem Ideal.IsHomogeneous.toIdeal_homogeneousHull_eq_self
  given: (h : I.IsHomogeneous 𝒜)
  proof: by
  apply le_antisymm _ (Ideal.le_toIdeal_homogeneousHull _ _)
  apply Ideal.span_le.2
  rintro _ ⟨i, x, rfl⟩
  exact h _ x.prop

@[simp]

中文:
定理 理想.IsHomogeneous.toIdeal_homogeneousHull_eq_self
  条件: (h : I.IsHomogeneous 𝒜)
  证明: by
  apply le_antisymm _ (Ideal.le_toIdeal_homogeneousHull _ _)
  apply Ideal.span_le.2
  rintro _ ⟨i, x, rfl⟩
  exact h _ x.prop

@[simp]

Depends on / 依赖: Ideal.le_toIdeal_homogeneousHull, Ideal.span_le, le_antisymm, le_toIdeal_homogeneousHull, span_le, x.prop
-/
theorem Ideal.IsHomogeneous.toIdeal_homogeneousHull_eq_self (h : I.IsHomogeneous 𝒜) :
    (Ideal.homogeneousHull 𝒜 I).toIdeal = I := by
  apply le_antisymm _ (Ideal.le_toIdeal_homogeneousHull _ _)
  apply Ideal.span_le.2
  rintro _ ⟨i, x, rfl⟩
  exact h _ x.prop

@[simp]
/--
theorem `HomogeneousIdeal.homogeneousHull_toIdeal_eq_self` / 定理 `HomogeneousIdeal.homogeneousHull_toIdeal_eq_self`

English:
theorem HomogeneousIdeal.homogeneousHull_toIdeal_eq_self
  given: (I : HomogeneousIdeal 𝒜)
  proof: HomogeneousIdeal.toIdeal_injective I.isHomogeneous.toIdeal_homogeneousHull_eq_self

中文:
定理 HomogeneousIdeal.homogeneousHull_toIdeal_eq_self
  条件: (I : HomogeneousIdeal 𝒜)
  证明: HomogeneousIdeal.toIdeal_injective I.isHomogeneous.toIdeal_homogeneousHull_eq_self

Depends on / 依赖: HomogeneousIdeal, HomogeneousIdeal.toIdeal_injective, I.isHomogeneous.toIdeal_homogeneousHull_eq_self, isHomogeneous, toIdeal_homogeneousHull_eq_self, toIdeal_injective
-/
theorem HomogeneousIdeal.homogeneousHull_toIdeal_eq_self (I : HomogeneousIdeal 𝒜) :
    I.toIdeal.homogeneousHull 𝒜 = I :=
HomogeneousIdeal.toIdeal_injective I.isHomogeneous.toIdeal_homogeneousHull_eq_self

variable (I 𝒜)

/--
theorem `Ideal.toIdeal_homogeneousHull_eq_iSup` / 定理 `Ideal.toIdeal_homogeneousHull_eq_iSup`

English:
theorem Ideal.toIdeal_homogeneousHull_eq_iSup
  proof: by
  rw [← Ideal.span_iUnion]
  apply congr_arg Ideal.span _
  ext1
  simp only [Set.mem_iUnion, Set.mem_image, mem_ofPred_eq, GradedRing.proj_apply, SetLike.exists,
    exists_prop, SetLike.mem_coe]

中文:
定理 理想.toIdeal_homogeneousHull_eq_iSup
  证明: by
  rw [← Ideal.span_iUnion]
  apply congr_arg Ideal.span _
  ext1
  simp only [Set.mem_iUnion, Set.mem_image, mem_ofPred_eq, GradedRing.proj_apply, SetLike.exists,
    exists_prop, SetLike.mem_coe]

Depends on / 依赖: GradedRing, GradedRing.proj_apply, Ideal.span, Ideal.span_iUnion, Set.mem_iUnion, Set.mem_image, SetLike, SetLike.exists, SetLike.mem_coe, congr_arg, exists_prop, mem_coe, mem_iUnion, mem_image, mem_ofPred_eq, proj_apply, span_iUnion
-/
theorem Ideal.toIdeal_homogeneousHull_eq_iSup :
    (I.homogeneousHull 𝒜).toIdeal = ⨆ i, Ideal.span (GradedRing.proj 𝒜 i '' I) := by
  rw [← Ideal.span_iUnion]
  apply congr_arg Ideal.span _
  ext1
  simp only [Set.mem_iUnion, Set.mem_image, mem_ofPred_eq, GradedRing.proj_apply, SetLike.exists,
    exists_prop, SetLike.mem_coe]

/--
theorem `Ideal.homogeneousHull_eq_iSup` / 定理 `Ideal.homogeneousHull_eq_iSup`

English:
theorem Ideal.homogeneousHull_eq_iSup
  proof: by
  ext1
  rw [Ideal.toIdeal_homogeneousHull_eq_iSup]; rw [toIdeal_iSup]

中文:
定理 理想.homogeneousHull_eq_iSup
  证明: by
  ext1
  rw [Ideal.toIdeal_homogeneousHull_eq_iSup]; rw [toIdeal_iSup]

Depends on / 依赖: Ideal.toIdeal_homogeneousHull_eq_iSup, toIdeal_homogeneousHull_eq_iSup, toIdeal_iSup
-/
theorem Ideal.homogeneousHull_eq_iSup :
    I.homogeneousHull 𝒜 =
      ⨆ i, ⟨Ideal.span (GradedRing.proj 𝒜 i '' I), Ideal.homogeneous_span 𝒜 _ (by
        rintro _ ⟨x, -, rfl⟩
        apply SetLike.isHomogeneousElem_coe)⟩ := by
  ext1
  rw [Ideal.toIdeal_homogeneousHull_eq_iSup]; rw [toIdeal_iSup]

end HomogeneousHull

section GaloisConnection

open HomogeneousIdeal

variable [Semiring A] [DecidableEq ι] [AddMonoid ι]
variable [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι -> σ) [GradedRing 𝒜]

/--
theorem `Ideal.homogeneousHull.gc` / 定理 `Ideal.homogeneousHull.gc`

English:
theorem Ideal.homogeneousHull.gc
  statement: GaloisConnection (Ideal.homogeneousHull 𝒜) toIdeal
  proof: fun _ J =>
  ⟨le_trans (Ideal.le_toIdeal_homogeneousHull _ _),
    fun H => J.homogeneousHull_toIdeal_eq_self ▸ Ideal.homogeneousHull_mono 𝒜 H⟩

中文:
定理 理想.homogeneousHull.gc
  结论: GaloisConnection (理想.homogeneousHull 𝒜) toIdeal
  证明: fun _ J =>
  ⟨le_trans (Ideal.le_toIdeal_homogeneousHull _ _),
    fun H => J.homogeneousHull_toIdeal_eq_self ▸ Ideal.homogeneousHull_mono 𝒜 H⟩
-/
theorem Ideal.homogeneousHull.gc : GaloisConnection (Ideal.homogeneousHull 𝒜) toIdeal := fun _ J =>
  ⟨le_trans (Ideal.le_toIdeal_homogeneousHull _ _),
    fun H => J.homogeneousHull_toIdeal_eq_self ▸ Ideal.homogeneousHull_mono 𝒜 H⟩

/--
Definition of `Ideal.homogeneousHull.gi` / `Ideal.homogeneousHull.gi` 的定义

English:
definition Ideal.homogeneousHull.gi
  signature: : GaloisInsertion (Ideal.homogeneousHull 𝒜) toIdeal where
  body: ⟨I, le_antisymm H (I.le_toIdeal_homogeneousHull 𝒜) ▸ isHomogeneous _⟩
  gc := Ideal.homogeneousHull.gc 𝒜
  le_l_u _ := Ideal.le_toIdeal_homogeneousHull _ _
  choice_eq I H := le_antisymm (I.le_toIdeal_homogeneousHull 𝒜) H

中文:
定义 理想.homogeneousHull.gi
  签名: : Galois嵌入 (理想.homogeneousHull 𝒜) toIdeal where
  定义体: ⟨I, le_antisymm H (I.le_toIdeal_homogeneousHull 𝒜) ▸ isHomogeneous _⟩
  gc := Ideal.homogeneousHull.gc 𝒜
  le_l_u _ := Ideal.le_toIdeal_homogeneousHull _ _
  choice_eq I H := le_antisymm (I.le_toIdeal_homogeneousHull 𝒜) H

Depends on / 依赖: I.le_toIdeal_homogeneousHull, isHomogeneous, le_antisymm, le_toIdeal_homogeneousHull
-/
def Ideal.homogeneousHull.gi : GaloisInsertion (Ideal.homogeneousHull 𝒜) toIdeal where
  choice I H := ⟨I, le_antisymm H (I.le_toIdeal_homogeneousHull 𝒜) ▸ isHomogeneous _⟩
  gc := Ideal.homogeneousHull.gc 𝒜
  le_l_u _ := Ideal.le_toIdeal_homogeneousHull _ _
  choice_eq I H := le_antisymm (I.le_toIdeal_homogeneousHull 𝒜) H

/--
theorem `Ideal.homogeneousHull_eq_sInf` / 定理 `Ideal.homogeneousHull_eq_sInf`

English:
theorem Ideal.homogeneousHull_eq_sInf
  given: (I : Ideal A)
  proof: Eq.symm IsGLB.sInf_eq (Ideal.homogeneousHull.gc 𝒜).isLeast_l.isGLB

中文:
定理 理想.homogeneousHull_eq_sInf
  条件: (I : 理想 A)
  证明: Eq.symm IsGLB.sInf_eq (Ideal.homogeneousHull.gc 𝒜).isLeast_l.isGLB

Depends on / 依赖: Eq.symm, Ideal.homogeneousHull.gc, IsGLB.sInf_eq, homogeneousHull, isLeast_l, isLeast_l.isGLB, sInf_eq
-/
theorem Ideal.homogeneousHull_eq_sInf (I : Ideal A) :
    Ideal.homogeneousHull 𝒜 I = sInf { J : HomogeneousIdeal 𝒜 | I <= J.toIdeal } :=
Eq.symm IsGLB.sInf_eq (Ideal.homogeneousHull.gc 𝒜).isLeast_l.isGLB

end GaloisConnection

section IrrelevantIdeal

namespace HomogeneousIdeal

variable [Semiring A]
variable [DecidableEq ι]
variable [AddCommMonoid ι] [PartialOrder ι] [CanonicallyOrderedAdd ι]
variable [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι -> σ) [GradedRing 𝒜]

open GradedRing SetLike.GradedMonoid DirectSum

/--
Definition of `irrelevant` / `irrelevant` 的定义

English:
definition irrelevant
  signature: : HomogeneousIdeal 𝒜
  body: ⟨RingHom.ker (GradedRing.projZeroRingHom 𝒜), fun i r (hr : (decompose 𝒜 r 0 : A) = 0) => by
    change (decompose 𝒜 (decompose 𝒜 r _ : A) 0 : A) = 0
    by_cases h : i = 0
    · rw [h, hr, decompose_zero, zero_apply, ZeroMemClass.coe_zero]
    · rw [decompose_of_mem_ne 𝒜 (SetLike.coe_mem _) h]⟩

@[i

中文:
定义 irrelevant
  签名: : HomogeneousIdeal 𝒜
  定义体: ⟨RingHom.ker (GradedRing.projZeroRingHom 𝒜), fun i r (hr : (decompose 𝒜 r 0 : A) = 0) => by
    change (decompose 𝒜 (decompose 𝒜 r _ : A) 0 : A) = 0
    by_cases h : i = 0
    · rw [h, hr, decompose_zero, zero_apply, ZeroMemClass.coe_zero]
    · rw [decompose_of_mem_ne 𝒜 (SetLike.coe_mem _) h]⟩

@[i

Depends on / 依赖: GradedRing, GradedRing.projZeroRingHom, RingHom, RingHom.ker, SetLike, SetLike.coe_mem, ZeroMemClass, ZeroMemClass.coe_zero, coe_mem, coe_zero, decompose, decompose_of_mem_ne, decompose_zero, projZeroRingHom, zero_apply
-/
def irrelevant : HomogeneousIdeal 𝒜 :=
  ⟨RingHom.ker (GradedRing.projZeroRingHom 𝒜), fun i r (hr : (decompose 𝒜 r 0 : A) = 0) => by
    change (decompose 𝒜 (decompose 𝒜 r _ : A) 0 : A) = 0
    by_cases h : i = 0
    · rw [h, hr, decompose_zero, zero_apply, ZeroMemClass.coe_zero]
    · rw [decompose_of_mem_ne 𝒜 (SetLike.coe_mem _) h]⟩

@[inherit_doc] scoped notation 𝒜 "₊" => irrelevant 𝒜

@[simp]
/--
theorem `mem_irrelevant_iff` / 定理 `mem_irrelevant_iff`

English:
theorem mem_irrelevant_iff
  given: (a : A)
  proof: Iff.rfl

@[simp]

中文:
定理 mem_irrelevant_iff
  条件: (a : A)
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_irrelevant_iff (a : A) :
    a in 𝒜₊ ↔ proj 𝒜 0 a = 0 :=
  Iff.rfl

@[simp]
/--
theorem `toIdeal_irrelevant` / 定理 `toIdeal_irrelevant`

English:
theorem toIdeal_irrelevant
  proof: rfl

中文:
定理 toIdeal_irrelevant
  证明: rfl
-/
theorem toIdeal_irrelevant :
    𝒜₊.toIdeal = RingHom.ker (GradedRing.projZeroRingHom 𝒜) :=
  rfl

/--
lemma `mem_irrelevant_of_mem` / 引理 `mem_irrelevant_of_mem`

English:
lemma mem_irrelevant_of_mem
  given: {x : A} {i : ι} (hi : 0 < i) (hx : x in 𝒜 i)
  statement: x in 𝒜₊
  proof: by
  rw [mem_irrelevant_iff]; rw [GradedRing.proj_apply]; rw [DirectSum.decompose_of_mem _ hx]; rw [DirectSum.of_eq_of_ne _ _ _ (by aesop)]; rw [ZeroMemClass.coe_zero]

中文:
引理 mem_irrelevant_of_mem
  条件: {x : A} {i : ι} (hi : 0 < i) (hx : x in 𝒜 i)
  结论: x in 𝒜₊
  证明: by
  rw [mem_irrelevant_iff]; rw [GradedRing.proj_apply]; rw [DirectSum.decompose_of_mem _ hx]; rw [DirectSum.of_eq_of_ne _ _ _ (by aesop)]; rw [ZeroMemClass.coe_zero]

Depends on / 依赖: DirectSum, DirectSum.decompose_of_mem, DirectSum.of_eq_of_ne, GradedRing, GradedRing.proj_apply, ZeroMemClass, ZeroMemClass.coe_zero, coe_zero, decompose_of_mem, mem_irrelevant_iff, of_eq_of_ne, proj_apply
-/
lemma mem_irrelevant_of_mem {x : A} {i : ι} (hi : 0 < i) (hx : x in 𝒜 i) : x in 𝒜₊ := by
  rw [mem_irrelevant_iff]; rw [GradedRing.proj_apply]; rw [DirectSum.decompose_of_mem _ hx]; rw [DirectSum.of_eq_of_ne _ _ _ (by aesop)]; rw [ZeroMemClass.coe_zero]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `irrelevant_eq_iSup` / 引理 `irrelevant_eq_iSup`

English:
lemma irrelevant_eq_iSup
  statement: 𝒜₊.toAddSubmonoid = ⨆ i > 0, .ofClass (𝒜 i)
  proof: by
refine le_antisymm (fun x hx => ?_) iSup₂_le fun i hi x hx => mem_irrelevant_of_mem _ hi hx
  classical rw [← DirectSum.sum_support_decompose 𝒜 x]
  refine sum_mem fun j hj => ?_
  by_cases hj₀ : j = 0
  · classical exact (DFinsupp.mem_support_iff.mp hj <| hj₀ ▸ (by simpa using hx)).elim
· exact 

中文:
引理 irrelevant_eq_iSup
  结论: 𝒜₊.toAddSubmonoid = ⨆ i > 0, .ofClass (𝒜 i)
  证明: by
refine le_antisymm (fun x hx => ?_) iSup₂_le fun i hi x hx => mem_irrelevant_of_mem _ hi hx
  classical rw [← DirectSum.sum_support_decompose 𝒜 x]
  refine sum_mem fun j hj => ?_
  by_cases hj₀ : j = 0
  · classical exact (DFinsupp.mem_support_iff.mp hj <| hj₀ ▸ (by simpa using hx)).elim
· exact 

Depends on / 依赖: AddSubmonoid, AddSubmonoid.mem_iSup_of_mem, DFinsupp, DFinsupp.mem_support_iff.mp, DirectSum, DirectSum.sum_support_decompose, Subtype, Subtype.prop, classical, le_antisymm, mem_iSup_of_mem, mem_irrelevant_of_mem, mem_support_iff, pos_of_ne_zero, sum_mem, sum_support_decompose
-/
lemma irrelevant_eq_iSup : 𝒜₊.toAddSubmonoid = ⨆ i > 0, .ofClass (𝒜 i) := by
refine le_antisymm (fun x hx => ?_) iSup₂_le fun i hi x hx => mem_irrelevant_of_mem _ hi hx
  classical rw [← DirectSum.sum_support_decompose 𝒜 x]
  refine sum_mem fun j hj => ?_
  by_cases hj₀ : j = 0
  · classical exact (DFinsupp.mem_support_iff.mp hj <| hj₀ ▸ (by simpa using hx)).elim
· exact AddSubmonoid.mem_iSup_of_mem j AddSubmonoid.mem_iSup_of_mem (pos_of_ne_zero hj₀)
      Subtype.prop _

open AddSubmonoid Set in
/--
lemma `irrelevant_eq_closure` / 引理 `irrelevant_eq_closure`

English:
lemma irrelevant_eq_closure
  statement: 𝒜₊.toAddSubmonoid = .closure (⋃ i > 0, 𝒜 i)
  proof: by
  rw [irrelevant_eq_iSup]
exact le_antisymm (iSup_le fun i => iSup_le fun hi _ hx => subset_closure <| mem_biUnion hi hx)
closure_le.mpr iUnion_subset fun i => iUnion_subset fun hi => le_biSup (ofClass <| 𝒜 ·) hi

中文:
引理 irrelevant_eq_closure
  结论: 𝒜₊.toAddSubmonoid = .closure (⋃ i > 0, 𝒜 i)
  证明: by
  rw [irrelevant_eq_iSup]
exact le_antisymm (iSup_le fun i => iSup_le fun hi _ hx => subset_closure <| mem_biUnion hi hx)
closure_le.mpr iUnion_subset fun i => iUnion_subset fun hi => le_biSup (ofClass <| 𝒜 ·) hi

Depends on / 依赖: closure_le, closure_le.mpr, iSup_le, iUnion_subset, irrelevant_eq_iSup, le_antisymm, le_biSup, mem_biUnion, ofClass, subset_closure
-/
lemma irrelevant_eq_closure : 𝒜₊.toAddSubmonoid = .closure (⋃ i > 0, 𝒜 i) := by
  rw [irrelevant_eq_iSup]
exact le_antisymm (iSup_le fun i => iSup_le fun hi _ hx => subset_closure <| mem_biUnion hi hx)
closure_le.mpr iUnion_subset fun i => iUnion_subset fun hi => le_biSup (ofClass <| 𝒜 ·) hi

open AddSubmonoid Set in
/--
lemma `irrelevant_eq_span` / 引理 `irrelevant_eq_span`

English:
lemma irrelevant_eq_span
  statement: 𝒜₊.toIdeal = .span (⋃ i > 0, 𝒜 i)
  proof: le_antisymm ((irrelevant_eq_closure 𝒜).trans_le <| closure_le.mpr Ideal.subset_span)
Ideal.span_le.mpr iUnion_subset fun _ => iUnion_subset fun hi _ hx =>
    mem_irrelevant_of_mem _ hi hx

中文:
引理 irrelevant_eq_span
  结论: 𝒜₊.toIdeal = .span (⋃ i > 0, 𝒜 i)
  证明: le_antisymm ((irrelevant_eq_closure 𝒜).trans_le <| closure_le.mpr Ideal.subset_span)
Ideal.span_le.mpr iUnion_subset fun _ => iUnion_subset fun hi _ hx =>
    mem_irrelevant_of_mem _ hi hx

Depends on / 依赖: Ideal.span_le.mpr, Ideal.subset_span, closure_le, closure_le.mpr, iUnion_subset, irrelevant_eq_closure, le_antisymm, mem_irrelevant_of_mem, span_le, subset_span, trans_le
-/
lemma irrelevant_eq_span : 𝒜₊.toIdeal = .span (⋃ i > 0, 𝒜 i) :=
le_antisymm ((irrelevant_eq_closure 𝒜).trans_le <| closure_le.mpr Ideal.subset_span)
Ideal.span_le.mpr iUnion_subset fun _ => iUnion_subset fun hi _ hx =>
    mem_irrelevant_of_mem _ hi hx

/--
lemma `toAddSubmonoid_irrelevant_le` / 引理 `toAddSubmonoid_irrelevant_le`

English:
lemma toAddSubmonoid_irrelevant_le
  given: {P : AddSubmonoid A}
  proof: by
  rw [irrelevant_eq_iSup]; rw [iSup₂_le_iff]

中文:
引理 toAddSubmonoid_irrelevant_le
  条件: {P : 加法子幺半群 A}
  证明: by
  rw [irrelevant_eq_iSup]; rw [iSup₂_le_iff]

Depends on / 依赖: irrelevant_eq_iSup
-/
lemma toAddSubmonoid_irrelevant_le {P : AddSubmonoid A} :
    𝒜₊.toAddSubmonoid <= P ↔ forall i > 0, .ofClass (𝒜 i) <= P := by
  rw [irrelevant_eq_iSup]; rw [iSup₂_le_iff]

/--
lemma `toIdeal_irrelevant_le` / 引理 `toIdeal_irrelevant_le`

English:
lemma toIdeal_irrelevant_le
  given: {I : Ideal A}
  proof: toAddSubmonoid_irrelevant_le _

中文:
引理 toIdeal_irrelevant_le
  条件: {I : 理想 A}
  证明: toAddSubmonoid_irrelevant_le _

Depends on / 依赖: toAddSubmonoid_irrelevant_le
-/
lemma toIdeal_irrelevant_le {I : Ideal A} :
    𝒜₊.toIdeal <= I ↔ forall i > 0, .ofClass (𝒜 i) <= I.toAddSubmonoid :=
  toAddSubmonoid_irrelevant_le _

/--
lemma `irrelevant_le` / 引理 `irrelevant_le`

English:
lemma irrelevant_le
  given: {P : HomogeneousIdeal 𝒜}
  proof: toIdeal_irrelevant_le _

中文:
引理 irrelevant_le
  条件: {P : HomogeneousIdeal 𝒜}
  证明: toIdeal_irrelevant_le _

Depends on / 依赖: toIdeal_irrelevant_le
-/
lemma irrelevant_le {P : HomogeneousIdeal 𝒜} :
    𝒜₊ <= P ↔ forall i > 0, .ofClass (𝒜 i) <= P.toAddSubmonoid :=
  toIdeal_irrelevant_le _

end HomogeneousIdeal

end IrrelevantIdeal
