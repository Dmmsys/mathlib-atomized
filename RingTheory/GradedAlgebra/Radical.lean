/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Eric Wieser
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal

/-!

This file contains a proof that the radical of any homogeneous ideal is a homogeneous ideal

## Main statements

* `Ideal.IsHomogeneous.isPrime_iff`: for any `I : Ideal A`, if `I` is homogeneous, then
  `I` is prime if and only if `I` is homogeneously prime, i.e. `I ≠ ⊤` and if `x, y` are
  homogeneous elements such that `x * y ∈ I`, then at least one of `x,y` is in `I`.
* `Ideal.IsPrime.homogeneousCore`: for any `I : Ideal A`, if `I` is prime, then
  `I.homogeneous_core 𝒜` (i.e. the largest homogeneous ideal contained in `I`) is also prime.
* `Ideal.IsHomogeneous.radical`: for any `I : Ideal A`, if `I` is homogeneous, then the
  radical of `I` is homogeneous as well.
* `HomogeneousIdeal.radical`: for any `I : HomogeneousIdeal 𝒜`, `I.radical` is the
  radical of `I` as a `HomogeneousIdeal 𝒜`.

## Implementation details

Throughout this file, the indexing type `ι` of grading is assumed to be a
linearly ordered cancellative monoid. This might be stronger than necessary but cancelling
property is strictly necessary; for a counterexample of how `Ideal.IsHomogeneous.isPrime_iff`
fails for a non-cancellative set see `Counterexamples/HomogeneousPrimeNotPrime.lean`.

## Tags

homogeneous, radical
-/

@[expose] public section


open GradedRing DirectSum SetLike Finset

variable {ι σ A : Type*}
variable [CommRing A]
variable [AddCommMonoid ι] [LinearOrder ι] [IsOrderedCancelAddMonoid ι]
variable [SetLike σ A] [AddSubmonoidClass σ A] {𝒜 : ι -> σ} [GradedRing 𝒜]

/--
theorem `Ideal.IsHomogeneous.isPrime_of_homogeneous_mem_or_mem` / 定理 `Ideal.IsHomogeneous.isPrime_of_homogeneous_mem_or_mem`

English:
theorem Ideal.IsHomogeneous.isPrime_of_homogeneous_mem_or_mem
  statement: {I : Ideal A} (hI : I.IsHomogeneous 𝒜)
  proof: ⟨I_ne_top, by
    intro x y hxy
    by_contra! ⟨rid₁, rid₂⟩
    classical
      /-
        The idea of the proof is the following :
        since `x * y ∈ I` and `I` homogeneous, then `proj i (x * y) ∈ I` for any `i : ι`.
        Then consider two sets `{i ∈ x.support | xᵢ ∉ I}` and `{j ∈ y.support 

中文:
定理 理想.IsHomogeneous.isPrime_of_homogeneous_mem_or_mem
  结论: {I : 理想 A} (hI : I.IsHomogeneous 𝒜)
  证明: ⟨I_ne_top, by
    intro x y hxy
    by_contra! ⟨rid₁, rid₂⟩
    classical
      /-
        The idea of the proof is the following :
        since `x * y ∈ I` and `I` homogeneous, then `proj i (x * y) ∈ I` for any `i : ι`.
        Then consider two sets `{i ∈ x.support | xᵢ ∉ I}` and `{j ∈ y.support 

Depends on / 依赖: I_ne_top, classical
-/
theorem Ideal.IsHomogeneous.isPrime_of_homogeneous_mem_or_mem {I : Ideal A} (hI : I.IsHomogeneous 𝒜)
    (I_ne_top : I != ⊤)
    (homogeneous_mem_or_mem :
      forall {x y : A}, IsHomogeneousElem 𝒜 x -> IsHomogeneousElem 𝒜 y -> x * y in I -> x in I ∨ y in I) :
    Ideal.IsPrime I :=
  ⟨I_ne_top, by
    intro x y hxy
    by_contra! ⟨rid₁, rid₂⟩
    classical
      /-
        The idea of the proof is the following :
        since `x * y ∈ I` and `I` homogeneous, then `proj i (x * y) ∈ I` for any `i : ι`.
        Then consider two sets `{i ∈ x.support | xᵢ ∉ I}` and `{j ∈ y.support | yⱼ ∉ J}`;
        let `max₁, max₂` be the maximum of the two sets, then `proj (max₁ + max₂) (x * y) ∈ I`.
        Then, `proj max₁ x ∉ I` and `proj max₂ j ∉ I`
        but `proj i x ∈ I` for all `max₁ < i` and `proj j y ∈ I` for all `max₂ < j`.
        ` proj (max₁ + max₂) (x * y)`
        `= ∑ {(i, j) ∈ supports | i + j = max₁ + max₂}, xᵢ * yⱼ`
        `= proj max₁ x * proj max₂ y`
        ` + ∑ {(i, j) ∈ supports \ {(max₁, max₂)} | i + j = max₁ + max₂}, xᵢ * yⱼ`.
        This is a contradiction, because both `proj (max₁ + max₂) (x * y) ∈ I` and the sum on the
        right-hand side is in `I` however `proj max₁ x * proj max₂ y` is not in `I`.
        -/
      set set₁ := {i in (decompose 𝒜 x).support | proj 𝒜 i x ∉ I} with set₁_eq
      set set₂ := {i in (decompose 𝒜 y).support | proj 𝒜 i y ∉ I} with set₂_eq
      have nonempty :
        forall x : A, x ∉ I -> {i in (decompose 𝒜 x).support | proj 𝒜 i x ∉ I}.Nonempty := by
        intro x hx
        rw [filter_nonempty_iff]
        contrapose! hx
        simp_rw [proj_apply] at hx
        rw [← sum_support_decompose 𝒜 x]
        exact Ideal.sum_mem _ hx
      set max₁ := set₁.max' (nonempty x rid₁)
      set max₂ := set₂.max' (nonempty y rid₂)
      have mem_max₁ : max₁ in set₁ := max'_mem set₁ (nonempty x rid₁)
      have mem_max₂ : max₂ in set₂ := max'_mem set₂ (nonempty y rid₂)
      replace hxy : proj 𝒜 (max₁ + max₂) (x * y) in I := hI _ hxy
      have mem_I : proj 𝒜 max₁ x * proj 𝒜 max₂ y in I := by
        set antidiag :=
          {z in (decompose 𝒜 x).support ×ˢ (decompose 𝒜 y).support | z.1 + z.2 = max₁ + max₂}
           with ha
        have mem_antidiag : (max₁, max₂) in antidiag := by
          simp only [antidiag, mem_filter, mem_product]
          exact ⟨⟨mem_of_mem_filter _ mem_max₁, mem_of_mem_filter _ mem_max₂⟩, trivial⟩
        have eq_add_sum :=
          calc
            proj 𝒜 (max₁ + max₂) (x * y) = ∑ ij in antidiag, proj 𝒜 ij.1 x * proj 𝒜 ij.2 y := by
              simp_rw [ha, proj_apply, DirectSum.decompose_mul, DirectSum.coe_mul_apply 𝒜]
            _ =
                proj 𝒜 max₁ x * proj 𝒜 max₂ y +
                  ∑ ij in antidiag.erase (max₁, max₂), proj 𝒜 ij.1 x * proj 𝒜 ij.2 y :=
              (add_sum_erase _ _ mem_antidiag).symm
        rw [eq_sub_of_add_eq eq_add_sum.symm]
        refine Ideal.sub_mem _ hxy (Ideal.sum_mem _ fun z H => ?_)
        rcases z with ⟨i, j⟩
        simp only [antidiag, mem_erase, Prod.mk_inj, Ne, mem_filter, mem_product] at H
        rcases H with ⟨H₁, ⟨H₂, H₃⟩, H₄⟩
        have max_lt : max₁ < i ∨ max₂ < j := by
          convert! le_or_lt_of_add_le_add H₄.ge using 1
          rw [Ne.le_iff_lt]
          rintro rfl
          cases H₁ ⟨rfl, add_left_cancel H₄⟩
        rcases max_lt with max_lt | max_lt
        · -- in this case `max₁ < i`, then `xᵢ ∈ I`; for otherwise `i ∈ set₁` then `i ≤ max₁`.
          have notMem : i ∉ set₁ := fun h =>
            lt_irrefl _ ((max'_lt_iff set₁ (nonempty x rid₁)).mp max_lt i h)
          rw [set₁_eq] at notMem
          simp only [not_and, Classical.not_not, mem_filter] at notMem
          exact Ideal.mul_mem_right _ I (notMem H₂)
        · -- in this case `max₂ < j`, then `yⱼ ∈ I`; for otherwise `j ∈ set₂`, then `j ≤ max₂`.
          have notMem : j ∉ set₂ := fun h =>
            lt_irrefl _ ((max'_lt_iff set₂ (nonempty y rid₂)).mp max_lt j h)
          rw [set₂_eq] at notMem
          simp only [not_and, Classical.not_not, mem_filter] at notMem
          exact Ideal.mul_mem_left I _ (notMem H₃)
      have notMem_I : proj 𝒜 max₁ x * proj 𝒜 max₂ y ∉ I := by
        have neither_mem : proj 𝒜 max₁ x ∉ I ∧ proj 𝒜 max₂ y ∉ I := by
          rw [mem_filter] at mem_max₁ mem_max₂
          exact ⟨mem_max₁.2, mem_max₂.2⟩
        intro _rid
        rcases homogeneous_mem_or_mem ⟨max₁, SetLike.coe_mem _⟩ ⟨max₂, SetLike.coe_mem _⟩ mem_I
          with h | h
        · apply neither_mem.1 h
        · apply neither_mem.2 h
      exact notMem_I mem_I⟩

/--
theorem `Ideal.IsHomogeneous.isPrime_iff` / 定理 `Ideal.IsHomogeneous.isPrime_iff`

English:
theorem Ideal.IsHomogeneous.isPrime_iff
  given: {I : Ideal A} (h : I.IsHomogeneous 𝒜)
  proof: ⟨fun HI => ⟨HI.ne_top, fun _ _ hxy => Ideal.IsPrime.mem_or_mem HI hxy⟩,
    fun ⟨I_ne_top, homogeneous_mem_or_mem⟩ =>
    h.isPrime_of_homogeneous_mem_or_mem I_ne_top @homogeneous_mem_or_mem⟩

中文:
定理 理想.IsHomogeneous.isPrime_iff
  条件: {I : 理想 A} (h : I.IsHomogeneous 𝒜)
  证明: ⟨fun HI => ⟨HI.ne_top, fun _ _ hxy => Ideal.IsPrime.mem_or_mem HI hxy⟩,
    fun ⟨I_ne_top, homogeneous_mem_or_mem⟩ =>
    h.isPrime_of_homogeneous_mem_or_mem I_ne_top @homogeneous_mem_or_mem⟩

Depends on / 依赖: HI.ne_top, I_ne_top, Ideal.IsPrime.mem_or_mem, IsPrime, h.isPrime_of_homogeneous_mem_or_mem, homogeneous_mem_or_mem, isPrime_of_homogeneous_mem_or_mem, mem_or_mem, ne_top
-/
theorem Ideal.IsHomogeneous.isPrime_iff {I : Ideal A} (h : I.IsHomogeneous 𝒜) :
    I.IsPrime ↔
      I != ⊤ ∧
        forall {x y : A},
          IsHomogeneousElem 𝒜 x -> IsHomogeneousElem 𝒜 y -> x * y in I -> x in I ∨ y in I :=
  ⟨fun HI => ⟨HI.ne_top, fun _ _ hxy => Ideal.IsPrime.mem_or_mem HI hxy⟩,
    fun ⟨I_ne_top, homogeneous_mem_or_mem⟩ =>
    h.isPrime_of_homogeneous_mem_or_mem I_ne_top @homogeneous_mem_or_mem⟩

/--
theorem `Ideal.IsPrime.homogeneousCore` / 定理 `Ideal.IsPrime.homogeneousCore`

English:
theorem Ideal.IsPrime.homogeneousCore
  given: {I : Ideal A} (h : I.IsPrime)
  proof: by
  apply (Ideal.homogeneousCore 𝒜 I).isHomogeneous.isPrime_of_homogeneous_mem_or_mem
  · exact ne_top_of_le_ne_top h.ne_top (Ideal.toIdeal_homogeneousCore_le 𝒜 I)
  rintro x y hx hy hxy
  have H := h.mem_or_mem (Ideal.toIdeal_homogeneousCore_le 𝒜 I hxy)
  refine H.imp ?_ ?_
  · exact Ideal.mem_hom

中文:
定理 理想.是素.homogeneousCore
  条件: {I : 理想 A} (h : I.是素)
  证明: by
  apply (Ideal.homogeneousCore 𝒜 I).isHomogeneous.isPrime_of_homogeneous_mem_or_mem
  · exact ne_top_of_le_ne_top h.ne_top (Ideal.toIdeal_homogeneousCore_le 𝒜 I)
  rintro x y hx hy hxy
  have H := h.mem_or_mem (Ideal.toIdeal_homogeneousCore_le 𝒜 I hxy)
  refine H.imp ?_ ?_
  · exact Ideal.mem_hom

Depends on / 依赖: H.imp, Ideal.homogeneousCore, Ideal.mem_homogeneousCore_of_homogeneous_of_mem, Ideal.toIdeal_homogeneousCore_le, h.mem_or_mem, h.ne_top, homogeneousCore, isHomogeneous, isHomogeneous.isPrime_of_homogeneous_mem_or_mem, isPrime_of_homogeneous_mem_or_mem, mem_homogeneousCore_of_homogeneous_of_mem, mem_or_mem, ne_top, ne_top_of_le_ne_top, toIdeal_homogeneousCore_le
-/
theorem Ideal.IsPrime.homogeneousCore {I : Ideal A} (h : I.IsPrime) :
    (I.homogeneousCore 𝒜).toIdeal.IsPrime := by
  apply (Ideal.homogeneousCore 𝒜 I).isHomogeneous.isPrime_of_homogeneous_mem_or_mem
  · exact ne_top_of_le_ne_top h.ne_top (Ideal.toIdeal_homogeneousCore_le 𝒜 I)
  rintro x y hx hy hxy
  have H := h.mem_or_mem (Ideal.toIdeal_homogeneousCore_le 𝒜 I hxy)
  refine H.imp ?_ ?_
  · exact Ideal.mem_homogeneousCore_of_homogeneous_of_mem hx
  · exact Ideal.mem_homogeneousCore_of_homogeneous_of_mem hy

/--
theorem `Ideal.IsHomogeneous.radical_eq` / 定理 `Ideal.IsHomogeneous.radical_eq`

English:
theorem Ideal.IsHomogeneous.radical_eq
  given: {I : Ideal A} (hI : I.IsHomogeneous 𝒜)
  proof: by
  rw [Ideal.radical_eq_sInf]
  apply le_antisymm
  · exact sInf_le_sInf fun J => And.right
  · refine sInf_le_sInf_of_isCoinitialFor ?_
    rintro J ⟨HJ₁, HJ₂⟩
    refine ⟨(J.homogeneousCore 𝒜).toIdeal, ?_, J.toIdeal_homogeneousCore_le _⟩
    refine ⟨HomogeneousIdeal.isHomogeneous _, ?_, HJ₂.homo

中文:
定理 理想.IsHomogeneous.radical_eq
  条件: {I : 理想 A} (hI : I.IsHomogeneous 𝒜)
  证明: by
  rw [Ideal.radical_eq_sInf]
  apply le_antisymm
  · exact sInf_le_sInf fun J => And.right
  · refine sInf_le_sInf_of_isCoinitialFor ?_
    rintro J ⟨HJ₁, HJ₂⟩
    refine ⟨(J.homogeneousCore 𝒜).toIdeal, ?_, J.toIdeal_homogeneousCore_le _⟩
    refine ⟨HomogeneousIdeal.isHomogeneous _, ?_, HJ₂.homo

Depends on / 依赖: And.right, HomogeneousIdeal, HomogeneousIdeal.isHomogeneous, Ideal.homogeneousCore_mono, Ideal.radical_eq_sInf, J.homogeneousCore, J.toIdeal_homogeneousCore_le, hI.toIdeal_homogeneousCore_eq_self.symm.trans_le, homogeneousCore, homogeneousCore_mono, isHomogeneous, le_antisymm, radical_eq_sInf, sInf_le_sInf, sInf_le_sInf_of_isCoinitialFor, toIdeal, toIdeal_homogeneousCore_eq_self, toIdeal_homogeneousCore_le, trans_le
-/
theorem Ideal.IsHomogeneous.radical_eq {I : Ideal A} (hI : I.IsHomogeneous 𝒜) :
    I.radical = InfSet.sInf { J | Ideal.IsHomogeneous 𝒜 J ∧ I <= J ∧ J.IsPrime } := by
  rw [Ideal.radical_eq_sInf]
  apply le_antisymm
  · exact sInf_le_sInf fun J => And.right
  · refine sInf_le_sInf_of_isCoinitialFor ?_
    rintro J ⟨HJ₁, HJ₂⟩
    refine ⟨(J.homogeneousCore 𝒜).toIdeal, ?_, J.toIdeal_homogeneousCore_le _⟩
    refine ⟨HomogeneousIdeal.isHomogeneous _, ?_, HJ₂.homogeneousCore⟩
    exact hI.toIdeal_homogeneousCore_eq_self.symm.trans_le (Ideal.homogeneousCore_mono _ HJ₁)

/--
theorem `Ideal.IsHomogeneous.radical` / 定理 `Ideal.IsHomogeneous.radical`

English:
theorem Ideal.IsHomogeneous.radical
  given: {I : Ideal A} (h : I.IsHomogeneous 𝒜)
  proof: by
  rw [h.radical_eq]
  exact Ideal.IsHomogeneous.sInf fun _ => And.left

中文:
定理 理想.IsHomogeneous.radical
  条件: {I : 理想 A} (h : I.IsHomogeneous 𝒜)
  证明: by
  rw [h.radical_eq]
  exact Ideal.IsHomogeneous.sInf fun _ => And.left

Depends on / 依赖: And.left, Ideal.IsHomogeneous.sInf, IsHomogeneous, h.radical_eq, radical_eq
-/
theorem Ideal.IsHomogeneous.radical {I : Ideal A} (h : I.IsHomogeneous 𝒜) :
    I.radical.IsHomogeneous 𝒜 := by
  rw [h.radical_eq]
  exact Ideal.IsHomogeneous.sInf fun _ => And.left

/--
Definition of `HomogeneousIdeal.radical` / `HomogeneousIdeal.radical` 的定义

English:
definition HomogeneousIdeal.radical
  signature: (I : HomogeneousIdeal 𝒜)
  body: ⟨I.toIdeal.radical, I.isHomogeneous.radical⟩

@[simp]

中文:
定义 HomogeneousIdeal.radical
  签名: (I : HomogeneousIdeal 𝒜)
  定义体: ⟨I.toIdeal.radical, I.isHomogeneous.radical⟩

@[simp]

Depends on / 依赖: I.isHomogeneous.radical, I.toIdeal.radical, isHomogeneous, radical, toIdeal
-/
def HomogeneousIdeal.radical (I : HomogeneousIdeal 𝒜) : HomogeneousIdeal 𝒜 :=
  ⟨I.toIdeal.radical, I.isHomogeneous.radical⟩

@[simp]
/--
theorem `HomogeneousIdeal.coe_radical` / 定理 `HomogeneousIdeal.coe_radical`

English:
theorem HomogeneousIdeal.coe_radical
  given: (I : HomogeneousIdeal 𝒜)
  proof: rfl

中文:
定理 HomogeneousIdeal.coe_radical
  条件: (I : HomogeneousIdeal 𝒜)
  证明: rfl
-/
theorem HomogeneousIdeal.coe_radical (I : HomogeneousIdeal 𝒜) :
    I.radical.toIdeal = I.toIdeal.radical := rfl
