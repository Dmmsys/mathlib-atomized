/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Chain
public import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas
public import Mathlib.LinearAlgebra.RootSystem.IsValuedIn

/-!
# Bases for root pairings / systems

This file contains a theory of bases for root pairings / systems.

## Implementation details

For reduced root pairings `RootSystem.Base` is equivalent to the usual definition appearing in the
informal literature (e.g., it follows from [serre1965](Ch. V, §8, Proposition 7) that
`RootSystem.Base` is equivalent to both [serre1965](Ch. V, §8, Definition 5) and
[bourbaki1968](Ch. VI, §1.5) for reduced pairings). However for non-reduced root pairings, it is
more restrictive because it includes axioms on coroots as well as on roots. For example by
`RootPairing.Base.eq_one_or_neg_one_of_mem_support_of_smul_mem` it is clear that the 1-dimensional
root system `{-2, -1, 0, 1, 2} ⊆ ℝ` has no base in the sense of `RootSystem.Base`.

It is also worth remembering that it is only for reduced root systems that one has the simply
transitive action of the Weyl group on the set of bases, and that the Weyl group of a non-reduced
root system is the same as that of the reduced root system obtained by passing to the indivisible
roots.

For infinite root systems, `RootSystem.Base` is usually not the right notion: linear independence
is too strong.

## Main definitions / results:
* `RootSystem.Base`: a base of a root pairing.
* `RootSystem.Base.IsPos`: the predicate that a (co)root is positive relative to a base.
* `RootSystem.Base.induction_add`: an induction principle for predicates on (co)roots which
  respect addition of a simple root.
* `RootSystem.Base.induction_reflect`: an induction principle for predicates on (co)roots which
  respect reflection in a simple root.

## TODO

* Develop a theory of base / separation / positive roots for infinite systems which specialises to
  the concept here for finite systems.

-/

@[expose] public section

noncomputable section

open Function Set Submodule
open FaithfulSMul (algebraMap_injective)
open Module
open End (invtSubmodule mem_invtSubmodule)

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

namespace RootPairing

/--
Definition of `Base` / `Base` 的定义

English:
structure Base
  parameters: (P : RootPairing ι R M N)
  axioms and operations (5):
    - support : Finset ι
    - linearIndepOn_root : LinearIndepOn R P.root support
    - linearIndepOn_coroot : LinearIndepOn R P.coroot support
    - root_mem_or_neg_mem((i : ι)) : P.root i in AddSubmonoid.closure (P.root '' support) ∨ -P.root i in AddSubmonoid.closure (P.root '' support)
    - coroot_mem_or_neg_mem((i : ι)) : P.coroot i in AddSubmonoid.closure (P.coroot '' support) ∨ -P.coroot i in AddSubmonoid.closure (P.coroot '' support)

中文:
结构 Base
  参数: (P : RootPairing ι R M N)
  公理与运算 (5 个):
    - support : 有限集 ι
    - linearIndepOn_root : LinearIndepOn R P.root support
    - linearIndepOn_coroot : LinearIndepOn R P.coroot support
    - root_mem_or_neg_mem((i : ι)) : P.root i in 加法子幺半群.closure (P.root '' support) ∨ -P.root i in 加法子幺半群.closure (P.root '' support)
    - coroot_mem_or_neg_mem((i : ι)) : P.coroot i in 加法子幺半群.closure (P.coroot '' support) ∨ -P.coroot i in 加法子幺半群.closure (P.coroot '' support)
-/
structure Base (P : RootPairing ι R M N) where
  /-- The indices of the simple roots / coroots. -/
  support : Finset ι
  linearIndepOn_root : LinearIndepOn R P.root support
  linearIndepOn_coroot : LinearIndepOn R P.coroot support
  root_mem_or_neg_mem (i : ι) : P.root i in AddSubmonoid.closure (P.root '' support) ∨
                               -P.root i in AddSubmonoid.closure (P.root '' support)
  coroot_mem_or_neg_mem (i : ι) : P.coroot i in AddSubmonoid.closure (P.coroot '' support) ∨
                                 -P.coroot i in AddSubmonoid.closure (P.coroot '' support)

namespace Base

section RootPairing

variable {P : RootPairing ι R M N} (b : P.Base)

/--
lemma `support_nonempty` / 引理 `support_nonempty`

English:
lemma support_nonempty
  given: [Nonempty ι] [NeZero (2 : R)]
  statement: b.support.Nonempty
  proof: by
  by_contra! contra
  inhabit ι
  simpa [P.ne_zero default, contra] using b.root_mem_or_neg_mem default

中文:
引理 support_nonempty
  条件: [非空 ι] [NeZero (2 : R)]
  结论: b.support.非空
  证明: by
  by_contra! contra
  inhabit ι
  simpa [P.ne_zero default, contra] using b.root_mem_or_neg_mem default

Depends on / 依赖: P.ne_zero, b.root_mem_or_neg_mem, contra, inhabit, ne_zero, root_mem_or_neg_mem
-/
lemma support_nonempty [Nonempty ι] [NeZero (2 : R)] : b.support.Nonempty := by
  by_contra! contra
  inhabit ι
  simpa [P.ne_zero default, contra] using b.root_mem_or_neg_mem default

/--
Definition of `flip` / `flip` 的定义

English:
definition flip
  signature: :
  body: b.support
  linearIndepOn_root := b.linearIndepOn_coroot
  linearIndepOn_coroot := b.linearIndepOn_root
  root_mem_or_neg_mem := b.coroot_mem_or_neg_mem
  coroot_mem_or_neg_mem := b.root_mem_or_neg_mem

include b in

中文:
定义 flip
  签名: :
  定义体: b.support
  linearIndepOn_root := b.linearIndepOn_coroot
  linearIndepOn_coroot := b.linearIndepOn_root
  root_mem_or_neg_mem := b.coroot_mem_or_neg_mem
  coroot_mem_or_neg_mem := b.root_mem_or_neg_mem

include b in
-/
@[simps] protected def flip :
    P.flip.Base where
  support := b.support
  linearIndepOn_root := b.linearIndepOn_coroot
  linearIndepOn_coroot := b.linearIndepOn_root
  root_mem_or_neg_mem := b.coroot_mem_or_neg_mem
  coroot_mem_or_neg_mem := b.root_mem_or_neg_mem

include b in
/--
lemma `root_ne_neg_of_ne` / 引理 `root_ne_neg_of_ne`

English:
lemma root_ne_neg_of_ne
  statement: [Nontrivial R] {i j : ι}
  proof: by
  classical
  intro contra
  have := linearIndepOn_iff'.mp b.linearIndepOn_root ({i, j} : Finset ι) 1
    (by simp [Set.insert_subset_iff, hi, hj]) (by simp [Finset.sum_pair hij, contra])
  simp_all

中文:
引理 root_ne_neg_of_ne
  结论: [非平凡 R] {i j : ι}
  证明: by
  classical
  intro contra
  have := linearIndepOn_iff'.mp b.linearIndepOn_root ({i, j} : Finset ι) 1
    (by simp [Set.insert_subset_iff, hi, hj]) (by simp [Finset.sum_pair hij, contra])
  simp_all

Depends on / 依赖: Finset, Finset.sum_pair, Set.insert_subset_iff, b.linearIndepOn_root, classical, contra, insert_subset_iff, linearIndepOn_iff, linearIndepOn_root, sum_pair
-/
lemma root_ne_neg_of_ne [Nontrivial R] {i j : ι}
    (hi : i in b.support) (hj : j in b.support) (hij : i != j) :
    P.root i != -P.root j := by
  classical
  intro contra
  have := linearIndepOn_iff'.mp b.linearIndepOn_root ({i, j} : Finset ι) 1
    (by simp [Set.insert_subset_iff, hi, hj]) (by simp [Finset.sum_pair hij, contra])
  simp_all

/--
lemma `linearIndependent_pair_of_ne` / 引理 `linearIndependent_pair_of_ne`

English:
lemma linearIndependent_pair_of_ne
  given: {i j : b.support} (hij : i != j)
  proof: by
  have : ({(j : ι), (i : ι)} : Set ι) subseteq b.support := by simp [pair_subset_iff]
  rw [← linearIndepOn_id_range_iff (by simp_all)]
simpa [image_pair] using LinearIndepOn.id_image b.linearIndepOn_root.mono this

中文:
引理 linearIndependent_pair_of_ne
  条件: {i j : b.support} (hij : i != j)
  证明: by
  have : ({(j : ι), (i : ι)} : Set ι) subseteq b.support := by simp [pair_subset_iff]
  rw [← linearIndepOn_id_range_iff (by simp_all)]
simpa [image_pair] using LinearIndepOn.id_image b.linearIndepOn_root.mono this

Depends on / 依赖: LinearIndepOn, LinearIndepOn.id_image, b.linearIndepOn_root.mono, b.support, id_image, image_pair, linearIndepOn_id_range_iff, linearIndepOn_root, pair_subset_iff, subseteq, support
-/
lemma linearIndependent_pair_of_ne {i j : b.support} (hij : i != j) :
    LinearIndependent R ![P.root i, P.root j] := by
  have : ({(j : ι), (i : ι)} : Set ι) subseteq b.support := by simp [pair_subset_iff]
  rw [← linearIndepOn_id_range_iff (by simp_all)]
simpa [image_pair] using LinearIndepOn.id_image b.linearIndepOn_root.mono this

/--
lemma `root_mem_span_int` / 引理 `root_mem_span_int`

English:
lemma root_mem_span_int
  given: (i : ι)
  proof: by
  have := b.root_mem_or_neg_mem i
  simp only [← span_nat_eq_addSubmonoidClosure, mem_toAddSubmonoid] at this
  rw [← span_span_of_tower (R := Nat)]
  rcases this with hi | hi
  · exact subset_span hi
  · rw [← neg_mem_iff]
    exact subset_span hi

中文:
引理 root_mem_span_int
  条件: (i : ι)
  证明: by
  have := b.root_mem_or_neg_mem i
  simp only [← span_nat_eq_addSubmonoidClosure, mem_toAddSubmonoid] at this
  rw [← span_span_of_tower (R := Nat)]
  rcases this with hi | hi
  · exact subset_span hi
  · rw [← neg_mem_iff]
    exact subset_span hi

Depends on / 依赖: b.root_mem_or_neg_mem, mem_toAddSubmonoid, neg_mem_iff, root_mem_or_neg_mem, span_nat_eq_addSubmonoidClosure, span_span_of_tower, subset_span
-/
lemma root_mem_span_int (i : ι) :
    P.root i in span Int (P.root '' b.support) := by
  have := b.root_mem_or_neg_mem i
  simp only [← span_nat_eq_addSubmonoidClosure, mem_toAddSubmonoid] at this
  rw [← span_span_of_tower (R := Nat)]
  rcases this with hi | hi
  · exact subset_span hi
  · rw [← neg_mem_iff]
    exact subset_span hi

/--
lemma `coroot_mem_span_int` / 引理 `coroot_mem_span_int`

English:
lemma coroot_mem_span_int
  given: (i : ι)
  proof: b.flip.root_mem_span_int i

@[simp]

中文:
引理 coroot_mem_span_int
  条件: (i : ι)
  证明: b.flip.root_mem_span_int i

@[simp]

Depends on / 依赖: b.flip.root_mem_span_int, root_mem_span_int
-/
lemma coroot_mem_span_int (i : ι) :
    P.coroot i in span Int (P.coroot '' b.support) :=
  b.flip.root_mem_span_int i

@[simp]
/--
lemma `span_int_root_support` / 引理 `span_int_root_support`

English:
lemma span_int_root_support
  proof: by
  refine le_antisymm (span_mono <| image_subset_range _ _) (span_le.mpr ?_)
  rintro - ⟨i, rfl⟩
  exact b.root_mem_span_int i

@[simp]

中文:
引理 span_int_root_support
  证明: by
  refine le_antisymm (span_mono <| image_subset_range _ _) (span_le.mpr ?_)
  rintro - ⟨i, rfl⟩
  exact b.root_mem_span_int i

@[simp]

Depends on / 依赖: b.root_mem_span_int, image_subset_range, le_antisymm, root_mem_span_int, span_le, span_le.mpr, span_mono
-/
lemma span_int_root_support :
    span Int (P.root '' b.support) = span Int (range P.root) := by
  refine le_antisymm (span_mono <| image_subset_range _ _) (span_le.mpr ?_)
  rintro - ⟨i, rfl⟩
  exact b.root_mem_span_int i

@[simp]
/--
lemma `span_int_coroot_support` / 引理 `span_int_coroot_support`

English:
lemma span_int_coroot_support
  proof: b.flip.span_int_root_support

@[simp]

中文:
引理 span_int_coroot_support
  证明: b.flip.span_int_root_support

@[simp]

Depends on / 依赖: b.flip.span_int_root_support, span_int_root_support
-/
lemma span_int_coroot_support :
    span Int (P.coroot '' b.support) = span Int (range P.coroot) :=
  b.flip.span_int_root_support

@[simp]
/--
lemma `span_root_support` / 引理 `span_root_support`

English:
lemma span_root_support
  proof: by
  rw [← span_span_of_tower (R := Int)]; rw [span_int_root_support]; rw [span_span_of_tower]

@[simp]

中文:
引理 span_root_support
  证明: by
  rw [← span_span_of_tower (R := Int)]; rw [span_int_root_support]; rw [span_span_of_tower]

@[simp]

Depends on / 依赖: span_int_root_support, span_span_of_tower
-/
lemma span_root_support :
    span R (P.root '' b.support) = P.rootSpan R := by
  rw [← span_span_of_tower (R := Int)]; rw [span_int_root_support]; rw [span_span_of_tower]

@[simp]
/--
lemma `span_coroot_support` / 引理 `span_coroot_support`

English:
lemma span_coroot_support
  proof: b.flip.span_root_support

中文:
引理 span_coroot_support
  证明: b.flip.span_root_support

Depends on / 依赖: b.flip.span_root_support, span_root_support
-/
lemma span_coroot_support :
    span R (P.coroot '' b.support) = P.corootSpan R :=
  b.flip.span_root_support

set_option backward.isDefEq.respectTransparency.types false in
open Finsupp in
/--
lemma `eq_one_or_neg_one_of_mem_support_of_smul_mem_aux` / 引理 `eq_one_or_neg_one_of_mem_support_of_smul_mem_aux`

English:
lemma eq_one_or_neg_one_of_mem_support_of_smul_mem_aux
  statement: [Finite ι]
  proof: by
  obtain ⟨j, hj⟩ := ht
  obtain ⟨f, hf⟩ : exists f : b.support -> Int, P.coroot i = ∑ i, (t * f i) • P.coroot i := by
    have : P.coroot j in span Int (P.coroot '' b.support) := b.coroot_mem_span_int j
    rw [image_eq_range]; rw [mem_span_range_iff_exists_fun] at this
    refine this.imp fun f hf => ?_
    simp only [Finset.coe_sort_coe] at hf
    simp_rw [mul_smul, ← Finset.smul_sum, Int.cast_smul_eq_zsmul, hf,
      coroot_eq_smul_coroot_iff.mpr hj]
  use f ⟨i, h⟩
  replace hf : P.coroot i = linearCombination R (fun k : b.support => P.coroot k)
      (t • (linearEquivFunOnFinite R _ _).symm (fun x => (f x : R))) := by
    rw [map_smul]; rw [linearCombination_eq_fintype_linearCombination_apply]; rw [Fintype.linearCombination_apply]; rw [hf]
    simp_rw [mul_smul, ← Finset.smul_sum]
  let g : b.support ->₀ R := single ⟨i, h⟩ 1
  have hg : P.coroot i = linearCombination R (fun k : b.support => P.coroot k) g := by simp [g]
  rw [hg] at hf
  have : Injective (linearCombination R fun k : b.support => P.coroot k) := b.linearIndepOn_coroot
  simpa [g, linearEquivFunOnFinite, mul_comm t] using (DFunLike.congr_fun (this hf) ⟨i, h⟩).symm

中文:
引理 eq_one_or_neg_one_of_mem_support_of_smul_mem_aux
  结论: [有限 ι]
  证明: by
  obtain ⟨j, hj⟩ := ht
  obtain ⟨f, hf⟩ : exists f : b.support -> Int, P.coroot i = ∑ i, (t * f i) • P.coroot i := by
    have : P.coroot j in span Int (P.coroot '' b.support) := b.coroot_mem_span_int j
    rw [image_eq_range]; rw [mem_span_range_iff_exists_fun] at this
    refine this.imp fun f hf => ?_
    simp only [Finset.coe_sort_coe] at hf
    simp_rw [mul_smul, ← Finset.smul_sum, Int.cast_smul_eq_zsmul, hf,
      coroot_eq_smul_coroot_iff.mpr hj]
  use f ⟨i, h⟩
  replace hf : P.coroot i = linearCombination R (fun k : b.support => P.coroot k)
      (t • (linearEquivFunOnFinite R _ _).symm (fun x => (f x : R))) := by
    rw [map_smul]; rw [linearCombination_eq_fintype_linearCombination_apply]; rw [Fintype.linearCombination_apply]; rw [hf]
    simp_rw [mul_smul, ← Finset.smul_sum]
  let g : b.support ->₀ R := single ⟨i, h⟩ 1
  have hg : P.coroot i = linearCombination R (fun k : b.support => P.coroot k) g := by simp [g]
  rw [hg] at hf
  have : Injective (linearCombination R fun k : b.support => P.coroot k) := b.linearIndepOn_coroot
  simpa [g, linearEquivFunOnFinite, mul_comm t] using (DFunLike.congr_fun (this hf) ⟨i, h⟩).symm

Depends on / 依赖: Finset, Finset.coe_sort_coe, Finset.smul_sum, Int.cast_smul_eq_zsmul, P.coroot, b.coroot_mem_span_int, b.support, cast_smul_eq_zsmul, coe_sort_coe, coroot, coroot_eq_smul_coroot_iff, coroot_eq_smul_coroot_iff.mpr, coroot_mem_span_int, image_eq_range, linearCombination, mem_span_range_iff_exists_fun, mul_smul, replace, simp_rw, smul_sum
-/
lemma eq_one_or_neg_one_of_mem_support_of_smul_mem_aux [Finite ι]
    [IsAddTorsionFree M] [IsAddTorsionFree N]
    (i : ι) (h : i in b.support) (t : R) (ht : t • P.root i in range P.root) :
    exists z : Int, z * t = 1 := by
  obtain ⟨j, hj⟩ := ht
  obtain ⟨f, hf⟩ : exists f : b.support -> Int, P.coroot i = ∑ i, (t * f i) • P.coroot i := by
    have : P.coroot j in span Int (P.coroot '' b.support) := b.coroot_mem_span_int j
    rw [image_eq_range]; rw [mem_span_range_iff_exists_fun] at this
    refine this.imp fun f hf => ?_
    simp only [Finset.coe_sort_coe] at hf
    simp_rw [mul_smul, ← Finset.smul_sum, Int.cast_smul_eq_zsmul, hf,
      coroot_eq_smul_coroot_iff.mpr hj]
  use f ⟨i, h⟩
  replace hf : P.coroot i = linearCombination R (fun k : b.support => P.coroot k)
      (t • (linearEquivFunOnFinite R _ _).symm (fun x => (f x : R))) := by
    rw [map_smul]; rw [linearCombination_eq_fintype_linearCombination_apply]; rw [Fintype.linearCombination_apply]; rw [hf]
    simp_rw [mul_smul, ← Finset.smul_sum]
  let g : b.support ->₀ R := single ⟨i, h⟩ 1
  have hg : P.coroot i = linearCombination R (fun k : b.support => P.coroot k) g := by simp [g]
  rw [hg] at hf
  have : Injective (linearCombination R fun k : b.support => P.coroot k) := b.linearIndepOn_coroot
  simpa [g, linearEquivFunOnFinite, mul_comm t] using (DFunLike.congr_fun (this hf) ⟨i, h⟩).symm

variable [CharZero R]

/--
lemma `eq_one_or_neg_one_of_mem_support_of_smul_mem` / 引理 `eq_one_or_neg_one_of_mem_support_of_smul_mem`

English:
lemma eq_one_or_neg_one_of_mem_support_of_smul_mem
  statement: [Finite ι]
  proof: by
  obtain ⟨z, hz⟩ := b.eq_one_or_neg_one_of_mem_support_of_smul_mem_aux i h t ht
  replace ht : (z : R) • P.coroot i in range P.coroot := by
    obtain ⟨j, hj⟩ := ht
    simpa only [coroot_eq_smul_coroot_iff.mpr hj, smul_smul, hz, one_smul] using mem_range_self j
  obtain ⟨w, hw⟩ := b.flip.eq_one_or_neg_one_of_mem_support_of_smul_mem_aux i h _ ht
  have : (z : R) * w = 1 := by
    simpa [mul_mul_mul_comm _ t, mul_comm t, mul_comm _ (z : R), hz] using congr_arg₂ (· * ·) hz hw
  suffices z = 1 ∨ z = -1 by
    rcases this with rfl | rfl
    · left; simpa using hz
    · right; simpa [neg_eq_iff_eq_neg] using hz
  norm_cast at this
  rw [Int.mul_eq_one_iff_eq_one_or_neg_one] at this
  tauto

中文:
引理 eq_one_or_neg_one_of_mem_support_of_smul_mem
  结论: [有限 ι]
  证明: by
  obtain ⟨z, hz⟩ := b.eq_one_or_neg_one_of_mem_support_of_smul_mem_aux i h t ht
  replace ht : (z : R) • P.coroot i in range P.coroot := by
    obtain ⟨j, hj⟩ := ht
    simpa only [coroot_eq_smul_coroot_iff.mpr hj, smul_smul, hz, one_smul] using mem_range_self j
  obtain ⟨w, hw⟩ := b.flip.eq_one_or_neg_one_of_mem_support_of_smul_mem_aux i h _ ht
  have : (z : R) * w = 1 := by
    simpa [mul_mul_mul_comm _ t, mul_comm t, mul_comm _ (z : R), hz] using congr_arg₂ (· * ·) hz hw
  suffices z = 1 ∨ z = -1 by
    rcases this with rfl | rfl
    · left; simpa using hz
    · right; simpa [neg_eq_iff_eq_neg] using hz
  norm_cast at this
  rw [Int.mul_eq_one_iff_eq_one_or_neg_one] at this
  tauto

Depends on / 依赖: P.coroot, b.eq_one_or_neg_one_of_mem_support_of_smul_mem_aux, b.flip.eq_one_or_neg_one_of_mem_support_of_smul_mem_aux, coroot, coroot_eq_smul_coroot_iff, coroot_eq_smul_coroot_iff.mpr, eq_one_or_neg_one_of_mem_support_of_smul_mem_aux, mem_range_self, mul_comm, mul_mul_mul_comm, one_smul, replace, smul_smul
-/
lemma eq_one_or_neg_one_of_mem_support_of_smul_mem [Finite ι]
    [IsAddTorsionFree M] [IsAddTorsionFree N]
    (i : ι) (h : i in b.support) (t : R) (ht : t • P.root i in range P.root) :
    t = 1 ∨ t = -1 := by
  obtain ⟨z, hz⟩ := b.eq_one_or_neg_one_of_mem_support_of_smul_mem_aux i h t ht
  replace ht : (z : R) • P.coroot i in range P.coroot := by
    obtain ⟨j, hj⟩ := ht
    simpa only [coroot_eq_smul_coroot_iff.mpr hj, smul_smul, hz, one_smul] using mem_range_self j
  obtain ⟨w, hw⟩ := b.flip.eq_one_or_neg_one_of_mem_support_of_smul_mem_aux i h _ ht
  have : (z : R) * w = 1 := by
    simpa [mul_mul_mul_comm _ t, mul_comm t, mul_comm _ (z : R), hz] using congr_arg₂ (· * ·) hz hw
  suffices z = 1 ∨ z = -1 by
    rcases this with rfl | rfl
    · left; simpa using hz
    · right; simpa [neg_eq_iff_eq_neg] using hz
  norm_cast at this
  rw [Int.mul_eq_one_iff_eq_one_or_neg_one] at this
  tauto

/--
lemma `pos_or_neg_of_sum_smul_root_mem` / 引理 `pos_or_neg_of_sum_smul_root_mem`

English:
lemma pos_or_neg_of_sum_smul_root_mem
  statement: (f : ι -> Int)
  proof: by
  suffices forall (f : ι -> Int)
      (hf : ∑ j in b.support, f j • P.root j in AddSubmonoid.closure (P.root '' b.support))
      (hf₀ : f.support subseteq b.support) (hf' : f != 0), 0 < f by
    obtain ⟨k, hk⟩ := hf
have hf' : f != 0 := by rintro rfl; exact P.ne_zero k by simp [hk]
    rcases b.root_mem_or_neg_mem k with hk' | hk' <;> rw [hk] at hk'
    · left; exact this f hk' hf₀ hf'
    · right; simpa using this (-f) (by convert! hk'; simp) (by simpa only [support_neg]) (by simpa)
  intro f hf hf₀ hf'
  let f' : b.support -> Int := fun i => f i
  replace hf : ∑ j, f' j • P.root j in AddSubmonoid.closure (P.root '' b.support) := by
    suffices ∑ j, f' j • P.root j = ∑ j in b.support, f j • P.root j by rwa [this]
    rw [← b.support.sum_finset_coe]; rfl
  rw [← span_nat_eq_addSubmonoidClosure]; rw [mem_toAddSubmonoid]; rw [Fintype.mem_span_image_iff_exists_fun] at hf
  obtain ⟨c, hc⟩ := hf
  replace hc (i : b.support) : c i = f' i := Fintype.linearIndependent_iffₛ.mp
    (b.linearIndepOn_root.restrict_scalars' Int) (Int.ofNat ∘ c) f' (by simpa) i
  have aux : 0 <= f := by
    intro i
    by_cases hi : i in b.support
    · change 0 <= f' ⟨i, hi⟩
      simp [← hc]
    · replace hi : i ∉ f.support := by contrapose hi; exact hf₀ hi
      simp_all
  refine Pi.lt_def.mpr ⟨aux, ?_⟩
  by_contra! contra
  replace contra : f = 0 := le_antisymm contra aux
  contradiction

中文:
引理 pos_or_neg_of_sum_smul_root_mem
  结论: (f : ι -> 整数)
  证明: by
  suffices forall (f : ι -> Int)
      (hf : ∑ j in b.support, f j • P.root j in AddSubmonoid.closure (P.root '' b.support))
      (hf₀ : f.support subseteq b.support) (hf' : f != 0), 0 < f by
    obtain ⟨k, hk⟩ := hf
have hf' : f != 0 := by rintro rfl; exact P.ne_zero k by simp [hk]
    rcases b.root_mem_or_neg_mem k with hk' | hk' <;> rw [hk] at hk'
    · left; exact this f hk' hf₀ hf'
    · right; simpa using this (-f) (by convert! hk'; simp) (by simpa only [support_neg]) (by simpa)
  intro f hf hf₀ hf'
  let f' : b.support -> Int := fun i => f i
  replace hf : ∑ j, f' j • P.root j in AddSubmonoid.closure (P.root '' b.support) := by
    suffices ∑ j, f' j • P.root j = ∑ j in b.support, f j • P.root j by rwa [this]
    rw [← b.support.sum_finset_coe]; rfl
  rw [← span_nat_eq_addSubmonoidClosure]; rw [mem_toAddSubmonoid]; rw [Fintype.mem_span_image_iff_exists_fun] at hf
  obtain ⟨c, hc⟩ := hf
  replace hc (i : b.support) : c i = f' i := Fintype.linearIndependent_iffₛ.mp
    (b.linearIndepOn_root.restrict_scalars' Int) (Int.ofNat ∘ c) f' (by simpa) i
  have aux : 0 <= f := by
    intro i
    by_cases hi : i in b.support
    · change 0 <= f' ⟨i, hi⟩
      simp [← hc]
    · replace hi : i ∉ f.support := by contrapose hi; exact hf₀ hi
      simp_all
  refine Pi.lt_def.mpr ⟨aux, ?_⟩
  by_contra! contra
  replace contra : f = 0 := le_antisymm contra aux
  contradiction

Depends on / 依赖: AddSubmonoid, AddSubmonoid.closure, P.ne_zero, P.root, b.root_mem_or_neg_mem, b.suppor, b.support, closure, convert, f.support, ne_zero, root_mem_or_neg_mem, subseteq, suppor, support, support_neg
-/
lemma pos_or_neg_of_sum_smul_root_mem (f : ι -> Int)
    (hf : ∑ j in b.support, f j • P.root j in range P.root) (hf₀ : f.support subseteq b.support) :
    0 < f ∨ f < 0 := by
  suffices forall (f : ι -> Int)
      (hf : ∑ j in b.support, f j • P.root j in AddSubmonoid.closure (P.root '' b.support))
      (hf₀ : f.support subseteq b.support) (hf' : f != 0), 0 < f by
    obtain ⟨k, hk⟩ := hf
have hf' : f != 0 := by rintro rfl; exact P.ne_zero k by simp [hk]
    rcases b.root_mem_or_neg_mem k with hk' | hk' <;> rw [hk] at hk'
    · left; exact this f hk' hf₀ hf'
    · right; simpa using this (-f) (by convert! hk'; simp) (by simpa only [support_neg]) (by simpa)
  intro f hf hf₀ hf'
  let f' : b.support -> Int := fun i => f i
  replace hf : ∑ j, f' j • P.root j in AddSubmonoid.closure (P.root '' b.support) := by
    suffices ∑ j, f' j • P.root j = ∑ j in b.support, f j • P.root j by rwa [this]
    rw [← b.support.sum_finset_coe]; rfl
  rw [← span_nat_eq_addSubmonoidClosure]; rw [mem_toAddSubmonoid]; rw [Fintype.mem_span_image_iff_exists_fun] at hf
  obtain ⟨c, hc⟩ := hf
  replace hc (i : b.support) : c i = f' i := Fintype.linearIndependent_iffₛ.mp
    (b.linearIndepOn_root.restrict_scalars' Int) (Int.ofNat ∘ c) f' (by simpa) i
  have aux : 0 <= f := by
    intro i
    by_cases hi : i in b.support
    · change 0 <= f' ⟨i, hi⟩
      simp [← hc]
    · replace hi : i ∉ f.support := by contrapose hi; exact hf₀ hi
      simp_all
  refine Pi.lt_def.mpr ⟨aux, ?_⟩
  by_contra! contra
  replace contra : f = 0 := le_antisymm contra aux
  contradiction

/--
lemma `not_nonpos_iff_pos_of_sum_mem_range_root` / 引理 `not_nonpos_iff_pos_of_sum_mem_range_root`

English:
lemma not_nonpos_iff_pos_of_sum_mem_range_root
  statement: (f : ι -> Int)
  proof: by
  rw [Pi.lt_def]
  refine ⟨fun h => ⟨?_, ?_⟩, fun ⟨h, ⟨i, hi⟩⟩ contra => by simp [le_antisymm contra h] at hi⟩
  · rcases b.pos_or_neg_of_sum_smul_root_mem f hf hf₀ with h' | h'
    · exact le_of_lt h'
    · exfalso
      exact h (le_of_lt h')
  · contrapose! h; exact h

中文:
引理 not_nonpos_iff_pos_of_sum_mem_range_root
  结论: (f : ι -> 整数)
  证明: by
  rw [Pi.lt_def]
  refine ⟨fun h => ⟨?_, ?_⟩, fun ⟨h, ⟨i, hi⟩⟩ contra => by simp [le_antisymm contra h] at hi⟩
  · rcases b.pos_or_neg_of_sum_smul_root_mem f hf hf₀ with h' | h'
    · exact le_of_lt h'
    · exfalso
      exact h (le_of_lt h')
  · contrapose! h; exact h

Depends on / 依赖: Pi.lt_def, b.pos_or_neg_of_sum_smul_root_mem, contra, contrapose, le_antisymm, le_of_lt, lt_def, pos_or_neg_of_sum_smul_root_mem
-/
lemma not_nonpos_iff_pos_of_sum_mem_range_root (f : ι -> Int)
    (hf : ∑ j in b.support, f j • P.root j in range P.root) (hf₀ : f.support subseteq b.support) :
    (¬ f <= 0) ↔ 0 < f := by
  rw [Pi.lt_def]
  refine ⟨fun h => ⟨?_, ?_⟩, fun ⟨h, ⟨i, hi⟩⟩ contra => by simp [le_antisymm contra h] at hi⟩
  · rcases b.pos_or_neg_of_sum_smul_root_mem f hf hf₀ with h' | h'
    · exact le_of_lt h'
    · exfalso
      exact h (le_of_lt h')
  · contrapose! h; exact h

/--
lemma `not_nonneg_iff_neg_of_sum_mem_range_root` / 引理 `not_nonneg_iff_neg_of_sum_mem_range_root`

English:
lemma not_nonneg_iff_neg_of_sum_mem_range_root
  statement: (f : ι -> Int)
  proof: by
  replace hf : ∑ j in b.support, (-f) j • P.root j in range P.root := by
    rw [← neg_mem_range_root_iff]; simpa
  have := b.not_nonpos_iff_pos_of_sum_mem_range_root (-f) hf (by simpa)
  simp_all

中文:
引理 not_nonneg_iff_neg_of_sum_mem_range_root
  结论: (f : ι -> 整数)
  证明: by
  replace hf : ∑ j in b.support, (-f) j • P.root j in range P.root := by
    rw [← neg_mem_range_root_iff]; simpa
  have := b.not_nonpos_iff_pos_of_sum_mem_range_root (-f) hf (by simpa)
  simp_all

Depends on / 依赖: P.root, b.not_nonpos_iff_pos_of_sum_mem_range_root, b.support, neg_mem_range_root_iff, not_nonpos_iff_pos_of_sum_mem_range_root, replace, support
-/
lemma not_nonneg_iff_neg_of_sum_mem_range_root (f : ι -> Int)
    (hf : ∑ j in b.support, f j • P.root j in range P.root) (hf₀ : f.support subseteq b.support) :
    (¬ 0 <= f) ↔ f < 0 := by
  replace hf : ∑ j in b.support, (-f) j • P.root j in range P.root := by
    rw [← neg_mem_range_root_iff]; simpa
  have := b.not_nonpos_iff_pos_of_sum_mem_range_root (-f) hf (by simpa)
  simp_all

/--
lemma `sub_notMem_range_root` / 引理 `sub_notMem_range_root`

English:
lemma sub_notMem_range_root
  proof: by
  rcases eq_or_ne j i with rfl | hij
  · simpa only [sub_self, mem_range, not_exists] using fun k => P.ne_zero k
  classical
  let f : ι -> Int := fun k => if k = i then 1 else if k = j then -1 else 0
  have hf : ∑ k in b.support, f k • P.root k = P.root i - P.root j := by
    have : {i, j} subseteq b.support := by aesop (add simp Finset.insert_subset_iff)
    rw [← Finset.sum_subset (s₁ := {i]; rw [j}) (s₂ := b.support) (by lia) (by aesop)]; rw [Finset.sum_insert (by grind)]; rw [Finset.sum_singleton]
    simp [f, hij, sub_eq_add_neg]
  intro contra
  rcases b.pos_or_neg_of_sum_smul_root_mem f (by rwa [hf]) (by aesop) with pos | neg
  · simpa [hij, f] using le_of_lt pos j
  · simpa [hij, f] using le_of_lt neg i

中文:
引理 sub_notMem_range_root
  证明: by
  rcases eq_or_ne j i with rfl | hij
  · simpa only [sub_self, mem_range, not_exists] using fun k => P.ne_zero k
  classical
  let f : ι -> Int := fun k => if k = i then 1 else if k = j then -1 else 0
  have hf : ∑ k in b.support, f k • P.root k = P.root i - P.root j := by
    have : {i, j} subseteq b.support := by aesop (add simp Finset.insert_subset_iff)
    rw [← Finset.sum_subset (s₁ := {i]; rw [j}) (s₂ := b.support) (by lia) (by aesop)]; rw [Finset.sum_insert (by grind)]; rw [Finset.sum_singleton]
    simp [f, hij, sub_eq_add_neg]
  intro contra
  rcases b.pos_or_neg_of_sum_smul_root_mem f (by rwa [hf]) (by aesop) with pos | neg
  · simpa [hij, f] using le_of_lt pos j
  · simpa [hij, f] using le_of_lt neg i

Depends on / 依赖: Finset, Finset.insert_subset_iff, Finset.sum_insert, Finset.sum_singleton, Finset.sum_subset, P.ne_zero, P.root, b.support, classical, eq_or_ne, insert_subset_iff, mem_range, ne_zero, not_exists, sub_self, subseteq, sum_insert, sum_singleton, sum_subset, support
-/
lemma sub_notMem_range_root
    {i j : ι} (hi : i in b.support) (hj : j in b.support) :
    P.root i - P.root j ∉ range P.root := by
  rcases eq_or_ne j i with rfl | hij
  · simpa only [sub_self, mem_range, not_exists] using fun k => P.ne_zero k
  classical
  let f : ι -> Int := fun k => if k = i then 1 else if k = j then -1 else 0
  have hf : ∑ k in b.support, f k • P.root k = P.root i - P.root j := by
    have : {i, j} subseteq b.support := by aesop (add simp Finset.insert_subset_iff)
    rw [← Finset.sum_subset (s₁ := {i]; rw [j}) (s₂ := b.support) (by lia) (by aesop)]; rw [Finset.sum_insert (by grind)]; rw [Finset.sum_singleton]
    simp [f, hij, sub_eq_add_neg]
  intro contra
  rcases b.pos_or_neg_of_sum_smul_root_mem f (by rwa [hf]) (by aesop) with pos | neg
  · simpa [hij, f] using le_of_lt pos j
  · simpa [hij, f] using le_of_lt neg i

/--
lemma `sub_notMem_range_coroot` / 引理 `sub_notMem_range_coroot`

English:
lemma sub_notMem_range_coroot
  proof: b.flip.sub_notMem_range_root hi hj

中文:
引理 sub_notMem_range_coroot
  证明: b.flip.sub_notMem_range_root hi hj

Depends on / 依赖: b.flip.sub_notMem_range_root, sub_notMem_range_root
-/
lemma sub_notMem_range_coroot
    {i j : ι} (hi : i in b.support) (hj : j in b.support) :
    P.coroot i - P.coroot j ∉ range P.coroot :=
  b.flip.sub_notMem_range_root hi hj

/--
lemma `pairingIn_le_zero_of_ne` / 引理 `pairingIn_le_zero_of_ne`

English:
lemma pairingIn_le_zero_of_ne
  statement: [IsDomain R] [P.IsCrystallographic] [Finite ι]
  proof: by
  by_contra! h
exact b.sub_notMem_range_root hi hj P.root_sub_root_mem_of_pairingIn_pos h hij

中文:
引理 pairingIn_le_zero_of_ne
  结论: [是整环 R] [P.IsCrystallographic] [有限 ι]
  证明: by
  by_contra! h
exact b.sub_notMem_range_root hi hj P.root_sub_root_mem_of_pairingIn_pos h hij

Depends on / 依赖: P.root_sub_root_mem_of_pairingIn_pos, b.sub_notMem_range_root, root_sub_root_mem_of_pairingIn_pos, sub_notMem_range_root
-/
lemma pairingIn_le_zero_of_ne [IsDomain R] [P.IsCrystallographic] [Finite ι]
    {i j} (hij : i != j) (hi : i in b.support) (hj : j in b.support) :
    P.pairingIn Int i j <= 0 := by
  by_contra! h
exact b.sub_notMem_range_root hi hj P.root_sub_root_mem_of_pairingIn_pos h hij

variable {b}
variable [IsDomain R] [P.IsCrystallographic] [Finite ι] {i j : b.support}

/--
lemma `chainBotCoeff_eq_zero` / 引理 `chainBotCoeff_eq_zero`

English:
lemma chainBotCoeff_eq_zero
  proof: chainBotCoeff_eq_zero_iff.mpr Or.inr b.sub_notMem_range_root j.property i.property

中文:
引理 chainBotCoeff_eq_zero
  证明: chainBotCoeff_eq_zero_iff.mpr Or.inr b.sub_notMem_range_root j.property i.property
-/
@[simp] lemma chainBotCoeff_eq_zero :
    P.chainBotCoeff i j = 0 :=
chainBotCoeff_eq_zero_iff.mpr Or.inr b.sub_notMem_range_root j.property i.property

/--
lemma `chainTopCoeff_eq_of_ne` / 引理 `chainTopCoeff_eq_of_ne`

English:
lemma chainTopCoeff_eq_of_ne
  given: (hij : i != j)
  proof: by
  rw [← chainTopCoeff_sub_chainBotCoeff (b.linearIndependent_pair_of_ne hij)]
  simp

中文:
引理 chainTopCoeff_eq_of_ne
  条件: (hij : i != j)
  证明: by
  rw [← chainTopCoeff_sub_chainBotCoeff (b.linearIndependent_pair_of_ne hij)]
  simp

Depends on / 依赖: b.linearIndependent_pair_of_ne, chainTopCoeff_sub_chainBotCoeff, linearIndependent_pair_of_ne
-/
lemma chainTopCoeff_eq_of_ne (hij : i != j) :
    P.chainTopCoeff i j = -P.pairingIn Int j i := by
  rw [← chainTopCoeff_sub_chainBotCoeff (b.linearIndependent_pair_of_ne hij)]
  simp

end RootPairing

section RootSystem

variable {P : RootPairing ι R M N} (b : P.Base) [P.IsRootSystem]

/--
Definition of `toWeightBasis` / `toWeightBasis` 的定义

English:
definition toWeightBasis
  signature: :
  body: Basis.mk b.linearIndepOn_root by
    change ⊤ <= span R (range <| P.root ∘ ((↑) : b.support -> ι))
    simp [range_comp]

中文:
定义 toWeightBasis
  签名: :
  定义体: Basis.mk b.linearIndepOn_root by
    change ⊤ <= span R (range <| P.root ∘ ((↑) : b.support -> ι))
    simp [range_comp]

Depends on / 依赖: Basis.mk, P.root, b.linearIndepOn_root, b.support, linearIndepOn_root, range_comp, support
-/
def toWeightBasis :
    Basis b.support R M :=
Basis.mk b.linearIndepOn_root by
    change ⊤ <= span R (range <| P.root ∘ ((↑) : b.support -> ι))
    simp [range_comp]

/--
lemma `toWeightBasis_apply` / 引理 `toWeightBasis_apply`

English:
lemma toWeightBasis_apply
  given: (i : b.support)
  proof: by
  simp [toWeightBasis]

中文:
引理 toWeightBasis_apply
  条件: (i : b.support)
  证明: by
  simp [toWeightBasis]
-/
@[simp] lemma toWeightBasis_apply (i : b.support) :
    b.toWeightBasis i = P.root i := by
  simp [toWeightBasis]

/--
lemma `toWeightBasis_repr_root` / 引理 `toWeightBasis_repr_root`

English:
lemma toWeightBasis_repr_root
  given: (i : b.support)
  proof: by
  simp [← LinearEquiv.eq_symm_apply]

中文:
引理 toWeightBasis_repr_root
  条件: (i : b.support)
  证明: by
  simp [← LinearEquiv.eq_symm_apply]
-/
@[simp] lemma toWeightBasis_repr_root (i : b.support) :
    b.toWeightBasis.repr (P.root i) = Finsupp.single i 1 := by
  simp [← LinearEquiv.eq_symm_apply]

/--
Definition of `toCoweightBasis` / `toCoweightBasis` 的定义

English:
definition toCoweightBasis
  signature: :
  body: Base.toWeightBasis (P := P.flip) b.flip

中文:
定义 toCoweightBasis
  签名: :
  定义体: Base.toWeightBasis (P := P.flip) b.flip

Depends on / 依赖: Base.toWeightBasis, P.flip, b.flip, toWeightBasis
-/
def toCoweightBasis :
    Basis b.support R N :=
  Base.toWeightBasis (P := P.flip) b.flip

/--
lemma `toCoweightBasis_apply` / 引理 `toCoweightBasis_apply`

English:
lemma toCoweightBasis_apply
  given: (i : b.support)
  proof: b.flip.toWeightBasis_apply (P := P.flip) i

中文:
引理 toCoweightBasis_apply
  条件: (i : b.support)
  证明: b.flip.toWeightBasis_apply (P := P.flip) i
-/
@[simp] lemma toCoweightBasis_apply (i : b.support) :
    b.toCoweightBasis i = P.coroot i :=
  b.flip.toWeightBasis_apply (P := P.flip) i

/--
lemma `toCoweightBasis_repr_coroot` / 引理 `toCoweightBasis_repr_coroot`

English:
lemma toCoweightBasis_repr_coroot
  given: (i : b.support)
  proof: by
  simp [← LinearEquiv.eq_symm_apply]

中文:
引理 toCoweightBasis_repr_coroot
  条件: (i : b.support)
  证明: by
  simp [← LinearEquiv.eq_symm_apply]
-/
@[simp] lemma toCoweightBasis_repr_coroot (i : b.support) :
    b.toCoweightBasis.repr (P.coroot i) = Finsupp.single i 1 := by
  simp [← LinearEquiv.eq_symm_apply]

end RootSystem

section RootPairing

variable {P : RootPairing ι R M N} (b : P.Base)

include b

/--
lemma `spanIntRootSupport` / 引理 `spanIntRootSupport`

English:
lemma spanIntRootSupport
  proof: by
  refine Submodule.eq_top_iff'.mpr fun ⟨x, hx⟩ => ?_
  rw [← SetLike.mem_coe]; rw [← (injective_subtype (P.rootSpan Int)).mem_set_image]; rw [← Submodule.map_coe]
  simpa [Submodule.map_span, ← image_comp]

中文:
引理 span整数RootSupport
  证明: by
  refine Submodule.eq_top_iff'.mpr fun ⟨x, hx⟩ => ?_
  rw [← SetLike.mem_coe]; rw [← (injective_subtype (P.rootSpan Int)).mem_set_image]; rw [← Submodule.map_coe]
  simpa [Submodule.map_span, ← image_comp]
-/
@[simp] lemma spanIntRootSupport :
    span Int (P.rootSpanMem Int '' b.support) = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun ⟨x, hx⟩ => ?_
  rw [← SetLike.mem_coe]; rw [← (injective_subtype (P.rootSpan Int)).mem_set_image]; rw [← Submodule.map_coe]
  simpa [Submodule.map_span, ← image_comp]

/--
lemma `linearIndependentInt` / 引理 `linearIndependentInt`

English:
lemma linearIndependentInt
  given: [CharZero R]
  proof: ((P.rootSpan Int).subtype.linearIndependent_iff (by simp)).mp
    b.linearIndepOn_root.restrict_scalars' Int

中文:
引理 linearIndependent整数
  条件: [特征零 R]
  证明: ((P.rootSpan Int).subtype.linearIndependent_iff (by simp)).mp
    b.linearIndepOn_root.restrict_scalars' Int

Depends on / 依赖: P.rootSpan, b.linearIndepOn_root.restrict_scalars, linearIndepOn_root, linearIndependent_iff, restrict_scalars, rootSpan, subtype, subtype.linearIndependent_iff
-/
lemma linearIndependentInt [CharZero R] :
    LinearIndependent Int (fun i : b.support => P.rootSpanMem Int i) :=
((P.rootSpan Int).subtype.linearIndependent_iff (by simp)).mp
    b.linearIndepOn_root.restrict_scalars' Int

/--
Definition of `toWeightBasisInt` / `toWeightBasisInt` 的定义

English:
definition toWeightBasisInt
  signature: [CharZero R]
  body: Basis.mk b.linearIndependentInt by
    have : (fun i : b.support => P.rootSpanMem Int i) = P.rootSpanMem Int ∘ ((↑) : b.support -> ι) := rfl
    simp [this, range_comp]

中文:
定义 toWeightBasis整数
  签名: [特征零 R]
  定义体: Basis.mk b.linearIndependentInt by
    have : (fun i : b.support => P.rootSpanMem Int i) = P.rootSpanMem Int ∘ ((↑) : b.support -> ι) := rfl
    simp [this, range_comp]

Depends on / 依赖: Basis.mk, P.rootSpanMem, b.linearIndependentInt, b.support, linearIndependentInt, range_comp, rootSpanMem, support
-/
def toWeightBasisInt [CharZero R] :
    Basis b.support Int (P.rootSpan Int) :=
Basis.mk b.linearIndependentInt by
    have : (fun i : b.support => P.rootSpanMem Int i) = P.rootSpanMem Int ∘ ((↑) : b.support -> ι) := rfl
    simp [this, range_comp]

/--
lemma `coe_toWeightBasisInt_apply` / 引理 `coe_toWeightBasisInt_apply`

English:
lemma coe_toWeightBasisInt_apply
  given: [CharZero R] (i : b.support)
  proof: by
  simp [toWeightBasisInt]

中文:
引理 coe_toWeightBasis整数_apply
  条件: [特征零 R] (i : b.support)
  证明: by
  simp [toWeightBasisInt]
-/
@[simp] lemma coe_toWeightBasisInt_apply [CharZero R] (i : b.support) :
    (b.toWeightBasisInt i : M) = P.root i := by
  simp [toWeightBasisInt]

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
lemma `exists_root_eq_sum_nat_or_neg` / 引理 `exists_root_eq_sum_nat_or_neg`

English:
lemma exists_root_eq_sum_nat_or_neg
  given: (i : ι)
  proof: by
  classical
  simp_rw [← neg_eq_iff_eq_neg]
  suffices forall m in AddSubmonoid.closure (P.root '' b.support),
    exists f : ι -> Nat, f.support subseteq b.support ∧ m = ∑ j in b.support, f j • P.root j by
    rcases b.root_mem_or_neg_mem i with hi | hi
    · obtain ⟨f, hf, hf'⟩ := this _ hi
      exact ⟨f, hf, Or.inl hf'⟩
    · obtain ⟨f, hf, hf'⟩ := this _ hi
      exact ⟨f, hf, Or.inr hf'⟩
  intro m hm
  refine AddSubmonoid.closure_induction ?_ ⟨0, by simp⟩ ?_ hm
  · rintro - ⟨j, hj, rfl⟩
    exact ⟨Pi.single j 1, by simpa, by aesop (add simp Pi.single_apply)⟩
  · intro _ _ _ _ ⟨f, hf, hf'⟩ ⟨g, hg, hg'⟩
    refine ⟨f + g, ?_, by simp [hf', hg', add_smul, Finset.sum_add_distrib]⟩
exact (support_add f g).trans union_subset_iff.mpr ⟨hf, hg⟩

中文:
引理 存在_root_eq_sum_nat_or_neg
  条件: (i : ι)
  证明: by
  classical
  simp_rw [← neg_eq_iff_eq_neg]
  suffices forall m in AddSubmonoid.closure (P.root '' b.support),
    exists f : ι -> Nat, f.support subseteq b.support ∧ m = ∑ j in b.support, f j • P.root j by
    rcases b.root_mem_or_neg_mem i with hi | hi
    · obtain ⟨f, hf, hf'⟩ := this _ hi
      exact ⟨f, hf, Or.inl hf'⟩
    · obtain ⟨f, hf, hf'⟩ := this _ hi
      exact ⟨f, hf, Or.inr hf'⟩
  intro m hm
  refine AddSubmonoid.closure_induction ?_ ⟨0, by simp⟩ ?_ hm
  · rintro - ⟨j, hj, rfl⟩
    exact ⟨Pi.single j 1, by simpa, by aesop (add simp Pi.single_apply)⟩
  · intro _ _ _ _ ⟨f, hf, hf'⟩ ⟨g, hg, hg'⟩
    refine ⟨f + g, ?_, by simp [hf', hg', add_smul, Finset.sum_add_distrib]⟩
exact (support_add f g).trans union_subset_iff.mpr ⟨hf, hg⟩

Depends on / 依赖: AddSubmonoid, AddSubmonoid.closure, AddSubmonoid.closure_induction, Or.inl, Or.inr, P.root, Pi.single, b.root_mem_or_neg_mem, b.support, classical, closure, closure_induction, f.support, neg_eq_iff_eq_neg, root_mem_or_neg_mem, simp_rw, single, subseteq, support
-/
lemma exists_root_eq_sum_nat_or_neg (i : ι) :
    exists f : ι -> Nat, f.support subseteq b.support ∧
      (P.root i = ∑ j in b.support, f j • P.root j ∨
       P.root i = - ∑ j in b.support, f j • P.root j) := by
  classical
  simp_rw [← neg_eq_iff_eq_neg]
  suffices forall m in AddSubmonoid.closure (P.root '' b.support),
    exists f : ι -> Nat, f.support subseteq b.support ∧ m = ∑ j in b.support, f j • P.root j by
    rcases b.root_mem_or_neg_mem i with hi | hi
    · obtain ⟨f, hf, hf'⟩ := this _ hi
      exact ⟨f, hf, Or.inl hf'⟩
    · obtain ⟨f, hf, hf'⟩ := this _ hi
      exact ⟨f, hf, Or.inr hf'⟩
  intro m hm
  refine AddSubmonoid.closure_induction ?_ ⟨0, by simp⟩ ?_ hm
  · rintro - ⟨j, hj, rfl⟩
    exact ⟨Pi.single j 1, by simpa, by aesop (add simp Pi.single_apply)⟩
  · intro _ _ _ _ ⟨f, hf, hf'⟩ ⟨g, hg, hg'⟩
    refine ⟨f + g, ?_, by simp [hf', hg', add_smul, Finset.sum_add_distrib]⟩
exact (support_add f g).trans union_subset_iff.mpr ⟨hf, hg⟩

/--
lemma `exists_root_eq_sum_int` / 引理 `exists_root_eq_sum_int`

English:
lemma exists_root_eq_sum_int
  given: [CharZero R] (i : ι)
  proof: by
  obtain ⟨f, hf, hf' | hf'⟩ := b.exists_root_eq_sum_nat_or_neg i
· refine ⟨Nat.cast ∘ f, by simpa, Or.inl Pi.lt_def.mpr ⟨fun _ => by simp, ?_⟩, by simp [hf']⟩
    by_contra! contra
    replace contra : f = 0 := by ext i; simpa using contra i
exact P.ne_zero i by simp [hf', contra]
· refine ⟨-Nat.cast ∘ f, by simpa, Or.inr Pi.lt_def.mpr ⟨fun _ => by simp, ?_⟩, by simp [hf']⟩
    by_contra! contra
    replace contra : f = 0 := by ext i; simpa using contra i
exact P.ne_zero i by simp [hf', contra]

中文:
引理 存在_root_eq_sum_int
  条件: [特征零 R] (i : ι)
  证明: by
  obtain ⟨f, hf, hf' | hf'⟩ := b.exists_root_eq_sum_nat_or_neg i
· refine ⟨Nat.cast ∘ f, by simpa, Or.inl Pi.lt_def.mpr ⟨fun _ => by simp, ?_⟩, by simp [hf']⟩
    by_contra! contra
    replace contra : f = 0 := by ext i; simpa using contra i
exact P.ne_zero i by simp [hf', contra]
· refine ⟨-Nat.cast ∘ f, by simpa, Or.inr Pi.lt_def.mpr ⟨fun _ => by simp, ?_⟩, by simp [hf']⟩
    by_contra! contra
    replace contra : f = 0 := by ext i; simpa using contra i
exact P.ne_zero i by simp [hf', contra]

Depends on / 依赖: Nat.cast, Or.inl, Or.inr, P.ne_zero, Pi.lt_def.mpr, b.exists_root_eq_sum_nat_or_neg, contra, exists_root_eq_sum_nat_or_neg, lt_def, ne_zero, replace
-/
lemma exists_root_eq_sum_int [CharZero R] (i : ι) :
    exists f : ι -> Int, f.support subseteq b.support ∧ (0 < f ∨ f < 0) ∧
      P.root i = ∑ j in b.support, f j • P.root j := by
  obtain ⟨f, hf, hf' | hf'⟩ := b.exists_root_eq_sum_nat_or_neg i
· refine ⟨Nat.cast ∘ f, by simpa, Or.inl Pi.lt_def.mpr ⟨fun _ => by simp, ?_⟩, by simp [hf']⟩
    by_contra! contra
    replace contra : f = 0 := by ext i; simpa using contra i
exact P.ne_zero i by simp [hf', contra]
· refine ⟨-Nat.cast ∘ f, by simpa, Or.inr Pi.lt_def.mpr ⟨fun _ => by simp, ?_⟩, by simp [hf']⟩
    by_contra! contra
    replace contra : f = 0 := by ext i; simpa using contra i
exact P.ne_zero i by simp [hf', contra]

end RootPairing

section PositiveRoots

variable {P : RootPairing ι R M N} (b : P.Base) [CharZero R]

/--
Definition of `height` / `height` 的定义

English:
definition height
  signature: (i : ι)
  body: ∑ j in b.support, (b.exists_root_eq_sum_int i).choose j

中文:
定义 height
  签名: (i : ι)
  定义体: ∑ j in b.support, (b.exists_root_eq_sum_int i).choose j

Depends on / 依赖: b.exists_root_eq_sum_int, b.support, exists_root_eq_sum_int, support
-/
def height (i : ι) : Int :=
  ∑ j in b.support, (b.exists_root_eq_sum_int i).choose j

variable {b} in
/--
lemma `height_eq_sum` / 引理 `height_eq_sum`

English:
lemma height_eq_sum
  given: {i : ι} {f : ι -> Int} (heq : P.root i = ∑ j in b.support, f j • P.root j)
  proof: by
  suffices forall j in b.support, (b.exists_root_eq_sum_int i).choose j = f j from
    Finset.sum_congr rfl this
  intro j hj
  obtain ⟨-, -, h⟩ := (b.exists_root_eq_sum_int i).choose_spec
  rw [h]; rw [b.support.sum_subtype (p := (· in b.support)) (by simp) (F := inferInstance)]; rw [b.support.sum_subtype (p := (· in b.support)) (by simp) (F := inferInstance)] at heq
  have aux (j : b.support) := Fintype.linearIndependent_iffₛ.mp
      (b.linearIndepOn_root.restrict_scalars' Int) ((b.exists_root_eq_sum_int i).choose ∘ (↑))
      (f ∘ (↑)) (by simpa) j
  simpa using! aux ⟨j, hj⟩

中文:
引理 height_eq_sum
  条件: {i : ι} {f : ι -> 整数} (heq : P.root i = ∑ j in b.support, f j • P.root j)
  证明: by
  suffices forall j in b.support, (b.exists_root_eq_sum_int i).choose j = f j from
    Finset.sum_congr rfl this
  intro j hj
  obtain ⟨-, -, h⟩ := (b.exists_root_eq_sum_int i).choose_spec
  rw [h]; rw [b.support.sum_subtype (p := (· in b.support)) (by simp) (F := inferInstance)]; rw [b.support.sum_subtype (p := (· in b.support)) (by simp) (F := inferInstance)] at heq
  have aux (j : b.support) := Fintype.linearIndependent_iffₛ.mp
      (b.linearIndepOn_root.restrict_scalars' Int) ((b.exists_root_eq_sum_int i).choose ∘ (↑))
      (f ∘ (↑)) (by simpa) j
  simpa using! aux ⟨j, hj⟩

Depends on / 依赖: Finset, Finset.sum_congr, Fintype, Fintype.linearIndependent_iff, b.exists_root_eq_sum_int, b.linearIndepOn_root.restrict_scalars, b.support, b.support.sum_subtype, choose_spec, exists_root_eq_sum_int, linearIndepOn_root, restrict_scalars, sum_congr, sum_subtype, support
-/
lemma height_eq_sum {i : ι} {f : ι -> Int} (heq : P.root i = ∑ j in b.support, f j • P.root j) :
    b.height i = ∑ j in b.support, f j := by
  suffices forall j in b.support, (b.exists_root_eq_sum_int i).choose j = f j from
    Finset.sum_congr rfl this
  intro j hj
  obtain ⟨-, -, h⟩ := (b.exists_root_eq_sum_int i).choose_spec
  rw [h]; rw [b.support.sum_subtype (p := (· in b.support)) (by simp) (F := inferInstance)]; rw [b.support.sum_subtype (p := (· in b.support)) (by simp) (F := inferInstance)] at heq
  have aux (j : b.support) := Fintype.linearIndependent_iffₛ.mp
      (b.linearIndepOn_root.restrict_scalars' Int) ((b.exists_root_eq_sum_int i).choose ∘ (↑))
      (f ∘ (↑)) (by simpa) j
  simpa using! aux ⟨j, hj⟩

/--
lemma `height_ne_zero` / 引理 `height_ne_zero`

English:
lemma height_ne_zero
  given: (i : ι)
  proof: by
  obtain ⟨f, hf₀, hf₁, hf₂⟩ := b.exists_root_eq_sum_int i
  rw [height_eq_sum hf₂]
  rcases hf₁ with pos | neg
  · refine (Finset.sum_pos' (fun i _ => pos.le i) ?_).ne'
    by_contra! contra
    replace contra (j : ι) : f j = 0 := by
      by_cases hj : j in f.support
      · exact le_antisymm (contra j (hf₀ hj)) (pos.le j)
      · simpa using hj
exact P.ne_zero i by simp [hf₂, contra]
  · refine (Finset.sum_neg' (fun i _ => neg.le i) ?_).ne
    by_contra! contra
    replace contra (j : ι) : f j = 0 := by
      by_cases hj : j in f.support
      · exact le_antisymm (neg.le j) (contra j (hf₀ hj))
      · simpa using hj
exact P.ne_zero i by simp [hf₂, contra]

中文:
引理 height_ne_zero
  条件: (i : ι)
  证明: by
  obtain ⟨f, hf₀, hf₁, hf₂⟩ := b.exists_root_eq_sum_int i
  rw [height_eq_sum hf₂]
  rcases hf₁ with pos | neg
  · refine (Finset.sum_pos' (fun i _ => pos.le i) ?_).ne'
    by_contra! contra
    replace contra (j : ι) : f j = 0 := by
      by_cases hj : j in f.support
      · exact le_antisymm (contra j (hf₀ hj)) (pos.le j)
      · simpa using hj
exact P.ne_zero i by simp [hf₂, contra]
  · refine (Finset.sum_neg' (fun i _ => neg.le i) ?_).ne
    by_contra! contra
    replace contra (j : ι) : f j = 0 := by
      by_cases hj : j in f.support
      · exact le_antisymm (neg.le j) (contra j (hf₀ hj))
      · simpa using hj
exact P.ne_zero i by simp [hf₂, contra]

Depends on / 依赖: Finset, Finset.sum_neg, Finset.sum_pos, P.ne_zero, b.exists_root_eq_sum_int, contra, exists_root_eq_sum_int, f.support, height_eq_sum, le_antisymm, ne_zero, neg.le, pos.le, replace, sum_neg, sum_pos, support
-/
lemma height_ne_zero (i : ι) :
    b.height i != 0 := by
  obtain ⟨f, hf₀, hf₁, hf₂⟩ := b.exists_root_eq_sum_int i
  rw [height_eq_sum hf₂]
  rcases hf₁ with pos | neg
  · refine (Finset.sum_pos' (fun i _ => pos.le i) ?_).ne'
    by_contra! contra
    replace contra (j : ι) : f j = 0 := by
      by_cases hj : j in f.support
      · exact le_antisymm (contra j (hf₀ hj)) (pos.le j)
      · simpa using hj
exact P.ne_zero i by simp [hf₂, contra]
  · refine (Finset.sum_neg' (fun i _ => neg.le i) ?_).ne
    by_contra! contra
    replace contra (j : ι) : f j = 0 := by
      by_cases hj : j in f.support
      · exact le_antisymm (neg.le j) (contra j (hf₀ hj))
      · simpa using hj
exact P.ne_zero i by simp [hf₂, contra]

/--
lemma `height_reflectionPerm_self` / 引理 `height_reflectionPerm_self`

English:
lemma height_reflectionPerm_self
  given: (i : ι)
  proof: P.indexNeg
    b.height (-i) = -b.height i := by
  let := P.indexNeg
  obtain ⟨f, hf₀, hf₁, hf₂⟩ := b.exists_root_eq_sum_int i
  have hf₃ : P.root (-i) = ∑ j in b.support, (-f) j • P.root j := by simpa
  simp only [height_eq_sum hf₂, height_eq_sum hf₃, Pi.neg_apply, Finset.sum_neg_distrib]

中文:
引理 height_reflectionPerm_self
  条件: (i : ι)
  证明: P.indexNeg
    b.height (-i) = -b.height i := by
  let := P.indexNeg
  obtain ⟨f, hf₀, hf₁, hf₂⟩ := b.exists_root_eq_sum_int i
  have hf₃ : P.root (-i) = ∑ j in b.support, (-f) j • P.root j := by simpa
  simp only [height_eq_sum hf₂, height_eq_sum hf₃, Pi.neg_apply, Finset.sum_neg_distrib]

Depends on / 依赖: P.indexNeg, indexNeg
-/
lemma height_reflectionPerm_self (i : ι) :
    letI := P.indexNeg
    b.height (-i) = -b.height i := by
  let := P.indexNeg
  obtain ⟨f, hf₀, hf₁, hf₂⟩ := b.exists_root_eq_sum_int i
  have hf₃ : P.root (-i) = ∑ j in b.support, (-f) j • P.root j := by simpa
  simp only [height_eq_sum hf₂, height_eq_sum hf₃, Pi.neg_apply, Finset.sum_neg_distrib]

variable {b} in
/--
lemma `height_one_of_mem_support` / 引理 `height_one_of_mem_support`

English:
lemma height_one_of_mem_support
  given: {i : ι} (hi : i in b.support)
  proof: by
  classical
  have : P.root i = ∑ j in b.support, (Pi.single i 1 : ι -> Int) j • P.root j := by
    rw [Finset.sum_eq_single_of_mem i hi (by simp_all)]; simp
  simpa [height_eq_sum this]

中文:
引理 height_one_of_mem_support
  条件: {i : ι} (hi : i in b.support)
  证明: by
  classical
  have : P.root i = ∑ j in b.support, (Pi.single i 1 : ι -> Int) j • P.root j := by
    rw [Finset.sum_eq_single_of_mem i hi (by simp_all)]; simp
  simpa [height_eq_sum this]

Depends on / 依赖: Finset, Finset.sum_eq_single_of_mem, P.root, Pi.single, b.support, classical, height_eq_sum, single, sum_eq_single_of_mem, support
-/
lemma height_one_of_mem_support {i : ι} (hi : i in b.support) :
    b.height i = 1 := by
  classical
  have : P.root i = ∑ j in b.support, (Pi.single i 1 : ι -> Int) j • P.root j := by
    rw [Finset.sum_eq_single_of_mem i hi (by simp_all)]; simp
  simpa [height_eq_sum this]

/--
lemma `height_add` / 引理 `height_add`

English:
lemma height_add
  given: {i j k : ι} (hk : P.root k = P.root i + P.root j)
  proof: by
  obtain ⟨f, -, -, hf⟩ := b.exists_root_eq_sum_int i
  obtain ⟨g, -, -, hg⟩ := b.exists_root_eq_sum_int j
  have hfg : P.root k = ∑ l in b.support, (f + g) l • P.root l := by
    simp_rw [Pi.add_apply, add_smul, Finset.sum_add_distrib, ← hf, ← hg, hk]
  simp_rw [height_eq_sum hf, height_eq_sum hg, height_eq_sum hfg, ← Finset.sum_add_distrib,
    Pi.add_apply]

中文:
引理 height_add
  条件: {i j k : ι} (hk : P.root k = P.root i + P.root j)
  证明: by
  obtain ⟨f, -, -, hf⟩ := b.exists_root_eq_sum_int i
  obtain ⟨g, -, -, hg⟩ := b.exists_root_eq_sum_int j
  have hfg : P.root k = ∑ l in b.support, (f + g) l • P.root l := by
    simp_rw [Pi.add_apply, add_smul, Finset.sum_add_distrib, ← hf, ← hg, hk]
  simp_rw [height_eq_sum hf, height_eq_sum hg, height_eq_sum hfg, ← Finset.sum_add_distrib,
    Pi.add_apply]

Depends on / 依赖: Finset, Finset.sum_add_distrib, P.root, Pi.add_apply, add_apply, add_smul, b.exists_root_eq_sum_int, b.support, exists_root_eq_sum_int, height_eq_sum, simp_rw, sum_add_distrib, support
-/
lemma height_add {i j k : ι} (hk : P.root k = P.root i + P.root j) :
    b.height k = b.height i + b.height j := by
  obtain ⟨f, -, -, hf⟩ := b.exists_root_eq_sum_int i
  obtain ⟨g, -, -, hg⟩ := b.exists_root_eq_sum_int j
  have hfg : P.root k = ∑ l in b.support, (f + g) l • P.root l := by
    simp_rw [Pi.add_apply, add_smul, Finset.sum_add_distrib, ← hf, ← hg, hk]
  simp_rw [height_eq_sum hf, height_eq_sum hg, height_eq_sum hfg, ← Finset.sum_add_distrib,
    Pi.add_apply]

/--
lemma `height_sub` / 引理 `height_sub`

English:
lemma height_sub
  given: {i j k : ι} (hk : P.root k = P.root i - P.root j)
  proof: by
  let := P.indexNeg
  replace hk : P.root k = P.root i + P.root (-j) := by simpa [← sub_eq_add_neg]
  rw [sub_eq_add_neg]; rw [← b.height_reflectionPerm_self]; rw [b.height_add hk]

中文:
引理 height_sub
  条件: {i j k : ι} (hk : P.root k = P.root i - P.root j)
  证明: by
  let := P.indexNeg
  replace hk : P.root k = P.root i + P.root (-j) := by simpa [← sub_eq_add_neg]
  rw [sub_eq_add_neg]; rw [← b.height_reflectionPerm_self]; rw [b.height_add hk]

Depends on / 依赖: P.indexNeg, P.root, b.height_add, b.height_reflectionPerm_self, height_add, height_reflectionPerm_self, indexNeg, replace, sub_eq_add_neg
-/
lemma height_sub {i j k : ι} (hk : P.root k = P.root i - P.root j) :
    b.height k = b.height i - b.height j := by
  let := P.indexNeg
  replace hk : P.root k = P.root i + P.root (-j) := by simpa [← sub_eq_add_neg]
  rw [sub_eq_add_neg]; rw [← b.height_reflectionPerm_self]; rw [b.height_add hk]

/--
lemma `height_add_zsmul` / 引理 `height_add_zsmul`

English:
lemma height_add_zsmul
  given: {i j k : ι} {z : Int} (hk : P.root k = P.root i + z • P.root j)
  proof: by
  obtain ⟨f, -, -, hf⟩ := b.exists_root_eq_sum_int i
  obtain ⟨g, -, -, hg⟩ := b.exists_root_eq_sum_int j
  have hfg : P.root k = ∑ l in b.support, (f + z • g) l • P.root l := by
    simp_rw [Pi.add_apply, Pi.smul_apply, add_smul, smul_assoc, Finset.sum_add_distrib,
      ← Finset.smul_sum, ← hf, ← hg, hk]
  simp_rw [height_eq_sum hf, height_eq_sum hg, height_eq_sum hfg, Pi.add_apply, Pi.smul_apply,
    Finset.sum_add_distrib, Finset.smul_sum]

中文:
引理 height_add_zsmul
  条件: {i j k : ι} {z : 整数} (hk : P.root k = P.root i + z • P.root j)
  证明: by
  obtain ⟨f, -, -, hf⟩ := b.exists_root_eq_sum_int i
  obtain ⟨g, -, -, hg⟩ := b.exists_root_eq_sum_int j
  have hfg : P.root k = ∑ l in b.support, (f + z • g) l • P.root l := by
    simp_rw [Pi.add_apply, Pi.smul_apply, add_smul, smul_assoc, Finset.sum_add_distrib,
      ← Finset.smul_sum, ← hf, ← hg, hk]
  simp_rw [height_eq_sum hf, height_eq_sum hg, height_eq_sum hfg, Pi.add_apply, Pi.smul_apply,
    Finset.sum_add_distrib, Finset.smul_sum]

Depends on / 依赖: Finset, Finset.smul_sum, Finset.sum_add_distrib, P.root, Pi.add_apply, Pi.smul_apply, add_apply, add_smul, b.exists_root_eq_sum_int, b.support, exists_root_eq_sum_int, height_eq_sum, simp_rw, smul_apply, smul_assoc, smul_sum, sum_add_distrib, support
-/
lemma height_add_zsmul {i j k : ι} {z : Int} (hk : P.root k = P.root i + z • P.root j) :
    b.height k = b.height i + z • b.height j := by
  obtain ⟨f, -, -, hf⟩ := b.exists_root_eq_sum_int i
  obtain ⟨g, -, -, hg⟩ := b.exists_root_eq_sum_int j
  have hfg : P.root k = ∑ l in b.support, (f + z • g) l • P.root l := by
    simp_rw [Pi.add_apply, Pi.smul_apply, add_smul, smul_assoc, Finset.sum_add_distrib,
      ← Finset.smul_sum, ← hf, ← hg, hk]
  simp_rw [height_eq_sum hf, height_eq_sum hg, height_eq_sum hfg, Pi.add_apply, Pi.smul_apply,
    Finset.sum_add_distrib, Finset.smul_sum]

/--
Definition of `IsPos` / `IsPos` 的定义

English:
definition IsPos
  signature: (i : ι)
  body: 0 < b.height i

中文:
定义 IsPos
  签名: (i : ι)
  定义体: 0 < b.height i

Depends on / 依赖: b.height, height
-/
def IsPos (i : ι) : Prop := 0 < b.height i

/--
lemma `isPos_iff` / 引理 `isPos_iff`

English:
lemma isPos_iff
  given: {i : ι}
  statement: b.IsPos i ↔ 0 < b.height i
  proof: Iff.rfl

中文:
引理 isPos_iff
  条件: {i : ι}
  结论: b.IsPos i ↔ 0 < b.height i
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma isPos_iff {i : ι} : b.IsPos i ↔ 0 < b.height i := Iff.rfl

/--
lemma `isPos_iff'` / 引理 `isPos_iff'`

English:
lemma isPos_iff'
  given: {i : ι}
  statement: b.IsPos i ↔ 0 <= b.height i
  proof: by
  rw [isPos_iff]
  have := b.height_ne_zero i
  lia

中文:
引理 isPos_iff'
  条件: {i : ι}
  结论: b.IsPos i ↔ 0 <= b.height i
  证明: by
  rw [isPos_iff]
  have := b.height_ne_zero i
  lia

Depends on / 依赖: b.height_ne_zero, height_ne_zero, isPos_iff
-/
lemma isPos_iff' {i : ι} : b.IsPos i ↔ 0 <= b.height i := by
  rw [isPos_iff]
  have := b.height_ne_zero i
  lia

/--
lemma `IsPos.or_neg` / 引理 `IsPos.or_neg`

English:
lemma IsPos.or_neg
  given: (i : ι)
  proof: P.indexNeg
    b.IsPos i ∨ b.IsPos (-i) := by
  rw [isPos_iff]; rw [isPos_iff]; rw [height_reflectionPerm_self]
  have := b.height_ne_zero i
  lia

中文:
引理 IsPos.or_neg
  条件: (i : ι)
  证明: P.indexNeg
    b.IsPos i ∨ b.IsPos (-i) := by
  rw [isPos_iff]; rw [isPos_iff]; rw [height_reflectionPerm_self]
  have := b.height_ne_zero i
  lia

Depends on / 依赖: P.indexNeg, indexNeg
-/
lemma IsPos.or_neg (i : ι) :
    letI := P.indexNeg
    b.IsPos i ∨ b.IsPos (-i) := by
  rw [isPos_iff]; rw [isPos_iff]; rw [height_reflectionPerm_self]
  have := b.height_ne_zero i
  lia

/--
lemma `IsPos.neg_iff_not` / 引理 `IsPos.neg_iff_not`

English:
lemma IsPos.neg_iff_not
  given: (i : ι)
  proof: P.indexNeg
    b.IsPos (-i) ↔ ¬ b.IsPos i := by
  rw [isPos_iff]; rw [isPos_iff]; rw [height_reflectionPerm_self]
  have := b.height_ne_zero i
  lia

中文:
引理 IsPos.neg_iff_not
  条件: (i : ι)
  证明: P.indexNeg
    b.IsPos (-i) ↔ ¬ b.IsPos i := by
  rw [isPos_iff]; rw [isPos_iff]; rw [height_reflectionPerm_self]
  have := b.height_ne_zero i
  lia

Depends on / 依赖: P.indexNeg, indexNeg
-/
lemma IsPos.neg_iff_not (i : ι) :
    letI := P.indexNeg
    b.IsPos (-i) ↔ ¬ b.IsPos i := by
  rw [isPos_iff]; rw [isPos_iff]; rw [height_reflectionPerm_self]
  have := b.height_ne_zero i
  lia

variable {b}

/--
lemma `isPos_of_mem_support` / 引理 `isPos_of_mem_support`

English:
lemma isPos_of_mem_support
  given: {i : ι} (h : i in b.support)
  proof: by
  rw [isPos_iff]; rw [height_one_of_mem_support h]
  exact Int.one_pos

中文:
引理 isPos_of_mem_support
  条件: {i : ι} (h : i in b.support)
  证明: by
  rw [isPos_iff]; rw [height_one_of_mem_support h]
  exact Int.one_pos

Depends on / 依赖: Int.one_pos, height_one_of_mem_support, isPos_iff, one_pos
-/
lemma isPos_of_mem_support {i : ι} (h : i in b.support) :
    b.IsPos i := by
  rw [isPos_iff]; rw [height_one_of_mem_support h]
  exact Int.one_pos

/--
lemma `IsPos.add` / 引理 `IsPos.add`

English:
lemma IsPos.add
  statement: {i j k : ι}
  proof: by
  rw [isPos_iff] at hi hj ⊢
  rw [b.height_add hk]
  lia

中文:
引理 IsPos.add
  结论: {i j k : ι}
  证明: by
  rw [isPos_iff] at hi hj ⊢
  rw [b.height_add hk]
  lia

Depends on / 依赖: b.height_add, height_add, isPos_iff
-/
lemma IsPos.add {i j k : ι}
    (hi : b.IsPos i) (hj : b.IsPos j) (hk : P.root k = P.root i + P.root j) :
    b.IsPos k := by
  rw [isPos_iff] at hi hj ⊢
  rw [b.height_add hk]
  lia

/--
lemma `IsPos.sub` / 引理 `IsPos.sub`

English:
lemma IsPos.sub
  statement: {i j k : ι}
  proof: by
  rw [isPos_iff] at hi
  rw [isPos_iff']; rw [b.height_sub hk]; rw [height_one_of_mem_support hj]
  lia

中文:
引理 IsPos.sub
  结论: {i j k : ι}
  证明: by
  rw [isPos_iff] at hi
  rw [isPos_iff']; rw [b.height_sub hk]; rw [height_one_of_mem_support hj]
  lia

Depends on / 依赖: b.height_sub, height_one_of_mem_support, height_sub, isPos_iff
-/
lemma IsPos.sub {i j k : ι}
    (hi : b.IsPos i) (hj : j in b.support) (hk : P.root k = P.root i - P.root j) :
    b.IsPos k := by
  rw [isPos_iff] at hi
  rw [isPos_iff']; rw [b.height_sub hk]; rw [height_one_of_mem_support hj]
  lia

/--
lemma `IsPos.exists_mem_support_pos_pairingIn` / 引理 `IsPos.exists_mem_support_pos_pairingIn`

English:
lemma IsPos.exists_mem_support_pos_pairingIn
  given: [P.IsCrystallographic] {i : ι} (h₀ : b.IsPos i)
  proof: by
  by_contra! contra
  suffices P.pairingIn Int i i <= 0 by simp_all
  obtain ⟨f, hf₀, hf₁, hf₂⟩ := b.exists_root_eq_sum_int i
  replace hf₁ : 0 < f := by
    refine hf₁.resolve_right ?_
    rw [isPos_iff]; rw [height_eq_sum hf₂] at h₀
    contrapose! h₀
    exact Finset.sum_nonpos fun i _ => h₀.le i
  have : P.pairingIn Int i i = ∑ j in b.support, f j • P.pairingIn Int j i :=
algebraMap_injective Int R by
      simp_rw [algebraMap_pairingIn, map_sum, ← root_coroot_eq_pairing, hf₂, map_sum, map_zsmul,
        LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, root_coroot_eq_pairing,
        zsmul_eq_mul, algebraMap_pairingIn]
  rw [this]
  refine Finset.sum_nonpos fun j _ => ?_
  by_cases hj : j in Function.support f
  · exact smul_nonpos_of_nonneg_of_nonpos (hf₁.le j) (contra j (hf₀ hj))
  · simp_all

中文:
引理 IsPos.存在_mem_support_pos_pairingIn
  条件: [P.IsCrystallographic] {i : ι} (h₀ : b.IsPos i)
  证明: by
  by_contra! contra
  suffices P.pairingIn Int i i <= 0 by simp_all
  obtain ⟨f, hf₀, hf₁, hf₂⟩ := b.exists_root_eq_sum_int i
  replace hf₁ : 0 < f := by
    refine hf₁.resolve_right ?_
    rw [isPos_iff]; rw [height_eq_sum hf₂] at h₀
    contrapose! h₀
    exact Finset.sum_nonpos fun i _ => h₀.le i
  have : P.pairingIn Int i i = ∑ j in b.support, f j • P.pairingIn Int j i :=
algebraMap_injective Int R by
      simp_rw [algebraMap_pairingIn, map_sum, ← root_coroot_eq_pairing, hf₂, map_sum, map_zsmul,
        LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, root_coroot_eq_pairing,
        zsmul_eq_mul, algebraMap_pairingIn]
  rw [this]
  refine Finset.sum_nonpos fun j _ => ?_
  by_cases hj : j in Function.support f
  · exact smul_nonpos_of_nonneg_of_nonpos (hf₁.le j) (contra j (hf₀ hj))
  · simp_all

Depends on / 依赖: Finset, Finset.sum_nonpos, LinearMap, LinearMap.coe_sum, P.pairingIn, algebraMap_injective, algebraMap_pairingIn, b.exists_root_eq_sum_int, b.support, coe_sum, contra, contrapose, exists_root_eq_sum_int, height_eq_sum, isPos_iff, map_sum, map_zsmul, pairingIn, replace, resolve_right
-/
lemma IsPos.exists_mem_support_pos_pairingIn [P.IsCrystallographic] {i : ι} (h₀ : b.IsPos i) :
    exists j in b.support, 0 < P.pairingIn Int j i := by
  by_contra! contra
  suffices P.pairingIn Int i i <= 0 by simp_all
  obtain ⟨f, hf₀, hf₁, hf₂⟩ := b.exists_root_eq_sum_int i
  replace hf₁ : 0 < f := by
    refine hf₁.resolve_right ?_
    rw [isPos_iff]; rw [height_eq_sum hf₂] at h₀
    contrapose! h₀
    exact Finset.sum_nonpos fun i _ => h₀.le i
  have : P.pairingIn Int i i = ∑ j in b.support, f j • P.pairingIn Int j i :=
algebraMap_injective Int R by
      simp_rw [algebraMap_pairingIn, map_sum, ← root_coroot_eq_pairing, hf₂, map_sum, map_zsmul,
        LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, root_coroot_eq_pairing,
        zsmul_eq_mul, algebraMap_pairingIn]
  rw [this]
  refine Finset.sum_nonpos fun j _ => ?_
  by_cases hj : j in Function.support f
  · exact smul_nonpos_of_nonneg_of_nonpos (hf₁.le j) (contra j (hf₀ hj))
  · simp_all

/--
lemma `exists_mem_support_pos_pairingIn_ne_zero` / 引理 `exists_mem_support_pos_pairingIn_ne_zero`

English:
lemma exists_mem_support_pos_pairingIn_ne_zero
  given: [P.IsCrystallographic] (i : ι)
  proof: by
  rcases IsPos.or_neg b i with hi | hi
  · obtain ⟨j, hj, hj₀⟩ := hi.exists_mem_support_pos_pairingIn
    exact ⟨j, hj, hj₀.ne'⟩
  · obtain ⟨j, hj, hj₀⟩ := hi.exists_mem_support_pos_pairingIn
    exact ⟨j, hj, by aesop⟩

中文:
引理 存在_mem_support_pos_pairingIn_ne_zero
  条件: [P.IsCrystallographic] (i : ι)
  证明: by
  rcases IsPos.or_neg b i with hi | hi
  · obtain ⟨j, hj, hj₀⟩ := hi.exists_mem_support_pos_pairingIn
    exact ⟨j, hj, hj₀.ne'⟩
  · obtain ⟨j, hj, hj₀⟩ := hi.exists_mem_support_pos_pairingIn
    exact ⟨j, hj, by aesop⟩

Depends on / 依赖: IsPos.or_neg, exists_mem_support_pos_pairingIn, hi.exists_mem_support_pos_pairingIn, or_neg
-/
lemma exists_mem_support_pos_pairingIn_ne_zero [P.IsCrystallographic] (i : ι) :
    exists j in b.support, P.pairingIn Int j i != 0 := by
  rcases IsPos.or_neg b i with hi | hi
  · obtain ⟨j, hj, hj₀⟩ := hi.exists_mem_support_pos_pairingIn
    exact ⟨j, hj, hj₀.ne'⟩
  · obtain ⟨j, hj, hj₀⟩ := hi.exists_mem_support_pos_pairingIn
    exact ⟨j, hj, by aesop⟩

variable [Finite ι] [IsDomain R] [P.IsCrystallographic] [P.IsReduced]

/--
lemma `IsPos.add_zsmul` / 引理 `IsPos.add_zsmul`

English:
lemma IsPos.add_zsmul
  statement: {i j k : ι} {z : Int} (hij : i != j)
  proof: by
  replace hij : LinearIndependent R ![P.root j, P.root i] := by
    refine IsReduced.linearIndependent P hij.symm fun contra => ?_
    let := P.indexNeg
    replace contra : i = -j := by rw [eq_comm, neg_eq_iff_eq_neg]; simpa using contra
    rw [contra]; rw [isPos_iff]; rw [height_reflectionPerm_self]; rw [height_one_of_mem_support hj] at hi
    lia
  induction z generalizing i k with
  | zero => simp_all
  | succ w hw =>
    obtain ⟨l, hl⟩ : P.root i + (w : Int) • P.root j in range P.root := by
      replace hk : P.root i + (w + 1) • P.root j in range P.root := ⟨k, by rw [hk]; module⟩
      simp only [natCast_zsmul, root_add_nsmul_mem_range_iff_le_chainTopCoeff hij] at hk ⊢
      lia
    replace hk : P.root k = P.root l + P.root j := by rw [hk, hl]; module
    exact (hw hi hl hij).add (b.isPos_of_mem_support hj) hk
  | pred w hw =>
    obtain ⟨l, hl⟩ : P.root i + (-w : Int) • P.root j in range P.root := by
      replace hk : P.root i - (w + 1) • P.root j in range P.root := ⟨k, by rw [hk]; module⟩
      rw [neg_smul]; rw [← sub_eq_add_neg]; rw [natCast_zsmul]
      simp only [root_sub_nsmul_mem_range_iff_le_chainBotCoeff hij] at hk ⊢
      lia
    replace hk : P.root k = P.root l - P.root j := by rw [hk, hl]; module
    exact (hw hi hl hij).sub hj hk

中文:
引理 IsPos.add_zsmul
  结论: {i j k : ι} {z : 整数} (hij : i != j)
  证明: by
  replace hij : LinearIndependent R ![P.root j, P.root i] := by
    refine IsReduced.linearIndependent P hij.symm fun contra => ?_
    let := P.indexNeg
    replace contra : i = -j := by rw [eq_comm, neg_eq_iff_eq_neg]; simpa using contra
    rw [contra]; rw [isPos_iff]; rw [height_reflectionPerm_self]; rw [height_one_of_mem_support hj] at hi
    lia
  induction z generalizing i k with
  | zero => simp_all
  | succ w hw =>
    obtain ⟨l, hl⟩ : P.root i + (w : Int) • P.root j in range P.root := by
      replace hk : P.root i + (w + 1) • P.root j in range P.root := ⟨k, by rw [hk]; module⟩
      simp only [natCast_zsmul, root_add_nsmul_mem_range_iff_le_chainTopCoeff hij] at hk ⊢
      lia
    replace hk : P.root k = P.root l + P.root j := by rw [hk, hl]; module
    exact (hw hi hl hij).add (b.isPos_of_mem_support hj) hk
  | pred w hw =>
    obtain ⟨l, hl⟩ : P.root i + (-w : Int) • P.root j in range P.root := by
      replace hk : P.root i - (w + 1) • P.root j in range P.root := ⟨k, by rw [hk]; module⟩
      rw [neg_smul]; rw [← sub_eq_add_neg]; rw [natCast_zsmul]
      simp only [root_sub_nsmul_mem_range_iff_le_chainBotCoeff hij] at hk ⊢
      lia
    replace hk : P.root k = P.root l - P.root j := by rw [hk, hl]; module
    exact (hw hi hl hij).sub hj hk

Depends on / 依赖: IsReduced, IsReduced.linearIndependent, LinearIndependent, P.indexNeg, P.root, contra, eq_comm, generalizing, height_one_of_mem_support, height_reflectionPerm_self, hij.symm, indexNeg, isPos_iff, linearIndependent, neg_eq_iff_eq_neg, replace
-/
lemma IsPos.add_zsmul {i j k : ι} {z : Int} (hij : i != j)
    (hi : b.IsPos i) (hj : j in b.support) (hk : P.root k = P.root i + z • P.root j) :
    b.IsPos k := by
  replace hij : LinearIndependent R ![P.root j, P.root i] := by
    refine IsReduced.linearIndependent P hij.symm fun contra => ?_
    let := P.indexNeg
    replace contra : i = -j := by rw [eq_comm, neg_eq_iff_eq_neg]; simpa using contra
    rw [contra]; rw [isPos_iff]; rw [height_reflectionPerm_self]; rw [height_one_of_mem_support hj] at hi
    lia
  induction z generalizing i k with
  | zero => simp_all
  | succ w hw =>
    obtain ⟨l, hl⟩ : P.root i + (w : Int) • P.root j in range P.root := by
      replace hk : P.root i + (w + 1) • P.root j in range P.root := ⟨k, by rw [hk]; module⟩
      simp only [natCast_zsmul, root_add_nsmul_mem_range_iff_le_chainTopCoeff hij] at hk ⊢
      lia
    replace hk : P.root k = P.root l + P.root j := by rw [hk, hl]; module
    exact (hw hi hl hij).add (b.isPos_of_mem_support hj) hk
  | pred w hw =>
    obtain ⟨l, hl⟩ : P.root i + (-w : Int) • P.root j in range P.root := by
      replace hk : P.root i - (w + 1) • P.root j in range P.root := ⟨k, by rw [hk]; module⟩
      rw [neg_smul]; rw [← sub_eq_add_neg]; rw [natCast_zsmul]
      simp only [root_sub_nsmul_mem_range_iff_le_chainBotCoeff hij] at hk ⊢
      lia
    replace hk : P.root k = P.root l - P.root j := by rw [hk, hl]; module
    exact (hw hi hl hij).sub hj hk

/--
lemma `IsPos.reflectionPerm` / 引理 `IsPos.reflectionPerm`

English:
lemma IsPos.reflectionPerm
  given: {i j : ι} (hi : b.IsPos i) (hj : j in b.support) (hij : i != j)
  proof: by
  have : P.root (P.reflectionPerm j i) = P.root i + (-P.pairingIn Int i j) • P.root j := by
    rw [root_reflectionPerm]; rw [neg_smul]; rw [reflection_apply_root' Int]; rw [sub_eq_add_neg]
  exact hi.add_zsmul hij hj this

omit [P.IsReduced] in

中文:
引理 IsPos.reflectionPerm
  条件: {i j : ι} (hi : b.IsPos i) (hj : j in b.support) (hij : i != j)
  证明: by
  have : P.root (P.reflectionPerm j i) = P.root i + (-P.pairingIn Int i j) • P.root j := by
    rw [root_reflectionPerm]; rw [neg_smul]; rw [reflection_apply_root' Int]; rw [sub_eq_add_neg]
  exact hi.add_zsmul hij hj this

omit [P.IsReduced] in

Depends on / 依赖: P.pairingIn, P.reflectionPerm, P.root, add_zsmul, hi.add_zsmul, neg_smul, pairingIn, reflectionPerm, reflection_apply_root, root_reflectionPerm, sub_eq_add_neg
-/
lemma IsPos.reflectionPerm {i j : ι} (hi : b.IsPos i) (hj : j in b.support) (hij : i != j) :
    b.IsPos (P.reflectionPerm j i) := by
  have : P.root (P.reflectionPerm j i) = P.root i + (-P.pairingIn Int i j) • P.root j := by
    rw [root_reflectionPerm]; rw [neg_smul]; rw [reflection_apply_root' Int]; rw [sub_eq_add_neg]
  exact hi.add_zsmul hij hj this

omit [P.IsReduced] in
/--
lemma `IsPos.induction_on_add` / 引理 `IsPos.induction_on_add`

English:
lemma IsPos.induction_on_add
  proof: by
  generalize hN : b.height i = N
  induction N using Int.induction_on generalizing i with
| zero => exact False.elim b.height_ne_zero i hN
  | succ n ih =>
    obtain ⟨j, hj, hj'⟩ := h₀.exists_mem_support_pos_pairingIn
    rw [P.zero_lt_pairingIn_iff'] at hj'
    rcases eq_or_ne i j with rfl | hij; · exact h₁ i hj
    obtain ⟨k, hk⟩ := P.root_sub_root_mem_of_pairingIn_pos hj' hij
    have hkn : b.height k = n := by rw [b.height_sub hk, height_one_of_mem_support hj]; lia
    have hkpos : b.IsPos k := by rw [isPos_iff']; lia
    exact h₂ k j i (by rw [hk]; module) (ih hkpos hkn) hj
  | pred n ih =>
    rw [isPos_iff] at h₀
    lia

omit [P.IsReduced] in

中文:
引理 IsPos.induction_on_add
  证明: by
  generalize hN : b.height i = N
  induction N using Int.induction_on generalizing i with
| zero => exact False.elim b.height_ne_zero i hN
  | succ n ih =>
    obtain ⟨j, hj, hj'⟩ := h₀.exists_mem_support_pos_pairingIn
    rw [P.zero_lt_pairingIn_iff'] at hj'
    rcases eq_or_ne i j with rfl | hij; · exact h₁ i hj
    obtain ⟨k, hk⟩ := P.root_sub_root_mem_of_pairingIn_pos hj' hij
    have hkn : b.height k = n := by rw [b.height_sub hk, height_one_of_mem_support hj]; lia
    have hkpos : b.IsPos k := by rw [isPos_iff']; lia
    exact h₂ k j i (by rw [hk]; module) (ih hkpos hkn) hj
  | pred n ih =>
    rw [isPos_iff] at h₀
    lia

omit [P.IsReduced] in

Depends on / 依赖: False.elim, Int.induction_on, P.root_sub_root_mem_of_pairingIn_pos, P.zero_lt_pairingIn_iff, b.IsPos, b.height, b.height_ne_zero, b.height_sub, eq_or_ne, exists_mem_support_pos_pairingIn, generalize, generalizing, height, height_ne_zero, height_one_of_mem_support, height_sub, induction_on, isPos_iff, root_sub_root_mem_of_pairingIn_pos, zero_lt_pairingIn_iff
-/
lemma IsPos.induction_on_add
    {i : ι} (h₀ : b.IsPos i)
    {p : ι -> Prop}
    (h₁ : forall i in b.support, p i)
    (h₂ : forall i j k, P.root k = P.root i + P.root j -> p i -> j in b.support -> p k) :
    p i := by
  generalize hN : b.height i = N
  induction N using Int.induction_on generalizing i with
| zero => exact False.elim b.height_ne_zero i hN
  | succ n ih =>
    obtain ⟨j, hj, hj'⟩ := h₀.exists_mem_support_pos_pairingIn
    rw [P.zero_lt_pairingIn_iff'] at hj'
    rcases eq_or_ne i j with rfl | hij; · exact h₁ i hj
    obtain ⟨k, hk⟩ := P.root_sub_root_mem_of_pairingIn_pos hj' hij
    have hkn : b.height k = n := by rw [b.height_sub hk, height_one_of_mem_support hj]; lia
    have hkpos : b.IsPos k := by rw [isPos_iff']; lia
    exact h₂ k j i (by rw [hk]; module) (ih hkpos hkn) hj
  | pred n ih =>
    rw [isPos_iff] at h₀
    lia

omit [P.IsReduced] in
/--
lemma `exists_eq_sum_and_forall_sum_mem_of_isPos` / 引理 `exists_eq_sum_and_forall_sum_mem_of_isPos`

English:
lemma exists_eq_sum_and_forall_sum_mem_of_isPos
  given: {i : ι} (hi : b.IsPos i)
  proof: by
  apply hi.induction_on_add (fun j hj => ⟨1, ![j], by simpa⟩)
  intro j k l h₁ ⟨n, f, h₂, h₃, h₄⟩ h₅
  refine ⟨n + 1, Fin.snoc f k, ?_, ?_, fun m => ?_⟩
  · simpa using insert_subset h₅ h₂
  · simp [Fin.sum_univ_castSucc, h₁, h₃]
  · by_cases hm : m < n
    · have : m = (⟨m, hm⟩ : Fin n).castSucc := rfl
      rw [this]; rw [Fin.sum_Iic_castSucc]
      simp only [Fin.snoc_castSucc, h₄]
    · replace hm : m = n := by lia
      replace hm : Finset.Iic m = Finset.univ := by ext; simp [hm, Fin.le_def, Fin.is_le]
      simp [hm, Fin.sum_univ_castSucc, ← h₃, ← h₁]

omit [P.IsReduced] in

中文:
引理 存在_eq_sum_and_对任意_sum_mem_of_isPos
  条件: {i : ι} (hi : b.IsPos i)
  证明: by
  apply hi.induction_on_add (fun j hj => ⟨1, ![j], by simpa⟩)
  intro j k l h₁ ⟨n, f, h₂, h₃, h₄⟩ h₅
  refine ⟨n + 1, Fin.snoc f k, ?_, ?_, fun m => ?_⟩
  · simpa using insert_subset h₅ h₂
  · simp [Fin.sum_univ_castSucc, h₁, h₃]
  · by_cases hm : m < n
    · have : m = (⟨m, hm⟩ : Fin n).castSucc := rfl
      rw [this]; rw [Fin.sum_Iic_castSucc]
      simp only [Fin.snoc_castSucc, h₄]
    · replace hm : m = n := by lia
      replace hm : Finset.Iic m = Finset.univ := by ext; simp [hm, Fin.le_def, Fin.is_le]
      simp [hm, Fin.sum_univ_castSucc, ← h₃, ← h₁]

omit [P.IsReduced] in

Depends on / 依赖: Fin.is_le, Fin.le_def, Fin.snoc, Fin.snoc_castSucc, Fin.sum_Iic_castSucc, Fin.sum_univ, Fin.sum_univ_castSucc, Finset, Finset.Iic, Finset.univ, castSucc, hi.induction_on_add, induction_on_add, insert_subset, is_le, le_def, replace, snoc_castSucc, sum_Iic_castSucc, sum_univ
-/
lemma exists_eq_sum_and_forall_sum_mem_of_isPos {i : ι} (hi : b.IsPos i) :
    exists n, exists f : Fin n -> ι,
      range f subseteq b.support ∧
      P.root i = ∑ m, P.root (f m) ∧
      forall m, ∑ m' <= m, P.root (f m') in range P.root := by
  apply hi.induction_on_add (fun j hj => ⟨1, ![j], by simpa⟩)
  intro j k l h₁ ⟨n, f, h₂, h₃, h₄⟩ h₅
  refine ⟨n + 1, Fin.snoc f k, ?_, ?_, fun m => ?_⟩
  · simpa using insert_subset h₅ h₂
  · simp [Fin.sum_univ_castSucc, h₁, h₃]
  · by_cases hm : m < n
    · have : m = (⟨m, hm⟩ : Fin n).castSucc := rfl
      rw [this]; rw [Fin.sum_Iic_castSucc]
      simp only [Fin.snoc_castSucc, h₄]
    · replace hm : m = n := by lia
      replace hm : Finset.Iic m = Finset.univ := by ext; simp [hm, Fin.le_def, Fin.is_le]
      simp [hm, Fin.sum_univ_castSucc, ← h₃, ← h₁]

omit [P.IsReduced] in
/--
lemma `induction_add` / 引理 `induction_add`

English:
lemma induction_add
  statement: (i : ι) {p : ι -> Prop}
  proof: by
  let := P.indexNeg
  rcases IsPos.or_neg b i with hi | hi
  · exact hi.induction_on_add h₁ h₂
  · suffices p (-i) by rw [← neg_neg i]; exact h₀ (-i) this
    exact hi.induction_on_add h₁ h₂

中文:
引理 induction_add
  结论: (i : ι) {p : ι -> 命题}
  证明: by
  let := P.indexNeg
  rcases IsPos.or_neg b i with hi | hi
  · exact hi.induction_on_add h₁ h₂
  · suffices p (-i) by rw [← neg_neg i]; exact h₀ (-i) this
    exact hi.induction_on_add h₁ h₂

Depends on / 依赖: IsPos.or_neg, P.indexNeg, hi.induction_on_add, indexNeg, induction_on_add, neg_neg, or_neg
-/
lemma induction_add (i : ι) {p : ι -> Prop}
    (h₀ : forall i, p i -> p (P.reflectionPerm i i))
    (h₁ : forall i in b.support, p i)
    (h₂ : forall i j k, P.root k = P.root i + P.root j -> p i -> j in b.support -> p k) :
    p i := by
  let := P.indexNeg
  rcases IsPos.or_neg b i with hi | hi
  · exact hi.induction_on_add h₁ h₂
  · suffices p (-i) by rw [← neg_neg i]; exact h₀ (-i) this
    exact hi.induction_on_add h₁ h₂

/--
lemma `IsPos.induction_on_reflect` / 引理 `IsPos.induction_on_reflect`

English:
lemma IsPos.induction_on_reflect
  proof: by
  generalize hN : (b.height i).natAbs = N
  induction N using Nat.strongRecOn generalizing i with
  | ind n ih =>
    obtain ⟨j, hj, hj'⟩ := h₀.exists_mem_support_pos_pairingIn
    rw [P.zero_lt_pairingIn_iff'] at hj'
    rcases eq_or_ne i j with rfl | hij; · exact h₁ i hj
    have hk := h₀.reflectionPerm hj hij
    have : (b.height (P.reflectionPerm j i)).natAbs < n := by
      suffices b.height (P.reflectionPerm j i) < b.height i by
        have : (b.height (P.reflectionPerm j i)).natAbs = b.height (P.reflectionPerm j i) :=
Int.natAbs_of_nonneg (isPos_iff' _).mp hk
        lia
      have := P.reflection_apply_root' Int (i := j) (j := i)
      rw [← root_reflectionPerm]; rw [sub_eq_add_neg]; rw [← neg_smul] at this
      rw [b.height_add_zsmul this]
replace hj : 0 < b.height j := (isPos_iff _).mp isPos_of_mem_support hj
      aesop
    simpa using h₂ (P.reflectionPerm j i) j
      (ih (m := (b.height (P.reflectionPerm j i)).natAbs) this hk rfl) hj

中文:
引理 IsPos.induction_on_reflect
  证明: by
  generalize hN : (b.height i).natAbs = N
  induction N using Nat.strongRecOn generalizing i with
  | ind n ih =>
    obtain ⟨j, hj, hj'⟩ := h₀.exists_mem_support_pos_pairingIn
    rw [P.zero_lt_pairingIn_iff'] at hj'
    rcases eq_or_ne i j with rfl | hij; · exact h₁ i hj
    have hk := h₀.reflectionPerm hj hij
    have : (b.height (P.reflectionPerm j i)).natAbs < n := by
      suffices b.height (P.reflectionPerm j i) < b.height i by
        have : (b.height (P.reflectionPerm j i)).natAbs = b.height (P.reflectionPerm j i) :=
Int.natAbs_of_nonneg (isPos_iff' _).mp hk
        lia
      have := P.reflection_apply_root' Int (i := j) (j := i)
      rw [← root_reflectionPerm]; rw [sub_eq_add_neg]; rw [← neg_smul] at this
      rw [b.height_add_zsmul this]
replace hj : 0 < b.height j := (isPos_iff _).mp isPos_of_mem_support hj
      aesop
    simpa using h₂ (P.reflectionPerm j i) j
      (ih (m := (b.height (P.reflectionPerm j i)).natAbs) this hk rfl) hj

Depends on / 依赖: Int.n, Nat.strongRecOn, P.reflectionPerm, P.zero_lt_pairingIn_iff, b.height, eq_or_ne, exists_mem_support_pos_pairingIn, generalize, generalizing, height, natAbs, reflectionPerm, strongRecOn, zero_lt_pairingIn_iff
-/
lemma IsPos.induction_on_reflect
    {i : ι} (h₀ : b.IsPos i)
    {p : ι -> Prop}
    (h₁ : forall i in b.support, p i)
    (h₂ : forall i j, p i -> j in b.support -> p (P.reflectionPerm j i)) :
    p i := by
  generalize hN : (b.height i).natAbs = N
  induction N using Nat.strongRecOn generalizing i with
  | ind n ih =>
    obtain ⟨j, hj, hj'⟩ := h₀.exists_mem_support_pos_pairingIn
    rw [P.zero_lt_pairingIn_iff'] at hj'
    rcases eq_or_ne i j with rfl | hij; · exact h₁ i hj
    have hk := h₀.reflectionPerm hj hij
    have : (b.height (P.reflectionPerm j i)).natAbs < n := by
      suffices b.height (P.reflectionPerm j i) < b.height i by
        have : (b.height (P.reflectionPerm j i)).natAbs = b.height (P.reflectionPerm j i) :=
Int.natAbs_of_nonneg (isPos_iff' _).mp hk
        lia
      have := P.reflection_apply_root' Int (i := j) (j := i)
      rw [← root_reflectionPerm]; rw [sub_eq_add_neg]; rw [← neg_smul] at this
      rw [b.height_add_zsmul this]
replace hj : 0 < b.height j := (isPos_iff _).mp isPos_of_mem_support hj
      aesop
    simpa using h₂ (P.reflectionPerm j i) j
      (ih (m := (b.height (P.reflectionPerm j i)).natAbs) this hk rfl) hj

/--
lemma `induction_reflect` / 引理 `induction_reflect`

English:
lemma induction_reflect
  statement: (i : ι) {p : ι -> Prop}
  proof: by
  let := P.indexNeg
  rcases IsPos.or_neg b i with hi | hi
  · exact hi.induction_on_reflect h₁ h₂
  · suffices p (-i) by rw [← neg_neg i]; exact h₀ (-i) this
    exact hi.induction_on_reflect h₁ h₂

中文:
引理 induction_reflect
  结论: (i : ι) {p : ι -> 命题}
  证明: by
  let := P.indexNeg
  rcases IsPos.or_neg b i with hi | hi
  · exact hi.induction_on_reflect h₁ h₂
  · suffices p (-i) by rw [← neg_neg i]; exact h₀ (-i) this
    exact hi.induction_on_reflect h₁ h₂

Depends on / 依赖: IsPos.or_neg, P.indexNeg, hi.induction_on_reflect, indexNeg, induction_on_reflect, neg_neg, or_neg
-/
lemma induction_reflect (i : ι) {p : ι -> Prop}
    (h₀ : forall i, p i -> p (P.reflectionPerm i i))
    (h₁ : forall i in b.support, p i)
    (h₂ : forall i j, p i -> j in b.support -> p (P.reflectionPerm j i)) :
    p i := by
  let := P.indexNeg
  rcases IsPos.or_neg b i with hi | hi
  · exact hi.induction_on_reflect h₁ h₂
  · suffices p (-i) by rw [← neg_neg i]; exact h₀ (-i) this
    exact hi.induction_on_reflect h₁ h₂

/--
lemma `forall_mem_support_invtSubmodule_iff` / 引理 `forall_mem_support_invtSubmodule_iff`

English:
lemma forall_mem_support_invtSubmodule_iff
  given: (q : Submodule R M)
  proof: by
  refine ⟨fun hq i => ?_, fun hq i _ => hq i⟩
  let := P.indexNeg
  have (j : ι) : P.reflection (-j) = P.reflection j := by ext x; simp [reflection_apply, two_smul]
  refine b.induction_reflect i (by simp_all) hq ?_
  clear i
  intro i j hi hj
  rw [reflection_reflectionPerm]
  exact Module.End.invtSubmodule.comp _ (Module.End.invtSubmodule.comp _ (hq j hj) hi) (hq j hj)

中文:
引理 对任意_mem_support_invtSubmodule_iff
  条件: (q : 子模 R M)
  证明: by
  refine ⟨fun hq i => ?_, fun hq i _ => hq i⟩
  let := P.indexNeg
  have (j : ι) : P.reflection (-j) = P.reflection j := by ext x; simp [reflection_apply, two_smul]
  refine b.induction_reflect i (by simp_all) hq ?_
  clear i
  intro i j hi hj
  rw [reflection_reflectionPerm]
  exact Module.End.invtSubmodule.comp _ (Module.End.invtSubmodule.comp _ (hq j hj) hi) (hq j hj)

Depends on / 依赖: Module, Module.End.invtSubmodule.comp, P.indexNeg, P.reflection, b.induction_reflect, indexNeg, induction_reflect, invtSubmodule, reflection, reflection_apply, reflection_reflectionPerm, two_smul
-/
lemma forall_mem_support_invtSubmodule_iff (q : Submodule R M) :
    (forall i in b.support, q in invtSubmodule (P.reflection i)) ↔
      (forall i, q in invtSubmodule (P.reflection i)) := by
  refine ⟨fun hq i => ?_, fun hq i _ => hq i⟩
  let := P.indexNeg
  have (j : ι) : P.reflection (-j) = P.reflection j := by ext x; simp [reflection_apply, two_smul]
  refine b.induction_reflect i (by simp_all) hq ?_
  clear i
  intro i j hi hj
  rw [reflection_reflectionPerm]
  exact Module.End.invtSubmodule.comp _ (Module.End.invtSubmodule.comp _ (hq j hj) hi) (hq j hj)

end PositiveRoots

end Base

end RootPairing
