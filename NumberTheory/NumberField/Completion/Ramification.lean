/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances
public import Mathlib.RingTheory.RamificationInertia.Inertia

/-!
# Ramification theory of completions of number fields

This file studies the ramification of completions of number fields.

## Main definitions

- `NumberField.InfinitePlace.inertiaDeg` : the inertia degree of a place `w` of `L` over a
  place `v` of `K`, defined as the local degree of the extension of completions at `w` and
  `v` if `w` lies over `v` and zero otherwise.

## Main results

- `NumberField.InfinitePlace.sum_inertiaDeg_eq_finrank` : the degree of `L` over `K` is equal to
  the sum of the inertia degrees of the places of `L` over `v`.

## Tags

number field, infinite places, ramification
-/

@[expose] public section

section infinite_place

namespace NumberField.InfinitePlace

open NumberField.ComplexEmbedding Finset AbsoluteValue.Completion

-- to enable `w.LiesOver v → Algebra v.Completion w.Completion` instance
open scoped NumberField.LiesOver

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (v : InfinitePlace K) {w : InfinitePlace L}

open Completion

/--
theorem `IsRamified.finrank_eq_two` / 定理 `IsRamified.finrank_eq_two`

English:
theorem IsRamified.finrank_eq_two
  given: [w.LiesOver v] (h : w.IsRamified K)
  proof: by
  have H := NumberField.InfinitePlace.isRamified_iff.mp h
  rw [NumberField.InfinitePlace.LiesOver.comap_eq w v] at H
  have := LiesOver.extensionEmbedding_liesOver_of_isReal w H.2
  rw [Algebra.finrank_eq_of_equiv_equiv (ringEquivRealOfIsReal H.2)
      (ringEquivComplexOfIsComplex H.1) (by ext;

中文:
定理 IsRamified.finrank_eq_two
  条件: [w.LiesOver v] (h : w.IsRamified K)
  证明: by
  have H := NumberField.InfinitePlace.isRamified_iff.mp h
  rw [NumberField.InfinitePlace.LiesOver.comap_eq w v] at H
  have := LiesOver.extensionEmbedding_liesOver_of_isReal w H.2
  rw [Algebra.finrank_eq_of_equiv_equiv (ringEquivRealOfIsReal H.2)
      (ringEquivComplexOfIsComplex H.1) (by ext;

Depends on / 依赖: Algebra, Algebra.finrank_eq_of_equiv_equiv, Complex.finrank_real_complex, InfinitePlace, LiesOver, LiesOver.extensionEmbedding_liesOver_of_isReal, NumberField, NumberField.InfinitePlace.LiesOver.comap_eq, NumberField.InfinitePlace.isRamified_iff.mp, comap_eq, extensionEmbedding_liesOver_of_isReal, finrank_eq_of_equiv_equiv, finrank_real_complex, isRamified_iff, ringEquivComplexOfIsComplex, ringEquivRealOfIsReal
-/
theorem IsRamified.finrank_eq_two [w.LiesOver v] (h : w.IsRamified K) :
    Module.finrank v.Completion w.Completion = 2 := by
  have H := NumberField.InfinitePlace.isRamified_iff.mp h
  rw [NumberField.InfinitePlace.LiesOver.comap_eq w v] at H
  have := LiesOver.extensionEmbedding_liesOver_of_isReal w H.2
  rw [Algebra.finrank_eq_of_equiv_equiv (ringEquivRealOfIsReal H.2)
      (ringEquivComplexOfIsComplex H.1) (by ext; simp)]; rw [Complex.finrank_real_complex]

/--
theorem `IsUnramified.finrank_eq_one` / 定理 `IsUnramified.finrank_eq_one`

English:
theorem IsUnramified.finrank_eq_one
  given: [w.LiesOver v] (h : w.IsUnramified K)
  proof: by
  rcases v.isReal_or_isComplex with (hv | hv)
  · have := LiesOver.extensionEmbedding_liesOver_of_isReal w hv
    rw [Algebra.finrank_eq_of_equiv_equiv (ringEquivRealOfIsReal hv) (ringEquivRealOfIsReal
(h.liesOver_isReal_over _ _ hv)) (RingHom.ext fun _ => Complex.ofReal_inj.1 by simp)]; rw [Modu

中文:
定理 IsUnramified.finrank_eq_one
  条件: [w.LiesOver v] (h : w.IsUnramified K)
  证明: by
  rcases v.isReal_or_isComplex with (hv | hv)
  · have := LiesOver.extensionEmbedding_liesOver_of_isReal w hv
    rw [Algebra.finrank_eq_of_equiv_equiv (ringEquivRealOfIsReal hv) (ringEquivRealOfIsReal
(h.liesOver_isReal_over _ _ hv)) (RingHom.ext fun _ => Complex.ofReal_inj.1 by simp)]; rw [Modu

Depends on / 依赖: Algebra, Algebra.finrank_eq_of_equiv_equiv, Complex.ofReal_inj, ComplexEmbedding, ComplexEmbedding.LiesOver, LiesOver, LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq, LiesOver.extensionEmbedding_liesOver_of_isReal, Module, Module.finrank_self, RingHom, RingHom.ext, embedding, embedding_comp_eq_or_conjugate_embedding_comp_eq, extensionEmbedding_liesOver_of_isReal, finrank_eq_of_equiv_equiv, finrank_self, h.liesOver_isReal_over, isReal_or_isComplex, liesOver_extensionEmbedding
-/
theorem IsUnramified.finrank_eq_one [w.LiesOver v] (h : w.IsUnramified K) :
    Module.finrank v.Completion w.Completion = 1 := by
  rcases v.isReal_or_isComplex with (hv | hv)
  · have := LiesOver.extensionEmbedding_liesOver_of_isReal w hv
    rw [Algebra.finrank_eq_of_equiv_equiv (ringEquivRealOfIsReal hv) (ringEquivRealOfIsReal
(h.liesOver_isReal_over _ _ hv)) (RingHom.ext fun _ => Complex.ofReal_inj.1 by simp)]; rw [Module.finrank_self]
  · cases LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq w v with
    | inl hl =>
      have : ComplexEmbedding.LiesOver w.embedding v.embedding := ⟨hl⟩
      have := liesOver_extensionEmbedding w v
      rw [Algebra.finrank_eq_of_equiv_equiv (ringEquivComplexOfIsComplex hv)
          (ringEquivComplexOfIsComplex (LiesOver.isComplex_of_isComplex_under _ hv)) (by ext; simp)]; rw [Module.finrank_self]
    | inr hr =>
      have : ComplexEmbedding.LiesOver (conjugate w.embedding) v.embedding := ⟨hr⟩
      have := liesOver_conjugate_extensionEmbedding w v
      rw [Algebra.finrank_eq_of_equiv_equiv (ringEquivComplexOfIsComplex hv)
        ((ringEquivComplexOfIsComplex (LiesOver.isComplex_of_isComplex_under _ hv)).trans
          (starRingAut (R := Complex))) (by ext; simp [← conjugate_coe_eq]),
        Module.finrank_self]

@[deprecated (since := "2026-07-10")] alias Completion.finrank_eq_two_of_isRamified :=
  IsRamified.finrank_eq_two

@[deprecated (since := "2026-07-10")] alias Completion.finrank_eq_one_of_isUnramified :=
  IsUnramified.finrank_eq_one

variable (w) in
/--
theorem `mult_mul_finrank` / 定理 `mult_mul_finrank`

English:
theorem mult_mul_finrank
  given: [w.LiesOver v]
  proof: by
  have hv : v = w.comap (algebraMap K L) := Subtype.ext ‹w.LiesOver v›.comp_eq.symm
  rcases w.isUnramified_or_isRamified K with h | h
  · rw [h.finrank_eq_one v, hv, h.eq, mul_one]
  · rw [h.finrank_eq_two v, hv, h.isReal.mult_eq_one, h.isComplex.mult_eq_two, one_mul]

中文:
定理 mult_mul_finrank
  条件: [w.LiesOver v]
  证明: by
  have hv : v = w.comap (algebraMap K L) := Subtype.ext ‹w.LiesOver v›.comp_eq.symm
  rcases w.isUnramified_or_isRamified K with h | h
  · rw [h.finrank_eq_one v, hv, h.eq, mul_one]
  · rw [h.finrank_eq_two v, hv, h.isReal.mult_eq_one, h.isComplex.mult_eq_two, one_mul]

Depends on / 依赖: LiesOver, Subtype, Subtype.ext, algebraMap, comp_eq, comp_eq.symm, finrank_eq_one, finrank_eq_two, h.eq, h.finrank_eq_one, h.finrank_eq_two, h.isComplex.mult_eq_two, h.isReal.mult_eq_one, isComplex, isReal, isUnramified_or_isRamified, mul_one, mult_eq_one, mult_eq_two, one_mul
-/
theorem mult_mul_finrank [w.LiesOver v] :
    v.mult * Module.finrank v.Completion w.Completion = w.mult := by
  have hv : v = w.comap (algebraMap K L) := Subtype.ext ‹w.LiesOver v›.comp_eq.symm
  rcases w.isUnramified_or_isRamified K with h | h
  · rw [h.finrank_eq_one v, hv, h.eq, mul_one]
  · rw [h.finrank_eq_two v, hv, h.isReal.mult_eq_one, h.isComplex.mult_eq_two, one_mul]

open Completion

variable (w)

open scoped Classical in
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def inertiaDeg
  body: if _ : w.LiesOver v then (⊥ : Ideal w.Completion).inertiaDeg v.Completion else 0

中文:
定义 noncomputable
  签名: def inertiaDeg
  定义体: if _ : w.LiesOver v then (⊥ : Ideal w.Completion).inertiaDeg v.Completion else 0
-/
protected noncomputable def inertiaDeg : Nat :=
  if _ : w.LiesOver v then (⊥ : Ideal w.Completion).inertiaDeg v.Completion else 0

/--
theorem `inertiaDeg_of_liesOver` / 定理 `inertiaDeg_of_liesOver`

English:
theorem inertiaDeg_of_liesOver
  given: [w.LiesOver v]
  proof: by
  simp only [InfinitePlace.inertiaDeg, dif_pos]

中文:
定理 inertiaDeg_of_liesOver
  条件: [w.LiesOver v]
  证明: by
  simp only [InfinitePlace.inertiaDeg, dif_pos]

Depends on / 依赖: InfinitePlace, InfinitePlace.inertiaDeg, dif_pos, inertiaDeg
-/
theorem inertiaDeg_of_liesOver [w.LiesOver v] :
    v.inertiaDeg w = (⊥ : Ideal w.Completion).inertiaDeg v.Completion := by
  simp only [InfinitePlace.inertiaDeg, dif_pos]

/--
theorem `inertiaDeg_eq_finrank` / 定理 `inertiaDeg_eq_finrank`

English:
theorem inertiaDeg_eq_finrank
  given: [w.LiesOver v]
  proof: by
  rw [inertiaDeg_of_liesOver]; rw [Ideal.inertiaDeg_eq_of_isMaximal ⊥]
  exact Algebra.finrank_eq_of_equiv_equiv (RingEquiv.quotientBot v.Completion)
    (RingEquiv.quotientBot w.Completion) (by ext; simp [RingHom.algebraMap_toAlgebra])

中文:
定理 inertiaDeg_eq_finrank
  条件: [w.LiesOver v]
  证明: by
  rw [inertiaDeg_of_liesOver]; rw [Ideal.inertiaDeg_eq_of_isMaximal ⊥]
  exact Algebra.finrank_eq_of_equiv_equiv (RingEquiv.quotientBot v.Completion)
    (RingEquiv.quotientBot w.Completion) (by ext; simp [RingHom.algebraMap_toAlgebra])

Depends on / 依赖: Algebra, Algebra.finrank_eq_of_equiv_equiv, Completion, Ideal.inertiaDeg_eq_of_isMaximal, RingEquiv, RingEquiv.quotientBot, RingHom, RingHom.algebraMap_toAlgebra, algebraMap_toAlgebra, finrank_eq_of_equiv_equiv, inertiaDeg_eq_of_isMaximal, inertiaDeg_of_liesOver, quotientBot, v.Completion, w.Completion
-/
theorem inertiaDeg_eq_finrank [w.LiesOver v] :
    v.inertiaDeg w = Module.finrank v.Completion w.Completion := by
  rw [inertiaDeg_of_liesOver]; rw [Ideal.inertiaDeg_eq_of_isMaximal ⊥]
  exact Algebra.finrank_eq_of_equiv_equiv (RingEquiv.quotientBot v.Completion)
    (RingEquiv.quotientBot w.Completion) (by ext; simp [RingHom.algebraMap_toAlgebra])

variable {v w} in
/--
theorem `inertiaDeg_eq_one` / 定理 `inertiaDeg_eq_one`

English:
theorem inertiaDeg_eq_one
  given: (hw : w in unramifiedPlacesOver L v)
  statement: v.inertiaDeg w = 1
  proof: have := (Set.mem_ofPred.1 hw).1; hw.2.finrank_eq_one v ▸ inertiaDeg_eq_finrank v w

中文:
定理 inertiaDeg_eq_one
  条件: (hw : w in unramifiedPlacesOver L v)
  结论: v.inertiaDeg w = 1
  证明: have := (Set.mem_ofPred.1 hw).1; hw.2.finrank_eq_one v ▸ inertiaDeg_eq_finrank v w

Depends on / 依赖: Set.mem_ofPred, finrank_eq_one, inertiaDeg_eq_finrank, mem_ofPred, o.out.str
-/
theorem inertiaDeg_eq_one (hw : w in unramifiedPlacesOver L v) : v.inertiaDeg w = 1 :=
  have := (Set.mem_ofPred.1 hw).1; hw.2.finrank_eq_one v ▸ inertiaDeg_eq_finrank v w

variable {v w} in
/--
theorem `inertiaDeg_eq_two` / 定理 `inertiaDeg_eq_two`

English:
theorem inertiaDeg_eq_two
  given: (hw : w in ramifiedPlacesOver L v)
  statement: v.inertiaDeg w = 2
  proof: have := (Set.mem_ofPred.1 hw).1; hw.2.finrank_eq_two v ▸ inertiaDeg_eq_finrank v w

中文:
定理 inertiaDeg_eq_two
  条件: (hw : w in ramifiedPlacesOver L v)
  结论: v.inertiaDeg w = 2
  证明: have := (Set.mem_ofPred.1 hw).1; hw.2.finrank_eq_two v ▸ inertiaDeg_eq_finrank v w

Depends on / 依赖: Set.mem_ofPred, finrank_eq_two, inertiaDeg_eq_finrank, mem_ofPred
-/
theorem inertiaDeg_eq_two (hw : w in ramifiedPlacesOver L v) : v.inertiaDeg w = 2 :=
  have := (Set.mem_ofPred.1 hw).1; hw.2.finrank_eq_two v ▸ inertiaDeg_eq_finrank v w

variable (K L) in
open scoped Classical in
open Finset Set in
/--
theorem `sum_inertiaDeg_eq_finrank` / 定理 `sum_inertiaDeg_eq_finrank`

English:
theorem sum_inertiaDeg_eq_finrank
  given: [NumberField K] [NumberField L]
  proof: by
  rw [← union_ramifiedPlacesOver_unramifiedPlacesOver L v]; rw [toFinset_union]; rw [sum_union (Set.disjoint_toFinset.2 <| disjoint_ramifiedPlacesOver_unramifiedPlacesOver L v)]; rw [sum_congr rfl (fun _ h => inertiaDeg_eq_two (by simpa using h))]; rw [sum_congr rfl (fun _ h => inertiaDeg_eq_one 

中文:
定理 sum_inertiaDeg_eq_finrank
  条件: [NumberField K] [NumberField L]
  证明: by
  rw [← union_ramifiedPlacesOver_unramifiedPlacesOver L v]; rw [toFinset_union]; rw [sum_union (Set.disjoint_toFinset.2 <| disjoint_ramifiedPlacesOver_unramifiedPlacesOver L v)]; rw [sum_congr rfl (fun _ h => inertiaDeg_eq_two (by simpa using h))]; rw [sum_congr rfl (fun _ h => inertiaDeg_eq_one 

Depends on / 依赖: Set.disjoint_toFinset, add_comm, disjoint_ramifiedPlacesOver_unramifiedPlacesOver, disjoint_toFinset, inertiaDeg_eq_one, inertiaDeg_eq_two, mul_comm, ncard_eq_toFinset_card, sum_congr, sum_const, sum_union, toFinset_union, union_ramifiedPlacesOver_unramifiedPlacesOver, unramifedPlacesOver_ncard_add_eq_finrank
-/
theorem sum_inertiaDeg_eq_finrank [NumberField K] [NumberField L] :
    ∑ w in v.placesOver L, v.inertiaDeg w = Module.finrank K L := by
  rw [← union_ramifiedPlacesOver_unramifiedPlacesOver L v]; rw [toFinset_union]; rw [sum_union (Set.disjoint_toFinset.2 <| disjoint_ramifiedPlacesOver_unramifiedPlacesOver L v)]; rw [sum_congr rfl (fun _ h => inertiaDeg_eq_two (by simpa using h))]; rw [sum_congr rfl (fun _ h => inertiaDeg_eq_one (by simpa using h))]; rw [sum_const]; rw [add_comm]
  simp [← unramifedPlacesOver_ncard_add_eq_finrank L v, mul_comm, ncard_eq_toFinset_card']

end NumberField.InfinitePlace

end infinite_place
