/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.Prod

import Mathlib.Data.Fintype.Order

/-!
# Convex sets

This file defines convex sets in a convex space.

## Implementation notes

To support non-field coefficients, for `s` to be convex we require that all finitary convex
combinations of points of `s` lie in `s`, instead of merely binary ones as is customary.

Since its body is an implementation detail, the predicate `IsConvexSet` is unexposed.
-/

open Finsupp Set

public noncomputable section

namespace Convexity
variable {ι I R K X Y : Type*}

section Semiring
variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] [ConvexSpace R X] [ConvexSpace R Y]
  {f : X -> Y} {w : StdSimplex R X} {s t : Set X} {x y : X}

variable (R s) in
/--
Definition of `IsConvexSet` / `IsConvexSet` 的定义

English:
definition IsConvexSet
  signature: : Prop
  body: forall ⦃w : StdSimplex R X⦄, ↑w.weights.support subseteq s -> w.sConvexComb in s

中文:
定义 IsConvexSet
  签名: : 命题
  定义体: forall ⦃w : StdSimplex R X⦄, ↑w.weights.support subseteq s -> w.sConvexComb in s

Depends on / 依赖: StdSimplex, sConvexComb, subseteq, support, w.sConvexComb, w.weights.support, weights
-/
def IsConvexSet : Prop := forall ⦃w : StdSimplex R X⦄, ↑w.weights.support subseteq s -> w.sConvexComb in s

/--
lemma `IsConvexSet.of_sConvexComb_mem` / 引理 `IsConvexSet.of_sConvexComb_mem`

English:
lemma IsConvexSet.of_sConvexComb_mem
  proof: hs

中文:
引理 IsConvexSet.of_sConvexComb_mem
  证明: hs
-/
lemma IsConvexSet.of_sConvexComb_mem
    (hs : forall w : StdSimplex R X, ↑w.weights.support subseteq s -> w.sConvexComb in s) : IsConvexSet R s :=
  hs

/--
lemma `IsConvexSet.sConvexComb_mem` / 引理 `IsConvexSet.sConvexComb_mem`

English:
lemma IsConvexSet.sConvexComb_mem
  given: (hs : IsConvexSet R s) (hw : ↑w.weights.support subseteq s)
  proof: hs hw

中文:
引理 IsConvexSet.sConvexComb_mem
  条件: (hs : IsConvexSet R s) (hw : ↑w.weights.support subseteq s)
  证明: hs hw
-/
lemma IsConvexSet.sConvexComb_mem (hs : IsConvexSet R s) (hw : ↑w.weights.support subseteq s) :
    w.sConvexComb in s := hs hw

/--
lemma `IsConvexSet.iConvexComb_mem` / 引理 `IsConvexSet.iConvexComb_mem`

English:
lemma IsConvexSet.iConvexComb_mem
  statement: (hs : IsConvexSet R s) {w : StdSimplex R ι} {f : ι -> X}
  proof: by
  classical
  refine hs ?_
  grw [StdSimplex.weights_map, mapDomain_support]
  simpa [subset_def]

中文:
引理 IsConvexSet.iConvexComb_mem
  结论: (hs : IsConvexSet R s) {w : StdSimplex R ι} {f : ι -> X}
  证明: by
  classical
  refine hs ?_
  grw [StdSimplex.weights_map, mapDomain_support]
  simpa [subset_def]

Depends on / 依赖: StdSimplex, StdSimplex.weights_map, classical, mapDomain_support, subset_def, weights_map
-/
lemma IsConvexSet.iConvexComb_mem (hs : IsConvexSet R s) {w : StdSimplex R ι} {f : ι -> X}
    (hf : forall i, w.weights i != 0 -> f i in s) : w.iConvexComb f in s := by
  classical
  refine hs ?_
  grw [StdSimplex.weights_map, mapDomain_support]
  simpa [subset_def]

/--
lemma `IsConvexSet.convexCombPair_mem` / 引理 `IsConvexSet.convexCombPair_mem`

English:
lemma IsConvexSet.convexCombPair_mem
  statement: (hs : IsConvexSet R s) (hx : x in s) (hy : y in s)
  proof: by
  classical
  refine hs.sConvexComb_mem ?_
  grw [StdSimplex.weights_duple, support_add, support_single_subset, support_single_subset]
  simp [*, insert_subset_iff]

中文:
引理 IsConvexSet.convexCombPair_mem
  结论: (hs : IsConvexSet R s) (hx : x in s) (hy : y in s)
  证明: by
  classical
  refine hs.sConvexComb_mem ?_
  grw [StdSimplex.weights_duple, support_add, support_single_subset, support_single_subset]
  simp [*, insert_subset_iff]

Depends on / 依赖: StdSimplex, StdSimplex.weights_duple, classical, hs.sConvexComb_mem, insert_subset_iff, sConvexComb_mem, support_add, support_single_subset, weights_duple
-/
lemma IsConvexSet.convexCombPair_mem (hs : IsConvexSet R s) (hx : x in s) (hy : y in s)
    {a b : R} (ha hb hab) : convexCombPair a b ha hb hab x y in s := by
  classical
  refine hs.sConvexComb_mem ?_
  grw [StdSimplex.weights_duple, support_add, support_single_subset, support_single_subset]
  simp [*, insert_subset_iff]

/--
lemma `IsConvexSet.empty` / 引理 `IsConvexSet.empty`

English:
lemma IsConvexSet.empty
  statement: IsConvexSet R (∅ : Set X)
  proof: by simp [IsConvexSet]

中文:
引理 IsConvexSet.empty
  结论: IsConvexSet R (∅ : Set X)
  证明: by simp [IsConvexSet]
-/
@[simp] protected lemma IsConvexSet.empty : IsConvexSet R (∅ : Set X) := by simp [IsConvexSet]
/--
lemma `IsConvexSet.univ` / 引理 `IsConvexSet.univ`

English:
lemma IsConvexSet.univ
  statement: IsConvexSet R (.univ : Set X)
  proof: by simp [IsConvexSet]

中文:
引理 IsConvexSet.univ
  结论: IsConvexSet R (.univ : Set X)
  证明: by simp [IsConvexSet]
-/
@[simp] protected lemma IsConvexSet.univ : IsConvexSet R (.univ : Set X) := by simp [IsConvexSet]

/--
lemma `IsConvexSet.singleton` / 引理 `IsConvexSet.singleton`

English:
lemma IsConvexSet.singleton
  statement: IsConvexSet R {x}
  proof: by
  simp [IsConvexSet, -subset_singleton_iff, Finset.coe_subset_singleton]

中文:
引理 IsConvexSet.singleton
  结论: IsConvexSet R {x}
  证明: by
  simp [IsConvexSet, -subset_singleton_iff, Finset.coe_subset_singleton]
-/
@[simp] protected lemma IsConvexSet.singleton : IsConvexSet R {x} := by
  simp [IsConvexSet, -subset_singleton_iff, Finset.coe_subset_singleton]

/--
lemma `IsConvexSet.of_subsingleton` / 引理 `IsConvexSet.of_subsingleton`

English:
lemma IsConvexSet.of_subsingleton
  given: (hs : s.Subsingleton)
  statement: IsConvexSet R s
  proof: by
  obtain rfl | ⟨x, rfl⟩ := hs.eq_empty_or_singleton <;> simp

中文:
引理 IsConvexSet.of_subsingleton
  条件: (hs : s.Subsingleton)
  结论: IsConvexSet R s
  证明: by
  obtain rfl | ⟨x, rfl⟩ := hs.eq_empty_or_singleton <;> simp

Depends on / 依赖: eq_empty_or_singleton, hs.eq_empty_or_singleton
-/
lemma IsConvexSet.of_subsingleton (hs : s.Subsingleton) : IsConvexSet R s := by
  obtain rfl | ⟨x, rfl⟩ := hs.eq_empty_or_singleton <;> simp

/--
lemma `IsConvexSet.inter` / 引理 `IsConvexSet.inter`

English:
lemma IsConvexSet.inter
  given: (hs : IsConvexSet R s) (ht : IsConvexSet R t)
  proof: by
  simp +contextual [IsConvexSet, hs.sConvexComb_mem, ht.sConvexComb_mem]

中文:
引理 IsConvexSet.inter
  条件: (hs : IsConvexSet R s) (ht : IsConvexSet R t)
  证明: by
  simp +contextual [IsConvexSet, hs.sConvexComb_mem, ht.sConvexComb_mem]
-/
protected lemma IsConvexSet.inter (hs : IsConvexSet R s) (ht : IsConvexSet R t) :
    IsConvexSet R (s inter t) := by
  simp +contextual [IsConvexSet, hs.sConvexComb_mem, ht.sConvexComb_mem]

/--
lemma `IsConvexSet.sInter` / 引理 `IsConvexSet.sInter`

English:
lemma IsConvexSet.sInter
  given: {S : Set (Set X)} (hS : forall s in S, IsConvexSet R s)
  proof: by simp +contextual [IsConvexSet, (hS _ _).sConvexComb_mem]

中文:
引理 IsConvexSet.sInter
  条件: {S : Set (Set X)} (hS : 对任意 s in S, IsConvexSet R s)
  证明: by simp +contextual [IsConvexSet, (hS _ _).sConvexComb_mem]
-/
protected lemma IsConvexSet.sInter {S : Set (Set X)} (hS : forall s in S, IsConvexSet R s) :
    IsConvexSet R (⋂₀ S) := by simp +contextual [IsConvexSet, (hS _ _).sConvexComb_mem]

/--
lemma `IsConvexSet.iInter` / 引理 `IsConvexSet.iInter`

English:
lemma IsConvexSet.iInter
  given: {ι : Sort*} {s : ι -> Set X} (hs : forall i, IsConvexSet R (s i))
  proof: by simp +contextual [IsConvexSet, (hs _).sConvexComb_mem]

中文:
引理 IsConvexSet.iInter
  条件: {ι : Sort*} {s : ι -> Set X} (hs : 对任意 i, IsConvexSet R (s i))
  证明: by simp +contextual [IsConvexSet, (hs _).sConvexComb_mem]
-/
protected lemma IsConvexSet.iInter {ι : Sort*} {s : ι -> Set X} (hs : forall i, IsConvexSet R (s i)) :
    IsConvexSet R (⋂ i, s i) := by simp +contextual [IsConvexSet, (hs _).sConvexComb_mem]

/--
lemma `IsConvexSet.iInter₂` / 引理 `IsConvexSet.iInter₂`

English:
lemma IsConvexSet.iInter₂
  statement: {ι : Sort*} {κ : ι -> Sort*} {s : forall i, κ i -> Set X}
  proof: .iInter fun i => .iInter h i

中文:
引理 IsConvexSet.iInter₂
  结论: {ι : Sort*} {κ : ι -> Sort*} {s : 对任意 i, κ i -> Set X}
  证明: .iInter fun i => .iInter h i

Depends on / 依赖: iInter
-/
lemma IsConvexSet.iInter₂ {ι : Sort*} {κ : ι -> Sort*} {s : forall i, κ i -> Set X}
    (h : forall i j, IsConvexSet R (s i j)) : IsConvexSet R (⋂ (i) (j), s i j) :=
.iInter fun i => .iInter h i

/--
lemma `IsConvexSet.sUnion` / 引理 `IsConvexSet.sUnion`

English:
lemma IsConvexSet.sUnion
  statement: {S : Set (Set X)} (hS : DirectedOn (· subseteq ·) S)
  proof: by
  obtain rfl | hS'' := S.eq_empty_or_nonempty
  · simp
  rintro w hw
  obtain ⟨s, hsS, hws⟩ :=
    hS.exists_mem_subset_of_finite_of_subset_sUnion hS'' w.weights.support.finite_toSet hw
  exact mem_sUnion_of_mem (hS' s hsS hws) hsS

中文:
引理 IsConvexSet.sUnion
  结论: {S : Set (Set X)} (hS : DirectedOn (· subseteq ·) S)
  证明: by
  obtain rfl | hS'' := S.eq_empty_or_nonempty
  · simp
  rintro w hw
  obtain ⟨s, hsS, hws⟩ :=
    hS.exists_mem_subset_of_finite_of_subset_sUnion hS'' w.weights.support.finite_toSet hw
  exact mem_sUnion_of_mem (hS' s hsS hws) hsS
-/
protected lemma IsConvexSet.sUnion {S : Set (Set X)} (hS : DirectedOn (· subseteq ·) S)
    (hS' : forall s in S, IsConvexSet R s) : IsConvexSet R (⋃₀ S) := by
  obtain rfl | hS'' := S.eq_empty_or_nonempty
  · simp
  rintro w hw
  obtain ⟨s, hsS, hws⟩ :=
    hS.exists_mem_subset_of_finite_of_subset_sUnion hS'' w.weights.support.finite_toSet hw
  exact mem_sUnion_of_mem (hS' s hsS hws) hsS

/--
lemma `IsConvexSet.iUnion` / 引理 `IsConvexSet.iUnion`

English:
lemma IsConvexSet.iUnion
  statement: {ι : Sort*} {s : ι -> Set X} (hs : Directed (· subseteq ·) s)
  proof: .sUnion hs.directedOn_range by simpa

中文:
引理 IsConvexSet.iUnion
  结论: {ι : Sort*} {s : ι -> Set X} (hs : Directed (· subseteq ·) s)
  证明: .sUnion hs.directedOn_range by simpa
-/
protected lemma IsConvexSet.iUnion {ι : Sort*} {s : ι -> Set X} (hs : Directed (· subseteq ·) s)
    (hs' : forall i, IsConvexSet R (s i)) : IsConvexSet R (⋃ i, s i) :=
.sUnion hs.directedOn_range by simpa

/--
lemma `IsConvexSet.preimage` / 引理 `IsConvexSet.preimage`

English:
lemma IsConvexSet.preimage
  given: {s : Set Y} (hf : IsAffineMap R f) (hs : IsConvexSet R s)
  proof: by
  rintro w hw
  simp only [mem_preimage, hf.map_sConvexComb, sConvexComb_map]
exact hs.iConvexComb_mem fun x hx => hw by simpa

中文:
引理 IsConvexSet.preimage
  条件: {s : Set Y} (hf : IsAffineMap R f) (hs : IsConvexSet R s)
  证明: by
  rintro w hw
  simp only [mem_preimage, hf.map_sConvexComb, sConvexComb_map]
exact hs.iConvexComb_mem fun x hx => hw by simpa
-/
protected lemma IsConvexSet.preimage {s : Set Y} (hf : IsAffineMap R f) (hs : IsConvexSet R s) :
    IsConvexSet R (f ⁻¹' s) := by
  rintro w hw
  simp only [mem_preimage, hf.map_sConvexComb, sConvexComb_map]
exact hs.iConvexComb_mem fun x hx => hw by simpa

/--
lemma `IsConvexSet.image` / 引理 `IsConvexSet.image`

English:
lemma IsConvexSet.image
  given: (hf : IsAffineMap R f) (hs : IsConvexSet R s)
  proof: by
  classical
  rintro w hw
  obtain ⟨u, hus, hfu, huw⟩ := Finset.exists_subset_injOn_image_eq_of_surjOn _ _ hw
  refine ⟨sConvexComb {
weights := .onFinset u (fun x => if x in u then w.weights (f x) else 0) by simp +contextual
      nonneg x := by simp; split <;> simp
      total := by
        sim

中文:
引理 IsConvexSet.image
  条件: (hf : IsAffineMap R f) (hs : IsConvexSet R s)
  证明: by
  classical
  rintro w hw
  obtain ⟨u, hus, hfu, huw⟩ := Finset.exists_subset_injOn_image_eq_of_surjOn _ _ hw
  refine ⟨sConvexComb {
weights := .onFinset u (fun x => if x in u then w.weights (f x) else 0) by simp +contextual
      nonneg x := by simp; split <;> simp
      total := by
        sim
-/
protected lemma IsConvexSet.image (hf : IsAffineMap R f) (hs : IsConvexSet R s) :
    IsConvexSet R (f '' s) := by
  classical
  rintro w hw
  obtain ⟨u, hus, hfu, huw⟩ := Finset.exists_subset_injOn_image_eq_of_surjOn _ _ hw
  refine ⟨sConvexComb {
weights := .onFinset u (fun x => if x in u then w.weights (f x) else 0) by simp +contextual
      nonneg x := by simp; split <;> simp
      total := by
        simp only [implies_true, sum_onFinset, Finset.sum_ite_mem, Finset.inter_self,
        ← Finset.sum_image hfu, huw]
        exact w.total
    }, hs.sConvexComb_mem <| by grw [support_onFinset_subset, hus], ?_⟩
  rw [hf.map_sConvexComb]
  congr
  ext y
  rw [StdSimplex.weights_map]
  by_cases hy : y in w.weights.support
  · rw [← huw, Finset.mem_image] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    convert mapDomain_apply' _ _ support_onFinset_subset hfu hx
    exact (if_pos hx).symm
  · rw [mapDomain_of_not_mem_image_support (by simp [← huw] at ⊢ hy; tauto)]
    simp_all

/-- A convex subset of a convex space is a convex space. -/
@[expose, implicit_reducible]
/--
Definition of `ConvexSpace.subtype` / `ConvexSpace.subtype` 的定义

English:
definition ConvexSpace.subtype
  signature: (s : Set X) (hs : IsConvexSet R s)
  body: .mk
  (fun w => ⟨w.iConvexComb (↑), hs.iConvexComb_mem <| by simp⟩)
  (fun x => by simp)
  (fun w => by ext; simp [iConvexComb_assoc])

中文:
定义 ConvexSpace.subtype
  签名: (s : Set X) (hs : IsConvexSet R s)
  定义体: .mk
  (fun w => ⟨w.iConvexComb (↑), hs.iConvexComb_mem <| by simp⟩)
  (fun x => by simp)
  (fun w => by ext; simp [iConvexComb_assoc])
-/
def ConvexSpace.subtype (s : Set X) (hs : IsConvexSet R s) : ConvexSpace R s := .mk
  (fun w => ⟨w.iConvexComb (↑), hs.iConvexComb_mem <| by simp⟩)
  (fun x => by simp)
  (fun w => by ext; simp [iConvexComb_assoc])

/--
lemma `isAffineMap_subtypeVal` / 引理 `isAffineMap_subtypeVal`

English:
lemma isAffineMap_subtypeVal
  given: (s : Set X) (hs : IsConvexSet R s)
  proof: .subtype s hs
    IsAffineMap R ((↑) : s -> X) :=
  letI : ConvexSpace R s := .subtype s hs
  ⟨fun _ => rfl⟩

@[simp]

中文:
引理 isAffineMap_subtypeVal
  条件: (s : Set X) (hs : IsConvexSet R s)
  证明: .subtype s hs
    IsAffineMap R ((↑) : s -> X) :=
  letI : ConvexSpace R s := .subtype s hs
  ⟨fun _ => rfl⟩

@[simp]

Depends on / 依赖: subtype
-/
lemma isAffineMap_subtypeVal (s : Set X) (hs : IsConvexSet R s) :
    letI : ConvexSpace R s := .subtype s hs
    IsAffineMap R ((↑) : s -> X) :=
  letI : ConvexSpace R s := .subtype s hs
  ⟨fun _ => rfl⟩

@[simp]
/--
lemma `subtypeVal_sConvexComb` / 引理 `subtypeVal_sConvexComb`

English:
lemma subtypeVal_sConvexComb
  given: (s : Set X) (hs : IsConvexSet R s) (w : StdSimplex R s)
  proof: .subtype s hs
    (w.sConvexComb : X) = w.iConvexComb (↑) := rfl

@[simp]

中文:
引理 subtypeVal_sConvexComb
  条件: (s : Set X) (hs : IsConvexSet R s) (w : StdSimplex R s)
  证明: .subtype s hs
    (w.sConvexComb : X) = w.iConvexComb (↑) := rfl

@[simp]

Depends on / 依赖: subtype
-/
lemma subtypeVal_sConvexComb (s : Set X) (hs : IsConvexSet R s) (w : StdSimplex R s) :
    letI : ConvexSpace R s := .subtype s hs
    (w.sConvexComb : X) = w.iConvexComb (↑) := rfl

@[simp]
/--
lemma `subtypeVal_iConvexComb` / 引理 `subtypeVal_iConvexComb`

English:
lemma subtypeVal_iConvexComb
  given: (s : Set X) (hs : IsConvexSet R s) (w : StdSimplex R I) (f : I -> s)
  proof: .subtype s hs
    (↑(w.iConvexComb f) : X) = w.iConvexComb (fun i => (f i).val) :=
  letI : ConvexSpace R s := .subtype s hs
  (isAffineMap_subtypeVal ..).map_iConvexComb ..

@[simp]

中文:
引理 subtypeVal_iConvexComb
  条件: (s : Set X) (hs : IsConvexSet R s) (w : StdSimplex R I) (f : I -> s)
  证明: .subtype s hs
    (↑(w.iConvexComb f) : X) = w.iConvexComb (fun i => (f i).val) :=
  letI : ConvexSpace R s := .subtype s hs
  (isAffineMap_subtypeVal ..).map_iConvexComb ..

@[simp]

Depends on / 依赖: subtype
-/
lemma subtypeVal_iConvexComb (s : Set X) (hs : IsConvexSet R s) (w : StdSimplex R I) (f : I -> s) :
    letI : ConvexSpace R s := .subtype s hs
    (↑(w.iConvexComb f) : X) = w.iConvexComb (fun i => (f i).val) :=
  letI : ConvexSpace R s := .subtype s hs
  (isAffineMap_subtypeVal ..).map_iConvexComb ..

@[simp]
/--
lemma `subtypeVal_convexCombPair` / 引理 `subtypeVal_convexCombPair`

English:
lemma subtypeVal_convexCombPair
  given: (s : Set X) (hs : IsConvexSet R s) (a b : R) (ha hb hab) (x y : s)
  proof: .subtype s hs
    (↑(convexCombPair a b ha hb hab x y) : X) = convexCombPair a b ha hb hab x.val y.val :=
  letI : ConvexSpace R s := .subtype s hs
  (isAffineMap_subtypeVal ..).map_convexCombPair ..

中文:
引理 subtypeVal_convexCombPair
  条件: (s : Set X) (hs : IsConvexSet R s) (a b : R) (ha hb hab) (x y : s)
  证明: .subtype s hs
    (↑(convexCombPair a b ha hb hab x y) : X) = convexCombPair a b ha hb hab x.val y.val :=
  letI : ConvexSpace R s := .subtype s hs
  (isAffineMap_subtypeVal ..).map_convexCombPair ..

Depends on / 依赖: subtype
-/
lemma subtypeVal_convexCombPair (s : Set X) (hs : IsConvexSet R s) (a b : R) (ha hb hab) (x y : s) :
    letI : ConvexSpace R s := .subtype s hs
    (↑(convexCombPair a b ha hb hab x y) : X) = convexCombPair a b ha hb hab x.val y.val :=
  letI : ConvexSpace R s := .subtype s hs
  (isAffineMap_subtypeVal ..).map_convexCombPair ..

/--
lemma `IsConvexSet.prod` / 引理 `IsConvexSet.prod`

English:
lemma IsConvexSet.prod
  statement: {Y : Type*} [ConvexSpace R Y] {t : Set Y}
  proof: by
  classical
  rintro w hw
  refine ⟨hs ?_, ht ?_⟩
  · grw [StdSimplex.weights_map, mapDomain_support, Finset.coe_image, hw, fst_image_prod_subset]
  · grw [StdSimplex.weights_map, mapDomain_support, Finset.coe_image, hw, snd_image_prod_subset]

中文:
引理 IsConvexSet.prod
  结论: {Y : 类型} [ConvexSpace R Y] {t : Set Y}
  证明: by
  classical
  rintro w hw
  refine ⟨hs ?_, ht ?_⟩
  · grw [StdSimplex.weights_map, mapDomain_support, Finset.coe_image, hw, fst_image_prod_subset]
  · grw [StdSimplex.weights_map, mapDomain_support, Finset.coe_image, hw, snd_image_prod_subset]
-/
protected lemma IsConvexSet.prod {Y : Type*} [ConvexSpace R Y] {t : Set Y}
    (hs : IsConvexSet R s) (ht : IsConvexSet R t) : IsConvexSet R (s ×ˢ t) := by
  classical
  rintro w hw
  refine ⟨hs ?_, ht ?_⟩
  · grw [StdSimplex.weights_map, mapDomain_support, Finset.coe_image, hw, fst_image_prod_subset]
  · grw [StdSimplex.weights_map, mapDomain_support, Finset.coe_image, hw, snd_image_prod_subset]

/--
lemma `IsConvexSet.pi` / 引理 `IsConvexSet.pi`

English:
lemma IsConvexSet.pi
  statement: {X : ι -> Type*} [forall i, ConvexSpace R (X i)] {s : Set ι}
  proof: by
  classical
  refine fun w hw i hi => ht i hi ?_
  grw [StdSimplex.weights_map, mapDomain_support, Finset.coe_image, hw, eval_image_pi_subset hi]

中文:
引理 IsConvexSet.pi
  结论: {X : ι -> 类型} [对任意 i, ConvexSpace R (X i)] {s : Set ι}
  证明: by
  classical
  refine fun w hw i hi => ht i hi ?_
  grw [StdSimplex.weights_map, mapDomain_support, Finset.coe_image, hw, eval_image_pi_subset hi]
-/
protected lemma IsConvexSet.pi {X : ι -> Type*} [forall i, ConvexSpace R (X i)] {s : Set ι}
    {t : forall i, Set (X i)} (ht : forall i in s, IsConvexSet R (t i)) : IsConvexSet R (s.pi t) := by
  classical
  refine fun w hw i hi => ht i hi ?_
  grw [StdSimplex.weights_map, mapDomain_support, Finset.coe_image, hw, eval_image_pi_subset hi]

end Semiring

section Field
variable [Field K] [LinearOrder K] [IsStrictOrderedRing K] [ConvexSpace K X] {w : StdSimplex K X}
  {s t : Set X} {x y : X}

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `IsConvexSet.of_convexCombPair_mem` / 引理 `IsConvexSet.of_convexCombPair_mem`

English:
lemma IsConvexSet.of_convexCombPair_mem
  proof: by
  classical
  rintro w hw
  set t := w.weights.support with hsw
  have ht : t.Nonempty := w.support_weights_nonempty
  clear_value t
  induction ht using Finset.Nonempty.cons_induction generalizing w with
  | singleton x => simp_all [eq_comm]
  | cons x t hx ht ih =>
  have hwx : w.weights x != 0

中文:
引理 IsConvexSet.of_convexCombPair_mem
  证明: by
  classical
  rintro w hw
  set t := w.weights.support with hsw
  have ht : t.Nonempty := w.support_weights_nonempty
  clear_value t
  induction ht using Finset.Nonempty.cons_induction generalizing w with
  | singleton x => simp_all [eq_comm]
  | cons x t hx ht ih =>
  have hwx : w.weights x != 0

Depends on / 依赖: Finset, Finset.Nonempty.cons_induction, Nonempty, classical, clear_value, cons_induction, convexCombPair_restrict_res, eq_comm, generalizing, ne_of_mem_of_not_mem, singleton, support, support_weights_nonempty, t.Nonempty, w.convexCombPair_restrict_res, w.support_weights_nonempty, w.weights, w.weights.support, weights
-/
lemma IsConvexSet.of_convexCombPair_mem
    (hs : forall a b : K, forall ha hb hab, forall x in s, forall y in s, convexCombPair a b ha hb hab x y in s) :
    IsConvexSet K s := by
  classical
  rintro w hw
  set t := w.weights.support with hsw
  have ht : t.Nonempty := w.support_weights_nonempty
  clear_value t
  induction ht using Finset.Nonempty.cons_induction generalizing w with
  | singleton x => simp_all [eq_comm]
  | cons x t hx ht ih =>
  have hwx : w.weights x != 0 := by simpa using congr(x in $hsw)
  have hwx' : exists y != x, w.weights y != 0 := by
    obtain ⟨y, hy⟩ := ht
    exact ⟨y, ne_of_mem_of_not_mem hy hx, by simpa [hy] using congr(y in $hsw)⟩
  rw [← w.convexCombPair_restrict_restrict_compl {x} (by simpa) hwx']
  simp only [mem_singleton_iff, StdSimplex.restrict_singleton, sConvexComb_convexCombPair,
    sConvexComb_single]
exact hs _ _ _ _ _ _ (hw <| by simp) _ ih (by grw [← hw, ← Finset.subset_cons])
    (by simp [← hsw]; grind)

end Field
end Convexity
