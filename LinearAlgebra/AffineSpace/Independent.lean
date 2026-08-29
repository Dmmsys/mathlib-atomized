/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Sign.Basic
public import Mathlib.LinearAlgebra.AffineSpace.Combination
public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Affine independence

This file defines affinely independent families of points.

## Main definitions

* `AffineIndependent` defines affinely independent families of points
  as those where no nontrivial weighted subtraction is `0`. This is
  proved equivalent to two other formulations: linear independence of
  the results of subtracting a base point in the family from the other
  points in the family, or any equal affine combinations having the
  same weights.

## References

* https://en.wikipedia.org/wiki/Affine_space

-/

@[expose] public section


noncomputable section

open Finset Function Module
open scoped Affine

section AffineIndependent

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
variable [AffineSpace V P] {ι : Type*}

/--
Definition of `AffineIndependent` / `AffineIndependent` 的定义

English:
definition AffineIndependent
  signature: (p : ι -> P)
  body: forall (s : Finset ι) (w : ι -> k),
    ∑ i in s, w i = 0 -> s.weightedVSub p w = (0 : V) -> forall i in s, w i = 0

中文:
定义 AffineIndependent
  签名: (p : ι -> P)
  定义体: forall (s : Finset ι) (w : ι -> k),
    ∑ i in s, w i = 0 -> s.weightedVSub p w = (0 : V) -> forall i in s, w i = 0

Depends on / 依赖: Finset, List.prod_toFinset, MeasurableEquiv, MeasurableEquiv.map_apply, MeasurableEquiv.piMeasurableEquivTProd_symm_apply, classical, elim_preimage_pi, map_apply, piMeasurableEquivTProd_symm_apply, prod_toFinset, s.weightedVSub, sortedUniv_nodup, sortedUniv_toFinset, tprod_tprod, weightedVSub
-/
def AffineIndependent (p : ι -> P) : Prop :=
  forall (s : Finset ι) (w : ι -> k),
    ∑ i in s, w i = 0 -> s.weightedVSub p w = (0 : V) -> forall i in s, w i = 0

/--
theorem `affineIndependent_def` / 定理 `affineIndependent_def`

English:
theorem affineIndependent_def
  given: (p : ι -> P)
  proof: Iff.rfl

中文:
定理 affineIndependent_def
  条件: (p : ι -> P)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem affineIndependent_def (p : ι -> P) :
    AffineIndependent k p ↔
      forall (s : Finset ι) (w : ι -> k),
        ∑ i in s, w i = 0 -> s.weightedVSub p w = (0 : V) -> forall i in s, w i = 0 :=
  Iff.rfl

/--
theorem `affineIndependent_of_subsingleton` / 定理 `affineIndependent_of_subsingleton`

English:
theorem affineIndependent_of_subsingleton
  given: [Subsingleton ι] (p : ι -> P)
  statement: AffineIndependent k p
  proof: fun _ _ h _ i hi => Fintype.eq_of_subsingleton_of_sum_eq h i hi

中文:
定理 affineIndependent_of_subsingleton
  条件: [Subsingleton ι] (p : ι -> P)
  结论: AffineIndependent k p
  证明: fun _ _ h _ i hi => Fintype.eq_of_subsingleton_of_sum_eq h i hi

Depends on / 依赖: Fintype, Fintype.eq_of_subsingleton_of_sum_eq, eq_of_subsingleton_of_sum_eq
-/
theorem affineIndependent_of_subsingleton [Subsingleton ι] (p : ι -> P) : AffineIndependent k p :=
  fun _ _ h _ i hi => Fintype.eq_of_subsingleton_of_sum_eq h i hi

/--
theorem `affineIndependent_iff_of_fintype` / 定理 `affineIndependent_iff_of_fintype`

English:
theorem affineIndependent_iff_of_fintype
  given: [Fintype ι] (p : ι -> P)
  proof: by
  constructor
  · exact fun h w hw hs i => h Finset.univ w hw hs i (Finset.mem_univ _)
  · intro h s w hw hs i hi
    rw [Finset.weightedVSub_indicator_subset _ _ (Finset.subset_univ s)] at hs
    rw [← Finset.sum_indicator_subset _ (Finset.subset_univ s)] at hw
    replace h := h ((↑s : Set ι).i

中文:
定理 affineIndependent_iff_of_fintype
  条件: [Fintype ι] (p : ι -> P)
  证明: by
  constructor
  · exact fun h w hw hs i => h Finset.univ w hw hs i (Finset.mem_univ _)
  · intro h s w hw hs i hi
    rw [Finset.weightedVSub_indicator_subset _ _ (Finset.subset_univ s)] at hs
    rw [← Finset.sum_indicator_subset _ (Finset.subset_univ s)] at hw
    replace h := h ((↑s : Set ι).i

Depends on / 依赖: Finset, Finset.mem_univ, Finset.subset_univ, Finset.sum_indicator_subset, Finset.univ, Finset.weightedVSub_indicator_subset, indicator, mem_univ, replace, subset_univ, sum_indicator_subset, weightedVSub_indicator_subset
-/
theorem affineIndependent_iff_of_fintype [Fintype ι] (p : ι -> P) :
    AffineIndependent k p ↔
      forall w : ι -> k, ∑ i, w i = 0 -> Finset.univ.weightedVSub p w = (0 : V) -> forall i, w i = 0 := by
  constructor
  · exact fun h w hw hs i => h Finset.univ w hw hs i (Finset.mem_univ _)
  · intro h s w hw hs i hi
    rw [Finset.weightedVSub_indicator_subset _ _ (Finset.subset_univ s)] at hs
    rw [← Finset.sum_indicator_subset _ (Finset.subset_univ s)] at hw
    replace h := h ((↑s : Set ι).indicator w) hw hs i
    simpa [hi] using h

/--
lemma `affineIndependent_vadd` / 引理 `affineIndependent_vadd`

English:
lemma affineIndependent_vadd
  given: {p : ι -> P} {v : V}
  proof: by
  simp +contextual [AffineIndependent, weightedVSub_vadd]

protected alias ⟨AffineIndependent.of_vadd, AffineIndependent.vadd⟩ := affineIndependent_vadd

中文:
引理 affineIndependent_vadd
  条件: {p : ι -> P} {v : V}
  证明: by
  simp +contextual [AffineIndependent, weightedVSub_vadd]

protected alias ⟨AffineIndependent.of_vadd, AffineIndependent.vadd⟩ := affineIndependent_vadd
-/
@[simp] lemma affineIndependent_vadd {p : ι -> P} {v : V} :
    AffineIndependent k (v +ᵥ p) ↔ AffineIndependent k p := by
  simp +contextual [AffineIndependent, weightedVSub_vadd]

protected alias ⟨AffineIndependent.of_vadd, AffineIndependent.vadd⟩ := affineIndependent_vadd

/--
lemma `affineIndependent_smul` / 引理 `affineIndependent_smul`

English:
lemma affineIndependent_smul
  statement: {G : Type*} [Group G] [DistribMulAction G V]
  proof: by
  simp +contextual [AffineIndependent,
    ← smul_comm (α := V) a, ← smul_sum, smul_eq_zero_iff_eq]

protected alias ⟨AffineIndependent.of_smul, AffineIndependent.smul⟩ := affineIndependent_smul

中文:
引理 affineIndependent_smul
  结论: {G : 类型} [Group G] [DistribMulAction G V]
  证明: by
  simp +contextual [AffineIndependent,
    ← smul_comm (α := V) a, ← smul_sum, smul_eq_zero_iff_eq]

protected alias ⟨AffineIndependent.of_smul, AffineIndependent.smul⟩ := affineIndependent_smul
-/
@[simp] lemma affineIndependent_smul {G : Type*} [Group G] [DistribMulAction G V]
    [SMulCommClass G k V] {p : ι -> V} {a : G} :
    AffineIndependent k (a • p) ↔ AffineIndependent k p := by
  simp +contextual [AffineIndependent,
    ← smul_comm (α := V) a, ← smul_sum, smul_eq_zero_iff_eq]

protected alias ⟨AffineIndependent.of_smul, AffineIndependent.smul⟩ := affineIndependent_smul

/--
theorem `affineIndependent_iff_linearIndependent_vsub` / 定理 `affineIndependent_iff_linearIndependent_vsub`

English:
theorem affineIndependent_iff_linearIndependent_vsub
  given: (p : ι -> P) (i1 : ι)
  proof: by
  classical
    constructor
    · intro h
      rw [linearIndependent_iff']
      intro s g hg i hi
      set f : ι -> k := fun x => if hx : x = i1 then -∑ y in s, g y else g ⟨x, hx⟩ with hfdef
      let s2 : Finset ι := insert i1 (s.map (Embedding.subtype _))
      have hfg : forall x : { x // x

中文:
定理 affineIndependent_iff_linearIndependent_vsub
  条件: (p : ι -> P) (i1 : ι)
  证明: by
  classical
    constructor
    · intro h
      rw [linearIndependent_iff']
      intro s g hg i hi
      set f : ι -> k := fun x => if hx : x = i1 then -∑ y in s, g y else g ⟨x, hx⟩ with hfdef
      let s2 : Finset ι := insert i1 (s.map (Embedding.subtype _))
      have hfg : forall x : { x // x

Depends on / 依赖: Classical, Classical.not_not, Embedding, Embedding.subtype, Finset, Finset.notMem_map_subtype_of_not_property, Finset.sum_insert, Finset.sum_subtype_map_embedding, classical, insert, linearIndependent_iff, notMem_map_subtype_of_not_property, not_not, s.map, subtype, sum_insert, sum_subtype_map_embedding
-/
theorem affineIndependent_iff_linearIndependent_vsub (p : ι -> P) (i1 : ι) :
    AffineIndependent k p ↔ LinearIndependent k fun i : { x // x != i1 } => (p i -ᵥ p i1 : V) := by
  classical
    constructor
    · intro h
      rw [linearIndependent_iff']
      intro s g hg i hi
      set f : ι -> k := fun x => if hx : x = i1 then -∑ y in s, g y else g ⟨x, hx⟩ with hfdef
      let s2 : Finset ι := insert i1 (s.map (Embedding.subtype _))
      have hfg : forall x : { x // x != i1 }, g x = f x := by grind
      rw [hfg]
      have hf : ∑ ι in s2, f ι = 0 := by
        rw [Finset.sum_insert
            (Finset.notMem_map_subtype_of_not_property s (Classical.not_not.2 rfl))]; rw [Finset.sum_subtype_map_embedding fun x _ => (hfg x).symm]
        rw [hfdef]
        dsimp only
        rw [dif_pos rfl]
        exact neg_add_cancel _
      have hs2 : s2.weightedVSub p f = (0 : V) := by
        set f2 : ι -> V := fun x => f x • (p x -ᵥ p i1) with hf2def
        set g2 : { x // x != i1 } -> V := fun x => g x • (p x -ᵥ p i1)
        have hf2g2 : forall x : { x // x != i1 }, f2 x = g2 x := by
          simp only [g2, hf2def]
          intro x
          rw [hfg]
        rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero s2 f p hf (p i1)]; rw [Finset.weightedVSubOfPoint_insert]; rw [Finset.weightedVSubOfPoint_apply]; rw [Finset.sum_subtype_map_embedding fun x _ => hf2g2 x]
        exact hg
      exact h s2 f hf hs2 i (Finset.mem_insert_of_mem (Finset.mem_map.2 ⟨i, hi, rfl⟩))
    · intro h
      rw [linearIndependent_iff'] at h
      intro s w hw hs i hi
      rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero s w p hw (p i1)]; rw [←
        s.weightedVSubOfPoint_erase w p i1]; rw [Finset.weightedVSubOfPoint_apply] at hs
      let f : ι -> V := fun i => w i • (p i -ᵥ p i1)
      have hs2 : (∑ i in (s.erase i1).subtype fun i => i != i1, f i) = 0 := by
        rw [← hs]
        convert! Finset.sum_subtype_of_mem f fun x => Finset.ne_of_mem_erase
      have h2 := h ((s.erase i1).subtype fun i => i != i1) (fun x => w x) hs2
      simp_rw [Finset.mem_subtype] at h2
      have h2b : forall i in s, i != i1 -> w i = 0 := fun i his hi =>
        h2 ⟨i, hi⟩ (Finset.mem_erase_of_ne_of_mem hi his)
      exact Finset.eq_zero_of_sum_eq_zero hw h2b i hi

/--
theorem `affineIndependent_set_iff_linearIndependent_vsub` / 定理 `affineIndependent_set_iff_linearIndependent_vsub`

English:
theorem affineIndependent_set_iff_linearIndependent_vsub
  given: {s : Set P} {p₁ : P} (hp₁ : p₁ in s)
  proof: by
  rw [affineIndependent_iff_linearIndependent_vsub k (fun p => p : s -> P) ⟨p₁]; rw [hp₁⟩]
  constructor
  · intro h
    have hv : forall v : (fun p => (p -ᵥ p₁ : V)) '' (s \ {p₁}), (v : V) +ᵥ p₁ in s \ {p₁} := fun v =>
      (vsub_left_injective p₁).mem_set_image.1 ((vadd_vsub (v : V) p₁).symm ▸

中文:
定理 affineIndependent_set_iff_linearIndependent_vsub
  条件: {s : Set P} {p₁ : P} (hp₁ : p₁ in s)
  证明: by
  rw [affineIndependent_iff_linearIndependent_vsub k (fun p => p : s -> P) ⟨p₁]; rw [hp₁⟩]
  constructor
  · intro h
    have hv : forall v : (fun p => (p -ᵥ p₁ : V)) '' (s \ {p₁}), (v : V) +ᵥ p₁ in s \ {p₁} := fun v =>
      (vsub_left_injective p₁).mem_set_image.1 ((vadd_vsub (v : V) p₁).symm ▸

Depends on / 依赖: Eq.symm, Set.mem_of_mem_sdiff, Set.notMem_of_mem_sdiff, Subtype, Subtype.ext_iff, affineIndependent_iff_linearIndependent_vsub, ext_iff, mem_of_mem_sdiff, mem_set_image, notMem_of_mem_sdiff, pi_eq, property, v.property, vadd_vsub, vsub_left_injective
-/
theorem affineIndependent_set_iff_linearIndependent_vsub {s : Set P} {p₁ : P} (hp₁ : p₁ in s) :
    AffineIndependent k (fun p => p : s -> P) ↔
      LinearIndependent k (fun v => v : (fun p => (p -ᵥ p₁ : V)) '' (s \ {p₁}) -> V) := by
  rw [affineIndependent_iff_linearIndependent_vsub k (fun p => p : s -> P) ⟨p₁]; rw [hp₁⟩]
  constructor
  · intro h
    have hv : forall v : (fun p => (p -ᵥ p₁ : V)) '' (s \ {p₁}), (v : V) +ᵥ p₁ in s \ {p₁} := fun v =>
      (vsub_left_injective p₁).mem_set_image.1 ((vadd_vsub (v : V) p₁).symm ▸ v.property)
    let f : (fun p : P => (p -ᵥ p₁ : V)) '' (s \ {p₁}) -> { x : s // x != ⟨p₁, hp₁⟩ } := fun x =>
      ⟨⟨(x : V) +ᵥ p₁, Set.mem_of_mem_sdiff (hv x)⟩, fun hx =>
        Set.notMem_of_mem_sdiff (hv x) (Subtype.ext_iff.1 hx)⟩
    convert!
      h.comp f fun x1 x2 hx =>
        Subtype.ext (vadd_right_cancel p₁ (Subtype.ext_iff.1 (Subtype.ext_iff.1 hx)))
    ext v
    exact (vadd_vsub (v : V) p₁).symm
  · intro h
    let f : { x : s // x != ⟨p₁, hp₁⟩ } -> (fun p : P => (p -ᵥ p₁ : V)) '' (s \ {p₁}) := fun x =>
      ⟨((x : s) : P) -ᵥ p₁, ⟨x, ⟨⟨(x : s).property, fun hx => x.property (Subtype.ext hx)⟩, rfl⟩⟩⟩
    convert!
      h.comp f fun x1 x2 hx => Subtype.ext (Subtype.ext (vsub_left_cancel (Subtype.ext_iff.1 hx)))

/--
theorem `linearIndependent_set_iff_affineIndependent_vadd_union_singleton` / 定理 `linearIndependent_set_iff_affineIndependent_vadd_union_singleton`

English:
theorem linearIndependent_set_iff_affineIndependent_vadd_union_singleton
  statement: {s : Set V}
  proof: by
  rw [affineIndependent_set_iff_linearIndependent_vsub k
      (Set.mem_union_left _ (Set.mem_singleton p₁))]
  have h : (fun p => (p -ᵥ p₁ : V)) '' (({p₁} union (fun v => v +ᵥ p₁) '' s) \ {p₁}) = s := by
    simp_rw [Set.union_sdiff_left, Set.image_sdiff (vsub_left_injective p₁), Set.image_image

中文:
定理 linearIndependent_set_iff_affineIndependent_vadd_union_singleton
  结论: {s : Set V}
  证明: by
  rw [affineIndependent_set_iff_linearIndependent_vsub k
      (Set.mem_union_left _ (Set.mem_singleton p₁))]
  have h : (fun p => (p -ᵥ p₁ : V)) '' (({p₁} union (fun v => v +ᵥ p₁) '' s) \ {p₁}) = s := by
    simp_rw [Set.union_sdiff_left, Set.image_sdiff (vsub_left_injective p₁), Set.image_image

Depends on / 依赖: Set.image_id, Set.image_image, Set.image_sdiff, Set.image_singleton, Set.mem_singleton, Set.mem_union_left, Set.sdiff_singleton_eq_self, Set.union_sdiff_left, affineIndependent_set_iff_linearIndependent_vsub, image_id, image_image, image_sdiff, image_singleton, mem_singleton, mem_union_left, sdiff_singleton_eq_self, simp_rw, union_sdiff_left, vadd_vsub, vsub_left_injective
-/
theorem linearIndependent_set_iff_affineIndependent_vadd_union_singleton {s : Set V}
    (hs : forall v in s, v != (0 : V)) (p₁ : P) : LinearIndependent k (fun v => v : s -> V) ↔
    AffineIndependent k (fun p => p : ({p₁} union (fun v => v +ᵥ p₁) '' s : Set P) -> P) := by
  rw [affineIndependent_set_iff_linearIndependent_vsub k
      (Set.mem_union_left _ (Set.mem_singleton p₁))]
  have h : (fun p => (p -ᵥ p₁ : V)) '' (({p₁} union (fun v => v +ᵥ p₁) '' s) \ {p₁}) = s := by
    simp_rw [Set.union_sdiff_left, Set.image_sdiff (vsub_left_injective p₁), Set.image_image,
      Set.image_singleton, vsub_self, vadd_vsub, Set.image_id']
    exact Set.sdiff_singleton_eq_self fun h => hs 0 h rfl
  rw [h]

/--
theorem `affineIndependent_iff_indicator_eq_of_affineCombination_eq` / 定理 `affineIndependent_iff_indicator_eq_of_affineCombination_eq`

English:
theorem affineIndependent_iff_indicator_eq_of_affineCombination_eq
  given: (p : ι -> P)
  proof: by
  classical
    constructor
    · intro ha s1 s2 w1 w2 hw1 hw2 heq
      ext i
      by_cases hi : i in s1 union s2
      · rw [← sub_eq_zero]
        rw [← Finset.sum_indicator_subset w1 (s1.subset_union_left (s₂ := s2))] at hw1
        rw [← Finset.sum_indicator_subset w2 (s1.subset_union_right

中文:
定理 affineIndependent_iff_indicator_eq_of_affineCombination_eq
  条件: (p : ι -> P)
  证明: by
  classical
    constructor
    · intro ha s1 s2 w1 w2 hw1 hw2 heq
      ext i
      by_cases hi : i in s1 union s2
      · rw [← sub_eq_zero]
        rw [← Finset.sum_indicator_subset w1 (s1.subset_union_left (s₂ := s2))] at hw1
        rw [← Finset.sum_indicator_subset w2 (s1.subset_union_right

Depends on / 依赖: Finset, Finset.affineCombination_indicat, Finset.affineCombination_indicator_subset, Finset.sum_indicator_subset, Set.indicator, affineCombination_indicat, affineCombination_indicator_subset, classical, indicator, s1.subset_union_left, s1.subset_union_right, sub_eq_zero, subset_union_left, subset_union_right, sum_indicator_subset
-/
theorem affineIndependent_iff_indicator_eq_of_affineCombination_eq (p : ι -> P) :
    AffineIndependent k p ↔
      forall (s1 s2 : Finset ι) (w1 w2 : ι -> k),
        ∑ i in s1, w1 i = 1 ->
          ∑ i in s2, w2 i = 1 ->
            s1.affineCombination k p w1 = s2.affineCombination k p w2 ->
              Set.indicator (↑s1) w1 = Set.indicator (↑s2) w2 := by
  classical
    constructor
    · intro ha s1 s2 w1 w2 hw1 hw2 heq
      ext i
      by_cases hi : i in s1 union s2
      · rw [← sub_eq_zero]
        rw [← Finset.sum_indicator_subset w1 (s1.subset_union_left (s₂ := s2))] at hw1
        rw [← Finset.sum_indicator_subset w2 (s1.subset_union_right)] at hw2
        have hws : (∑ i in s1 union s2, (Set.indicator (↑s1) w1 - Set.indicator (↑s2) w2) i) = 0 := by
          simp [hw1, hw2]
        rw [Finset.affineCombination_indicator_subset w1 p (s1.subset_union_left (s₂ := s2))]; rw [Finset.affineCombination_indicator_subset w2 p s1.subset_union_right]; rw [← @vsub_eq_zero_iff_eq V]; rw [Finset.affineCombination_vsub] at heq
        exact ha (s1 union s2) (Set.indicator (↑s1) w1 - Set.indicator (↑s2) w2) hws heq i hi
      · simp_all
    · intro ha s w hw hs i0 hi0
      let w1 : ι -> k := Function.update (Function.const ι 0) i0 1
      have hw1 : ∑ i in s, w1 i = 1 := by
        rw [Finset.sum_update_of_mem hi0]
        simp only [Finset.sum_const_zero, add_zero, const_apply]
      have hw1s : s.affineCombination k p w1 = p i0 :=
        s.affineCombination_of_eq_one_of_eq_zero w1 p hi0 (Function.update_self ..)
          fun _ _ hne => Function.update_of_ne hne ..
      let w2 := w + w1
      have hw2 : ∑ i in s, w2 i = 1 := by
        simp_all only [w2, Pi.add_apply, Finset.sum_add_distrib, zero_add]
      have hw2s : s.affineCombination k p w2 = p i0 := by
        simp_all only [w2, ← Finset.weightedVSub_vadd_affineCombination, zero_vadd]
      replace ha := ha s s w2 w1 hw2 hw1 (hw1s.symm ▸ hw2s)
      have hws : w2 i0 - w1 i0 = 0 := by
        rw [← Finset.mem_coe] at hi0
        rw [← Set.indicator_of_mem hi0 w2]; rw [← Set.indicator_of_mem hi0 w1]; rw [ha]; rw [sub_self]
      simpa [w2] using hws

/--
theorem `affineIndependent_iff_eq_of_fintype_affineCombination_eq` / 定理 `affineIndependent_iff_eq_of_fintype_affineCombination_eq`

English:
theorem affineIndependent_iff_eq_of_fintype_affineCombination_eq
  given: [Fintype ι] (p : ι -> P)
  proof: by
  rw [affineIndependent_iff_indicator_eq_of_affineCombination_eq]
  constructor
  · intro h w1 w2 hw1 hw2 hweq
    simpa only [Set.indicator_univ, Finset.coe_univ] using h _ _ w1 w2 hw1 hw2 hweq
  · intro h s1 s2 w1 w2 hw1 hw2 hweq
    have hw1' : (∑ i, (s1 : Set ι).indicator w1 i) = 1 := by
    

中文:
定理 affineIndependent_iff_eq_of_fintype_affineCombination_eq
  条件: [Fintype ι] (p : ι -> P)
  证明: by
  rw [affineIndependent_iff_indicator_eq_of_affineCombination_eq]
  constructor
  · intro h w1 w2 hw1 hw2 hweq
    simpa only [Set.indicator_univ, Finset.coe_univ] using h _ _ w1 w2 hw1 hw2 hweq
  · intro h s1 s2 w1 w2 hw1 hw2 hweq
    have hw1' : (∑ i, (s1 : Set ι).indicator w1 i) = 1 := by
    

Depends on / 依赖: Finset, Finset.affineCombination_indicator_subs, Finset.coe_univ, Finset.subset_univ, Finset.sum_indicator_subset, Set.indicator_univ, affineCombination_indicator_subs, affineIndependent_iff_indicator_eq_of_affineCombination_eq, coe_univ, indicator, indicator_univ, instIsFiniteMeasure, pi.instIsFiniteMeasure, subset_univ, sum_indicator_subset
-/
theorem affineIndependent_iff_eq_of_fintype_affineCombination_eq [Fintype ι] (p : ι -> P) :
    AffineIndependent k p ↔ forall w1 w2 : ι -> k, ∑ i, w1 i = 1 -> ∑ i, w2 i = 1 ->
    Finset.univ.affineCombination k p w1 = Finset.univ.affineCombination k p w2 -> w1 = w2 := by
  rw [affineIndependent_iff_indicator_eq_of_affineCombination_eq]
  constructor
  · intro h w1 w2 hw1 hw2 hweq
    simpa only [Set.indicator_univ, Finset.coe_univ] using h _ _ w1 w2 hw1 hw2 hweq
  · intro h s1 s2 w1 w2 hw1 hw2 hweq
    have hw1' : (∑ i, (s1 : Set ι).indicator w1 i) = 1 := by
      rwa [Finset.sum_indicator_subset _ (Finset.subset_univ s1)]
    have hw2' : (∑ i, (s2 : Set ι).indicator w2 i) = 1 := by
      rwa [Finset.sum_indicator_subset _ (Finset.subset_univ s2)]
    rw [Finset.affineCombination_indicator_subset w1 p (Finset.subset_univ s1)]; rw [Finset.affineCombination_indicator_subset w2 p (Finset.subset_univ s2)] at hweq
    exact h _ _ hw1' hw2' hweq

/--
theorem `LinearIndependent.affineIndependent` / 定理 `LinearIndependent.affineIndependent`

English:
theorem LinearIndependent.affineIndependent
  proof: by
  intro s w hw0 hwv i hi
  rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ _ _ hw0 0]; rw [Finset.weightedVSubOfPoint_apply] at hwv
  simp only [vsub_eq_sub, sub_zero] at hwv
  exact linearIndependent_iff'.mp hv s w hwv i hi

中文:
定理 LinearIndependent.affineIndependent
  证明: by
  intro s w hw0 hwv i hi
  rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ _ _ hw0 0]; rw [Finset.weightedVSubOfPoint_apply] at hwv
  simp only [vsub_eq_sub, sub_zero] at hwv
  exact linearIndependent_iff'.mp hv s w hwv i hi

Depends on / 依赖: Finset, Finset.weightedVSubOfPoint_apply, Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero, linearIndependent_iff, sub_zero, vsub_eq_sub, weightedVSubOfPoint_apply, weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero
-/
theorem LinearIndependent.affineIndependent
    {v : ι -> V} (hv : LinearIndependent k v) : AffineIndependent k v := by
  intro s w hw0 hwv i hi
  rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ _ _ hw0 0]; rw [Finset.weightedVSubOfPoint_apply] at hwv
  simp only [vsub_eq_sub, sub_zero] at hwv
  exact linearIndependent_iff'.mp hv s w hwv i hi

variable {k}

set_option backward.isDefEq.respectTransparency false in
/--
theorem `AffineIndependent.units_lineMap` / 定理 `AffineIndependent.units_lineMap`

English:
theorem AffineIndependent.units_lineMap
  statement: {p : ι -> P} (hp : AffineIndependent k p) (j : ι)
  proof: by
  rw [affineIndependent_iff_linearIndependent_vsub k _ j] at hp ⊢
  simp only [AffineMap.lineMap_vsub_left, AffineMap.coe_const, AffineMap.lineMap_same, const_apply]
  exact hp.units_smul fun i => w i

中文:
定理 AffineIndependent.units_lineMap
  结论: {p : ι -> P} (hp : AffineIndependent k p) (j : ι)
  证明: by
  rw [affineIndependent_iff_linearIndependent_vsub k _ j] at hp ⊢
  simp only [AffineMap.lineMap_vsub_left, AffineMap.coe_const, AffineMap.lineMap_same, const_apply]
  exact hp.units_smul fun i => w i

Depends on / 依赖: AffineMap, AffineMap.coe_const, AffineMap.lineMap_same, AffineMap.lineMap_vsub_left, affineIndependent_iff_linearIndependent_vsub, coe_const, const_apply, hp.units_smul, lineMap_same, lineMap_vsub_left, units_smul
-/
theorem AffineIndependent.units_lineMap {p : ι -> P} (hp : AffineIndependent k p) (j : ι)
    (w : ι -> Units k) : AffineIndependent k fun i => AffineMap.lineMap (p j) (p i) (w i : k) := by
  rw [affineIndependent_iff_linearIndependent_vsub k _ j] at hp ⊢
  simp only [AffineMap.lineMap_vsub_left, AffineMap.coe_const, AffineMap.lineMap_same, const_apply]
  exact hp.units_smul fun i => w i

/--
theorem `AffineIndependent.indicator_eq_of_affineCombination_eq` / 定理 `AffineIndependent.indicator_eq_of_affineCombination_eq`

English:
theorem AffineIndependent.indicator_eq_of_affineCombination_eq
  statement: {p : ι -> P}
  proof: (affineIndependent_iff_indicator_eq_of_affineCombination_eq k p).1 ha s₁ s₂ w₁ w₂ hw₁ hw₂ h

中文:
定理 AffineIndependent.indicator_eq_of_affineCombination_eq
  结论: {p : ι -> P}
  证明: (affineIndependent_iff_indicator_eq_of_affineCombination_eq k p).1 ha s₁ s₂ w₁ w₂ hw₁ hw₂ h

Depends on / 依赖: affineIndependent_iff_indicator_eq_of_affineCombination_eq, instIsProbabilityMeasure, pi.instIsProbabilityMeasure
-/
theorem AffineIndependent.indicator_eq_of_affineCombination_eq {p : ι -> P}
    (ha : AffineIndependent k p) (s₁ s₂ : Finset ι) (w₁ w₂ : ι -> k) (hw₁ : ∑ i in s₁, w₁ i = 1)
    (hw₂ : ∑ i in s₂, w₂ i = 1) (h : s₁.affineCombination k p w₁ = s₂.affineCombination k p w₂) :
    Set.indicator (↑s₁) w₁ = Set.indicator (↑s₂) w₂ :=
  (affineIndependent_iff_indicator_eq_of_affineCombination_eq k p).1 ha s₁ s₂ w₁ w₂ hw₁ hw₂ h

/--
lemma `AffineIndependent.affineCombination_eq_iff_eq` / 引理 `AffineIndependent.affineCombination_eq_iff_eq`

English:
lemma AffineIndependent.affineCombination_eq_iff_eq
  statement: {p : ι -> P} (ha : AffineIndependent k p)
  proof: by
  refine ⟨fun h => ?_, fun h => s.affineCombination_congr h fun _ _ => rfl⟩
  have hi := ha.indicator_eq_of_affineCombination_eq _ _ _ _ hw₁ hw₂ h
  intro i hs
  suffices Set.indicator s w₁ i = Set.indicator s w₂ i by simpa [hs] using this
  simp [hi]

中文:
引理 AffineIndependent.affineCombination_eq_iff_eq
  结论: {p : ι -> P} (ha : AffineIndependent k p)
  证明: by
  refine ⟨fun h => ?_, fun h => s.affineCombination_congr h fun _ _ => rfl⟩
  have hi := ha.indicator_eq_of_affineCombination_eq _ _ _ _ hw₁ hw₂ h
  intro i hs
  suffices Set.indicator s w₁ i = Set.indicator s w₂ i by simpa [hs] using this
  simp [hi]

Depends on / 依赖: Set.indicator, affineCombination_congr, ha.indicator_eq_of_affineCombination_eq, indicator, indicator_eq_of_affineCombination_eq, s.affineCombination_congr
-/
lemma AffineIndependent.affineCombination_eq_iff_eq {p : ι -> P} (ha : AffineIndependent k p)
    {w₁ w₂ : ι -> k} {s : Finset ι} (hw₁ : ∑ i in s, w₁ i = 1) (hw₂ : ∑ i in s, w₂ i = 1) :
    s.affineCombination k p w₁ = s.affineCombination k p w₂ ↔ forall i in s, w₁ i = w₂ i := by
  refine ⟨fun h => ?_, fun h => s.affineCombination_congr h fun _ _ => rfl⟩
  have hi := ha.indicator_eq_of_affineCombination_eq _ _ _ _ hw₁ hw₂ h
  intro i hs
  suffices Set.indicator s w₁ i = Set.indicator s w₂ i by simpa [hs] using this
  simp [hi]

/--
theorem `AffineIndependent.injective` / 定理 `AffineIndependent.injective`

English:
theorem AffineIndependent.injective
  statement: [Nontrivial k] {p : ι -> P}
  proof: by
  intro i j hij
  rw [affineIndependent_iff_linearIndependent_vsub _ _ j] at ha
  by_contra hij'
  refine ha.ne_zero ⟨i, hij'⟩ (vsub_eq_zero_iff_eq.mpr ?_)
  simp_all only [ne_eq]

中文:
定理 AffineIndependent.injective
  结论: [Nontrivial k] {p : ι -> P}
  证明: by
  intro i j hij
  rw [affineIndependent_iff_linearIndependent_vsub _ _ j] at ha
  by_contra hij'
  refine ha.ne_zero ⟨i, hij'⟩ (vsub_eq_zero_iff_eq.mpr ?_)
  simp_all only [ne_eq]
-/
protected theorem AffineIndependent.injective [Nontrivial k] {p : ι -> P}
    (ha : AffineIndependent k p) : Function.Injective p := by
  intro i j hij
  rw [affineIndependent_iff_linearIndependent_vsub _ _ j] at ha
  by_contra hij'
  refine ha.ne_zero ⟨i, hij'⟩ (vsub_eq_zero_iff_eq.mpr ?_)
  simp_all only [ne_eq]

/--
theorem `AffineIndependent.comp_embedding` / 定理 `AffineIndependent.comp_embedding`

English:
theorem AffineIndependent.comp_embedding
  statement: {ι2 : Type*} (f : ι2 ↪ ι) {p : ι -> P}
  proof: by
  classical
    intro fs w hw hs i0 hi0
    let fs' := fs.map f
    let w' i := if h : exists i2, f i2 = i then w h.choose else 0
    have hw' : forall i2 : ι2, w' (f i2) = w i2 := by
      intro i2
      have h : exists i : ι2, f i = f i2 := ⟨i2, rfl⟩
      have hs : h.choose = i2 := f.injective

中文:
定理 AffineIndependent.comp_embedding
  结论: {ι2 : 类型} (f : ι2 ↪ ι) {p : ι -> P}
  证明: by
  classical
    intro fs w hw hs i0 hi0
    let fs' := fs.map f
    let w' i := if h : exists i2, f i2 = i then w h.choose else 0
    have hw' : forall i2 : ι2, w' (f i2) = w i2 := by
      intro i2
      have h : exists i : ι2, f i = f i2 := ⟨i2, rfl⟩
      have hs : h.choose = i2 := f.injective

Depends on / 依赖: Finset, Finset.sum_map, Finset.weightedVSub_map, choose_spec, classical, dif_pos, f.injective, fs.map, h.choose, h.choose_spec, injective, simp_rw, sum_map, weightedVSub, weightedVSub_map
-/
theorem AffineIndependent.comp_embedding {ι2 : Type*} (f : ι2 ↪ ι) {p : ι -> P}
    (ha : AffineIndependent k p) : AffineIndependent k (p ∘ f) := by
  classical
    intro fs w hw hs i0 hi0
    let fs' := fs.map f
    let w' i := if h : exists i2, f i2 = i then w h.choose else 0
    have hw' : forall i2 : ι2, w' (f i2) = w i2 := by
      intro i2
      have h : exists i : ι2, f i = f i2 := ⟨i2, rfl⟩
      have hs : h.choose = i2 := f.injective h.choose_spec
      simp_rw [w', dif_pos h, hs]
    have hw's : ∑ i in fs', w' i = 0 := by
      rw [← hw]; rw [Finset.sum_map]
      simp [hw']
    have hs' : fs'.weightedVSub p w' = (0 : V) := by
      rw [← hs]; rw [Finset.weightedVSub_map]
      congr with i
      simp_all only [comp_apply]
    rw [← ha fs' w' hw's hs' (f i0) ((Finset.mem_map' _).2 hi0)]; rw [hw']

/--
theorem `AffineIndependent.subtype` / 定理 `AffineIndependent.subtype`

English:
theorem AffineIndependent.subtype
  given: {p : ι -> P} (ha : AffineIndependent k p) (s : Set ι)
  proof: ha.comp_embedding (Embedding.subtype _)

中文:
定理 AffineIndependent.subtype
  条件: {p : ι -> P} (ha : AffineIndependent k p) (s : Set ι)
  证明: ha.comp_embedding (Embedding.subtype _)

Depends on / 依赖: pi.sigmaFinite, sigmaFinite
-/
protected theorem AffineIndependent.subtype {p : ι -> P} (ha : AffineIndependent k p) (s : Set ι) :
    AffineIndependent k fun i : s => p i :=
  ha.comp_embedding (Embedding.subtype _)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `AffineIndependent.range` / 定理 `AffineIndependent.range`

English:
theorem AffineIndependent.range
  given: {p : ι -> P} (ha : AffineIndependent k p)
  proof: by
  let f : Set.range p -> ι := fun x => x.property.choose
  have hf : forall x, p (f x) = x := fun x => x.property.choose_spec
  let fe : Set.range p ↪ ι := ⟨f, fun x₁ x₂ he => Subtype.ext (hf x₁ ▸ hf x₂ ▸ he ▸ rfl)⟩
  convert! ha.comp_embedding fe
  ext
  simp [fe, hf]

中文:
定理 AffineIndependent.range
  条件: {p : ι -> P} (ha : AffineIndependent k p)
  证明: by
  let f : Set.range p -> ι := fun x => x.property.choose
  have hf : forall x, p (f x) = x := fun x => x.property.choose_spec
  let fe : Set.range p ↪ ι := ⟨f, fun x₁ x₂ he => Subtype.ext (hf x₁ ▸ hf x₂ ▸ he ▸ rfl)⟩
  convert! ha.comp_embedding fe
  ext
  simp [fe, hf]
-/
protected theorem AffineIndependent.range {p : ι -> P} (ha : AffineIndependent k p) :
    AffineIndependent k (fun x => x : Set.range p -> P) := by
  let f : Set.range p -> ι := fun x => x.property.choose
  have hf : forall x, p (f x) = x := fun x => x.property.choose_spec
  let fe : Set.range p ↪ ι := ⟨f, fun x₁ x₂ he => Subtype.ext (hf x₁ ▸ hf x₂ ▸ he ▸ rfl)⟩
  convert! ha.comp_embedding fe
  ext
  simp [fe, hf]

/--
theorem `affineIndependent_equiv` / 定理 `affineIndependent_equiv`

English:
theorem affineIndependent_equiv
  given: {ι' : Type*} (e : ι ≃ ι') {p : ι' -> P}
  proof: by
  refine ⟨?_, AffineIndependent.comp_embedding e.toEmbedding⟩
  intro h
  have : p = p ∘ e ∘ e.symm.toEmbedding := by
    ext
    simp
  rw [this]
  exact h.comp_embedding e.symm.toEmbedding

中文:
定理 affineIndependent_equiv
  条件: {ι' : 类型} (e : ι ≃ ι') {p : ι' -> P}
  证明: by
  refine ⟨?_, AffineIndependent.comp_embedding e.toEmbedding⟩
  intro h
  have : p = p ∘ e ∘ e.symm.toEmbedding := by
    ext
    simp
  rw [this]
  exact h.comp_embedding e.symm.toEmbedding

Depends on / 依赖: AffineIndependent, AffineIndependent.comp_embedding, comp_embedding, e.symm.toEmbedding, e.toEmbedding, h.comp_embedding, toEmbedding
-/
theorem affineIndependent_equiv {ι' : Type*} (e : ι ≃ ι') {p : ι' -> P} :
    AffineIndependent k (p ∘ e) ↔ AffineIndependent k p := by
  refine ⟨?_, AffineIndependent.comp_embedding e.toEmbedding⟩
  intro h
  have : p = p ∘ e ∘ e.symm.toEmbedding := by
    ext
    simp
  rw [this]
  exact h.comp_embedding e.symm.toEmbedding

/--
theorem `AffineIndependent.comm_left` / 定理 `AffineIndependent.comm_left`

English:
theorem AffineIndependent.comm_left
  given: {p₁ p₂ p₃ : P} (h : AffineIndependent k ![p₁, p₂, p₃])
  proof: by
  rw [← affineIndependent_equiv (Equiv.swap 0 1)]
  convert! h using 1
  ext x
  fin_cases x <;> rfl

中文:
定理 AffineIndependent.comm_left
  条件: {p₁ p₂ p₃ : P} (h : AffineIndependent k ![p₁, p₂, p₃])
  证明: by
  rw [← affineIndependent_equiv (Equiv.swap 0 1)]
  convert! h using 1
  ext x
  fin_cases x <;> rfl

Depends on / 依赖: Equiv.swap, affineIndependent_equiv, convert, fin_cases
-/
theorem AffineIndependent.comm_left {p₁ p₂ p₃ : P} (h : AffineIndependent k ![p₁, p₂, p₃]) :
    AffineIndependent k ![p₂, p₁, p₃] := by
  rw [← affineIndependent_equiv (Equiv.swap 0 1)]
  convert! h using 1
  ext x
  fin_cases x <;> rfl

/--
theorem `AffineIndependent.comm_right` / 定理 `AffineIndependent.comm_right`

English:
theorem AffineIndependent.comm_right
  given: {p₁ p₂ p₃ : P} (h : AffineIndependent k ![p₁, p₂, p₃])
  proof: by
  rw [← affineIndependent_equiv (Equiv.swap 1 2)]
  convert! h using 1
  ext x
  fin_cases x <;> rfl

中文:
定理 AffineIndependent.comm_right
  条件: {p₁ p₂ p₃ : P} (h : AffineIndependent k ![p₁, p₂, p₃])
  证明: by
  rw [← affineIndependent_equiv (Equiv.swap 1 2)]
  convert! h using 1
  ext x
  fin_cases x <;> rfl

Depends on / 依赖: Equiv.swap, affineIndependent_equiv, convert, fin_cases
-/
theorem AffineIndependent.comm_right {p₁ p₂ p₃ : P} (h : AffineIndependent k ![p₁, p₂, p₃]) :
    AffineIndependent k ![p₁, p₃, p₂] := by
  rw [← affineIndependent_equiv (Equiv.swap 1 2)]
  convert! h using 1
  ext x
  fin_cases x <;> rfl

/--
theorem `AffineIndependent.reverse_of_three` / 定理 `AffineIndependent.reverse_of_three`

English:
theorem AffineIndependent.reverse_of_three
  given: {p₁ p₂ p₃ : P} (h : AffineIndependent k ![p₁, p₂, p₃])
  proof: by
  rw [← affineIndependent_equiv (Equiv.swap 0 2)]
  convert! h using 1
  ext x
  fin_cases x <;> rfl

中文:
定理 AffineIndependent.reverse_of_three
  条件: {p₁ p₂ p₃ : P} (h : AffineIndependent k ![p₁, p₂, p₃])
  证明: by
  rw [← affineIndependent_equiv (Equiv.swap 0 2)]
  convert! h using 1
  ext x
  fin_cases x <;> rfl

Depends on / 依赖: Equiv.swap, affineIndependent_equiv, convert, fin_cases
-/
theorem AffineIndependent.reverse_of_three {p₁ p₂ p₃ : P} (h : AffineIndependent k ![p₁, p₂, p₃]) :
    AffineIndependent k ![p₃, p₂, p₁] := by
  rw [← affineIndependent_equiv (Equiv.swap 0 2)]
  convert! h using 1
  ext x
  fin_cases x <;> rfl

/--
theorem `AffineIndependent.mono` / 定理 `AffineIndependent.mono`

English:
theorem AffineIndependent.mono
  statement: {s t : Set P}
  proof: ha.comp_embedding (s.embeddingOfSubset t hs)

中文:
定理 AffineIndependent.mono
  结论: {s t : Set P}
  证明: ha.comp_embedding (s.embeddingOfSubset t hs)
-/
protected theorem AffineIndependent.mono {s t : Set P}
    (ha : AffineIndependent k (fun x => x : t -> P)) (hs : s subseteq t) :
    AffineIndependent k (fun x => x : s -> P) :=
  ha.comp_embedding (s.embeddingOfSubset t hs)

/--
theorem `AffineIndependent.of_set_of_injective` / 定理 `AffineIndependent.of_set_of_injective`

English:
theorem AffineIndependent.of_set_of_injective
  statement: {p : ι -> P}
  proof: ha.comp_embedding
    (⟨fun i => ⟨p i, Set.mem_range_self _⟩, fun _ _ h => hi (Subtype.mk_eq_mk.1 h)⟩ :
      ι ↪ Set.range p)

中文:
定理 AffineIndependent.of_set_of_injective
  结论: {p : ι -> P}
  证明: ha.comp_embedding
    (⟨fun i => ⟨p i, Set.mem_range_self _⟩, fun _ _ h => hi (Subtype.mk_eq_mk.1 h)⟩ :
      ι ↪ Set.range p)

Depends on / 依赖: Set.mem_range_self, Set.range, Subtype, Subtype.mk_eq_mk, comp_embedding, ha.comp_embedding, mem_range_self, mk_eq_mk
-/
theorem AffineIndependent.of_set_of_injective {p : ι -> P}
    (ha : AffineIndependent k (fun x => x : Set.range p -> P)) (hi : Function.Injective p) :
    AffineIndependent k p :=
  ha.comp_embedding
    (⟨fun i => ⟨p i, Set.mem_range_self _⟩, fun _ _ h => hi (Subtype.mk_eq_mk.1 h)⟩ :
      ι ↪ Set.range p)

/--
lemma `AffineIndependent.eq_zero_of_affineCombination_mem_affineSpan` / 引理 `AffineIndependent.eq_zero_of_affineCombination_mem_affineSpan`

English:
lemma AffineIndependent.eq_zero_of_affineCombination_mem_affineSpan
  statement: {p : ι -> P}
  proof: by
  obtain ⟨fs', w', hfs's, hw', he⟩ := eq_affineCombination_of_mem_affineSpan_image hm
  have hi' : (fs : Set ι).indicator w i = 0 := by
    rw [ha.indicator_eq_of_affineCombination_eq fs fs' w w' hw hw' he]
    exact Set.indicator_of_notMem (Set.notMem_subset hfs's his) w'
  rw [Set.indicator_app

中文:
引理 AffineIndependent.eq_zero_of_affineCombination_mem_affineSpan
  结论: {p : ι -> P}
  证明: by
  obtain ⟨fs', w', hfs's, hw', he⟩ := eq_affineCombination_of_mem_affineSpan_image hm
  have hi' : (fs : Set ι).indicator w i = 0 := by
    rw [ha.indicator_eq_of_affineCombination_eq fs fs' w w' hw hw' he]
    exact Set.indicator_of_notMem (Set.notMem_subset hfs's his) w'
  rw [Set.indicator_app

Depends on / 依赖: Finset, Finset.mem_coe, Set.indicator_apply_eq_zero, Set.indicator_of_notMem, Set.notMem_subset, eq_affineCombination_of_mem_affineSpan_image, ha.indicator_eq_of_affineCombination_eq, indicator, indicator_apply_eq_zero, indicator_eq_of_affineCombination_eq, indicator_of_notMem, mem_coe, notMem_subset
-/
lemma AffineIndependent.eq_zero_of_affineCombination_mem_affineSpan {p : ι -> P}
    (ha : AffineIndependent k p) {fs : Finset ι} {w : ι -> k} (hw : ∑ i in fs, w i = 1) {s : Set ι}
    (hm : fs.affineCombination k p w in affineSpan k (p '' s)) {i : ι} (hifs : i in fs)
    (his : i ∉ s) : w i = 0 := by
  obtain ⟨fs', w', hfs's, hw', he⟩ := eq_affineCombination_of_mem_affineSpan_image hm
  have hi' : (fs : Set ι).indicator w i = 0 := by
    rw [ha.indicator_eq_of_affineCombination_eq fs fs' w w' hw hw' he]
    exact Set.indicator_of_notMem (Set.notMem_subset hfs's his) w'
  rw [Set.indicator_apply_eq_zero] at hi'
  exact hi' (Finset.mem_coe.2 hifs)

/--
lemma `AffineIndependent.indicator_extend_eq_of_affineCombination_comp_embedding_eq` / 引理 `AffineIndependent.indicator_extend_eq_of_affineCombination_comp_embedding_eq`

English:
lemma AffineIndependent.indicator_extend_eq_of_affineCombination_comp_embedding_eq
  statement: {ι₂ : Type*}
  proof: by
  have hw₂e : extend e w₂ 0 ∘ e = w₂ := extend_comp e.injective _ _
  rw [← hw₂e]; rw [← affineCombination_map] at h
  refine (ha.indicator_eq_of_affineCombination_eq s₁ (s₂.map e) _ _ hw₁ ?_ h.symm).symm
  rw [sum_map]
  convert! hw₂ with i hi
  exact e.injective.extend_apply _ _ _

中文:
引理 AffineIndependent.indicator_extend_eq_of_affineCombination_comp_embedding_eq
  结论: {ι₂ : 类型}
  证明: by
  have hw₂e : extend e w₂ 0 ∘ e = w₂ := extend_comp e.injective _ _
  rw [← hw₂e]; rw [← affineCombination_map] at h
  refine (ha.indicator_eq_of_affineCombination_eq s₁ (s₂.map e) _ _ hw₁ ?_ h.symm).symm
  rw [sum_map]
  convert! hw₂ with i hi
  exact e.injective.extend_apply _ _ _

Depends on / 依赖: affineCombination_map, convert, e.injective, e.injective.extend_apply, extend, extend_apply, extend_comp, h.symm, ha.indicator_eq_of_affineCombination_eq, indicator_eq_of_affineCombination_eq, injective, sum_map
-/
lemma AffineIndependent.indicator_extend_eq_of_affineCombination_comp_embedding_eq {ι₂ : Type*}
    {p : ι -> P} (ha : AffineIndependent k p) {s₁ : Finset ι} {s₂ : Finset ι₂} {w₁ : ι -> k}
    {w₂ : ι₂ -> k} (hw₁ : ∑ i in s₁, w₁ i = 1) (hw₂ : ∑ i in s₂, w₂ i = 1) (e : ι₂ ↪ ι)
    (h : s₂.affineCombination k (p ∘ e) w₂ = s₁.affineCombination k p w₁) :
    Set.indicator (s₂.map e) (extend e w₂ 0) = Set.indicator s₁ w₁ := by
  have hw₂e : extend e w₂ 0 ∘ e = w₂ := extend_comp e.injective _ _
  rw [← hw₂e]; rw [← affineCombination_map] at h
  refine (ha.indicator_eq_of_affineCombination_eq s₁ (s₂.map e) _ _ hw₁ ?_ h.symm).symm
  rw [sum_map]
  convert! hw₂ with i hi
  exact e.injective.extend_apply _ _ _

/--
lemma `AffineIndependent.indicator_extend_eq_of_affineCombination_comp_embedding_eq_of_fintype` / 引理 `AffineIndependent.indicator_extend_eq_of_affineCombination_comp_embedding_eq_of_fintype`

English:
lemma AffineIndependent.indicator_extend_eq_of_affineCombination_comp_embedding_eq_of_fintype
  proof: by
  simpa using ha.indicator_extend_eq_of_affineCombination_comp_embedding_eq hw₁ hw₂ e h

中文:
引理 AffineIndependent.indicator_extend_eq_of_affineCombination_comp_embedding_eq_of_fintype
  证明: by
  simpa using ha.indicator_extend_eq_of_affineCombination_comp_embedding_eq hw₁ hw₂ e h

Depends on / 依赖: ha.indicator_extend_eq_of_affineCombination_comp_embedding_eq, indicator_extend_eq_of_affineCombination_comp_embedding_eq
-/
lemma AffineIndependent.indicator_extend_eq_of_affineCombination_comp_embedding_eq_of_fintype
    [Fintype ι] {ι₂ : Type*} [Fintype ι₂] {p : ι -> P} (ha : AffineIndependent k p) {w₁ : ι -> k}
    {w₂ : ι₂ -> k} (hw₁ : ∑ i, w₁ i = 1) (hw₂ : ∑ i, w₂ i = 1) (e : ι₂ ↪ ι)
    (h : Finset.univ.affineCombination k (p ∘ e) w₂ = Finset.univ.affineCombination k p w₁) :
    Set.indicator (Set.range e) (extend e w₂ 0) = w₁ := by
  simpa using ha.indicator_extend_eq_of_affineCombination_comp_embedding_eq hw₁ hw₂ e h

section Composition

variable {V₂ P₂ : Type*} [AddCommGroup V₂] [Module k V₂] [AffineSpace V₂ P₂]

/--
theorem `AffineIndependent.of_comp` / 定理 `AffineIndependent.of_comp`

English:
theorem AffineIndependent.of_comp
  given: {p : ι -> P} (f : P ->ᵃ[k] P₂) (hai : AffineIndependent k (f ∘ p))
  proof: by
  rcases isEmpty_or_nonempty ι with h | h
  · apply affineIndependent_of_subsingleton
  obtain ⟨i⟩ := h
  rw [affineIndependent_iff_linearIndependent_vsub k p i]
  simp_rw [affineIndependent_iff_linearIndependent_vsub k (f ∘ p) i, Function.comp_apply, ←
    f.linearMap_vsub] at hai
  exact Linear

中文:
定理 AffineIndependent.of_comp
  条件: {p : ι -> P} (f : P ->ᵃ[k] P₂) (hai : AffineIndependent k (f ∘ p))
  证明: by
  rcases isEmpty_or_nonempty ι with h | h
  · apply affineIndependent_of_subsingleton
  obtain ⟨i⟩ := h
  rw [affineIndependent_iff_linearIndependent_vsub k p i]
  simp_rw [affineIndependent_iff_linearIndependent_vsub k (f ∘ p) i, Function.comp_apply, ←
    f.linearMap_vsub] at hai
  exact Linear

Depends on / 依赖: Function, Function.comp_apply, LinearIndependent, LinearIndependent.of_comp, affineIndependent_iff_linearIndependent_vsub, affineIndependent_of_subsingleton, comp_apply, f.linear, f.linearMap_vsub, isEmpty_or_nonempty, linear, linearMap_vsub, of_comp, simp_rw
-/
theorem AffineIndependent.of_comp {p : ι -> P} (f : P ->ᵃ[k] P₂) (hai : AffineIndependent k (f ∘ p)) :
    AffineIndependent k p := by
  rcases isEmpty_or_nonempty ι with h | h
  · apply affineIndependent_of_subsingleton
  obtain ⟨i⟩ := h
  rw [affineIndependent_iff_linearIndependent_vsub k p i]
  simp_rw [affineIndependent_iff_linearIndependent_vsub k (f ∘ p) i, Function.comp_apply, ←
    f.linearMap_vsub] at hai
  exact LinearIndependent.of_comp f.linear hai

/--
theorem `AffineIndependent.map'` / 定理 `AffineIndependent.map'`

English:
theorem AffineIndependent.map'
  statement: {p : ι -> P} (hai : AffineIndependent k p) (f : P ->ᵃ[k] P₂)
  proof: by
  rcases isEmpty_or_nonempty ι with h | h
  · apply affineIndependent_of_subsingleton
  obtain ⟨i⟩ := h
  rw [affineIndependent_iff_linearIndependent_vsub k p i] at hai
  simp_rw [affineIndependent_iff_linearIndependent_vsub k (f ∘ p) i, Function.comp_apply, ←
    f.linearMap_vsub]
  have hf' : L

中文:
定理 AffineIndependent.map'
  结论: {p : ι -> P} (hai : AffineIndependent k p) (f : P ->ᵃ[k] P₂)
  证明: by
  rcases isEmpty_or_nonempty ι with h | h
  · apply affineIndependent_of_subsingleton
  obtain ⟨i⟩ := h
  rw [affineIndependent_iff_linearIndependent_vsub k p i] at hai
  simp_rw [affineIndependent_iff_linearIndependent_vsub k (f ∘ p) i, Function.comp_apply, ←
    f.linearMap_vsub]
  have hf' : L

Depends on / 依赖: Function, Function.comp_apply, LinearIndependent, LinearIndependent.map, LinearMap, LinearMap.ker, LinearMap.ker_eq_bot, affineIndependent_iff_linearIndependent_vsub, affineIndependent_of_subsingleton, comp_apply, f.linear, f.linearMap_vsub, f.linear_injective_iff, isEmpty_or_nonempty, ker_eq_bot, linear, linearMap_vsub, linear_injective_iff, simp_rw
-/
theorem AffineIndependent.map' {p : ι -> P} (hai : AffineIndependent k p) (f : P ->ᵃ[k] P₂)
    (hf : Function.Injective f) : AffineIndependent k (f ∘ p) := by
  rcases isEmpty_or_nonempty ι with h | h
  · apply affineIndependent_of_subsingleton
  obtain ⟨i⟩ := h
  rw [affineIndependent_iff_linearIndependent_vsub k p i] at hai
  simp_rw [affineIndependent_iff_linearIndependent_vsub k (f ∘ p) i, Function.comp_apply, ←
    f.linearMap_vsub]
  have hf' : LinearMap.ker f.linear = ⊥ := by rwa [LinearMap.ker_eq_bot, f.linear_injective_iff]
  exact LinearIndependent.map' hai f.linear hf'

/--
theorem `AffineMap.affineIndependent_iff` / 定理 `AffineMap.affineIndependent_iff`

English:
theorem AffineMap.affineIndependent_iff
  given: {p : ι -> P} (f : P ->ᵃ[k] P₂) (hf : Function.Injective f)
  proof: ⟨AffineIndependent.of_comp f, fun hai => AffineIndependent.map' hai f hf⟩

中文:
定理 AffineMap.affineIndependent_iff
  条件: {p : ι -> P} (f : P ->ᵃ[k] P₂) (hf : Function.Injective f)
  证明: ⟨AffineIndependent.of_comp f, fun hai => AffineIndependent.map' hai f hf⟩

Depends on / 依赖: AffineIndependent, AffineIndependent.map, AffineIndependent.of_comp, of_comp
-/
theorem AffineMap.affineIndependent_iff {p : ι -> P} (f : P ->ᵃ[k] P₂) (hf : Function.Injective f) :
    AffineIndependent k (f ∘ p) ↔ AffineIndependent k p :=
  ⟨AffineIndependent.of_comp f, fun hai => AffineIndependent.map' hai f hf⟩

/--
theorem `AffineEquiv.affineIndependent_iff` / 定理 `AffineEquiv.affineIndependent_iff`

English:
theorem AffineEquiv.affineIndependent_iff
  given: {p : ι -> P} (e : P ≃ᵃ[k] P₂)
  proof: e.toAffineMap.affineIndependent_iff e.toEquiv.injective

中文:
定理 AffineEquiv.affineIndependent_iff
  条件: {p : ι -> P} (e : P ≃ᵃ[k] P₂)
  证明: e.toAffineMap.affineIndependent_iff e.toEquiv.injective

Depends on / 依赖: affineIndependent_iff, e.toAffineMap.affineIndependent_iff, e.toEquiv.injective, injective, toAffineMap, toEquiv
-/
theorem AffineEquiv.affineIndependent_iff {p : ι -> P} (e : P ≃ᵃ[k] P₂) :
    AffineIndependent k (e ∘ p) ↔ AffineIndependent k p :=
  e.toAffineMap.affineIndependent_iff e.toEquiv.injective

set_option backward.isDefEq.respectTransparency false in
/--
theorem `AffineEquiv.affineIndependent_set_of_eq_iff` / 定理 `AffineEquiv.affineIndependent_set_of_eq_iff`

English:
theorem AffineEquiv.affineIndependent_set_of_eq_iff
  given: {s : Set P} (e : P ≃ᵃ[k] P₂)
  proof: by
  have : e ∘ ((↑) : s -> P) = ((↑) : e '' s -> P₂) ∘ (e : P ≃ P₂).image s := rfl
  simp [← e.affineIndependent_iff, this, affineIndependent_equiv]

中文:
定理 AffineEquiv.affineIndependent_set_of_eq_iff
  条件: {s : Set P} (e : P ≃ᵃ[k] P₂)
  证明: by
  have : e ∘ ((↑) : s -> P) = ((↑) : e '' s -> P₂) ∘ (e : P ≃ P₂).image s := rfl
  simp [← e.affineIndependent_iff, this, affineIndependent_equiv]

Depends on / 依赖: affineIndependent_equiv, affineIndependent_iff, e.affineIndependent_iff
-/
theorem AffineEquiv.affineIndependent_set_of_eq_iff {s : Set P} (e : P ≃ᵃ[k] P₂) :
    AffineIndependent k ((↑) : e '' s -> P₂) ↔ AffineIndependent k ((↑) : s -> P) := by
  have : e ∘ ((↑) : s -> P) = ((↑) : e '' s -> P₂) ∘ (e : P ≃ P₂).image s := rfl
  simp [← e.affineIndependent_iff, this, affineIndependent_equiv]

end Composition

/--
lemma `AffineIndependent.inf_affineSpan_eq_affineSpan_inter` / 引理 `AffineIndependent.inf_affineSpan_eq_affineSpan_inter`

English:
lemma AffineIndependent.inf_affineSpan_eq_affineSpan_inter
  statement: [Nontrivial k] {p : ι -> P}
  proof: by
  classical
  ext p'
  simp_rw [AffineSubspace.mem_inf_iff, Set.image_eq_range, mem_affineSpan_iff_eq_affineCombination,
    ← Finset.eq_affineCombination_subset_iff_eq_affineCombination_subtype]
  constructor
  · rintro ⟨⟨fs₁, hfs₁, w₁, hw₁, rfl⟩, ⟨fs₂, hfs₂, w₂, hw₂, hw₁₂⟩⟩
    rw [affineIndepe

中文:
引理 AffineIndependent.inf_affineSpan_eq_affineSpan_inter
  结论: [Nontrivial k] {p : ι -> P}
  证明: by
  classical
  ext p'
  simp_rw [AffineSubspace.mem_inf_iff, Set.image_eq_range, mem_affineSpan_iff_eq_affineCombination,
    ← Finset.eq_affineCombination_subset_iff_eq_affineCombination_subtype]
  constructor
  · rintro ⟨⟨fs₁, hfs₁, w₁, hw₁, rfl⟩, ⟨fs₂, hfs₂, w₂, hw₂, hw₁₂⟩⟩
    rw [affineIndepe

Depends on / 依赖: AffineSubspace, AffineSubspace.mem_inf_iff, Finset, Finset.eq_affineCombination_subset_iff_eq_affineCombination_subtype, Set.image_eq_range, add_zero, affineIndependent_iff_indicator_eq_of_affineCombination_eq, classical, convert, eq_affineCombination_subset_iff_eq_affineCombination_subtype, eq_comm, image_eq_range, mem_affineSpan_iff_eq_affineCombination, mem_inf_iff, replace, simp_rw, sum_inter_add_sum_sdiff
-/
lemma AffineIndependent.inf_affineSpan_eq_affineSpan_inter [Nontrivial k] {p : ι -> P}
    (ha : AffineIndependent k p) (s₁ s₂ : Set ι) :
    affineSpan k (p '' s₁) ⊓ affineSpan k (p '' s₂) = affineSpan k (p '' (s₁ inter s₂)) := by
  classical
  ext p'
  simp_rw [AffineSubspace.mem_inf_iff, Set.image_eq_range, mem_affineSpan_iff_eq_affineCombination,
    ← Finset.eq_affineCombination_subset_iff_eq_affineCombination_subtype]
  constructor
  · rintro ⟨⟨fs₁, hfs₁, w₁, hw₁, rfl⟩, ⟨fs₂, hfs₂, w₂, hw₂, hw₁₂⟩⟩
    rw [affineIndependent_iff_indicator_eq_of_affineCombination_eq] at ha
    replace ha := ha fs₁ fs₂ w₁ w₂ hw₁ hw₂ hw₁₂
    refine ⟨fs₁ inter fs₂, by grind, w₁, ?_, ?_⟩
    · rw [← hw₁, ← fs₁.sum_inter_add_sum_sdiff fs₂, eq_comm]
      convert! add_zero _
      refine Finset.sum_eq_zero ?_
      intro i hi
      rw [← Set.indicator_of_mem (s := ↑fs₁) (by grind) w₁]; rw [ha]; rw [Set.indicator_of_notMem (by grind)]
    · rw [affineCombination_indicator_subset w₁ p Finset.inter_subset_left]
      refine affineCombination_congr (k := k) (P := P) _ ?_ (fun _ _ => rfl)
      intro i hi
      rw [coe_inter]; rw [← Set.indicator_indicator]; rw [Set.indicator_of_mem (by simpa using hi)]; rw [Set.indicator_apply]
      simp only [mem_coe, left_eq_ite_iff]
      intro hi₂
      rw [← Set.indicator_of_mem (s := ↑fs₁) (by simpa using hi) w₁]; rw [ha]
      simp [hi₂]
  · grind

/--
theorem `AffineIndependent.exists_mem_inter_of_exists_mem_inter_affineSpan` / 定理 `AffineIndependent.exists_mem_inter_of_exists_mem_inter_affineSpan`

English:
theorem AffineIndependent.exists_mem_inter_of_exists_mem_inter_affineSpan
  statement: [Nontrivial k] {p : ι -> P}
  proof: by
  have hp0' : p0 in affineSpan k (p '' s1) ⊓ affineSpan k (p '' s2) := ⟨hp0s1, hp0s2⟩
  rw [ha.inf_affineSpan_eq_affineSpan_inter] at hp0'
  rw [← Set.Nonempty]
  by_contra he
  rw [Set.not_nonempty_iff_eq_empty] at he
  simp [he, AffineSubspace.notMem_bot] at hp0'

中文:
定理 AffineIndependent.exists_mem_inter_of_exists_mem_inter_affineSpan
  结论: [Nontrivial k] {p : ι -> P}
  证明: by
  have hp0' : p0 in affineSpan k (p '' s1) ⊓ affineSpan k (p '' s2) := ⟨hp0s1, hp0s2⟩
  rw [ha.inf_affineSpan_eq_affineSpan_inter] at hp0'
  rw [← Set.Nonempty]
  by_contra he
  rw [Set.not_nonempty_iff_eq_empty] at he
  simp [he, AffineSubspace.notMem_bot] at hp0'

Depends on / 依赖: AffineSubspace, AffineSubspace.notMem_bot, Nonempty, Set.Nonempty, Set.not_nonempty_iff_eq_empty, affineSpan, ha.inf_affineSpan_eq_affineSpan_inter, inf_affineSpan_eq_affineSpan_inter, notMem_bot, not_nonempty_iff_eq_empty
-/
theorem AffineIndependent.exists_mem_inter_of_exists_mem_inter_affineSpan [Nontrivial k] {p : ι -> P}
    (ha : AffineIndependent k p) {s1 s2 : Set ι} {p0 : P} (hp0s1 : p0 in affineSpan k (p '' s1))
    (hp0s2 : p0 in affineSpan k (p '' s2)) : exists i : ι, i in s1 inter s2 := by
  have hp0' : p0 in affineSpan k (p '' s1) ⊓ affineSpan k (p '' s2) := ⟨hp0s1, hp0s2⟩
  rw [ha.inf_affineSpan_eq_affineSpan_inter] at hp0'
  rw [← Set.Nonempty]
  by_contra he
  rw [Set.not_nonempty_iff_eq_empty] at he
  simp [he, AffineSubspace.notMem_bot] at hp0'

/--
theorem `AffineIndependent.affineSpan_disjoint_of_disjoint` / 定理 `AffineIndependent.affineSpan_disjoint_of_disjoint`

English:
theorem AffineIndependent.affineSpan_disjoint_of_disjoint
  statement: [Nontrivial k] {p : ι -> P}
  proof: by
  refine Set.disjoint_left.2 fun p0 hp0s1 hp0s2 => ?_
  obtain ⟨i, hi⟩ := ha.exists_mem_inter_of_exists_mem_inter_affineSpan hp0s1 hp0s2
  exact Set.disjoint_iff.1 hd hi

中文:
定理 AffineIndependent.affineSpan_disjoint_of_disjoint
  结论: [Nontrivial k] {p : ι -> P}
  证明: by
  refine Set.disjoint_left.2 fun p0 hp0s1 hp0s2 => ?_
  obtain ⟨i, hi⟩ := ha.exists_mem_inter_of_exists_mem_inter_affineSpan hp0s1 hp0s2
  exact Set.disjoint_iff.1 hd hi

Depends on / 依赖: Set.disjoint_iff, Set.disjoint_left, disjoint_iff, disjoint_left, exists_mem_inter_of_exists_mem_inter_affineSpan, ha.exists_mem_inter_of_exists_mem_inter_affineSpan
-/
theorem AffineIndependent.affineSpan_disjoint_of_disjoint [Nontrivial k] {p : ι -> P}
    (ha : AffineIndependent k p) {s1 s2 : Set ι} (hd : Disjoint s1 s2) :
    Disjoint (affineSpan k (p '' s1) : Set P) (affineSpan k (p '' s2)) := by
  refine Set.disjoint_left.2 fun p0 hp0s1 hp0s2 => ?_
  obtain ⟨i, hi⟩ := ha.exists_mem_inter_of_exists_mem_inter_affineSpan hp0s1 hp0s2
  exact Set.disjoint_iff.1 hd hi

/-- If a family is affinely independent, a point in the family is in
the span of some of the points given by a subset of the index type if
and only if that point's index is in the subset, if the underlying
ring is nontrivial. -/
@[simp]
/--
theorem `AffineIndependent.mem_affineSpan_iff` / 定理 `AffineIndependent.mem_affineSpan_iff`

English:
theorem AffineIndependent.mem_affineSpan_iff
  statement: [Nontrivial k] {p : ι -> P}
  proof: by
  constructor
  · intro hs
    have h :=
      AffineIndependent.exists_mem_inter_of_exists_mem_inter_affineSpan ha hs
        (mem_affineSpan k (Set.mem_image_of_mem _ (Set.mem_singleton _)))
    rwa [← Set.nonempty_def, Set.inter_singleton_nonempty] at h
  · exact fun h => mem_affineSpan k (Set

中文:
定理 AffineIndependent.mem_affineSpan_iff
  结论: [Nontrivial k] {p : ι -> P}
  证明: by
  constructor
  · intro hs
    have h :=
      AffineIndependent.exists_mem_inter_of_exists_mem_inter_affineSpan ha hs
        (mem_affineSpan k (Set.mem_image_of_mem _ (Set.mem_singleton _)))
    rwa [← Set.nonempty_def, Set.inter_singleton_nonempty] at h
  · exact fun h => mem_affineSpan k (Set
-/
protected theorem AffineIndependent.mem_affineSpan_iff [Nontrivial k] {p : ι -> P}
    (ha : AffineIndependent k p) (i : ι) (s : Set ι) : p i in affineSpan k (p '' s) ↔ i in s := by
  constructor
  · intro hs
    have h :=
      AffineIndependent.exists_mem_inter_of_exists_mem_inter_affineSpan ha hs
        (mem_affineSpan k (Set.mem_image_of_mem _ (Set.mem_singleton _)))
    rwa [← Set.nonempty_def, Set.inter_singleton_nonempty] at h
  · exact fun h => mem_affineSpan k (Set.mem_image_of_mem p h)

/--
theorem `AffineIndependent.notMem_affineSpan_sdiff` / 定理 `AffineIndependent.notMem_affineSpan_sdiff`

English:
theorem AffineIndependent.notMem_affineSpan_sdiff
  statement: [Nontrivial k] {p : ι -> P}
  proof: by
  simp [ha]

@[deprecated (since := "2026-06-03")]
alias AffineIndependent.notMem_affineSpan_diff := AffineIndependent.notMem_affineSpan_sdiff

中文:
定理 AffineIndependent.notMem_affineSpan_sdiff
  结论: [Nontrivial k] {p : ι -> P}
  证明: by
  simp [ha]

@[deprecated (since := "2026-06-03")]
alias AffineIndependent.notMem_affineSpan_diff := AffineIndependent.notMem_affineSpan_sdiff
-/
theorem AffineIndependent.notMem_affineSpan_sdiff [Nontrivial k] {p : ι -> P}
    (ha : AffineIndependent k p) (i : ι) (s : Set ι) : p i ∉ affineSpan k (p '' (s \ {i})) := by
  simp [ha]

@[deprecated (since := "2026-06-03")]
alias AffineIndependent.notMem_affineSpan_diff := AffineIndependent.notMem_affineSpan_sdiff

/--
lemma `AffineIndependent.injective_affineSpan_image` / 引理 `AffineIndependent.injective_affineSpan_image`

English:
lemma AffineIndependent.injective_affineSpan_image
  statement: [Nontrivial k] {p : ι -> P}
  proof: by
  by_contra hn
  rw [not_injective_iff] at hn
  obtain ⟨s₁, s₂, hs₁₂, hne⟩ := hn
  apply hne
  ext i
  simp_rw [← ha.mem_affineSpan_iff, hs₁₂]

中文:
引理 AffineIndependent.injective_affineSpan_image
  结论: [Nontrivial k] {p : ι -> P}
  证明: by
  by_contra hn
  rw [not_injective_iff] at hn
  obtain ⟨s₁, s₂, hs₁₂, hne⟩ := hn
  apply hne
  ext i
  simp_rw [← ha.mem_affineSpan_iff, hs₁₂]

Depends on / 依赖: ha.mem_affineSpan_iff, mem_affineSpan_iff, not_injective_iff, simp_rw
-/
lemma AffineIndependent.injective_affineSpan_image [Nontrivial k] {p : ι -> P}
    (ha : AffineIndependent k p) : Injective fun (s : Set ι) => affineSpan k (p '' s) := by
  by_contra hn
  rw [not_injective_iff] at hn
  obtain ⟨s₁, s₂, hs₁₂, hne⟩ := hn
  apply hne
  ext i
  simp_rw [← ha.mem_affineSpan_iff, hs₁₂]

/--
lemma `AffineIndependent.vectorSpan_image_ne_of_mem_of_notMem_of_not_subsingleton` / 引理 `AffineIndependent.vectorSpan_image_ne_of_mem_of_notMem_of_not_subsingleton`

English:
lemma AffineIndependent.vectorSpan_image_ne_of_mem_of_notMem_of_not_subsingleton
  proof: by
  classical
  rw [Set.not_subsingleton_iff] at h₁
  obtain ⟨j, hj, hne⟩ := h₁.exists_ne i
  intro he
  have hs : p i -ᵥ p j in vectorSpan k (p '' s₁) :=
    vsub_mem_vectorSpan k (Set.mem_image_of_mem _ his₁) (Set.mem_image_of_mem _ hj)
  rw [he]; rw [Set.image_eq_range]; rw [mem_vectorSpan_iff_e

中文:
引理 AffineIndependent.vectorSpan_image_ne_of_mem_of_notMem_of_not_subsingleton
  证明: by
  classical
  rw [Set.not_subsingleton_iff] at h₁
  obtain ⟨j, hj, hne⟩ := h₁.exists_ne i
  intro he
  have hs : p i -ᵥ p j in vectorSpan k (p '' s₁) :=
    vsub_mem_vectorSpan k (Set.mem_image_of_mem _ his₁) (Set.mem_image_of_mem _ hj)
  rw [he]; rw [Set.image_eq_range]; rw [mem_vectorSpan_iff_e
-/
private lemma AffineIndependent.vectorSpan_image_ne_of_mem_of_notMem_of_not_subsingleton
    [Nontrivial k] {p : ι -> P} (ha : AffineIndependent k p) {s₁ s₂ : Set ι} {i : ι}
    (his₁ : i in s₁) (his₂ : i ∉ s₂) (h₁ : ¬s₁.Subsingleton) :
    vectorSpan k (p '' s₁) != vectorSpan k (p '' s₂) := by
  classical
  rw [Set.not_subsingleton_iff] at h₁
  obtain ⟨j, hj, hne⟩ := h₁.exists_ne i
  intro he
  have hs : p i -ᵥ p j in vectorSpan k (p '' s₁) :=
    vsub_mem_vectorSpan k (Set.mem_image_of_mem _ his₁) (Set.mem_image_of_mem _ hj)
  rw [he]; rw [Set.image_eq_range]; rw [mem_vectorSpan_iff_eq_weightedVSub] at hs
  obtain ⟨fs, w, hw, hs⟩ := hs
  let w' : ι -> k := Function.extend Subtype.val w 0
  have hw' : ∑ t in fs.map (Embedding.subtype _), w' t = 0 := by
    simp only [sum_map, Embedding.subtype_apply, ← hw]
    exact sum_congr rfl fun t ht => by simp [w']
  have hs' : p i -ᵥ p j = (fs.map (Embedding.subtype _)).weightedVSub p w' := by
    rw [hs]; rw [weightedVSub_map]
    simp [w', Function.comp_def]
  let fs' : Finset ι := insert i (insert j (fs.map (Embedding.subtype _)))
  have hfsfs' : fs.map (Embedding.subtype _) subseteq fs' := by grind
  let w'' : ι -> k := Set.indicator (fs.map (Embedding.subtype _)) w'
  have hs'' : p i -ᵥ p j = fs'.weightedVSub p w'' := by
    rw [hs']
    exact weightedVSubOfPoint_indicator_subset _ _ _ (by grind)
  have hw'' : ∑ t in fs', w'' t = 0 := by
    rw [← hw']
    exact sum_indicator_subset _ (by grind)
  let w''' : ι -> k := w'' - weightedVSubVSubWeights k i j
  have hi : i in fs' := by grind
  have hj : j in fs' := by grind
  have hw''' : ∑ t in fs', w''' t = 0 := by
    simp [w''', sum_sub_distrib, hw'', hi, hj]
  have hs''' : fs'.weightedVSub p w''' = 0 := by
    simp [w''', ← hs'', hi, hj]
  have h0 := ha fs' w''' hw''' hs''' i hi
  simp [w''', w'', Pi.sub_apply, hne.symm, his₂] at h0

/--
lemma `AffineIndependent.vectorSpan_image_eq_iff` / 引理 `AffineIndependent.vectorSpan_image_eq_iff`

English:
lemma AffineIndependent.vectorSpan_image_eq_iff
  statement: [Nontrivial k] {p : ι -> P}
  proof: by
  constructor
  · intro h
    by_cases he : s₁ = s₂
    · simp [he]
    simp only [he, false_or]
    by_cases h₁ : s₁.Subsingleton
    · rw [vectorSpan_of_subsingleton _ (h₁.image _), eq_comm, vectorSpan_eq_bot_iff_subsingleton]
        at h
      exact ⟨h₁, Set.subsingleton_of_image ha.injective

中文:
引理 AffineIndependent.vectorSpan_image_eq_iff
  结论: [Nontrivial k] {p : ι -> P}
  证明: by
  constructor
  · intro h
    by_cases he : s₁ = s₂
    · simp [he]
    simp only [he, false_or]
    by_cases h₁ : s₁.Subsingleton
    · rw [vectorSpan_of_subsingleton _ (h₁.image _), eq_comm, vectorSpan_eq_bot_iff_subsingleton]
        at h
      exact ⟨h₁, Set.subsingleton_of_image ha.injective

Depends on / 依赖: Set.subsingleton_of_image, Subsingleton, eq_comm, false_and, false_or, ha.injective, injective, subsingleton_of_image, vectorSpan_eq_bot_iff_subsingleton, vectorSpan_of_subsingleton
-/
lemma AffineIndependent.vectorSpan_image_eq_iff [Nontrivial k] {p : ι -> P}
    (ha : AffineIndependent k p) {s₁ s₂ : Set ι} :
    vectorSpan k (p '' s₁) = vectorSpan k (p '' s₂) ↔
      s₁ = s₂ ∨ s₁.Subsingleton ∧ s₂.Subsingleton := by
  constructor
  · intro h
    by_cases he : s₁ = s₂
    · simp [he]
    simp only [he, false_or]
    by_cases h₁ : s₁.Subsingleton
    · rw [vectorSpan_of_subsingleton _ (h₁.image _), eq_comm, vectorSpan_eq_bot_iff_subsingleton]
        at h
      exact ⟨h₁, Set.subsingleton_of_image ha.injective s₂ h⟩
    by_cases h₂ : s₂.Subsingleton
    · rw [vectorSpan_of_subsingleton _ (h₂.image _), vectorSpan_eq_bot_iff_subsingleton]
        at h
      exact ⟨Set.subsingleton_of_image ha.injective s₁ h, h₂⟩
    simp only [h₁, h₂, false_and]
    have hi : (exists i in s₁, i ∉ s₂) ∨ exists i in s₂, i ∉ s₁ := by grind
    rcases hi with ⟨i, his₁, his₂⟩ | ⟨i, his₂, his₁⟩
    · exact ha.vectorSpan_image_ne_of_mem_of_notMem_of_not_subsingleton his₁ his₂ h₁ h
    · exact ha.vectorSpan_image_ne_of_mem_of_notMem_of_not_subsingleton his₂ his₁ h₂ h.symm
  · intro h
    rcases h with rfl | ⟨h₁, h₂⟩
    · rfl
    · simp [h₁.image p, h₂.image p, vectorSpan_of_subsingleton]

/--
theorem `exists_nontrivial_relation_sum_zero_of_not_affine_ind` / 定理 `exists_nontrivial_relation_sum_zero_of_not_affine_ind`

English:
theorem exists_nontrivial_relation_sum_zero_of_not_affine_ind
  statement: {t : Finset V}
  proof: by
  classical
    rw [affineIndependent_iff_of_fintype] at h
    simp only [exists_prop, not_forall] at h
    obtain ⟨w, hw, hwt, i, hi⟩ := h
    simp only [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ w ((↑) : t -> V) hw 0,
      vsub_eq_sub, Finset.weightedVSubOfPoint_apply, sub_ze

中文:
定理 exists_nontrivial_relation_sum_zero_of_not_affine_ind
  结论: {t : Finset V}
  证明: by
  classical
    rw [affineIndependent_iff_of_fintype] at h
    simp only [exists_prop, not_forall] at h
    obtain ⟨w, hw, hwt, i, hi⟩ := h
    simp only [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ w ((↑) : t -> V) hw 0,
      vsub_eq_sub, Finset.weightedVSubOfPoint_apply, sub_ze

Depends on / 依赖: Finset, Finset.weightedVSubOfPoint_apply, Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero, affineIndependent_iff_of_fintype, classical, exists_prop, not_forall, on_goal, sub_zero, vsub_eq_sub, weightedVSubOfPoint_apply, weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero
-/
theorem exists_nontrivial_relation_sum_zero_of_not_affine_ind {t : Finset V}
    (h : ¬AffineIndependent k ((↑) : t -> V)) :
    exists f : V -> k, ∑ e in t, f e • e = 0 ∧ ∑ e in t, f e = 0 ∧ exists x in t, f x != 0 := by
  classical
    rw [affineIndependent_iff_of_fintype] at h
    simp only [exists_prop, not_forall] at h
    obtain ⟨w, hw, hwt, i, hi⟩ := h
    simp only [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ w ((↑) : t -> V) hw 0,
      vsub_eq_sub, Finset.weightedVSubOfPoint_apply, sub_zero] at hwt
    let f : forall x : V, x in t -> k := fun x hx => w ⟨x, hx⟩
    refine ⟨fun x => if hx : x in t then f x hx else (0 : k), ?_, ?_, by use i; simp [f, hi]⟩
    on_goal 1 =>
      suffices (∑ e in t, dite (e in t) (fun hx => f e hx • e) fun _ => 0) = 0 by
        convert! this
        rename V => x
        by_cases hx : x in t <;> simp [hx]
    all_goals
      simp only [f, Finset.sum_dite_of_true fun _ h => h, Finset.mk_coe, hwt, hw]

variable {s : Finset ι} {w w₁ w₂ : ι -> k} {p : ι -> V}

/--
theorem `affineIndependent_iff` / 定理 `affineIndependent_iff`

English:
theorem affineIndependent_iff
  given: {ι} {p : ι -> V}
  proof: forall₃_congr fun s w hw => by simp [s.weightedVSub_eq_linear_combination hw]

中文:
定理 affineIndependent_iff
  条件: {ι} {p : ι -> V}
  证明: forall₃_congr fun s w hw => by simp [s.weightedVSub_eq_linear_combination hw]

Depends on / 依赖: s.weightedVSub_eq_linear_combination, weightedVSub_eq_linear_combination
-/
theorem affineIndependent_iff {ι} {p : ι -> V} :
    AffineIndependent k p ↔
      forall (s : Finset ι) (w : ι -> k), s.sum w = 0 -> ∑ e in s, w e • p e = 0 -> forall e in s, w e = 0 :=
  forall₃_congr fun s w hw => by simp [s.weightedVSub_eq_linear_combination hw]

/--
lemma `AffineIndependent.eq_zero_of_sum_eq_zero` / 引理 `AffineIndependent.eq_zero_of_sum_eq_zero`

English:
lemma AffineIndependent.eq_zero_of_sum_eq_zero
  statement: (hp : AffineIndependent k p)
  proof: affineIndependent_iff.1 hp _ _ hw₀ hw₁

中文:
引理 AffineIndependent.eq_zero_of_sum_eq_zero
  结论: (hp : AffineIndependent k p)
  证明: affineIndependent_iff.1 hp _ _ hw₀ hw₁

Depends on / 依赖: affineIndependent_iff
-/
lemma AffineIndependent.eq_zero_of_sum_eq_zero (hp : AffineIndependent k p)
    (hw₀ : ∑ i in s, w i = 0) (hw₁ : ∑ i in s, w i • p i = 0) : forall i in s, w i = 0 :=
  affineIndependent_iff.1 hp _ _ hw₀ hw₁

/--
lemma `AffineIndependent.eq_of_sum_eq_sum` / 引理 `AffineIndependent.eq_of_sum_eq_sum`

English:
lemma AffineIndependent.eq_of_sum_eq_sum
  statement: (hp : AffineIndependent k p)
  proof: by
  refine fun i hi => sub_eq_zero.1 (hp.eq_zero_of_sum_eq_zero (w := w₁ - w₂) ?_ ?_ _ hi) <;>
    simpa [sub_mul, sub_smul, sub_eq_zero]

中文:
引理 AffineIndependent.eq_of_sum_eq_sum
  结论: (hp : AffineIndependent k p)
  证明: by
  refine fun i hi => sub_eq_zero.1 (hp.eq_zero_of_sum_eq_zero (w := w₁ - w₂) ?_ ?_ _ hi) <;>
    simpa [sub_mul, sub_smul, sub_eq_zero]

Depends on / 依赖: eq_zero_of_sum_eq_zero, hp.eq_zero_of_sum_eq_zero, sub_eq_zero, sub_mul, sub_smul
-/
lemma AffineIndependent.eq_of_sum_eq_sum (hp : AffineIndependent k p)
    (hw : ∑ i in s, w₁ i = ∑ i in s, w₂ i) (hwp : ∑ i in s, w₁ i • p i = ∑ i in s, w₂ i • p i) :
    forall i in s, w₁ i = w₂ i := by
  refine fun i hi => sub_eq_zero.1 (hp.eq_zero_of_sum_eq_zero (w := w₁ - w₂) ?_ ?_ _ hi) <;>
    simpa [sub_mul, sub_smul, sub_eq_zero]

/--
lemma `AffineIndependent.eq_zero_of_sum_eq_zero_subtype` / 引理 `AffineIndependent.eq_zero_of_sum_eq_zero_subtype`

English:
lemma AffineIndependent.eq_zero_of_sum_eq_zero_subtype
  statement: {s : Finset V}
  proof: by
  rw [← sum_attach] at hw₀ hw₁
  exact fun x hx => hp.eq_zero_of_sum_eq_zero hw₀ hw₁ ⟨x, hx⟩ (mem_univ _)

中文:
引理 AffineIndependent.eq_zero_of_sum_eq_zero_subtype
  结论: {s : Finset V}
  证明: by
  rw [← sum_attach] at hw₀ hw₁
  exact fun x hx => hp.eq_zero_of_sum_eq_zero hw₀ hw₁ ⟨x, hx⟩ (mem_univ _)

Depends on / 依赖: eq_zero_of_sum_eq_zero, hp.eq_zero_of_sum_eq_zero, mem_univ, sum_attach
-/
lemma AffineIndependent.eq_zero_of_sum_eq_zero_subtype {s : Finset V}
    (hp : AffineIndependent k ((↑) : s -> V)) {w : V -> k} (hw₀ : ∑ x in s, w x = 0)
    (hw₁ : ∑ x in s, w x • x = 0) : forall x in s, w x = 0 := by
  rw [← sum_attach] at hw₀ hw₁
  exact fun x hx => hp.eq_zero_of_sum_eq_zero hw₀ hw₁ ⟨x, hx⟩ (mem_univ _)

/--
lemma `AffineIndependent.eq_of_sum_eq_sum_subtype` / 引理 `AffineIndependent.eq_of_sum_eq_sum_subtype`

English:
lemma AffineIndependent.eq_of_sum_eq_sum_subtype
  statement: {s : Finset V}
  proof: by
  refine fun i hi => sub_eq_zero.1 (hp.eq_zero_of_sum_eq_zero_subtype (w := w₁ - w₂) ?_ ?_ _ hi) <;>
    simpa [sub_mul, sub_smul, sub_eq_zero]

中文:
引理 AffineIndependent.eq_of_sum_eq_sum_subtype
  结论: {s : Finset V}
  证明: by
  refine fun i hi => sub_eq_zero.1 (hp.eq_zero_of_sum_eq_zero_subtype (w := w₁ - w₂) ?_ ?_ _ hi) <;>
    simpa [sub_mul, sub_smul, sub_eq_zero]

Depends on / 依赖: eq_zero_of_sum_eq_zero_subtype, hp.eq_zero_of_sum_eq_zero_subtype, sub_eq_zero, sub_mul, sub_smul
-/
lemma AffineIndependent.eq_of_sum_eq_sum_subtype {s : Finset V}
    (hp : AffineIndependent k ((↑) : s -> V)) {w₁ w₂ : V -> k} (hw : ∑ i in s, w₁ i = ∑ i in s, w₂ i)
    (hwp : ∑ i in s, w₁ i • i = ∑ i in s, w₂ i • i) : forall i in s, w₁ i = w₂ i := by
  refine fun i hi => sub_eq_zero.1 (hp.eq_zero_of_sum_eq_zero_subtype (w := w₁ - w₂) ?_ ?_ _ hi) <;>
    simpa [sub_mul, sub_smul, sub_eq_zero]

/--
theorem `weightedVSub_mem_vectorSpan_pair` / 定理 `weightedVSub_mem_vectorSpan_pair`

English:
theorem weightedVSub_mem_vectorSpan_pair
  statement: {p : ι -> P} (h : AffineIndependent k p) {w w₁ w₂ : ι -> k}
  proof: by
  rw [mem_vectorSpan_pair]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with ⟨r, hr⟩
    refine ⟨r, fun i hi => ?_⟩
    rw [s.affineCombination_vsub]; rw [← s.weightedVSub_const_smul]; rw [← sub_eq_zero]; rw [← map_sub] at hr
    have hw' : (∑ j in s, (r • (w₁ - w₂) - w) j) = 0 := by
      si

中文:
定理 weightedVSub_mem_vectorSpan_pair
  结论: {p : ι -> P} (h : AffineIndependent k p) {w w₁ w₂ : ι -> k}
  证明: by
  rw [mem_vectorSpan_pair]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with ⟨r, hr⟩
    refine ⟨r, fun i hi => ?_⟩
    rw [s.affineCombination_vsub]; rw [← s.weightedVSub_const_smul]; rw [← sub_eq_zero]; rw [← map_sub] at hr
    have hw' : (∑ j in s, (r • (w₁ - w₂) - w) j) = 0 := by
      si

Depends on / 依赖: Finset, Finset.smul_sum, Finset.sum_sub_distrib, Pi.smul_apply, Pi.sub_apply, affineCombination_vsub, eq_comm, map_sub, mem_vectorSpan_pair, s.affineCombination_vsub, s.weightedVSub_const_smul, simp_rw, smul_apply, smul_eq_mul, smul_sub, smul_sum, sub_apply, sub_eq_zero, sub_self, sum_sub_distrib
-/
theorem weightedVSub_mem_vectorSpan_pair {p : ι -> P} (h : AffineIndependent k p) {w w₁ w₂ : ι -> k}
    {s : Finset ι} (hw : ∑ i in s, w i = 0) (hw₁ : ∑ i in s, w₁ i = 1)
    (hw₂ : ∑ i in s, w₂ i = 1) :
    s.weightedVSub p w in
        vectorSpan k ({s.affineCombination k p w₁, s.affineCombination k p w₂} : Set P) ↔
      exists r : k, forall i in s, w i = r * (w₁ i - w₂ i) := by
  rw [mem_vectorSpan_pair]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with ⟨r, hr⟩
    refine ⟨r, fun i hi => ?_⟩
    rw [s.affineCombination_vsub]; rw [← s.weightedVSub_const_smul]; rw [← sub_eq_zero]; rw [← map_sub] at hr
    have hw' : (∑ j in s, (r • (w₁ - w₂) - w) j) = 0 := by
      simp_rw [Pi.sub_apply, Pi.smul_apply, Pi.sub_apply, smul_sub, Finset.sum_sub_distrib, ←
        Finset.smul_sum, hw, hw₁, hw₂, sub_self]
    have hr' := h s _ hw' hr i hi
    rw [eq_comm]; rw [← sub_eq_zero]; rw [← smul_eq_mul]
    exact hr'
  · rcases h with ⟨r, hr⟩
    refine ⟨r, ?_⟩
    let w' i := r * (w₁ i - w₂ i)
    change forall i in s, w i = w' i at hr
    rw [s.weightedVSub_congr hr fun _ _ => rfl]; rw [s.affineCombination_vsub]; rw [←
      s.weightedVSub_const_smul]
    congr

/--
theorem `affineCombination_mem_affineSpan_pair` / 定理 `affineCombination_mem_affineSpan_pair`

English:
theorem affineCombination_mem_affineSpan_pair
  statement: {p : ι -> P} (h : AffineIndependent k p)
  proof: by
  rw [← vsub_vadd (s.affineCombination k p w) (s.affineCombination k p w₁)]; rw [AffineSubspace.vadd_mem_iff_mem_direction _ (left_mem_affineSpan_pair _ _ _)]; rw [direction_affineSpan]; rw [s.affineCombination_vsub]; rw [Set.pair_comm]; rw [weightedVSub_mem_vectorSpan_pair h _ hw₂ hw₁]
  · simp 

中文:
定理 affineCombination_mem_affineSpan_pair
  结论: {p : ι -> P} (h : AffineIndependent k p)
  证明: by
  rw [← vsub_vadd (s.affineCombination k p w) (s.affineCombination k p w₁)]; rw [AffineSubspace.vadd_mem_iff_mem_direction _ (left_mem_affineSpan_pair _ _ _)]; rw [direction_affineSpan]; rw [s.affineCombination_vsub]; rw [Set.pair_comm]; rw [weightedVSub_mem_vectorSpan_pair h _ hw₂ hw₁]
  · simp 

Depends on / 依赖: AffineSubspace, AffineSubspace.vadd_mem_iff_mem_direction, Finset, Finset.sum_sub_distrib, Pi.sub_apply, Set.pair_comm, affineCombination, affineCombination_vsub, direction_affineSpan, left_mem_affineSpan_pair, pair_comm, s.affineCombination, s.affineCombination_vsub, sub_apply, sub_eq_iff_eq_add, sub_self, sum_sub_distrib, vadd_mem_iff_mem_direction, vsub_vadd, weightedVSub_mem_vectorSpan_pair
-/
theorem affineCombination_mem_affineSpan_pair {p : ι -> P} (h : AffineIndependent k p)
    {w w₁ w₂ : ι -> k} {s : Finset ι} (_ : ∑ i in s, w i = 1) (hw₁ : ∑ i in s, w₁ i = 1)
    (hw₂ : ∑ i in s, w₂ i = 1) :
    s.affineCombination k p w in line[k, s.affineCombination k p w₁, s.affineCombination k p w₂] ↔
      exists r : k, forall i in s, w i = r * (w₂ i - w₁ i) + w₁ i := by
  rw [← vsub_vadd (s.affineCombination k p w) (s.affineCombination k p w₁)]; rw [AffineSubspace.vadd_mem_iff_mem_direction _ (left_mem_affineSpan_pair _ _ _)]; rw [direction_affineSpan]; rw [s.affineCombination_vsub]; rw [Set.pair_comm]; rw [weightedVSub_mem_vectorSpan_pair h _ hw₂ hw₁]
  · simp only [Pi.sub_apply, sub_eq_iff_eq_add]
  · simp_all only [Pi.sub_apply, Finset.sum_sub_distrib, sub_self]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `AffineIndependent.affineCombination_eq_lineMap_iff_weight_lineMap` / 定理 `AffineIndependent.affineCombination_eq_lineMap_iff_weight_lineMap`

English:
theorem AffineIndependent.affineCombination_eq_lineMap_iff_weight_lineMap
  statement: {p : ι -> P}
  proof: by
  rw [← AffineMap.apply_lineMap]; rw [ha.affineCombination_eq_iff_eq hw]
  · simp [AffineMap.lineMap_apply]
  · simp [AffineMap.lineMap_apply, sum_add_distrib, ← mul_sum, hw₁, hw₂]

中文:
定理 AffineIndependent.affineCombination_eq_lineMap_iff_weight_lineMap
  结论: {p : ι -> P}
  证明: by
  rw [← AffineMap.apply_lineMap]; rw [ha.affineCombination_eq_iff_eq hw]
  · simp [AffineMap.lineMap_apply]
  · simp [AffineMap.lineMap_apply, sum_add_distrib, ← mul_sum, hw₁, hw₂]

Depends on / 依赖: AffineMap, AffineMap.apply_lineMap, AffineMap.lineMap_apply, affineCombination_eq_iff_eq, apply_lineMap, ha.affineCombination_eq_iff_eq, lineMap_apply, mul_sum, pi_nullSingletonClass, sum_add_distrib
-/
theorem AffineIndependent.affineCombination_eq_lineMap_iff_weight_lineMap {p : ι -> P}
    (ha : AffineIndependent k p) {w w₁ w₂ : ι -> k} {s : Finset ι} (hw : ∑ i in s, w i = 1)
    (hw₁ : ∑ i in s, w₁ i = 1) (hw₂ : ∑ i in s, w₂ i = 1) (c : k) :
    s.affineCombination k p w =
      AffineMap.lineMap (s.affineCombination k p w₁) (s.affineCombination k p w₂) c ↔
        forall i in s, w i = AffineMap.lineMap (w₁ i) (w₂ i) c := by
  rw [← AffineMap.apply_lineMap]; rw [ha.affineCombination_eq_iff_eq hw]
  · simp [AffineMap.lineMap_apply]
  · simp [AffineMap.lineMap_apply, sum_add_distrib, ← mul_sum, hw₁, hw₂]

end AffineIndependent

section DivisionRing

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
variable [AffineSpace V P] {ι : Type*}

set_option backward.isDefEq.respectTransparency false in
/--
theorem `exists_subset_affineIndependent_affineSpan_eq_top` / 定理 `exists_subset_affineIndependent_affineSpan_eq_top`

English:
theorem exists_subset_affineIndependent_affineSpan_eq_top
  statement: {s : Set P}
  proof: by
  rcases s.eq_empty_or_nonempty with (rfl | ⟨p₁, hp₁⟩)
  · have p₁ : P := AddTorsor.nonempty.some
    let hsv := Basis.ofVectorSpace k V
    have hsvi := hsv.linearIndependent
    have hsvt := hsv.span_eq
    rw [Basis.coe_ofVectorSpace] at hsvi hsvt
    have h0 : forall v : V, v in Basis.ofVecto

中文:
定理 exists_subset_affineIndependent_affineSpan_eq_top
  结论: {s : Set P}
  证明: by
  rcases s.eq_empty_or_nonempty with (rfl | ⟨p₁, hp₁⟩)
  · have p₁ : P := AddTorsor.nonempty.some
    let hsv := Basis.ofVectorSpace k V
    have hsvi := hsv.linearIndependent
    have hsvt := hsv.span_eq
    rw [Basis.coe_ofVectorSpace] at hsvi hsvt
    have h0 : forall v : V, v in Basis.ofVecto

Depends on / 依赖: AddTorsor, AddTorsor.nonempty.some, Basis.coe_ofVectorSpace, Basis.ofVectorSpace, Basis.ofVectorSpaceIndex, Set.empty_subs, coe_ofVectorSpace, empty_subs, eq_empty_or_nonempty, hsv.linearIndependent, hsv.ne_zero, hsv.span_eq, linearIndependent, linearIndependent_set_iff_affineIndependent_vadd_union_singleton, ne_zero, nonempty, ofVectorSpace, ofVectorSpaceIndex, s.eq_empty_or_nonempty, span_eq
-/
theorem exists_subset_affineIndependent_affineSpan_eq_top {s : Set P}
    (h : AffineIndependent k (fun p => p : s -> P)) :
    exists t : Set P, s subseteq t ∧ AffineIndependent k (fun p => p : t -> P) ∧ affineSpan k t = ⊤ := by
  rcases s.eq_empty_or_nonempty with (rfl | ⟨p₁, hp₁⟩)
  · have p₁ : P := AddTorsor.nonempty.some
    let hsv := Basis.ofVectorSpace k V
    have hsvi := hsv.linearIndependent
    have hsvt := hsv.span_eq
    rw [Basis.coe_ofVectorSpace] at hsvi hsvt
    have h0 : forall v : V, v in Basis.ofVectorSpaceIndex k V -> v != 0 := by
      intro v hv
      simpa [hsv] using hsv.ne_zero ⟨v, hv⟩
    rw [linearIndependent_set_iff_affineIndependent_vadd_union_singleton k h0 p₁] at hsvi
    exact
      ⟨{p₁} union (fun v => v +ᵥ p₁) '' _, Set.empty_subset _, hsvi,
        affineSpan_singleton_union_vadd_eq_top_of_span_eq_top p₁ hsvt⟩
  · rw [affineIndependent_set_iff_linearIndependent_vsub k hp₁] at h
    let bsv := Basis.extend h
    have hsvi := bsv.linearIndependent
    have hsvt := bsv.span_eq
    rw [Basis.coe_extend] at hsvi hsvt
    rw [linearIndependent_subtype_iff] at hsvi h
    have hsv := h.subset_extend (Set.subset_univ _)
    have h0 : forall v : V, v in h.extend (Set.subset_univ _) -> v != 0 := by
      intro v hv
      simpa [bsv] using bsv.ne_zero ⟨v, hv⟩
    rw [← linearIndependent_subtype_iff]; rw [linearIndependent_set_iff_affineIndependent_vadd_union_singleton k h0 p₁] at hsvi
    refine ⟨{p₁} union (fun v => v +ᵥ p₁) '' h.extend (Set.subset_univ _), ?_, ?_⟩
    · refine Set.Subset.trans ?_ (Set.union_subset_union_right _ (Set.image_mono hsv))
      simp [Set.image_image]
    · use hsvi
      exact affineSpan_singleton_union_vadd_eq_top_of_span_eq_top p₁ hsvt

variable (k V)

/--
theorem `exists_affineIndependent` / 定理 `exists_affineIndependent`

English:
theorem exists_affineIndependent
  given: (s : Set P)
  proof: by
  rcases s.eq_empty_or_nonempty with (rfl | ⟨p, hp⟩)
  · exact ⟨∅, Set.empty_subset ∅, rfl, affineIndependent_of_subsingleton k _⟩
  obtain ⟨b, hb₁, hb₂, hb₃⟩ := exists_linearIndependent k ((Equiv.vaddConst p).symm '' s)
  have hb₀ : forall v : V, v in b -> v != 0 := fun v hv => hb₃.ne_zero (⟨v, 

中文:
定理 exists_affineIndependent
  条件: (s : Set P)
  证明: by
  rcases s.eq_empty_or_nonempty with (rfl | ⟨p, hp⟩)
  · exact ⟨∅, Set.empty_subset ∅, rfl, affineIndependent_of_subsingleton k _⟩
  obtain ⟨b, hb₁, hb₂, hb₃⟩ := exists_linearIndependent k ((Equiv.vaddConst p).symm '' s)
  have hb₀ : forall v : V, v in b -> v != 0 := fun v hv => hb₃.ne_zero (⟨v, 

Depends on / 依赖: Equiv.vaddConst, Set.empty_subset, Set.singleton_subset_iff.mpr, Set.union_subset, affineIndependent_of_subsingleton, empty_subset, eq_empty_or_nonempty, exists_linearIndependent, isLocallyFiniteMeasure, linearIndependent_set_iff_affineIndependent_vadd_union_singleton, ne_zero, pi.isLocallyFiniteMeasure, s.eq_empty_or_nonempty, singleton_subset_iff, union_subset, vaddConst
-/
theorem exists_affineIndependent (s : Set P) :
    exists t subseteq s, affineSpan k t = affineSpan k s ∧ AffineIndependent k ((↑) : t -> P) := by
  rcases s.eq_empty_or_nonempty with (rfl | ⟨p, hp⟩)
  · exact ⟨∅, Set.empty_subset ∅, rfl, affineIndependent_of_subsingleton k _⟩
  obtain ⟨b, hb₁, hb₂, hb₃⟩ := exists_linearIndependent k ((Equiv.vaddConst p).symm '' s)
  have hb₀ : forall v : V, v in b -> v != 0 := fun v hv => hb₃.ne_zero (⟨v, hv⟩ : b)
  rw [linearIndependent_set_iff_affineIndependent_vadd_union_singleton k hb₀ p] at hb₃
  refine ⟨{p} union Equiv.vaddConst p '' b, ?_, ?_, hb₃⟩
  · apply Set.union_subset (Set.singleton_subset_iff.mpr hp)
    rwa [← (Equiv.vaddConst p).subset_symm_image b s]
  · rw [Equiv.coe_vaddConst_symm, ← vectorSpan_eq_span_vsub_set_right k hp] at hb₂
    apply AffineSubspace.ext_of_direction_eq
    · have : Submodule.span k b = Submodule.span k (insert 0 b) := by simp
      simp only [direction_affineSpan, ← hb₂, Equiv.coe_vaddConst, Set.singleton_union,
        vectorSpan_eq_span_vsub_set_right k (Set.mem_insert p _), this]
      congr
      change (Equiv.vaddConst p).symm '' insert p (Equiv.vaddConst p '' b) = _
      rw [Set.image_insert_eq]; rw [← Set.image_comp]
      simp
    · use p
      simp only [Equiv.coe_vaddConst, Set.singleton_union, Set.mem_inter_iff]
      exact ⟨mem_affineSpan k (Set.mem_insert p _), mem_affineSpan k hp⟩

variable {V}

/--
theorem `affineIndependent_of_ne` / 定理 `affineIndependent_of_ne`

English:
theorem affineIndependent_of_ne
  given: {p₁ p₂ : P} (h : p₁ != p₂)
  statement: AffineIndependent k ![p₁, p₂]
  proof: by
  rw [affineIndependent_iff_linearIndependent_vsub k ![p₁]; rw [p₂] 0]
  let i₁ : { x // x != (0 : Fin 2) } := ⟨1, by simp⟩
  have he' : forall i, i = i₁ := by
    rintro ⟨i, hi⟩
    ext
    fin_cases i
    · simp at hi
    · simp [i₁]
  have : Unique { x // x != (0 : Fin 2) } := ⟨⟨i₁⟩, he'⟩
  re

中文:
定理 affineIndependent_of_ne
  条件: {p₁ p₂ : P} (h : p₁ != p₂)
  结论: AffineIndependent k ![p₁, p₂]
  证明: by
  rw [affineIndependent_iff_linearIndependent_vsub k ![p₁]; rw [p₂] 0]
  let i₁ : { x // x != (0 : Fin 2) } := ⟨1, by simp⟩
  have he' : forall i, i = i₁ := by
    rintro ⟨i, hi⟩
    ext
    fin_cases i
    · simp at hi
    · simp [i₁]
  have : Unique { x // x != (0 : Fin 2) } := ⟨⟨i₁⟩, he'⟩
  re

Depends on / 依赖: Unique, affineIndependent_iff_linearIndependent_vsub, fin_cases, h.symm, of_subsingleton
-/
theorem affineIndependent_of_ne {p₁ p₂ : P} (h : p₁ != p₂) : AffineIndependent k ![p₁, p₂] := by
  rw [affineIndependent_iff_linearIndependent_vsub k ![p₁]; rw [p₂] 0]
  let i₁ : { x // x != (0 : Fin 2) } := ⟨1, by simp⟩
  have he' : forall i, i = i₁ := by
    rintro ⟨i, hi⟩
    ext
    fin_cases i
    · simp at hi
    · simp [i₁]
  have : Unique { x // x != (0 : Fin 2) } := ⟨⟨i₁⟩, he'⟩
  refine .of_subsingleton default ?_
  rw [he' default]
  simpa using! h.symm

variable {k}

/--
theorem `AffineIndependent.affineIndependent_of_notMem_span` / 定理 `AffineIndependent.affineIndependent_of_notMem_span`

English:
theorem AffineIndependent.affineIndependent_of_notMem_span
  statement: {p : ι -> P} {i : ι}
  proof: by
  classical
    intro s w hw hs
    let s' : Finset { y // y != i } := s.subtype (· != i)
    let p' : { y // y != i } -> P := fun x => p x
    by_cases his : i in s ∧ w i != 0
    · refine False.elim (hi ?_)
      let wm : ι -> k := -(w i)⁻¹ • w
      have hms : s.weightedVSub p wm = (0 : V) := 

中文:
定理 AffineIndependent.affineIndependent_of_notMem_span
  结论: {p : ι -> P} {i : ι}
  证明: by
  classical
    intro s w hw hs
    let s' : Finset { y // y != i } := s.subtype (· != i)
    let p' : { y // y != i } -> P := fun x => p x
    by_cases his : i in s ∧ w i != 0
    · refine False.elim (hi ?_)
      let wm : ι -> k := -(w i)⁻¹ • w
      have hms : s.weightedVSub p wm = (0 : V) := 

Depends on / 依赖: False.elim, Finset, Finset.mul_sum, classical, mul_sum, s.subtype, s.weightedVSub, simp_rw, subtype, weightedVSub
-/
theorem AffineIndependent.affineIndependent_of_notMem_span {p : ι -> P} {i : ι}
    (ha : AffineIndependent k fun x : { y // y != i } => p x)
    (hi : p i ∉ affineSpan k (p '' { x | x != i })) : AffineIndependent k p := by
  classical
    intro s w hw hs
    let s' : Finset { y // y != i } := s.subtype (· != i)
    let p' : { y // y != i } -> P := fun x => p x
    by_cases his : i in s ∧ w i != 0
    · refine False.elim (hi ?_)
      let wm : ι -> k := -(w i)⁻¹ • w
      have hms : s.weightedVSub p wm = (0 : V) := by simp [wm, hs]
      have hwm : ∑ i in s, wm i = 0 := by simp [wm, ← Finset.mul_sum, hw]
      have hwmi : wm i = -1 := by simp [wm, his.2]
      let w' : { y // y != i } -> k := fun x => wm x
      have hw' : ∑ x in s', w' x = 1 := by
        simp_rw [w', s', Finset.sum_subtype_eq_sum_filter]
        rw [← s.sum_filter_add_sum_filter_not (· != i)] at hwm
        simpa only [not_not, Finset.filter_eq' _ i, if_pos his.1, sum_singleton, hwmi,
          add_neg_eq_zero] using hwm
      rw [← s.affineCombination_eq_of_weightedVSub_eq_zero_of_eq_neg_one hms his.1 hwmi]; rw [←
        (Subtype.range_coe : _ = { x | x != i })]; rw [← Set.range_comp]; rw [←
        s.affineCombination_subtype_eq_filter]
      exact affineCombination_mem_affineSpan hw' p'
    · rw [not_and_or, Classical.not_not] at his
      let w' : { y // y != i } -> k := fun x => w x
      have hw' : ∑ x in s', w' x = 0 := by
        simp_rw [w', s', Finset.sum_subtype_eq_sum_filter]
        rw [Finset.sum_filter_of_ne]; rw [hw]
        rintro x hxs hwx rfl
        exact hwx (his.neg_resolve_left hxs)
      have hs' : s'.weightedVSub p' w' = (0 : V) := by
        simp_rw [w', s', p', Finset.weightedVSub_subtype_eq_filter]
        rw [Finset.weightedVSub_filter_of_ne]; rw [hs]
        rintro x hxs hwx rfl
        exact hwx (his.neg_resolve_left hxs)
      intro j hj
      by_cases hji : j = i
      · rw [hji] at hj
        exact hji.symm ▸ his.neg_resolve_left hj
      · exact ha s' w' hw' hs' ⟨j, hji⟩ (Finset.mem_subtype.2 hj)

/--
theorem `affineIndependent_of_ne_of_mem_of_mem_of_notMem` / 定理 `affineIndependent_of_ne_of_mem_of_mem_of_notMem`

English:
theorem affineIndependent_of_ne_of_mem_of_mem_of_notMem
  statement: {s : AffineSubspace k P} {p₁ p₂ p₃ : P}
  proof: by
  have ha : AffineIndependent k fun x : { x : Fin 3 // x != 2 } => ![p₁, p₂, p₃] x := by
    rw [← affineIndependent_equiv (finSuccAboveEquiv (2 : Fin 3))]
    convert! affineIndependent_of_ne k hp₁p₂
    ext x
    fin_cases x <;> rfl
  refine ha.affineIndependent_of_notMem_span ?_
  intro h
  re

中文:
定理 affineIndependent_of_ne_of_mem_of_mem_of_notMem
  结论: {s : AffineSubspace k P} {p₁ p₂ p₃ : P}
  证明: by
  have ha : AffineIndependent k fun x : { x : Fin 3 // x != 2 } => ![p₁, p₂, p₃] x := by
    rw [← affineIndependent_equiv (finSuccAboveEquiv (2 : Fin 3))]
    convert! affineIndependent_of_ne k hp₁p₂
    ext x
    fin_cases x <;> rfl
  refine ha.affineIndependent_of_notMem_span ?_
  intro h
  re

Depends on / 依赖: AffineIndependent, AffineSubspace, AffineSubspace.le_def, Set.image_subset_iff, Set.mem_preimage, Set.subset_def, affineIndependent_equiv, affineIndependent_of_ne, affineIndependent_of_notMem_span, affineSpan_le, convert, finSuccAboveEquiv, fin_cases, ha.affineIndependent_of_notMem_span, image_subset_iff, le_def, mem_preimage, simp_rw, subset_def
-/
theorem affineIndependent_of_ne_of_mem_of_mem_of_notMem {s : AffineSubspace k P} {p₁ p₂ p₃ : P}
    (hp₁p₂ : p₁ != p₂) (hp₁ : p₁ in s) (hp₂ : p₂ in s) (hp₃ : p₃ ∉ s) :
    AffineIndependent k ![p₁, p₂, p₃] := by
  have ha : AffineIndependent k fun x : { x : Fin 3 // x != 2 } => ![p₁, p₂, p₃] x := by
    rw [← affineIndependent_equiv (finSuccAboveEquiv (2 : Fin 3))]
    convert! affineIndependent_of_ne k hp₁p₂
    ext x
    fin_cases x <;> rfl
  refine ha.affineIndependent_of_notMem_span ?_
  intro h
  refine hp₃ ((AffineSubspace.le_def' _ s).1 ?_ p₃ h)
  simp_rw [affineSpan_le, Set.image_subset_iff, Set.subset_def, Set.mem_preimage]
  intro x
  fin_cases x <;> simp +decide [hp₁, hp₂]

/--
theorem `affineIndependent_of_ne_of_mem_of_notMem_of_mem` / 定理 `affineIndependent_of_ne_of_mem_of_notMem_of_mem`

English:
theorem affineIndependent_of_ne_of_mem_of_notMem_of_mem
  statement: {s : AffineSubspace k P} {p₁ p₂ p₃ : P}
  proof: by
  rw [← affineIndependent_equiv (Equiv.swap (1 : Fin 3) 2)]
  convert! affineIndependent_of_ne_of_mem_of_mem_of_notMem hp₁p₃ hp₁ hp₃ hp₂ using 1
  ext x
  fin_cases x <;> rfl

中文:
定理 affineIndependent_of_ne_of_mem_of_notMem_of_mem
  结论: {s : AffineSubspace k P} {p₁ p₂ p₃ : P}
  证明: by
  rw [← affineIndependent_equiv (Equiv.swap (1 : Fin 3) 2)]
  convert! affineIndependent_of_ne_of_mem_of_mem_of_notMem hp₁p₃ hp₁ hp₃ hp₂ using 1
  ext x
  fin_cases x <;> rfl

Depends on / 依赖: Equiv.swap, affineIndependent_equiv, affineIndependent_of_ne_of_mem_of_mem_of_notMem, convert, fin_cases, isMulLeftInvariant, pi.isMulLeftInvariant
-/
theorem affineIndependent_of_ne_of_mem_of_notMem_of_mem {s : AffineSubspace k P} {p₁ p₂ p₃ : P}
    (hp₁p₃ : p₁ != p₃) (hp₁ : p₁ in s) (hp₂ : p₂ ∉ s) (hp₃ : p₃ in s) :
    AffineIndependent k ![p₁, p₂, p₃] := by
  rw [← affineIndependent_equiv (Equiv.swap (1 : Fin 3) 2)]
  convert! affineIndependent_of_ne_of_mem_of_mem_of_notMem hp₁p₃ hp₁ hp₃ hp₂ using 1
  ext x
  fin_cases x <;> rfl

/--
theorem `affineIndependent_of_ne_of_notMem_of_mem_of_mem` / 定理 `affineIndependent_of_ne_of_notMem_of_mem_of_mem`

English:
theorem affineIndependent_of_ne_of_notMem_of_mem_of_mem
  statement: {s : AffineSubspace k P} {p₁ p₂ p₃ : P}
  proof: by
  rw [← affineIndependent_equiv (Equiv.swap (0 : Fin 3) 2)]
  convert! affineIndependent_of_ne_of_mem_of_mem_of_notMem hp₂p₃.symm hp₃ hp₂ hp₁ using 1
  ext x
  fin_cases x <;> rfl

中文:
定理 affineIndependent_of_ne_of_notMem_of_mem_of_mem
  结论: {s : AffineSubspace k P} {p₁ p₂ p₃ : P}
  证明: by
  rw [← affineIndependent_equiv (Equiv.swap (0 : Fin 3) 2)]
  convert! affineIndependent_of_ne_of_mem_of_mem_of_notMem hp₂p₃.symm hp₃ hp₂ hp₁ using 1
  ext x
  fin_cases x <;> rfl

Depends on / 依赖: Equiv.swap, affineIndependent_equiv, affineIndependent_of_ne_of_mem_of_mem_of_notMem, convert, fin_cases
-/
theorem affineIndependent_of_ne_of_notMem_of_mem_of_mem {s : AffineSubspace k P} {p₁ p₂ p₃ : P}
    (hp₂p₃ : p₂ != p₃) (hp₁ : p₁ ∉ s) (hp₂ : p₂ in s) (hp₃ : p₃ in s) :
    AffineIndependent k ![p₁, p₂, p₃] := by
  rw [← affineIndependent_equiv (Equiv.swap (0 : Fin 3) 2)]
  convert! affineIndependent_of_ne_of_mem_of_mem_of_notMem hp₂p₃.symm hp₃ hp₂ hp₁ using 1
  ext x
  fin_cases x <;> rfl

/--
theorem `AffineIndependent.affineIndependent_update_of_notMem_affineSpan` / 定理 `AffineIndependent.affineIndependent_update_of_notMem_affineSpan`

English:
theorem AffineIndependent.affineIndependent_update_of_notMem_affineSpan
  statement: [DecidableEq ι]
  proof: by
  set f : ι -> P := Function.update p i p₀ with hf
  have h₁ : (fun x : {x | x != i} => p x) = fun x : {x | x != i} => f x := by ext x; aesop
have h₂ : p '' {x | x != i} = f '' {x | x != i} := Set.image_congr by simpa using congr_fun h₁
  replace ha : AffineIndependent k fun x : {x | x != i} => f

中文:
定理 AffineIndependent.affineIndependent_update_of_notMem_affineSpan
  结论: [DecidableEq ι]
  证明: by
  set f : ι -> P := Function.update p i p₀ with hf
  have h₁ : (fun x : {x | x != i} => p x) = fun x : {x | x != i} => f x := by ext x; aesop
have h₂ : p '' {x | x != i} = f '' {x | x != i} := Set.image_congr by simpa using congr_fun h₁
  replace ha : AffineIndependent k fun x : {x | x != i} => f

Depends on / 依赖: AffineIndependent, AffineIndependent.affineIndependent_of_notMem_span, AffineIndependent.subtype, Function, Function.update, Set.image_congr, affineIndependent_of_notMem_span, congr_fun, image_congr, isMulRightInvariant, pi.isMulRightInvariant, replace, subtype, update
-/
theorem AffineIndependent.affineIndependent_update_of_notMem_affineSpan [DecidableEq ι]
    {p : ι -> P} (ha : AffineIndependent k p) {i : ι} {p₀ : P}
    (hp₀ : p₀ ∉ affineSpan k (p '' {x | x != i})) :
    AffineIndependent k (Function.update p i p₀) := by
  set f : ι -> P := Function.update p i p₀ with hf
  have h₁ : (fun x : {x | x != i} => p x) = fun x : {x | x != i} => f x := by ext x; aesop
have h₂ : p '' {x | x != i} = f '' {x | x != i} := Set.image_congr by simpa using congr_fun h₁
  replace ha : AffineIndependent k fun x : {x | x != i} => f x := h₁ ▸ AffineIndependent.subtype ha _
exact AffineIndependent.affineIndependent_of_notMem_span ha by aesop

end DivisionRing

section Ordered

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup V]
variable [Module k V] [AffineSpace V P] {ι : Type*}

/--
theorem `sign_eq_of_affineCombination_mem_affineSpan_pair` / 定理 `sign_eq_of_affineCombination_mem_affineSpan_pair`

English:
theorem sign_eq_of_affineCombination_mem_affineSpan_pair
  statement: {p : ι -> P} (h : AffineIndependent k p)
  proof: by
  rw [affineCombination_mem_affineSpan_pair h hw hw₁ hw₂] at hs
  rcases hs with ⟨r, hr⟩
  rw [hr i hi]; rw [hr j hj]; rw [hi0]; rw [hj0]; rw [add_zero]; rw [add_zero]; rw [sub_zero]; rw [sub_zero]; rw [sign_mul]; rw [sign_mul]; rw [hij]

中文:
定理 sign_eq_of_affineCombination_mem_affineSpan_pair
  结论: {p : ι -> P} (h : AffineIndependent k p)
  证明: by
  rw [affineCombination_mem_affineSpan_pair h hw hw₁ hw₂] at hs
  rcases hs with ⟨r, hr⟩
  rw [hr i hi]; rw [hr j hj]; rw [hi0]; rw [hj0]; rw [add_zero]; rw [add_zero]; rw [sub_zero]; rw [sub_zero]; rw [sign_mul]; rw [sign_mul]; rw [hij]

Depends on / 依赖: add_zero, affineCombination_mem_affineSpan_pair, sign_mul, sub_zero
-/
theorem sign_eq_of_affineCombination_mem_affineSpan_pair {p : ι -> P} (h : AffineIndependent k p)
    {w w₁ w₂ : ι -> k} {s : Finset ι} (hw : ∑ i in s, w i = 1) (hw₁ : ∑ i in s, w₁ i = 1)
    (hw₂ : ∑ i in s, w₂ i = 1)
    (hs :
      s.affineCombination k p w in line[k, s.affineCombination k p w₁, s.affineCombination k p w₂])
    {i j : ι} (hi : i in s) (hj : j in s) (hi0 : w₁ i = 0) (hj0 : w₁ j = 0)
    (hij : SignType.sign (w₂ i) = SignType.sign (w₂ j)) :
    SignType.sign (w i) = SignType.sign (w j) := by
  rw [affineCombination_mem_affineSpan_pair h hw hw₁ hw₂] at hs
  rcases hs with ⟨r, hr⟩
  rw [hr i hi]; rw [hr j hj]; rw [hi0]; rw [hj0]; rw [add_zero]; rw [add_zero]; rw [sub_zero]; rw [sub_zero]; rw [sign_mul]; rw [sign_mul]; rw [hij]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `sign_eq_of_affineCombination_mem_affineSpan_single_lineMap` / 定理 `sign_eq_of_affineCombination_mem_affineSpan_single_lineMap`

English:
theorem sign_eq_of_affineCombination_mem_affineSpan_single_lineMap
  statement: {p : ι -> P}
  proof: by
  classical
    rw [← s.affineCombination_piSingle k p h₁]; rw [←
      s.affineCombination_affineCombinationLineMapWeights p h₂ h₃ c] at hs
    refine
      sign_eq_of_affineCombination_mem_affineSpan_pair h hw ?_
        (s.sum_affineCombinationLineMapWeights h₂ h₃ c) hs h₂ h₃
        (Pi.singl

中文:
定理 sign_eq_of_affineCombination_mem_affineSpan_single_lineMap
  结论: {p : ι -> P}
  证明: by
  classical
    rw [← s.affineCombination_piSingle k p h₁]; rw [←
      s.affineCombination_affineCombinationLineMapWeights p h₂ h₃ c] at hs
    refine
      sign_eq_of_affineCombination_mem_affineSpan_pair h hw ?_
        (s.sum_affineCombinationLineMapWeights h₂ h₃ c) hs h₂ h₃
        (Pi.singl

Depends on / 依赖: Finset, Finset.affineCombinationLineMapWeights_apply_left, Finset.affineCombinationLineMapWeights_apply_right, Finset.sum_pi_single, Pi.single_eq_of_ne, affineCombinationLineMapWeights_apply_left, affineCombinationLineMapWeights_apply_right, affineCombination_affineCombinationLineMapWeights, affineCombination_piSingle, classical, if_pos, isInvInvariant, pi.isInvInvariant, s.affineCombination_affineCombinationLineMapWeights, s.affineCombination_piSingle, s.sum_affineCombinationLineMapWeights, sign_eq_of_affineCombination_mem_affineSpan_pair, single_eq_of_ne, sub_p, sum_affineCombinationLineMapWeights
-/
theorem sign_eq_of_affineCombination_mem_affineSpan_single_lineMap {p : ι -> P}
    (h : AffineIndependent k p) {w : ι -> k} {s : Finset ι} (hw : ∑ i in s, w i = 1) {i₁ i₂ i₃ : ι}
    (h₁ : i₁ in s) (h₂ : i₂ in s) (h₃ : i₃ in s) (h₁₂ : i₁ != i₂) (h₁₃ : i₁ != i₃) (h₂₃ : i₂ != i₃)
    {c : k} (hc0 : 0 < c) (hc1 : c < 1)
    (hs : s.affineCombination k p w in line[k, p i₁, AffineMap.lineMap (p i₂) (p i₃) c]) :
    SignType.sign (w i₂) = SignType.sign (w i₃) := by
  classical
    rw [← s.affineCombination_piSingle k p h₁]; rw [←
      s.affineCombination_affineCombinationLineMapWeights p h₂ h₃ c] at hs
    refine
      sign_eq_of_affineCombination_mem_affineSpan_pair h hw ?_
        (s.sum_affineCombinationLineMapWeights h₂ h₃ c) hs h₂ h₃
        (Pi.single_eq_of_ne h₁₂.symm _)
        (Pi.single_eq_of_ne h₁₃.symm _) ?_
    · rw [Finset.sum_pi_single', if_pos h₁]
    rw [Finset.affineCombinationLineMapWeights_apply_left h₂₃]; rw [Finset.affineCombinationLineMapWeights_apply_right h₂₃]
    simp_all only [sub_pos, sign_pos]

end Ordered
