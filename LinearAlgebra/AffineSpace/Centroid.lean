/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.Combination

/-!
# Centroid of a Finite Set of Points in Affine Space

This file defines the centroid of a finite set of points in an affine space over a division
ring.

## Main definitions

* `centroidWeights`: A constant weight function assigning to each index in a `Finset` the same
  weight, equal to the reciprocal of the number of elements.

* `centroid`: the centroid of a `Finset` of points, defined as the affine combination using
  `centroidWeights`.

-/

@[expose] public section

assert_not_exists Affine.Simplex

noncomputable section

open Affine

namespace Finset

variable (k : Type*) {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
variable [AffineSpace V P] {ι : Type*} (s : Finset ι) {ι₂ : Type*} (s₂ : Finset ι₂)

/--
Definition of `centroidWeights` / `centroidWeights` 的定义

English:
definition centroidWeights
  signature: : ι -> k
  body: Function.const ι (#s : k)⁻¹

中文:
定义 centroidWeights
  签名: : ι -> k
  定义体: Function.const ι (#s : k)⁻¹

Depends on / 依赖: Function, Function.const
-/
def centroidWeights : ι -> k :=
  Function.const ι (#s : k)⁻¹

/-- `centroidWeights` at any point. -/
@[simp]
/--
theorem `centroidWeights_apply` / 定理 `centroidWeights_apply`

English:
theorem centroidWeights_apply
  given: (i : ι)
  statement: s.centroidWeights k i = (#s : k)⁻¹
  proof: rfl

中文:
定理 centroidWeights_apply
  条件: (i : ι)
  结论: s.centroidWeights k i = (#s : k)⁻¹
  证明: rfl
-/
theorem centroidWeights_apply (i : ι) : s.centroidWeights k i = (#s : k)⁻¹ :=
  rfl

/--
theorem `centroidWeights_eq_const` / 定理 `centroidWeights_eq_const`

English:
theorem centroidWeights_eq_const
  statement: s.centroidWeights k = Function.const ι (#s : k)⁻¹
  proof: rfl

中文:
定理 centroidWeights_eq_const
  结论: s.centroidWeights k = 函数.const ι (#s : k)⁻¹
  证明: rfl
-/
theorem centroidWeights_eq_const : s.centroidWeights k = Function.const ι (#s : k)⁻¹ :=
  rfl

variable {k} in
/--
theorem `sum_centroidWeights_eq_one_of_cast_card_ne_zero` / 定理 `sum_centroidWeights_eq_one_of_cast_card_ne_zero`

English:
theorem sum_centroidWeights_eq_one_of_cast_card_ne_zero
  given: (h : (#s : k) != 0)
  proof: by simp [h]

中文:
定理 sum_centroidWeights_eq_one_of_cast_card_ne_zero
  条件: (h : (#s : k) != 0)
  证明: by simp [h]
-/
theorem sum_centroidWeights_eq_one_of_cast_card_ne_zero (h : (#s : k) != 0) :
    ∑ i in s, s.centroidWeights k i = 1 := by simp [h]

/--
theorem `sum_centroidWeights_eq_one_of_card_ne_zero` / 定理 `sum_centroidWeights_eq_one_of_card_ne_zero`

English:
theorem sum_centroidWeights_eq_one_of_card_ne_zero
  given: [CharZero k] (h : #s != 0)
  proof: by
  simp_all

中文:
定理 sum_centroidWeights_eq_one_of_card_ne_zero
  条件: [特征零 k] (h : #s != 0)
  证明: by
  simp_all
-/
theorem sum_centroidWeights_eq_one_of_card_ne_zero [CharZero k] (h : #s != 0) :
    ∑ i in s, s.centroidWeights k i = 1 := by
  simp_all

/--
theorem `sum_centroidWeights_eq_one_of_nonempty` / 定理 `sum_centroidWeights_eq_one_of_nonempty`

English:
theorem sum_centroidWeights_eq_one_of_nonempty
  given: [CharZero k] (h : s.Nonempty)
  proof: s.sum_centroidWeights_eq_one_of_card_ne_zero k (ne_of_gt (card_pos.2 h))

中文:
定理 sum_centroidWeights_eq_one_of_nonempty
  条件: [特征零 k] (h : s.非空)
  证明: s.sum_centroidWeights_eq_one_of_card_ne_zero k (ne_of_gt (card_pos.2 h))

Depends on / 依赖: card_pos, ne_of_gt, s.sum_centroidWeights_eq_one_of_card_ne_zero, sum_centroidWeights_eq_one_of_card_ne_zero
-/
theorem sum_centroidWeights_eq_one_of_nonempty [CharZero k] (h : s.Nonempty) :
    ∑ i in s, s.centroidWeights k i = 1 :=
  s.sum_centroidWeights_eq_one_of_card_ne_zero k (ne_of_gt (card_pos.2 h))

/--
theorem `sum_centroidWeights_eq_one_of_card_eq_add_one` / 定理 `sum_centroidWeights_eq_one_of_card_eq_add_one`

English:
theorem sum_centroidWeights_eq_one_of_card_eq_add_one
  given: [CharZero k] {n : Nat} (h : #s = n + 1)
  proof: s.sum_centroidWeights_eq_one_of_card_ne_zero k (h.symm ▸ Nat.succ_ne_zero n)

中文:
定理 sum_centroidWeights_eq_one_of_card_eq_add_one
  条件: [特征零 k] {n : 自然数} (h : #s = n + 1)
  证明: s.sum_centroidWeights_eq_one_of_card_ne_zero k (h.symm ▸ Nat.succ_ne_zero n)

Depends on / 依赖: Nat.succ_ne_zero, h.symm, s.sum_centroidWeights_eq_one_of_card_ne_zero, succ_ne_zero, sum_centroidWeights_eq_one_of_card_ne_zero
-/
theorem sum_centroidWeights_eq_one_of_card_eq_add_one [CharZero k] {n : Nat} (h : #s = n + 1) :
    ∑ i in s, s.centroidWeights k i = 1 :=
  s.sum_centroidWeights_eq_one_of_card_ne_zero k (h.symm ▸ Nat.succ_ne_zero n)

/--
Definition of `centroid` / `centroid` 的定义

English:
definition centroid
  signature: (p : ι -> P)
  body: s.affineCombination k p (s.centroidWeights k)

中文:
定义 centroid
  签名: (p : ι -> P)
  定义体: s.affineCombination k p (s.centroidWeights k)

Depends on / 依赖: affineCombination, centroidWeights, s.affineCombination, s.centroidWeights
-/
def centroid (p : ι -> P) : P :=
  s.affineCombination k p (s.centroidWeights k)

/--
theorem `centroid_def` / 定理 `centroid_def`

English:
theorem centroid_def
  given: (p : ι -> P)
  statement: s.centroid k p = s.affineCombination k p (s.centroidWeights k)
  proof: rfl

中文:
定理 centroid_def
  条件: (p : ι -> P)
  结论: s.centroid k p = s.affineCombination k p (s.centroidWeights k)
  证明: rfl
-/
theorem centroid_def (p : ι -> P) : s.centroid k p = s.affineCombination k p (s.centroidWeights k) :=
  rfl

/--
theorem `centroid_univ` / 定理 `centroid_univ`

English:
theorem centroid_univ
  given: (s : Finset P)
  statement: univ.centroid k ((↑) : s -> P) = s.centroid k id
  proof: by
  rw [centroid]; rw [centroid]; rw [← s.attach_affineCombination_coe]
  congr
  ext
  simp

中文:
定理 centroid_univ
  条件: (s : 有限集 P)
  结论: univ.centroid k ((↑) : s -> P) = s.centroid k id
  证明: by
  rw [centroid]; rw [centroid]; rw [← s.attach_affineCombination_coe]
  congr
  ext
  simp

Depends on / 依赖: attach_affineCombination_coe, centroid, s.attach_affineCombination_coe
-/
theorem centroid_univ (s : Finset P) : univ.centroid k ((↑) : s -> P) = s.centroid k id := by
  rw [centroid]; rw [centroid]; rw [← s.attach_affineCombination_coe]
  congr
  ext
  simp

/-- The centroid of a single point. -/
@[simp]
/--
theorem `centroid_singleton` / 定理 `centroid_singleton`

English:
theorem centroid_singleton
  given: (p : ι -> P) (i : ι)
  statement: ({i} : Finset ι).centroid k p = p i
  proof: by
  simp [centroid_def, affineCombination_apply]

中文:
定理 centroid_singleton
  条件: (p : ι -> P) (i : ι)
  结论: ({i} : 有限集 ι).centroid k p = p i
  证明: by
  simp [centroid_def, affineCombination_apply]

Depends on / 依赖: affineCombination_apply, centroid_def
-/
theorem centroid_singleton (p : ι -> P) (i : ι) : ({i} : Finset ι).centroid k p = p i := by
  simp [centroid_def, affineCombination_apply]

/--
theorem `centroid_pair` / 定理 `centroid_pair`

English:
theorem centroid_pair
  given: [DecidableEq ι] [Invertible (2 : k)] (p : ι -> P) (i₁ i₂ : ι)
  proof: by
  by_cases h : i₁ = i₂
  · simp [h]
  · have hc : (#{i₁, i₂} : k) != 0 := by
      rw [card_insert_of_notMem (notMem_singleton.2 h)]; rw [card_singleton]
      simpa using Invertible.ne_zero _
    rw [centroid_def]; rw [affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ _ _
        (sum_centroidWeights_eq_one_of_cast_card_ne_zero _ hc) (p i₁)]
    simp [h, one_add_one_eq_two]

中文:
定理 centroid_pair
  条件: [DecidableEq ι] [可逆 (2 : k)] (p : ι -> P) (i₁ i₂ : ι)
  证明: by
  by_cases h : i₁ = i₂
  · simp [h]
  · have hc : (#{i₁, i₂} : k) != 0 := by
      rw [card_insert_of_notMem (notMem_singleton.2 h)]; rw [card_singleton]
      simpa using Invertible.ne_zero _
    rw [centroid_def]; rw [affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ _ _
        (sum_centroidWeights_eq_one_of_cast_card_ne_zero _ hc) (p i₁)]
    simp [h, one_add_one_eq_two]

Depends on / 依赖: Invertible, Invertible.ne_zero, affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one, card_insert_of_notMem, card_singleton, centroid_def, ne_zero, notMem_singleton, one_add_one_eq_two, sum_centroidWeights_eq_one_of_cast_card_ne_zero
-/
theorem centroid_pair [DecidableEq ι] [Invertible (2 : k)] (p : ι -> P) (i₁ i₂ : ι) :
    ({i₁, i₂} : Finset ι).centroid k p = (2⁻¹ : k) • (p i₂ -ᵥ p i₁) +ᵥ p i₁ := by
  by_cases h : i₁ = i₂
  · simp [h]
  · have hc : (#{i₁, i₂} : k) != 0 := by
      rw [card_insert_of_notMem (notMem_singleton.2 h)]; rw [card_singleton]
      simpa using Invertible.ne_zero _
    rw [centroid_def]; rw [affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ _ _
        (sum_centroidWeights_eq_one_of_cast_card_ne_zero _ hc) (p i₁)]
    simp [h, one_add_one_eq_two]

/--
theorem `centroid_pair_fin` / 定理 `centroid_pair_fin`

English:
theorem centroid_pair_fin
  given: [Invertible (2 : k)] (p : Fin 2 -> P)
  proof: by
  rw [univ_fin2]
  convert! centroid_pair k p 0 1

中文:
定理 centroid_pair_fin
  条件: [可逆 (2 : k)] (p : 有限集 2 -> P)
  证明: by
  rw [univ_fin2]
  convert! centroid_pair k p 0 1

Depends on / 依赖: centroid_pair, convert, univ_fin2
-/
theorem centroid_pair_fin [Invertible (2 : k)] (p : Fin 2 -> P) :
    univ.centroid k p = (2⁻¹ : k) • (p 1 -ᵥ p 0) +ᵥ p 0 := by
  rw [univ_fin2]
  convert! centroid_pair k p 0 1

/--
theorem `centroid_map` / 定理 `centroid_map`

English:
theorem centroid_map
  given: (e : ι₂ ↪ ι) (p : ι -> P)
  proof: by
  simp [centroid_def, affineCombination_map, centroidWeights]

中文:
定理 centroid_map
  条件: (e : ι₂ ↪ ι) (p : ι -> P)
  证明: by
  simp [centroid_def, affineCombination_map, centroidWeights]

Depends on / 依赖: affineCombination_map, centroidWeights, centroid_def
-/
theorem centroid_map (e : ι₂ ↪ ι) (p : ι -> P) :
    (s₂.map e).centroid k p = s₂.centroid k (p ∘ e) := by
  simp [centroid_def, affineCombination_map, centroidWeights]

/--
Definition of `centroidWeightsIndicator` / `centroidWeightsIndicator` 的定义

English:
definition centroidWeightsIndicator
  signature: : ι -> k
  body: Set.indicator (↑s) (s.centroidWeights k)

中文:
定义 centroidWeightsIndicator
  签名: : ι -> k
  定义体: Set.indicator (↑s) (s.centroidWeights k)

Depends on / 依赖: Set.indicator, centroidWeights, indicator, s.centroidWeights
-/
def centroidWeightsIndicator : ι -> k :=
  Set.indicator (↑s) (s.centroidWeights k)

/--
theorem `centroidWeightsIndicator_def` / 定理 `centroidWeightsIndicator_def`

English:
theorem centroidWeightsIndicator_def
  proof: rfl

中文:
定理 centroidWeightsIndicator_def
  证明: rfl
-/
theorem centroidWeightsIndicator_def :
    s.centroidWeightsIndicator k = Set.indicator (↑s) (s.centroidWeights k) :=
  rfl

/--
theorem `sum_centroidWeightsIndicator` / 定理 `sum_centroidWeightsIndicator`

English:
theorem sum_centroidWeightsIndicator
  given: [Fintype ι]
  proof: sum_indicator_subset _ (subset_univ _)

中文:
定理 sum_centroidWeightsIndicator
  条件: [有限类型 ι]
  证明: sum_indicator_subset _ (subset_univ _)

Depends on / 依赖: subset_univ, sum_indicator_subset
-/
theorem sum_centroidWeightsIndicator [Fintype ι] :
    ∑ i, s.centroidWeightsIndicator k i = ∑ i in s, s.centroidWeights k i :=
  sum_indicator_subset _ (subset_univ _)

/--
theorem `sum_centroidWeightsIndicator_eq_one_of_card_ne_zero` / 定理 `sum_centroidWeightsIndicator_eq_one_of_card_ne_zero`

English:
theorem sum_centroidWeightsIndicator_eq_one_of_card_ne_zero
  statement: [CharZero k] [Fintype ι]
  proof: by
  rw [sum_centroidWeightsIndicator]
  exact s.sum_centroidWeights_eq_one_of_card_ne_zero k h

中文:
定理 sum_centroidWeightsIndicator_eq_one_of_card_ne_zero
  结论: [特征零 k] [有限类型 ι]
  证明: by
  rw [sum_centroidWeightsIndicator]
  exact s.sum_centroidWeights_eq_one_of_card_ne_zero k h

Depends on / 依赖: s.sum_centroidWeights_eq_one_of_card_ne_zero, sum_centroidWeightsIndicator, sum_centroidWeights_eq_one_of_card_ne_zero
-/
theorem sum_centroidWeightsIndicator_eq_one_of_card_ne_zero [CharZero k] [Fintype ι]
    (h : #s != 0) : ∑ i, s.centroidWeightsIndicator k i = 1 := by
  rw [sum_centroidWeightsIndicator]
  exact s.sum_centroidWeights_eq_one_of_card_ne_zero k h

/--
theorem `sum_centroidWeightsIndicator_eq_one_of_nonempty` / 定理 `sum_centroidWeightsIndicator_eq_one_of_nonempty`

English:
theorem sum_centroidWeightsIndicator_eq_one_of_nonempty
  given: [CharZero k] [Fintype ι] (h : s.Nonempty)
  proof: by
  rw [sum_centroidWeightsIndicator]
  exact s.sum_centroidWeights_eq_one_of_nonempty k h

中文:
定理 sum_centroidWeightsIndicator_eq_one_of_nonempty
  条件: [特征零 k] [有限类型 ι] (h : s.非空)
  证明: by
  rw [sum_centroidWeightsIndicator]
  exact s.sum_centroidWeights_eq_one_of_nonempty k h

Depends on / 依赖: s.sum_centroidWeights_eq_one_of_nonempty, sum_centroidWeightsIndicator, sum_centroidWeights_eq_one_of_nonempty
-/
theorem sum_centroidWeightsIndicator_eq_one_of_nonempty [CharZero k] [Fintype ι] (h : s.Nonempty) :
    ∑ i, s.centroidWeightsIndicator k i = 1 := by
  rw [sum_centroidWeightsIndicator]
  exact s.sum_centroidWeights_eq_one_of_nonempty k h

/--
theorem `sum_centroidWeightsIndicator_eq_one_of_card_eq_add_one` / 定理 `sum_centroidWeightsIndicator_eq_one_of_card_eq_add_one`

English:
theorem sum_centroidWeightsIndicator_eq_one_of_card_eq_add_one
  statement: [CharZero k] [Fintype ι] {n : Nat}
  proof: by
  rw [sum_centroidWeightsIndicator]
  exact s.sum_centroidWeights_eq_one_of_card_eq_add_one k h

中文:
定理 sum_centroidWeightsIndicator_eq_one_of_card_eq_add_one
  结论: [特征零 k] [有限类型 ι] {n : 自然数}
  证明: by
  rw [sum_centroidWeightsIndicator]
  exact s.sum_centroidWeights_eq_one_of_card_eq_add_one k h

Depends on / 依赖: s.sum_centroidWeights_eq_one_of_card_eq_add_one, sum_centroidWeightsIndicator, sum_centroidWeights_eq_one_of_card_eq_add_one
-/
theorem sum_centroidWeightsIndicator_eq_one_of_card_eq_add_one [CharZero k] [Fintype ι] {n : Nat}
    (h : #s = n + 1) : ∑ i, s.centroidWeightsIndicator k i = 1 := by
  rw [sum_centroidWeightsIndicator]
  exact s.sum_centroidWeights_eq_one_of_card_eq_add_one k h

/--
theorem `centroid_eq_affineCombination_fintype` / 定理 `centroid_eq_affineCombination_fintype`

English:
theorem centroid_eq_affineCombination_fintype
  given: [Fintype ι] (p : ι -> P)
  proof: affineCombination_indicator_subset _ _ (subset_univ _)

中文:
定理 centroid_eq_affineCombination_fintype
  条件: [有限类型 ι] (p : ι -> P)
  证明: affineCombination_indicator_subset _ _ (subset_univ _)

Depends on / 依赖: affineCombination_indicator_subset, subset_univ
-/
theorem centroid_eq_affineCombination_fintype [Fintype ι] (p : ι -> P) :
    s.centroid k p = univ.affineCombination k p (s.centroidWeightsIndicator k) :=
  affineCombination_indicator_subset _ _ (subset_univ _)

/--
theorem `centroid_eq_centroid_image_of_inj_on` / 定理 `centroid_eq_centroid_image_of_inj_on`

English:
theorem centroid_eq_centroid_image_of_inj_on
  statement: {p : ι -> P}
  proof: by
  let f : p '' ↑s -> ι := fun x => x.property.choose
  have hf : forall x, f x in s ∧ p (f x) = x := fun x => x.property.choose_spec
  let f' : ps -> ι := fun x => f ⟨x, hps ▸ x.property⟩
  have hf' : forall x, f' x in s ∧ p (f' x) = x := fun x => hf ⟨x, hps ▸ x.property⟩
  have hf'i : Function.Injective f' := by
    intro x y h
    rw [Subtype.ext_iff]; rw [← (hf' x).2]; rw [← (hf' y).2]; rw [h]
  let f'e : ps ↪ ι := ⟨f', hf'i⟩
  have hu : Finset.univ.map f'e = s := by
    ext x
    rw [mem_map]
    constructor
    · rintro ⟨i, _, rfl⟩
      exact (hf' i).1
    · intro hx
      use ⟨p x, hps.symm ▸ Set.mem_image_of_mem _ hx⟩, mem_univ _
      refine hi _ (hf' _).1 _ hx ?_
      rw [(hf' _).2]
  rw [← hu]; rw [centroid_map]
  congr with x
  change p (f' x) = ↑x
  rw [(hf' x).2]

中文:
定理 centroid_eq_centroid_image_of_inj_on
  结论: {p : ι -> P}
  证明: by
  let f : p '' ↑s -> ι := fun x => x.property.choose
  have hf : forall x, f x in s ∧ p (f x) = x := fun x => x.property.choose_spec
  let f' : ps -> ι := fun x => f ⟨x, hps ▸ x.property⟩
  have hf' : forall x, f' x in s ∧ p (f' x) = x := fun x => hf ⟨x, hps ▸ x.property⟩
  have hf'i : Function.Injective f' := by
    intro x y h
    rw [Subtype.ext_iff]; rw [← (hf' x).2]; rw [← (hf' y).2]; rw [h]
  let f'e : ps ↪ ι := ⟨f', hf'i⟩
  have hu : Finset.univ.map f'e = s := by
    ext x
    rw [mem_map]
    constructor
    · rintro ⟨i, _, rfl⟩
      exact (hf' i).1
    · intro hx
      use ⟨p x, hps.symm ▸ Set.mem_image_of_mem _ hx⟩, mem_univ _
      refine hi _ (hf' _).1 _ hx ?_
      rw [(hf' _).2]
  rw [← hu]; rw [centroid_map]
  congr with x
  change p (f' x) = ↑x
  rw [(hf' x).2]

Depends on / 依赖: Finset, Finset.univ.map, Function, Function.Injective, Injective, Subtype, Subtype.ext_iff, choose_spec, ext_iff, mem_map, property, x.property, x.property.choose, x.property.choose_spec
-/
theorem centroid_eq_centroid_image_of_inj_on {p : ι -> P}
    (hi : forall i in s, forall j in s, p i = p j -> i = j) {ps : Set P} [Fintype ps]
    (hps : ps = p '' ↑s) : s.centroid k p = (univ : Finset ps).centroid k fun x => (x : P) := by
  let f : p '' ↑s -> ι := fun x => x.property.choose
  have hf : forall x, f x in s ∧ p (f x) = x := fun x => x.property.choose_spec
  let f' : ps -> ι := fun x => f ⟨x, hps ▸ x.property⟩
  have hf' : forall x, f' x in s ∧ p (f' x) = x := fun x => hf ⟨x, hps ▸ x.property⟩
  have hf'i : Function.Injective f' := by
    intro x y h
    rw [Subtype.ext_iff]; rw [← (hf' x).2]; rw [← (hf' y).2]; rw [h]
  let f'e : ps ↪ ι := ⟨f', hf'i⟩
  have hu : Finset.univ.map f'e = s := by
    ext x
    rw [mem_map]
    constructor
    · rintro ⟨i, _, rfl⟩
      exact (hf' i).1
    · intro hx
      use ⟨p x, hps.symm ▸ Set.mem_image_of_mem _ hx⟩, mem_univ _
      refine hi _ (hf' _).1 _ hx ?_
      rw [(hf' _).2]
  rw [← hu]; rw [centroid_map]
  congr with x
  change p (f' x) = ↑x
  rw [(hf' x).2]

/--
theorem `centroid_eq_of_inj_on_of_image_eq` / 定理 `centroid_eq_of_inj_on_of_image_eq`

English:
theorem centroid_eq_of_inj_on_of_image_eq
  statement: {p : ι -> P}
  proof: by
  classical rw [s.centroid_eq_centroid_image_of_inj_on k hi rfl,
      s₂.centroid_eq_centroid_image_of_inj_on k hi₂ he]

中文:
定理 centroid_eq_of_inj_on_of_image_eq
  结论: {p : ι -> P}
  证明: by
  classical rw [s.centroid_eq_centroid_image_of_inj_on k hi rfl,
      s₂.centroid_eq_centroid_image_of_inj_on k hi₂ he]

Depends on / 依赖: centroid_eq_centroid_image_of_inj_on, classical, s.centroid_eq_centroid_image_of_inj_on
-/
theorem centroid_eq_of_inj_on_of_image_eq {p : ι -> P}
    (hi : forall i in s, forall j in s, p i = p j -> i = j) {p₂ : ι₂ -> P}
    (hi₂ : forall i in s₂, forall j in s₂, p₂ i = p₂ j -> i = j) (he : p '' ↑s = p₂ '' ↑s₂) :
    s.centroid k p = s₂.centroid k p₂ := by
  classical rw [s.centroid_eq_centroid_image_of_inj_on k hi rfl,
      s₂.centroid_eq_centroid_image_of_inj_on k hi₂ he]

/--
theorem `centroid_vsub_const` / 定理 `centroid_vsub_const`

English:
theorem centroid_vsub_const
  given: [CharZero k] {p : ι -> P} {p₀ : P} (hs : s.Nonempty)
  proof: by
  have h := s.sum_centroidWeights_eq_one_of_nonempty k hs
  simp only [centroid_def]
  grind [sum_smul_vsub_const_eq_affineCombination_vsub, affineCombination_eq_linear_combination]

中文:
定理 centroid_vsub_const
  条件: [特征零 k] {p : ι -> P} {p₀ : P} (hs : s.非空)
  证明: by
  have h := s.sum_centroidWeights_eq_one_of_nonempty k hs
  simp only [centroid_def]
  grind [sum_smul_vsub_const_eq_affineCombination_vsub, affineCombination_eq_linear_combination]

Depends on / 依赖: affineCombination_eq_linear_combination, centroid_def, s.sum_centroidWeights_eq_one_of_nonempty, sum_centroidWeights_eq_one_of_nonempty, sum_smul_vsub_const_eq_affineCombination_vsub
-/
theorem centroid_vsub_const [CharZero k] {p : ι -> P} {p₀ : P} (hs : s.Nonempty) :
    Finset.centroid k s p -ᵥ p₀ = Finset.centroid k s (fun i => p i -ᵥ p₀) := by
  have h := s.sum_centroidWeights_eq_one_of_nonempty k hs
  simp only [centroid_def]
  grind [sum_smul_vsub_const_eq_affineCombination_vsub, affineCombination_eq_linear_combination]

end Finset

section DivisionRing

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
variable [AffineSpace V P] {ι : Type*}

open Set Finset

/--
theorem `centroid_mem_affineSpan_of_cast_card_ne_zero` / 定理 `centroid_mem_affineSpan_of_cast_card_ne_zero`

English:
theorem centroid_mem_affineSpan_of_cast_card_ne_zero
  statement: {s : Finset ι} (p : ι -> P)
  proof: affineCombination_mem_affineSpan (s.sum_centroidWeights_eq_one_of_cast_card_ne_zero h) p

中文:
定理 centroid_mem_affineSpan_of_cast_card_ne_zero
  结论: {s : 有限集 ι} (p : ι -> P)
  证明: affineCombination_mem_affineSpan (s.sum_centroidWeights_eq_one_of_cast_card_ne_zero h) p

Depends on / 依赖: affineCombination_mem_affineSpan, s.sum_centroidWeights_eq_one_of_cast_card_ne_zero, sum_centroidWeights_eq_one_of_cast_card_ne_zero
-/
theorem centroid_mem_affineSpan_of_cast_card_ne_zero {s : Finset ι} (p : ι -> P)
    (h : (#s : k) != 0) : s.centroid k p in affineSpan k (range p) :=
  affineCombination_mem_affineSpan (s.sum_centroidWeights_eq_one_of_cast_card_ne_zero h) p

variable (k)

/--
theorem `centroid_mem_affineSpan_of_card_ne_zero` / 定理 `centroid_mem_affineSpan_of_card_ne_zero`

English:
theorem centroid_mem_affineSpan_of_card_ne_zero
  statement: [CharZero k] {s : Finset ι} (p : ι -> P)
  proof: affineCombination_mem_affineSpan (s.sum_centroidWeights_eq_one_of_card_ne_zero k h) p

中文:
定理 centroid_mem_affineSpan_of_card_ne_zero
  结论: [特征零 k] {s : 有限集 ι} (p : ι -> P)
  证明: affineCombination_mem_affineSpan (s.sum_centroidWeights_eq_one_of_card_ne_zero k h) p

Depends on / 依赖: affineCombination_mem_affineSpan, s.sum_centroidWeights_eq_one_of_card_ne_zero, sum_centroidWeights_eq_one_of_card_ne_zero
-/
theorem centroid_mem_affineSpan_of_card_ne_zero [CharZero k] {s : Finset ι} (p : ι -> P)
    (h : #s != 0) : s.centroid k p in affineSpan k (range p) :=
  affineCombination_mem_affineSpan (s.sum_centroidWeights_eq_one_of_card_ne_zero k h) p

/--
theorem `centroid_mem_affineSpan_of_nonempty` / 定理 `centroid_mem_affineSpan_of_nonempty`

English:
theorem centroid_mem_affineSpan_of_nonempty
  statement: [CharZero k] {s : Finset ι} (p : ι -> P)
  proof: affineCombination_mem_affineSpan (s.sum_centroidWeights_eq_one_of_nonempty k h) p

中文:
定理 centroid_mem_affineSpan_of_nonempty
  结论: [特征零 k] {s : 有限集 ι} (p : ι -> P)
  证明: affineCombination_mem_affineSpan (s.sum_centroidWeights_eq_one_of_nonempty k h) p

Depends on / 依赖: affineCombination_mem_affineSpan, s.sum_centroidWeights_eq_one_of_nonempty, sum_centroidWeights_eq_one_of_nonempty
-/
theorem centroid_mem_affineSpan_of_nonempty [CharZero k] {s : Finset ι} (p : ι -> P)
    (h : s.Nonempty) : s.centroid k p in affineSpan k (range p) :=
  affineCombination_mem_affineSpan (s.sum_centroidWeights_eq_one_of_nonempty k h) p

/--
theorem `centroid_mem_affineSpan_of_card_eq_add_one` / 定理 `centroid_mem_affineSpan_of_card_eq_add_one`

English:
theorem centroid_mem_affineSpan_of_card_eq_add_one
  statement: [CharZero k] {s : Finset ι} (p : ι -> P) {n : Nat}
  proof: affineCombination_mem_affineSpan (s.sum_centroidWeights_eq_one_of_card_eq_add_one k h) p

中文:
定理 centroid_mem_affineSpan_of_card_eq_add_one
  结论: [特征零 k] {s : 有限集 ι} (p : ι -> P) {n : 自然数}
  证明: affineCombination_mem_affineSpan (s.sum_centroidWeights_eq_one_of_card_eq_add_one k h) p

Depends on / 依赖: affineCombination_mem_affineSpan, s.sum_centroidWeights_eq_one_of_card_eq_add_one, sum_centroidWeights_eq_one_of_card_eq_add_one
-/
theorem centroid_mem_affineSpan_of_card_eq_add_one [CharZero k] {s : Finset ι} (p : ι -> P) {n : Nat}
    (h : #s = n + 1) : s.centroid k p in affineSpan k (range p) :=
  affineCombination_mem_affineSpan (s.sum_centroidWeights_eq_one_of_card_eq_add_one k h) p

end DivisionRing
