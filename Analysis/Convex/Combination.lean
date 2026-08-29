/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.LinearAlgebra.AffineSpace.Basis
public import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic

/-!
# Convex combinations

This file defines convex combinations of points in a vector space.

## Main declarations

* `Finset.centerMass`: Center of mass of a finite family of points.

## Implementation notes

We divide by the sum of the weights in the definition of `Finset.centerMass` because of the way
mathematical arguments go: one doesn't change weights, but merely adds some. This also makes a few
lemmas unconditional on the sum of the weights being `1`.
-/

@[expose] public section

assert_not_exists Cardinal

open Set Function Pointwise

universe u u'

section
variable {R R' E F ι ι' α : Type*} [Field R] [Field R'] [AddCommGroup E] [AddCommGroup F]
  [AddCommGroup α] [LinearOrder α] [Module R E] [Module R F] [Module R α] {s : Set E}

/--
Definition of `Finset.centerMass` / `Finset.centerMass` 的定义

English:
definition Finset.centerMass
  signature: (t : Finset ι) (w : ι -> R) (z : ι -> E)
  body: (∑ i in t, w i)⁻¹ • ∑ i in t, w i • z i

中文:
定义 有限集.centerMass
  签名: (t : 有限集 ι) (w : ι -> R) (z : ι -> E)
  定义体: (∑ i in t, w i)⁻¹ • ∑ i in t, w i • z i
-/
def Finset.centerMass (t : Finset ι) (w : ι -> R) (z : ι -> E) : E :=
  (∑ i in t, w i)⁻¹ • ∑ i in t, w i • z i

variable (i j : ι) (c : R) (t : Finset ι) (w : ι -> R) (z : ι -> E)

open Finset

/--
theorem `Finset.centerMass_empty` / 定理 `Finset.centerMass_empty`

English:
theorem Finset.centerMass_empty
  statement: (∅ : Finset ι).centerMass w z = 0
  proof: by
  simp only [centerMass, sum_empty, smul_zero]

中文:
定理 有限集.centerMass_empty
  结论: (∅ : 有限集 ι).centerMass w z = 0
  证明: by
  simp only [centerMass, sum_empty, smul_zero]

Depends on / 依赖: centerMass, smul_zero, sum_empty
-/
theorem Finset.centerMass_empty : (∅ : Finset ι).centerMass w z = 0 := by
  simp only [centerMass, sum_empty, smul_zero]

/--
theorem `Finset.centerMass_pair` / 定理 `Finset.centerMass_pair`

English:
theorem Finset.centerMass_pair
  given: [DecidableEq ι] (hne : i != j)
  proof: by
  simp only [centerMass, sum_pair hne]
  module

中文:
定理 有限集.centerMass_pair
  条件: [DecidableEq ι] (hne : i != j)
  证明: by
  simp only [centerMass, sum_pair hne]
  module

Depends on / 依赖: centerMass, module, sum_pair
-/
theorem Finset.centerMass_pair [DecidableEq ι] (hne : i != j) :
    ({i, j} : Finset ι).centerMass w z = (w i / (w i + w j)) • z i + (w j / (w i + w j)) • z j := by
  simp only [centerMass, sum_pair hne]
  module

variable {w}

/--
theorem `Finset.centerMass_insert` / 定理 `Finset.centerMass_insert`

English:
theorem Finset.centerMass_insert
  given: [DecidableEq ι] (ha : i ∉ t) (hw : ∑ j in t, w j != 0)
  proof: by
  simp only [centerMass, sum_insert ha, smul_add, (mul_smul _ _ _).symm, ← div_eq_inv_mul]
  congr 2
  rw [div_mul_eq_mul_div]; rw [mul_inv_cancel₀ hw]; rw [one_div]

中文:
定理 有限集.centerMass_insert
  条件: [DecidableEq ι] (ha : i ∉ t) (hw : ∑ j in t, w j != 0)
  证明: by
  simp only [centerMass, sum_insert ha, smul_add, (mul_smul _ _ _).symm, ← div_eq_inv_mul]
  congr 2
  rw [div_mul_eq_mul_div]; rw [mul_inv_cancel₀ hw]; rw [one_div]

Depends on / 依赖: centerMass, div_eq_inv_mul, div_mul_eq_mul_div, mul_smul, one_div, smul_add, sum_insert
-/
theorem Finset.centerMass_insert [DecidableEq ι] (ha : i ∉ t) (hw : ∑ j in t, w j != 0) :
    (insert i t).centerMass w z =
      (w i / (w i + ∑ j in t, w j)) • z i +
        ((∑ j in t, w j) / (w i + ∑ j in t, w j)) • t.centerMass w z := by
  simp only [centerMass, sum_insert ha, smul_add, (mul_smul _ _ _).symm, ← div_eq_inv_mul]
  congr 2
  rw [div_mul_eq_mul_div]; rw [mul_inv_cancel₀ hw]; rw [one_div]

/--
theorem `Finset.centerMass_singleton` / 定理 `Finset.centerMass_singleton`

English:
theorem Finset.centerMass_singleton
  given: (hw : w i != 0)
  statement: ({i} : Finset ι).centerMass w z = z i
  proof: by
  rw [centerMass]; rw [sum_singleton]; rw [sum_singleton]
  match_scalars
  field

中文:
定理 有限集.centerMass_singleton
  条件: (hw : w i != 0)
  结论: ({i} : 有限集 ι).centerMass w z = z i
  证明: by
  rw [centerMass]; rw [sum_singleton]; rw [sum_singleton]
  match_scalars
  field

Depends on / 依赖: centerMass, match_scalars, sum_singleton
-/
theorem Finset.centerMass_singleton (hw : w i != 0) : ({i} : Finset ι).centerMass w z = z i := by
  rw [centerMass]; rw [sum_singleton]; rw [sum_singleton]
  match_scalars
  field

/--
lemma `Finset.centerMass_neg_left` / 引理 `Finset.centerMass_neg_left`

English:
lemma Finset.centerMass_neg_left
  statement: t.centerMass (-w) z = t.centerMass w z
  proof: by
  simp [centerMass, inv_neg]

中文:
引理 有限集.centerMass_neg_left
  结论: t.centerMass (-w) z = t.centerMass w z
  证明: by
  simp [centerMass, inv_neg]
-/
@[simp] lemma Finset.centerMass_neg_left : t.centerMass (-w) z = t.centerMass w z := by
  simp [centerMass, inv_neg]

/--
lemma `Finset.centerMass_smul_left` / 引理 `Finset.centerMass_smul_left`

English:
lemma Finset.centerMass_smul_left
  statement: {c : R'} [Module R' R] [Module R' E] [SMulCommClass R' R R]
  proof: by
  simp [centerMass, -smul_assoc, smul_assoc c, ← smul_sum, smul_inv₀, smul_smul_smul_comm, hc]

中文:
引理 有限集.centerMass_smul_left
  结论: {c : R'} [模 R' R] [模 R' E] [标量交换类 R' R R]
  证明: by
  simp [centerMass, -smul_assoc, smul_assoc c, ← smul_sum, smul_inv₀, smul_smul_smul_comm, hc]

Depends on / 依赖: centerMass, smul_assoc, smul_smul_smul_comm, smul_sum
-/
lemma Finset.centerMass_smul_left {c : R'} [Module R' R] [Module R' E] [SMulCommClass R' R R]
    [IsScalarTower R' R R] [SMulCommClass R R' E] [IsScalarTower R' R E] (hc : c != 0) :
    t.centerMass (c • w) z = t.centerMass w z := by
  simp [centerMass, -smul_assoc, smul_assoc c, ← smul_sum, smul_inv₀, smul_smul_smul_comm, hc]

/--
theorem `Finset.centerMass_eq_of_sum_1` / 定理 `Finset.centerMass_eq_of_sum_1`

English:
theorem Finset.centerMass_eq_of_sum_1
  given: (hw : ∑ i in t, w i = 1)
  proof: by
  simp only [Finset.centerMass, hw, inv_one, one_smul]

中文:
定理 有限集.centerMass_eq_of_sum_1
  条件: (hw : ∑ i in t, w i = 1)
  证明: by
  simp only [Finset.centerMass, hw, inv_one, one_smul]

Depends on / 依赖: Finset, Finset.centerMass, centerMass, inv_one, one_smul
-/
theorem Finset.centerMass_eq_of_sum_1 (hw : ∑ i in t, w i = 1) :
    t.centerMass w z = ∑ i in t, w i • z i := by
  simp only [Finset.centerMass, hw, inv_one, one_smul]

/--
theorem `Finset.centerMass_smul` / 定理 `Finset.centerMass_smul`

English:
theorem Finset.centerMass_smul
  statement: (t.centerMass w fun i => c • z i) = c • t.centerMass w z
  proof: by
  simp only [Finset.centerMass, Finset.smul_sum, (mul_smul _ _ _).symm, mul_comm c, mul_assoc]

中文:
定理 有限集.centerMass_smul
  结论: (t.centerMass w fun i => c • z i) = c • t.centerMass w z
  证明: by
  simp only [Finset.centerMass, Finset.smul_sum, (mul_smul _ _ _).symm, mul_comm c, mul_assoc]

Depends on / 依赖: Finset, Finset.centerMass, Finset.smul_sum, centerMass, mul_assoc, mul_comm, mul_smul, smul_sum
-/
theorem Finset.centerMass_smul : (t.centerMass w fun i => c • z i) = c • t.centerMass w z := by
  simp only [Finset.centerMass, Finset.smul_sum, (mul_smul _ _ _).symm, mul_comm c, mul_assoc]

/--
theorem `Finset.centerMass_segment'` / 定理 `Finset.centerMass_segment'`

English:
theorem Finset.centerMass_segment'
  statement: (s : Finset ι) (t : Finset ι') (ws : ι -> R) (zs : ι -> E)
  proof: by
  rw [s.centerMass_eq_of_sum_1 _ hws]; rw [t.centerMass_eq_of_sum_1 _ hwt]; rw [smul_sum]; rw [smul_sum]; rw [←
    Finset.sum_sumElim]; rw [Finset.centerMass_eq_of_sum_1]
  · congr with ⟨⟩ <;> simp only [Sum.elim_inl, Sum.elim_inr, mul_smul]
  · rw [sum_sumElim, ← mul_sum, ← mul_sum, hws, hwt, mul_one, mul_one, hab]

中文:
定理 有限集.centerMass_segment'
  结论: (s : 有限集 ι) (t : 有限集 ι') (ws : ι -> R) (zs : ι -> E)
  证明: by
  rw [s.centerMass_eq_of_sum_1 _ hws]; rw [t.centerMass_eq_of_sum_1 _ hwt]; rw [smul_sum]; rw [smul_sum]; rw [←
    Finset.sum_sumElim]; rw [Finset.centerMass_eq_of_sum_1]
  · congr with ⟨⟩ <;> simp only [Sum.elim_inl, Sum.elim_inr, mul_smul]
  · rw [sum_sumElim, ← mul_sum, ← mul_sum, hws, hwt, mul_one, mul_one, hab]

Depends on / 依赖: Finset, Finset.centerMass_eq_of_sum_1, Finset.sum_sumElim, Sum.elim_inl, Sum.elim_inr, centerMass_eq_of_sum_1, elim_inl, elim_inr, mul_one, mul_smul, mul_sum, s.centerMass_eq_of_sum_1, smul_sum, sum_sumElim, t.centerMass_eq_of_sum_1
-/
theorem Finset.centerMass_segment' (s : Finset ι) (t : Finset ι') (ws : ι -> R) (zs : ι -> E)
    (wt : ι' -> R) (zt : ι' -> E) (hws : ∑ i in s, ws i = 1) (hwt : ∑ i in t, wt i = 1) (a b : R)
    (hab : a + b = 1) : a • s.centerMass ws zs + b • t.centerMass wt zt = (s.disjSum t).centerMass
    (Sum.elim (fun i => a * ws i) fun j => b * wt j) (Sum.elim zs zt) := by
  rw [s.centerMass_eq_of_sum_1 _ hws]; rw [t.centerMass_eq_of_sum_1 _ hwt]; rw [smul_sum]; rw [smul_sum]; rw [←
    Finset.sum_sumElim]; rw [Finset.centerMass_eq_of_sum_1]
  · congr with ⟨⟩ <;> simp only [Sum.elim_inl, Sum.elim_inr, mul_smul]
  · rw [sum_sumElim, ← mul_sum, ← mul_sum, hws, hwt, mul_one, mul_one, hab]

/--
theorem `Finset.centerMass_segment` / 定理 `Finset.centerMass_segment`

English:
theorem Finset.centerMass_segment
  statement: (s : Finset ι) (w₁ w₂ : ι -> R) (z : ι -> E)
  proof: by
  have hw : (∑ i in s, (a * w₁ i + b * w₂ i)) = 1 := by
    simp only [← mul_sum, sum_add_distrib, mul_one, *]
  simp only [Finset.centerMass_eq_of_sum_1, smul_sum, sum_add_distrib, add_smul, mul_smul, *]

中文:
定理 有限集.centerMass_segment
  结论: (s : 有限集 ι) (w₁ w₂ : ι -> R) (z : ι -> E)
  证明: by
  have hw : (∑ i in s, (a * w₁ i + b * w₂ i)) = 1 := by
    simp only [← mul_sum, sum_add_distrib, mul_one, *]
  simp only [Finset.centerMass_eq_of_sum_1, smul_sum, sum_add_distrib, add_smul, mul_smul, *]

Depends on / 依赖: Finset, Finset.centerMass_eq_of_sum_1, add_smul, centerMass_eq_of_sum_1, mul_one, mul_smul, mul_sum, smul_sum, sum_add_distrib
-/
theorem Finset.centerMass_segment (s : Finset ι) (w₁ w₂ : ι -> R) (z : ι -> E)
    (hw₁ : ∑ i in s, w₁ i = 1) (hw₂ : ∑ i in s, w₂ i = 1) (a b : R) (hab : a + b = 1) :
    a • s.centerMass w₁ z + b • s.centerMass w₂ z =
    s.centerMass (fun i => a * w₁ i + b * w₂ i) z := by
  have hw : (∑ i in s, (a * w₁ i + b * w₂ i)) = 1 := by
    simp only [← mul_sum, sum_add_distrib, mul_one, *]
  simp only [Finset.centerMass_eq_of_sum_1, smul_sum, sum_add_distrib, add_smul, mul_smul, *]

/--
theorem `Finset.centerMass_ite_eq` / 定理 `Finset.centerMass_ite_eq`

English:
theorem Finset.centerMass_ite_eq
  given: [DecidableEq ι] (hi : i in t)
  proof: by
  rw [Finset.centerMass_eq_of_sum_1]
  · trans ∑ j in t, if i = j then z i else 0
    · congr with i
      split_ifs with h
      exacts [h ▸ one_smul _ _, zero_smul _ _]
    · rw [sum_ite_eq, if_pos hi]
  · rw [sum_ite_eq, if_pos hi]

中文:
定理 有限集.centerMass_ite_eq
  条件: [DecidableEq ι] (hi : i in t)
  证明: by
  rw [Finset.centerMass_eq_of_sum_1]
  · trans ∑ j in t, if i = j then z i else 0
    · congr with i
      split_ifs with h
      exacts [h ▸ one_smul _ _, zero_smul _ _]
    · rw [sum_ite_eq, if_pos hi]
  · rw [sum_ite_eq, if_pos hi]

Depends on / 依赖: Finset, Finset.centerMass_eq_of_sum_1, centerMass_eq_of_sum_1, exacts, if_pos, one_smul, split_ifs, sum_ite_eq, zero_smul
-/
theorem Finset.centerMass_ite_eq [DecidableEq ι] (hi : i in t) :
    t.centerMass (fun j => if i = j then (1 : R) else 0) z = z i := by
  rw [Finset.centerMass_eq_of_sum_1]
  · trans ∑ j in t, if i = j then z i else 0
    · congr with i
      split_ifs with h
      exacts [h ▸ one_smul _ _, zero_smul _ _]
    · rw [sum_ite_eq, if_pos hi]
  · rw [sum_ite_eq, if_pos hi]

variable {t}

/--
theorem `Finset.centerMass_subset` / 定理 `Finset.centerMass_subset`

English:
theorem Finset.centerMass_subset
  given: {t' : Finset ι} (ht : t subseteq t') (h : forall i in t', i ∉ t -> w i = 0)
  proof: by
  rw [centerMass]; rw [sum_subset ht h]; rw [smul_sum]; rw [centerMass]; rw [smul_sum]
  apply sum_subset ht
  intro i hit' hit
  rw [h i hit' hit]; rw [zero_smul]; rw [smul_zero]

中文:
定理 有限集.centerMass_subset
  条件: {t' : 有限集 ι} (ht : t subseteq t') (h : 对任意 i in t', i ∉ t -> w i = 0)
  证明: by
  rw [centerMass]; rw [sum_subset ht h]; rw [smul_sum]; rw [centerMass]; rw [smul_sum]
  apply sum_subset ht
  intro i hit' hit
  rw [h i hit' hit]; rw [zero_smul]; rw [smul_zero]

Depends on / 依赖: centerMass, smul_sum, smul_zero, sum_subset, zero_smul
-/
theorem Finset.centerMass_subset {t' : Finset ι} (ht : t subseteq t') (h : forall i in t', i ∉ t -> w i = 0) :
    t.centerMass w z = t'.centerMass w z := by
  rw [centerMass]; rw [sum_subset ht h]; rw [smul_sum]; rw [centerMass]; rw [smul_sum]
  apply sum_subset ht
  intro i hit' hit
  rw [h i hit' hit]; rw [zero_smul]; rw [smul_zero]

/--
theorem `Finset.centerMass_filter_ne_zero` / 定理 `Finset.centerMass_filter_ne_zero`

English:
theorem Finset.centerMass_filter_ne_zero
  given: [forall i, Decidable (w i != 0)]
  proof: Finset.centerMass_subset z (filter_subset _ _) fun i hit hit' => by
    simpa only [hit, mem_filter, true_and, Ne, Classical.not_not] using hit'

中文:
定理 有限集.centerMass_filter_ne_zero
  条件: [对任意 i, 可判定 (w i != 0)]
  证明: Finset.centerMass_subset z (filter_subset _ _) fun i hit hit' => by
    simpa only [hit, mem_filter, true_and, Ne, Classical.not_not] using hit'

Depends on / 依赖: Classical, Classical.not_not, Finset, Finset.centerMass_subset, centerMass_subset, filter_subset, mem_filter, not_not, true_and
-/
theorem Finset.centerMass_filter_ne_zero [forall i, Decidable (w i != 0)] :
    {i in t | w i != 0}.centerMass w z = t.centerMass w z :=
  Finset.centerMass_subset z (filter_subset _ _) fun i hit hit' => by
    simpa only [hit, mem_filter, true_and, Ne, Classical.not_not] using hit'

namespace Finset

variable [LinearOrder R] [IsOrderedAddMonoid α] [PosSMulMono R α]

/--
theorem `centerMass_le_sup` / 定理 `centerMass_le_sup`

English:
theorem centerMass_le_sup
  statement: {s : Finset ι} {f : ι -> α} {w : ι -> R} (hw₀ : forall i in s, 0 <= w i)
  proof: by
  rw [centerMass]; rw [inv_smul_le_iff_of_pos hw₁]; rw [sum_smul]
exact sum_le_sum fun i hi => smul_le_smul_of_nonneg_left (le_sup' _ hi) hw₀ i hi

中文:
定理 centerMass_le_sup
  结论: {s : 有限集 ι} {f : ι -> α} {w : ι -> R} (hw₀ : 对任意 i in s, 0 <= w i)
  证明: by
  rw [centerMass]; rw [inv_smul_le_iff_of_pos hw₁]; rw [sum_smul]
exact sum_le_sum fun i hi => smul_le_smul_of_nonneg_left (le_sup' _ hi) hw₀ i hi

Depends on / 依赖: centerMass, inv_smul_le_iff_of_pos, le_sup, smul_le_smul_of_nonneg_left, sum_le_sum, sum_smul
-/
theorem centerMass_le_sup {s : Finset ι} {f : ι -> α} {w : ι -> R} (hw₀ : forall i in s, 0 <= w i)
    (hw₁ : 0 < ∑ i in s, w i) :
    s.centerMass w f <= s.sup' (nonempty_of_ne_empty <| by rintro rfl; simp at hw₁) f := by
  rw [centerMass]; rw [inv_smul_le_iff_of_pos hw₁]; rw [sum_smul]
exact sum_le_sum fun i hi => smul_le_smul_of_nonneg_left (le_sup' _ hi) hw₀ i hi

/--
theorem `inf_le_centerMass` / 定理 `inf_le_centerMass`

English:
theorem inf_le_centerMass
  statement: {s : Finset ι} {f : ι -> α} {w : ι -> R} (hw₀ : forall i in s, 0 <= w i)
  proof: centerMass_le_sup (α := αᵒᵈ) hw₀ hw₁

中文:
定理 inf_le_centerMass
  结论: {s : 有限集 ι} {f : ι -> α} {w : ι -> R} (hw₀ : 对任意 i in s, 0 <= w i)
  证明: centerMass_le_sup (α := αᵒᵈ) hw₀ hw₁

Depends on / 依赖: centerMass_le_sup
-/
theorem inf_le_centerMass {s : Finset ι} {f : ι -> α} {w : ι -> R} (hw₀ : forall i in s, 0 <= w i)
    (hw₁ : 0 < ∑ i in s, w i) :
    s.inf' (nonempty_of_ne_empty <| by rintro rfl; simp at hw₁) f <= s.centerMass w f :=
  centerMass_le_sup (α := αᵒᵈ) hw₀ hw₁

end Finset

variable {z}

/--
lemma `Finset.centerMass_const` / 引理 `Finset.centerMass_const`

English:
lemma Finset.centerMass_const
  given: (hw : ∑ j in t, w j != 0) (c : E)
  proof: by
  simp [centerMass, ← sum_smul, hw]

中文:
引理 有限集.centerMass_const
  条件: (hw : ∑ j in t, w j != 0) (c : E)
  证明: by
  simp [centerMass, ← sum_smul, hw]

Depends on / 依赖: centerMass, sum_smul
-/
lemma Finset.centerMass_const (hw : ∑ j in t, w j != 0) (c : E) :
    t.centerMass w (Function.const _ c) = c := by
  simp [centerMass, ← sum_smul, hw]

/--
lemma `Finset.centerMass_congr` / 引理 `Finset.centerMass_congr`

English:
lemma Finset.centerMass_congr
  statement: [DecidableEq ι] {t' : Finset ι} {w' : ι -> R} {z' : ι -> E}
  proof: by
  classical
  rw [← centerMass_filter_ne_zero]; rw [centerMass]; rw [← centerMass_filter_ne_zero]; rw [centerMass]
  congr 1
  · congr 1
    exact sum_congr (by grind) (by grind)
  · exact sum_congr (by grind) (by grind)

中文:
引理 有限集.centerMass_congr
  结论: [DecidableEq ι] {t' : 有限集 ι} {w' : ι -> R} {z' : ι -> E}
  证明: by
  classical
  rw [← centerMass_filter_ne_zero]; rw [centerMass]; rw [← centerMass_filter_ne_zero]; rw [centerMass]
  congr 1
  · congr 1
    exact sum_congr (by grind) (by grind)
  · exact sum_congr (by grind) (by grind)

Depends on / 依赖: centerMass, centerMass_filter_ne_zero, classical, sum_congr
-/
lemma Finset.centerMass_congr [DecidableEq ι] {t' : Finset ι} {w' : ι -> R} {z' : ι -> E}
    (h : forall i, (i in t ∧ w i != 0 ∨ i in t' ∧ w' i != 0) -> i in t inter t' ∧ w i = w' i ∧ z i = z' i) :
    t.centerMass w z = t'.centerMass w' z' := by
  classical
  rw [← centerMass_filter_ne_zero]; rw [centerMass]; rw [← centerMass_filter_ne_zero]; rw [centerMass]
  congr 1
  · congr 1
    exact sum_congr (by grind) (by grind)
  · exact sum_congr (by grind) (by grind)

/--
lemma `Finset.centerMass_congr_finset` / 引理 `Finset.centerMass_congr_finset`

English:
lemma Finset.centerMass_congr_finset
  statement: [DecidableEq ι] {t' : Finset ι}
  proof: centerMass_congr (by grind)

中文:
引理 有限集.centerMass_congr_finset
  结论: [DecidableEq ι] {t' : 有限集 ι}
  证明: centerMass_congr (by grind)

Depends on / 依赖: centerMass_congr
-/
lemma Finset.centerMass_congr_finset [DecidableEq ι] {t' : Finset ι}
    (h : forall i in t union t', w i != 0 -> i in t inter t') : t.centerMass w z = t'.centerMass w z :=
  centerMass_congr (by grind)

/--
lemma `Finset.centerMass_congr_weights` / 引理 `Finset.centerMass_congr_weights`

English:
lemma Finset.centerMass_congr_weights
  given: {w' : ι -> R} (h : forall i in t, w i = w' i)
  proof: by
  classical
  exact centerMass_congr (by grind)

中文:
引理 有限集.centerMass_congr_weights
  条件: {w' : ι -> R} (h : 对任意 i in t, w i = w' i)
  证明: by
  classical
  exact centerMass_congr (by grind)

Depends on / 依赖: centerMass_congr, classical
-/
lemma Finset.centerMass_congr_weights {w' : ι -> R} (h : forall i in t, w i = w' i) :
    t.centerMass w z = t.centerMass w' z := by
  classical
  exact centerMass_congr (by grind)

/--
lemma `Finset.centerMass_congr_fun` / 引理 `Finset.centerMass_congr_fun`

English:
lemma Finset.centerMass_congr_fun
  given: {z' : ι -> E} (h : forall i in t, w i != 0 -> z i = z' i)
  proof: by
  classical
  exact centerMass_congr (by grind)

中文:
引理 有限集.centerMass_congr_fun
  条件: {z' : ι -> E} (h : 对任意 i in t, w i != 0 -> z i = z' i)
  证明: by
  classical
  exact centerMass_congr (by grind)

Depends on / 依赖: centerMass_congr, classical
-/
lemma Finset.centerMass_congr_fun {z' : ι -> E} (h : forall i in t, w i != 0 -> z i = z' i) :
    t.centerMass w z = t.centerMass w z' := by
  classical
  exact centerMass_congr (by grind)

/--
lemma `Finset.centerMass_of_sum_add_sum_eq_zero` / 引理 `Finset.centerMass_of_sum_add_sum_eq_zero`

English:
lemma Finset.centerMass_of_sum_add_sum_eq_zero
  statement: {s t : Finset ι}
  proof: by
  simp [centerMass, eq_neg_of_add_eq_zero_right hw, eq_neg_of_add_eq_zero_left hz]

中文:
引理 有限集.centerMass_of_sum_add_sum_eq_zero
  结论: {s t : 有限集 ι}
  证明: by
  simp [centerMass, eq_neg_of_add_eq_zero_right hw, eq_neg_of_add_eq_zero_left hz]

Depends on / 依赖: centerMass, eq_neg_of_add_eq_zero_left, eq_neg_of_add_eq_zero_right
-/
lemma Finset.centerMass_of_sum_add_sum_eq_zero {s t : Finset ι}
    (hw : ∑ i in s, w i + ∑ i in t, w i = 0) (hz : ∑ i in s, w i • z i + ∑ i in t, w i • z i = 0) :
    s.centerMass w z = t.centerMass w z := by
  simp [centerMass, eq_neg_of_add_eq_zero_right hw, eq_neg_of_add_eq_zero_left hz]

variable [LinearOrder R] [IsStrictOrderedRing R] [IsOrderedAddMonoid α] [PosSMulMono R α]

/--
theorem `Convex.centerMass_mem` / 定理 `Convex.centerMass_mem`

English:
theorem Convex.centerMass_mem
  given: (hs : Convex R s)
  proof: by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert i t hi ht =>
    intro h₀ hpos hmem
    have zi : z i in s := hmem _ (mem_insert_self _ _)
have hs₀ : forall j in t, 0 <= w j := fun j hj => h₀ j mem_insert_of_mem hj
    rw [sum_insert hi] at hpos
    by_cases hsum_t : ∑ j in t, w j = 0
    · have ws : forall j in t, w j = 0 := (sum_eq_zero_iff_of_nonneg hs₀).1 hsum_t
      have wz : ∑ j in t, w j • z j = 0 := sum_eq_zero fun i hi => by simp [ws i hi]
      simp only [centerMass, sum_insert hi, wz, hsum_t, add_zero]
      simp only [hsum_t, add_zero] at hpos
      rw [← mul_smul]; rw [inv_mul_cancel₀ (ne_of_gt hpos)]; rw [one_smul]
      exact zi
    · rw [Finset.centerMass_insert _ _ _ hi hsum_t]
      refine convex_iff_div.1 hs zi (ht hs₀ ?_ ?_) ?_ (sum_nonneg hs₀) hpos
      · exact lt_of_le_of_ne (sum_nonneg hs₀) (Ne.symm hsum_t)
      · intro j hj
        exact hmem j (mem_insert_of_mem hj)
      · exact h₀ _ (mem_insert_self _ _)

中文:
定理 凸.centerMass_mem
  条件: (hs : 凸 R s)
  证明: by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert i t hi ht =>
    intro h₀ hpos hmem
    have zi : z i in s := hmem _ (mem_insert_self _ _)
have hs₀ : forall j in t, 0 <= w j := fun j hj => h₀ j mem_insert_of_mem hj
    rw [sum_insert hi] at hpos
    by_cases hsum_t : ∑ j in t, w j = 0
    · have ws : forall j in t, w j = 0 := (sum_eq_zero_iff_of_nonneg hs₀).1 hsum_t
      have wz : ∑ j in t, w j • z j = 0 := sum_eq_zero fun i hi => by simp [ws i hi]
      simp only [centerMass, sum_insert hi, wz, hsum_t, add_zero]
      simp only [hsum_t, add_zero] at hpos
      rw [← mul_smul]; rw [inv_mul_cancel₀ (ne_of_gt hpos)]; rw [one_smul]
      exact zi
    · rw [Finset.centerMass_insert _ _ _ hi hsum_t]
      refine convex_iff_div.1 hs zi (ht hs₀ ?_ ?_) ?_ (sum_nonneg hs₀) hpos
      · exact lt_of_le_of_ne (sum_nonneg hs₀) (Ne.symm hsum_t)
      · intro j hj
        exact hmem j (mem_insert_of_mem hj)
      · exact h₀ _ (mem_insert_self _ _)

Depends on / 依赖: Finset, Finset.induction, centerMass, classical, hsum_t, insert, mem_insert_of_mem, mem_insert_self, sum_eq_zero, sum_eq_zero_iff_of_nonneg, sum_insert
-/
theorem Convex.centerMass_mem (hs : Convex R s) :
    (forall i in t, 0 <= w i) -> (0 < ∑ i in t, w i) -> (forall i in t, z i in s) -> t.centerMass w z in s := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert i t hi ht =>
    intro h₀ hpos hmem
    have zi : z i in s := hmem _ (mem_insert_self _ _)
have hs₀ : forall j in t, 0 <= w j := fun j hj => h₀ j mem_insert_of_mem hj
    rw [sum_insert hi] at hpos
    by_cases hsum_t : ∑ j in t, w j = 0
    · have ws : forall j in t, w j = 0 := (sum_eq_zero_iff_of_nonneg hs₀).1 hsum_t
      have wz : ∑ j in t, w j • z j = 0 := sum_eq_zero fun i hi => by simp [ws i hi]
      simp only [centerMass, sum_insert hi, wz, hsum_t, add_zero]
      simp only [hsum_t, add_zero] at hpos
      rw [← mul_smul]; rw [inv_mul_cancel₀ (ne_of_gt hpos)]; rw [one_smul]
      exact zi
    · rw [Finset.centerMass_insert _ _ _ hi hsum_t]
      refine convex_iff_div.1 hs zi (ht hs₀ ?_ ?_) ?_ (sum_nonneg hs₀) hpos
      · exact lt_of_le_of_ne (sum_nonneg hs₀) (Ne.symm hsum_t)
      · intro j hj
        exact hmem j (mem_insert_of_mem hj)
      · exact h₀ _ (mem_insert_self _ _)

/--
theorem `Convex.sum_mem` / 定理 `Convex.sum_mem`

English:
theorem Convex.sum_mem
  statement: (hs : Convex R s) (h₀ : forall i in t, 0 <= w i) (h₁ : ∑ i in t, w i = 1)
  proof: by
  simpa only [h₁, centerMass, inv_one, one_smul] using
    hs.centerMass_mem h₀ (h₁.symm ▸ zero_lt_one) hz

中文:
定理 凸.sum_mem
  结论: (hs : 凸 R s) (h₀ : 对任意 i in t, 0 <= w i) (h₁ : ∑ i in t, w i = 1)
  证明: by
  simpa only [h₁, centerMass, inv_one, one_smul] using
    hs.centerMass_mem h₀ (h₁.symm ▸ zero_lt_one) hz

Depends on / 依赖: centerMass, centerMass_mem, hs.centerMass_mem, inv_one, one_smul, zero_lt_one
-/
theorem Convex.sum_mem (hs : Convex R s) (h₀ : forall i in t, 0 <= w i) (h₁ : ∑ i in t, w i = 1)
    (hz : forall i in t, z i in s) : (∑ i in t, w i • z i) in s := by
  simpa only [h₁, centerMass, inv_one, one_smul] using
    hs.centerMass_mem h₀ (h₁.symm ▸ zero_lt_one) hz

/--
theorem `Convex.finsum_mem` / 定理 `Convex.finsum_mem`

English:
theorem Convex.finsum_mem
  statement: {ι : Sort*} {w : ι -> R} {z : ι -> E} {s : Set E} (hs : Convex R s)
  proof: by
  have hfin_w : HasFiniteSupport (w ∘ PLift.down) := by
    by_contra H
    rw [finsum]; rw [dif_neg H] at h₁
    exact zero_ne_one h₁
  have hsub : support ((fun i => w i • z i) ∘ PLift.down) subseteq hfin_w.toFinset :=
    (support_smul_subset_left _ _).trans hfin_w.coe_toFinset.ge
  rw [finsum_eq_sum_plift_of_support_subset hsub]
  refine hs.sum_mem (fun _ _ => h₀ _) ?_ fun i hi => hz _ ?_
  · rwa [finsum, dif_pos hfin_w] at h₁
  · rwa [hfin_w.mem_toFinset] at hi

中文:
定理 凸.finsum_mem
  结论: {ι : 类型层*} {w : ι -> R} {z : ι -> E} {s : 集合 E} (hs : 凸 R s)
  证明: by
  have hfin_w : HasFiniteSupport (w ∘ PLift.down) := by
    by_contra H
    rw [finsum]; rw [dif_neg H] at h₁
    exact zero_ne_one h₁
  have hsub : support ((fun i => w i • z i) ∘ PLift.down) subseteq hfin_w.toFinset :=
    (support_smul_subset_left _ _).trans hfin_w.coe_toFinset.ge
  rw [finsum_eq_sum_plift_of_support_subset hsub]
  refine hs.sum_mem (fun _ _ => h₀ _) ?_ fun i hi => hz _ ?_
  · rwa [finsum, dif_pos hfin_w] at h₁
  · rwa [hfin_w.mem_toFinset] at hi

Depends on / 依赖: HasFiniteSupport, PLift.down, coe_toFinset, dif_neg, dif_pos, finsum, finsum_eq_sum_plift_of_support_subset, hfin_w, hfin_w.coe_toFinset.ge, hfin_w.mem_toFinset, hfin_w.toFinset, hs.sum_mem, mem_toFinset, subseteq, sum_mem, support, support_smul_subset_left, toFinset, zero_ne_one
-/
theorem Convex.finsum_mem {ι : Sort*} {w : ι -> R} {z : ι -> E} {s : Set E} (hs : Convex R s)
    (h₀ : forall i, 0 <= w i) (h₁ : ∑ᶠ i, w i = 1) (hz : forall i, w i != 0 -> z i in s) :
    (∑ᶠ i, w i • z i) in s := by
  have hfin_w : HasFiniteSupport (w ∘ PLift.down) := by
    by_contra H
    rw [finsum]; rw [dif_neg H] at h₁
    exact zero_ne_one h₁
  have hsub : support ((fun i => w i • z i) ∘ PLift.down) subseteq hfin_w.toFinset :=
    (support_smul_subset_left _ _).trans hfin_w.coe_toFinset.ge
  rw [finsum_eq_sum_plift_of_support_subset hsub]
  refine hs.sum_mem (fun _ _ => h₀ _) ?_ fun i hi => hz _ ?_
  · rwa [finsum, dif_pos hfin_w] at h₁
  · rwa [hfin_w.mem_toFinset] at hi

/--
theorem `convex_iff_sum_mem` / 定理 `convex_iff_sum_mem`

English:
theorem convex_iff_sum_mem
  statement: Convex R s ↔ forall (t : Finset E) (w : E -> R),
  proof: by
  classical
  refine ⟨fun hs t w hw₀ hw₁ hts => hs.sum_mem hw₀ hw₁ hts, ?_⟩
  intro h x hx y hy a b ha hb hab
  by_cases h_cases : x = y
  · rw [h_cases, ← add_smul, hab, one_smul]
    exact hy
  · convert! h { x, y } (fun z => if z = y then b else a) _ _ _
    · simp only [sum_pair h_cases, if_neg h_cases, if_pos trivial]
    · grind
    · simp only [sum_pair h_cases, if_neg h_cases, if_pos trivial, hab]
    · intro i hi
      simp only [Finset.mem_singleton, Finset.mem_insert] at hi
      cases hi <;> subst i <;> assumption

中文:
定理 convex_iff_sum_mem
  结论: 凸 R s ↔ 对任意 (t : 有限集 E) (w : E -> R),
  证明: by
  classical
  refine ⟨fun hs t w hw₀ hw₁ hts => hs.sum_mem hw₀ hw₁ hts, ?_⟩
  intro h x hx y hy a b ha hb hab
  by_cases h_cases : x = y
  · rw [h_cases, ← add_smul, hab, one_smul]
    exact hy
  · convert! h { x, y } (fun z => if z = y then b else a) _ _ _
    · simp only [sum_pair h_cases, if_neg h_cases, if_pos trivial]
    · grind
    · simp only [sum_pair h_cases, if_neg h_cases, if_pos trivial, hab]
    · intro i hi
      simp only [Finset.mem_singleton, Finset.mem_insert] at hi
      cases hi <;> subst i <;> assumption

Depends on / 依赖: Finset, Finset.mem_insert, Finset.mem_singleton, add_smul, classical, convert, h_cases, hs.sum_mem, if_neg, if_pos, mem_insert, mem_singleton, one_smul, sum_mem, sum_pair
-/
theorem convex_iff_sum_mem : Convex R s ↔ forall (t : Finset E) (w : E -> R),
    (forall i in t, 0 <= w i) -> ∑ i in t, w i = 1 -> (forall x in t, x in s) -> (∑ x in t, w x • x) in s := by
  classical
  refine ⟨fun hs t w hw₀ hw₁ hts => hs.sum_mem hw₀ hw₁ hts, ?_⟩
  intro h x hx y hy a b ha hb hab
  by_cases h_cases : x = y
  · rw [h_cases, ← add_smul, hab, one_smul]
    exact hy
  · convert! h { x, y } (fun z => if z = y then b else a) _ _ _
    · simp only [sum_pair h_cases, if_neg h_cases, if_pos trivial]
    · grind
    · simp only [sum_pair h_cases, if_neg h_cases, if_pos trivial, hab]
    · intro i hi
      simp only [Finset.mem_singleton, Finset.mem_insert] at hi
      cases hi <;> subst i <;> assumption

/--
theorem `Finset.centerMass_mem_convexHull` / 定理 `Finset.centerMass_mem_convexHull`

English:
theorem Finset.centerMass_mem_convexHull
  statement: (t : Finset ι) {w : ι -> R} (hw₀ : forall i in t, 0 <= w i)
  proof: (convex_convexHull R s).centerMass_mem hw₀ hws fun i hi => subset_convexHull R s hz i hi

中文:
定理 有限集.centerMass_mem_convexHull
  结论: (t : 有限集 ι) {w : ι -> R} (hw₀ : 对任意 i in t, 0 <= w i)
  证明: (convex_convexHull R s).centerMass_mem hw₀ hws fun i hi => subset_convexHull R s hz i hi

Depends on / 依赖: centerMass_mem, convex_convexHull, subset_convexHull
-/
theorem Finset.centerMass_mem_convexHull (t : Finset ι) {w : ι -> R} (hw₀ : forall i in t, 0 <= w i)
    (hws : 0 < ∑ i in t, w i) {z : ι -> E} (hz : forall i in t, z i in s) :
    t.centerMass w z in convexHull R s :=
(convex_convexHull R s).centerMass_mem hw₀ hws fun i hi => subset_convexHull R s hz i hi

/--
lemma `Finset.centerMass_mem_convexHull_of_nonpos` / 引理 `Finset.centerMass_mem_convexHull_of_nonpos`

English:
lemma Finset.centerMass_mem_convexHull_of_nonpos
  statement: (t : Finset ι) (hw₀ : forall i in t, w i <= 0)
  proof: by
  rw [← centerMass_neg_left]
  exact Finset.centerMass_mem_convexHull _ (fun _i hi => neg_nonneg.2 <| hw₀ _ hi) (by simpa) hz

中文:
引理 有限集.centerMass_mem_convexHull_of_nonpos
  结论: (t : 有限集 ι) (hw₀ : 对任意 i in t, w i <= 0)
  证明: by
  rw [← centerMass_neg_left]
  exact Finset.centerMass_mem_convexHull _ (fun _i hi => neg_nonneg.2 <| hw₀ _ hi) (by simpa) hz

Depends on / 依赖: Finset, Finset.centerMass_mem_convexHull, centerMass_mem_convexHull, centerMass_neg_left, neg_nonneg
-/
lemma Finset.centerMass_mem_convexHull_of_nonpos (t : Finset ι) (hw₀ : forall i in t, w i <= 0)
    (hws : ∑ i in t, w i < 0) (hz : forall i in t, z i in s) : t.centerMass w z in convexHull R s := by
  rw [← centerMass_neg_left]
  exact Finset.centerMass_mem_convexHull _ (fun _i hi => neg_nonneg.2 <| hw₀ _ hi) (by simpa) hz

/--
theorem `Finset.centerMass_id_mem_convexHull` / 定理 `Finset.centerMass_id_mem_convexHull`

English:
theorem Finset.centerMass_id_mem_convexHull
  statement: (t : Finset E) {w : E -> R} (hw₀ : forall i in t, 0 <= w i)
  proof: t.centerMass_mem_convexHull hw₀ hws fun _ => mem_coe.2

中文:
定理 有限集.centerMass_id_mem_convexHull
  结论: (t : 有限集 E) {w : E -> R} (hw₀ : 对任意 i in t, 0 <= w i)
  证明: t.centerMass_mem_convexHull hw₀ hws fun _ => mem_coe.2

Depends on / 依赖: centerMass_mem_convexHull, mem_coe, t.centerMass_mem_convexHull
-/
theorem Finset.centerMass_id_mem_convexHull (t : Finset E) {w : E -> R} (hw₀ : forall i in t, 0 <= w i)
    (hws : 0 < ∑ i in t, w i) : t.centerMass w id in convexHull R (t : Set E) :=
  t.centerMass_mem_convexHull hw₀ hws fun _ => mem_coe.2

/--
lemma `Finset.centerMass_id_mem_convexHull_of_nonpos` / 引理 `Finset.centerMass_id_mem_convexHull_of_nonpos`

English:
lemma Finset.centerMass_id_mem_convexHull_of_nonpos
  statement: (t : Finset E) {w : E -> R}
  proof: t.centerMass_mem_convexHull_of_nonpos hw₀ hws fun _ => mem_coe.2

omit [LinearOrder R] [IsStrictOrderedRing R] in

中文:
引理 有限集.centerMass_id_mem_convexHull_of_nonpos
  结论: (t : 有限集 E) {w : E -> R}
  证明: t.centerMass_mem_convexHull_of_nonpos hw₀ hws fun _ => mem_coe.2

omit [LinearOrder R] [IsStrictOrderedRing R] in

Depends on / 依赖: centerMass_mem_convexHull_of_nonpos, mem_coe, t.centerMass_mem_convexHull_of_nonpos
-/
lemma Finset.centerMass_id_mem_convexHull_of_nonpos (t : Finset E) {w : E -> R}
    (hw₀ : forall i in t, w i <= 0) (hws : ∑ i in t, w i < 0) :
    t.centerMass w id in convexHull R (t : Set E) :=
  t.centerMass_mem_convexHull_of_nonpos hw₀ hws fun _ => mem_coe.2

omit [LinearOrder R] [IsStrictOrderedRing R] in
/--
theorem `affineCombination_eq_centerMass` / 定理 `affineCombination_eq_centerMass`

English:
theorem affineCombination_eq_centerMass
  statement: {ι : Type*} {t : Finset ι} {p : ι -> E} {w : ι -> R}
  proof: by
  rw [affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ w _ hw₂ (0 : E)]; rw [Finset.weightedVSubOfPoint_apply]; rw [vadd_eq_add]; rw [add_zero]; rw [t.centerMass_eq_of_sum_1 _ hw₂]
  simp_rw [vsub_eq_sub, sub_zero]

中文:
定理 affineCombination_eq_centerMass
  结论: {ι : 类型} {t : 有限集 ι} {p : ι -> E} {w : ι -> R}
  证明: by
  rw [affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ w _ hw₂ (0 : E)]; rw [Finset.weightedVSubOfPoint_apply]; rw [vadd_eq_add]; rw [add_zero]; rw [t.centerMass_eq_of_sum_1 _ hw₂]
  simp_rw [vsub_eq_sub, sub_zero]

Depends on / 依赖: Finset, Finset.weightedVSubOfPoint_apply, add_zero, affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one, centerMass_eq_of_sum_1, simp_rw, sub_zero, t.centerMass_eq_of_sum_1, vadd_eq_add, vsub_eq_sub, weightedVSubOfPoint_apply
-/
theorem affineCombination_eq_centerMass {ι : Type*} {t : Finset ι} {p : ι -> E} {w : ι -> R}
    (hw₂ : ∑ i in t, w i = 1) : t.affineCombination R p w = centerMass t w p := by
  rw [affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ w _ hw₂ (0 : E)]; rw [Finset.weightedVSubOfPoint_apply]; rw [vadd_eq_add]; rw [add_zero]; rw [t.centerMass_eq_of_sum_1 _ hw₂]
  simp_rw [vsub_eq_sub, sub_zero]

/--
theorem `affineCombination_mem_convexHull` / 定理 `affineCombination_mem_convexHull`

English:
theorem affineCombination_mem_convexHull
  statement: {s : Finset ι} {v : ι -> E} {w : ι -> R}
  proof: by
  rw [affineCombination_eq_centerMass hw₁]
  apply s.centerMass_mem_convexHull hw₀
  · simp [hw₁]
  · simp

中文:
定理 affineCombination_mem_convexHull
  结论: {s : 有限集 ι} {v : ι -> E} {w : ι -> R}
  证明: by
  rw [affineCombination_eq_centerMass hw₁]
  apply s.centerMass_mem_convexHull hw₀
  · simp [hw₁]
  · simp

Depends on / 依赖: affineCombination_eq_centerMass, centerMass_mem_convexHull, s.centerMass_mem_convexHull
-/
theorem affineCombination_mem_convexHull {s : Finset ι} {v : ι -> E} {w : ι -> R}
    (hw₀ : forall i in s, 0 <= w i) (hw₁ : s.sum w = 1) :
    s.affineCombination R v w in convexHull R (range v) := by
  rw [affineCombination_eq_centerMass hw₁]
  apply s.centerMass_mem_convexHull hw₀
  · simp [hw₁]
  · simp

/-- The centroid can be regarded as a center of mass. -/
@[simp]
/--
theorem `Finset.centroid_eq_centerMass` / 定理 `Finset.centroid_eq_centerMass`

English:
theorem Finset.centroid_eq_centerMass
  given: (s : Finset ι) (hs : s.Nonempty) (p : ι -> E)
  proof: affineCombination_eq_centerMass (s.sum_centroidWeights_eq_one_of_nonempty R hs)

中文:
定理 有限集.centroid_eq_centerMass
  条件: (s : 有限集 ι) (hs : s.非空) (p : ι -> E)
  证明: affineCombination_eq_centerMass (s.sum_centroidWeights_eq_one_of_nonempty R hs)

Depends on / 依赖: affineCombination_eq_centerMass, s.sum_centroidWeights_eq_one_of_nonempty, sum_centroidWeights_eq_one_of_nonempty
-/
theorem Finset.centroid_eq_centerMass (s : Finset ι) (hs : s.Nonempty) (p : ι -> E) :
    s.centroid R p = s.centerMass (s.centroidWeights R) p :=
  affineCombination_eq_centerMass (s.sum_centroidWeights_eq_one_of_nonempty R hs)

/--
theorem `Finset.centroid_mem_convexHull` / 定理 `Finset.centroid_mem_convexHull`

English:
theorem Finset.centroid_mem_convexHull
  given: (s : Finset E) (hs : s.Nonempty)
  proof: by
  rw [s.centroid_eq_centerMass hs]
  apply s.centerMass_id_mem_convexHull
  · simp only [inv_nonneg, imp_true_iff, Nat.cast_nonneg, Finset.centroidWeights_apply]
  · have hs_card : (#s : R) != 0 := by simp [Finset.nonempty_iff_ne_empty.mp hs]
    simp only [hs_card, Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀, Ne, not_false_iff,
      Finset.centroidWeights_apply, zero_lt_one]

中文:
定理 有限集.centroid_mem_convexHull
  条件: (s : 有限集 E) (hs : s.非空)
  证明: by
  rw [s.centroid_eq_centerMass hs]
  apply s.centerMass_id_mem_convexHull
  · simp only [inv_nonneg, imp_true_iff, Nat.cast_nonneg, Finset.centroidWeights_apply]
  · have hs_card : (#s : R) != 0 := by simp [Finset.nonempty_iff_ne_empty.mp hs]
    simp only [hs_card, Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀, Ne, not_false_iff,
      Finset.centroidWeights_apply, zero_lt_one]

Depends on / 依赖: Finset, Finset.centroidWeights_apply, Finset.nonempty_iff_ne_empty.mp, Finset.sum_const, Nat.cast_nonneg, cast_nonneg, centerMass_id_mem_convexHull, centroidWeights_apply, centroid_eq_centerMass, hs_card, imp_true_iff, inv_nonneg, nonempty_iff_ne_empty, not_false_iff, nsmul_eq_mul, s.centerMass_id_mem_convexHull, s.centroid_eq_centerMass, sum_const, zero_lt_one
-/
theorem Finset.centroid_mem_convexHull (s : Finset E) (hs : s.Nonempty) :
    s.centroid R id in convexHull R (s : Set E) := by
  rw [s.centroid_eq_centerMass hs]
  apply s.centerMass_id_mem_convexHull
  · simp only [inv_nonneg, imp_true_iff, Nat.cast_nonneg, Finset.centroidWeights_apply]
  · have hs_card : (#s : R) != 0 := by simp [Finset.nonempty_iff_ne_empty.mp hs]
    simp only [hs_card, Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀, Ne, not_false_iff,
      Finset.centroidWeights_apply, zero_lt_one]

/--
theorem `convexHull_range_eq_exists_affineCombination` / 定理 `convexHull_range_eq_exists_affineCombination`

English:
theorem convexHull_range_eq_exists_affineCombination
  given: (v : ι -> E)
  statement: convexHull R (range v) =
  proof: by
  classical
  refine Subset.antisymm (convexHull_min ?_ ?_) ?_
  · intro x hx
    obtain ⟨i, hi⟩ := Set.mem_range.mp hx
    exact ⟨{i}, Function.const ι (1 : R), by simp, by simp, by simp [hi]⟩
  · rintro x ⟨s, w, hw₀, hw₁, rfl⟩ y ⟨s', w', hw₀', hw₁', rfl⟩ a b ha hb hab
    let W : ι -> R := fun i => (if i in s then a * w i else 0) + if i in s' then b * w' i else 0
    have hW₁ : (s union s').sum W = 1 := by
      rw [sum_add_distrib]; rw [← sum_subset subset_union_left]; rw [← sum_subset subset_union_right]; rw [sum_ite_of_true]; rw [sum_ite_of_true]; rw [← mul_sum]; rw [← mul_sum]; rw [hw₁]; rw [hw₁']; rw [← add_mul]; rw [hab]; rw [mul_one] <;> intros <;> simp_all
    refine ⟨s union s', W, ?_, hW₁, ?_⟩
    · rintro i -
      by_cases hi : i in s <;> by_cases hi' : i in s' <;>
        simp [W, hi, hi', add_nonneg, mul_nonneg ha (hw₀ i _), mul_nonneg hb (hw₀' i _)]
    · simp_rw [W, affineCombination_eq_linear_combination (s union s') v _ hW₁,
        affineCombination_eq_linear_combination s v w hw₁,
        affineCombination_eq_linear_combination s' v w' hw₁', add_smul, sum_add_distrib]
      rw [← sum_subset subset_union_left]; rw [← sum_subset subset_union_right]
      · simp only [ite_smul, sum_ite_of_true fun _ hi => hi, mul_smul, ← smul_sum]
      · intro i _ hi'
        simp [hi']
      · intro i _ hi'
        simp [hi']
  · rintro x ⟨s, w, hw₀, hw₁, rfl⟩
    exact affineCombination_mem_convexHull hw₀ hw₁

中文:
定理 convexHull_range_eq_存在_affineCombination
  条件: (v : ι -> E)
  结论: convexHull R (range v) =
  证明: by
  classical
  refine Subset.antisymm (convexHull_min ?_ ?_) ?_
  · intro x hx
    obtain ⟨i, hi⟩ := Set.mem_range.mp hx
    exact ⟨{i}, Function.const ι (1 : R), by simp, by simp, by simp [hi]⟩
  · rintro x ⟨s, w, hw₀, hw₁, rfl⟩ y ⟨s', w', hw₀', hw₁', rfl⟩ a b ha hb hab
    let W : ι -> R := fun i => (if i in s then a * w i else 0) + if i in s' then b * w' i else 0
    have hW₁ : (s union s').sum W = 1 := by
      rw [sum_add_distrib]; rw [← sum_subset subset_union_left]; rw [← sum_subset subset_union_right]; rw [sum_ite_of_true]; rw [sum_ite_of_true]; rw [← mul_sum]; rw [← mul_sum]; rw [hw₁]; rw [hw₁']; rw [← add_mul]; rw [hab]; rw [mul_one] <;> intros <;> simp_all
    refine ⟨s union s', W, ?_, hW₁, ?_⟩
    · rintro i -
      by_cases hi : i in s <;> by_cases hi' : i in s' <;>
        simp [W, hi, hi', add_nonneg, mul_nonneg ha (hw₀ i _), mul_nonneg hb (hw₀' i _)]
    · simp_rw [W, affineCombination_eq_linear_combination (s union s') v _ hW₁,
        affineCombination_eq_linear_combination s v w hw₁,
        affineCombination_eq_linear_combination s' v w' hw₁', add_smul, sum_add_distrib]
      rw [← sum_subset subset_union_left]; rw [← sum_subset subset_union_right]
      · simp only [ite_smul, sum_ite_of_true fun _ hi => hi, mul_smul, ← smul_sum]
      · intro i _ hi'
        simp [hi']
      · intro i _ hi'
        simp [hi']
  · rintro x ⟨s, w, hw₀, hw₁, rfl⟩
    exact affineCombination_mem_convexHull hw₀ hw₁

Depends on / 依赖: Function, Function.const, Set.mem_range.mp, Subset, Subset.antisymm, antisymm, classical, convexHull_min, mem_range, subset_union_left, subset_union_right, sum_add_distrib, sum_ite_, sum_subset
-/
theorem convexHull_range_eq_exists_affineCombination (v : ι -> E) : convexHull R (range v) =
    { x | exists (s : Finset ι) (w : ι -> R), (forall i in s, 0 <= w i) ∧ s.sum w = 1 ∧
      s.affineCombination R v w = x } := by
  classical
  refine Subset.antisymm (convexHull_min ?_ ?_) ?_
  · intro x hx
    obtain ⟨i, hi⟩ := Set.mem_range.mp hx
    exact ⟨{i}, Function.const ι (1 : R), by simp, by simp, by simp [hi]⟩
  · rintro x ⟨s, w, hw₀, hw₁, rfl⟩ y ⟨s', w', hw₀', hw₁', rfl⟩ a b ha hb hab
    let W : ι -> R := fun i => (if i in s then a * w i else 0) + if i in s' then b * w' i else 0
    have hW₁ : (s union s').sum W = 1 := by
      rw [sum_add_distrib]; rw [← sum_subset subset_union_left]; rw [← sum_subset subset_union_right]; rw [sum_ite_of_true]; rw [sum_ite_of_true]; rw [← mul_sum]; rw [← mul_sum]; rw [hw₁]; rw [hw₁']; rw [← add_mul]; rw [hab]; rw [mul_one] <;> intros <;> simp_all
    refine ⟨s union s', W, ?_, hW₁, ?_⟩
    · rintro i -
      by_cases hi : i in s <;> by_cases hi' : i in s' <;>
        simp [W, hi, hi', add_nonneg, mul_nonneg ha (hw₀ i _), mul_nonneg hb (hw₀' i _)]
    · simp_rw [W, affineCombination_eq_linear_combination (s union s') v _ hW₁,
        affineCombination_eq_linear_combination s v w hw₁,
        affineCombination_eq_linear_combination s' v w' hw₁', add_smul, sum_add_distrib]
      rw [← sum_subset subset_union_left]; rw [← sum_subset subset_union_right]
      · simp only [ite_smul, sum_ite_of_true fun _ hi => hi, mul_smul, ← smul_sum]
      · intro i _ hi'
        simp [hi']
      · intro i _ hi'
        simp [hi']
  · rintro x ⟨s, w, hw₀, hw₁, rfl⟩
    exact affineCombination_mem_convexHull hw₀ hw₁

/--
theorem `convexHull_eq` / 定理 `convexHull_eq`

English:
theorem convexHull_eq
  given: (s : Set E)
  statement: convexHull R s =
  proof: by
  refine Subset.antisymm (convexHull_min ?_ ?_) ?_
  · intro x hx
    use PUnit, {PUnit.unit}, fun _ => 1, fun _ => x, fun _ _ => zero_le_one, sum_singleton _ _,
      fun _ _ => hx
    simp only [Finset.centerMass, Finset.sum_singleton, inv_one, one_smul]
  · rintro x ⟨ι, sx, wx, zx, hwx₀, hwx₁, hzx, rfl⟩ y ⟨ι', sy, wy, zy, hwy₀, hwy₁, hzy, rfl⟩ a b ha
      hb hab
    rw [Finset.centerMass_segment' _ _ _ _ _ _ hwx₁ hwy₁ _ _ hab]
    refine ⟨_, _, _, _, ?_, ?_, ?_, rfl⟩
    · rintro i hi
      rw [Finset.mem_disjSum] at hi
      rcases hi with (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) <;> simp only [Sum.elim_inl, Sum.elim_inr] <;>
        apply_rules [mul_nonneg, hwx₀, hwy₀]
    · simp [← mul_sum, *]
    · intro i hi
      rw [Finset.mem_disjSum] at hi
      rcases hi with (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) <;> apply_rules [hzx, hzy]
  · rintro _ ⟨ι, t, w, z, hw₀, hw₁, hz, rfl⟩
    exact t.centerMass_mem_convexHull hw₀ (hw₁.symm ▸ zero_lt_one) hz

中文:
定理 convexHull_eq
  条件: (s : 集合 E)
  结论: convexHull R s =
  证明: by
  refine Subset.antisymm (convexHull_min ?_ ?_) ?_
  · intro x hx
    use PUnit, {PUnit.unit}, fun _ => 1, fun _ => x, fun _ _ => zero_le_one, sum_singleton _ _,
      fun _ _ => hx
    simp only [Finset.centerMass, Finset.sum_singleton, inv_one, one_smul]
  · rintro x ⟨ι, sx, wx, zx, hwx₀, hwx₁, hzx, rfl⟩ y ⟨ι', sy, wy, zy, hwy₀, hwy₁, hzy, rfl⟩ a b ha
      hb hab
    rw [Finset.centerMass_segment' _ _ _ _ _ _ hwx₁ hwy₁ _ _ hab]
    refine ⟨_, _, _, _, ?_, ?_, ?_, rfl⟩
    · rintro i hi
      rw [Finset.mem_disjSum] at hi
      rcases hi with (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) <;> simp only [Sum.elim_inl, Sum.elim_inr] <;>
        apply_rules [mul_nonneg, hwx₀, hwy₀]
    · simp [← mul_sum, *]
    · intro i hi
      rw [Finset.mem_disjSum] at hi
      rcases hi with (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) <;> apply_rules [hzx, hzy]
  · rintro _ ⟨ι, t, w, z, hw₀, hw₁, hz, rfl⟩
    exact t.centerMass_mem_convexHull hw₀ (hw₁.symm ▸ zero_lt_one) hz

Depends on / 依赖: Finset, Finset.centerMass, Finset.centerMass_segment, Finset.mem_disjSum, Finset.sum_singleton, PUnit.unit, Subset, Subset.antisymm, antisymm, centerMass, centerMass_segment, convexHull_min, inv_one, mem_disjSum, one_smul, sum_singleton, zero_le_one
-/
theorem convexHull_eq (s : Set E) : convexHull R s =
    { x : E | exists (ι : Type) (t : Finset ι) (w : ι -> R) (z : ι -> E), (forall i in t, 0 <= w i) ∧
      ∑ i in t, w i = 1 ∧ (forall i in t, z i in s) ∧ t.centerMass w z = x } := by
  refine Subset.antisymm (convexHull_min ?_ ?_) ?_
  · intro x hx
    use PUnit, {PUnit.unit}, fun _ => 1, fun _ => x, fun _ _ => zero_le_one, sum_singleton _ _,
      fun _ _ => hx
    simp only [Finset.centerMass, Finset.sum_singleton, inv_one, one_smul]
  · rintro x ⟨ι, sx, wx, zx, hwx₀, hwx₁, hzx, rfl⟩ y ⟨ι', sy, wy, zy, hwy₀, hwy₁, hzy, rfl⟩ a b ha
      hb hab
    rw [Finset.centerMass_segment' _ _ _ _ _ _ hwx₁ hwy₁ _ _ hab]
    refine ⟨_, _, _, _, ?_, ?_, ?_, rfl⟩
    · rintro i hi
      rw [Finset.mem_disjSum] at hi
      rcases hi with (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) <;> simp only [Sum.elim_inl, Sum.elim_inr] <;>
        apply_rules [mul_nonneg, hwx₀, hwy₀]
    · simp [← mul_sum, *]
    · intro i hi
      rw [Finset.mem_disjSum] at hi
      rcases hi with (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) <;> apply_rules [hzx, hzy]
  · rintro _ ⟨ι, t, w, z, hw₀, hw₁, hz, rfl⟩
    exact t.centerMass_mem_convexHull hw₀ (hw₁.symm ▸ zero_lt_one) hz

/--
lemma `mem_convexHull_of_exists_fintype` / 引理 `mem_convexHull_of_exists_fintype`

English:
lemma mem_convexHull_of_exists_fintype
  statement: {s : Set E} {x : E} [Fintype ι] (w : ι -> R) (z : ι -> E)
  proof: by
  rw [← hx]; rw [← centerMass_eq_of_sum_1 _ _ hw₁]
  exact centerMass_mem_convexHull _ (by simpa using hw₀) (by simp [hw₁]) (by simpa using hz)

中文:
引理 mem_convexHull_of_存在_fintype
  结论: {s : 集合 E} {x : E} [有限类型 ι] (w : ι -> R) (z : ι -> E)
  证明: by
  rw [← hx]; rw [← centerMass_eq_of_sum_1 _ _ hw₁]
  exact centerMass_mem_convexHull _ (by simpa using hw₀) (by simp [hw₁]) (by simpa using hz)

Depends on / 依赖: centerMass_eq_of_sum_1, centerMass_mem_convexHull
-/
lemma mem_convexHull_of_exists_fintype {s : Set E} {x : E} [Fintype ι] (w : ι -> R) (z : ι -> E)
    (hw₀ : forall i, 0 <= w i) (hw₁ : ∑ i, w i = 1) (hz : forall i, z i in s) (hx : ∑ i, w i • z i = x) :
    x in convexHull R s := by
  rw [← hx]; rw [← centerMass_eq_of_sum_1 _ _ hw₁]
  exact centerMass_mem_convexHull _ (by simpa using hw₀) (by simp [hw₁]) (by simpa using hz)

/--
lemma `mem_convexHull_iff_exists_fintype` / 引理 `mem_convexHull_iff_exists_fintype`

English:
lemma mem_convexHull_iff_exists_fintype
  given: {s : Set E} {x : E}
  proof: by
  constructor
  · simp only [convexHull_eq, mem_ofPred_eq]
    rintro ⟨ι, t, w, z, h⟩
    refine ⟨t, inferInstance, w ∘ (↑), z ∘ (↑), ?_⟩
    simpa [← sum_attach t, centerMass_eq_of_sum_1 _ _ h.2.1] using h
  · rintro ⟨ι, _, w, z, hw₀, hw₁, hz, hx⟩
    exact mem_convexHull_of_exists_fintype w z hw₀ hw₁ hz hx

中文:
引理 mem_convexHull_iff_存在_fintype
  条件: {s : 集合 E} {x : E}
  证明: by
  constructor
  · simp only [convexHull_eq, mem_ofPred_eq]
    rintro ⟨ι, t, w, z, h⟩
    refine ⟨t, inferInstance, w ∘ (↑), z ∘ (↑), ?_⟩
    simpa [← sum_attach t, centerMass_eq_of_sum_1 _ _ h.2.1] using h
  · rintro ⟨ι, _, w, z, hw₀, hw₁, hz, hx⟩
    exact mem_convexHull_of_exists_fintype w z hw₀ hw₁ hz hx

Depends on / 依赖: centerMass_eq_of_sum_1, convexHull_eq, mem_convexHull_of_exists_fintype, mem_ofPred_eq, sum_attach
-/
lemma mem_convexHull_iff_exists_fintype {s : Set E} {x : E} :
    x in convexHull R s ↔ exists (ι : Type) (_ : Fintype ι) (w : ι -> R) (z : ι -> E), (forall i, 0 <= w i) ∧
      ∑ i, w i = 1 ∧ (forall i, z i in s) ∧ ∑ i, w i • z i = x := by
  constructor
  · simp only [convexHull_eq, mem_ofPred_eq]
    rintro ⟨ι, t, w, z, h⟩
    refine ⟨t, inferInstance, w ∘ (↑), z ∘ (↑), ?_⟩
    simpa [← sum_attach t, centerMass_eq_of_sum_1 _ _ h.2.1] using h
  · rintro ⟨ι, _, w, z, hw₀, hw₁, hz, hx⟩
    exact mem_convexHull_of_exists_fintype w z hw₀ hw₁ hz hx

/--
theorem `Finset.convexHull_eq` / 定理 `Finset.convexHull_eq`

English:
theorem Finset.convexHull_eq
  given: (s : Finset E)
  statement: convexHull R ↑s =
  proof: by
  classical
  refine Set.Subset.antisymm (convexHull_min ?_ ?_) ?_
  · intro x hx
    rw [Finset.mem_coe] at hx
    refine ⟨_, ?_, ?_, Finset.centerMass_ite_eq _ _ _ hx⟩
    · intros
      split_ifs
      exacts [zero_le_one, le_refl 0]
    · rw [Finset.sum_ite_eq, if_pos hx]
  · rintro x ⟨wx, hwx₀, hwx₁, rfl⟩ y ⟨wy, hwy₀, hwy₁, rfl⟩ a b ha hb hab
    rw [Finset.centerMass_segment _ _ _ _ hwx₁ hwy₁ _ _ hab]
    refine ⟨_, ?_, ?_, rfl⟩
    · rintro i hi
      apply_rules [add_nonneg, mul_nonneg, hwx₀, hwy₀]
    · simp only [Finset.sum_add_distrib, ← mul_sum, mul_one, *]
  · rintro _ ⟨w, hw₀, hw₁, rfl⟩
    exact
      s.centerMass_mem_convexHull (fun x hx => hw₀ _ hx) (hw₁.symm ▸ zero_lt_one) fun x hx => hx

中文:
定理 有限集.convexHull_eq
  条件: (s : 有限集 E)
  结论: convexHull R ↑s =
  证明: by
  classical
  refine Set.Subset.antisymm (convexHull_min ?_ ?_) ?_
  · intro x hx
    rw [Finset.mem_coe] at hx
    refine ⟨_, ?_, ?_, Finset.centerMass_ite_eq _ _ _ hx⟩
    · intros
      split_ifs
      exacts [zero_le_one, le_refl 0]
    · rw [Finset.sum_ite_eq, if_pos hx]
  · rintro x ⟨wx, hwx₀, hwx₁, rfl⟩ y ⟨wy, hwy₀, hwy₁, rfl⟩ a b ha hb hab
    rw [Finset.centerMass_segment _ _ _ _ hwx₁ hwy₁ _ _ hab]
    refine ⟨_, ?_, ?_, rfl⟩
    · rintro i hi
      apply_rules [add_nonneg, mul_nonneg, hwx₀, hwy₀]
    · simp only [Finset.sum_add_distrib, ← mul_sum, mul_one, *]
  · rintro _ ⟨w, hw₀, hw₁, rfl⟩
    exact
      s.centerMass_mem_convexHull (fun x hx => hw₀ _ hx) (hw₁.symm ▸ zero_lt_one) fun x hx => hx

Depends on / 依赖: Finset, Finset.centerMass_ite_eq, Finset.centerMass_segment, Finset.mem_coe, Finset.sum_add_distrib, Finset.sum_ite_eq, Set.Subset.antisymm, Subset, add_nonneg, antisymm, apply_rules, centerMass_ite_eq, centerMass_segment, classical, convexHull_min, exacts, if_pos, intros, le_refl, mem_coe
-/
theorem Finset.convexHull_eq (s : Finset E) : convexHull R ↑s =
    { x : E | exists w : E -> R, (forall y in s, 0 <= w y) ∧ ∑ y in s, w y = 1 ∧ s.centerMass w id = x } := by
  classical
  refine Set.Subset.antisymm (convexHull_min ?_ ?_) ?_
  · intro x hx
    rw [Finset.mem_coe] at hx
    refine ⟨_, ?_, ?_, Finset.centerMass_ite_eq _ _ _ hx⟩
    · intros
      split_ifs
      exacts [zero_le_one, le_refl 0]
    · rw [Finset.sum_ite_eq, if_pos hx]
  · rintro x ⟨wx, hwx₀, hwx₁, rfl⟩ y ⟨wy, hwy₀, hwy₁, rfl⟩ a b ha hb hab
    rw [Finset.centerMass_segment _ _ _ _ hwx₁ hwy₁ _ _ hab]
    refine ⟨_, ?_, ?_, rfl⟩
    · rintro i hi
      apply_rules [add_nonneg, mul_nonneg, hwx₀, hwy₀]
    · simp only [Finset.sum_add_distrib, ← mul_sum, mul_one, *]
  · rintro _ ⟨w, hw₀, hw₁, rfl⟩
    exact
      s.centerMass_mem_convexHull (fun x hx => hw₀ _ hx) (hw₁.symm ▸ zero_lt_one) fun x hx => hx

/--
theorem `Finset.mem_convexHull` / 定理 `Finset.mem_convexHull`

English:
theorem Finset.mem_convexHull
  given: {s : Finset E} {x : E}
  statement: x in convexHull R (s : Set E) ↔
  proof: by
  rw [Finset.convexHull_eq]; rw [Set.mem_ofPred_eq]

中文:
定理 有限集.mem_convexHull
  条件: {s : 有限集 E} {x : E}
  结论: x in convexHull R (s : 集合 E) ↔
  证明: by
  rw [Finset.convexHull_eq]; rw [Set.mem_ofPred_eq]

Depends on / 依赖: Finset, Finset.convexHull_eq, Set.mem_ofPred_eq, convexHull_eq, mem_ofPred_eq
-/
theorem Finset.mem_convexHull {s : Finset E} {x : E} : x in convexHull R (s : Set E) ↔
    exists w : E -> R, (forall y in s, 0 <= w y) ∧ ∑ y in s, w y = 1 ∧ s.centerMass w id = x := by
  rw [Finset.convexHull_eq]; rw [Set.mem_ofPred_eq]

/--
lemma `Finset.mem_convexHull'` / 引理 `Finset.mem_convexHull'`

English:
lemma Finset.mem_convexHull'
  given: {s : Finset E} {x : E}
  proof: by
  rw [mem_convexHull]
refine exists_congr fun w => and_congr_right' and_congr_right fun hw => ?_
  simp_rw [centerMass_eq_of_sum_1 _ _ hw, id_eq]

中文:
引理 有限集.mem_convexHull'
  条件: {s : 有限集 E} {x : E}
  证明: by
  rw [mem_convexHull]
refine exists_congr fun w => and_congr_right' and_congr_right fun hw => ?_
  simp_rw [centerMass_eq_of_sum_1 _ _ hw, id_eq]

Depends on / 依赖: and_congr_right, centerMass_eq_of_sum_1, exists_congr, id_eq, mem_convexHull, simp_rw
-/
lemma Finset.mem_convexHull' {s : Finset E} {x : E} :
    x in convexHull R (s : Set E) ↔
      exists w : E -> R, (forall y in s, 0 <= w y) ∧ ∑ y in s, w y = 1 ∧ ∑ y in s, w y • y = x := by
  rw [mem_convexHull]
refine exists_congr fun w => and_congr_right' and_congr_right fun hw => ?_
  simp_rw [centerMass_eq_of_sum_1 _ _ hw, id_eq]

/--
theorem `Set.Finite.convexHull_eq` / 定理 `Set.Finite.convexHull_eq`

English:
theorem Set.Finite.convexHull_eq
  given: {s : Set E} (hs : s.Finite)
  statement: convexHull R s =
  proof: by
  simpa only [Set.Finite.coe_toFinset, Set.Finite.mem_toFinset, exists_prop] using
    hs.toFinset.convexHull_eq

中文:
定理 集合.有限.convexHull_eq
  条件: {s : 集合 E} (hs : s.有限)
  结论: convexHull R s =
  证明: by
  simpa only [Set.Finite.coe_toFinset, Set.Finite.mem_toFinset, exists_prop] using
    hs.toFinset.convexHull_eq

Depends on / 依赖: Finite, Set.Finite.coe_toFinset, Set.Finite.mem_toFinset, coe_toFinset, convexHull_eq, exists_prop, hs.toFinset.convexHull_eq, mem_toFinset, toFinset
-/
theorem Set.Finite.convexHull_eq {s : Set E} (hs : s.Finite) : convexHull R s =
    { x : E | exists w : E -> R, (forall y in s, 0 <= w y) ∧ ∑ y in hs.toFinset, w y = 1 ∧
      hs.toFinset.centerMass w id = x } := by
  simpa only [Set.Finite.coe_toFinset, Set.Finite.mem_toFinset, exists_prop] using
    hs.toFinset.convexHull_eq

/--
theorem `convexHull_eq_union_convexHull_finite_subsets` / 定理 `convexHull_eq_union_convexHull_finite_subsets`

English:
theorem convexHull_eq_union_convexHull_finite_subsets
  given: (s : Set E)
  proof: by
  classical
  refine Subset.antisymm ?_ ?_
  · rw [_root_.convexHull_eq]
    rintro x ⟨ι, t, w, z, hw₀, hw₁, hz, rfl⟩
    simp only [mem_iUnion]
    refine ⟨t.image z, ?_, ?_⟩
    · rw [coe_image, Set.image_subset_iff]
      exact hz
    · apply t.centerMass_mem_convexHull hw₀
      · simp only [hw₁, zero_lt_one]
      · exact fun i hi => Finset.mem_coe.2 (Finset.mem_image_of_mem _ hi)
  · exact iUnion_subset fun i => iUnion_subset convexHull_mono

中文:
定理 convexHull_eq_union_convexHull_finite_subsets
  条件: (s : 集合 E)
  证明: by
  classical
  refine Subset.antisymm ?_ ?_
  · rw [_root_.convexHull_eq]
    rintro x ⟨ι, t, w, z, hw₀, hw₁, hz, rfl⟩
    simp only [mem_iUnion]
    refine ⟨t.image z, ?_, ?_⟩
    · rw [coe_image, Set.image_subset_iff]
      exact hz
    · apply t.centerMass_mem_convexHull hw₀
      · simp only [hw₁, zero_lt_one]
      · exact fun i hi => Finset.mem_coe.2 (Finset.mem_image_of_mem _ hi)
  · exact iUnion_subset fun i => iUnion_subset convexHull_mono

Depends on / 依赖: Finset, Finset.mem_coe, Finset.mem_image_of_mem, Set.image_subset_iff, Subset, Subset.antisymm, _root_, _root_.convexHull_eq, antisymm, centerMass_mem_convexHull, classical, coe_image, convexHull_eq, convexHull_mono, iUnion_subset, image_subset_iff, mem_coe, mem_iUnion, mem_image_of_mem, t.centerMass_mem_convexHull
-/
theorem convexHull_eq_union_convexHull_finite_subsets (s : Set E) :
    convexHull R s = ⋃ (t : Finset E) (_ : ↑t subseteq s), convexHull R ↑t := by
  classical
  refine Subset.antisymm ?_ ?_
  · rw [_root_.convexHull_eq]
    rintro x ⟨ι, t, w, z, hw₀, hw₁, hz, rfl⟩
    simp only [mem_iUnion]
    refine ⟨t.image z, ?_, ?_⟩
    · rw [coe_image, Set.image_subset_iff]
      exact hz
    · apply t.centerMass_mem_convexHull hw₀
      · simp only [hw₁, zero_lt_one]
      · exact fun i hi => Finset.mem_coe.2 (Finset.mem_image_of_mem _ hi)
  · exact iUnion_subset fun i => iUnion_subset convexHull_mono

/--
theorem `vectorSpan_segment` / 定理 `vectorSpan_segment`

English:
theorem vectorSpan_segment
  given: {p₁ p₂ : E}
  proof: by
  rw [← convexHull_pair]; rw [← direction_affineSpan]; rw [affineSpan_convexHull]; rw [direction_affineSpan]; rw [vectorSpan_pair_rev]; rw [vsub_eq_sub]

中文:
定理 vectorSpan_segment
  条件: {p₁ p₂ : E}
  证明: by
  rw [← convexHull_pair]; rw [← direction_affineSpan]; rw [affineSpan_convexHull]; rw [direction_affineSpan]; rw [vectorSpan_pair_rev]; rw [vsub_eq_sub]

Depends on / 依赖: affineSpan_convexHull, convexHull_pair, direction_affineSpan, vectorSpan_pair_rev, vsub_eq_sub
-/
theorem vectorSpan_segment {p₁ p₂ : E} :
    vectorSpan R (segment R p₁ p₂) = R ∙ (p₂ -ᵥ p₁) := by
  rw [← convexHull_pair]; rw [← direction_affineSpan]; rw [affineSpan_convexHull]; rw [direction_affineSpan]; rw [vectorSpan_pair_rev]; rw [vsub_eq_sub]

/--
theorem `mk_mem_convexHull_prod` / 定理 `mk_mem_convexHull_prod`

English:
theorem mk_mem_convexHull_prod
  statement: {t : Set F} {x : E} {y : F} (hx : x in convexHull R s)
  proof: by
  rw [mem_convexHull_iff_exists_fintype] at hx hy ⊢
  obtain ⟨ι, _, w, f, hw₀, hw₁, hfs, hf⟩ := hx
  obtain ⟨κ, _, v, g, hv₀, hv₁, hgt, hg⟩ := hy
  have h_sum : ∑ i : ι × κ, w i.1 * v i.2 = 1 := by
    rw [Fintype.sum_prod_type]; rw [← sum_mul_sum]; rw [hw₁]; rw [hv₁]; rw [mul_one]
  refine ⟨ι × κ, inferInstance, fun p => w p.1 * v p.2, fun p => (f p.1, g p.2),
    fun p => mul_nonneg (hw₀ _) (hv₀ _), h_sum, fun p => ⟨hfs _, hgt _⟩, ?_⟩
  ext
  · simp_rw [Prod.fst_sum, Prod.smul_mk, Fintype.sum_prod_type, mul_comm (w _), mul_smul,
      sum_comm (γ := ι), ← Fintype.sum_smul_sum, hv₁, one_smul, hf]
  · simp_rw [Prod.snd_sum, Prod.smul_mk, Fintype.sum_prod_type, mul_smul, ← Fintype.sum_smul_sum,
      hw₁, one_smul, hg]

@[simp]

中文:
定理 mk_mem_convexHull_prod
  结论: {t : 集合 F} {x : E} {y : F} (hx : x in convexHull R s)
  证明: by
  rw [mem_convexHull_iff_exists_fintype] at hx hy ⊢
  obtain ⟨ι, _, w, f, hw₀, hw₁, hfs, hf⟩ := hx
  obtain ⟨κ, _, v, g, hv₀, hv₁, hgt, hg⟩ := hy
  have h_sum : ∑ i : ι × κ, w i.1 * v i.2 = 1 := by
    rw [Fintype.sum_prod_type]; rw [← sum_mul_sum]; rw [hw₁]; rw [hv₁]; rw [mul_one]
  refine ⟨ι × κ, inferInstance, fun p => w p.1 * v p.2, fun p => (f p.1, g p.2),
    fun p => mul_nonneg (hw₀ _) (hv₀ _), h_sum, fun p => ⟨hfs _, hgt _⟩, ?_⟩
  ext
  · simp_rw [Prod.fst_sum, Prod.smul_mk, Fintype.sum_prod_type, mul_comm (w _), mul_smul,
      sum_comm (γ := ι), ← Fintype.sum_smul_sum, hv₁, one_smul, hf]
  · simp_rw [Prod.snd_sum, Prod.smul_mk, Fintype.sum_prod_type, mul_smul, ← Fintype.sum_smul_sum,
      hw₁, one_smul, hg]

@[simp]

Depends on / 依赖: Fintype, Fintype.sum_prod_type, Prod.fst_sum, Prod.smul_mk, fst_sum, h_sum, mem_convexHull_iff_exists_fintype, mul_comm, mul_nonneg, mul_one, simp_rw, smul_mk, sum_mul_sum, sum_prod_type
-/
theorem mk_mem_convexHull_prod {t : Set F} {x : E} {y : F} (hx : x in convexHull R s)
    (hy : y in convexHull R t) : (x, y) in convexHull R (s ×ˢ t) := by
  rw [mem_convexHull_iff_exists_fintype] at hx hy ⊢
  obtain ⟨ι, _, w, f, hw₀, hw₁, hfs, hf⟩ := hx
  obtain ⟨κ, _, v, g, hv₀, hv₁, hgt, hg⟩ := hy
  have h_sum : ∑ i : ι × κ, w i.1 * v i.2 = 1 := by
    rw [Fintype.sum_prod_type]; rw [← sum_mul_sum]; rw [hw₁]; rw [hv₁]; rw [mul_one]
  refine ⟨ι × κ, inferInstance, fun p => w p.1 * v p.2, fun p => (f p.1, g p.2),
    fun p => mul_nonneg (hw₀ _) (hv₀ _), h_sum, fun p => ⟨hfs _, hgt _⟩, ?_⟩
  ext
  · simp_rw [Prod.fst_sum, Prod.smul_mk, Fintype.sum_prod_type, mul_comm (w _), mul_smul,
      sum_comm (γ := ι), ← Fintype.sum_smul_sum, hv₁, one_smul, hf]
  · simp_rw [Prod.snd_sum, Prod.smul_mk, Fintype.sum_prod_type, mul_smul, ← Fintype.sum_smul_sum,
      hw₁, one_smul, hg]

@[simp]
/--
theorem `convexHull_prod` / 定理 `convexHull_prod`

English:
theorem convexHull_prod
  given: (s : Set E) (t : Set F)
  proof: Subset.antisymm
      (convexHull_min (prod_mono (subset_convexHull _ _) <| subset_convexHull _ _) <|
(convex_convexHull _ _).prod convex_convexHull _ _) <|
    prod_subset_iff.2 fun _ hx _ => mk_mem_convexHull_prod hx

中文:
定理 convexHull_prod
  条件: (s : 集合 E) (t : 集合 F)
  证明: Subset.antisymm
      (convexHull_min (prod_mono (subset_convexHull _ _) <| subset_convexHull _ _) <|
(convex_convexHull _ _).prod convex_convexHull _ _) <|
    prod_subset_iff.2 fun _ hx _ => mk_mem_convexHull_prod hx

Depends on / 依赖: Subset, Subset.antisymm, antisymm, convexHull_min, convex_convexHull, mk_mem_convexHull_prod, prod_mono, prod_subset_iff, subset_convexHull
-/
theorem convexHull_prod (s : Set E) (t : Set F) :
    convexHull R (s ×ˢ t) = convexHull R s ×ˢ convexHull R t :=
  Subset.antisymm
      (convexHull_min (prod_mono (subset_convexHull _ _) <| subset_convexHull _ _) <|
(convex_convexHull _ _).prod convex_convexHull _ _) <|
    prod_subset_iff.2 fun _ hx _ => mk_mem_convexHull_prod hx

/--
theorem `convexHull_add` / 定理 `convexHull_add`

English:
theorem convexHull_add
  given: (s t : Set E)
  statement: convexHull R (s + t) = convexHull R s + convexHull R t
  proof: by
  simp_rw [← add_image_prod, ← IsLinearMap.isLinearMap_add.image_convexHull, convexHull_prod]

中文:
定理 convexHull_add
  条件: (s t : 集合 E)
  结论: convexHull R (s + t) = convexHull R s + convexHull R t
  证明: by
  simp_rw [← add_image_prod, ← IsLinearMap.isLinearMap_add.image_convexHull, convexHull_prod]

Depends on / 依赖: IsLinearMap, IsLinearMap.isLinearMap_add.image_convexHull, add_image_prod, convexHull_prod, image_convexHull, isLinearMap_add, simp_rw
-/
theorem convexHull_add (s t : Set E) : convexHull R (s + t) = convexHull R s + convexHull R t := by
  simp_rw [← add_image_prod, ← IsLinearMap.isLinearMap_add.image_convexHull, convexHull_prod]

variable (R E)

/-- `convexHull` is an additive monoid morphism under pointwise addition. -/
@[simps]
/--
Definition of `convexHullAddMonoidHom` / `convexHullAddMonoidHom` 的定义

English:
definition convexHullAddMonoidHom
  signature: : Set E ->+ Set E where
  body: convexHull R
  map_add' := convexHull_add
  map_zero' := convexHull_zero

中文:
定义 convexHullAddMonoidHom
  签名: : 集合 E ->+ 集合 E where
  定义体: convexHull R
  map_add' := convexHull_add
  map_zero' := convexHull_zero

Depends on / 依赖: convexHull
-/
noncomputable def convexHullAddMonoidHom : Set E ->+ Set E where
  toFun := convexHull R
  map_add' := convexHull_add
  map_zero' := convexHull_zero

variable {R E}

/--
theorem `convexHull_sub` / 定理 `convexHull_sub`

English:
theorem convexHull_sub
  given: (s t : Set E)
  statement: convexHull R (s - t) = convexHull R s - convexHull R t
  proof: by
  simp_rw [sub_eq_add_neg, convexHull_add, ← convexHull_neg]

中文:
定理 convexHull_sub
  条件: (s t : 集合 E)
  结论: convexHull R (s - t) = convexHull R s - convexHull R t
  证明: by
  simp_rw [sub_eq_add_neg, convexHull_add, ← convexHull_neg]

Depends on / 依赖: convexHull_add, convexHull_neg, simp_rw, sub_eq_add_neg
-/
theorem convexHull_sub (s t : Set E) : convexHull R (s - t) = convexHull R s - convexHull R t := by
  simp_rw [sub_eq_add_neg, convexHull_add, ← convexHull_neg]

/--
theorem `convexHull_list_sum` / 定理 `convexHull_list_sum`

English:
theorem convexHull_list_sum
  given: (l : List (Set E))
  statement: convexHull R l.sum = (l.map <| convexHull R).sum
  proof: map_list_sum (convexHullAddMonoidHom R E) l

中文:
定理 convexHull_list_sum
  条件: (l : 列表 (集合 E))
  结论: convexHull R l.求和 = (l.map <| convexHull R).求和
  证明: map_list_sum (convexHullAddMonoidHom R E) l

Depends on / 依赖: convexHullAddMonoidHom, map_list_sum
-/
theorem convexHull_list_sum (l : List (Set E)) : convexHull R l.sum = (l.map <| convexHull R).sum :=
  map_list_sum (convexHullAddMonoidHom R E) l

/--
theorem `convexHull_multiset_sum` / 定理 `convexHull_multiset_sum`

English:
theorem convexHull_multiset_sum
  given: (s : Multiset (Set E))
  proof: map_multiset_sum (convexHullAddMonoidHom R E) s

中文:
定理 convexHull_multiset_sum
  条件: (s : Multiset (集合 E))
  证明: map_multiset_sum (convexHullAddMonoidHom R E) s

Depends on / 依赖: convexHullAddMonoidHom, map_multiset_sum
-/
theorem convexHull_multiset_sum (s : Multiset (Set E)) :
    convexHull R s.sum = (s.map <| convexHull R).sum :=
  map_multiset_sum (convexHullAddMonoidHom R E) s

/--
theorem `convexHull_sum` / 定理 `convexHull_sum`

English:
theorem convexHull_sum
  given: {ι} (s : Finset ι) (t : ι -> Set E)
  proof: map_sum (convexHullAddMonoidHom R E) _ _

中文:
定理 convexHull_sum
  条件: {ι} (s : 有限集 ι) (t : ι -> 集合 E)
  证明: map_sum (convexHullAddMonoidHom R E) _ _

Depends on / 依赖: convexHullAddMonoidHom, map_sum
-/
theorem convexHull_sum {ι} (s : Finset ι) (t : ι -> Set E) :
    convexHull R (∑ i in s, t i) = ∑ i in s, convexHull R (t i) :=
  map_sum (convexHullAddMonoidHom R E) _ _

/--
theorem `AffineBasis.convexHull_eq_nonneg_coord` / 定理 `AffineBasis.convexHull_eq_nonneg_coord`

English:
theorem AffineBasis.convexHull_eq_nonneg_coord
  given: {ι : Type*} (b : AffineBasis ι R E)
  proof: by
  rw [convexHull_range_eq_exists_affineCombination]
  ext x
  refine ⟨?_, fun hx => ?_⟩
  · rintro ⟨s, w, hw₀, hw₁, rfl⟩ i
    by_cases hi : i in s
    · rw [b.coord_apply_combination_of_mem hi hw₁]
      exact hw₀ i hi
    · rw [b.coord_apply_combination_of_notMem hi hw₁]
  · have hx' : x in affineSpan R (range b) := by
      rw [b.tot]
      exact AffineSubspace.mem_top R E x
    obtain ⟨s, w, hw₁, rfl⟩ := (mem_affineSpan_iff_eq_affineCombination R E).mp hx'
    refine ⟨s, w, ?_, hw₁, rfl⟩
    intro i hi
    specialize hx i
    rw [b.coord_apply_combination_of_mem hi hw₁] at hx
    exact hx

中文:
定理 仿射基.convexHull_eq_nonneg_coord
  条件: {ι : 类型} (b : 仿射基 ι R E)
  证明: by
  rw [convexHull_range_eq_exists_affineCombination]
  ext x
  refine ⟨?_, fun hx => ?_⟩
  · rintro ⟨s, w, hw₀, hw₁, rfl⟩ i
    by_cases hi : i in s
    · rw [b.coord_apply_combination_of_mem hi hw₁]
      exact hw₀ i hi
    · rw [b.coord_apply_combination_of_notMem hi hw₁]
  · have hx' : x in affineSpan R (range b) := by
      rw [b.tot]
      exact AffineSubspace.mem_top R E x
    obtain ⟨s, w, hw₁, rfl⟩ := (mem_affineSpan_iff_eq_affineCombination R E).mp hx'
    refine ⟨s, w, ?_, hw₁, rfl⟩
    intro i hi
    specialize hx i
    rw [b.coord_apply_combination_of_mem hi hw₁] at hx
    exact hx

Depends on / 依赖: AffineSubspace, AffineSubspace.mem_top, affineSpan, b.coord_apply_com, b.coord_apply_combination_of_mem, b.coord_apply_combination_of_notMem, b.tot, convexHull_range_eq_exists_affineCombination, coord_apply_com, coord_apply_combination_of_mem, coord_apply_combination_of_notMem, mem_affineSpan_iff_eq_affineCombination, mem_top, specialize
-/
theorem AffineBasis.convexHull_eq_nonneg_coord {ι : Type*} (b : AffineBasis ι R E) :
    convexHull R (range b) = { x | forall i, 0 <= b.coord i x } := by
  rw [convexHull_range_eq_exists_affineCombination]
  ext x
  refine ⟨?_, fun hx => ?_⟩
  · rintro ⟨s, w, hw₀, hw₁, rfl⟩ i
    by_cases hi : i in s
    · rw [b.coord_apply_combination_of_mem hi hw₁]
      exact hw₀ i hi
    · rw [b.coord_apply_combination_of_notMem hi hw₁]
  · have hx' : x in affineSpan R (range b) := by
      rw [b.tot]
      exact AffineSubspace.mem_top R E x
    obtain ⟨s, w, hw₁, rfl⟩ := (mem_affineSpan_iff_eq_affineCombination R E).mp hx'
    refine ⟨s, w, ?_, hw₁, rfl⟩
    intro i hi
    specialize hx i
    rw [b.coord_apply_combination_of_mem hi hw₁] at hx
    exact hx

variable {s t t₁ t₂ : Finset E}

/--
lemma `AffineIndependent.convexHull_inter` / 引理 `AffineIndependent.convexHull_inter`

English:
lemma AffineIndependent.convexHull_inter
  statement: (hs : AffineIndependent R ((↑) : s -> E))
  proof: by
  classical
  refine (Set.subset_inter (convexHull_mono inf_le_left) <|
    convexHull_mono inf_le_right).antisymm ?_
  simp_rw [Set.subset_def, mem_inter_iff, Set.inf_eq_inter, ← coe_inter, mem_convexHull']
  rintro x ⟨⟨w₁, h₁w₁, h₂w₁, h₃w₁⟩, w₂, -, h₂w₂, h₃w₂⟩
  let w (x : E) : R := (if x in t₁ then w₁ x else 0) - if x in t₂ then w₂ x else 0
  have h₁w : ∑ i in s, w i = 0 := by simp [w, Finset.inter_eq_right.2, *]
replace hs := hs.eq_zero_of_sum_eq_zero_subtype h₁w by
    simp only [w, sub_smul, zero_smul, ite_smul, Finset.sum_sub_distrib, ← Finset.sum_filter, h₃w₁,
      Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 ht₁, Finset.inter_eq_right.2 ht₂, h₃w₂,
      sub_self]
  have ht (x) (hx₁ : x in t₁) (hx₂ : x ∉ t₂) : w₁ x = 0 := by
    simpa [w, hx₁, hx₂] using hs _ (ht₁ hx₁)
  refine ⟨w₁, ?_, ?_, ?_⟩
  · simp only [and_imp, Finset.mem_inter]
    exact fun y hy₁ _ => h₁w₁ y hy₁
  all_goals
  · rwa [sum_subset inter_subset_left]
    rintro x
    simp_intro hx₁ hx₂
    simp [ht x hx₁ hx₂]

中文:
引理 AffineIndependent.convexHull_inter
  结论: (hs : AffineIndependent R ((↑) : s -> E))
  证明: by
  classical
  refine (Set.subset_inter (convexHull_mono inf_le_left) <|
    convexHull_mono inf_le_right).antisymm ?_
  simp_rw [Set.subset_def, mem_inter_iff, Set.inf_eq_inter, ← coe_inter, mem_convexHull']
  rintro x ⟨⟨w₁, h₁w₁, h₂w₁, h₃w₁⟩, w₂, -, h₂w₂, h₃w₂⟩
  let w (x : E) : R := (if x in t₁ then w₁ x else 0) - if x in t₂ then w₂ x else 0
  have h₁w : ∑ i in s, w i = 0 := by simp [w, Finset.inter_eq_right.2, *]
replace hs := hs.eq_zero_of_sum_eq_zero_subtype h₁w by
    simp only [w, sub_smul, zero_smul, ite_smul, Finset.sum_sub_distrib, ← Finset.sum_filter, h₃w₁,
      Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 ht₁, Finset.inter_eq_right.2 ht₂, h₃w₂,
      sub_self]
  have ht (x) (hx₁ : x in t₁) (hx₂ : x ∉ t₂) : w₁ x = 0 := by
    simpa [w, hx₁, hx₂] using hs _ (ht₁ hx₁)
  refine ⟨w₁, ?_, ?_, ?_⟩
  · simp only [and_imp, Finset.mem_inter]
    exact fun y hy₁ _ => h₁w₁ y hy₁
  all_goals
  · rwa [sum_subset inter_subset_left]
    rintro x
    simp_intro hx₁ hx₂
    simp [ht x hx₁ hx₂]

Depends on / 依赖: Finset, Finset.inter_eq_right, Set.inf_eq_inter, Set.subset_def, Set.subset_inter, antisymm, classical, coe_inter, convexHull_mono, eq_zero_of_sum_eq_zero_subtype, hs.eq_zero_of_sum_eq_zero_subtype, inf_eq_inter, inf_le_left, inf_le_right, inter_eq_right, mem_convexHull, mem_inter_iff, replace, simp_rw, sub_smul
-/
lemma AffineIndependent.convexHull_inter (hs : AffineIndependent R ((↑) : s -> E))
    (ht₁ : t₁ subseteq s) (ht₂ : t₂ subseteq s) :
    convexHull R (t₁ inter t₂ : Set E) = convexHull R t₁ inter convexHull R t₂ := by
  classical
  refine (Set.subset_inter (convexHull_mono inf_le_left) <|
    convexHull_mono inf_le_right).antisymm ?_
  simp_rw [Set.subset_def, mem_inter_iff, Set.inf_eq_inter, ← coe_inter, mem_convexHull']
  rintro x ⟨⟨w₁, h₁w₁, h₂w₁, h₃w₁⟩, w₂, -, h₂w₂, h₃w₂⟩
  let w (x : E) : R := (if x in t₁ then w₁ x else 0) - if x in t₂ then w₂ x else 0
  have h₁w : ∑ i in s, w i = 0 := by simp [w, Finset.inter_eq_right.2, *]
replace hs := hs.eq_zero_of_sum_eq_zero_subtype h₁w by
    simp only [w, sub_smul, zero_smul, ite_smul, Finset.sum_sub_distrib, ← Finset.sum_filter, h₃w₁,
      Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 ht₁, Finset.inter_eq_right.2 ht₂, h₃w₂,
      sub_self]
  have ht (x) (hx₁ : x in t₁) (hx₂ : x ∉ t₂) : w₁ x = 0 := by
    simpa [w, hx₁, hx₂] using hs _ (ht₁ hx₁)
  refine ⟨w₁, ?_, ?_, ?_⟩
  · simp only [and_imp, Finset.mem_inter]
    exact fun y hy₁ _ => h₁w₁ y hy₁
  all_goals
  · rwa [sum_subset inter_subset_left]
    rintro x
    simp_intro hx₁ hx₂
    simp [ht x hx₁ hx₂]

/--
lemma `AffineIndependent.convexHull_inter'` / 引理 `AffineIndependent.convexHull_inter'`

English:
lemma AffineIndependent.convexHull_inter'
  statement: [DecidableEq E]
  proof: hs.convexHull_inter subset_union_left subset_union_right

中文:
引理 AffineIndependent.convexHull_inter'
  结论: [DecidableEq E]
  证明: hs.convexHull_inter subset_union_left subset_union_right

Depends on / 依赖: convexHull_inter, hs.convexHull_inter, subset_union_left, subset_union_right
-/
lemma AffineIndependent.convexHull_inter' [DecidableEq E]
    (hs : AffineIndependent R ((↑) : ↑(t₁ union t₂) -> E)) :
    convexHull R (t₁ inter t₂ : Set E) = convexHull R t₁ inter convexHull R t₂ :=
  hs.convexHull_inter subset_union_left subset_union_right

end

section pi
variable {𝕜 ι : Type*} {E : ι -> Type*} [Finite ι] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [Π i, AddCommGroup (E i)] [Π i, Module 𝕜 (E i)] {s : Set ι} {t : Π i, Set (E i)} {x : Π i, E i}

open Finset Fintype

/--
lemma `mem_convexHull_pi` / 引理 `mem_convexHull_pi`

English:
lemma mem_convexHull_pi
  given: (h : forall i in s, x i in convexHull 𝕜 (t i))
  statement: x in convexHull 𝕜 (s.pi t)
  proof: by
  classical
  cases nonempty_fintype ι
  wlog hs : s = Set.univ generalizing s t
  · rw [← pi_univ_ite]
    refine this (fun i _ => ?_) rfl
    split_ifs with hi
    · exact h i hi
    · simp
  subst hs
  simp only [Set.mem_univ, mem_convexHull_iff_exists_fintype, true_implies] at h
  choose κ _ w f hw₀ hw₁ hft hf using h
  refine mem_convexHull_of_exists_fintype (fun k : Π i, κ i => ∏ i, w i (k i)) (fun g i => f _ (g i))
    (fun g => prod_nonneg fun _ _ => hw₀ _ _) ?_ (fun _ _ _ => hft _ _) ?_
  · rw [← Fintype.prod_sum]
    exact prod_eq_one fun _ _ => hw₁ _
  ext i
  calc
    _ = ∑ g : forall i, κ i, (∏ i, w i (g i)) • f i (g i) := by
      simp only [Finset.sum_apply, Pi.smul_apply]
    _ = ∑ j : κ i, ∑ g : {g : forall k, κ k // g i = j},
          (∏ k, w k (g.1 k)) • f i ((g : forall i, κ i) i) := by
      rw [← Fintype.sum_fiberwise fun g : forall k]; rw [κ k => g i]
    _ = ∑ j : κ i, (∑ g : {g : forall k, κ k // g i = j}, ∏ k, w k (g.1 k)) • f i j := by
      simp_rw [sum_smul]
      congr! with j _ g _
      exact g.2
    _ = ∑ j : κ i, w i j • f i j := ?_
    _ = x i := hf _
  congr! with j _
  calc
    ∑ g : {g : forall k, κ k // g i = j}, ∏ k, w k (g.1 k)
      = ∑ g in piFinset fun k => if hk : k = i then hk ▸ {j} else univ, ∏ k, w k (g k) :=
      Finset.sum_bij' (fun g _ => g) (fun g hg => ⟨g, by simpa using mem_piFinset.1 hg i⟩)
        (by aesop) (by simp) (by simp) (by simp) (by simp)
    _ = w i j := by
      rw [← prod_univ_sum]; rw [← prod_mul_prod_compl]; rw [Finset.prod_singleton]; rw [Finset.sum_eq_single]; rw [Finset.prod_eq_one]; rw [mul_one] <;> simp +contextual [hw₁]

中文:
引理 mem_convexHull_pi
  条件: (h : 对任意 i in s, x i in convexHull 𝕜 (t i))
  结论: x in convexHull 𝕜 (s.pi t)
  证明: by
  classical
  cases nonempty_fintype ι
  wlog hs : s = Set.univ generalizing s t
  · rw [← pi_univ_ite]
    refine this (fun i _ => ?_) rfl
    split_ifs with hi
    · exact h i hi
    · simp
  subst hs
  simp only [Set.mem_univ, mem_convexHull_iff_exists_fintype, true_implies] at h
  choose κ _ w f hw₀ hw₁ hft hf using h
  refine mem_convexHull_of_exists_fintype (fun k : Π i, κ i => ∏ i, w i (k i)) (fun g i => f _ (g i))
    (fun g => prod_nonneg fun _ _ => hw₀ _ _) ?_ (fun _ _ _ => hft _ _) ?_
  · rw [← Fintype.prod_sum]
    exact prod_eq_one fun _ _ => hw₁ _
  ext i
  calc
    _ = ∑ g : forall i, κ i, (∏ i, w i (g i)) • f i (g i) := by
      simp only [Finset.sum_apply, Pi.smul_apply]
    _ = ∑ j : κ i, ∑ g : {g : forall k, κ k // g i = j},
          (∏ k, w k (g.1 k)) • f i ((g : forall i, κ i) i) := by
      rw [← Fintype.sum_fiberwise fun g : forall k]; rw [κ k => g i]
    _ = ∑ j : κ i, (∑ g : {g : forall k, κ k // g i = j}, ∏ k, w k (g.1 k)) • f i j := by
      simp_rw [sum_smul]
      congr! with j _ g _
      exact g.2
    _ = ∑ j : κ i, w i j • f i j := ?_
    _ = x i := hf _
  congr! with j _
  calc
    ∑ g : {g : forall k, κ k // g i = j}, ∏ k, w k (g.1 k)
      = ∑ g in piFinset fun k => if hk : k = i then hk ▸ {j} else univ, ∏ k, w k (g k) :=
      Finset.sum_bij' (fun g _ => g) (fun g hg => ⟨g, by simpa using mem_piFinset.1 hg i⟩)
        (by aesop) (by simp) (by simp) (by simp) (by simp)
    _ = w i j := by
      rw [← prod_univ_sum]; rw [← prod_mul_prod_compl]; rw [Finset.prod_singleton]; rw [Finset.sum_eq_single]; rw [Finset.prod_eq_one]; rw [mul_one] <;> simp +contextual [hw₁]

Depends on / 依赖: Fintype, Fintype.prod_sum, Set.mem_univ, Set.univ, classical, generalizing, mem_convexHull_iff_exists_fintype, mem_convexHull_of_exists_fintype, mem_univ, nonempty_fintype, pi_univ_ite, prod_nonneg, prod_sum, split_ifs, true_implies
-/
lemma mem_convexHull_pi (h : forall i in s, x i in convexHull 𝕜 (t i)) : x in convexHull 𝕜 (s.pi t) := by
  classical
  cases nonempty_fintype ι
  wlog hs : s = Set.univ generalizing s t
  · rw [← pi_univ_ite]
    refine this (fun i _ => ?_) rfl
    split_ifs with hi
    · exact h i hi
    · simp
  subst hs
  simp only [Set.mem_univ, mem_convexHull_iff_exists_fintype, true_implies] at h
  choose κ _ w f hw₀ hw₁ hft hf using h
  refine mem_convexHull_of_exists_fintype (fun k : Π i, κ i => ∏ i, w i (k i)) (fun g i => f _ (g i))
    (fun g => prod_nonneg fun _ _ => hw₀ _ _) ?_ (fun _ _ _ => hft _ _) ?_
  · rw [← Fintype.prod_sum]
    exact prod_eq_one fun _ _ => hw₁ _
  ext i
  calc
    _ = ∑ g : forall i, κ i, (∏ i, w i (g i)) • f i (g i) := by
      simp only [Finset.sum_apply, Pi.smul_apply]
    _ = ∑ j : κ i, ∑ g : {g : forall k, κ k // g i = j},
          (∏ k, w k (g.1 k)) • f i ((g : forall i, κ i) i) := by
      rw [← Fintype.sum_fiberwise fun g : forall k]; rw [κ k => g i]
    _ = ∑ j : κ i, (∑ g : {g : forall k, κ k // g i = j}, ∏ k, w k (g.1 k)) • f i j := by
      simp_rw [sum_smul]
      congr! with j _ g _
      exact g.2
    _ = ∑ j : κ i, w i j • f i j := ?_
    _ = x i := hf _
  congr! with j _
  calc
    ∑ g : {g : forall k, κ k // g i = j}, ∏ k, w k (g.1 k)
      = ∑ g in piFinset fun k => if hk : k = i then hk ▸ {j} else univ, ∏ k, w k (g k) :=
      Finset.sum_bij' (fun g _ => g) (fun g hg => ⟨g, by simpa using mem_piFinset.1 hg i⟩)
        (by aesop) (by simp) (by simp) (by simp) (by simp)
    _ = w i j := by
      rw [← prod_univ_sum]; rw [← prod_mul_prod_compl]; rw [Finset.prod_singleton]; rw [Finset.sum_eq_single]; rw [Finset.prod_eq_one]; rw [mul_one] <;> simp +contextual [hw₁]

/--
lemma `convexHull_pi` / 引理 `convexHull_pi`

English:
lemma convexHull_pi
  given: (s : Set ι) (t : Π i, Set (E i))
  proof: Set.Subset.antisymm (convexHull_min (Set.pi_mono fun _ _ => subset_convexHull _ _) <| convex_pi <|
    fun _ _ => convex_convexHull _ _) fun _ => mem_convexHull_pi

中文:
引理 convexHull_pi
  条件: (s : 集合 ι) (t : Π i, 集合 (E i))
  证明: Set.Subset.antisymm (convexHull_min (Set.pi_mono fun _ _ => subset_convexHull _ _) <| convex_pi <|
    fun _ _ => convex_convexHull _ _) fun _ => mem_convexHull_pi
-/
@[simp] lemma convexHull_pi (s : Set ι) (t : Π i, Set (E i)) :
    convexHull 𝕜 (s.pi t) = s.pi (fun i => convexHull 𝕜 (t i)) :=
  Set.Subset.antisymm (convexHull_min (Set.pi_mono fun _ _ => subset_convexHull _ _) <| convex_pi <|
    fun _ _ => convex_convexHull _ _) fun _ => mem_convexHull_pi

end pi

namespace Affine.Simplex

/--
theorem `convexHull_eq_closedInterior` / 定理 `convexHull_eq_closedInterior`

English:
theorem convexHull_eq_closedInterior
  statement: {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜]
  proof: by
  ext p
  rw [convexHull_range_eq_exists_affineCombination]; rw [Set.mem_ofPred]
  constructor <;> intro h
  · obtain ⟨u, w, hw, hw1, rfl⟩ := h
    have hw' : forall i in u, w i <= 1 := by
      intro i hi
      rw [← hw1]
      apply Finset.single_le_sum (fun j hj => hw j hj) hi
    have hw1' : ∑ i, (u : Set (Fin (n + 1))).indicator w i = 1 := by
      simpa [Finset.sum_indicator_subset _ u.subset_univ] using hw1
    rw [Finset.affineCombination_indicator_subset _ _ u.subset_univ]; rw [affineCombination_mem_closedInterior_iff hw1']
    intro i
    by_cases hi : i in (u : Set (Fin (n + 1))) <;> aesop
· obtain ⟨w, hw1, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype
      Set.mem_of_mem_of_subset h s.closedInterior_subset_affineSpan
    rw [affineCombination_mem_closedInterior_iff hw1] at h
    exact ⟨Finset.univ, w, fun i _ => (h i).1, hw1, rfl⟩

中文:
定理 convexHull_eq_closed整数erior
  结论: {𝕜 V : 类型} [域 𝕜] [线性序 𝕜]
  证明: by
  ext p
  rw [convexHull_range_eq_exists_affineCombination]; rw [Set.mem_ofPred]
  constructor <;> intro h
  · obtain ⟨u, w, hw, hw1, rfl⟩ := h
    have hw' : forall i in u, w i <= 1 := by
      intro i hi
      rw [← hw1]
      apply Finset.single_le_sum (fun j hj => hw j hj) hi
    have hw1' : ∑ i, (u : Set (Fin (n + 1))).indicator w i = 1 := by
      simpa [Finset.sum_indicator_subset _ u.subset_univ] using hw1
    rw [Finset.affineCombination_indicator_subset _ _ u.subset_univ]; rw [affineCombination_mem_closedInterior_iff hw1']
    intro i
    by_cases hi : i in (u : Set (Fin (n + 1))) <;> aesop
· obtain ⟨w, hw1, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype
      Set.mem_of_mem_of_subset h s.closedInterior_subset_affineSpan
    rw [affineCombination_mem_closedInterior_iff hw1] at h
    exact ⟨Finset.univ, w, fun i _ => (h i).1, hw1, rfl⟩
-/
@[simp] theorem convexHull_eq_closedInterior {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsOrderedRing 𝕜] [AddCommGroup V] [Module 𝕜 V] {n : Nat} (s : Simplex 𝕜 V n) :
    convexHull 𝕜 (Set.range s.points) = s.closedInterior := by
  ext p
  rw [convexHull_range_eq_exists_affineCombination]; rw [Set.mem_ofPred]
  constructor <;> intro h
  · obtain ⟨u, w, hw, hw1, rfl⟩ := h
    have hw' : forall i in u, w i <= 1 := by
      intro i hi
      rw [← hw1]
      apply Finset.single_le_sum (fun j hj => hw j hj) hi
    have hw1' : ∑ i, (u : Set (Fin (n + 1))).indicator w i = 1 := by
      simpa [Finset.sum_indicator_subset _ u.subset_univ] using hw1
    rw [Finset.affineCombination_indicator_subset _ _ u.subset_univ]; rw [affineCombination_mem_closedInterior_iff hw1']
    intro i
    by_cases hi : i in (u : Set (Fin (n + 1))) <;> aesop
· obtain ⟨w, hw1, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype
      Set.mem_of_mem_of_subset h s.closedInterior_subset_affineSpan
    rw [affineCombination_mem_closedInterior_iff hw1] at h
    exact ⟨Finset.univ, w, fun i _ => (h i).1, hw1, rfl⟩

end Affine.Simplex
