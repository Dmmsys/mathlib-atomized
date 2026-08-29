/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic

/-!
# Shifting an affine subspace towards a point

This file introduces a "shift" transformation of affine subspace, where the subspace is translated
relatively to a point `c`. This is equivalent to `AffineSubspace.map (AffineEquiv.constVAdd ..)`,
but hides the detail of arbitrarily choosing a point in the subspace.

Shifting is controlled by a parameter `r`, indicating how far the output space is to `c`. We set
`r = 0` to mean the output space passes through `c` (See `AffineSubspace.shift_zero`),
while `r = 1` means not moving the input space at all (See `AffineSubspace.shift_one`).
With this convention, this transformation is also equivalent to `AffineSubspace.map (homothety c r)`
when `r` is a unit.

## Main declarations
* `AffineSubspace.shift` defines the shift transformation.
* `AffineSubspace.shift_eq` shows the shift transformation is equivalent to translation.
* `AffineSubspace.shift_eq_map_homothety` shows the shift transformation is equivalent to homothety.
-/

public section

open Module Submodule Finset AffineMap AffineSubspace

variable {k V P : Type*}

namespace AffineSubspace

section Ring
variable [Ring k] [AddCommGroup V] [AddTorsor V P] [Module k V]

open scoped Classical in
/-- `AffineSubspace.shift s c r` is an affine subspace parallel to `s`, where an arbitrary point on
`s` is moved towards `c` with linear interpolation by `r`. When `r = 0`, that point is moved onto
`c`. When `r = 1`, that point stays at the original position. A different choice of the point will
not affect the output (See `AffineSubspace.shift_eq`).

We define `AffineSubspace.shift ⊥ c r = ⊥` (See `AffineSubspace.shift_bot`). -/
noncomputable
/--
Definition of `shift` / `shift` 的定义

English:
definition shift
  signature: (s : AffineSubspace k P) (c : P) (r : k)
  body: if h : Nonempty s then
s.map AffineEquiv.constVAdd k P ((1 - r) • (c -ᵥ h.some))
  else
    ⊥

@[simp]

中文:
定义 shift
  签名: (s : AffineSubspace k P) (c : P) (r : k)
  定义体: if h : Nonempty s then
s.map AffineEquiv.constVAdd k P ((1 - r) • (c -ᵥ h.some))
  else
    ⊥

@[simp]

Depends on / 依赖: AffineEquiv, AffineEquiv.constVAdd, Nonempty, constVAdd, h.some, s.map
-/
def shift (s : AffineSubspace k P) (c : P) (r : k) : AffineSubspace k P :=
  if h : Nonempty s then
s.map AffineEquiv.constVAdd k P ((1 - r) • (c -ᵥ h.some))
  else
    ⊥

@[simp]
/--
theorem `direction_shift` / 定理 `direction_shift`

English:
theorem direction_shift
  given: (s : AffineSubspace k P) (c : P) (r : k)
  proof: by
  rcases s.eq_bot_or_nonempty with h | h
  · simp [shift, h]
  have h : Nonempty s := by simpa using! h
  simp [shift, h]

中文:
定理 direction_shift
  条件: (s : AffineSubspace k P) (c : P) (r : k)
  证明: by
  rcases s.eq_bot_or_nonempty with h | h
  · simp [shift, h]
  have h : Nonempty s := by simpa using! h
  simp [shift, h]

Depends on / 依赖: Nonempty, eq_bot_or_nonempty, s.eq_bot_or_nonempty
-/
theorem direction_shift (s : AffineSubspace k P) (c : P) (r : k) :
    (s.shift c r).direction = s.direction := by
  rcases s.eq_bot_or_nonempty with h | h
  · simp [shift, h]
  have h : Nonempty s := by simpa using! h
  simp [shift, h]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `shift_top` / 定理 `shift_top`

English:
theorem shift_top
  given: (c : P) (r : k)
  statement: shift ⊤ c r = ⊤
  proof: by
  simp [shift, AffineEquiv.surjective]

@[simp]

中文:
定理 shift_top
  条件: (c : P) (r : k)
  结论: shift ⊤ c r = ⊤
  证明: by
  simp [shift, AffineEquiv.surjective]

@[simp]

Depends on / 依赖: AffineEquiv, AffineEquiv.surjective, surjective
-/
theorem shift_top (c : P) (r : k) : shift ⊤ c r = ⊤ := by
  simp [shift, AffineEquiv.surjective]

@[simp]
/--
theorem `shift_bot` / 定理 `shift_bot`

English:
theorem shift_bot
  given: (c : P) (r : k)
  statement: shift ⊥ c r = ⊥
  proof: by
  simp [shift]

中文:
定理 shift_bot
  条件: (c : P) (r : k)
  结论: shift ⊥ c r = ⊥
  证明: by
  simp [shift]
-/
theorem shift_bot (c : P) (r : k) : shift ⊥ c r = ⊥ := by
  simp [shift]

/--
theorem `shift_eq` / 定理 `shift_eq`

English:
theorem shift_eq
  given: {s : AffineSubspace k P} (p : s) (c : P) (r : k)
  proof: by
  have h : Nonempty s := ⟨p⟩
  simp only [shift, h, ↓reduceDIte]
  ext q
  simp only [mem_map, AffineEquiv.coe_toAffineMap, AffineEquiv.constVAdd_apply]
  constructor <;> intro ⟨x, hx, heq⟩ <;> rw [← heq]
  · refine ⟨(1 - r) • (p.val -ᵥ h.some.val) +ᵥ x, ?_, ?_⟩
    · exact vadd_mem_of_mem_direct

中文:
定理 shift_eq
  条件: {s : AffineSubspace k P} (p : s) (c : P) (r : k)
  证明: by
  have h : Nonempty s := ⟨p⟩
  simp only [shift, h, ↓reduceDIte]
  ext q
  simp only [mem_map, AffineEquiv.coe_toAffineMap, AffineEquiv.constVAdd_apply]
  constructor <;> intro ⟨x, hx, heq⟩ <;> rw [← heq]
  · refine ⟨(1 - r) • (p.val -ᵥ h.some.val) +ᵥ x, ?_, ?_⟩
    · exact vadd_mem_of_mem_direct

Depends on / 依赖: AffineEquiv, AffineEquiv.coe_toAffineMap, AffineEquiv.constVAdd_apply, Nonempty, coe_toAffineMap, constVAdd_apply, h.some.prop, h.some.val, mem_map, p.prop, p.val, reduceDIte, smul_add, smul_mem, vadd_mem_of_mem_direction, vadd_vadd, vsub_add_vsub_cancel, vsub_mem_direction
-/
theorem shift_eq {s : AffineSubspace k P} (p : s) (c : P) (r : k) :
    s.shift c r = s.map (AffineEquiv.constVAdd k P ((1 - r) • (c -ᵥ p))) := by
  have h : Nonempty s := ⟨p⟩
  simp only [shift, h, ↓reduceDIte]
  ext q
  simp only [mem_map, AffineEquiv.coe_toAffineMap, AffineEquiv.constVAdd_apply]
  constructor <;> intro ⟨x, hx, heq⟩ <;> rw [← heq]
  · refine ⟨(1 - r) • (p.val -ᵥ h.some.val) +ᵥ x, ?_, ?_⟩
    · exact vadd_mem_of_mem_direction (smul_mem _ _ (vsub_mem_direction p.prop h.some.prop)) hx
    · rw [vadd_vadd, ← smul_add, vsub_add_vsub_cancel]
  · refine ⟨(1 - r) • (h.some.val -ᵥ p.val) +ᵥ x, ?_, ?_⟩
    · exact vadd_mem_of_mem_direction (smul_mem _ _ (vsub_mem_direction h.some.prop p.prop)) hx
    · rw [vadd_vadd, ← smul_add, vsub_add_vsub_cancel]

@[simp]
/--
theorem `shift_zero` / 定理 `shift_zero`

English:
theorem shift_zero
  given: (s : AffineSubspace k P) [h : Nonempty s] (c : P)
  proof: by
  refine ext_of_direction_eq (by simp) ⟨c, ?_⟩
  suffices exists x in s, (c -ᵥ h.some) +ᵥ x = c by simpa [shift, h]
  exact ⟨h.some, by simp⟩

@[simp]

中文:
定理 shift_zero
  条件: (s : AffineSubspace k P) [h : Nonempty s] (c : P)
  证明: by
  refine ext_of_direction_eq (by simp) ⟨c, ?_⟩
  suffices exists x in s, (c -ᵥ h.some) +ᵥ x = c by simpa [shift, h]
  exact ⟨h.some, by simp⟩

@[simp]

Depends on / 依赖: ext_of_direction_eq, h.some, small_succ
-/
theorem shift_zero (s : AffineSubspace k P) [h : Nonempty s] (c : P) :
    s.shift c 0 = mk' c s.direction := by
  refine ext_of_direction_eq (by simp) ⟨c, ?_⟩
  suffices exists x in s, (c -ᵥ h.some) +ᵥ x = c by simpa [shift, h]
  exact ⟨h.some, by simp⟩

@[simp]
/--
theorem `shift_one` / 定理 `shift_one`

English:
theorem shift_one
  given: (s : AffineSubspace k P) (c : P)
  statement: s.shift c 1 = s
  proof: by
  rcases s.eq_bot_or_nonempty with h | h
  · simp [h]
  have h : Nonempty s := by simpa using! h
  simp [shift, h]

中文:
定理 shift_one
  条件: (s : AffineSubspace k P) (c : P)
  结论: s.shift c 1 = s
  证明: by
  rcases s.eq_bot_or_nonempty with h | h
  · simp [h]
  have h : Nonempty s := by simpa using! h
  simp [shift, h]

Depends on / 依赖: Nonempty, eq_bot_or_nonempty, s.eq_bot_or_nonempty
-/
theorem shift_one (s : AffineSubspace k P) (c : P) : s.shift c 1 = s := by
  rcases s.eq_bot_or_nonempty with h | h
  · simp [h]
  have h : Nonempty s := by simpa using! h
  simp [shift, h]

/--
theorem `affineCombination_mem_shift` / 定理 `affineCombination_mem_shift`

English:
theorem affineCombination_mem_shift
  statement: {ι : Type*} [Fintype ι] [Nontrivial ι]
  proof: by
  cases subsingleton_or_nontrivial k
  · suffices (affineSpan k <| p '' {i}ᶜ) = ⊤ by simp [this]
have : Subsingleton P := (AddTorsor.subsingleton_iff V P).mp Module.subsingleton k V
    simp
  classical
  obtain ⟨j, hj⟩ := exists_ne i
  rw [shift_eq ⟨p j]; rw [mem_affineSpan k <| Set.mem_image_of

中文:
定理 affineCombination_mem_shift
  结论: {ι : 类型} [Fintype ι] [Nontrivial ι]
  证明: by
  cases subsingleton_or_nontrivial k
  · suffices (affineSpan k <| p '' {i}ᶜ) = ⊤ by simp [this]
have : Subsingleton P := (AddTorsor.subsingleton_iff V P).mp Module.subsingleton k V
    simp
  classical
  obtain ⟨j, hj⟩ := exists_ne i
  rw [shift_eq ⟨p j]; rw [mem_affineSpan k <| Set.mem_image_of

Depends on / 依赖: AddTorsor, AddTorsor.subsingleton_iff, Module, Module.subsingleton, Set.mem_image_of_mem, Subsingleton, affineCom, affineCombination, affineSpan, classical, exists_ne, mem_affineSpan, mem_image_of_mem, shift_eq, subsingleton, subsingleton_iff, subsingleton_or_nontrivial
-/
theorem affineCombination_mem_shift {ι : Type*} [Fintype ι] [Nontrivial ι]
    (p : ι -> P) (i : ι) {w : ι -> k} (hw : ∑ i, w i = 1) :
    affineCombination k univ p w in (affineSpan k <| p '' {i}ᶜ).shift (p i) (1 - w i) := by
  cases subsingleton_or_nontrivial k
  · suffices (affineSpan k <| p '' {i}ᶜ) = ⊤ by simp [this]
have : Subsingleton P := (AddTorsor.subsingleton_iff V P).mp Module.subsingleton k V
    simp
  classical
  obtain ⟨j, hj⟩ := exists_ne i
  rw [shift_eq ⟨p j]; rw [mem_affineSpan k <| Set.mem_image_of_mem _ hj⟩]
  suffices exists q in affineSpan k (p '' {i}ᶜ), w i • (p i -ᵥ p j) +ᵥ q = affineCombination k univ p w by
    simpa
  refine ⟨-(w i • (p i -ᵥ p j)) +ᵥ affineCombination k univ p w, ?_, by simp⟩
  rw [← affineCombination_piSingle k _ p (mem_univ i)]; rw [← affineCombination_piSingle k _ p (mem_univ j)]; rw [affineCombination_vsub]; rw [← map_smul]; rw [← map_neg]; rw [weightedVSub_vadd_affineCombination]
  refine affineCombination_mem_affineSpan_image ?_ (fun i' _ hi => by aesop) _
  simp [sum_add_distrib, ← mul_sum, hw]

/--
theorem `_root_.AffineIndependent.affineCombination_mem_shift_iff` / 定理 `_root_.AffineIndependent.affineCombination_mem_shift_iff`

English:
theorem _root_.AffineIndependent.affineCombination_mem_shift_iff
  proof: by
  classical
  refine ⟨?_, fun h => by simpa [h] using affineCombination_mem_shift p i hw⟩
  obtain ⟨j, hj⟩ := exists_ne i
  rw [shift_eq ⟨p j]; rw [mem_affineSpan k <| Set.mem_image_of_mem _ hj⟩]
  suffices forall q in affineSpan k (p '' {i}ᶜ),
    (1 - c) • (p i -ᵥ p j) +ᵥ q = affineCombination 

中文:
定理 _root_.AffineIndependent.affineCombination_mem_shift_iff
  证明: by
  classical
  refine ⟨?_, fun h => by simpa [h] using affineCombination_mem_shift p i hw⟩
  obtain ⟨j, hj⟩ := exists_ne i
  rw [shift_eq ⟨p j]; rw [mem_affineSpan k <| Set.mem_image_of_mem _ hj⟩]
  suffices forall q in affineSpan k (p '' {i}ᶜ),
    (1 - c) • (p i -ᵥ p j) +ᵥ q = affineCombination 

Depends on / 依赖: Set.indicator_of_notMem, Set.mem_image_of_mem, affineCombination, affineCombination_mem_shift, affineSpan, classical, eq_affineCombination_of_mem_affineSpan_image, exists_ne, indicator, indicator_of_notMem, mem_affineSpan, mem_image_of_mem, shift_eq
-/
theorem _root_.AffineIndependent.affineCombination_mem_shift_iff
    {ι : Type*} [Fintype ι] [Nontrivial ι] {p : ι -> P}
    (h : AffineIndependent k p) (i : ι) {w : ι -> k} (hw : ∑ i, w i = 1) (c : k) :
    affineCombination k univ p w in (affineSpan k <| p '' {i}ᶜ).shift (p i) c ↔
    w i = 1 - c := by
  classical
  refine ⟨?_, fun h => by simpa [h] using affineCombination_mem_shift p i hw⟩
  obtain ⟨j, hj⟩ := exists_ne i
  rw [shift_eq ⟨p j]; rw [mem_affineSpan k <| Set.mem_image_of_mem _ hj⟩]
  suffices forall q in affineSpan k (p '' {i}ᶜ),
    (1 - c) • (p i -ᵥ p j) +ᵥ q = affineCombination k univ p w -> w i = 1 - c by simpa
  intro q hqmem heq
  obtain ⟨t, w', ht, hw', rfl⟩ := eq_affineCombination_of_mem_affineSpan_image hqmem
  have ht : (t : Set ι).indicator w' i = 0 := Set.indicator_of_notMem (by simpa using ht) w'
  rw [affineCombination_indicator_subset _ _ t.subset_univ]; rw [← affineCombination_piSingle k _ p (mem_univ i)]; rw [← affineCombination_piSingle k _ p (mem_univ j)]; rw [affineCombination_vsub]; rw [← map_smul]; rw [weightedVSub_vadd_affineCombination]; rw [h.affineCombination_eq_iff_eq ?_ hw] at heq
  · simpa [hj.symm, ht] using (heq i (mem_univ i)).symm
  · simp [sum_add_distrib, sum_indicator_subset, ← mul_sum, hw']

end Ring

section CommRing
variable [CommRing k] [AddCommGroup V] [AddTorsor V P] [Module k V]

/--
theorem `shift_eq_map_homothety` / 定理 `shift_eq_map_homothety`

English:
theorem shift_eq_map_homothety
  given: (s : AffineSubspace k P) (c : P) {r : k} (hr : IsUnit r)
  proof: by
  obtain ⟨t, ht⟩ := hr.exists_right_inv
  rcases s.eq_bot_or_nonempty with h | h
  · simp [h]
  have h : Nonempty s := by simpa using! h
  rw [s.shift_eq h.some]
  ext p
  suffices (exists y in s, (1 - r) • (c -ᵥ h.some) +ᵥ y = p) ↔ exists y in s, r • (y -ᵥ c) +ᵥ c = p by
    simpa [homothety_def

中文:
定理 shift_eq_map_homothety
  条件: (s : AffineSubspace k P) (c : P) {r : k} (hr : IsUnit r)
  证明: by
  obtain ⟨t, ht⟩ := hr.exists_right_inv
  rcases s.eq_bot_or_nonempty with h | h
  · simp [h]
  have h : Nonempty s := by simpa using! h
  rw [s.shift_eq h.some]
  ext p
  suffices (exists y in s, (1 - r) • (c -ᵥ h.some) +ᵥ y = p) ↔ exists y in s, r • (y -ᵥ c) +ᵥ c = p by
    simpa [homothety_def

Depends on / 依赖: Nonempty, eq_bot_or_nonempty, equivShrink, exists_right_inv, h.some, h.some.prop, h.some.val, homothety_def, hr.exists_right_inv, nontrivial, s.eq_bot_or_nonempty, s.shift_eq, shift_eq, smul_mem, symm.nontrivial, vadd_mem_of_mem_direction, vsub_mem_direction
-/
theorem shift_eq_map_homothety (s : AffineSubspace k P) (c : P) {r : k} (hr : IsUnit r) :
    s.shift c r = s.map (homothety c r) := by
  obtain ⟨t, ht⟩ := hr.exists_right_inv
  rcases s.eq_bot_or_nonempty with h | h
  · simp [h]
  have h : Nonempty s := by simpa using! h
  rw [s.shift_eq h.some]
  ext p
  suffices (exists y in s, (1 - r) • (c -ᵥ h.some) +ᵥ y = p) ↔ exists y in s, r • (y -ᵥ c) +ᵥ c = p by
    simpa [homothety_def]
  constructor <;> intro ⟨x, hmem, heq⟩ <;> rw [← heq]
  · refine ⟨t • (x -ᵥ h.some.val) +ᵥ h.some.val, ?_, ?_⟩
    · refine vadd_mem_of_mem_direction ?_ h.some.prop
exact smul_mem _ _ vsub_mem_direction hmem h.some.prop
    · rw [vadd_vsub_assoc, smul_add, smul_smul, ht, sub_eq_add_neg, add_smul, one_smul, one_smul,
        neg_smul, ← smul_neg, neg_vsub_eq_vsub_rev]
      simp_rw [add_comm _ (r • (h.some.val -ᵥ c)), ← vadd_vadd, vsub_vadd_comm x h.some.val c]
  · refine ⟨r • (x -ᵥ h.some.val) +ᵥ h.some.val, ?_, ?_⟩
    · refine vadd_mem_of_mem_direction ?_ h.some.prop
exact smul_mem _ _ vsub_mem_direction hmem h.some.prop
    · rw [sub_eq_add_neg, add_smul, one_smul, neg_smul, ← smul_neg, neg_vsub_eq_vsub_rev,
        ← vadd_vadd, vadd_vadd _ _ h.some.val, ← smul_add, add_comm, vsub_add_vsub_cancel,
        vadd_vadd, add_comm, ← vadd_vadd, vsub_vadd]

end CommRing

end AffineSubspace

namespace Affine.Simplex

section Ring
variable [Ring k] [PartialOrder k] [IsOrderedAddMonoid k] [AddCommGroup V] [AddTorsor V P]
  [Module k V] {n : Nat} [NeZero n] (s : Affine.Simplex k P n) (i : Fin (n + 1))

/--
theorem `closedInterior_inter_shift_zero` / 定理 `closedInterior_inter_shift_zero`

English:
theorem closedInterior_inter_shift_zero
  given: [ZeroLEOneClass k]
  proof: by
  refine subset_antisymm (fun p ⟨hp, hshift⟩ => ?_) (by simp [s.point_mem_closedInterior i])
obtain ⟨w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype
    s.closedInterior_subset_affineSpan hp
  suffices w = Pi.single i 1 by simp [this]
  rw [affineCombination_mem_closedInterior_if

中文:
定理 closedInterior_inter_shift_zero
  条件: [ZeroLEOneClass k]
  证明: by
  refine subset_antisymm (fun p ⟨hp, hshift⟩ => ?_) (by simp [s.point_mem_closedInterior i])
obtain ⟨w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype
    s.closedInterior_subset_affineSpan hp
  suffices w = Pi.single i 1 by simp [this]
  rw [affineCombination_mem_closedInterior_if

Depends on / 依赖: Pi.single, SetLike, SetLike.mem_coe, affineCombination_mem_closedInterior_iff, affineCombination_mem_shift_iff, closedInterior_subset_affineSpan, eq_affineCombination_of_mem_affineSpan_of_fintype, hshift, independent, mem_coe, mem_univ, point_mem_closedInterior, s.closedInterior_subset_affineSpan, s.independent.affineCombination_mem_shift_iff, s.point_mem_closedInterior, single, sub_zero, subset_antisymm, sum_erase_add, univ.sum_erase_add
-/
theorem closedInterior_inter_shift_zero [ZeroLEOneClass k] :
    s.closedInterior inter (affineSpan k <| s.points '' {i}ᶜ).shift (s.points i) 0 =
    {s.points i} := by
  refine subset_antisymm (fun p ⟨hp, hshift⟩ => ?_) (by simp [s.point_mem_closedInterior i])
obtain ⟨w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype
    s.closedInterior_subset_affineSpan hp
  suffices w = Pi.single i 1 by simp [this]
  rw [affineCombination_mem_closedInterior_iff hw] at hp
  rw [SetLike.mem_coe]; rw [s.independent.affineCombination_mem_shift_iff i hw]; rw [sub_zero] at hshift
  ext j
  by_cases hj : j = i
  · aesop
  rw [← univ.sum_erase_add w (mem_univ i)]; rw [hshift]; rw [add_eq_right]; rw [sum_eq_zero_iff_of_nonneg fun j _ => (hp j).1] at hw
  simp [hw j (by simpa using hj), hj]

/--
theorem `disjoint_closedInterior_shift` / 定理 `disjoint_closedInterior_shift`

English:
theorem disjoint_closedInterior_shift
  given: {x : k} (hx : x < 0 ∨ 1 < x)
  proof: by
  refine Set.disjoint_left.mpr fun p hleft hright => ?_
obtain ⟨w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype
    s.closedInterior_subset_affineSpan hleft
  rw [SetLike.mem_coe]; rw [s.independent.affineCombination_mem_shift_iff i hw] at hright
  rw [affineCombination_mem_close

中文:
定理 disjoint_closedInterior_shift
  条件: {x : k} (hx : x < 0 ∨ 1 < x)
  证明: by
  refine Set.disjoint_left.mpr fun p hleft hright => ?_
obtain ⟨w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype
    s.closedInterior_subset_affineSpan hleft
  rw [SetLike.mem_coe]; rw [s.independent.affineCombination_mem_shift_iff i hw] at hright
  rw [affineCombination_mem_close

Depends on / 依赖: Set.disjoint_left.mpr, SetLike, SetLike.mem_coe, affineCombination_mem_closedInterior_iff, affineCombination_mem_shift_iff, closedInterior_subset_affineSpan, disjoint_left, eq_affineCombination_of_mem_affineSpan_of_fintype, hright, independent, mem_coe, s.closedInterior_subset_affineSpan, s.independent.affineCombination_mem_shift_iff
-/
theorem disjoint_closedInterior_shift {x : k} (hx : x < 0 ∨ 1 < x) :
Disjoint s.closedInterior (affineSpan k (s.points '' {i}ᶜ)).shift (s.points i) x := by
  refine Set.disjoint_left.mpr fun p hleft hright => ?_
obtain ⟨w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype
    s.closedInterior_subset_affineSpan hleft
  rw [SetLike.mem_coe]; rw [s.independent.affineCombination_mem_shift_iff i hw] at hright
  rw [affineCombination_mem_closedInterior_iff hw] at hleft
  grind

end Ring

section Field
variable [Field k] [LinearOrder k] [IsOrderedRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

/--
theorem `closedInterior_inter_shift_aux` / 定理 `closedInterior_inter_shift_aux`

English:
theorem closedInterior_inter_shift_aux
  statement: {n : Nat} (i : Fin n) {x : k} (hxpos : 0 < x)
  proof: by
  rw [show x⁻¹ * (w i - 1) + 1 = 0 ↔ w i = 1 - x by grind]
  refine and_congr_left fun hi => ⟨fun hj j hji => ⟨?_, ?_⟩, fun hj => ?_⟩
  · exact mul_nonneg (by simpa using hxpos.le) (hj j).1
  · rw [eq_sub_iff_add_eq, add_comm, ← eq_sub_iff_add_eq] at hi
    rw [inv_mul_le_one₀ hxpos]; rw [hi]; rw

中文:
定理 closedInterior_inter_shift_aux
  结论: {n : 自然数} (i : Fin n) {x : k} (hxpos : 0 < x)
  证明: by
  rw [show x⁻¹ * (w i - 1) + 1 = 0 ↔ w i = 1 - x by grind]
  refine and_congr_left fun hi => ⟨fun hj j hji => ⟨?_, ?_⟩, fun hj => ?_⟩
  · exact mul_nonneg (by simpa using hxpos.le) (hj j).1
  · rw [eq_sub_iff_add_eq, add_comm, ← eq_sub_iff_add_eq] at hi
    rw [inv_mul_le_one₀ hxpos]; rw [hi]; rw
-/
private theorem closedInterior_inter_shift_aux {n : Nat} (i : Fin n) {x : k} (hxpos : 0 < x)
    (hx1 : x <= 1) {w : Fin n -> k} (hw : ∑ i, w i = 1) :
    (forall j, w j in Set.Icc 0 1) ∧ w i = 1 - x ↔
    (forall j, j != i -> x⁻¹ * w j in Set.Icc 0 1) ∧ x⁻¹ * (w i - 1) + 1 = 0 := by
  rw [show x⁻¹ * (w i - 1) + 1 = 0 ↔ w i = 1 - x by grind]
  refine and_congr_left fun hi => ⟨fun hj j hji => ⟨?_, ?_⟩, fun hj => ?_⟩
  · exact mul_nonneg (by simpa using hxpos.le) (hj j).1
  · rw [eq_sub_iff_add_eq, add_comm, ← eq_sub_iff_add_eq] at hi
    rw [inv_mul_le_one₀ hxpos]; rw [hi]; rw [le_sub_iff_add_le]; rw [← hw]
    exact add_le_sum (fun i _ => (hj i).1) (mem_univ j) (mem_univ i) hji
  · suffices forall j, 0 <= w j from
      fun j => ⟨this j, hw ▸ Finset.single_le_sum (fun j _ => this j) (mem_univ j)⟩
    intro j
    by_cases hji : j = i <;> aesop

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `closedInterior_inter_shift_eq_homothety` / 定理 `closedInterior_inter_shift_eq_homothety`

English:
theorem closedInterior_inter_shift_eq_homothety
  statement: {n : Nat} [NeZero n] (s : Affine.Simplex k P n)
  proof: by
  rcases hx.1.eq_or_lt with hx0 | hxpos
  · simpa [hx0.symm, nonempty_closedInterior] using s.closedInterior_inter_shift_zero i
  ext p
  by_cases hp : p in affineSpan k (.range s.points)
  · obtain ⟨w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hp
    rw [Set.mem_inter_iff]; r

中文:
定理 closedInterior_inter_shift_eq_homothety
  结论: {n : 自然数} [NeZero n] (s : Affine.Simplex k P n)
  证明: by
  rcases hx.1.eq_or_lt with hx0 | hxpos
  · simpa [hx0.symm, nonempty_closedInterior] using s.closedInterior_inter_shift_zero i
  ext p
  by_cases hp : p in affineSpan k (.range s.points)
  · obtain ⟨w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hp
    rw [Set.mem_inter_iff]; r

Depends on / 依赖: AffineMap, AffineMap.homothety_eq_iff_of_mul_eq_one, Set.mem_image, Set.mem_inter_iff, SetLike, SetLike.mem_coe, affineCombination_mem_closedInterior_iff, affineCombination_mem_shift_iff, affineSpan, closedInterior_inter_shift_zero, eq_affineCombination_of_mem_affineSpan_of_fintype, eq_or_lt, homothety_eq_iff_of_mul_eq_one, hx0.symm, independent, mem_coe, mem_image, mem_inter_iff, nonempty_closedInterior, points
-/
theorem closedInterior_inter_shift_eq_homothety {n : Nat} [NeZero n] (s : Affine.Simplex k P n)
    (i : Fin (n + 1)) {x : k} (hx : x in Set.Icc 0 1) :
    s.closedInterior inter (affineSpan k (s.points '' {i}ᶜ)).shift (s.points i) x =
    homothety (s.points i) x '' (s.faceOpposite i).closedInterior := by
  rcases hx.1.eq_or_lt with hx0 | hxpos
  · simpa [hx0.symm, nonempty_closedInterior] using s.closedInterior_inter_shift_zero i
  ext p
  by_cases hp : p in affineSpan k (.range s.points)
  · obtain ⟨w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hp
    rw [Set.mem_inter_iff]; rw [SetLike.mem_coe]; rw [s.independent.affineCombination_mem_shift_iff i hw]; rw [affineCombination_mem_closedInterior_iff hw]; rw [Set.mem_image]
    simp_rw [AffineMap.homothety_eq_iff_of_mul_eq_one (mul_inv_cancel₀ hxpos.ne.symm),
      univ.homothety_affineCombination _ _ (mem_univ i)]
    simp only [↓existsAndEq, and_true]
    rw [faceOpposite]; rw [affineCombination_mem_closedInterior_face_iff_mem_Icc]; rw [closedInterior_inter_shift_aux i hxpos hx.2 hw]
    · simp only [mem_compl, mem_singleton, not_not, forall_eq]
congrm (forall j, (hj : _) -> $(by simp [lineMap_apply, hj])) ∧ (by simp [lineMap_apply])
    · simp [AffineMap.lineMap_apply, Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_sub_distrib, hw]
  · apply iff_of_false (hp <| s.closedInterior_subset_affineSpan ·.1)
    rintro ⟨q, hq, rfl⟩
exact hp homothety_mem (mem_affineSpan _ (by simp)) _
      affineSpan_mono _ (by simp) ((s.faceOpposite i).closedInterior_subset_affineSpan hq)

end Field
end Affine.Simplex
