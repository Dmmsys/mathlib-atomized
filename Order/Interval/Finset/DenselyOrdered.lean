/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Order.Interval.Finset.Basic

/-!
# Linear locally finite orders are densely ordered iff they are trivial

## Main results
* `LocallyFiniteOrder.denselyOrdered_iff_subsingleton`:
  A linear locally finite order is densely ordered if and only if it is a subsingleton.

-/

public section

variable {X : Type*} [LinearOrder X] [LocallyFiniteOrder X]

/--
lemma `LocallyFiniteOrder.denselyOrdered_iff_subsingleton` / 引理 `LocallyFiniteOrder.denselyOrdered_iff_subsingleton`

English:
lemma LocallyFiniteOrder.denselyOrdered_iff_subsingleton
  proof: by
  refine ⟨fun H => ?_, fun h => h.instDenselyOrdered⟩
  rw [← not_nontrivial_iff_subsingleton]; rw [nontrivial_iff_lt]
  rintro ⟨a, b, hab⟩
  exact not_lt_of_denselyOrdered_of_locallyFinite a b hab

中文:
引理 LocallyFiniteOrder.denselyOrdered_iff_subsingleton
  证明: by
  refine ⟨fun H => ?_, fun h => h.instDenselyOrdered⟩
  rw [← not_nontrivial_iff_subsingleton]; rw [nontrivial_iff_lt]
  rintro ⟨a, b, hab⟩
  exact not_lt_of_denselyOrdered_of_locallyFinite a b hab

Depends on / 依赖: h.instDenselyOrdered, instDenselyOrdered, nontrivial_iff_lt, not_lt_of_denselyOrdered_of_locallyFinite, not_nontrivial_iff_subsingleton
-/
lemma LocallyFiniteOrder.denselyOrdered_iff_subsingleton :
    DenselyOrdered X ↔ Subsingleton X := by
  refine ⟨fun H => ?_, fun h => h.instDenselyOrdered⟩
  rw [← not_nontrivial_iff_subsingleton]; rw [nontrivial_iff_lt]
  rintro ⟨a, b, hab⟩
  exact not_lt_of_denselyOrdered_of_locallyFinite a b hab

/--
lemma `denselyOrdered_set_iff_subsingleton` / 引理 `denselyOrdered_set_iff_subsingleton`

English:
lemma denselyOrdered_set_iff_subsingleton
  given: {s : Set X}
  proof: by
  classical
  simp [LocallyFiniteOrder.denselyOrdered_iff_subsingleton]

中文:
引理 denselyOrdered_set_iff_subsingleton
  条件: {s : Set X}
  证明: by
  classical
  simp [LocallyFiniteOrder.denselyOrdered_iff_subsingleton]

Depends on / 依赖: LocallyFiniteOrder, LocallyFiniteOrder.denselyOrdered_iff_subsingleton, classical, denselyOrdered_iff_subsingleton
-/
lemma denselyOrdered_set_iff_subsingleton {s : Set X} :
    DenselyOrdered s ↔ s.Subsingleton := by
  classical
  simp [LocallyFiniteOrder.denselyOrdered_iff_subsingleton]

/--
lemma `WithBot.denselyOrdered_set_iff_subsingleton` / 引理 `WithBot.denselyOrdered_set_iff_subsingleton`

English:
lemma WithBot.denselyOrdered_set_iff_subsingleton
  given: {s : Set (WithBot X)}
  proof: by
  refine ⟨fun H => ?_, fun h => h.denselyOrdered⟩
  rw [← Set.subsingleton_coe]; rw [← not_nontrivial_iff_subsingleton]; rw [nontrivial_iff_lt]
  suffices DenselyOrdered (WithBot.some ⁻¹' s) by
    rintro ⟨x, y, H⟩
    rw [_root_.denselyOrdered_set_iff_subsingleton] at this
    obtain ⟨z, hz, hz'

中文:
引理 WithBot.denselyOrdered_set_iff_subsingleton
  条件: {s : Set (WithBot X)}
  证明: by
  refine ⟨fun H => ?_, fun h => h.denselyOrdered⟩
  rw [← Set.subsingleton_coe]; rw [← not_nontrivial_iff_subsingleton]; rw [nontrivial_iff_lt]
  suffices DenselyOrdered (WithBot.some ⁻¹' s) by
    rintro ⟨x, y, H⟩
    rw [_root_.denselyOrdered_set_iff_subsingleton] at this
    obtain ⟨z, hz, hz'

Depends on / 依赖: DenselyOrdered, Set.subsingleton_coe, Subtype, Subtype.coe_lt_coe.mpr, WithBot, WithBot.coe_lt_coe, WithBot.some, WithBot.unbot, _root_, _root_.denselyOrdered_set_iff_subsingleton, coe_lt_coe, denselyOrdered, denselyOrdered_set_iff_subsingleton, exists_between, h.denselyOrdered, hz0.ne, hz0.trans, nontrivial_iff_lt, not_nontrivial_iff_subsingleton, replace
-/
lemma WithBot.denselyOrdered_set_iff_subsingleton {s : Set (WithBot X)} :
    DenselyOrdered s ↔ s.Subsingleton := by
  refine ⟨fun H => ?_, fun h => h.denselyOrdered⟩
  rw [← Set.subsingleton_coe]; rw [← not_nontrivial_iff_subsingleton]; rw [nontrivial_iff_lt]
  suffices DenselyOrdered (WithBot.some ⁻¹' s) by
    rintro ⟨x, y, H⟩
    rw [_root_.denselyOrdered_set_iff_subsingleton] at this
    obtain ⟨z, hz, hz'⟩ := exists_between H
    have hz0 : (⊥ : WithBot X) < z := by simp [(Subtype.coe_lt_coe.mpr hz).trans_le']
    replace hz' : WithBot.unbot z.val hz0.ne' < WithBot.unbot y (hz0.trans hz').ne' := by
      rwa [← WithBot.coe_lt_coe, WithBot.coe_unbot, WithBot.coe_unbot]
    refine absurd (this ?_ ?_) hz'.ne <;>
    simp
  constructor
  simp only [Subtype.exists, Set.mem_preimage, Subtype.forall, Subtype.mk_lt_mk, exists_and_right,
    exists_prop]
  intro x hx y hy hxy
  have : (⟨_, hx⟩ : s) < ⟨_, hy⟩ := by simp [hxy]
  obtain ⟨z, hz, hz'⟩ := exists_between this
  simp only [← Subtype.coe_lt_coe] at hz hz'
  refine ⟨WithBot.unbot z (hz.trans_le' (by simp)).ne', ⟨?_, ?_⟩, ?_⟩
  · simp
  · rw [← WithBot.coe_lt_coe]
    simp [hz.trans_le]
  · rw [← WithBot.coe_lt_coe]
    simp [hz'.trans_le']

/--
lemma `WithTop.denselyOrdered_set_iff_subsingleton` / 引理 `WithTop.denselyOrdered_set_iff_subsingleton`

English:
lemma WithTop.denselyOrdered_set_iff_subsingleton
  given: {s : Set (WithTop X)}
  proof: by
  have he : StrictAnti (WithTop.toDual.image s) :=
    WithTop.toDual.image_strictAnti _ (fun ⦃a b⦄ a => a)
  rw [denselyOrdered_iff_of_strictAnti _ he]; rw [WithBot.denselyOrdered_set_iff_subsingleton]; rw [WithTop.toDual.injective.subsingleton_image_iff]

中文:
引理 WithTop.denselyOrdered_set_iff_subsingleton
  条件: {s : Set (WithTop X)}
  证明: by
  have he : StrictAnti (WithTop.toDual.image s) :=
    WithTop.toDual.image_strictAnti _ (fun ⦃a b⦄ a => a)
  rw [denselyOrdered_iff_of_strictAnti _ he]; rw [WithBot.denselyOrdered_set_iff_subsingleton]; rw [WithTop.toDual.injective.subsingleton_image_iff]

Depends on / 依赖: StrictAnti, WithBot, WithBot.denselyOrdered_set_iff_subsingleton, WithTop, WithTop.toDual.image, WithTop.toDual.image_strictAnti, WithTop.toDual.injective.subsingleton_image_iff, denselyOrdered_iff_of_strictAnti, denselyOrdered_set_iff_subsingleton, image_strictAnti, injective, subsingleton_image_iff, toDual
-/
lemma WithTop.denselyOrdered_set_iff_subsingleton {s : Set (WithTop X)} :
    DenselyOrdered s ↔ s.Subsingleton := by
  have he : StrictAnti (WithTop.toDual.image s) :=
    WithTop.toDual.image_strictAnti _ (fun ⦃a b⦄ a => a)
  rw [denselyOrdered_iff_of_strictAnti _ he]; rw [WithBot.denselyOrdered_set_iff_subsingleton]; rw [WithTop.toDual.injective.subsingleton_image_iff]
