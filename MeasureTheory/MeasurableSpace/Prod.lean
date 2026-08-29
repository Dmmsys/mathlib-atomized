/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.MeasureTheory.PiSystem

/-!
# The product sigma algebra

This file talks about the measurability of operations on binary functions.
-/

public section

assert_not_exists MeasureTheory.Measure

noncomputable section

open Set MeasurableSpace

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/--
theorem `generateFrom_prod_eq` / 定理 `generateFrom_prod_eq`

English:
theorem generateFrom_prod_eq
  statement: {α β} {C : Set (Set α)} {D : Set (Set β)} (hC : IsCountablySpanning C)
  proof: by
  apply le_antisymm
  · refine sup_le ?_ ?_ <;> rw [comap_generateFrom] <;> apply generateFrom_le <;>
      rintro _ ⟨s, hs, rfl⟩
    · rcases hD with ⟨t, h1t, h2t⟩
      rw [← prod_univ]; rw [← h2t]; rw [prod_iUnion]
      apply MeasurableSet.iUnion
      intro n
      apply measurableSet_generateFrom
      exact ⟨s, hs, t n, h1t n, rfl⟩
    · rcases hC with ⟨t, h1t, h2t⟩
      rw [← univ_prod]; rw [← h2t]; rw [iUnion_prod_const]
      apply MeasurableSet.iUnion
      rintro n
      apply measurableSet_generateFrom
      exact mem_image2_of_mem (h1t n) hs
  · apply generateFrom_le
    rintro _ ⟨s, hs, t, ht, rfl⟩
    dsimp only
    rw [prod_eq]
    apply (measurable_fst _).inter (measurable_snd _)
    · exact measurableSet_generateFrom hs
    · exact measurableSet_generateFrom ht

中文:
定理 generateFrom_prod_eq
  结论: {α β} {C : 集合 (集合 α)} {D : 集合 (集合 β)} (hC : IsCountablySpanning C)
  证明: by
  apply le_antisymm
  · refine sup_le ?_ ?_ <;> rw [comap_generateFrom] <;> apply generateFrom_le <;>
      rintro _ ⟨s, hs, rfl⟩
    · rcases hD with ⟨t, h1t, h2t⟩
      rw [← prod_univ]; rw [← h2t]; rw [prod_iUnion]
      apply MeasurableSet.iUnion
      intro n
      apply measurableSet_generateFrom
      exact ⟨s, hs, t n, h1t n, rfl⟩
    · rcases hC with ⟨t, h1t, h2t⟩
      rw [← univ_prod]; rw [← h2t]; rw [iUnion_prod_const]
      apply MeasurableSet.iUnion
      rintro n
      apply measurableSet_generateFrom
      exact mem_image2_of_mem (h1t n) hs
  · apply generateFrom_le
    rintro _ ⟨s, hs, t, ht, rfl⟩
    dsimp only
    rw [prod_eq]
    apply (measurable_fst _).inter (measurable_snd _)
    · exact measurableSet_generateFrom hs
    · exact measurableSet_generateFrom ht

Depends on / 依赖: MeasurableSet, MeasurableSet.iUnion, comap_generateFrom, generateFrom_le, iUnion, iUnion_prod_const, le_antisymm, measurableSet_generateFrom, mem_image2_of_mem, prod_iUnion, prod_univ, sup_le, univ_prod
-/
theorem generateFrom_prod_eq {α β} {C : Set (Set α)} {D : Set (Set β)} (hC : IsCountablySpanning C)
    (hD : IsCountablySpanning D) :
    @Prod.instMeasurableSpace _ _ (generateFrom C) (generateFrom D) =
      generateFrom (image2 (· ×ˢ ·) C D) := by
  apply le_antisymm
  · refine sup_le ?_ ?_ <;> rw [comap_generateFrom] <;> apply generateFrom_le <;>
      rintro _ ⟨s, hs, rfl⟩
    · rcases hD with ⟨t, h1t, h2t⟩
      rw [← prod_univ]; rw [← h2t]; rw [prod_iUnion]
      apply MeasurableSet.iUnion
      intro n
      apply measurableSet_generateFrom
      exact ⟨s, hs, t n, h1t n, rfl⟩
    · rcases hC with ⟨t, h1t, h2t⟩
      rw [← univ_prod]; rw [← h2t]; rw [iUnion_prod_const]
      apply MeasurableSet.iUnion
      rintro n
      apply measurableSet_generateFrom
      exact mem_image2_of_mem (h1t n) hs
  · apply generateFrom_le
    rintro _ ⟨s, hs, t, ht, rfl⟩
    dsimp only
    rw [prod_eq]
    apply (measurable_fst _).inter (measurable_snd _)
    · exact measurableSet_generateFrom hs
    · exact measurableSet_generateFrom ht

/--
theorem `generateFrom_eq_prod` / 定理 `generateFrom_eq_prod`

English:
theorem generateFrom_eq_prod
  statement: {C : Set (Set α)} {D : Set (Set β)} (hC : generateFrom C = ‹_›)
  proof: by
  rw [← hC]; rw [← hD]; rw [generateFrom_prod_eq h2C h2D]

中文:
定理 generateFrom_eq_prod
  结论: {C : 集合 (集合 α)} {D : 集合 (集合 β)} (hC : generateFrom C = ‹_›)
  证明: by
  rw [← hC]; rw [← hD]; rw [generateFrom_prod_eq h2C h2D]

Depends on / 依赖: generateFrom_prod_eq
-/
theorem generateFrom_eq_prod {C : Set (Set α)} {D : Set (Set β)} (hC : generateFrom C = ‹_›)
    (hD : generateFrom D = ‹_›) (h2C : IsCountablySpanning C) (h2D : IsCountablySpanning D) :
    generateFrom (image2 (· ×ˢ ·) C D) = Prod.instMeasurableSpace := by
  rw [← hC]; rw [← hD]; rw [generateFrom_prod_eq h2C h2D]

/--
lemma `generateFrom_prod` / 引理 `generateFrom_prod`

English:
lemma generateFrom_prod
  proof: generateFrom_eq_prod generateFrom_measurableSet generateFrom_measurableSet
    isCountablySpanning_measurableSet isCountablySpanning_measurableSet

中文:
引理 generateFrom_prod
  证明: generateFrom_eq_prod generateFrom_measurableSet generateFrom_measurableSet
    isCountablySpanning_measurableSet isCountablySpanning_measurableSet

Depends on / 依赖: generateFrom_eq_prod, generateFrom_measurableSet, isCountablySpanning_measurableSet
-/
lemma generateFrom_prod :
    generateFrom (image2 (· ×ˢ ·) { s : Set α | MeasurableSet s } { t : Set β | MeasurableSet t }) =
      Prod.instMeasurableSpace :=
  generateFrom_eq_prod generateFrom_measurableSet generateFrom_measurableSet
    isCountablySpanning_measurableSet isCountablySpanning_measurableSet

/--
lemma `isPiSystem_prod` / 引理 `isPiSystem_prod`

English:
lemma isPiSystem_prod
  proof: isPiSystem_measurableSet.prod isPiSystem_measurableSet

中文:
引理 isPiSystem_prod
  证明: isPiSystem_measurableSet.prod isPiSystem_measurableSet

Depends on / 依赖: isPiSystem_measurableSet, isPiSystem_measurableSet.prod
-/
lemma isPiSystem_prod :
    IsPiSystem (image2 (· ×ˢ ·) { s : Set α | MeasurableSet s } { t : Set β | MeasurableSet t }) :=
  isPiSystem_measurableSet.prod isPiSystem_measurableSet

/--
lemma `MeasurableSpace.comap_prodMk` / 引理 `MeasurableSpace.comap_prodMk`

English:
lemma MeasurableSpace.comap_prodMk
  statement: {α β γ : Type*} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
  proof: by
  simp_rw [MeasurableSpace.prod, comap_sup, comap_comp]
  rfl

中文:
引理 可测空间.comap_prodMk
  结论: {α β γ : 类型} {mβ : 可测空间 β} {mγ : 可测空间 γ}
  证明: by
  simp_rw [MeasurableSpace.prod, comap_sup, comap_comp]
  rfl

Depends on / 依赖: MeasurableSpace, MeasurableSpace.prod, comap_comp, comap_sup, simp_rw
-/
lemma MeasurableSpace.comap_prodMk {α β γ : Type*} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
    (X : α -> β) (Y : α -> γ) :
    (mβ.prod mγ).comap (fun ω => (X ω, Y ω)) = mβ.comap X ⊔ mγ.comap Y := by
  simp_rw [MeasurableSpace.prod, comap_sup, comap_comp]
  rfl

/--
lemma `MeasurableSpace.comap_prodMap` / 引理 `MeasurableSpace.comap_prodMap`

English:
lemma MeasurableSpace.comap_prodMap
  statement: {α β γ δ : Type*}
  proof: by
  simp_rw [MeasurableSpace.prod, comap_sup, comap_comp]
  rfl

中文:
引理 可测空间.comap_prodMap
  结论: {α β γ δ : 类型}
  证明: by
  simp_rw [MeasurableSpace.prod, comap_sup, comap_comp]
  rfl

Depends on / 依赖: MeasurableSpace, MeasurableSpace.prod, comap_comp, comap_sup, simp_rw
-/
lemma MeasurableSpace.comap_prodMap {α β γ δ : Type*}
    {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (X : γ -> α) (Y : δ -> β) :
    (mα.prod mβ).comap (Prod.map X Y) = (mα.comap X).prod (mβ.comap Y) := by
  simp_rw [MeasurableSpace.prod, comap_sup, comap_comp]
  rfl

/--
lemma `MeasurableEmbedding.prodMap` / 引理 `MeasurableEmbedding.prodMap`

English:
lemma MeasurableEmbedding.prodMap
  statement: {α β γ δ : Type*} {mα : MeasurableSpace α}
  proof: by
  rw [MeasurableEmbedding.iff_comap_eq]
  refine ⟨hg.injective.prodMap hf.injective, ?_, ?_⟩
  · rw [Prod.instMeasurableSpace, Prod.instMeasurableSpace, MeasurableSpace.comap_prodMap,
      hg.comap_eq, hf.comap_eq]
  · rw [range_prodMap]
    exact hg.measurableSet_range.prod hf.measurableSet_range

中文:
引理 可测嵌入.prodMap
  结论: {α β γ δ : 类型} {mα : 可测空间 α}
  证明: by
  rw [MeasurableEmbedding.iff_comap_eq]
  refine ⟨hg.injective.prodMap hf.injective, ?_, ?_⟩
  · rw [Prod.instMeasurableSpace, Prod.instMeasurableSpace, MeasurableSpace.comap_prodMap,
      hg.comap_eq, hf.comap_eq]
  · rw [range_prodMap]
    exact hg.measurableSet_range.prod hf.measurableSet_range

Depends on / 依赖: MeasurableEmbedding, MeasurableEmbedding.iff_comap_eq, MeasurableSpace, MeasurableSpace.comap_prodMap, Prod.instMeasurableSpace, comap_eq, comap_prodMap, hf.comap_eq, hf.injective, hf.measurableSet_range, hg.comap_eq, hg.injective.prodMap, hg.measurableSet_range.prod, iff_comap_eq, injective, instMeasurableSpace, measurableSet_range, prodMap, range_prodMap
-/
lemma MeasurableEmbedding.prodMap {α β γ δ : Type*} {mα : MeasurableSpace α}
    {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ} {f : α -> β}
    {g : γ -> δ} (hg : MeasurableEmbedding g) (hf : MeasurableEmbedding f) :
    MeasurableEmbedding (Prod.map g f) := by
  rw [MeasurableEmbedding.iff_comap_eq]
  refine ⟨hg.injective.prodMap hf.injective, ?_, ?_⟩
  · rw [Prod.instMeasurableSpace, Prod.instMeasurableSpace, MeasurableSpace.comap_prodMap,
      hg.comap_eq, hf.comap_eq]
  · rw [range_prodMap]
    exact hg.measurableSet_range.prod hf.measurableSet_range

/--
lemma `MeasurableEmbedding.prodMk_left` / 引理 `MeasurableEmbedding.prodMk_left`

English:
lemma MeasurableEmbedding.prodMk_left
  statement: {β γ : Type*} [MeasurableSingletonClass α]
  proof: by
    intro y y'
    simp only [Prod.mk.injEq, true_and]
    exact fun h => hf.injective h
  measurable := Measurable.prodMk measurable_const hf.measurable
  measurableSet_image' := by
    intro s hs
    convert! (MeasurableSet.singleton x).prod (hf.measurableSet_image.mpr hs)
    ext x
    simp [Prod.ext_iff, eq_comm, ← exists_and_left, and_left_comm]

中文:
引理 可测嵌入.prodMk_left
  结论: {β γ : 类型} [MeasurableSingleton类 α]
  证明: by
    intro y y'
    simp only [Prod.mk.injEq, true_and]
    exact fun h => hf.injective h
  measurable := Measurable.prodMk measurable_const hf.measurable
  measurableSet_image' := by
    intro s hs
    convert! (MeasurableSet.singleton x).prod (hf.measurableSet_image.mpr hs)
    ext x
    simp [Prod.ext_iff, eq_comm, ← exists_and_left, and_left_comm]

Depends on / 依赖: Measurable, Measurable.prodMk, MeasurableSet, MeasurableSet.singleton, Prod.ext_iff, Prod.mk.injEq, and_left_comm, convert, eq_comm, exists_and_left, ext_iff, hf.injective, hf.measurable, hf.measurableSet_image.mpr, injective, measurable, measurableSet_image, measurable_const, prodMk, singleton
-/
lemma MeasurableEmbedding.prodMk_left {β γ : Type*} [MeasurableSingletonClass α]
    {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
    (x : α) {f : γ -> β} (hf : MeasurableEmbedding f) :
    MeasurableEmbedding (fun y => (x, f y)) where
  injective := by
    intro y y'
    simp only [Prod.mk.injEq, true_and]
    exact fun h => hf.injective h
  measurable := Measurable.prodMk measurable_const hf.measurable
  measurableSet_image' := by
    intro s hs
    convert! (MeasurableSet.singleton x).prod (hf.measurableSet_image.mpr hs)
    ext x
    simp [Prod.ext_iff, eq_comm, ← exists_and_left, and_left_comm]

/--
lemma `measurableEmbedding_prodMk_left` / 引理 `measurableEmbedding_prodMk_left`

English:
lemma measurableEmbedding_prodMk_left
  given: [MeasurableSingletonClass α] (x : α)
  proof: MeasurableEmbedding.prodMk_left x MeasurableEmbedding.id

中文:
引理 measurableEmbedding_prodMk_left
  条件: [MeasurableSingleton类 α] (x : α)
  证明: MeasurableEmbedding.prodMk_left x MeasurableEmbedding.id

Depends on / 依赖: MeasurableEmbedding, MeasurableEmbedding.id, MeasurableEmbedding.prodMk_left, prodMk_left
-/
lemma measurableEmbedding_prodMk_left [MeasurableSingletonClass α] (x : α) :
    MeasurableEmbedding (Prod.mk x : β -> α × β) :=
  MeasurableEmbedding.prodMk_left x MeasurableEmbedding.id

/--
lemma `MeasurableEmbedding.prodMk_right` / 引理 `MeasurableEmbedding.prodMk_right`

English:
lemma MeasurableEmbedding.prodMk_right
  statement: {β γ : Type*} [MeasurableSingletonClass α]
  proof: MeasurableEquiv.prodComm.measurableEmbedding.comp (hf.prodMk_left _)

中文:
引理 可测嵌入.prodMk_right
  结论: {β γ : 类型} [MeasurableSingleton类 α]
  证明: MeasurableEquiv.prodComm.measurableEmbedding.comp (hf.prodMk_left _)

Depends on / 依赖: MeasurableEquiv, MeasurableEquiv.prodComm.measurableEmbedding.comp, hf.prodMk_left, measurableEmbedding, prodComm, prodMk_left
-/
lemma MeasurableEmbedding.prodMk_right {β γ : Type*} [MeasurableSingletonClass α]
    {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
    {f : γ -> β} (hf : MeasurableEmbedding f) (x : α) :
    MeasurableEmbedding (fun y => (f y, x)) :=
  MeasurableEquiv.prodComm.measurableEmbedding.comp (hf.prodMk_left _)

/--
lemma `measurableEmbedding_prod_mk_right` / 引理 `measurableEmbedding_prod_mk_right`

English:
lemma measurableEmbedding_prod_mk_right
  given: [MeasurableSingletonClass α] (x : α)
  proof: MeasurableEmbedding.prodMk_right MeasurableEmbedding.id x

中文:
引理 measurableEmbedding_prod_mk_right
  条件: [MeasurableSingleton类 α] (x : α)
  证明: MeasurableEmbedding.prodMk_right MeasurableEmbedding.id x

Depends on / 依赖: MeasurableEmbedding, MeasurableEmbedding.id, MeasurableEmbedding.prodMk_right, prodMk_right
-/
lemma measurableEmbedding_prod_mk_right [MeasurableSingletonClass α] (x : α) :
    MeasurableEmbedding (fun y => (y, x) : β -> β × α) :=
  MeasurableEmbedding.prodMk_right MeasurableEmbedding.id x
