/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.Tactic.FunProp

/-!
# Measurable embeddings and equivalences

A measurable equivalence between measurable spaces is an equivalence
which respects the σ-algebras, that is, for which both directions of
the equivalence are measurable functions.

## Main definitions

* `MeasurableEmbedding`: a map `f : α → β` is called a *measurable embedding* if it is injective,
  measurable, and sends measurable sets to measurable sets.
* `MeasurableEquiv`: an equivalence `α ≃ β` is a *measurable equivalence* if its forward and inverse
  functions are measurable.

We prove a multitude of elementary lemmas about these, and one more substantial theorem:

* `MeasurableEmbedding.schroederBernstein`: the **measurable Schröder-Bernstein Theorem**: given
  measurable embeddings `α → β` and `β → α`, we can find a measurable equivalence `α ≃ᵐ β`.

## Notation

* We write `α ≃ᵐ β` for measurable equivalences between the measurable spaces `α` and `β`.
  This should not be confused with `≃ₘ` which is used for diffeomorphisms between manifolds.

## Tags

measurable equivalence, measurable embedding
-/

@[expose] public section


open Set Function Equiv MeasureTheory

universe uι

variable {α β γ δ δ' : Type*} {ι : Sort uι} {s t u : Set α}

/--
Definition of `MeasurableEmbedding` / `MeasurableEmbedding` 的定义

English:
structure MeasurableEmbedding
  parameters: [MeasurableSpace α] [MeasurableSpace β] (f : α -> β)
  axioms and operations (3):
    - injective : Injective f
    - measurable : Measurable f
    - measurableSet_image' : forall ⦃s⦄, MeasurableSet s -> MeasurableSet (f '' s)

中文:
结构 可测嵌入
  参数: [可测空间 α] [可测空间 β] (f : α -> β)
  公理与运算 (3 个):
    - injective : 单射 f
    - measurable : 可测 f
    - measurableSet_image' : 对任意 ⦃s⦄, 可测集 s -> 可测集 (f '' s)
-/
structure MeasurableEmbedding [MeasurableSpace α] [MeasurableSpace β] (f : α -> β) : Prop where
  /-- A measurable embedding is injective. -/
  protected injective : Injective f
  /-- A measurable embedding is a measurable function. -/
  protected measurable : Measurable f
  /-- The image of a measurable set under a measurable embedding is a measurable set. -/
  protected measurableSet_image' : forall ⦃s⦄, MeasurableSet s -> MeasurableSet (f '' s)

attribute [fun_prop] MeasurableEmbedding.measurable

namespace MeasurableEmbedding

variable {mα : MeasurableSpace α} [MeasurableSpace β] [MeasurableSpace γ] {f : α -> β} {g : β -> γ}

/--
theorem `measurableSet_image` / 定理 `measurableSet_image`

English:
theorem measurableSet_image
  given: (hf : MeasurableEmbedding f)
  proof: ⟨fun h => by simpa only [hf.injective.preimage_image] using hf.measurable h, fun h =>
    hf.measurableSet_image' h⟩

中文:
定理 measurableSet_image
  条件: (hf : 可测嵌入 f)
  证明: ⟨fun h => by simpa only [hf.injective.preimage_image] using hf.measurable h, fun h =>
    hf.measurableSet_image' h⟩

Depends on / 依赖: hf.injective.preimage_image, hf.measurable, hf.measurableSet_image, injective, measurable, measurableSet_image, preimage_image
-/
theorem measurableSet_image (hf : MeasurableEmbedding f) :
    MeasurableSet (f '' s) ↔ MeasurableSet s :=
  ⟨fun h => by simpa only [hf.injective.preimage_image] using hf.measurable h, fun h =>
    hf.measurableSet_image' h⟩

/--
theorem `id` / 定理 `id`

English:
theorem id
  statement: MeasurableEmbedding (id : α -> α)
  proof: ⟨injective_id, measurable_id, fun s hs => by rwa [image_id]⟩

中文:
定理 id
  结论: 可测嵌入 (id : α -> α)
  证明: ⟨injective_id, measurable_id, fun s hs => by rwa [image_id]⟩

Depends on / 依赖: image_id, injective_id, measurable_id
-/
theorem id : MeasurableEmbedding (id : α -> α) :=
  ⟨injective_id, measurable_id, fun s hs => by rwa [image_id]⟩

/--
theorem `comp` / 定理 `comp`

English:
theorem comp
  given: (hg : MeasurableEmbedding g) (hf : MeasurableEmbedding f)
  proof: ⟨hg.injective.comp hf.injective, hg.measurable.comp hf.measurable, fun s hs => by
    rwa [image_comp, hg.measurableSet_image, hf.measurableSet_image]⟩

中文:
定理 comp
  条件: (hg : 可测嵌入 g) (hf : 可测嵌入 f)
  证明: ⟨hg.injective.comp hf.injective, hg.measurable.comp hf.measurable, fun s hs => by
    rwa [image_comp, hg.measurableSet_image, hf.measurableSet_image]⟩

Depends on / 依赖: hf.injective, hf.measurable, hf.measurableSet_image, hg.injective.comp, hg.measurable.comp, hg.measurableSet_image, image_comp, injective, measurable, measurableSet_image
-/
theorem comp (hg : MeasurableEmbedding g) (hf : MeasurableEmbedding f) :
    MeasurableEmbedding (g ∘ f) :=
  ⟨hg.injective.comp hf.injective, hg.measurable.comp hf.measurable, fun s hs => by
    rwa [image_comp, hg.measurableSet_image, hf.measurableSet_image]⟩

/--
theorem `subtype_coe` / 定理 `subtype_coe`

English:
theorem subtype_coe
  given: (hs : MeasurableSet s)
  statement: MeasurableEmbedding ((↑) : s -> α) where
  proof: Subtype.coe_injective
  measurable := measurable_subtype_coe
  measurableSet_image' := fun _ => MeasurableSet.subtype_image hs

中文:
定理 subtype_coe
  条件: (hs : 可测集 s)
  结论: 可测嵌入 ((↑) : s -> α) where
  证明: Subtype.coe_injective
  measurable := measurable_subtype_coe
  measurableSet_image' := fun _ => MeasurableSet.subtype_image hs

Depends on / 依赖: Subtype, Subtype.coe_injective, coe_injective
-/
theorem subtype_coe (hs : MeasurableSet s) : MeasurableEmbedding ((↑) : s -> α) where
  injective := Subtype.coe_injective
  measurable := measurable_subtype_coe
  measurableSet_image' := fun _ => MeasurableSet.subtype_image hs

/--
theorem `measurableSet_range` / 定理 `measurableSet_range`

English:
theorem measurableSet_range
  given: (hf : MeasurableEmbedding f)
  statement: MeasurableSet (range f)
  proof: by
  rw [← image_univ]
  exact hf.measurableSet_image' MeasurableSet.univ

中文:
定理 measurableSet_range
  条件: (hf : 可测嵌入 f)
  结论: 可测集 (range f)
  证明: by
  rw [← image_univ]
  exact hf.measurableSet_image' MeasurableSet.univ

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, hf.measurableSet_image, image_univ, measurableSet_image
-/
theorem measurableSet_range (hf : MeasurableEmbedding f) : MeasurableSet (range f) := by
  rw [← image_univ]
  exact hf.measurableSet_image' MeasurableSet.univ

/--
theorem `measurableSet_preimage` / 定理 `measurableSet_preimage`

English:
theorem measurableSet_preimage
  given: (hf : MeasurableEmbedding f) {s : Set β}
  proof: by
  rw [← image_preimage_eq_inter_range]; rw [hf.measurableSet_image]

中文:
定理 measurableSet_preimage
  条件: (hf : 可测嵌入 f) {s : 集合 β}
  证明: by
  rw [← image_preimage_eq_inter_range]; rw [hf.measurableSet_image]

Depends on / 依赖: hf.measurableSet_image, image_preimage_eq_inter_range, measurableSet_image
-/
theorem measurableSet_preimage (hf : MeasurableEmbedding f) {s : Set β} :
    MeasurableSet (f ⁻¹' s) ↔ MeasurableSet (s inter range f) := by
  rw [← image_preimage_eq_inter_range]; rw [hf.measurableSet_image]

/--
theorem `measurable_rangeSplitting` / 定理 `measurable_rangeSplitting`

English:
theorem measurable_rangeSplitting
  given: (hf : MeasurableEmbedding f)
  proof: fun s hs => by
  rwa [preimage_rangeSplitting hf.injective,
    ← (subtype_coe hf.measurableSet_range).measurableSet_image, ← image_comp,
    coe_comp_rangeFactorization, hf.measurableSet_image]

中文:
定理 measurable_rangeSplitting
  条件: (hf : 可测嵌入 f)
  证明: fun s hs => by
  rwa [preimage_rangeSplitting hf.injective,
    ← (subtype_coe hf.measurableSet_range).measurableSet_image, ← image_comp,
    coe_comp_rangeFactorization, hf.measurableSet_image]

Depends on / 依赖: coe_comp_rangeFactorization, hf.injective, hf.measurableSet_image, hf.measurableSet_range, image_comp, injective, measurableSet_image, measurableSet_range, preimage_rangeSplitting, subtype_coe
-/
theorem measurable_rangeSplitting (hf : MeasurableEmbedding f) :
    Measurable (rangeSplitting f) := fun s hs => by
  rwa [preimage_rangeSplitting hf.injective,
    ← (subtype_coe hf.measurableSet_range).measurableSet_image, ← image_comp,
    coe_comp_rangeFactorization, hf.measurableSet_image]

/--
theorem `measurable_extend` / 定理 `measurable_extend`

English:
theorem measurable_extend
  statement: (hf : MeasurableEmbedding f) {g : α -> γ} {g' : β -> γ} (hg : Measurable g)
  proof: by
  refine measurable_of_restrict_of_restrict_compl hf.measurableSet_range ?_ ?_
  · rw [domRestrict_extend_range]
    simpa only [rangeSplitting] using! hg.comp hf.measurable_rangeSplitting
  · rw [domRestrict_extend_compl_range]
    exact hg'.comp measurable_subtype_coe

中文:
定理 measurable_extend
  结论: (hf : 可测嵌入 f) {g : α -> γ} {g' : β -> γ} (hg : 可测 g)
  证明: by
  refine measurable_of_restrict_of_restrict_compl hf.measurableSet_range ?_ ?_
  · rw [domRestrict_extend_range]
    simpa only [rangeSplitting] using! hg.comp hf.measurable_rangeSplitting
  · rw [domRestrict_extend_compl_range]
    exact hg'.comp measurable_subtype_coe

Depends on / 依赖: domRestrict_extend_compl_range, domRestrict_extend_range, hf.measurableSet_range, hf.measurable_rangeSplitting, hg.comp, measurableSet_range, measurable_of_restrict_of_restrict_compl, measurable_rangeSplitting, measurable_subtype_coe, rangeSplitting
-/
theorem measurable_extend (hf : MeasurableEmbedding f) {g : α -> γ} {g' : β -> γ} (hg : Measurable g)
    (hg' : Measurable g') : Measurable (extend f g g') := by
  refine measurable_of_restrict_of_restrict_compl hf.measurableSet_range ?_ ?_
  · rw [domRestrict_extend_range]
    simpa only [rangeSplitting] using! hg.comp hf.measurable_rangeSplitting
  · rw [domRestrict_extend_compl_range]
    exact hg'.comp measurable_subtype_coe

/--
theorem `exists_measurable_extend` / 定理 `exists_measurable_extend`

English:
theorem exists_measurable_extend
  statement: (hf : MeasurableEmbedding f) {g : α -> γ} (hg : Measurable g)
  proof: ⟨extend f g fun x => Classical.choice (hne x),
    hf.measurable_extend hg (measurable_const' fun _ _ => rfl),
    funext fun _ => hf.injective.extend_apply _ _ _⟩

中文:
定理 存在_measurable_extend
  结论: (hf : 可测嵌入 f) {g : α -> γ} (hg : 可测 g)
  证明: ⟨extend f g fun x => Classical.choice (hne x),
    hf.measurable_extend hg (measurable_const' fun _ _ => rfl),
    funext fun _ => hf.injective.extend_apply _ _ _⟩

Depends on / 依赖: Classical, Classical.choice, choice, extend, extend_apply, hf.injective.extend_apply, hf.measurable_extend, injective, measurable_const, measurable_extend
-/
theorem exists_measurable_extend (hf : MeasurableEmbedding f) {g : α -> γ} (hg : Measurable g)
    (hne : β -> Nonempty γ) : exists g' : β -> γ, Measurable g' ∧ g' ∘ f = g :=
  ⟨extend f g fun x => Classical.choice (hne x),
    hf.measurable_extend hg (measurable_const' fun _ _ => rfl),
    funext fun _ => hf.injective.extend_apply _ _ _⟩

/--
theorem `measurable_comp_iff` / 定理 `measurable_comp_iff`

English:
theorem measurable_comp_iff
  given: (hg : MeasurableEmbedding g)
  statement: Measurable (g ∘ f) ↔ Measurable f
  proof: by
  refine ⟨fun H => ?_, hg.measurable.comp⟩
  suffices Measurable ((rangeSplitting g ∘ rangeFactorization g) ∘ f) by
    rwa [(rightInverse_rangeSplitting hg.injective).comp_eq_id] at this
  exact hg.measurable_rangeSplitting.comp H.subtype_mk

中文:
定理 measurable_comp_iff
  条件: (hg : 可测嵌入 g)
  结论: 可测 (g ∘ f) ↔ 可测 f
  证明: by
  refine ⟨fun H => ?_, hg.measurable.comp⟩
  suffices Measurable ((rangeSplitting g ∘ rangeFactorization g) ∘ f) by
    rwa [(rightInverse_rangeSplitting hg.injective).comp_eq_id] at this
  exact hg.measurable_rangeSplitting.comp H.subtype_mk

Depends on / 依赖: H.subtype_mk, Measurable, comp_eq_id, hg.injective, hg.measurable.comp, hg.measurable_rangeSplitting.comp, injective, krullDim_nonpos_of_subsingleton, measurable, measurable_rangeSplitting, rangeFactorization, rangeSplitting, rightInverse_rangeSplitting, subtype_mk
-/
theorem measurable_comp_iff (hg : MeasurableEmbedding g) : Measurable (g ∘ f) ↔ Measurable f := by
  refine ⟨fun H => ?_, hg.measurable.comp⟩
  suffices Measurable ((rangeSplitting g ∘ rangeFactorization g) ∘ f) by
    rwa [(rightInverse_rangeSplitting hg.injective).comp_eq_id] at this
  exact hg.measurable_rangeSplitting.comp H.subtype_mk

/--
lemma `natCast` / 引理 `natCast`

English:
lemma natCast
  statement: {α : Type*} [MeasurableSpace α]
  proof: Nat.cast_injective
  measurable := measurable_from_nat
  measurableSet_image' := fun _ _ =>
    ((Set.countable_range (Nat.cast : Nat -> α)).mono
      (Set.image_subset_range _ _)).measurableSet

中文:
引理 natCast
  结论: {α : 类型} [可测空间 α]
  证明: Nat.cast_injective
  measurable := measurable_from_nat
  measurableSet_image' := fun _ _ =>
    ((Set.countable_range (Nat.cast : Nat -> α)).mono
      (Set.image_subset_range _ _)).measurableSet

Depends on / 依赖: Nat.cast_injective, cast_injective
-/
lemma natCast {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] [AddMonoidWithOne α] [CharZero α] :
    MeasurableEmbedding (Nat.cast : Nat -> α) where
  injective := Nat.cast_injective
  measurable := measurable_from_nat
  measurableSet_image' := fun _ _ =>
    ((Set.countable_range (Nat.cast : Nat -> α)).mono
      (Set.image_subset_range _ _)).measurableSet

end MeasurableEmbedding

section gluing
variable {α₁ α₂ α₃ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mα₁ : MeasurableSpace α₁} {mα₂ : MeasurableSpace α₂} {mα₃ : MeasurableSpace α₃}
  {i₁ : α₁ -> α} {i₂ : α₂ -> α} {i₃ : α₃ -> α} {s : Set α} {f : α -> β}

/--
lemma `MeasurableSet.of_union_range_cover` / 引理 `MeasurableSet.of_union_range_cover`

English:
lemma MeasurableSet.of_union_range_cover
  statement: (hi₁ : MeasurableEmbedding i₁)
  proof: by
  convert! (hi₁.measurableSet_image' hs₁).union (hi₂.measurableSet_image' hs₂)
  simp [image_preimage_eq_range_inter, ← union_inter_distrib_right, univ_subset_iff.1 h]

中文:
引理 可测集.of_union_range_cover
  结论: (hi₁ : 可测嵌入 i₁)
  证明: by
  convert! (hi₁.measurableSet_image' hs₁).union (hi₂.measurableSet_image' hs₂)
  simp [image_preimage_eq_range_inter, ← union_inter_distrib_right, univ_subset_iff.1 h]

Depends on / 依赖: convert, image_preimage_eq_range_inter, measurableSet_image, union_inter_distrib_right, univ_subset_iff
-/
lemma MeasurableSet.of_union_range_cover (hi₁ : MeasurableEmbedding i₁)
    (hi₂ : MeasurableEmbedding i₂) (h : univ subseteq range i₁ union range i₂)
    (hs₁ : MeasurableSet (i₁ ⁻¹' s)) (hs₂ : MeasurableSet (i₂ ⁻¹' s)) : MeasurableSet s := by
  convert! (hi₁.measurableSet_image' hs₁).union (hi₂.measurableSet_image' hs₂)
  simp [image_preimage_eq_range_inter, ← union_inter_distrib_right, univ_subset_iff.1 h]

/--
lemma `MeasurableSet.of_union₃_range_cover` / 引理 `MeasurableSet.of_union₃_range_cover`

English:
lemma MeasurableSet.of_union₃_range_cover
  statement: (hi₁ : MeasurableEmbedding i₁)
  proof: by
  convert!
.union (hi₁.measurableSet_image' hs₁).union (hi₂.measurableSet_image' hs₂)
      (hi₃.measurableSet_image' hs₃)
  simp [image_preimage_eq_range_inter, ← union_inter_distrib_right, univ_subset_iff.1 h]

中文:
引理 可测集.of_union₃_range_cover
  结论: (hi₁ : 可测嵌入 i₁)
  证明: by
  convert!
.union (hi₁.measurableSet_image' hs₁).union (hi₂.measurableSet_image' hs₂)
      (hi₃.measurableSet_image' hs₃)
  simp [image_preimage_eq_range_inter, ← union_inter_distrib_right, univ_subset_iff.1 h]

Depends on / 依赖: convert, image_preimage_eq_range_inter, measurableSet_image, union_inter_distrib_right, univ_subset_iff
-/
lemma MeasurableSet.of_union₃_range_cover (hi₁ : MeasurableEmbedding i₁)
    (hi₂ : MeasurableEmbedding i₂) (hi₃ : MeasurableEmbedding i₃)
    (h : univ subseteq range i₁ union range i₂ union range i₃) (hs₁ : MeasurableSet (i₁ ⁻¹' s))
    (hs₂ : MeasurableSet (i₂ ⁻¹' s)) (hs₃ : MeasurableSet (i₃ ⁻¹' s)) : MeasurableSet s := by
  convert!
.union (hi₁.measurableSet_image' hs₁).union (hi₂.measurableSet_image' hs₂)
      (hi₃.measurableSet_image' hs₃)
  simp [image_preimage_eq_range_inter, ← union_inter_distrib_right, univ_subset_iff.1 h]

/--
lemma `Measurable.of_union_range_cover` / 引理 `Measurable.of_union_range_cover`

English:
lemma Measurable.of_union_range_cover
  statement: (hi₁ : MeasurableEmbedding i₁)
  proof: fun _s hs => .of_union_range_cover hi₁ hi₂ h (hf₁ hs) (hf₂ hs)

中文:
引理 可测.of_union_range_cover
  结论: (hi₁ : 可测嵌入 i₁)
  证明: fun _s hs => .of_union_range_cover hi₁ hi₂ h (hf₁ hs) (hf₂ hs)

Depends on / 依赖: of_union_range_cover
-/
lemma Measurable.of_union_range_cover (hi₁ : MeasurableEmbedding i₁)
    (hi₂ : MeasurableEmbedding i₂) (h : univ subseteq range i₁ union range i₂)
    (hf₁ : Measurable (f ∘ i₁)) (hf₂ : Measurable (f ∘ i₂)) : Measurable f :=
  fun _s hs => .of_union_range_cover hi₁ hi₂ h (hf₁ hs) (hf₂ hs)

/--
lemma `Measurable.of_union₃_range_cover` / 引理 `Measurable.of_union₃_range_cover`

English:
lemma Measurable.of_union₃_range_cover
  statement: (hi₁ : MeasurableEmbedding i₁)
  proof: fun _s hs => .of_union₃_range_cover hi₁ hi₂ hi₃ h (hf₁ hs) (hf₂ hs) (hf₃ hs)

中文:
引理 可测.of_union₃_range_cover
  结论: (hi₁ : 可测嵌入 i₁)
  证明: fun _s hs => .of_union₃_range_cover hi₁ hi₂ hi₃ h (hf₁ hs) (hf₂ hs) (hf₃ hs)
-/
lemma Measurable.of_union₃_range_cover (hi₁ : MeasurableEmbedding i₁)
    (hi₂ : MeasurableEmbedding i₂) (hi₃ : MeasurableEmbedding i₃)
    (h : univ subseteq range i₁ union range i₂ union range i₃) (hf₁ : Measurable (f ∘ i₁))
    (hf₂ : Measurable (f ∘ i₂)) (hf₃ : Measurable (f ∘ i₃)) : Measurable f :=
  fun _s hs => .of_union₃_range_cover hi₁ hi₂ hi₃ h (hf₁ hs) (hf₂ hs) (hf₃ hs)

end gluing

/--
theorem `MeasurableSet.exists_measurable_proj` / 定理 `MeasurableSet.exists_measurable_proj`

English:
theorem MeasurableSet.exists_measurable_proj
  statement: {_ : MeasurableSpace α}
  proof: let ⟨f, hfm, hf⟩ :=
    (MeasurableEmbedding.subtype_coe hs).exists_measurable_extend measurable_id fun _ =>
      hne.to_subtype
  ⟨f, hfm, congr_fun hf⟩

中文:
定理 可测集.存在_measurable_proj
  结论: {_ : 可测空间 α}
  证明: let ⟨f, hfm, hf⟩ :=
    (MeasurableEmbedding.subtype_coe hs).exists_measurable_extend measurable_id fun _ =>
      hne.to_subtype
  ⟨f, hfm, congr_fun hf⟩

Depends on / 依赖: MeasurableEmbedding, MeasurableEmbedding.subtype_coe, congr_fun, exists_measurable_extend, hne.to_subtype, measurable_id, subtype_coe, to_subtype
-/
theorem MeasurableSet.exists_measurable_proj {_ : MeasurableSpace α}
    (hs : MeasurableSet s) (hne : s.Nonempty) : exists f : α -> s, Measurable f ∧ forall x : s, f x = x :=
  let ⟨f, hfm, hf⟩ :=
    (MeasurableEmbedding.subtype_coe hs).exists_measurable_extend measurable_id fun _ =>
      hne.to_subtype
  ⟨f, hfm, congr_fun hf⟩

/--
Definition of `MeasurableEquiv` / `MeasurableEquiv` 的定义

English:
structure MeasurableEquiv
  parameters: (α β : Type*) [MeasurableSpace α] [MeasurableSpace β]
  extends: α ≃ β
  axioms and operations (2):
    - measurable_toFun : Measurable toEquiv  [default: by measurability]
    - measurable_invFun : Measurable toEquiv.symm  [default: by measurability]

中文:
结构 可测等价
  参数: (α β : 类型) [可测空间 α] [可测空间 β]
  继承: α ≃ β
  公理与运算 (2 个):
    - measurable_toFun : 可测 toEquiv  [默认: by measurability]
    - measurable_invFun : 可测 toEquiv.symm  [默认: by measurability]

Depends on / 依赖: measurability
-/
structure MeasurableEquiv (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] extends α ≃ β where
  /-- The forward function of a measurable equivalence is measurable. -/
  measurable_toFun : Measurable toEquiv := by measurability
  /-- The inverse function of a measurable equivalence is measurable. -/
  measurable_invFun : Measurable toEquiv.symm := by measurability

@[inherit_doc]
infixl:25 " ≃ᵐ " => MeasurableEquiv

namespace MeasurableEquiv

variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/--
theorem `toEquiv_injective` / 定理 `toEquiv_injective`

English:
theorem toEquiv_injective
  statement: Injective (toEquiv : α ≃ᵐ β -> α ≃ β)
  proof: by
  rintro ⟨e₁, _, _⟩ ⟨e₂, _, _⟩ (rfl : e₁ = e₂)
  rfl

中文:
定理 toEquiv_injective
  结论: 单射 (toEquiv : α ≃ᵐ β -> α ≃ β)
  证明: by
  rintro ⟨e₁, _, _⟩ ⟨e₂, _, _⟩ (rfl : e₁ = e₂)
  rfl
-/
theorem toEquiv_injective : Injective (toEquiv : α ≃ᵐ β -> α ≃ β) := by
  rintro ⟨e₁, _, _⟩ ⟨e₂, _, _⟩ (rfl : e₁ = e₂)
  rfl

/--
Instance `instEquivLike` / 实例 `instEquivLike`

English:
instance instEquivLike
  signature: : EquivLike (α ≃ᵐ β) α β where
  body: e.toEquiv
  inv e := e.toEquiv.symm
  left_inv e := e.toEquiv.left_inv
  right_inv e := e.toEquiv.right_inv
coe_injective' _ _ he _ := toEquiv_injective DFunLike.ext' he

@[simp]

中文:
实例 instEquivLike
  签名: : 等价状 (α ≃ᵐ β) α β where
  定义体: e.toEquiv
  inv e := e.toEquiv.symm
  left_inv e := e.toEquiv.left_inv
  right_inv e := e.toEquiv.right_inv
coe_injective' _ _ he _ := toEquiv_injective DFunLike.ext' he

@[simp]

Depends on / 依赖: e.toEquiv, toEquiv
-/
instance instEquivLike : EquivLike (α ≃ᵐ β) α β where
  coe e := e.toEquiv
  inv e := e.toEquiv.symm
  left_inv e := e.toEquiv.left_inv
  right_inv e := e.toEquiv.right_inv
coe_injective' _ _ he _ := toEquiv_injective DFunLike.ext' he

@[simp]
/--
theorem `coe_toEquiv` / 定理 `coe_toEquiv`

English:
theorem coe_toEquiv
  given: (e : α ≃ᵐ β)
  statement: (e.toEquiv : α -> β) = e
  proof: rfl

@[fun_prop]

中文:
定理 coe_toEquiv
  条件: (e : α ≃ᵐ β)
  结论: (e.toEquiv : α -> β) = e
  证明: rfl

@[fun_prop]
-/
theorem coe_toEquiv (e : α ≃ᵐ β) : (e.toEquiv : α -> β) = e :=
  rfl

@[fun_prop]
/--
theorem `measurable` / 定理 `measurable`

English:
theorem measurable
  given: (e : α ≃ᵐ β)
  statement: Measurable (e : α -> β)
  proof: e.measurable_toFun

@[simp]

中文:
定理 measurable
  条件: (e : α ≃ᵐ β)
  结论: 可测 (e : α -> β)
  证明: e.measurable_toFun

@[simp]
-/
protected theorem measurable (e : α ≃ᵐ β) : Measurable (e : α -> β) :=
  e.measurable_toFun

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (e : α ≃ β) (h1 : Measurable e) (h2 : Measurable e.symm)
  proof: rfl

中文:
定理 coe_mk
  条件: (e : α ≃ β) (h1 : 可测 e) (h2 : 可测 e.symm)
  证明: rfl
-/
theorem coe_mk (e : α ≃ β) (h1 : Measurable e) (h2 : Measurable e.symm) :
    ((⟨e, h1, h2⟩ : α ≃ᵐ β) : α -> β) = e :=
  rfl

/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: (α : Type*) [MeasurableSpace α]
  body: Equiv.refl α

中文:
定义 refl
  签名: (α : 类型) [可测空间 α]
  定义体: Equiv.refl α

Depends on / 依赖: Equiv.refl
-/
def refl (α : Type*) [MeasurableSpace α] : α ≃ᵐ α where
  toEquiv := Equiv.refl α

/--
Instance `instInhabited` / 实例 `instInhabited`

English:
instance instInhabited
  signature: : Inhabited (α ≃ᵐ α)
  body: ⟨refl α⟩

中文:
实例 instInhabited
  签名: : 可居 (α ≃ᵐ α)
  定义体: ⟨refl α⟩
-/
instance instInhabited : Inhabited (α ≃ᵐ α) := ⟨refl α⟩

/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: (ab : α ≃ᵐ β) (bc : β ≃ᵐ γ)
  body: ab.toEquiv.trans bc.toEquiv
  measurable_toFun := bc.measurable_toFun.comp ab.measurable_toFun
  measurable_invFun := ab.measurable_invFun.comp bc.measurable_invFun

中文:
定义 trans
  签名: (ab : α ≃ᵐ β) (bc : β ≃ᵐ γ)
  定义体: ab.toEquiv.trans bc.toEquiv
  measurable_toFun := bc.measurable_toFun.comp ab.measurable_toFun
  measurable_invFun := ab.measurable_invFun.comp bc.measurable_invFun

Depends on / 依赖: ab.toEquiv.trans, bc.toEquiv, toEquiv
-/
def trans (ab : α ≃ᵐ β) (bc : β ≃ᵐ γ) : α ≃ᵐ γ where
  toEquiv := ab.toEquiv.trans bc.toEquiv
  measurable_toFun := bc.measurable_toFun.comp ab.measurable_toFun
  measurable_invFun := ab.measurable_invFun.comp bc.measurable_invFun

/--
theorem `coe_trans` / 定理 `coe_trans`

English:
theorem coe_trans
  given: (ab : α ≃ᵐ β) (bc : β ≃ᵐ γ)
  statement: ⇑(ab.trans bc) = bc ∘ ab
  proof: rfl

中文:
定理 coe_trans
  条件: (ab : α ≃ᵐ β) (bc : β ≃ᵐ γ)
  结论: ⇑(ab.trans bc) = bc ∘ ab
  证明: rfl
-/
theorem coe_trans (ab : α ≃ᵐ β) (bc : β ≃ᵐ γ) : ⇑(ab.trans bc) = bc ∘ ab := rfl

/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: (ab : α ≃ᵐ β)
  body: ab.toEquiv.symm
  measurable_toFun := ab.measurable_invFun

@[simp]

中文:
定义 symm
  签名: (ab : α ≃ᵐ β)
  定义体: ab.toEquiv.symm
  measurable_toFun := ab.measurable_invFun

@[simp]

Depends on / 依赖: ab.toEquiv.symm, toEquiv
-/
def symm (ab : α ≃ᵐ β) : β ≃ᵐ α where
  toEquiv := ab.toEquiv.symm
  measurable_toFun := ab.measurable_invFun

@[simp]
/--
theorem `coe_toEquiv_symm` / 定理 `coe_toEquiv_symm`

English:
theorem coe_toEquiv_symm
  given: (e : α ≃ᵐ β)
  statement: (e.toEquiv.symm : β -> α) = e.symm
  proof: rfl

中文:
定理 coe_toEquiv_symm
  条件: (e : α ≃ᵐ β)
  结论: (e.toEquiv.symm : β -> α) = e.symm
  证明: rfl
-/
theorem coe_toEquiv_symm (e : α ≃ᵐ β) : (e.toEquiv.symm : β -> α) = e.symm :=
  rfl

/--
Definition of `Simps.apply` / `Simps.apply` 的定义

English:
definition Simps.apply
  signature: (h : α ≃ᵐ β)
  body: h

中文:
定义 Simps.apply
  签名: (h : α ≃ᵐ β)
  定义体: h
-/
def Simps.apply (h : α ≃ᵐ β) : α -> β := h

/--
Definition of `Simps.symm_apply` / `Simps.symm_apply` 的定义

English:
definition Simps.symm_apply
  signature: (h : α ≃ᵐ β)
  body: h.symm

initialize_simps_projections MeasurableEquiv (toFun -> apply, invFun -> symm_apply)

中文:
定义 Simps.symm_apply
  签名: (h : α ≃ᵐ β)
  定义体: h.symm

initialize_simps_projections MeasurableEquiv (toFun -> apply, invFun -> symm_apply)
-/
def Simps.symm_apply (h : α ≃ᵐ β) : β -> α := h.symm

initialize_simps_projections MeasurableEquiv (toFun -> apply, invFun -> symm_apply)

/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {e₁ e₂ : α ≃ᵐ β} (h : (e₁ : α -> β) = e₂)
  statement: e₁ = e₂
  proof: DFunLike.ext' h

@[simp]

中文:
定理 ext
  条件: {e₁ e₂ : α ≃ᵐ β} (h : (e₁ : α -> β) = e₂)
  结论: e₁ = e₂
  证明: DFunLike.ext' h

@[simp]
-/
@[ext] theorem ext {e₁ e₂ : α ≃ᵐ β} (h : (e₁ : α -> β) = e₂) : e₁ = e₂ := DFunLike.ext' h

@[simp]
/--
theorem `symm_mk` / 定理 `symm_mk`

English:
theorem symm_mk
  given: (e : α ≃ β) (h1 : Measurable e) (h2 : Measurable e.symm)
  proof: rfl

中文:
定理 symm_mk
  条件: (e : α ≃ β) (h1 : 可测 e) (h2 : 可测 e.symm)
  证明: rfl
-/
theorem symm_mk (e : α ≃ β) (h1 : Measurable e) (h2 : Measurable e.symm) :
    (⟨e, h1, h2⟩ : α ≃ᵐ β).symm = ⟨e.symm, h2, h1⟩ :=
  rfl

attribute [simps! apply toEquiv] trans refl

@[simp]
/--
theorem `symm_symm` / 定理 `symm_symm`

English:
theorem symm_symm
  given: (e : α ≃ᵐ β)
  statement: e.symm.symm = e
  proof: rfl

中文:
定理 symm_symm
  条件: (e : α ≃ᵐ β)
  结论: e.symm.symm = e
  证明: rfl
-/
theorem symm_symm (e : α ≃ᵐ β) : e.symm.symm = e := rfl

/--
theorem `symm_bijective` / 定理 `symm_bijective`

English:
theorem symm_bijective
  proof: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]

中文:
定理 symm_bijective
  证明: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]

Depends on / 依赖: Function, Function.bijective_iff_has_inverse.mpr, bijective_iff_has_inverse, symm_symm
-/
theorem symm_bijective :
    Function.Bijective (MeasurableEquiv.symm : (α ≃ᵐ β) -> β ≃ᵐ α) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]
/--
theorem `symm_refl` / 定理 `symm_refl`

English:
theorem symm_refl
  given: (α : Type*) [MeasurableSpace α]
  statement: (refl α).symm = refl α
  proof: rfl

@[simp]

中文:
定理 symm_refl
  条件: (α : 类型) [可测空间 α]
  结论: (refl α).symm = refl α
  证明: rfl

@[simp]
-/
theorem symm_refl (α : Type*) [MeasurableSpace α] : (refl α).symm = refl α :=
  rfl

@[simp]
/--
theorem `symm_comp_self` / 定理 `symm_comp_self`

English:
theorem symm_comp_self
  given: (e : α ≃ᵐ β)
  statement: e.symm ∘ e = id
  proof: funext e.left_inv

@[simp]

中文:
定理 symm_comp_self
  条件: (e : α ≃ᵐ β)
  结论: e.symm ∘ e = id
  证明: funext e.left_inv

@[simp]

Depends on / 依赖: e.left_inv, left_inv
-/
theorem symm_comp_self (e : α ≃ᵐ β) : e.symm ∘ e = id :=
  funext e.left_inv

@[simp]
/--
theorem `self_comp_symm` / 定理 `self_comp_symm`

English:
theorem self_comp_symm
  given: (e : α ≃ᵐ β)
  statement: e ∘ e.symm = id
  proof: funext e.right_inv

@[simp]

中文:
定理 self_comp_symm
  条件: (e : α ≃ᵐ β)
  结论: e ∘ e.symm = id
  证明: funext e.right_inv

@[simp]

Depends on / 依赖: e.right_inv, right_inv
-/
theorem self_comp_symm (e : α ≃ᵐ β) : e ∘ e.symm = id :=
  funext e.right_inv

@[simp]
/--
theorem `apply_symm_apply` / 定理 `apply_symm_apply`

English:
theorem apply_symm_apply
  given: (e : α ≃ᵐ β) (y : β)
  statement: e (e.symm y) = y
  proof: e.right_inv y

@[simp]

中文:
定理 apply_symm_apply
  条件: (e : α ≃ᵐ β) (y : β)
  结论: e (e.symm y) = y
  证明: e.right_inv y

@[simp]

Depends on / 依赖: e.right_inv, right_inv
-/
theorem apply_symm_apply (e : α ≃ᵐ β) (y : β) : e (e.symm y) = y :=
  e.right_inv y

@[simp]
/--
theorem `symm_apply_apply` / 定理 `symm_apply_apply`

English:
theorem symm_apply_apply
  given: (e : α ≃ᵐ β) (x : α)
  statement: e.symm (e x) = x
  proof: e.left_inv x

@[simp]

中文:
定理 symm_apply_apply
  条件: (e : α ≃ᵐ β) (x : α)
  结论: e.symm (e x) = x
  证明: e.left_inv x

@[simp]

Depends on / 依赖: e.left_inv, left_inv
-/
theorem symm_apply_apply (e : α ≃ᵐ β) (x : α) : e.symm (e x) = x :=
  e.left_inv x

@[simp]
/--
theorem `symm_trans_self` / 定理 `symm_trans_self`

English:
theorem symm_trans_self
  given: (e : α ≃ᵐ β)
  statement: e.symm.trans e = refl β
  proof: ext e.self_comp_symm

@[simp]

中文:
定理 symm_trans_self
  条件: (e : α ≃ᵐ β)
  结论: e.symm.trans e = refl β
  证明: ext e.self_comp_symm

@[simp]

Depends on / 依赖: e.self_comp_symm, self_comp_symm
-/
theorem symm_trans_self (e : α ≃ᵐ β) : e.symm.trans e = refl β :=
  ext e.self_comp_symm

@[simp]
/--
theorem `self_trans_symm` / 定理 `self_trans_symm`

English:
theorem self_trans_symm
  given: (e : α ≃ᵐ β)
  statement: e.trans e.symm = refl α
  proof: ext e.symm_comp_self

@[simp]

中文:
定理 self_trans_symm
  条件: (e : α ≃ᵐ β)
  结论: e.trans e.symm = refl α
  证明: ext e.symm_comp_self

@[simp]

Depends on / 依赖: e.symm_comp_self, symm_comp_self
-/
theorem self_trans_symm (e : α ≃ᵐ β) : e.trans e.symm = refl α :=
  ext e.symm_comp_self

@[simp]
/--
theorem `trans_symm` / 定理 `trans_symm`

English:
theorem trans_symm
  given: (e₁ : α ≃ᵐ β) (e₂ : β ≃ᵐ γ)
  statement: (e₁.trans e₂).symm = e₂.symm.trans (e₁.symm)
  proof: rfl

中文:
定理 trans_symm
  条件: (e₁ : α ≃ᵐ β) (e₂ : β ≃ᵐ γ)
  结论: (e₁.trans e₂).symm = e₂.symm.trans (e₁.symm)
  证明: rfl
-/
theorem trans_symm (e₁ : α ≃ᵐ β) (e₂ : β ≃ᵐ γ) : (e₁.trans e₂).symm = e₂.symm.trans (e₁.symm) :=
  rfl

/--
theorem `symm_apply_eq` / 定理 `symm_apply_eq`

English:
theorem symm_apply_eq
  given: (e : α ≃ᵐ β) {x y}
  statement: e.symm x = y ↔ x = e y
  proof: e.toEquiv.symm_apply_eq

中文:
定理 symm_apply_eq
  条件: (e : α ≃ᵐ β) {x y}
  结论: e.symm x = y ↔ x = e y
  证明: e.toEquiv.symm_apply_eq

Depends on / 依赖: e.toEquiv.symm_apply_eq, symm_apply_eq, toEquiv
-/
theorem symm_apply_eq (e : α ≃ᵐ β) {x y} : e.symm x = y ↔ x = e y :=
  e.toEquiv.symm_apply_eq

/--
theorem `eq_symm_apply` / 定理 `eq_symm_apply`

English:
theorem eq_symm_apply
  given: (e : α ≃ᵐ β) {x y}
  statement: y = e.symm x ↔ e y = x
  proof: e.toEquiv.eq_symm_apply

中文:
定理 eq_symm_apply
  条件: (e : α ≃ᵐ β) {x y}
  结论: y = e.symm x ↔ e y = x
  证明: e.toEquiv.eq_symm_apply

Depends on / 依赖: e.toEquiv.eq_symm_apply, eq_symm_apply, toEquiv
-/
theorem eq_symm_apply (e : α ≃ᵐ β) {x y} : y = e.symm x ↔ e y = x :=
  e.toEquiv.eq_symm_apply

/--
theorem `surjective` / 定理 `surjective`

English:
theorem surjective
  given: (e : α ≃ᵐ β)
  statement: Surjective e
  proof: e.toEquiv.surjective

中文:
定理 surjective
  条件: (e : α ≃ᵐ β)
  结论: 满射 e
  证明: e.toEquiv.surjective
-/
protected theorem surjective (e : α ≃ᵐ β) : Surjective e :=
  e.toEquiv.surjective

/--
theorem `bijective` / 定理 `bijective`

English:
theorem bijective
  given: (e : α ≃ᵐ β)
  statement: Bijective e
  proof: e.toEquiv.bijective

中文:
定理 bijective
  条件: (e : α ≃ᵐ β)
  结论: 双射 e
  证明: e.toEquiv.bijective
-/
protected theorem bijective (e : α ≃ᵐ β) : Bijective e :=
  e.toEquiv.bijective

/--
theorem `injective` / 定理 `injective`

English:
theorem injective
  given: (e : α ≃ᵐ β)
  statement: Injective e
  proof: e.toEquiv.injective

@[simp]

中文:
定理 injective
  条件: (e : α ≃ᵐ β)
  结论: 单射 e
  证明: e.toEquiv.injective

@[simp]
-/
protected theorem injective (e : α ≃ᵐ β) : Injective e :=
  e.toEquiv.injective

@[simp]
/--
theorem `symm_preimage_preimage` / 定理 `symm_preimage_preimage`

English:
theorem symm_preimage_preimage
  given: (e : α ≃ᵐ β) (s : Set β)
  statement: e.symm ⁻¹' e ⁻¹' s = s
  proof: e.toEquiv.symm_preimage_preimage s

中文:
定理 symm_preimage_preimage
  条件: (e : α ≃ᵐ β) (s : 集合 β)
  结论: e.symm ⁻¹' e ⁻¹' s = s
  证明: e.toEquiv.symm_preimage_preimage s

Depends on / 依赖: e.toEquiv.symm_preimage_preimage, symm_preimage_preimage, toEquiv
-/
theorem symm_preimage_preimage (e : α ≃ᵐ β) (s : Set β) : e.symm ⁻¹' e ⁻¹' s = s :=
  e.toEquiv.symm_preimage_preimage s

/--
theorem `image_eq_preimage_symm` / 定理 `image_eq_preimage_symm`

English:
theorem image_eq_preimage_symm
  given: (e : α ≃ᵐ β) (s : Set α)
  statement: e '' s = e.symm ⁻¹' s
  proof: e.toEquiv.image_eq_preimage_symm s

中文:
定理 image_eq_preimage_symm
  条件: (e : α ≃ᵐ β) (s : 集合 α)
  结论: e '' s = e.symm ⁻¹' s
  证明: e.toEquiv.image_eq_preimage_symm s

Depends on / 依赖: e.toEquiv.image_eq_preimage_symm, image_eq_preimage_symm, toEquiv
-/
theorem image_eq_preimage_symm (e : α ≃ᵐ β) (s : Set α) : e '' s = e.symm ⁻¹' s :=
  e.toEquiv.image_eq_preimage_symm s

/--
lemma `preimage_symm` / 引理 `preimage_symm`

English:
lemma preimage_symm
  given: (e : α ≃ᵐ β) (s : Set α)
  statement: e.symm ⁻¹' s = e '' s
  proof: (image_eq_preimage_symm ..).symm

中文:
引理 preimage_symm
  条件: (e : α ≃ᵐ β) (s : 集合 α)
  结论: e.symm ⁻¹' s = e '' s
  证明: (image_eq_preimage_symm ..).symm

Depends on / 依赖: image_eq_preimage_symm
-/
lemma preimage_symm (e : α ≃ᵐ β) (s : Set α) : e.symm ⁻¹' s = e '' s :=
  (image_eq_preimage_symm ..).symm

/--
lemma `image_symm` / 引理 `image_symm`

English:
lemma image_symm
  given: (e : α ≃ᵐ β) (s : Set β)
  statement: e.symm '' s = e ⁻¹' s
  proof: image_symm_eq_preimage ..

中文:
引理 image_symm
  条件: (e : α ≃ᵐ β) (s : 集合 β)
  结论: e.symm '' s = e ⁻¹' s
  证明: image_symm_eq_preimage ..

Depends on / 依赖: image_symm_eq_preimage
-/
lemma image_symm (e : α ≃ᵐ β) (s : Set β) : e.symm '' s = e ⁻¹' s := image_symm_eq_preimage ..

/--
lemma `eq_image_iff_symm_image_eq` / 引理 `eq_image_iff_symm_image_eq`

English:
lemma eq_image_iff_symm_image_eq
  given: (e : α ≃ᵐ β) (s : Set β) (t : Set α)
  proof: by
  rw [← coe_toEquiv]; rw [Equiv.eq_image_iff_symm_image_eq]; rw [coe_toEquiv_symm]

@[simp]

中文:
引理 eq_image_iff_symm_image_eq
  条件: (e : α ≃ᵐ β) (s : 集合 β) (t : 集合 α)
  证明: by
  rw [← coe_toEquiv]; rw [Equiv.eq_image_iff_symm_image_eq]; rw [coe_toEquiv_symm]

@[simp]

Depends on / 依赖: Equiv.eq_image_iff_symm_image_eq, coe_toEquiv, coe_toEquiv_symm, eq_image_iff_symm_image_eq
-/
lemma eq_image_iff_symm_image_eq (e : α ≃ᵐ β) (s : Set β) (t : Set α) :
    s = e '' t ↔ e.symm '' s = t := by
  rw [← coe_toEquiv]; rw [Equiv.eq_image_iff_symm_image_eq]; rw [coe_toEquiv_symm]

@[simp]
/--
lemma `image_preimage` / 引理 `image_preimage`

English:
lemma image_preimage
  given: (e : α ≃ᵐ β) (s : Set β)
  statement: e '' e ⁻¹' s = s
  proof: by
  rw [← coe_toEquiv]; rw [Equiv.image_preimage]

@[simp]

中文:
引理 image_preimage
  条件: (e : α ≃ᵐ β) (s : 集合 β)
  结论: e '' e ⁻¹' s = s
  证明: by
  rw [← coe_toEquiv]; rw [Equiv.image_preimage]

@[simp]

Depends on / 依赖: Equiv.image_preimage, coe_toEquiv, image_preimage
-/
lemma image_preimage (e : α ≃ᵐ β) (s : Set β) : e '' e ⁻¹' s = s := by
  rw [← coe_toEquiv]; rw [Equiv.image_preimage]

@[simp]
/--
lemma `preimage_image` / 引理 `preimage_image`

English:
lemma preimage_image
  given: (e : α ≃ᵐ β) (s : Set α)
  statement: e ⁻¹' e '' s = s
  proof: by
  rw [← coe_toEquiv]; rw [Equiv.preimage_image]

@[simp]

中文:
引理 preimage_image
  条件: (e : α ≃ᵐ β) (s : 集合 α)
  结论: e ⁻¹' e '' s = s
  证明: by
  rw [← coe_toEquiv]; rw [Equiv.preimage_image]

@[simp]

Depends on / 依赖: Equiv.preimage_image, coe_toEquiv, preimage_image
-/
lemma preimage_image (e : α ≃ᵐ β) (s : Set α) : e ⁻¹' e '' s = s := by
  rw [← coe_toEquiv]; rw [Equiv.preimage_image]

@[simp]
/--
theorem `measurableSet_preimage` / 定理 `measurableSet_preimage`

English:
theorem measurableSet_preimage
  given: (e : α ≃ᵐ β) {s : Set β}
  proof: ⟨fun h => by simpa only [symm_preimage_preimage] using e.symm.measurable h, fun h =>
    e.measurable h⟩

@[simp]

中文:
定理 measurableSet_preimage
  条件: (e : α ≃ᵐ β) {s : 集合 β}
  证明: ⟨fun h => by simpa only [symm_preimage_preimage] using e.symm.measurable h, fun h =>
    e.measurable h⟩

@[simp]

Depends on / 依赖: e.measurable, e.symm.measurable, measurable, symm_preimage_preimage
-/
theorem measurableSet_preimage (e : α ≃ᵐ β) {s : Set β} :
    MeasurableSet (e ⁻¹' s) ↔ MeasurableSet s :=
  ⟨fun h => by simpa only [symm_preimage_preimage] using e.symm.measurable h, fun h =>
    e.measurable h⟩

@[simp]
/--
theorem `measurableSet_image` / 定理 `measurableSet_image`

English:
theorem measurableSet_image
  given: (e : α ≃ᵐ β)
  statement: MeasurableSet (e '' s) ↔ MeasurableSet s
  proof: by
  rw [image_eq_preimage_symm]; rw [measurableSet_preimage]

中文:
定理 measurableSet_image
  条件: (e : α ≃ᵐ β)
  结论: 可测集 (e '' s) ↔ 可测集 s
  证明: by
  rw [image_eq_preimage_symm]; rw [measurableSet_preimage]

Depends on / 依赖: image_eq_preimage_symm, measurableSet_preimage
-/
theorem measurableSet_image (e : α ≃ᵐ β) : MeasurableSet (e '' s) ↔ MeasurableSet s := by
  rw [image_eq_preimage_symm]; rw [measurableSet_preimage]

/--
theorem `map_eq` / 定理 `map_eq`

English:
theorem map_eq
  given: (e : α ≃ᵐ β)
  statement: MeasurableSpace.map e ‹_› = ‹_›
  proof: e.measurable.le_map.antisymm' fun _s => e.measurableSet_preimage.1

中文:
定理 map_eq
  条件: (e : α ≃ᵐ β)
  结论: 可测空间.map e ‹_› = ‹_›
  证明: e.measurable.le_map.antisymm' fun _s => e.measurableSet_preimage.1
-/
@[simp] theorem map_eq (e : α ≃ᵐ β) : MeasurableSpace.map e ‹_› = ‹_› :=
  e.measurable.le_map.antisymm' fun _s => e.measurableSet_preimage.1

/--
theorem `measurableEmbedding` / 定理 `measurableEmbedding`

English:
theorem measurableEmbedding
  given: (e : α ≃ᵐ β)
  statement: MeasurableEmbedding e where
  proof: e.injective
  measurable := e.measurable
  measurableSet_image' := fun _ => e.measurableSet_image.2

中文:
定理 measurableEmbedding
  条件: (e : α ≃ᵐ β)
  结论: 可测嵌入 e where
  证明: e.injective
  measurable := e.measurable
  measurableSet_image' := fun _ => e.measurableSet_image.2
-/
protected theorem measurableEmbedding (e : α ≃ᵐ β) : MeasurableEmbedding e where
  injective := e.injective
  measurable := e.measurable
  measurableSet_image' := fun _ => e.measurableSet_image.2

/--
Definition of `cast` / `cast` 的定义

English:
definition cast
  signature: {α β} [i₁ : MeasurableSpace α] [i₂ : MeasurableSpace β] (h : α = β)
  body: Equiv.cast h

中文:
定义 cast
  签名: {α β} [i₁ : 可测空间 α] [i₂ : 可测空间 β] (h : α = β)
  定义体: Equiv.cast h
-/
protected def cast {α β} [i₁ : MeasurableSpace α] [i₂ : MeasurableSpace β] (h : α = β)
    (hi : i₁ ≍ i₂) : α ≃ᵐ β where
  toEquiv := Equiv.cast h

/--
Definition of `ulift.` / `ulift.` 的定义

English:
definition ulift.{u,
  signature: v} {α
  body: ⟨Equiv.ulift, measurable_down, measurable_up⟩

中文:
定义 ulift.{u,
  签名: v} {α
  定义体: ⟨Equiv.ulift, measurable_down, measurable_up⟩

Depends on / 依赖: Equiv.ulift, measurable_down, measurable_up
-/
def ulift.{u, v} {α : Type u} [MeasurableSpace α] : ULift.{v, u} α ≃ᵐ α :=
  ⟨Equiv.ulift, measurable_down, measurable_up⟩

/--
theorem `measurable_comp_iff` / 定理 `measurable_comp_iff`

English:
theorem measurable_comp_iff
  given: {f : β -> γ} (e : α ≃ᵐ β)
  proof: Iff.intro
    (fun hfe => by
      have : Measurable (f ∘ (e.symm.trans e).toEquiv) := hfe.comp e.symm.measurable
      rwa [coe_toEquiv, symm_trans_self] at this)
    fun h => h.comp e.measurable

中文:
定理 measurable_comp_iff
  条件: {f : β -> γ} (e : α ≃ᵐ β)
  证明: Iff.intro
    (fun hfe => by
      have : Measurable (f ∘ (e.symm.trans e).toEquiv) := hfe.comp e.symm.measurable
      rwa [coe_toEquiv, symm_trans_self] at this)
    fun h => h.comp e.measurable
-/
protected theorem measurable_comp_iff {f : β -> γ} (e : α ≃ᵐ β) :
    Measurable (f ∘ e) ↔ Measurable f :=
  Iff.intro
    (fun hfe => by
      have : Measurable (f ∘ (e.symm.trans e).toEquiv) := hfe.comp e.symm.measurable
      rwa [coe_toEquiv, symm_trans_self] at this)
    fun h => h.comp e.measurable

/--
Definition of `ofUniqueOfUnique` / `ofUniqueOfUnique` 的定义

English:
definition ofUniqueOfUnique
  signature: (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] [Unique α] [Unique β]
  body: ofUnique α β

中文:
定义 ofUniqueOfUnique
  签名: (α β : 类型) [可测空间 α] [可测空间 β] [唯一 α] [唯一 β]
  定义体: ofUnique α β

Depends on / 依赖: ofUnique
-/
def ofUniqueOfUnique (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] [Unique α] [Unique β] :
    α ≃ᵐ β where
  toEquiv := ofUnique α β

variable [MeasurableSpace δ] in
/--
Definition of `prodCongr` / `prodCongr` 的定义

English:
definition prodCongr
  signature: (ab : α ≃ᵐ β) (cd : γ ≃ᵐ δ)
  body: .prodCongr ab.toEquiv cd.toEquiv

中文:
定义 prodCongr
  签名: (ab : α ≃ᵐ β) (cd : γ ≃ᵐ δ)
  定义体: .prodCongr ab.toEquiv cd.toEquiv

Depends on / 依赖: ab.toEquiv, cd.toEquiv, prodCongr, toEquiv
-/
def prodCongr (ab : α ≃ᵐ β) (cd : γ ≃ᵐ δ) : α × γ ≃ᵐ β × δ where
  toEquiv := .prodCongr ab.toEquiv cd.toEquiv

/--
Definition of `prodComm` / `prodComm` 的定义

English:
definition prodComm
  signature: : α × β ≃ᵐ β × α where
  body: .prodComm α β

中文:
定义 prodComm
  签名: : α × β ≃ᵐ β × α where
  定义体: .prodComm α β

Depends on / 依赖: prodComm
-/
def prodComm : α × β ≃ᵐ β × α where
  toEquiv := .prodComm α β

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `prodAssoc` / `prodAssoc` 的定义

English:
definition prodAssoc
  signature: : (α × β) × γ ≃ᵐ α × β × γ where
  body: .prodAssoc α β γ
  measurable_toFun := by eta_expand; dsimp; measurability
  measurable_invFun := by eta_expand; dsimp; measurability

中文:
定义 prodAssoc
  签名: : (α × β) × γ ≃ᵐ α × β × γ where
  定义体: .prodAssoc α β γ
  measurable_toFun := by eta_expand; dsimp; measurability
  measurable_invFun := by eta_expand; dsimp; measurability

Depends on / 依赖: prodAssoc
-/
def prodAssoc : (α × β) × γ ≃ᵐ α × β × γ where
  toEquiv := .prodAssoc α β γ
  measurable_toFun := by eta_expand; dsimp; measurability
  measurable_invFun := by eta_expand; dsimp; measurability

/--
Definition of `punitProd` / `punitProd` 的定义

English:
definition punitProd
  signature: : PUnit × α ≃ᵐ α where
  body: Equiv.punitProd α
  measurable_toFun := measurable_snd
  measurable_invFun := measurable_prodMk_left

中文:
定义 punitProd
  签名: : 命题单元 × α ≃ᵐ α where
  定义体: Equiv.punitProd α
  measurable_toFun := measurable_snd
  measurable_invFun := measurable_prodMk_left

Depends on / 依赖: Equiv.punitProd, punitProd
-/
def punitProd : PUnit × α ≃ᵐ α where
  toEquiv := Equiv.punitProd α
  measurable_toFun := measurable_snd
  measurable_invFun := measurable_prodMk_left

/--
Definition of `prodPUnit` / `prodPUnit` 的定义

English:
definition prodPUnit
  signature: : α × PUnit ≃ᵐ α where
  body: Equiv.prodPUnit α
  measurable_toFun := measurable_fst
  measurable_invFun := measurable_prodMk_right

中文:
定义 prodPUnit
  签名: : α × 命题单元 ≃ᵐ α where
  定义体: Equiv.prodPUnit α
  measurable_toFun := measurable_fst
  measurable_invFun := measurable_prodMk_right

Depends on / 依赖: Equiv.prodPUnit, prodPUnit
-/
def prodPUnit : α × PUnit ≃ᵐ α where
  toEquiv := Equiv.prodPUnit α
  measurable_toFun := measurable_fst
  measurable_invFun := measurable_prodMk_right

variable [MeasurableSpace δ] in
/--
Definition of `sumCongr` / `sumCongr` 的定义

English:
definition sumCongr
  signature: (ab : α ≃ᵐ β) (cd : γ ≃ᵐ δ)
  body: .sumCongr ab.toEquiv cd.toEquiv
  measurable_toFun := ab.measurable.sumMap cd.measurable
  measurable_invFun := ab.symm.measurable.sumMap cd.symm.measurable

中文:
定义 sumCongr
  签名: (ab : α ≃ᵐ β) (cd : γ ≃ᵐ δ)
  定义体: .sumCongr ab.toEquiv cd.toEquiv
  measurable_toFun := ab.measurable.sumMap cd.measurable
  measurable_invFun := ab.symm.measurable.sumMap cd.symm.measurable

Depends on / 依赖: ab.toEquiv, cd.toEquiv, sumCongr, toEquiv
-/
def sumCongr (ab : α ≃ᵐ β) (cd : γ ≃ᵐ δ) : α oplus γ ≃ᵐ β oplus δ where
  toEquiv := .sumCongr ab.toEquiv cd.toEquiv
  measurable_toFun := ab.measurable.sumMap cd.measurable
  measurable_invFun := ab.symm.measurable.sumMap cd.symm.measurable

/--
Definition of `Set.prod` / `Set.prod` 的定义

English:
definition Set.prod
  signature: (s : Set α) (t : Set β)
  body: Equiv.Set.prod s t
  measurable_toFun := .prodMk (by measurability) (by measurability)
measurable_invFun := Measurable.subtype_mk by fun_prop

中文:
定义 集合.乘积
  签名: (s : 集合 α) (t : 集合 β)
  定义体: Equiv.Set.prod s t
  measurable_toFun := .prodMk (by measurability) (by measurability)
measurable_invFun := Measurable.subtype_mk by fun_prop
-/
def Set.prod (s : Set α) (t : Set β) : ↥(s ×ˢ t) ≃ᵐ s × t where
  toEquiv := Equiv.Set.prod s t
  measurable_toFun := .prodMk (by measurability) (by measurability)
measurable_invFun := Measurable.subtype_mk by fun_prop

/--
Definition of `Set.univ` / `Set.univ` 的定义

English:
definition Set.univ
  signature: (α : Type*) [MeasurableSpace α]
  body: Equiv.Set.univ α
  measurable_toFun := measurable_id.subtype_val
  measurable_invFun := measurable_id.subtype_mk

中文:
定义 集合.univ
  签名: (α : 类型) [可测空间 α]
  定义体: Equiv.Set.univ α
  measurable_toFun := measurable_id.subtype_val
  measurable_invFun := measurable_id.subtype_mk
-/
def Set.univ (α : Type*) [MeasurableSpace α] : (univ : Set α) ≃ᵐ α where
  toEquiv := Equiv.Set.univ α
  measurable_toFun := measurable_id.subtype_val
  measurable_invFun := measurable_id.subtype_mk

/--
Definition of `Set.singleton` / `Set.singleton` 的定义

English:
definition Set.singleton
  signature: (a : α)
  body: Equiv.Set.singleton a

中文:
定义 集合.singleton
  签名: (a : α)
  定义体: Equiv.Set.singleton a

Depends on / 依赖: Equiv.Set.singleton, singleton
-/
def Set.singleton (a : α) : ({a} : Set α) ≃ᵐ Unit where
  toEquiv := Equiv.Set.singleton a

/--
Definition of `Set.rangeInl` / `Set.rangeInl` 的定义

English:
definition Set.rangeInl
  signature: : (range Sum.inl : Set (α oplus β)) ≃ᵐ α where
  body: Equiv.Set.rangeInl α β
  measurable_toFun s (hs : MeasurableSet s) := by
    refine ⟨_, hs.inl_image, Set.ext ?_⟩
    simp
  measurable_invFun := Measurable.subtype_mk measurable_inl

中文:
定义 集合.rangeInl
  签名: : (range 和.inl : 集合 (α oplus β)) ≃ᵐ α where
  定义体: Equiv.Set.rangeInl α β
  measurable_toFun s (hs : MeasurableSet s) := by
    refine ⟨_, hs.inl_image, Set.ext ?_⟩
    simp
  measurable_invFun := Measurable.subtype_mk measurable_inl

Depends on / 依赖: Equiv.Set.rangeInl, rangeInl
-/
def Set.rangeInl : (range Sum.inl : Set (α oplus β)) ≃ᵐ α where
  toEquiv := Equiv.Set.rangeInl α β
  measurable_toFun s (hs : MeasurableSet s) := by
    refine ⟨_, hs.inl_image, Set.ext ?_⟩
    simp
  measurable_invFun := Measurable.subtype_mk measurable_inl

/--
Definition of `Set.rangeInr` / `Set.rangeInr` 的定义

English:
definition Set.rangeInr
  signature: : (range Sum.inr : Set (α oplus β)) ≃ᵐ β where
  body: Equiv.Set.rangeInr α β
  measurable_toFun s (hs : MeasurableSet s) := by
    refine ⟨_, hs.inr_image, Set.ext ?_⟩
    simp
  measurable_invFun := Measurable.subtype_mk measurable_inr

中文:
定义 集合.rangeInr
  签名: : (range 和.inr : 集合 (α oplus β)) ≃ᵐ β where
  定义体: Equiv.Set.rangeInr α β
  measurable_toFun s (hs : MeasurableSet s) := by
    refine ⟨_, hs.inr_image, Set.ext ?_⟩
    simp
  measurable_invFun := Measurable.subtype_mk measurable_inr

Depends on / 依赖: Equiv.Set.rangeInr, rangeInr
-/
def Set.rangeInr : (range Sum.inr : Set (α oplus β)) ≃ᵐ β where
  toEquiv := Equiv.Set.rangeInr α β
  measurable_toFun s (hs : MeasurableSet s) := by
    refine ⟨_, hs.inr_image, Set.ext ?_⟩
    simp
  measurable_invFun := Measurable.subtype_mk measurable_inr

/--
Definition of `sumProdDistrib` / `sumProdDistrib` 的定义

English:
definition sumProdDistrib
  signature: (α β γ) [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  body: .sumProdDistrib α β γ
  measurable_toFun := by
    refine
      measurable_of_measurable_union_cover (range Sum.inl ×ˢ (univ : Set γ))
        (range Sum.inr ×ˢ (univ : Set γ)) (measurableSet_range_inl.prod MeasurableSet.univ)
        (measurableSet_range_inr.prod MeasurableSet.univ)
        (by rintro ⟨a | b, c⟩ <;> simp [Set.prod_eq]) ?_ ?_
    · refine (Set.prod (range Sum.inl) univ).symm.measurable_comp_iff.1 ?_
      refine (prodCongr Set.rangeInl (Set.univ _)).symm.measurable_comp_iff.1 ?_
      exact measurable_inl
    · refine (Set.prod (range Sum.inr) univ).symm.measurable_comp_iff.1 ?_
      refine (prodCongr Set.rangeInr (Set.univ _)).symm.measurable_comp_iff.1 ?_
      exact measurable_inr
  measurable_invFun :=
    measurable_fun_sum ((measurable_inl.comp measurable_fst).prodMk measurable_snd)
      ((measurable_inr.comp measurable_fst).prodMk measurable_snd)

中文:
定义 sumProdDistrib
  签名: (α β γ) [可测空间 α] [可测空间 β] [可测空间 γ]
  定义体: .sumProdDistrib α β γ
  measurable_toFun := by
    refine
      measurable_of_measurable_union_cover (range Sum.inl ×ˢ (univ : Set γ))
        (range Sum.inr ×ˢ (univ : Set γ)) (measurableSet_range_inl.prod MeasurableSet.univ)
        (measurableSet_range_inr.prod MeasurableSet.univ)
        (by rintro ⟨a | b, c⟩ <;> simp [Set.prod_eq]) ?_ ?_
    · refine (Set.prod (range Sum.inl) univ).symm.measurable_comp_iff.1 ?_
      refine (prodCongr Set.rangeInl (Set.univ _)).symm.measurable_comp_iff.1 ?_
      exact measurable_inl
    · refine (Set.prod (range Sum.inr) univ).symm.measurable_comp_iff.1 ?_
      refine (prodCongr Set.rangeInr (Set.univ _)).symm.measurable_comp_iff.1 ?_
      exact measurable_inr
  measurable_invFun :=
    measurable_fun_sum ((measurable_inl.comp measurable_fst).prodMk measurable_snd)
      ((measurable_inr.comp measurable_fst).prodMk measurable_snd)

Depends on / 依赖: sumProdDistrib
-/
def sumProdDistrib (α β γ) [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] :
    (α oplus β) × γ ≃ᵐ (α × γ) oplus (β × γ) where
  toEquiv := .sumProdDistrib α β γ
  measurable_toFun := by
    refine
      measurable_of_measurable_union_cover (range Sum.inl ×ˢ (univ : Set γ))
        (range Sum.inr ×ˢ (univ : Set γ)) (measurableSet_range_inl.prod MeasurableSet.univ)
        (measurableSet_range_inr.prod MeasurableSet.univ)
        (by rintro ⟨a | b, c⟩ <;> simp [Set.prod_eq]) ?_ ?_
    · refine (Set.prod (range Sum.inl) univ).symm.measurable_comp_iff.1 ?_
      refine (prodCongr Set.rangeInl (Set.univ _)).symm.measurable_comp_iff.1 ?_
      exact measurable_inl
    · refine (Set.prod (range Sum.inr) univ).symm.measurable_comp_iff.1 ?_
      refine (prodCongr Set.rangeInr (Set.univ _)).symm.measurable_comp_iff.1 ?_
      exact measurable_inr
  measurable_invFun :=
    measurable_fun_sum ((measurable_inl.comp measurable_fst).prodMk measurable_snd)
      ((measurable_inr.comp measurable_fst).prodMk measurable_snd)

/--
Definition of `prodSumDistrib` / `prodSumDistrib` 的定义

English:
definition prodSumDistrib
  signature: (α β γ) [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  body: prodComm.trans (sumProdDistrib _ _ _).trans sumCongr prodComm prodComm

中文:
定义 prodSumDistrib
  签名: (α β γ) [可测空间 α] [可测空间 β] [可测空间 γ]
  定义体: prodComm.trans (sumProdDistrib _ _ _).trans sumCongr prodComm prodComm

Depends on / 依赖: prodComm, prodComm.trans, sumCongr, sumProdDistrib
-/
def prodSumDistrib (α β γ) [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] :
    α × (β oplus γ) ≃ᵐ (α × β) oplus (α × γ) :=
prodComm.trans (sumProdDistrib _ _ _).trans sumCongr prodComm prodComm

/--
Definition of `sumProdSum` / `sumProdSum` 的定义

English:
definition sumProdSum
  signature: (α β γ δ) [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  body: (sumProdDistrib _ _ _).trans sumCongr (prodSumDistrib _ _ _) (prodSumDistrib _ _ _)

中文:
定义 sumProdSum
  签名: (α β γ δ) [可测空间 α] [可测空间 β] [可测空间 γ]
  定义体: (sumProdDistrib _ _ _).trans sumCongr (prodSumDistrib _ _ _) (prodSumDistrib _ _ _)

Depends on / 依赖: prodSumDistrib, sumCongr, sumProdDistrib
-/
def sumProdSum (α β γ δ) [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace δ] : (α oplus β) × (γ oplus δ) ≃ᵐ ((α × γ) oplus (α × δ)) oplus ((β × γ) oplus (β × δ)) :=
(sumProdDistrib _ _ _).trans sumCongr (prodSumDistrib _ _ _) (prodSumDistrib _ _ _)

variable {π π' : δ' -> Type*} [forall x, MeasurableSpace (π x)] [forall x, MeasurableSpace (π' x)]

/--
Definition of `subtypePiEquivPi` / `subtypePiEquivPi` 的定义

English:
definition subtypePiEquivPi
  signature: {p : (a : δ') -> π a -> Prop}
  body: .subtypePiEquivPi
  measurable_toFun := measurable_pi_lambda _ (fun a =>
    ((measurable_pi_apply a).comp measurable_subtype_coe).subtype_mk)
  measurable_invFun := (measurable_pi_lambda _ (fun a =>
    measurable_subtype_coe.comp (measurable_pi_apply a))).subtype_mk

中文:
定义 subtypePiEquivPi
  签名: {p : (a : δ') -> π a -> 命题}
  定义体: .subtypePiEquivPi
  measurable_toFun := measurable_pi_lambda _ (fun a =>
    ((measurable_pi_apply a).comp measurable_subtype_coe).subtype_mk)
  measurable_invFun := (measurable_pi_lambda _ (fun a =>
    measurable_subtype_coe.comp (measurable_pi_apply a))).subtype_mk

Depends on / 依赖: subtypePiEquivPi
-/
def subtypePiEquivPi {p : (a : δ') -> π a -> Prop} :
    { f : (a : δ') -> π a // forall (a : δ'), p a (f a) } ≃ᵐ ((a : δ') -> { b : π a // p a b }) where
  toEquiv := .subtypePiEquivPi
  measurable_toFun := measurable_pi_lambda _ (fun a =>
    ((measurable_pi_apply a).comp measurable_subtype_coe).subtype_mk)
  measurable_invFun := (measurable_pi_lambda _ (fun a =>
    measurable_subtype_coe.comp (measurable_pi_apply a))).subtype_mk

/--
Definition of `piCongrRight` / `piCongrRight` 的定义

English:
definition piCongrRight
  signature: (e : forall a, π a ≃ᵐ π' a)
  body: .piCongrRight fun a => (e a).toEquiv
  measurable_toFun :=
    measurable_pi_lambda _ fun i => (e i).measurable_toFun.comp (measurable_pi_apply i)
  measurable_invFun :=
    measurable_pi_lambda _ fun i => (e i).measurable_invFun.comp (measurable_pi_apply i)

中文:
定义 piCongrRight
  签名: (e : 对任意 a, π a ≃ᵐ π' a)
  定义体: .piCongrRight fun a => (e a).toEquiv
  measurable_toFun :=
    measurable_pi_lambda _ fun i => (e i).measurable_toFun.comp (measurable_pi_apply i)
  measurable_invFun :=
    measurable_pi_lambda _ fun i => (e i).measurable_invFun.comp (measurable_pi_apply i)

Depends on / 依赖: piCongrRight, toEquiv
-/
def piCongrRight (e : forall a, π a ≃ᵐ π' a) : (forall a, π a) ≃ᵐ forall a, π' a where
  toEquiv := .piCongrRight fun a => (e a).toEquiv
  measurable_toFun :=
    measurable_pi_lambda _ fun i => (e i).measurable_toFun.comp (measurable_pi_apply i)
  measurable_invFun :=
    measurable_pi_lambda _ fun i => (e i).measurable_invFun.comp (measurable_pi_apply i)

variable (π) in
/--
Definition of `piCongrLeft` / `piCongrLeft` 的定义

English:
definition piCongrLeft
  signature: (f : δ ≃ δ')
  body: Equiv.piCongrLeft π f
  measurable_invFun := by
    rw [measurable_pi_iff]
    exact fun i => measurable_pi_apply (f i)

中文:
定义 piCongrLeft
  签名: (f : δ ≃ δ')
  定义体: Equiv.piCongrLeft π f
  measurable_invFun := by
    rw [measurable_pi_iff]
    exact fun i => measurable_pi_apply (f i)

Depends on / 依赖: Equiv.piCongrLeft, piCongrLeft
-/
def piCongrLeft (f : δ ≃ δ') : (forall b, π (f b)) ≃ᵐ forall a, π a where
  __ := Equiv.piCongrLeft π f
  measurable_invFun := by
    rw [measurable_pi_iff]
    exact fun i => measurable_pi_apply (f i)

/--
theorem `coe_piCongrLeft` / 定理 `coe_piCongrLeft`

English:
theorem coe_piCongrLeft
  given: (f : δ ≃ δ')
  proof: by rfl

中文:
定理 coe_piCongrLeft
  条件: (f : δ ≃ δ')
  证明: by rfl
-/
theorem coe_piCongrLeft (f : δ ≃ δ') :
    ⇑(MeasurableEquiv.piCongrLeft π f) = f.piCongrLeft π := by rfl

/--
lemma `piCongrLeft_apply_apply` / 引理 `piCongrLeft_apply_apply`

English:
lemma piCongrLeft_apply_apply
  statement: {ι ι' : Type*} (e : ι ≃ ι') {β : ι' -> Type*}
  proof: by
  rw [piCongrLeft]; rw [coe_mk]; rw [Equiv.piCongrLeft_apply_apply]

中文:
引理 piCongrLeft_apply_apply
  结论: {ι ι' : 类型} (e : ι ≃ ι') {β : ι' -> 类型}
  证明: by
  rw [piCongrLeft]; rw [coe_mk]; rw [Equiv.piCongrLeft_apply_apply]

Depends on / 依赖: Equiv.piCongrLeft_apply_apply, coe_mk, piCongrLeft, piCongrLeft_apply_apply
-/
lemma piCongrLeft_apply_apply {ι ι' : Type*} (e : ι ≃ ι') {β : ι' -> Type*}
    [forall i', MeasurableSpace (β i')] (x : (i : ι) -> β (e i)) (i : ι) :
    piCongrLeft (fun i' => β i') e x (e i) = x i := by
  rw [piCongrLeft]; rw [coe_mk]; rw [Equiv.piCongrLeft_apply_apply]

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `arrowProdEquivProdArrow` / `arrowProdEquivProdArrow` 的定义

English:
definition arrowProdEquivProdArrow
  signature: (α β γ : Type*) [MeasurableSpace α] [MeasurableSpace β]
  body: Equiv.arrowProdEquivProdArrow γ _ _
  measurable_toFun := by
    dsimp [Equiv.arrowProdEquivProdArrow]
    fun_prop
  measurable_invFun := by
    dsimp [Equiv.arrowProdEquivProdArrow]
    fun_prop

中文:
定义 arrowProdEquivProdArrow
  签名: (α β γ : 类型) [可测空间 α] [可测空间 β]
  定义体: Equiv.arrowProdEquivProdArrow γ _ _
  measurable_toFun := by
    dsimp [Equiv.arrowProdEquivProdArrow]
    fun_prop
  measurable_invFun := by
    dsimp [Equiv.arrowProdEquivProdArrow]
    fun_prop

Depends on / 依赖: Equiv.arrowProdEquivProdArrow, arrowProdEquivProdArrow
-/
def arrowProdEquivProdArrow (α β γ : Type*) [MeasurableSpace α] [MeasurableSpace β] :
    (γ -> α × β) ≃ᵐ (γ -> α) × (γ -> β) where
  __ := Equiv.arrowProdEquivProdArrow γ _ _
  measurable_toFun := by
    dsimp [Equiv.arrowProdEquivProdArrow]
    fun_prop
  measurable_invFun := by
    dsimp [Equiv.arrowProdEquivProdArrow]
    fun_prop

/--
Definition of `arrowCongr'` / `arrowCongr'` 的定义

English:
definition arrowCongr'
  signature: {α₁ β₁ α₂ β₂ : Type*} [MeasurableSpace β₁] [MeasurableSpace β₂]
  body: Equiv.arrowCongr' hα hβ
  measurable_toFun _ h := by
exact MeasurableSet.preimage h
      measurable_pi_iff.mpr fun _ => hβ.measurable.comp (measurable_pi_apply _)
  measurable_invFun _ h := by
exact MeasurableSet.preimage h
      measurable_pi_iff.mpr fun _ => hβ.symm.measurable.comp (measurable_pi_apply _)

中文:
定义 arrowCongr'
  签名: {α₁ β₁ α₂ β₂ : 类型} [可测空间 β₁] [可测空间 β₂]
  定义体: Equiv.arrowCongr' hα hβ
  measurable_toFun _ h := by
exact MeasurableSet.preimage h
      measurable_pi_iff.mpr fun _ => hβ.measurable.comp (measurable_pi_apply _)
  measurable_invFun _ h := by
exact MeasurableSet.preimage h
      measurable_pi_iff.mpr fun _ => hβ.symm.measurable.comp (measurable_pi_apply _)

Depends on / 依赖: Equiv.arrowCongr, arrowCongr
-/
def arrowCongr' {α₁ β₁ α₂ β₂ : Type*} [MeasurableSpace β₁] [MeasurableSpace β₂]
    (hα : α₁ ≃ α₂) (hβ : β₁ ≃ᵐ β₂) :
    (α₁ -> β₁) ≃ᵐ (α₂ -> β₂) where
  __ := Equiv.arrowCongr' hα hβ
  measurable_toFun _ h := by
exact MeasurableSet.preimage h
      measurable_pi_iff.mpr fun _ => hβ.measurable.comp (measurable_pi_apply _)
  measurable_invFun _ h := by
exact MeasurableSet.preimage h
      measurable_pi_iff.mpr fun _ => hβ.symm.measurable.comp (measurable_pi_apply _)

/-- Pi-types are measurably equivalent to iterated products. -/
@[simps! -fullyApplied]
/--
Definition of `piMeasurableEquivTProd` / `piMeasurableEquivTProd` 的定义

English:
definition piMeasurableEquivTProd
  signature: [DecidableEq δ'] {l : List δ'} (hnd : l.Nodup) (h : forall i, i in l)
  body: List.TProd.piEquivTProd hnd h
  measurable_toFun := measurable_tProd_mk l
  measurable_invFun := measurable_tProd_elim' h

中文:
定义 piMeasurableEquivTProd
  签名: [DecidableEq δ'] {l : 列表 δ'} (hnd : l.Nodup) (h : 对任意 i, i in l)
  定义体: List.TProd.piEquivTProd hnd h
  measurable_toFun := measurable_tProd_mk l
  measurable_invFun := measurable_tProd_elim' h

Depends on / 依赖: List.TProd.piEquivTProd, piEquivTProd
-/
def piMeasurableEquivTProd [DecidableEq δ'] {l : List δ'} (hnd : l.Nodup) (h : forall i, i in l) :
    (forall i, π i) ≃ᵐ List.TProd π l where
  toEquiv := List.TProd.piEquivTProd hnd h
  measurable_toFun := measurable_tProd_mk l
  measurable_invFun := measurable_tProd_elim' h

variable (π) in
/-- The measurable equivalence `(∀ i, π i) ≃ᵐ π ⋆` when the domain of `π` only contains `⋆` -/
@[simps! -fullyApplied]
/--
Definition of `piUnique` / `piUnique` 的定义

English:
definition piUnique
  signature: [Unique δ']
  body: Equiv.piUnique π

中文:
定义 piUnique
  签名: [唯一 δ']
  定义体: Equiv.piUnique π

Depends on / 依赖: Equiv.piUnique, piUnique
-/
def piUnique [Unique δ'] : (forall i, π i) ≃ᵐ π default where
  toEquiv := Equiv.piUnique π

/-- If `α` has a unique term, then the type of function `α → β` is measurably equivalent to `β`. -/
@[simps! -fullyApplied]
/--
Definition of `funUnique` / `funUnique` 的定义

English:
definition funUnique
  signature: (α β : Type*) [Unique α] [MeasurableSpace β]
  body: MeasurableEquiv.piUnique _

中文:
定义 funUnique
  签名: (α β : 类型) [唯一 α] [可测空间 β]
  定义体: MeasurableEquiv.piUnique _

Depends on / 依赖: MeasurableEquiv, MeasurableEquiv.piUnique, piUnique
-/
def funUnique (α β : Type*) [Unique α] [MeasurableSpace β] : (α -> β) ≃ᵐ β :=
  MeasurableEquiv.piUnique _

/-- The space `Π i : Fin 2, α i` is measurably equivalent to `α 0 × α 1`. -/
@[simps! -fullyApplied]
/--
Definition of `piFinTwo` / `piFinTwo` 的定义

English:
definition piFinTwo
  signature: (α : Fin 2 -> Type*) [forall i, MeasurableSpace (α i)]
  body: piFinTwoEquiv α
measurable_invFun := measurable_pi_iff.2 Fin.forall_fin_two.2 ⟨measurable_fst, measurable_snd⟩

中文:
定义 piFinTwo
  签名: (α : 有限集 2 -> 类型) [对任意 i, 可测空间 (α i)]
  定义体: piFinTwoEquiv α
measurable_invFun := measurable_pi_iff.2 Fin.forall_fin_two.2 ⟨measurable_fst, measurable_snd⟩

Depends on / 依赖: piFinTwoEquiv
-/
def piFinTwo (α : Fin 2 -> Type*) [forall i, MeasurableSpace (α i)] : (forall i, α i) ≃ᵐ α 0 × α 1 where
  toEquiv := piFinTwoEquiv α
measurable_invFun := measurable_pi_iff.2 Fin.forall_fin_two.2 ⟨measurable_fst, measurable_snd⟩

/-- The space `Fin 2 → α` is measurably equivalent to `α × α`. -/
@[simps! -fullyApplied]
/--
Definition of `finTwoArrow` / `finTwoArrow` 的定义

English:
definition finTwoArrow
  signature: : (Fin 2 -> α) ≃ᵐ α × α
  body: piFinTwo fun _ => α

中文:
定义 finTwoArrow
  签名: : (有限集 2 -> α) ≃ᵐ α × α
  定义体: piFinTwo fun _ => α

Depends on / 依赖: piFinTwo
-/
def finTwoArrow : (Fin 2 -> α) ≃ᵐ α × α :=
  piFinTwo fun _ => α

/-- Measurable equivalence between `Π j : Fin (n + 1), α j` and
`α i × Π j : Fin n, α (Fin.succAbove i j)`.

Measurable version of `Fin.insertNthEquiv`. -/
@[simps! -fullyApplied]
/--
Definition of `piFinSuccAbove` / `piFinSuccAbove` 的定义

English:
definition piFinSuccAbove
  signature: {n : Nat} (α : Fin (n + 1) -> Type*) [forall i, MeasurableSpace (α i)]
  body: (Fin.insertNthEquiv α i).symm
measurable_toFun := (measurable_pi_apply i).prodMk measurable_pi_iff.2 fun _ =>
    measurable_pi_apply _
measurable_invFun := measurable_pi_iff.2 i.forall_iff_succAbove.2
    ⟨by simp [measurable_fst], fun j => by simpa using! (measurable_pi_apply _).comp measurable_snd⟩

中文:
定义 piFinSuccAbove
  签名: {n : 自然数} (α : 有限集 (n + 1) -> 类型) [对任意 i, 可测空间 (α i)]
  定义体: (Fin.insertNthEquiv α i).symm
measurable_toFun := (measurable_pi_apply i).prodMk measurable_pi_iff.2 fun _ =>
    measurable_pi_apply _
measurable_invFun := measurable_pi_iff.2 i.forall_iff_succAbove.2
    ⟨by simp [measurable_fst], fun j => by simpa using! (measurable_pi_apply _).comp measurable_snd⟩

Depends on / 依赖: Fin.insertNthEquiv, insertNthEquiv
-/
def piFinSuccAbove {n : Nat} (α : Fin (n + 1) -> Type*) [forall i, MeasurableSpace (α i)]
    (i : Fin (n + 1)) : (forall j, α j) ≃ᵐ α i × forall j, α (i.succAbove j) where
  toEquiv := (Fin.insertNthEquiv α i).symm
measurable_toFun := (measurable_pi_apply i).prodMk measurable_pi_iff.2 fun _ =>
    measurable_pi_apply _
measurable_invFun := measurable_pi_iff.2 i.forall_iff_succAbove.2
    ⟨by simp [measurable_fst], fun j => by simpa using! (measurable_pi_apply _).comp measurable_snd⟩

variable (π)

/-- Measurable equivalence between (dependent) functions on a type and pairs of functions on
`{i // p i}` and `{i // ¬p i}`. See also `Equiv.piEquivPiSubtypeProd`. -/
@[simps! -fullyApplied]
/--
Definition of `piEquivPiSubtypeProd` / `piEquivPiSubtypeProd` 的定义

English:
definition piEquivPiSubtypeProd
  signature: (p : δ' -> Prop) [DecidablePred p]
  body: .piEquivPiSubtypeProd p π

中文:
定义 piEquivPiSubtypeProd
  签名: (p : δ' -> 命题) [DecidablePred p]
  定义体: .piEquivPiSubtypeProd p π

Depends on / 依赖: piEquivPiSubtypeProd
-/
def piEquivPiSubtypeProd (p : δ' -> Prop) [DecidablePred p] :
    (forall i, π i) ≃ᵐ (forall i : Subtype p, π i) × forall i : { i // ¬p i }, π i where
  toEquiv := .piEquivPiSubtypeProd p π

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `sumPiEquivProdPi` / `sumPiEquivProdPi` 的定义

English:
definition sumPiEquivProdPi
  signature: (α : δ oplus δ' -> Type*) [forall i, MeasurableSpace (α i)]
  body: Equiv.sumPiEquivProdPi α
  measurable_toFun := by eta_expand; dsimp; measurability
  measurable_invFun := by
    rw [measurable_pi_iff]; rintro (i | i)
    · exact measurable_pi_iff.1 measurable_fst _
    · exact measurable_pi_iff.1 measurable_snd _

中文:
定义 sumPiEquivProdPi
  签名: (α : δ oplus δ' -> 类型) [对任意 i, 可测空间 (α i)]
  定义体: Equiv.sumPiEquivProdPi α
  measurable_toFun := by eta_expand; dsimp; measurability
  measurable_invFun := by
    rw [measurable_pi_iff]; rintro (i | i)
    · exact measurable_pi_iff.1 measurable_fst _
    · exact measurable_pi_iff.1 measurable_snd _

Depends on / 依赖: Equiv.sumPiEquivProdPi, sumPiEquivProdPi
-/
def sumPiEquivProdPi (α : δ oplus δ' -> Type*) [forall i, MeasurableSpace (α i)] :
    (forall i, α i) ≃ᵐ (forall i, α (.inl i)) × forall i', α (.inr i') where
  __ := Equiv.sumPiEquivProdPi α
  measurable_toFun := by eta_expand; dsimp; measurability
  measurable_invFun := by
    rw [measurable_pi_iff]; rintro (i | i)
    · exact measurable_pi_iff.1 measurable_fst _
    · exact measurable_pi_iff.1 measurable_snd _

/--
theorem `coe_sumPiEquivProdPi` / 定理 `coe_sumPiEquivProdPi`

English:
theorem coe_sumPiEquivProdPi
  given: (α : δ oplus δ' -> Type*) [forall i, MeasurableSpace (α i)]
  proof: by rfl

中文:
定理 coe_sumPiEquivProdPi
  条件: (α : δ oplus δ' -> 类型) [对任意 i, 可测空间 (α i)]
  证明: by rfl
-/
theorem coe_sumPiEquivProdPi (α : δ oplus δ' -> Type*) [forall i, MeasurableSpace (α i)] :
    ⇑(MeasurableEquiv.sumPiEquivProdPi α) = Equiv.sumPiEquivProdPi α := by rfl

/--
theorem `coe_sumPiEquivProdPi_symm` / 定理 `coe_sumPiEquivProdPi_symm`

English:
theorem coe_sumPiEquivProdPi_symm
  given: (α : δ oplus δ' -> Type*) [forall i, MeasurableSpace (α i)]
  proof: by rfl

中文:
定理 coe_sumPiEquivProdPi_symm
  条件: (α : δ oplus δ' -> 类型) [对任意 i, 可测空间 (α i)]
  证明: by rfl
-/
theorem coe_sumPiEquivProdPi_symm (α : δ oplus δ' -> Type*) [forall i, MeasurableSpace (α i)] :
    ⇑(MeasurableEquiv.sumPiEquivProdPi α).symm = (Equiv.sumPiEquivProdPi α).symm := by rfl

/--
Definition of `piOptionEquivProd` / `piOptionEquivProd` 的定义

English:
definition piOptionEquivProd
  signature: {δ : Type*} (α : Option δ -> Type*) [forall i, MeasurableSpace (α i)]
  body: let e : Option δ ≃ δ oplus Unit := Equiv.optionEquivSumPUnit δ
  let em1 : ((i : δ oplus Unit) -> α (e.symm i)) ≃ᵐ ((a : Option δ) -> α a) :=
    MeasurableEquiv.piCongrLeft α e.symm
  let em2 : ((i : δ oplus Unit) -> α (e.symm i)) ≃ᵐ ((i : δ) -> α (e.symm (Sum.inl i)))
      × ((i' : Unit) -> α (e.symm (Sum.inr i'))) :=
    MeasurableEquiv.sumPiEquivProdPi (fun i => α (e.symm i))
  let em3 : ((i : δ) -> α (e.symm (Sum.inl i))) × ((i' : Unit) -> α (e.symm (Sum.inr i')))
      ≃ᵐ ((i : δ) -> α (some i)) × α none :=
    MeasurableEquiv.prodCongr (MeasurableEquiv.refl ((i : δ) -> α (e.symm (Sum.inl i))))
      (MeasurableEquiv.piUnique fun i => α (e.symm (Sum.inr i)))
em1.symm.trans em2.trans em3

中文:
定义 piOptionEquivProd
  签名: {δ : 类型} (α : 选项类型 δ -> 类型) [对任意 i, 可测空间 (α i)]
  定义体: let e : Option δ ≃ δ oplus Unit := Equiv.optionEquivSumPUnit δ
  let em1 : ((i : δ oplus Unit) -> α (e.symm i)) ≃ᵐ ((a : Option δ) -> α a) :=
    MeasurableEquiv.piCongrLeft α e.symm
  let em2 : ((i : δ oplus Unit) -> α (e.symm i)) ≃ᵐ ((i : δ) -> α (e.symm (Sum.inl i)))
      × ((i' : Unit) -> α (e.symm (Sum.inr i'))) :=
    MeasurableEquiv.sumPiEquivProdPi (fun i => α (e.symm i))
  let em3 : ((i : δ) -> α (e.symm (Sum.inl i))) × ((i' : Unit) -> α (e.symm (Sum.inr i')))
      ≃ᵐ ((i : δ) -> α (some i)) × α none :=
    MeasurableEquiv.prodCongr (MeasurableEquiv.refl ((i : δ) -> α (e.symm (Sum.inl i))))
      (MeasurableEquiv.piUnique fun i => α (e.symm (Sum.inr i)))
em1.symm.trans em2.trans em3

Depends on / 依赖: Equiv.optionEquivSumPUnit, Measur, MeasurableEquiv, MeasurableEquiv.piCongrLeft, MeasurableEquiv.sumPiEquivProdPi, Sum.inl, Sum.inr, e.symm, optionEquivSumPUnit, piCongrLeft, sumPiEquivProdPi
-/
def piOptionEquivProd {δ : Type*} (α : Option δ -> Type*) [forall i, MeasurableSpace (α i)] :
    (forall i, α i) ≃ᵐ (forall (i : δ), α i) × α none :=
  let e : Option δ ≃ δ oplus Unit := Equiv.optionEquivSumPUnit δ
  let em1 : ((i : δ oplus Unit) -> α (e.symm i)) ≃ᵐ ((a : Option δ) -> α a) :=
    MeasurableEquiv.piCongrLeft α e.symm
  let em2 : ((i : δ oplus Unit) -> α (e.symm i)) ≃ᵐ ((i : δ) -> α (e.symm (Sum.inl i)))
      × ((i' : Unit) -> α (e.symm (Sum.inr i'))) :=
    MeasurableEquiv.sumPiEquivProdPi (fun i => α (e.symm i))
  let em3 : ((i : δ) -> α (e.symm (Sum.inl i))) × ((i' : Unit) -> α (e.symm (Sum.inr i')))
      ≃ᵐ ((i : δ) -> α (some i)) × α none :=
    MeasurableEquiv.prodCongr (MeasurableEquiv.refl ((i : δ) -> α (e.symm (Sum.inl i))))
      (MeasurableEquiv.piUnique fun i => α (e.symm (Sum.inr i)))
em1.symm.trans em2.trans em3

/--
Definition of `piFinsetUnion` / `piFinsetUnion` 的定义

English:
definition piFinsetUnion
  signature: [DecidableEq δ'] {s t : Finset δ'} (h : Disjoint s t)
  body: letI e := Finset.union s t h
.symm.trans MeasurableEquiv.sumPiEquivProdPi (fun b => π (e b))
    .piCongrLeft (fun i : ↥(s union t) => π i) e

中文:
定义 piFinsetUnion
  签名: [DecidableEq δ'] {s t : 有限集 δ'} (h : Disjoint s t)
  定义体: letI e := Finset.union s t h
.symm.trans MeasurableEquiv.sumPiEquivProdPi (fun b => π (e b))
    .piCongrLeft (fun i : ↥(s union t) => π i) e

Depends on / 依赖: Finset, Finset.union, MeasurableEquiv, MeasurableEquiv.sumPiEquivProdPi, piCongrLeft, sumPiEquivProdPi, symm.trans
-/
def piFinsetUnion [DecidableEq δ'] {s t : Finset δ'} (h : Disjoint s t) :
    ((forall i : s, π i) × forall i : t, π i) ≃ᵐ forall i : (s union t : Finset δ'), π i :=
  letI e := Finset.union s t h
.symm.trans MeasurableEquiv.sumPiEquivProdPi (fun b => π (e b))
    .piCongrLeft (fun i : ↥(s union t) => π i) e

/--
Definition of `sumCompl` / `sumCompl` 的定义

English:
definition sumCompl
  signature: {s : Set α} [DecidablePred (· in s)] (hs : MeasurableSet s)
  body: .sumCompl (· in s)
  measurable_toFun := measurable_subtype_coe.sumElim measurable_subtype_coe
  measurable_invFun := Measurable.dite measurable_inl measurable_inr hs

中文:
定义 sumCompl
  签名: {s : 集合 α} [DecidablePred (· in s)] (hs : 可测集 s)
  定义体: .sumCompl (· in s)
  measurable_toFun := measurable_subtype_coe.sumElim measurable_subtype_coe
  measurable_invFun := Measurable.dite measurable_inl measurable_inr hs

Depends on / 依赖: Lattice, LinearOrder, LinearOrder.toLattice, sumCompl, toLattice
-/
def sumCompl {s : Set α} [DecidablePred (· in s)] (hs : MeasurableSet s) :
    s oplus (sᶜ : Set α) ≃ᵐ α where
  toEquiv := .sumCompl (· in s)
  measurable_toFun := measurable_subtype_coe.sumElim measurable_subtype_coe
  measurable_invFun := Measurable.dite measurable_inl measurable_inr hs

/-- Convert a measurable involutive function `f` to a measurable permutation with
`toFun = invFun = f`. See also `Function.Involutive.toPerm`. -/
@[simps toEquiv]
/--
Definition of `ofInvolutive` / `ofInvolutive` 的定义

English:
definition ofInvolutive
  signature: (f : α -> α) (hf : Involutive f) (hf' : Measurable f)
  body: hf.toPerm

中文:
定义 ofInvolutive
  签名: (f : α -> α) (hf : 对合 f) (hf' : 可测 f)
  定义体: hf.toPerm

Depends on / 依赖: hf.toPerm, toPerm
-/
def ofInvolutive (f : α -> α) (hf : Involutive f) (hf' : Measurable f) : α ≃ᵐ α where
  toEquiv := hf.toPerm

/--
theorem `ofInvolutive_apply` / 定理 `ofInvolutive_apply`

English:
theorem ofInvolutive_apply
  given: (f : α -> α) (hf : Involutive f) (hf' : Measurable f) (a : α)
  proof: rfl

中文:
定理 ofInvolutive_apply
  条件: (f : α -> α) (hf : 对合 f) (hf' : 可测 f) (a : α)
  证明: rfl
-/
@[simp] theorem ofInvolutive_apply (f : α -> α) (hf : Involutive f) (hf' : Measurable f) (a : α) :
    ofInvolutive f hf hf' a = f a := rfl

/--
theorem `ofInvolutive_symm` / 定理 `ofInvolutive_symm`

English:
theorem ofInvolutive_symm
  given: (f : α -> α) (hf : Involutive f) (hf' : Measurable f)
  proof: rfl

中文:
定理 ofInvolutive_symm
  条件: (f : α -> α) (hf : 对合 f) (hf' : 可测 f)
  证明: rfl
-/
@[simp] theorem ofInvolutive_symm (f : α -> α) (hf : Involutive f) (hf' : Measurable f) :
    (ofInvolutive f hf hf').symm = ofInvolutive f hf hf' := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- `Set.ofPred` as a `MeasurableEquiv`. -/
@[simps]
/--
Definition of `setOfPred` / `setOfPred` 的定义

English:
definition setOfPred
  signature: {α : Type*}
  body: {a | p a}
  invFun s a := a in s

@[deprecated (since := "2026-07-09")]
protected alias setOf := MeasurableEquiv.setOfPred

@[deprecated (since := "2026-07-09")]
alias setOf_apply := MeasurableEquiv.setOfPred_apply

@[deprecated (since := "2026-07-09")]
alias setOf_symm_apply := MeasurableEquiv.setOfPred_symm_apply

中文:
定义 setOfPred
  签名: {α : 类型}
  定义体: {a | p a}
  invFun s a := a in s

@[deprecated (since := "2026-07-09")]
protected alias setOf := MeasurableEquiv.setOfPred

@[deprecated (since := "2026-07-09")]
alias setOf_apply := MeasurableEquiv.setOfPred_apply

@[deprecated (since := "2026-07-09")]
alias setOf_symm_apply := MeasurableEquiv.setOfPred_symm_apply
-/
protected def setOfPred {α : Type*} : (α -> Prop) ≃ᵐ Set α where
  toFun p := {a | p a}
  invFun s a := a in s

@[deprecated (since := "2026-07-09")]
protected alias setOf := MeasurableEquiv.setOfPred

@[deprecated (since := "2026-07-09")]
alias setOf_apply := MeasurableEquiv.setOfPred_apply

@[deprecated (since := "2026-07-09")]
alias setOf_symm_apply := MeasurableEquiv.setOfPred_symm_apply

/--
lemma `coe_setOfPred` / 引理 `coe_setOfPred`

English:
lemma coe_setOfPred
  given: {α : Type*}
  proof: rfl

@[deprecated (since := "2026-07-09")]
alias coe_setOf := coe_setOfPred

中文:
引理 coe_setOfPred
  条件: {α : 类型}
  证明: rfl

@[deprecated (since := "2026-07-09")]
alias coe_setOf := coe_setOfPred
-/
@[simp, norm_cast] lemma coe_setOfPred {α : Type*} :
    ⇑MeasurableEquiv.setOfPred = Set.ofPred (α := α) := rfl

@[deprecated (since := "2026-07-09")]
alias coe_setOf := coe_setOfPred

end MeasurableEquiv

namespace MeasurableEmbedding

variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] {f : α -> β} {g : β -> α}

/--
theorem `comap_eq` / 定理 `comap_eq`

English:
theorem comap_eq
  given: (hf : MeasurableEmbedding f)
  statement: MeasurableSpace.comap f ‹_› = ‹_›
  proof: hf.measurable.comap_le.antisymm fun _s h =>
    ⟨_, hf.measurableSet_image' h, hf.injective.preimage_image _⟩

中文:
定理 comap_eq
  条件: (hf : 可测嵌入 f)
  结论: 可测空间.comap f ‹_› = ‹_›
  证明: hf.measurable.comap_le.antisymm fun _s h =>
    ⟨_, hf.measurableSet_image' h, hf.injective.preimage_image _⟩
-/
@[simp] theorem comap_eq (hf : MeasurableEmbedding f) : MeasurableSpace.comap f ‹_› = ‹_› :=
  hf.measurable.comap_le.antisymm fun _s h =>
    ⟨_, hf.measurableSet_image' h, hf.injective.preimage_image _⟩

/--
theorem `iff_comap_eq` / 定理 `iff_comap_eq`

English:
theorem iff_comap_eq
  proof: ⟨fun hf => ⟨hf.injective, hf.comap_eq, hf.measurableSet_range⟩, fun hf =>
    { injective := hf.1
      measurable := by rw [← hf.2.1]; exact comap_measurable f
      measurableSet_image' := by
        rw [← hf.2.1]
        rintro _ ⟨s, hs, rfl⟩
        simpa only [image_preimage_eq_inter_range] using hs.inter hf.2.2 }⟩

中文:
定理 iff_comap_eq
  证明: ⟨fun hf => ⟨hf.injective, hf.comap_eq, hf.measurableSet_range⟩, fun hf =>
    { injective := hf.1
      measurable := by rw [← hf.2.1]; exact comap_measurable f
      measurableSet_image' := by
        rw [← hf.2.1]
        rintro _ ⟨s, hs, rfl⟩
        simpa only [image_preimage_eq_inter_range] using hs.inter hf.2.2 }⟩

Depends on / 依赖: comap_eq, comap_measurable, hf.comap_eq, hf.injective, hf.measurableSet_range, hs.inter, image_preimage_eq_inter_range, injective, measurable, measurableSet_image, measurableSet_range
-/
theorem iff_comap_eq :
    MeasurableEmbedding f ↔
      Injective f ∧ MeasurableSpace.comap f ‹_› = ‹_› ∧ MeasurableSet (range f) :=
  ⟨fun hf => ⟨hf.injective, hf.comap_eq, hf.measurableSet_range⟩, fun hf =>
    { injective := hf.1
      measurable := by rw [← hf.2.1]; exact comap_measurable f
      measurableSet_image' := by
        rw [← hf.2.1]
        rintro _ ⟨s, hs, rfl⟩
        simpa only [image_preimage_eq_inter_range] using hs.inter hf.2.2 }⟩

/--
Definition of `equivImage` / `equivImage` 的定义

English:
definition equivImage
  signature: (s : Set α) (hf : MeasurableEmbedding f)
  body: Equiv.Set.image f s hf.injective
  measurable_toFun := (hf.measurable.comp measurable_id.subtype_val).subtype_mk
  measurable_invFun := by
    rintro t ⟨u, hu, rfl⟩
    simpa [preimage_preimage, Set.image_symm_preimage hf.injective]
      using measurable_subtype_coe (hf.measurableSet_image' hu)

中文:
定义 equivImage
  签名: (s : 集合 α) (hf : 可测嵌入 f)
  定义体: Equiv.Set.image f s hf.injective
  measurable_toFun := (hf.measurable.comp measurable_id.subtype_val).subtype_mk
  measurable_invFun := by
    rintro t ⟨u, hu, rfl⟩
    simpa [preimage_preimage, Set.image_symm_preimage hf.injective]
      using measurable_subtype_coe (hf.measurableSet_image' hu)

Depends on / 依赖: Equiv.Set.image, hf.injective, injective
-/
noncomputable def equivImage (s : Set α) (hf : MeasurableEmbedding f) : s ≃ᵐ f '' s where
  toEquiv := Equiv.Set.image f s hf.injective
  measurable_toFun := (hf.measurable.comp measurable_id.subtype_val).subtype_mk
  measurable_invFun := by
    rintro t ⟨u, hu, rfl⟩
    simpa [preimage_preimage, Set.image_symm_preimage hf.injective]
      using measurable_subtype_coe (hf.measurableSet_image' hu)

/--
Definition of `equivRange` / `equivRange` 的定义

English:
definition equivRange
  signature: (hf : MeasurableEmbedding f)
  body: (MeasurableEquiv.Set.univ _).symm.trans
(hf.equivImage univ).trans MeasurableEquiv.cast (by rw [image_univ]) (by rw [image_univ])

中文:
定义 equivRange
  签名: (hf : 可测嵌入 f)
  定义体: (MeasurableEquiv.Set.univ _).symm.trans
(hf.equivImage univ).trans MeasurableEquiv.cast (by rw [image_univ]) (by rw [image_univ])

Depends on / 依赖: DistribLattice, LinearOrder, MeasurableEquiv, MeasurableEquiv.Set.univ, MeasurableEquiv.cast, equivImage, hf.equivImage, image_univ, symm.trans
-/
noncomputable def equivRange (hf : MeasurableEmbedding f) : α ≃ᵐ range f :=
(MeasurableEquiv.Set.univ _).symm.trans
(hf.equivImage univ).trans MeasurableEquiv.cast (by rw [image_univ]) (by rw [image_univ])

/--
theorem `of_measurable_inverse_on_range` / 定理 `of_measurable_inverse_on_range`

English:
theorem of_measurable_inverse_on_range
  statement: {g : range f -> α} (hf₁ : Measurable f)
  proof: by
  set e : α ≃ᵐ range f :=
    ⟨⟨rangeFactorization f, g, H, H.rightInverse_of_surjective rangeFactorization_surjective⟩,
      hf₁.subtype_mk, hg⟩
  exact (MeasurableEmbedding.subtype_coe hf₂).comp e.measurableEmbedding

中文:
定理 of_measurable_inverse_on_range
  结论: {g : range f -> α} (hf₁ : 可测 f)
  证明: by
  set e : α ≃ᵐ range f :=
    ⟨⟨rangeFactorization f, g, H, H.rightInverse_of_surjective rangeFactorization_surjective⟩,
      hf₁.subtype_mk, hg⟩
  exact (MeasurableEmbedding.subtype_coe hf₂).comp e.measurableEmbedding

Depends on / 依赖: H.rightInverse_of_surjective, MeasurableEmbedding, MeasurableEmbedding.subtype_coe, e.measurableEmbedding, measurableEmbedding, rangeFactorization, rangeFactorization_surjective, rightInverse_of_surjective, subtype_coe, subtype_mk
-/
theorem of_measurable_inverse_on_range {g : range f -> α} (hf₁ : Measurable f)
    (hf₂ : MeasurableSet (range f)) (hg : Measurable g) (H : LeftInverse g (rangeFactorization f)) :
    MeasurableEmbedding f := by
  set e : α ≃ᵐ range f :=
    ⟨⟨rangeFactorization f, g, H, H.rightInverse_of_surjective rangeFactorization_surjective⟩,
      hf₁.subtype_mk, hg⟩
  exact (MeasurableEmbedding.subtype_coe hf₂).comp e.measurableEmbedding

/--
theorem `of_measurable_inverse` / 定理 `of_measurable_inverse`

English:
theorem of_measurable_inverse
  statement: (hf₁ : Measurable f) (hf₂ : MeasurableSet (range f))
  proof: of_measurable_inverse_on_range hf₁ hf₂ (hg.comp measurable_subtype_coe) H

中文:
定理 of_measurable_inverse
  结论: (hf₁ : 可测 f) (hf₂ : 可测集 (range f))
  证明: of_measurable_inverse_on_range hf₁ hf₂ (hg.comp measurable_subtype_coe) H

Depends on / 依赖: hg.comp, measurable_subtype_coe, of_measurable_inverse_on_range
-/
theorem of_measurable_inverse (hf₁ : Measurable f) (hf₂ : MeasurableSet (range f))
    (hg : Measurable g) (H : LeftInverse g f) : MeasurableEmbedding f :=
  of_measurable_inverse_on_range hf₁ hf₂ (hg.comp measurable_subtype_coe) H

/--
Definition of `schroederBernstein` / `schroederBernstein` 的定义

English:
definition schroederBernstein
  signature: {f : α -> β} {g : β -> α} (hf : MeasurableEmbedding f)
  body: by
  let F : Set α -> Set α := fun A => (g '' (f '' A)ᶜ)ᶜ
  -- We follow the proof of the usual SB theorem in mathlib,
  -- the crux of which is finding a fixed point of this F.
  -- However, we must find this fixed point manually instead of invoking Knaster-Tarski
  -- in order to make sure it is measurable.
  suffices Σ' A : Set α, MeasurableSet A ∧ F A = A by
    classical
    rcases this with ⟨A, Ameas, Afp⟩
    let B := f '' A
    have Bmeas : MeasurableSet B := hf.measurableSet_image' Ameas
    refine (MeasurableEquiv.sumCompl Ameas).symm.trans
      (MeasurableEquiv.trans ?_ (MeasurableEquiv.sumCompl Bmeas))
    apply MeasurableEquiv.sumCongr (hf.equivImage _)
    have : Aᶜ = g '' Bᶜ := by
      apply compl_injective
      rw [← Afp]
      simp [F, B]
    rw [this]
    exact (hg.equivImage _).symm
  have Fmono : forall {A B}, A subseteq B -> F A subseteq F B := fun h =>
compl_subset_compl.mpr Set.image_mono compl_subset_compl.mpr Set.image_mono h
  let X : Nat -> Set α := fun n => F^[n] univ
  refine ⟨iInter X, ?_, ?_⟩
  · refine MeasurableSet.iInter fun n => ?_
    induction n with
    | zero => exact MeasurableSet.univ
    | succ n ih =>
      rw [Function.iterate_succ']; rw [Function.comp_apply]
      exact (hg.measurableSet_image' (hf.measurableSet_image' ih).compl).compl
  apply subset_antisymm
  · apply subset_iInter
    intro n
    cases n
    · exact subset_univ _
    rw [Function.iterate_succ']; rw [Function.comp_apply]
    exact Fmono (iInter_subset _ _)
  rintro x hx ⟨y, hy, rfl⟩
  rw [mem_iInter] at hx
  apply hy
  rw [hf.injective.injOn.image_iInter_eq]
  rw [mem_iInter]
  intro n
  specialize hx n.succ
  rw [Function.iterate_succ']; rw [Function.comp_apply] at hx
  by_contra h
  apply hx
  exact ⟨y, h, rfl⟩

中文:
定义 schroederBernstein
  签名: {f : α -> β} {g : β -> α} (hf : 可测嵌入 f)
  定义体: by
  let F : Set α -> Set α := fun A => (g '' (f '' A)ᶜ)ᶜ
  -- We follow the proof of the usual SB theorem in mathlib,
  -- the crux of which is finding a fixed point of this F.
  -- However, we must find this fixed point manually instead of invoking Knaster-Tarski
  -- in order to make sure it is measurable.
  suffices Σ' A : Set α, MeasurableSet A ∧ F A = A by
    classical
    rcases this with ⟨A, Ameas, Afp⟩
    let B := f '' A
    have Bmeas : MeasurableSet B := hf.measurableSet_image' Ameas
    refine (MeasurableEquiv.sumCompl Ameas).symm.trans
      (MeasurableEquiv.trans ?_ (MeasurableEquiv.sumCompl Bmeas))
    apply MeasurableEquiv.sumCongr (hf.equivImage _)
    have : Aᶜ = g '' Bᶜ := by
      apply compl_injective
      rw [← Afp]
      simp [F, B]
    rw [this]
    exact (hg.equivImage _).symm
  have Fmono : forall {A B}, A subseteq B -> F A subseteq F B := fun h =>
compl_subset_compl.mpr Set.image_mono compl_subset_compl.mpr Set.image_mono h
  let X : Nat -> Set α := fun n => F^[n] univ
  refine ⟨iInter X, ?_, ?_⟩
  · refine MeasurableSet.iInter fun n => ?_
    induction n with
    | zero => exact MeasurableSet.univ
    | succ n ih =>
      rw [Function.iterate_succ']; rw [Function.comp_apply]
      exact (hg.measurableSet_image' (hf.measurableSet_image' ih).compl).compl
  apply subset_antisymm
  · apply subset_iInter
    intro n
    cases n
    · exact subset_univ _
    rw [Function.iterate_succ']; rw [Function.comp_apply]
    exact Fmono (iInter_subset _ _)
  rintro x hx ⟨y, hy, rfl⟩
  rw [mem_iInter] at hx
  apply hy
  rw [hf.injective.injOn.image_iInter_eq]
  rw [mem_iInter]
  intro n
  specialize hx n.succ
  rw [Function.iterate_succ']; rw [Function.comp_apply] at hx
  by_contra h
  apply hx
  exact ⟨y, h, rfl⟩
-/
noncomputable def schroederBernstein {f : α -> β} {g : β -> α} (hf : MeasurableEmbedding f)
    (hg : MeasurableEmbedding g) : α ≃ᵐ β := by
  let F : Set α -> Set α := fun A => (g '' (f '' A)ᶜ)ᶜ
  -- We follow the proof of the usual SB theorem in mathlib,
  -- the crux of which is finding a fixed point of this F.
  -- However, we must find this fixed point manually instead of invoking Knaster-Tarski
  -- in order to make sure it is measurable.
  suffices Σ' A : Set α, MeasurableSet A ∧ F A = A by
    classical
    rcases this with ⟨A, Ameas, Afp⟩
    let B := f '' A
    have Bmeas : MeasurableSet B := hf.measurableSet_image' Ameas
    refine (MeasurableEquiv.sumCompl Ameas).symm.trans
      (MeasurableEquiv.trans ?_ (MeasurableEquiv.sumCompl Bmeas))
    apply MeasurableEquiv.sumCongr (hf.equivImage _)
    have : Aᶜ = g '' Bᶜ := by
      apply compl_injective
      rw [← Afp]
      simp [F, B]
    rw [this]
    exact (hg.equivImage _).symm
  have Fmono : forall {A B}, A subseteq B -> F A subseteq F B := fun h =>
compl_subset_compl.mpr Set.image_mono compl_subset_compl.mpr Set.image_mono h
  let X : Nat -> Set α := fun n => F^[n] univ
  refine ⟨iInter X, ?_, ?_⟩
  · refine MeasurableSet.iInter fun n => ?_
    induction n with
    | zero => exact MeasurableSet.univ
    | succ n ih =>
      rw [Function.iterate_succ']; rw [Function.comp_apply]
      exact (hg.measurableSet_image' (hf.measurableSet_image' ih).compl).compl
  apply subset_antisymm
  · apply subset_iInter
    intro n
    cases n
    · exact subset_univ _
    rw [Function.iterate_succ']; rw [Function.comp_apply]
    exact Fmono (iInter_subset _ _)
  rintro x hx ⟨y, hy, rfl⟩
  rw [mem_iInter] at hx
  apply hy
  rw [hf.injective.injOn.image_iInter_eq]
  rw [mem_iInter]
  intro n
  specialize hx n.succ
  rw [Function.iterate_succ']; rw [Function.comp_apply] at hx
  by_contra h
  apply hx
  exact ⟨y, h, rfl⟩

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `equivRange_apply` / 引理 `equivRange_apply`

English:
lemma equivRange_apply
  given: (hf : MeasurableEmbedding f) (x : α)
  proof: by
  simp [MeasurableEmbedding.equivRange, MeasurableEquiv.cast, MeasurableEquiv.Set.univ,
    MeasurableEmbedding.equivImage]

@[simp]

中文:
引理 equivRange_apply
  条件: (hf : 可测嵌入 f) (x : α)
  证明: by
  simp [MeasurableEmbedding.equivRange, MeasurableEquiv.cast, MeasurableEquiv.Set.univ,
    MeasurableEmbedding.equivImage]

@[simp]

Depends on / 依赖: MeasurableEmbedding, MeasurableEmbedding.equivImage, MeasurableEmbedding.equivRange, MeasurableEquiv, MeasurableEquiv.Set.univ, MeasurableEquiv.cast, equivImage, equivRange
-/
lemma equivRange_apply (hf : MeasurableEmbedding f) (x : α) :
    hf.equivRange x = ⟨f x, mem_range_self x⟩ := by
  simp [MeasurableEmbedding.equivRange, MeasurableEquiv.cast, MeasurableEquiv.Set.univ,
    MeasurableEmbedding.equivImage]

@[simp]
/--
lemma `equivRange_symm_apply_mk` / 引理 `equivRange_symm_apply_mk`

English:
lemma equivRange_symm_apply_mk
  given: (hf : MeasurableEmbedding f) (x : α)
  proof: by
  nth_rw 3 [← hf.equivRange.symm_apply_apply x]
  rw [hf.equivRange_apply]

中文:
引理 equivRange_symm_apply_mk
  条件: (hf : 可测嵌入 f) (x : α)
  证明: by
  nth_rw 3 [← hf.equivRange.symm_apply_apply x]
  rw [hf.equivRange_apply]

Depends on / 依赖: equivRange, equivRange_apply, hf.equivRange.symm_apply_apply, hf.equivRange_apply, nth_rw, symm_apply_apply
-/
lemma equivRange_symm_apply_mk (hf : MeasurableEmbedding f) (x : α) :
    hf.equivRange.symm ⟨f x, mem_range_self x⟩ = x := by
  nth_rw 3 [← hf.equivRange.symm_apply_apply x]
  rw [hf.equivRange_apply]

/-- The left-inverse of a `MeasurableEmbedding` -/
protected noncomputable
/--
Definition of `invFun` / `invFun` 的定义

English:
definition invFun
  signature: [Nonempty α] (hf : MeasurableEmbedding f) (x : β)
  body: open scoped Classical in
  if hx : x in range f then hf.equivRange.symm ⟨x, hx⟩ else (Nonempty.some inferInstance)

@[fun_prop]

中文:
定义 invFun
  签名: [非空 α] (hf : 可测嵌入 f) (x : β)
  定义体: open scoped Classical in
  if hx : x in range f then hf.equivRange.symm ⟨x, hx⟩ else (Nonempty.some inferInstance)

@[fun_prop]

Depends on / 依赖: Classical, Nonempty, Nonempty.some, equivRange, hf.equivRange.symm, scoped
-/
def invFun [Nonempty α] (hf : MeasurableEmbedding f) (x : β) : α :=
  open scoped Classical in
  if hx : x in range f then hf.equivRange.symm ⟨x, hx⟩ else (Nonempty.some inferInstance)

@[fun_prop]
/--
lemma `measurable_invFun` / 引理 `measurable_invFun`

English:
lemma measurable_invFun
  given: [Nonempty α] (hf : MeasurableEmbedding f)
  proof: open scoped Classical in
  Measurable.dite (by fun_prop) measurable_const hf.measurableSet_range

中文:
引理 measurable_invFun
  条件: [非空 α] (hf : 可测嵌入 f)
  证明: open scoped Classical in
  Measurable.dite (by fun_prop) measurable_const hf.measurableSet_range

Depends on / 依赖: Classical, Measurable, Measurable.dite, fun_prop, hf.measurableSet_range, measurableSet_range, measurable_const, scoped
-/
lemma measurable_invFun [Nonempty α] (hf : MeasurableEmbedding f) :
    Measurable (hf.invFun : β -> α) :=
  open scoped Classical in
  Measurable.dite (by fun_prop) measurable_const hf.measurableSet_range

/--
lemma `leftInverse_invFun` / 引理 `leftInverse_invFun`

English:
lemma leftInverse_invFun
  given: [Nonempty α] (hf : MeasurableEmbedding f)
  statement: hf.invFun.LeftInverse f
  proof: by
  intro x
  simp [MeasurableEmbedding.invFun]

中文:
引理 leftInverse_invFun
  条件: [非空 α] (hf : 可测嵌入 f)
  结论: hf.invFun.左逆 f
  证明: by
  intro x
  simp [MeasurableEmbedding.invFun]

Depends on / 依赖: MeasurableEmbedding, MeasurableEmbedding.invFun, invFun
-/
lemma leftInverse_invFun [Nonempty α] (hf : MeasurableEmbedding f) : hf.invFun.LeftInverse f := by
  intro x
  simp [MeasurableEmbedding.invFun]

end MeasurableEmbedding

/--
theorem `MeasurableSpace.comap_compl` / 定理 `MeasurableSpace.comap_compl`

English:
theorem MeasurableSpace.comap_compl
  statement: {m' : MeasurableSpace β} [BooleanAlgebra β]
  proof: by
  rw [← Function.comp_def]; rw [← MeasurableSpace.comap_comp]
  congr
  exact (MeasurableEquiv.ofInvolutive _ compl_involutive h).measurableEmbedding.comap_eq

中文:
定理 可测空间.comap_compl
  结论: {m' : 可测空间 β} [布尔代数 β]
  证明: by
  rw [← Function.comp_def]; rw [← MeasurableSpace.comap_comp]
  congr
  exact (MeasurableEquiv.ofInvolutive _ compl_involutive h).measurableEmbedding.comap_eq

Depends on / 依赖: Function, Function.comp_def, MeasurableEquiv, MeasurableEquiv.ofInvolutive, MeasurableSpace, MeasurableSpace.comap_comp, comap_comp, comap_eq, comp_def, compl_involutive, measurableEmbedding, measurableEmbedding.comap_eq, ofInvolutive
-/
theorem MeasurableSpace.comap_compl {m' : MeasurableSpace β} [BooleanAlgebra β]
    (h : Measurable (compl : β -> β)) (f : α -> β) :
    MeasurableSpace.comap (fun a => (f a)ᶜ) inferInstance =
      MeasurableSpace.comap f inferInstance := by
  rw [← Function.comp_def]; rw [← MeasurableSpace.comap_comp]
  congr
  exact (MeasurableEquiv.ofInvolutive _ compl_involutive h).measurableEmbedding.comap_eq

/--
theorem `MeasurableSpace.comap_not` / 定理 `MeasurableSpace.comap_not`

English:
theorem MeasurableSpace.comap_not
  given: (p : α -> Prop)
  proof: MeasurableSpace.comap_compl (fun _ _ => measurableSet_top) _

中文:
定理 可测空间.comap_not
  条件: (p : α -> 命题)
  证明: MeasurableSpace.comap_compl (fun _ _ => measurableSet_top) _
-/
@[simp] theorem MeasurableSpace.comap_not (p : α -> Prop) :
    MeasurableSpace.comap (fun a => ¬p a) inferInstance = MeasurableSpace.comap p inferInstance :=
  MeasurableSpace.comap_compl (fun _ _ => measurableSet_top) _

section curry

/-! ### Currying as a measurable equivalence -/

namespace MeasurableEquiv

/-- The currying operation `Function.curry` as a measurable equivalence.
See `MeasurableEquiv.curry` for the non-dependent version. -/
@[simps!]
/--
Definition of `piCurry` / `piCurry` 的定义

English:
definition piCurry
  signature: {ι : Type*} {κ : ι -> Type*} (X : (i : ι) -> κ i -> Type*)
  body: Equiv.piCurry X

中文:
定义 piCurry
  签名: {ι : 类型} {κ : ι -> 类型} (X : (i : ι) -> κ i -> 类型)
  定义体: Equiv.piCurry X

Depends on / 依赖: Equiv.piCurry, piCurry
-/
def piCurry {ι : Type*} {κ : ι -> Type*} (X : (i : ι) -> κ i -> Type*)
    [forall i j, MeasurableSpace (X i j)] :
    ((p : (i : ι) × κ i) -> X p.1 p.2) ≃ᵐ ((i : ι) -> (j : κ i) -> X i j) where
  toEquiv := Equiv.piCurry X

/--
lemma `coe_piCurry` / 引理 `coe_piCurry`

English:
lemma coe_piCurry
  statement: {ι : Type*} {κ : ι -> Type*} (X : (i : ι) -> κ i -> Type*)
  proof: rfl

中文:
引理 coe_piCurry
  结论: {ι : 类型} {κ : ι -> 类型} (X : (i : ι) -> κ i -> 类型)
  证明: rfl
-/
lemma coe_piCurry {ι : Type*} {κ : ι -> Type*} (X : (i : ι) -> κ i -> Type*)
    [forall i j, MeasurableSpace (X i j)] : ⇑(piCurry X) = Sigma.curry := rfl

/--
lemma `coe_piCurry_symm` / 引理 `coe_piCurry_symm`

English:
lemma coe_piCurry_symm
  statement: {ι : Type*} {κ : ι -> Type*} (X : (i : ι) -> κ i -> Type*)
  proof: rfl

中文:
引理 coe_piCurry_symm
  结论: {ι : 类型} {κ : ι -> 类型} (X : (i : ι) -> κ i -> 类型)
  证明: rfl
-/
lemma coe_piCurry_symm {ι : Type*} {κ : ι -> Type*} (X : (i : ι) -> κ i -> Type*)
    [forall i j, MeasurableSpace (X i j)] : ⇑(piCurry X).symm = Sigma.uncurry := rfl

/-- The currying operation `Sigma.curry` as a measurable equivalence.
See `MeasurableEquiv.piCurry` for the dependent version. -/
@[simps!]
/--
Definition of `curry` / `curry` 的定义

English:
definition curry
  signature: (ι κ X : Type*) [MeasurableSpace X]
  body: Equiv.curry ι κ X

中文:
定义 curry
  签名: (ι κ X : 类型) [可测空间 X]
  定义体: Equiv.curry ι κ X

Depends on / 依赖: Equiv.curry
-/
def curry (ι κ X : Type*) [MeasurableSpace X] : (ι × κ -> X) ≃ᵐ (ι -> κ -> X) where
  toEquiv := Equiv.curry ι κ X

/--
lemma `coe_curry` / 引理 `coe_curry`

English:
lemma coe_curry
  given: (ι κ X : Type*) [MeasurableSpace X]
  statement: ⇑(curry ι κ X) = Function.curry
  proof: rfl

中文:
引理 coe_curry
  条件: (ι κ X : 类型) [可测空间 X]
  结论: ⇑(curry ι κ X) = 函数.curry
  证明: rfl
-/
lemma coe_curry (ι κ X : Type*) [MeasurableSpace X] : ⇑(curry ι κ X) = Function.curry := rfl

/--
lemma `coe_curry_symm` / 引理 `coe_curry_symm`

English:
lemma coe_curry_symm
  given: (ι κ X : Type*) [MeasurableSpace X]
  proof: rfl

中文:
引理 coe_curry_symm
  条件: (ι κ X : 类型) [可测空间 X]
  证明: rfl
-/
lemma coe_curry_symm (ι κ X : Type*) [MeasurableSpace X] :
    ⇑(curry ι κ X).symm = Function.uncurry := rfl

end MeasurableEquiv

end curry
