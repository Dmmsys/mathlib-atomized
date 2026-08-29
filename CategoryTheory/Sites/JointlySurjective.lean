/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Hypercover.Zero
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
# The jointly surjective precoverage

In the category of types, the jointly surjective precoverage has the jointly surjective
families as coverings. We show that this precoverage is stable under the standard constructions.

## Notes

See `Mathlib/CategoryTheory/Sites/Types.lean` for the Grothendieck topology of jointly surjective
covers.
-/

@[expose] public section

universe u

namespace CategoryTheory

open Limits

namespace Types

/--
Definition of `jointlySurjectivePrecoverage` / `jointlySurjectivePrecoverage` 的定义

English:
definition jointlySurjectivePrecoverage
  signature: : Precoverage (Type u) where
  body: {R | forall x : X, exists (Y : Type u) (g : Y ⟶ X), R g ∧ x in Set.range g}

中文:
定义 jointlySurjectivePrecoverage
  签名: : Precoverage (类型u) where
  定义体: {R | forall x : X, exists (Y : Type u) (g : Y ⟶ X), R g ∧ x in Set.range g}

Depends on / 依赖: Set.range
-/
def jointlySurjectivePrecoverage : Precoverage (Type u) where
  coverings X := {R | forall x : X, exists (Y : Type u) (g : Y ⟶ X), R g ∧ x in Set.range g}

/--
lemma `mem_jointlySurjectivePrecoverage_iff` / 引理 `mem_jointlySurjectivePrecoverage_iff`

English:
lemma mem_jointlySurjectivePrecoverage_iff
  given: {X : Type u} {R : Presieve X}
  proof: .rfl

中文:
引理 mem_jointlySurjectivePrecoverage_iff
  条件: {X : 类型u} {R : Presieve X}
  证明: .rfl
-/
lemma mem_jointlySurjectivePrecoverage_iff {X : Type u} {R : Presieve X} :
    R in jointlySurjectivePrecoverage X ↔
      forall x : X, exists (Y : Type u) (g : Y ⟶ X), R g ∧ x in Set.range g :=
  .rfl

/--
lemma `singleton_mem_jointlySurjectivePrecoverage_iff` / 引理 `singleton_mem_jointlySurjectivePrecoverage_iff`

English:
lemma singleton_mem_jointlySurjectivePrecoverage_iff
  given: {X Y : Type u} {f : X ⟶ Y}
  proof: by
  rw [mem_jointlySurjectivePrecoverage_iff]
  refine ⟨fun hf x => ?_, fun hf x => ⟨X, f, ⟨⟩, by simp [hf.range_eq]⟩⟩
  obtain ⟨_, _, ⟨⟩, hx⟩ := hf x
  exact hx

@[simp]

中文:
引理 singleton_mem_jointlySurjectivePrecoverage_iff
  条件: {X Y : 类型u} {f : X ⟶ Y}
  证明: by
  rw [mem_jointlySurjectivePrecoverage_iff]
  refine ⟨fun hf x => ?_, fun hf x => ⟨X, f, ⟨⟩, by simp [hf.range_eq]⟩⟩
  obtain ⟨_, _, ⟨⟩, hx⟩ := hf x
  exact hx

@[simp]

Depends on / 依赖: hf.range_eq, mem_jointlySurjectivePrecoverage_iff, range_eq
-/
lemma singleton_mem_jointlySurjectivePrecoverage_iff {X Y : Type u} {f : X ⟶ Y} :
    Presieve.singleton f in jointlySurjectivePrecoverage Y ↔ Function.Surjective f := by
  rw [mem_jointlySurjectivePrecoverage_iff]
  refine ⟨fun hf x => ?_, fun hf x => ⟨X, f, ⟨⟩, by simp [hf.range_eq]⟩⟩
  obtain ⟨_, _, ⟨⟩, hx⟩ := hf x
  exact hx

@[simp]
/--
lemma `ofArrows_mem_jointlySurjectivePrecoverage_iff` / 引理 `ofArrows_mem_jointlySurjectivePrecoverage_iff`

English:
lemma ofArrows_mem_jointlySurjectivePrecoverage_iff
  statement: {X : Type u} {ι : Type*}
  proof: by
  refine ⟨fun h x => ?_, fun h x => ?_⟩
  · obtain ⟨Y, g, ⟨i⟩, hx⟩ := h x
    use i
  · obtain ⟨i, hx⟩ := h x
    use Y i, f i, ⟨i⟩

中文:
引理 ofArrows_mem_jointlySurjectivePrecoverage_iff
  结论: {X : 类型u} {ι : 类型}
  证明: by
  refine ⟨fun h x => ?_, fun h x => ?_⟩
  · obtain ⟨Y, g, ⟨i⟩, hx⟩ := h x
    use i
  · obtain ⟨i, hx⟩ := h x
    use Y i, f i, ⟨i⟩
-/
lemma ofArrows_mem_jointlySurjectivePrecoverage_iff {X : Type u} {ι : Type*}
    {Y : ι -> Type u} {f : forall i, Y i ⟶ X} :
    Presieve.ofArrows Y f in jointlySurjectivePrecoverage X ↔
      forall x, exists (i : ι), x in Set.range (f i) := by
  refine ⟨fun h x => ?_, fun h x => ?_⟩
  · obtain ⟨Y, g, ⟨i⟩, hx⟩ := h x
    use i
  · obtain ⟨i, hx⟩ := h x
    use Y i, f i, ⟨i⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: jointlySurjectivePrecoverage.HasIsos
  body: by
    use S, f, ⟨⟩
    exact surjective_of_epi f x

中文:
实例 :
  签名: jointlySurjectivePrecoverage.有是os
  定义体: by
    use S, f, ⟨⟩
    exact surjective_of_epi f x

Depends on / 依赖: surjective_of_epi
-/
instance : jointlySurjectivePrecoverage.HasIsos where
  mem_coverings_of_isIso {S T} f hf x := by
    use S, f, ⟨⟩
    exact surjective_of_epi f x

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: jointlySurjectivePrecoverage.IsStableUnderComposition
  body: by
    simp_rw [ofArrows_mem_jointlySurjectivePrecoverage_iff] at hf hg ⊢
    intro x
    obtain ⟨i, y, rfl⟩ := hf x
    obtain ⟨j, z, rfl⟩ := hg i y
    use ⟨i, j⟩, z
    simp

中文:
实例 :
  签名: jointlySurjectivePrecoverage.是StableUnderComposition
  定义体: by
    simp_rw [ofArrows_mem_jointlySurjectivePrecoverage_iff] at hf hg ⊢
    intro x
    obtain ⟨i, y, rfl⟩ := hf x
    obtain ⟨j, z, rfl⟩ := hg i y
    use ⟨i, j⟩, z
    simp

Depends on / 依赖: ofArrows_mem_jointlySurjectivePrecoverage_iff, simp_rw
-/
instance : jointlySurjectivePrecoverage.IsStableUnderComposition where
  comp_mem_coverings {ι} S X f hf σ Y g hg := by
    simp_rw [ofArrows_mem_jointlySurjectivePrecoverage_iff] at hf hg ⊢
    intro x
    obtain ⟨i, y, rfl⟩ := hf x
    obtain ⟨j, z, rfl⟩ := hg i y
    use ⟨i, j⟩, z
    simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: jointlySurjectivePrecoverage.IsStableUnderSup
  body: by
    obtain ⟨Y, f, hf, hx⟩ := hR x
    use Y, f, .inl hf

中文:
实例 :
  签名: jointlySurjectivePrecoverage.是StableUnderSup
  定义体: by
    obtain ⟨Y, f, hf, hx⟩ := hR x
    use Y, f, .inl hf
-/
instance : jointlySurjectivePrecoverage.IsStableUnderSup where
  sup_mem_coverings {X} R S hR _ x := by
    obtain ⟨Y, f, hf, hx⟩ := hR x
    use Y, f, .inl hf

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Precoverage.Small.{u} jointlySurjectivePrecoverage.{u}
  body: by
    choose i y hy using ofArrows_mem_jointlySurjectivePrecoverage_iff.mp E.mem₀
    refine ⟨X, i, ?_⟩
    rw [ofArrows_mem_jointlySurjectivePrecoverage_iff]
    intro x
    use x, y x, hy x

中文:
实例 :
  签名: Precoverage.Small.{u} jointlySurjectivePrecoverage.{u}
  定义体: by
    choose i y hy using ofArrows_mem_jointlySurjectivePrecoverage_iff.mp E.mem₀
    refine ⟨X, i, ?_⟩
    rw [ofArrows_mem_jointlySurjectivePrecoverage_iff]
    intro x
    use x, y x, hy x

Depends on / 依赖: E.mem, ofArrows_mem_jointlySurjectivePrecoverage_iff, ofArrows_mem_jointlySurjectivePrecoverage_iff.mp
-/
instance : Precoverage.Small.{u} jointlySurjectivePrecoverage.{u} where
  zeroHypercoverSmall {X} E := by
    choose i y hy using ofArrows_mem_jointlySurjectivePrecoverage_iff.mp E.mem₀
    refine ⟨X, i, ?_⟩
    rw [ofArrows_mem_jointlySurjectivePrecoverage_iff]
    intro x
    use x, y x, hy x

end Types

variable {C : Type*} [Category* C] (F : C ⥤ Type u)

/--
lemma `Presieve.mem_comap_jointlySurjectivePrecoverage_iff` / 引理 `Presieve.mem_comap_jointlySurjectivePrecoverage_iff`

English:
lemma Presieve.mem_comap_jointlySurjectivePrecoverage_iff
  given: {X : C} {R : Presieve X}
  proof: by
  rw [Precoverage.mem_comap_iff]
  refine ⟨fun h x => ?_, fun h x => ?_⟩
  · obtain ⟨-, -, ⟨hf⟩, hi⟩ := h x
    exact ⟨_, _, hf, hi⟩
  · obtain ⟨Y, g, hg, hi⟩ := h x
    exact ⟨_, _, ⟨hg⟩, hi⟩

中文:
引理 Presieve.mem_comap_jointlySurjectivePrecoverage_iff
  条件: {X : C} {R : Presieve X}
  证明: by
  rw [Precoverage.mem_comap_iff]
  refine ⟨fun h x => ?_, fun h x => ?_⟩
  · obtain ⟨-, -, ⟨hf⟩, hi⟩ := h x
    exact ⟨_, _, hf, hi⟩
  · obtain ⟨Y, g, hg, hi⟩ := h x
    exact ⟨_, _, ⟨hg⟩, hi⟩

Depends on / 依赖: Precoverage, Precoverage.mem_comap_iff, mem_comap_iff
-/
lemma Presieve.mem_comap_jointlySurjectivePrecoverage_iff {X : C} {R : Presieve X} :
    R in Types.jointlySurjectivePrecoverage.comap F X ↔
      forall x : F.obj X, exists (Y : C) (f : Y ⟶ X), R f ∧ x in Set.range (F.map f) := by
  rw [Precoverage.mem_comap_iff]
  refine ⟨fun h x => ?_, fun h x => ?_⟩
  · obtain ⟨-, -, ⟨hf⟩, hi⟩ := h x
    exact ⟨_, _, hf, hi⟩
  · obtain ⟨Y, g, hg, hi⟩ := h x
    exact ⟨_, _, ⟨hg⟩, hi⟩

/--
lemma `Presieve.ofArrows_mem_comap_jointlySurjectivePrecoverage_iff` / 引理 `Presieve.ofArrows_mem_comap_jointlySurjectivePrecoverage_iff`

English:
lemma Presieve.ofArrows_mem_comap_jointlySurjectivePrecoverage_iff
  statement: {X : C} {ι : Type*}
  proof: by
  simp

中文:
引理 Presieve.ofArrows_mem_comap_jointlySurjectivePrecoverage_iff
  结论: {X : C} {ι : 类型}
  证明: by
  simp
-/
lemma Presieve.ofArrows_mem_comap_jointlySurjectivePrecoverage_iff {X : C} {ι : Type*}
    {Y : ι -> C} {f : forall i, Y i ⟶ X} :
    ofArrows Y f in Types.jointlySurjectivePrecoverage.comap F X ↔
      forall x : F.obj X, exists (i : ι), x in Set.range (F.map (f i)) := by
  simp

/--
lemma `isStableUnderBaseChange_comap_jointlySurjectivePrecoverage` / 引理 `isStableUnderBaseChange_comap_jointlySurjectivePrecoverage`

English:
lemma isStableUnderBaseChange_comap_jointlySurjectivePrecoverage
  proof: by
    rw [Precoverage.mem_comap_iff]; rw [Presieve.map_ofArrows]; rw [Types.ofArrows_mem_jointlySurjectivePrecoverage_iff] at hf ⊢
    intro x
    obtain ⟨i, hi⟩ := hf (F.map g x)
    have : HasPullback g (f i) := (h i).hasPullback
    use i
    have : F.map (p₁ i) = F.map ((h i).isoPullback.hom) ≫ pullbackComparison F g (f i) ≫
        pullback.fst _ _ := by simp [← Functor.map_comp]
    rwa [this, types_comp, types_comp, Function.comp_assoc, Set.range_comp,
Function.Surjective.range_eq (H _ _).comp (surjective_of_epi _), Set.image_univ,
      Types.range_pullbackFst]

中文:
引理 isStableUnderBaseChange_comap_jointlySurjectivePrecoverage
  证明: by
    rw [Precoverage.mem_comap_iff]; rw [Presieve.map_ofArrows]; rw [Types.ofArrows_mem_jointlySurjectivePrecoverage_iff] at hf ⊢
    intro x
    obtain ⟨i, hi⟩ := hf (F.map g x)
    have : HasPullback g (f i) := (h i).hasPullback
    use i
    have : F.map (p₁ i) = F.map ((h i).isoPullback.hom) ≫ pullbackComparison F g (f i) ≫
        pullback.fst _ _ := by simp [← Functor.map_comp]
    rwa [this, types_comp, types_comp, Function.comp_assoc, Set.range_comp,
Function.Surjective.range_eq (H _ _).comp (surjective_of_epi _), Set.image_univ,
      Types.range_pullbackFst]

Depends on / 依赖: F.map, Function, Function.Surjective.range_eq, Function.comp_assoc, Functor, Functor.map_comp, HasPullback, Precoverage, Precoverage.mem_comap_iff, Presieve, Presieve.map_ofArrows, Set.im, Set.range_comp, Surjective, Types.ofArrows_mem_jointlySurjectivePrecoverage_iff, comp_assoc, hasPullback, isoPullback, isoPullback.hom, map_comp
-/
lemma isStableUnderBaseChange_comap_jointlySurjectivePrecoverage
    (H : forall {X Y S : C} (f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g],
      Function.Surjective (pullbackComparison F f g)) :
    (Types.jointlySurjectivePrecoverage.comap F).IsStableUnderBaseChange where
  mem_coverings_of_isPullback {ι} S X f hf Y g P p₁ p₂ h := by
    rw [Precoverage.mem_comap_iff]; rw [Presieve.map_ofArrows]; rw [Types.ofArrows_mem_jointlySurjectivePrecoverage_iff] at hf ⊢
    intro x
    obtain ⟨i, hi⟩ := hf (F.map g x)
    have : HasPullback g (f i) := (h i).hasPullback
    use i
    have : F.map (p₁ i) = F.map ((h i).isoPullback.hom) ≫ pullbackComparison F g (f i) ≫
        pullback.fst _ _ := by simp [← Functor.map_comp]
    rwa [this, types_comp, types_comp, Function.comp_assoc, Set.range_comp,
Function.Surjective.range_eq (H _ _).comp (surjective_of_epi _), Set.image_univ,
      Types.range_pullbackFst]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Types.jointlySurjectivePrecoverage.IsStableUnderBaseChange
  body: by
  rw [← Precoverage.comap_id Types.jointlySurjectivePrecoverage]
  apply isStableUnderBaseChange_comap_jointlySurjectivePrecoverage
  intro X Y S f g _
  exact surjective_of_epi _

中文:
实例 :
  签名: Types.jointlySurjectivePrecoverage.是StableUnderBaseChange
  定义体: by
  rw [← Precoverage.comap_id Types.jointlySurjectivePrecoverage]
  apply isStableUnderBaseChange_comap_jointlySurjectivePrecoverage
  intro X Y S f g _
  exact surjective_of_epi _

Depends on / 依赖: Precoverage, Precoverage.comap_id, Types.jointlySurjectivePrecoverage, comap_id, isStableUnderBaseChange_comap_jointlySurjectivePrecoverage, jointlySurjectivePrecoverage, surjective_of_epi
-/
instance : Types.jointlySurjectivePrecoverage.IsStableUnderBaseChange := by
  rw [← Precoverage.comap_id Types.jointlySurjectivePrecoverage]
  apply isStableUnderBaseChange_comap_jointlySurjectivePrecoverage
  intro X Y S f g _
  exact surjective_of_epi _

end CategoryTheory
