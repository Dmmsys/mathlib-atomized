/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Sites.Closed
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Sites.Hypercover.IsSheaf
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Adjunction.Opposites
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves

/-!
# Continuous functors between sites.

We define the notion of continuous functor between sites: these are functors `F` such that
the precomposition with `F.op` preserves sheaves of types (and actually sheaves in any
category).

## Main definitions

* `Functor.IsContinuous`: a functor between sites is continuous if the
  precomposition with this functor preserves sheaves with values in
  the category `Type t` for a certain auxiliary universe `t`.
* `Functor.sheafPushforwardContinuous`: the induced functor
  `Sheaf K A ⥤ Sheaf J A` for a continuous functor `G : (C, J) ⥤ (D, K)`. In case this is
  part of a morphism of sites, this would be understood as the pushforward functor
  even though it goes in the opposite direction as the functor `G`. (Here, the auxiliary
  universe `t` in the assumption that `G` is continuous is the one such that morphisms
  in the category `A` are in `Type t`.)
* `Functor.PreservesOneHypercovers`: a type-class expressing that a functor preserves
  1-hypercovers of a certain size

## Main result

- `Functor.isContinuous_of_preservesOneHypercovers`: if the topology on `C` is generated
  by 1-hypercovers of size `w` and that `F : C ⥤ D` preserves 1-hypercovers of size `w`,
  then `F` is continuous (for any auxiliary universe parameter `t`).
  This is an instance for `w = max u₁ v₁` when `C : Type u₁` and `[Category.{v₁} C]`

## References
* https://stacks.math.columbia.edu/tag/00WU

-/

@[expose] public section

universe w t v₁ v₂ v₃ u₁ u₂ u₃ u

namespace CategoryTheory

open Limits

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]

namespace PreOneHypercover

variable {X : C} (E : PreOneHypercover X) (F : C ⥤ D)

/-- The image of a 1-pre-hypercover by a functor. -/
@[simps toPreZeroHypercover I₁ Y p₁ p₂]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: : PreOneHypercover (F.obj X) where
  body: E.toPreZeroHypercover.map F
  I₁ := E.I₁
  Y _ _ j := F.obj (E.Y j)
  p₁ _ _ j := F.map (E.p₁ j)
  p₂ _ _ j := F.map (E.p₂ j)
  w _ _ j := by simpa using! F.congr_map (E.w j)

@[simp]

中文:
定义 map
  签名: : PreOneHypercover (F.obj X) where
  定义体: E.toPreZeroHypercover.map F
  I₁ := E.I₁
  Y _ _ j := F.obj (E.Y j)
  p₁ _ _ j := F.map (E.p₁ j)
  p₂ _ _ j := F.map (E.p₂ j)
  w _ _ j := by simpa using! F.congr_map (E.w j)

@[simp]

Depends on / 依赖: E.toPreZeroHypercover.map, toPreZeroHypercover
-/
def map : PreOneHypercover (F.obj X) where
  __ := E.toPreZeroHypercover.map F
  I₁ := E.I₁
  Y _ _ j := F.obj (E.Y j)
  p₁ _ _ j := F.map (E.p₁ j)
  p₂ _ _ j := F.map (E.p₂ j)
  w _ _ j := by simpa using! F.congr_map (E.w j)

@[simp]
/--
lemma `map_id` / 引理 `map_id`

English:
lemma map_id
  statement: E.map (𝟭 _) = E
  proof: rfl

中文:
引理 map_id
  结论: E.map (𝟭 _) = E
  证明: rfl
-/
lemma map_id : E.map (𝟭 _) = E :=
  rfl

/--
lemma `map_comp` / 引理 `map_comp`

English:
lemma map_comp
  given: {D' : Type*} [Category* D'] (G : D ⥤ D')
  statement: E.map (F ⋙ G) = (E.map F).map G
  proof: rfl

中文:
引理 map_comp
  条件: {D' : 类型} [范畴* D'] (G : D ⥤ D')
  结论: E.map (F ⋙ G) = (E.map F).map G
  证明: rfl
-/
lemma map_comp {D' : Type*} [Category* D'] (G : D ⥤ D') : E.map (F ⋙ G) = (E.map F).map G :=
  rfl

/--
lemma `sieve₀_map` / 引理 `sieve₀_map`

English:
lemma sieve₀_map
  statement: (E.map F).sieve₀ = Sieve.functorPushforward _ E.sieve₀
  proof: by
  rw [PreZeroHypercover.sieve₀]; rw [Sieve.ofArrows]; rw [← PreZeroHypercover.presieve₀]; rw [PreOneHypercover.map_toPreZeroHypercover]; rw [PreZeroHypercover.presieve₀_map]; rw [Sieve.generate_map_eq_functorPushforward]

中文:
引理 sieve₀_map
  结论: (E.map F).sieve₀ = 筛.functorPushforward _ E.sieve₀
  证明: by
  rw [PreZeroHypercover.sieve₀]; rw [Sieve.ofArrows]; rw [← PreZeroHypercover.presieve₀]; rw [PreOneHypercover.map_toPreZeroHypercover]; rw [PreZeroHypercover.presieve₀_map]; rw [Sieve.generate_map_eq_functorPushforward]

Depends on / 依赖: PreOneHypercover, PreOneHypercover.map_toPreZeroHypercover, PreZeroHypercover, PreZeroHypercover.presieve, PreZeroHypercover.sieve, Sieve.generate_map_eq_functorPushforward, Sieve.ofArrows, generate_map_eq_functorPushforward, map_toPreZeroHypercover, ofArrows
-/
lemma sieve₀_map : (E.map F).sieve₀ = Sieve.functorPushforward _ E.sieve₀ := by
  rw [PreZeroHypercover.sieve₀]; rw [Sieve.ofArrows]; rw [← PreZeroHypercover.presieve₀]; rw [PreOneHypercover.map_toPreZeroHypercover]; rw [PreZeroHypercover.presieve₀_map]; rw [Sieve.generate_map_eq_functorPushforward]

/--
Definition of `isLimitMapMultiforkEquiv` / `isLimitMapMultiforkEquiv` 的定义

English:
definition isLimitMapMultiforkEquiv
  signature: {A : Type u} [Category.{t} A] (P : Dᵒᵖ ⥤ A)
  body: by rfl

中文:
定义 isLimitMapMultiforkEquiv
  签名: {A : 类型u} [范畴.{t} A] (P : Dᵒᵖ ⥤ A)
  定义体: by rfl
-/
def isLimitMapMultiforkEquiv {A : Type u} [Category.{t} A] (P : Dᵒᵖ ⥤ A) :
    IsLimit ((E.map F).multifork P) ≃ IsLimit (E.multifork (F.op ⋙ P)) := by rfl

section

variable {E} {W : C} {i₁ i₂ : E.I₀} (p₁ : W ⟶ E.X i₁) (p₂ : W ⟶ E.X i₂)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `functorPushforward_sieve₁_map_le` / 引理 `functorPushforward_sieve₁_map_le`

English:
lemma functorPushforward_sieve₁_map_le
  proof: by
  rw [Sieve.functorPushforward_le_iff_le_functorPullback]
  intro Y f ⟨k, u, hf₁, hf₂⟩
  exact ⟨k, F.map u, by simp [← Functor.map_comp, hf₁], by simp [← Functor.map_comp, hf₂]⟩

中文:
引理 functorPushforward_sieve₁_map_le
  证明: by
  rw [Sieve.functorPushforward_le_iff_le_functorPullback]
  intro Y f ⟨k, u, hf₁, hf₂⟩
  exact ⟨k, F.map u, by simp [← Functor.map_comp, hf₁], by simp [← Functor.map_comp, hf₂]⟩

Depends on / 依赖: F.map, Functor, Functor.map_comp, Sieve.functorPushforward_le_iff_le_functorPullback, functorPushforward_le_iff_le_functorPullback, map_comp
-/
lemma functorPushforward_sieve₁_map_le :
    Sieve.functorPushforward F (E.sieve₁ p₁ p₂) <= (E.map F).sieve₁ (F.map p₁) (F.map p₂) := by
  rw [Sieve.functorPushforward_le_iff_le_functorPullback]
  intro Y f ⟨k, u, hf₁, hf₂⟩
  exact ⟨k, F.map u, by simp [← Functor.map_comp, hf₁], by simp [← Functor.map_comp, hf₂]⟩

variable (i₁ i₂) in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `functorPushforward_sieve₁'_of_preservesLimit` / 引理 `functorPushforward_sieve₁'_of_preservesLimit`

English:
lemma functorPushforward_sieve₁'_of_preservesLimit
  statement: [HasPullback (E.f i₁) (E.f i₂)]
  proof: by
  have : HasPullback ((E.map F).f i₁) ((E.map F).f i₂) :=
    hasPullback_of_preservesPullback F (E.f i₁) (E.f i₂)
  refine le_antisymm ?_ ?_
  · rw [PreOneHypercover.sieve₁'_eq_sieve₁]
    apply PreOneHypercover.functorPushforward_sieve₁_map_le
  · rw [PreOneHypercover.sieve₁_eq_pullback_sieve₁' _ _ _
      (by simp [← Functor.map_comp, pullback.condition])]
    rintro W f ⟨Z, u, v, ⟨k⟩, h⟩
    refine ⟨E.Y k, pullback.lift (E.p₁ k) (E.p₂ k) (E.w _), u, ?_, ?_⟩
    · use E.Y k, 𝟙 _, pullback.lift (E.p₁ k) (E.p₂ k) (E.w _), ⟨k⟩
      simp
    · simp only [pullback.hom_ext_iff, Category.assoc, limit.lift_π, PullbackCone.mk_π_app] at h
      apply IsPullback.hom_ext (IsPullback.map _ (.of_hasPullback _ _)) <;>
        simp [← h.left, ← h.right, ← Functor.map_comp]

中文:
引理 functorPushforward_sieve₁'_of_preservesLimit
  结论: [HasPullback (E.f i₁) (E.f i₂)]
  证明: by
  have : HasPullback ((E.map F).f i₁) ((E.map F).f i₂) :=
    hasPullback_of_preservesPullback F (E.f i₁) (E.f i₂)
  refine le_antisymm ?_ ?_
  · rw [PreOneHypercover.sieve₁'_eq_sieve₁]
    apply PreOneHypercover.functorPushforward_sieve₁_map_le
  · rw [PreOneHypercover.sieve₁_eq_pullback_sieve₁' _ _ _
      (by simp [← Functor.map_comp, pullback.condition])]
    rintro W f ⟨Z, u, v, ⟨k⟩, h⟩
    refine ⟨E.Y k, pullback.lift (E.p₁ k) (E.p₂ k) (E.w _), u, ?_, ?_⟩
    · use E.Y k, 𝟙 _, pullback.lift (E.p₁ k) (E.p₂ k) (E.w _), ⟨k⟩
      simp
    · simp only [pullback.hom_ext_iff, Category.assoc, limit.lift_π, PullbackCone.mk_π_app] at h
      apply IsPullback.hom_ext (IsPullback.map _ (.of_hasPullback _ _)) <;>
        simp [← h.left, ← h.right, ← Functor.map_comp]

Depends on / 依赖: E.map, Functor, Functor.map_comp, HasPullback, PreOneHypercover, PreOneHypercover.functorPushforward_sieve, PreOneHypercover.sieve, condition, hasPullback_of_preservesPullback, le_antisymm, map_comp, pullback, pullback.condition, pullback.lift
-/
lemma functorPushforward_sieve₁'_of_preservesLimit [HasPullback (E.f i₁) (E.f i₂)]
    [PreservesLimit (cospan (E.f i₁) (E.f i₂)) F] :
    Sieve.functorPushforward F (E.sieve₁' i₁ i₂) =
      (E.map F).sieve₁ (F.map <| pullback.fst _ _) (F.map <| pullback.snd _ _) := by
  have : HasPullback ((E.map F).f i₁) ((E.map F).f i₂) :=
    hasPullback_of_preservesPullback F (E.f i₁) (E.f i₂)
  refine le_antisymm ?_ ?_
  · rw [PreOneHypercover.sieve₁'_eq_sieve₁]
    apply PreOneHypercover.functorPushforward_sieve₁_map_le
  · rw [PreOneHypercover.sieve₁_eq_pullback_sieve₁' _ _ _
      (by simp [← Functor.map_comp, pullback.condition])]
    rintro W f ⟨Z, u, v, ⟨k⟩, h⟩
    refine ⟨E.Y k, pullback.lift (E.p₁ k) (E.p₂ k) (E.w _), u, ?_, ?_⟩
    · use E.Y k, 𝟙 _, pullback.lift (E.p₁ k) (E.p₂ k) (E.w _), ⟨k⟩
      simp
    · simp only [pullback.hom_ext_iff, Category.assoc, limit.lift_π, PullbackCone.mk_π_app] at h
      apply IsPullback.hom_ext (IsPullback.map _ (.of_hasPullback _ _)) <;>
        simp [← h.left, ← h.right, ← Functor.map_comp]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `functorPushforward_sieve₁_of_preservesPullbacks` / 引理 `functorPushforward_sieve₁_of_preservesPullbacks`

English:
lemma functorPushforward_sieve₁_of_preservesPullbacks
  statement: (h : p₁ ≫ E.f _ = p₂ ≫ E.f _)
  proof: by
  refine le_antisymm (PreOneHypercover.functorPushforward_sieve₁_map_le _ _ _) ?_
  have : HasPullback ((E.map F).f i₁) ((E.map F).f i₂) :=
    hasPullback_of_preservesPullback F (E.f i₁) (E.f i₂)
  rintro T f ⟨k, u, hf₁, hf₂⟩
  let l : W ⟶ pullback (E.f i₁) (E.f i₂) := pullback.lift p₁ p₂ h
  have hl₁ : l ≫ pullback.fst _ _ = p₁ := by simp [l]
  have hl₂ : l ≫ pullback.snd _ _ = p₂ := by simp [l]
  let r : E.Y k ⟶ pullback (E.f i₁) (E.f i₂) := pullback.lift (E.p₁ _) (E.p₂ _) (E.w _)
  refine ⟨pullback l r, pullback.fst _ _, IsPullback.lift
    (IsPullback.map _ (.of_hasPullback _ _)) f u ?_, ?_, ?_⟩
  · apply (IsPullback.map _ (.of_hasPullback _ _)).hom_ext <;>
      simp [l, r, ← Functor.map_comp, hf₁, hf₂]
  · refine ⟨k, pullback.snd _ _, ?_, ?_⟩ <;> simp [← hl₁, ← hl₂, pullback.condition_assoc, r]
  · simp

中文:
引理 functorPushforward_sieve₁_of_preservesPullbacks
  结论: (h : p₁ ≫ E.f _ = p₂ ≫ E.f _)
  证明: by
  refine le_antisymm (PreOneHypercover.functorPushforward_sieve₁_map_le _ _ _) ?_
  have : HasPullback ((E.map F).f i₁) ((E.map F).f i₂) :=
    hasPullback_of_preservesPullback F (E.f i₁) (E.f i₂)
  rintro T f ⟨k, u, hf₁, hf₂⟩
  let l : W ⟶ pullback (E.f i₁) (E.f i₂) := pullback.lift p₁ p₂ h
  have hl₁ : l ≫ pullback.fst _ _ = p₁ := by simp [l]
  have hl₂ : l ≫ pullback.snd _ _ = p₂ := by simp [l]
  let r : E.Y k ⟶ pullback (E.f i₁) (E.f i₂) := pullback.lift (E.p₁ _) (E.p₂ _) (E.w _)
  refine ⟨pullback l r, pullback.fst _ _, IsPullback.lift
    (IsPullback.map _ (.of_hasPullback _ _)) f u ?_, ?_, ?_⟩
  · apply (IsPullback.map _ (.of_hasPullback _ _)).hom_ext <;>
      simp [l, r, ← Functor.map_comp, hf₁, hf₂]
  · refine ⟨k, pullback.snd _ _, ?_, ?_⟩ <;> simp [← hl₁, ← hl₂, pullback.condition_assoc, r]
  · simp

Depends on / 依赖: E.map, HasPullback, PreOneHypercover, PreOneHypercover.functorPushforward_sieve, hasPullback_of_preservesPullback, le_antisymm, pullback, pullback.fst, pullback.lift, pullback.snd
-/
lemma functorPushforward_sieve₁_of_preservesPullbacks (h : p₁ ≫ E.f _ = p₂ ≫ E.f _)
    [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan F] :
    Sieve.functorPushforward F (E.sieve₁ p₁ p₂) = (E.map F).sieve₁ (F.map p₁) (F.map p₂) := by
  refine le_antisymm (PreOneHypercover.functorPushforward_sieve₁_map_le _ _ _) ?_
  have : HasPullback ((E.map F).f i₁) ((E.map F).f i₂) :=
    hasPullback_of_preservesPullback F (E.f i₁) (E.f i₂)
  rintro T f ⟨k, u, hf₁, hf₂⟩
  let l : W ⟶ pullback (E.f i₁) (E.f i₂) := pullback.lift p₁ p₂ h
  have hl₁ : l ≫ pullback.fst _ _ = p₁ := by simp [l]
  have hl₂ : l ≫ pullback.snd _ _ = p₂ := by simp [l]
  let r : E.Y k ⟶ pullback (E.f i₁) (E.f i₂) := pullback.lift (E.p₁ _) (E.p₂ _) (E.w _)
  refine ⟨pullback l r, pullback.fst _ _, IsPullback.lift
    (IsPullback.map _ (.of_hasPullback _ _)) f u ?_, ?_, ?_⟩
  · apply (IsPullback.map _ (.of_hasPullback _ _)).hom_ext <;>
      simp [l, r, ← Functor.map_comp, hf₁, hf₂]
  · refine ⟨k, pullback.snd _ _, ?_, ?_⟩ <;> simp [← hl₁, ← hl₂, pullback.condition_assoc, r]
  · simp

end

end PreOneHypercover

namespace GrothendieckTopology

namespace OneHypercover

variable {J : GrothendieckTopology C} {X : C} (E : J.OneHypercover X)

/--
Definition of `IsPreservedBy` / `IsPreservedBy` 的定义

English:
class IsPreservedBy
  parameters: (F : C ⥤ D) (K : GrothendieckTopology D)
  axioms and operations (2):
    - mem₀ : (E.toPreOneHypercover.map F).sieve₀ in K (F.obj X)
    - mem₁((i₁ i₂ : E.I₀) ⦃W) : D⦄ (p₁ : W ⟶ F.obj (E.X i₁)) (p₂ : W ⟶ F.obj (E.X i₂)) (w : p₁ ≫ F.map (E.f i₁) = p₂ ≫ F.map (E.f i₂)) : (E.toPreOneHypercover.map F).sieve₁ p₁ p₂ in K W

中文:
类 是PreservedBy
  参数: (F : C ⥤ D) (K : Grothendieck拓扑 D)
  公理与运算 (2 个):
    - mem₀ : (E.toPreOneHypercover.map F).sieve₀ in K (F.obj X)
    - mem₁((i₁ i₂ : E.I₀) ⦃W) : D⦄ (p₁ : W ⟶ F.obj (E.X i₁)) (p₂ : W ⟶ F.obj (E.X i₂)) (w : p₁ ≫ F.map (E.f i₁) = p₂ ≫ F.map (E.f i₂)) : (E.toPreOneHypercover.map F).sieve₁ p₁ p₂ in K W
-/
class IsPreservedBy (F : C ⥤ D) (K : GrothendieckTopology D) : Prop where
  mem₀ : (E.toPreOneHypercover.map F).sieve₀ in K (F.obj X)
  mem₁ (i₁ i₂ : E.I₀) ⦃W : D⦄ (p₁ : W ⟶ F.obj (E.X i₁)) (p₂ : W ⟶ F.obj (E.X i₂))
    (w : p₁ ≫ F.map (E.f i₁) = p₂ ≫ F.map (E.f i₂)) :
      (E.toPreOneHypercover.map F).sieve₁ p₁ p₂ in K W

/-- Given a 1-hypercover `E : J.OneHypercover X` of an object of `C`, a functor `F : C ⥤ D`
such that `E.IsPreservedBy F K` for a Grothendieck topology `K` on `D`, this is
the image of `E` by `F`, as a 1-hypercover of `F.obj X` for `K`. -/
@[simps! toPreOneHypercover]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (F : C ⥤ D) (K : GrothendieckTopology D) [E.IsPreservedBy F K]
  body: E.toPreOneHypercover.map F
  mem₀ := IsPreservedBy.mem₀
  mem₁ _ _ _ _ _ h := IsPreservedBy.mem₁ _ _ _ _ h

中文:
定义 map
  签名: (F : C ⥤ D) (K : Grothendieck拓扑 D) [E.是PreservedBy F K]
  定义体: E.toPreOneHypercover.map F
  mem₀ := IsPreservedBy.mem₀
  mem₁ _ _ _ _ _ h := IsPreservedBy.mem₁ _ _ _ _ h

Depends on / 依赖: E.toPreOneHypercover.map, toPreOneHypercover
-/
def map (F : C ⥤ D) (K : GrothendieckTopology D) [E.IsPreservedBy F K] :
    K.OneHypercover (F.obj X) where
  toPreOneHypercover := E.toPreOneHypercover.map F
  mem₀ := IsPreservedBy.mem₀
  mem₁ _ _ _ _ _ h := IsPreservedBy.mem₁ _ _ _ _ h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: E.IsPreservedBy (𝟭 C) J
  body: E.mem₀
  mem₁ := E.mem₁

中文:
实例 :
  签名: E.是PreservedBy (𝟭 C) J
  定义体: E.mem₀
  mem₁ := E.mem₁

Depends on / 依赖: E.mem
-/
instance : E.IsPreservedBy (𝟭 C) J where
  mem₀ := E.mem₀
  mem₁ := E.mem₁

end OneHypercover

end GrothendieckTopology

namespace Functor

variable (F F' : C ⥤ D) (τ : F ⟶ F') (e : F ≅ F') (G : D ⥤ E)
  {F'' : C ⥤ C} (eF'' : F'' ≅ 𝟭 C) {FG : C ⥤ E} (eFG : F ⋙ G ≅ FG)
  {A : Type u} [Category.{t} A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : GrothendieckTopology E)

/--
Definition of `PreservesOneHypercovers` / `PreservesOneHypercovers` 的定义

English:
abbreviation PreservesOneHypercovers
  body: forall {X : C} (E : GrothendieckTopology.OneHypercover.{w} J X), E.IsPreservedBy F K

中文:
缩写 PreservesOneHypercovers
  定义体: forall {X : C} (E : GrothendieckTopology.OneHypercover.{w} J X), E.IsPreservedBy F K

Depends on / 依赖: E.IsPreservedBy, GrothendieckTopology, GrothendieckTopology.OneHypercover, IsPreservedBy, OneHypercover
-/
abbrev PreservesOneHypercovers :=
  forall {X : C} (E : GrothendieckTopology.OneHypercover.{w} J X), E.IsPreservedBy F K

/--
Definition of `IsContinuous` / `IsContinuous` 的定义

English:
class IsContinuous
  parameters: : Prop where
  axioms and operations (1):
    - op_comp_isSheaf_of_types((G : Sheaf K (Type max u₁ v₁ u₂ v₂))) : Presieve.IsSheaf J (F.op ⋙ G.obj)

中文:
类 是连续
  参数: : 命题 where
  公理与运算 (1 个):
    - op_comp_isSheaf_of_types((G : 层 K (类型 最大值 u₁ v₁ u₂ v₂))) : Presieve.是层 J (F.op ⋙ G.obj)

Depends on / 依赖: IsContinuous, IsContinuous.op_comp_isSheaf_of_types, adj.map_comp_bijective_iff, isSheaf_iff_isSheaf_of_type, map_comp_bijective_iff, op_comp_isSheaf_of_types
-/
class IsContinuous : Prop where
  op_comp_isSheaf_of_types (G : Sheaf K (Type max u₁ v₁ u₂ v₂)) : Presieve.IsSheaf J (F.op ⋙ G.obj)

/--
lemma `W_map_of_adjunction_of_isContinuous_aux` / 引理 `W_map_of_adjunction_of_isContinuous_aux`

English:
lemma W_map_of_adjunction_of_isContinuous_aux
  statement: (F : C ⥤ D)
  proof: by
  intro U hU
  rw [adj.map_comp_bijective_iff]
  apply hf
  rw [isSheaf_iff_isSheaf_of_type]
  exact IsContinuous.op_comp_isSheaf_of_types (F := F) ⟨U, hU⟩

中文:
引理 W_map_of_adjunction_of_isContinuous_aux
  结论: (F : C ⥤ D)
  证明: by
  intro U hU
  rw [adj.map_comp_bijective_iff]
  apply hf
  rw [isSheaf_iff_isSheaf_of_type]
  exact IsContinuous.op_comp_isSheaf_of_types (F := F) ⟨U, hU⟩
-/
private lemma W_map_of_adjunction_of_isContinuous_aux (F : C ⥤ D)
    (H : (Cᵒᵖ ⥤ Type max u₁ v₁ u₂ v₂) ⥤ (Dᵒᵖ ⥤ Type max u₁ v₁ u₂ v₂))
    (adj : H ⊣ (Functor.whiskeringLeft _ _ _).obj F.op)
    [Functor.IsContinuous F J K] {G G' : Cᵒᵖ ⥤ Type max u₁ v₁ u₂ v₂} (f : G ⟶ G') (hf : J.W f) :
    K.W (H.map f) := by
  intro U hU
  rw [adj.map_comp_bijective_iff]
  apply hf
  rw [isSheaf_iff_isSheaf_of_type]
  exact IsContinuous.op_comp_isSheaf_of_types (F := F) ⟨U, hU⟩

set_option backward.defeqAttrib.useBackward true in
/--
lemma `isSheaf_of_isContinuous_aux` / 引理 `isSheaf_of_isContinuous_aux`

English:
lemma isSheaf_of_isContinuous_aux
  statement: (F : C ⥤ D) [Functor.IsContinuous F J K]
  proof: by
  let H : (Cᵒᵖ ⥤ Type max u₁ v₁ u₂ v₂) ⥤ Dᵒᵖ ⥤ Type max u₁ v₁ u₂ v₂ := F.op.lan
  let adj : H ⊣ (Functor.whiskeringLeft _ _ _).obj F.op := F.op.lanAdjunction _
  let H' : (Cᵒᵖ ⥤ Type max w u₁ v₁ u₂ v₂) ⥤ Dᵒᵖ ⥤ Type max w u₁ v₁ u₂ v₂ := F.op.lan
  let adj' : H' ⊣ (Functor.whiskeringLeft _ _ _).obj F.op := F.op.lanAdjunction _
  refine Presieve.IsSheaf.comp_of_W_map_of_adjunction _ adj' ?_ _ hG
  intro X S hS
  have hWS : J.W (Sieve.shrinkFunctor.{max u₁ v₁ u₂ v₂} S).ι :=
    Sieve.W_shrinkFunctor_ι_of_mem.{max u₁ v₁ u₂ v₂} _ S hS
  have : K.W _ := Functor.W_map_of_adjunction_of_isContinuous_aux (J := J) K F H adj
    (Sieve.shrinkFunctor.{max u₁ v₁ u₂ v₂} S).ι hWS
  let e : H ⋙ (Functor.whiskeringRight _ _ _).obj uliftFunctor.{w} ≅
      (Functor.whiskeringRight _ _ _).obj uliftFunctor.{w} ⋙ H' :=
    uliftFunctor.{w, max (max (max u₁ u₂) v₁) v₂}.lanCompIsoOfPreserves F.op
  let iso : Arrow.mk (H'.map (Sieve.shrinkFunctor.{max w u₁ v₁ u₂ v₂} S).ι) ≅
      .mk (Functor.whiskerRight
        (H.map (Sieve.shrinkFunctor.{max u₁ v₁ u₂ v₂} S).ι) uliftFunctor.{w}) :=
    Arrow.isoMk' _ _
      (H'.mapIso (Sieve.shrinkFunctorUliftFunctorIso.{max u₁ v₁ u₂ v₂, w} S).symm ≪≫ (e.app _).symm)
(H'.mapIso (shrinkYonedaUliftFunctorIso.{max u₁ v₁ u₂ v₂}.app _).symm ≪≫ (e.app _).symm) by
        simp only [Functor.mapIso_symm, Functor.comp_obj, Functor.whiskeringRight_obj_obj,
          Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, Iso.app_inv, Category.assoc]
        rw [← Functor.map_comp_assoc]; rw [← dsimp% e.inv.naturality]; rw [← Functor.map_comp_assoc]; rw [Sieve.shrinkFunctorUliftFunctorIso_inv_ι]
  rw [K.W.arrow_mk_iso_iff iso]
  apply GrothendieckTopology.W_of_preservesSheafification
  exact F.W_map_of_adjunction_of_isContinuous_aux J K H adj
    (Sieve.shrinkFunctor.{max u₁ v₁ u₂ v₂} S).ι hWS

中文:
引理 isSheaf_of_isContinuous_aux
  结论: (F : C ⥤ D) [函子.是连续 F J K]
  证明: by
  let H : (Cᵒᵖ ⥤ Type max u₁ v₁ u₂ v₂) ⥤ Dᵒᵖ ⥤ Type max u₁ v₁ u₂ v₂ := F.op.lan
  let adj : H ⊣ (Functor.whiskeringLeft _ _ _).obj F.op := F.op.lanAdjunction _
  let H' : (Cᵒᵖ ⥤ Type max w u₁ v₁ u₂ v₂) ⥤ Dᵒᵖ ⥤ Type max w u₁ v₁ u₂ v₂ := F.op.lan
  let adj' : H' ⊣ (Functor.whiskeringLeft _ _ _).obj F.op := F.op.lanAdjunction _
  refine Presieve.IsSheaf.comp_of_W_map_of_adjunction _ adj' ?_ _ hG
  intro X S hS
  have hWS : J.W (Sieve.shrinkFunctor.{max u₁ v₁ u₂ v₂} S).ι :=
    Sieve.W_shrinkFunctor_ι_of_mem.{max u₁ v₁ u₂ v₂} _ S hS
  have : K.W _ := Functor.W_map_of_adjunction_of_isContinuous_aux (J := J) K F H adj
    (Sieve.shrinkFunctor.{max u₁ v₁ u₂ v₂} S).ι hWS
  let e : H ⋙ (Functor.whiskeringRight _ _ _).obj uliftFunctor.{w} ≅
      (Functor.whiskeringRight _ _ _).obj uliftFunctor.{w} ⋙ H' :=
    uliftFunctor.{w, max (max (max u₁ u₂) v₁) v₂}.lanCompIsoOfPreserves F.op
  let iso : Arrow.mk (H'.map (Sieve.shrinkFunctor.{max w u₁ v₁ u₂ v₂} S).ι) ≅
      .mk (Functor.whiskerRight
        (H.map (Sieve.shrinkFunctor.{max u₁ v₁ u₂ v₂} S).ι) uliftFunctor.{w}) :=
    Arrow.isoMk' _ _
      (H'.mapIso (Sieve.shrinkFunctorUliftFunctorIso.{max u₁ v₁ u₂ v₂, w} S).symm ≪≫ (e.app _).symm)
(H'.mapIso (shrinkYonedaUliftFunctorIso.{max u₁ v₁ u₂ v₂}.app _).symm ≪≫ (e.app _).symm) by
        simp only [Functor.mapIso_symm, Functor.comp_obj, Functor.whiskeringRight_obj_obj,
          Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, Iso.app_inv, Category.assoc]
        rw [← Functor.map_comp_assoc]; rw [← dsimp% e.inv.naturality]; rw [← Functor.map_comp_assoc]; rw [Sieve.shrinkFunctorUliftFunctorIso_inv_ι]
  rw [K.W.arrow_mk_iso_iff iso]
  apply GrothendieckTopology.W_of_preservesSheafification
  exact F.W_map_of_adjunction_of_isContinuous_aux J K H adj
    (Sieve.shrinkFunctor.{max u₁ v₁ u₂ v₂} S).ι hWS
-/
private lemma isSheaf_of_isContinuous_aux (F : C ⥤ D) [Functor.IsContinuous F J K]
    (G : Dᵒᵖ ⥤ Type max w u₁ v₁ u₂ v₂) (hG : Presieve.IsSheaf K G) :
    Presieve.IsSheaf J (F.op ⋙ G) := by
  let H : (Cᵒᵖ ⥤ Type max u₁ v₁ u₂ v₂) ⥤ Dᵒᵖ ⥤ Type max u₁ v₁ u₂ v₂ := F.op.lan
  let adj : H ⊣ (Functor.whiskeringLeft _ _ _).obj F.op := F.op.lanAdjunction _
  let H' : (Cᵒᵖ ⥤ Type max w u₁ v₁ u₂ v₂) ⥤ Dᵒᵖ ⥤ Type max w u₁ v₁ u₂ v₂ := F.op.lan
  let adj' : H' ⊣ (Functor.whiskeringLeft _ _ _).obj F.op := F.op.lanAdjunction _
  refine Presieve.IsSheaf.comp_of_W_map_of_adjunction _ adj' ?_ _ hG
  intro X S hS
  have hWS : J.W (Sieve.shrinkFunctor.{max u₁ v₁ u₂ v₂} S).ι :=
    Sieve.W_shrinkFunctor_ι_of_mem.{max u₁ v₁ u₂ v₂} _ S hS
  have : K.W _ := Functor.W_map_of_adjunction_of_isContinuous_aux (J := J) K F H adj
    (Sieve.shrinkFunctor.{max u₁ v₁ u₂ v₂} S).ι hWS
  let e : H ⋙ (Functor.whiskeringRight _ _ _).obj uliftFunctor.{w} ≅
      (Functor.whiskeringRight _ _ _).obj uliftFunctor.{w} ⋙ H' :=
    uliftFunctor.{w, max (max (max u₁ u₂) v₁) v₂}.lanCompIsoOfPreserves F.op
  let iso : Arrow.mk (H'.map (Sieve.shrinkFunctor.{max w u₁ v₁ u₂ v₂} S).ι) ≅
      .mk (Functor.whiskerRight
        (H.map (Sieve.shrinkFunctor.{max u₁ v₁ u₂ v₂} S).ι) uliftFunctor.{w}) :=
    Arrow.isoMk' _ _
      (H'.mapIso (Sieve.shrinkFunctorUliftFunctorIso.{max u₁ v₁ u₂ v₂, w} S).symm ≪≫ (e.app _).symm)
(H'.mapIso (shrinkYonedaUliftFunctorIso.{max u₁ v₁ u₂ v₂}.app _).symm ≪≫ (e.app _).symm) by
        simp only [Functor.mapIso_symm, Functor.comp_obj, Functor.whiskeringRight_obj_obj,
          Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, Iso.app_inv, Category.assoc]
        rw [← Functor.map_comp_assoc]; rw [← dsimp% e.inv.naturality]; rw [← Functor.map_comp_assoc]; rw [Sieve.shrinkFunctorUliftFunctorIso_inv_ι]
  rw [K.W.arrow_mk_iso_iff iso]
  apply GrothendieckTopology.W_of_preservesSheafification
  exact F.W_map_of_adjunction_of_isContinuous_aux J K H adj
    (Sieve.shrinkFunctor.{max u₁ v₁ u₂ v₂} S).ι hWS

/--
lemma `op_comp_isSheaf_of_types` / 引理 `op_comp_isSheaf_of_types`

English:
lemma op_comp_isSheaf_of_types
  given: [Functor.IsContinuous F J K] (G : Sheaf K (Type t))
  proof: by
  rw [← Presieve.isSheaf_comp_uliftFunctor_iff.{t]; rw [max u₁ v₁ u₂ v₂}]; rw [← isSheaf_iff_isSheaf_of_type]; rw [Presheaf.isSheaf_of_iso_iff (Functor.associator _ _ _)]; rw [isSheaf_iff_isSheaf_of_type]
  apply isSheaf_of_isContinuous_aux.{t} J K
  rw [Presieve.isSheaf_comp_uliftFunctor_iff]; rw [← isSheaf_iff_isSheaf_of_type]
  exact G.property

中文:
引理 op_comp_isSheaf_of_types
  条件: [函子.是连续 F J K] (G : 层 K (类型 t))
  证明: by
  rw [← Presieve.isSheaf_comp_uliftFunctor_iff.{t]; rw [max u₁ v₁ u₂ v₂}]; rw [← isSheaf_iff_isSheaf_of_type]; rw [Presheaf.isSheaf_of_iso_iff (Functor.associator _ _ _)]; rw [isSheaf_iff_isSheaf_of_type]
  apply isSheaf_of_isContinuous_aux.{t} J K
  rw [Presieve.isSheaf_comp_uliftFunctor_iff]; rw [← isSheaf_iff_isSheaf_of_type]
  exact G.property

Depends on / 依赖: Functor, Functor.associator, G.property, Presheaf, Presheaf.isSheaf_of_iso_iff, Presieve, Presieve.isSheaf_comp_uliftFunctor_iff, associator, isSheaf_comp_uliftFunctor_iff, isSheaf_iff_isSheaf_of_type, isSheaf_of_isContinuous_aux, isSheaf_of_iso_iff, property
-/
lemma op_comp_isSheaf_of_types [Functor.IsContinuous F J K] (G : Sheaf K (Type t)) :
    Presieve.IsSheaf J (F.op ⋙ G.obj) := by
  rw [← Presieve.isSheaf_comp_uliftFunctor_iff.{t]; rw [max u₁ v₁ u₂ v₂}]; rw [← isSheaf_iff_isSheaf_of_type]; rw [Presheaf.isSheaf_of_iso_iff (Functor.associator _ _ _)]; rw [isSheaf_iff_isSheaf_of_type]
  apply isSheaf_of_isContinuous_aux.{t} J K
  rw [Presieve.isSheaf_comp_uliftFunctor_iff]; rw [← isSheaf_iff_isSheaf_of_type]
  exact G.property

/--
lemma `op_comp_isSheaf` / 引理 `op_comp_isSheaf`

English:
lemma op_comp_isSheaf
  given: [Functor.IsContinuous F J K] (G : Sheaf K A)
  proof: fun T => F.op_comp_isSheaf_of_types J K ⟨_, (isSheaf_iff_isSheaf_of_type _ _).2 (G.property T)⟩

中文:
引理 op_comp_isSheaf
  条件: [函子.是连续 F J K] (G : 层 K A)
  证明: fun T => F.op_comp_isSheaf_of_types J K ⟨_, (isSheaf_iff_isSheaf_of_type _ _).2 (G.property T)⟩

Depends on / 依赖: F.op_comp_isSheaf_of_types, G.property, isSheaf_iff_isSheaf_of_type, op_comp_isSheaf_of_types, property
-/
lemma op_comp_isSheaf [Functor.IsContinuous F J K] (G : Sheaf K A) :
    Presheaf.IsSheaf J (F.op ⋙ G.obj) :=
  fun T => F.op_comp_isSheaf_of_types J K ⟨_, (isSheaf_iff_isSheaf_of_type _ _).2 (G.property T)⟩

/--
lemma `op_comp_isSheaf_of_isSheaf` / 引理 `op_comp_isSheaf_of_isSheaf`

English:
lemma op_comp_isSheaf_of_isSheaf
  given: [IsContinuous F J K] (P : Dᵒᵖ ⥤ A) (h : Presheaf.IsSheaf K P)
  proof: F.op_comp_isSheaf J K ⟨P, h⟩

中文:
引理 op_comp_isSheaf_of_isSheaf
  条件: [是连续 F J K] (P : Dᵒᵖ ⥤ A) (h : 预层.是层 K P)
  证明: F.op_comp_isSheaf J K ⟨P, h⟩

Depends on / 依赖: F.op_comp_isSheaf, op_comp_isSheaf
-/
lemma op_comp_isSheaf_of_isSheaf [IsContinuous F J K] (P : Dᵒᵖ ⥤ A) (h : Presheaf.IsSheaf K P) :
    Presheaf.IsSheaf J (F.op ⋙ P) :=
  F.op_comp_isSheaf J K ⟨P, h⟩

variable {K} in
/--
lemma `op_comp_isSheaf_of_isSheaf_type` / 引理 `op_comp_isSheaf_of_isSheaf_type`

English:
lemma op_comp_isSheaf_of_isSheaf_type
  statement: [F.IsContinuous J K] {G : Dᵒᵖ ⥤ Type*}
  proof: by
  rw [← isSheaf_iff_isSheaf_of_type] at h ⊢
  exact F.op_comp_isSheaf_of_isSheaf _ _ _ h

中文:
引理 op_comp_isSheaf_of_isSheaf_type
  结论: [F.是连续 J K] {G : Dᵒᵖ ⥤ 类型}
  证明: by
  rw [← isSheaf_iff_isSheaf_of_type] at h ⊢
  exact F.op_comp_isSheaf_of_isSheaf _ _ _ h

Depends on / 依赖: F.op_comp_isSheaf_of_isSheaf, isSheaf_iff_isSheaf_of_type, op_comp_isSheaf_of_isSheaf
-/
lemma op_comp_isSheaf_of_isSheaf_type [F.IsContinuous J K] {G : Dᵒᵖ ⥤ Type*}
    (h : Presieve.IsSheaf K G) :
    Presieve.IsSheaf J (F.op ⋙ G) := by
  rw [← isSheaf_iff_isSheaf_of_type] at h ⊢
  exact F.op_comp_isSheaf_of_isSheaf _ _ _ h

/--
lemma `W_map_of_adjunction_of_isContinuous` / 引理 `W_map_of_adjunction_of_isContinuous`

English:
lemma W_map_of_adjunction_of_isContinuous
  statement: (F : C ⥤ D) (H : (Cᵒᵖ ⥤ A) ⥤ (Dᵒᵖ ⥤ A))
  proof: by
  intro U hU
  rw [adj.map_comp_bijective_iff]
  exact hf _ (F.op_comp_isSheaf_of_isSheaf _ _ _ hU)

中文:
引理 W_map_of_adjunction_of_isContinuous
  结论: (F : C ⥤ D) (H : (Cᵒᵖ ⥤ A) ⥤ (Dᵒᵖ ⥤ A))
  证明: by
  intro U hU
  rw [adj.map_comp_bijective_iff]
  exact hf _ (F.op_comp_isSheaf_of_isSheaf _ _ _ hU)

Depends on / 依赖: F.op_comp_isSheaf_of_isSheaf, adj.map_comp_bijective_iff, map_comp_bijective_iff, op_comp_isSheaf_of_isSheaf
-/
lemma W_map_of_adjunction_of_isContinuous (F : C ⥤ D) (H : (Cᵒᵖ ⥤ A) ⥤ (Dᵒᵖ ⥤ A))
    (adj : H ⊣ (Functor.whiskeringLeft _ _ _).obj F.op)
    [Functor.IsContinuous F J K] {G G' : Cᵒᵖ ⥤ A} (f : G ⟶ G') (hf : J.W f) :
    K.W (H.map f) := by
  intro U hU
  rw [adj.map_comp_bijective_iff]
  exact hf _ (F.op_comp_isSheaf_of_isSheaf _ _ _ hU)

/--
lemma `isContinuous_of_iso` / 引理 `isContinuous_of_iso`

English:
lemma isContinuous_of_iso
  statement: {F₁ F₂ : C ⥤ D} (e : F₁ ≅ F₂)
  proof: Presieve.isSheaf_iso J (isoWhiskerRight (NatIso.op e.symm) _)
      (F₁.op_comp_isSheaf_of_types J K G)

中文:
引理 isContinuous_of_iso
  结论: {F₁ F₂ : C ⥤ D} (e : F₁ ≅ F₂)
  证明: Presieve.isSheaf_iso J (isoWhiskerRight (NatIso.op e.symm) _)
      (F₁.op_comp_isSheaf_of_types J K G)

Depends on / 依赖: NatIso, NatIso.op, Presieve, Presieve.isSheaf_iso, e.symm, isSheaf_iso, isoWhiskerRight, op_comp_isSheaf_of_types
-/
lemma isContinuous_of_iso {F₁ F₂ : C ⥤ D} (e : F₁ ≅ F₂)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [Functor.IsContinuous F₁ J K] : Functor.IsContinuous F₂ J K where
  op_comp_isSheaf_of_types G :=
    Presieve.isSheaf_iso J (isoWhiskerRight (NatIso.op e.symm) _)
      (F₁.op_comp_isSheaf_of_types J K G)

/--
Instance `isContinuous_id` / 实例 `isContinuous_id`

English:
instance isContinuous_id
  signature: : Functor.IsContinuous (𝟭 C) J J where
  body: (isSheaf_iff_isSheaf_of_type _ _).1 G.2

中文:
实例 isContinuous_id
  签名: : 函子.是连续 (𝟭 C) J J where
  定义体: (isSheaf_iff_isSheaf_of_type _ _).1 G.2

Depends on / 依赖: isSheaf_iff_isSheaf_of_type
-/
instance isContinuous_id : Functor.IsContinuous (𝟭 C) J J where
  op_comp_isSheaf_of_types G := (isSheaf_iff_isSheaf_of_type _ _).1 G.2

/--
lemma `isContinuous_comp` / 引理 `isContinuous_comp`

English:
lemma isContinuous_comp
  statement: (F₁ : C ⥤ D) (F₂ : D ⥤ E) (J : GrothendieckTopology C)
  proof: F₁.op_comp_isSheaf_of_types J K
      ⟨_,(isSheaf_iff_isSheaf_of_type _ _).2 (F₂.op_comp_isSheaf_of_types K L G)⟩

中文:
引理 isContinuous_comp
  结论: (F₁ : C ⥤ D) (F₂ : D ⥤ E) (J : Grothendieck拓扑 C)
  证明: F₁.op_comp_isSheaf_of_types J K
      ⟨_,(isSheaf_iff_isSheaf_of_type _ _).2 (F₂.op_comp_isSheaf_of_types K L G)⟩

Depends on / 依赖: isSheaf_iff_isSheaf_of_type, op_comp_isSheaf_of_types
-/
lemma isContinuous_comp (F₁ : C ⥤ D) (F₂ : D ⥤ E) (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) (L : GrothendieckTopology E)
    [Functor.IsContinuous F₁ J K] [Functor.IsContinuous F₂ K L] :
    Functor.IsContinuous (F₁ ⋙ F₂) J L where
  op_comp_isSheaf_of_types G :=
    F₁.op_comp_isSheaf_of_types J K
      ⟨_,(isSheaf_iff_isSheaf_of_type _ _).2 (F₂.op_comp_isSheaf_of_types K L G)⟩

/--
lemma `isContinuous_comp'` / 引理 `isContinuous_comp'`

English:
lemma isContinuous_comp'
  statement: {F₁ : C ⥤ D} {F₂ : D ⥤ E} {F₁₂ : C ⥤ E}
  proof: by
  have := Functor.isContinuous_comp F₁ F₂ J K L
  apply Functor.isContinuous_of_iso e

中文:
引理 isContinuous_comp'
  结论: {F₁ : C ⥤ D} {F₂ : D ⥤ E} {F₁₂ : C ⥤ E}
  证明: by
  have := Functor.isContinuous_comp F₁ F₂ J K L
  apply Functor.isContinuous_of_iso e

Depends on / 依赖: Functor, Functor.isContinuous_comp, Functor.isContinuous_of_iso, isContinuous_comp, isContinuous_of_iso
-/
lemma isContinuous_comp' {F₁ : C ⥤ D} {F₂ : D ⥤ E} {F₁₂ : C ⥤ E}
    (e : F₁ ⋙ F₂ ≅ F₁₂) (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) (L : GrothendieckTopology E)
    [Functor.IsContinuous F₁ J K] [Functor.IsContinuous F₂ K L] :
    Functor.IsContinuous F₁₂ J L := by
  have := Functor.isContinuous_comp F₁ F₂ J K L
  apply Functor.isContinuous_of_iso e

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Functor.IsContinuous
  signature: F J K] :
  body: by
  assumption

中文:
实例 [函子.是连续
  签名: F J K] :
  定义体: by
  assumption
-/
instance [Functor.IsContinuous F J K] :
    Functor.IsContinuous (F ⋙ 𝟭 D) J K := by
  assumption

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Functor.IsContinuous
  signature: F J K] :
  body: by
  assumption

中文:
实例 [函子.是连续
  签名: F J K] :
  定义体: by
  assumption
-/
instance [Functor.IsContinuous F J K] :
    Functor.IsContinuous (𝟭 C ⋙ F) J K := by
  assumption

/--
lemma `isContinuous_toGrothendieck_of_pullbacksPreservedBy` / 引理 `isContinuous_toGrothendieck_of_pullbacksPreservedBy`

English:
lemma isContinuous_toGrothendieck_of_pullbacksPreservedBy
  statement: (J : Precoverage C)
  proof: fun ⟨G, H⟩ => by
    rw [isSheaf_iff_isSheaf_of_type] at H
    rw [← Precoverage.toGrothendieck_toCoverage]; rw [Presieve.isSheaf_coverage] at H ⊢
    intro X R hR
    have : F.PreservesPairwisePullbacks R := J.preservesPairwisePullbacks_of_mem hR
    have : R.HasPairwisePullbacks := J.hasPairwisePullbacks_of_mem hR
    rw [Presieve.IsSheafFor.comp_iff_of_preservesPairwisePullbacks]
    exact H _ (h _ hR)

中文:
引理 isContinuous_toGrothendieck_of_pullbacksPreservedBy
  结论: (J : Precoverage C)
  证明: fun ⟨G, H⟩ => by
    rw [isSheaf_iff_isSheaf_of_type] at H
    rw [← Precoverage.toGrothendieck_toCoverage]; rw [Presieve.isSheaf_coverage] at H ⊢
    intro X R hR
    have : F.PreservesPairwisePullbacks R := J.preservesPairwisePullbacks_of_mem hR
    have : R.HasPairwisePullbacks := J.hasPairwisePullbacks_of_mem hR
    rw [Presieve.IsSheafFor.comp_iff_of_preservesPairwisePullbacks]
    exact H _ (h _ hR)

Depends on / 依赖: F.PreservesPairwisePullbacks, HasPairwisePullbacks, IsSheafFor, J.hasPairwisePullbacks_of_mem, J.preservesPairwisePullbacks_of_mem, Precoverage, Precoverage.toGrothendieck_toCoverage, PreservesPairwisePullbacks, Presieve, Presieve.IsSheafFor.comp_iff_of_preservesPairwisePullbacks, Presieve.isSheaf_coverage, R.HasPairwisePullbacks, comp_iff_of_preservesPairwisePullbacks, hasPairwisePullbacks_of_mem, isSheaf_coverage, isSheaf_iff_isSheaf_of_type, preservesPairwisePullbacks_of_mem, toGrothendieck_toCoverage
-/
lemma isContinuous_toGrothendieck_of_pullbacksPreservedBy (J : Precoverage C)
    (K : Precoverage D) [J.IsStableUnderBaseChange] [J.HasPullbacks] [K.IsStableUnderBaseChange]
    [K.HasPullbacks] [J.PullbacksPreservedBy F] (h : J <= K.comap F) :
    Functor.IsContinuous F J.toGrothendieck K.toGrothendieck where
  op_comp_isSheaf_of_types := fun ⟨G, H⟩ => by
    rw [isSheaf_iff_isSheaf_of_type] at H
    rw [← Precoverage.toGrothendieck_toCoverage]; rw [Presieve.isSheaf_coverage] at H ⊢
    intro X R hR
    have : F.PreservesPairwisePullbacks R := J.preservesPairwisePullbacks_of_mem hR
    have : R.HasPairwisePullbacks := J.hasPairwisePullbacks_of_mem hR
    rw [Presieve.IsSheafFor.comp_iff_of_preservesPairwisePullbacks]
    exact H _ (h _ hR)

section

/--
lemma `op_comp_isSheaf_of_preservesOneHypercovers` / 引理 `op_comp_isSheaf_of_preservesOneHypercovers`

English:
lemma op_comp_isSheaf_of_preservesOneHypercovers
  proof: by
  rw [Presheaf.isSheaf_iff_of_isGeneratedByOneHypercovers.{w}]
  intro X E
  exact ⟨(E.toPreOneHypercover.isLimitMapMultiforkEquiv F P)
    ((E.map F K).isLimitMultifork ⟨P, hP⟩)⟩

中文:
引理 op_comp_isSheaf_of_preservesOneHypercovers
  证明: by
  rw [Presheaf.isSheaf_iff_of_isGeneratedByOneHypercovers.{w}]
  intro X E
  exact ⟨(E.toPreOneHypercover.isLimitMapMultiforkEquiv F P)
    ((E.map F K).isLimitMultifork ⟨P, hP⟩)⟩

Depends on / 依赖: E.map, E.toPreOneHypercover.isLimitMapMultiforkEquiv, Presheaf, Presheaf.isSheaf_iff_of_isGeneratedByOneHypercovers, isLimitMapMultiforkEquiv, isLimitMultifork, isSheaf_iff_of_isGeneratedByOneHypercovers, toPreOneHypercover
-/
lemma op_comp_isSheaf_of_preservesOneHypercovers
    [PreservesOneHypercovers.{w} F J K] [GrothendieckTopology.IsGeneratedByOneHypercovers.{w} J]
    (P : Dᵒᵖ ⥤ A) (hP : Presheaf.IsSheaf K P) :
    Presheaf.IsSheaf J (F.op ⋙ P) := by
  rw [Presheaf.isSheaf_iff_of_isGeneratedByOneHypercovers.{w}]
  intro X E
  exact ⟨(E.toPreOneHypercover.isLimitMapMultiforkEquiv F P)
    ((E.map F K).isLimitMultifork ⟨P, hP⟩)⟩

/--
lemma `isContinuous_of_preservesOneHypercovers` / 引理 `isContinuous_of_preservesOneHypercovers`

English:
lemma isContinuous_of_preservesOneHypercovers
  proof: by
    rintro ⟨P, hP⟩
    rw [← isSheaf_iff_isSheaf_of_type]
    exact F.op_comp_isSheaf_of_preservesOneHypercovers J K P hP

中文:
引理 isContinuous_of_preservesOneHypercovers
  证明: by
    rintro ⟨P, hP⟩
    rw [← isSheaf_iff_isSheaf_of_type]
    exact F.op_comp_isSheaf_of_preservesOneHypercovers J K P hP

Depends on / 依赖: F.op_comp_isSheaf_of_preservesOneHypercovers, isSheaf_iff_isSheaf_of_type, op_comp_isSheaf_of_preservesOneHypercovers
-/
lemma isContinuous_of_preservesOneHypercovers
    [PreservesOneHypercovers.{w} F J K] [GrothendieckTopology.IsGeneratedByOneHypercovers.{w} J] :
    IsContinuous F J K where
  op_comp_isSheaf_of_types := by
    rintro ⟨P, hP⟩
    rw [← isSheaf_iff_isSheaf_of_type]
    exact F.op_comp_isSheaf_of_preservesOneHypercovers J K P hP

end

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [PreservesOneHypercovers.{max
  signature: u₁ v₁} F J K] :
  body: isContinuous_of_preservesOneHypercovers.{max u₁ v₁} F J K

中文:
实例 [PreservesOneHypercovers.{最大值
  签名: u₁ v₁} F J K] :
  定义体: isContinuous_of_preservesOneHypercovers.{max u₁ v₁} F J K

Depends on / 依赖: isContinuous_of_preservesOneHypercovers
-/
instance [PreservesOneHypercovers.{max u₁ v₁} F J K] :
    IsContinuous F J K :=
  isContinuous_of_preservesOneHypercovers.{max u₁ v₁} F J K

variable (A)
variable [Functor.IsContinuous F J K]

/-- The induced functor `Sheaf K A ⥤ Sheaf J A` given by `F.op ⋙ _`
if `F` is a continuous functor.
-/
@[simps!]
/--
Definition of `sheafPushforwardContinuous` / `sheafPushforwardContinuous` 的定义

English:
definition sheafPushforwardContinuous
  signature: : Sheaf K A ⥤ Sheaf J A
  body: ObjectProperty.lift _
    (sheafToPresheaf _ _ ⋙ (whiskeringLeft _ _ _).obj F.op)
    (F.op_comp_isSheaf J K)

中文:
定义 sheafPushforwardContinuous
  签名: : 层 K A ⥤ 层 J A
  定义体: ObjectProperty.lift _
    (sheafToPresheaf _ _ ⋙ (whiskeringLeft _ _ _).obj F.op)
    (F.op_comp_isSheaf J K)

Depends on / 依赖: F.op, F.op_comp_isSheaf, ObjectProperty, ObjectProperty.lift, op_comp_isSheaf, sheafToPresheaf, whiskeringLeft
-/
def sheafPushforwardContinuous : Sheaf K A ⥤ Sheaf J A :=
  ObjectProperty.lift _
    (sheafToPresheaf _ _ ⋙ (whiskeringLeft _ _ _).obj F.op)
    (F.op_comp_isSheaf J K)

/-- The functor `F.sheafPushforwardContinuous A J K : Sheaf K A ⥤ Sheaf J A`
is induced by the precomposition with `F.op`. -/
@[simps!]
/--
Definition of `sheafPushforwardContinuousCompSheafToPresheafIso` / `sheafPushforwardContinuousCompSheafToPresheafIso` 的定义

English:
definition sheafPushforwardContinuousCompSheafToPresheafIso
  signature: :
  body: Iso.refl _

中文:
定义 sheafPushforwardContinuousCompSheafToPresheafIso
  签名: :
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def sheafPushforwardContinuousCompSheafToPresheafIso :
    F.sheafPushforwardContinuous A J K ⋙ sheafToPresheaf J A ≅
      sheafToPresheaf K A ⋙ (whiskeringLeft _ _ _).obj F.op := Iso.refl _

/-- The functor `sheafPushforwardContinuous` corresponding to the identity functor
identifies to the identity functor. -/
@[simps!]
/--
Definition of `sheafPushforwardContinuousId` / `sheafPushforwardContinuousId` 的定义

English:
definition sheafPushforwardContinuousId
  signature: :
  body: Iso.refl _

中文:
定义 sheafPushforwardContinuousId
  签名: :
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def sheafPushforwardContinuousId :
    sheafPushforwardContinuous (𝟭 C) A J J ≅ 𝟭 _ := Iso.refl _

/-- The composition of two pushforward functors on sheaves identifies to
the pushforward for the composition of the two functors. -/
@[simps!]
/--
Definition of `sheafPushforwardContinuousComp` / `sheafPushforwardContinuousComp` 的定义

English:
definition sheafPushforwardContinuousComp
  signature: [IsContinuous G K L]
  body: isContinuous_comp F G J K L
    sheafPushforwardContinuous G A K L ⋙ sheafPushforwardContinuous F A J K ≅
    sheafPushforwardContinuous (F ⋙ G) A J L := Iso.refl _

中文:
定义 sheafPushforwardContinuousComp
  签名: [是连续 G K L]
  定义体: isContinuous_comp F G J K L
    sheafPushforwardContinuous G A K L ⋙ sheafPushforwardContinuous F A J K ≅
    sheafPushforwardContinuous (F ⋙ G) A J L := Iso.refl _

Depends on / 依赖: isContinuous_comp
-/
def sheafPushforwardContinuousComp [IsContinuous G K L] :
    letI := isContinuous_comp F G J K L
    sheafPushforwardContinuous G A K L ⋙ sheafPushforwardContinuous F A J K ≅
    sheafPushforwardContinuous (F ⋙ G) A J L := Iso.refl _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
variable {F F'} in
/-- The action of a natural transformation on pushforward functors of sheaves. -/
@[simps]
/--
Definition of `sheafPushforwardContinuousNatTrans` / `sheafPushforwardContinuousNatTrans` 的定义

English:
definition sheafPushforwardContinuousNatTrans
  signature: [IsContinuous F' J K]
  body: ⟨whiskerRight (NatTrans.op τ) _⟩

中文:
定义 sheafPushforwardContinuous自然数Trans
  签名: [是连续 F' J K]
  定义体: ⟨whiskerRight (NatTrans.op τ) _⟩

Depends on / 依赖: NatTrans, NatTrans.op, whiskerRight
-/
def sheafPushforwardContinuousNatTrans [IsContinuous F' J K] :
    sheafPushforwardContinuous F' A J K ⟶ sheafPushforwardContinuous F A J K where
  app M := ⟨whiskerRight (NatTrans.op τ) _⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
variable {F F'} in
/-- The action of a natural isomorphism on pushforward functors of sheaves. -/
@[simps]
/--
Definition of `sheafPushforwardContinuousIso` / `sheafPushforwardContinuousIso` 的定义

English:
definition sheafPushforwardContinuousIso
  signature: [IsContinuous F' J K]
  body: sheafPushforwardContinuousNatTrans e.inv _ _ _
  inv := sheafPushforwardContinuousNatTrans e.hom _ _ _
  hom_inv_id := by ext; simp [← Functor.map_comp, ← op_comp]
  inv_hom_id := by ext; simp [← Functor.map_comp, ← op_comp]

中文:
定义 sheafPushforwardContinuousIso
  签名: [是连续 F' J K]
  定义体: sheafPushforwardContinuousNatTrans e.inv _ _ _
  inv := sheafPushforwardContinuousNatTrans e.hom _ _ _
  hom_inv_id := by ext; simp [← Functor.map_comp, ← op_comp]
  inv_hom_id := by ext; simp [← Functor.map_comp, ← op_comp]

Depends on / 依赖: e.inv, sheafPushforwardContinuousNatTrans
-/
def sheafPushforwardContinuousIso [IsContinuous F' J K] :
    sheafPushforwardContinuous F A J K ≅ sheafPushforwardContinuous F' A J K where
  hom := sheafPushforwardContinuousNatTrans e.inv _ _ _
  inv := sheafPushforwardContinuousNatTrans e.hom _ _ _
  hom_inv_id := by ext; simp [← Functor.map_comp, ← op_comp]
  inv_hom_id := by ext; simp [← Functor.map_comp, ← op_comp]

set_option backward.isDefEq.respectTransparency.types false in
/-- If a continuous functor between sites is isomorphic to the identity functor,
then the corresponding pushforward functor on sheaves identifies to the
identity functor. -/
@[simps!]
/--
Definition of `sheafPushforwardContinuousId'` / `sheafPushforwardContinuousId'` 的定义

English:
definition sheafPushforwardContinuousId'
  signature: [IsContinuous F'' J J]
  body: sheafPushforwardContinuousIso eF'' _ _ _ ≪≫ sheafPushforwardContinuousId _ _

中文:
定义 sheafPushforwardContinuousId'
  签名: [是连续 F'' J J]
  定义体: sheafPushforwardContinuousIso eF'' _ _ _ ≪≫ sheafPushforwardContinuousId _ _

Depends on / 依赖: sheafPushforwardContinuousId, sheafPushforwardContinuousIso
-/
def sheafPushforwardContinuousId' [IsContinuous F'' J J] :
    sheafPushforwardContinuous F'' A J J ≅ 𝟭 _ :=
  sheafPushforwardContinuousIso eF'' _ _ _ ≪≫ sheafPushforwardContinuousId _ _

set_option backward.isDefEq.respectTransparency.types false in
variable {F G} in
/-- When we have an isomorphism `F ⋙ G ≅ FG` between continuous functors
between sites, the composition of the pushforward functors for
`G` and `F` identifies to the pushforward functor for `FG`. -/
@[simps!]
/--
Definition of `sheafPushforwardContinuousComp'` / `sheafPushforwardContinuousComp'` 的定义

English:
definition sheafPushforwardContinuousComp'
  body: letI := isContinuous_comp F G J K L
  sheafPushforwardContinuousComp _ _ _ _ _ _ ≪≫ sheafPushforwardContinuousIso eFG _ _ _

中文:
定义 sheafPushforwardContinuousComp'
  定义体: letI := isContinuous_comp F G J K L
  sheafPushforwardContinuousComp _ _ _ _ _ _ ≪≫ sheafPushforwardContinuousIso eFG _ _ _

Depends on / 依赖: _of_subset, eRk_eq_encard, encard_eq_eRk, eq_of_subset_of_encard_le, h.eRk_eq_encard.symm, h.indep, h.subset, hI.subset_isBasis, hIfin.eq_of_subset_of_encard_le, hJ.encard_eq_eRk.trans, hcard.symm, isContinuous_comp, sheafPushforwardContinuousComp, sheafPushforwardContinuousIso, subset, subset_isBasis
-/
def sheafPushforwardContinuousComp'
    [IsContinuous G K L] [IsContinuous FG J L] :
    sheafPushforwardContinuous G A K L ⋙ sheafPushforwardContinuous F A J K ≅
    sheafPushforwardContinuous FG A J L :=
  letI := isContinuous_comp F G J K L
  sheafPushforwardContinuousComp _ _ _ _ _ _ ≪≫ sheafPushforwardContinuousIso eFG _ _ _

end Functor

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If `F ⊣ G` is an adjunction between continuous functors, the associated
pushforwards on sheaves are adjoint. -/
@[simps!]
/--
Definition of `Adjunction.sheafPushforwardContinuous` / `Adjunction.sheafPushforwardContinuous` 的定义

English:
definition Adjunction.sheafPushforwardContinuous
  signature: {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
  body: { hom := (adj.op.whiskerLeft _).unit.app P.obj }
  counit.app P := { hom := (adj.op.whiskerLeft _).counit.app P.obj }
  left_triangle_components P := by
    ext : 1
    exact (adj.op.whiskerLeft _).left_triangle_components P.obj
  right_triangle_components P := by
    ext : 1
    exact (adj.op.whiskerLeft _).right_triangle_components P.obj

中文:
定义 伴随.sheafPushforwardContinuous
  签名: {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
  定义体: { hom := (adj.op.whiskerLeft _).unit.app P.obj }
  counit.app P := { hom := (adj.op.whiskerLeft _).counit.app P.obj }
  left_triangle_components P := by
    ext : 1
    exact (adj.op.whiskerLeft _).left_triangle_components P.obj
  right_triangle_components P := by
    ext : 1
    exact (adj.op.whiskerLeft _).right_triangle_components P.obj

Depends on / 依赖: P.obj, adj.op.whiskerLeft, unit.app, whiskerLeft
-/
def Adjunction.sheafPushforwardContinuous {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) [F.IsContinuous J K]
    [G.IsContinuous K J] :
    F.sheafPushforwardContinuous E J K ⊣ G.sheafPushforwardContinuous E K J where
  unit.app P := { hom := (adj.op.whiskerLeft _).unit.app P.obj }
  counit.app P := { hom := (adj.op.whiskerLeft _).counit.app P.obj }
  left_triangle_components P := by
    ext : 1
    exact (adj.op.whiskerLeft _).left_triangle_components P.obj
  right_triangle_components P := by
    ext : 1
    exact (adj.op.whiskerLeft _).right_triangle_components P.obj

end CategoryTheory
