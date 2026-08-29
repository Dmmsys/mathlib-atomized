/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Joël Riou, Adam Topaz
-/
module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Sites.JointlySurjective
public import Mathlib.CategoryTheory.Sites.MorphismProperty

/-!

# Site defined by a morphism property

Given a multiplicative morphism property `P` that is stable under base change, we define the
associated precoverage on the category of schemes, where coverings are given
by jointly surjective families of morphisms satisfying `P`.

-/

@[expose] public section

universe v u

open CategoryTheory MorphismProperty Limits

namespace AlgebraicGeometry

namespace Scheme

/--
Definition of `IsJointlySurjectivePreserving` / `IsJointlySurjectivePreserving` 的定义

English:
class IsJointlySurjectivePreserving
  parameters: (P : MorphismProperty Scheme.{u})
  axioms and operations (1):
    - exists_preimage_fst_triplet_of_prop({X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} [HasPullback f g] (hg : P g) (x : X) (y : Y) (h : f x = g y)) : exists a : ↑(pullback f g), pullback.fst f g a = x

中文:
类 IsJointlySurjectivePreserving
  参数: (P : Morphism命题erty Scheme.{u})
  公理与运算 (1 个):
    - exists_preimage_fst_triplet_of_prop({X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} [HasPullback f g] (hg : P g) (x : X) (y : Y) (h : f x = g y)) : 存在 a : ↑(pullback f g), pullback.fst f g a = x
-/
class IsJointlySurjectivePreserving (P : MorphismProperty Scheme.{u}) where
  exists_preimage_fst_triplet_of_prop {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} [HasPullback f g]
    (hg : P g) (x : X) (y : Y) (h : f x = g y) :
    exists a : ↑(pullback f g), pullback.fst f g a = x

variable {P : MorphismProperty Scheme.{u}}

/--
lemma `IsJointlySurjectivePreserving.exists_preimage_snd_triplet_of_prop` / 引理 `IsJointlySurjectivePreserving.exists_preimage_snd_triplet_of_prop`

English:
lemma IsJointlySurjectivePreserving.exists_preimage_snd_triplet_of_prop
  proof: by
  let iso := pullbackSymmetry f g
  have : HasPullback g f := hasPullback_symmetry f g
  obtain ⟨a, ha⟩ := exists_preimage_fst_triplet_of_prop hf y x h.symm
  use (pullbackSymmetry f g).inv a
  rwa [← Scheme.Hom.comp_apply, pullbackSymmetry_inv_comp_snd]

中文:
引理 IsJointlySurjectivePreserving.exists_preimage_snd_triplet_of_prop
  证明: by
  let iso := pullbackSymmetry f g
  have : HasPullback g f := hasPullback_symmetry f g
  obtain ⟨a, ha⟩ := exists_preimage_fst_triplet_of_prop hf y x h.symm
  use (pullbackSymmetry f g).inv a
  rwa [← Scheme.Hom.comp_apply, pullbackSymmetry_inv_comp_snd]

Depends on / 依赖: HasPullback, Scheme, Scheme.Hom.comp_apply, comp_apply, exists_preimage_fst_triplet_of_prop, h.symm, hasPullback_symmetry, pullbackSymmetry, pullbackSymmetry_inv_comp_snd
-/
lemma IsJointlySurjectivePreserving.exists_preimage_snd_triplet_of_prop
    [IsJointlySurjectivePreserving P] {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} [HasPullback f g]
    (hf : P f) (x : X) (y : Y) (h : f x = g y) :
    exists a : ↑(pullback f g), pullback.snd f g a = y := by
  let iso := pullbackSymmetry f g
  have : HasPullback g f := hasPullback_symmetry f g
  obtain ⟨a, ha⟩ := exists_preimage_fst_triplet_of_prop hf y x h.symm
  use (pullbackSymmetry f g).inv a
  rwa [← Scheme.Hom.comp_apply, pullbackSymmetry_inv_comp_snd]

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsJointlySurjectivePreserving @IsOpenImmersion
  body: by
    rw [← show _ = (pullback.fst _ _ : pullback f g ⟶ _).base from
        PreservesPullback.iso_hom_fst Scheme.forgetToTop f g]
    have : x in Set.range (pullback.fst f.base g.base) := by
      rw [TopCat.pullback_fst_range f.base g.base]
      use y
    obtain ⟨a, ha⟩ := this
    use (Preserve

中文:
实例 :
  签名: IsJointlySurjectivePreserving @IsOpenImmersion
  定义体: by
    rw [← show _ = (pullback.fst _ _ : pullback f g ⟶ _).base from
        PreservesPullback.iso_hom_fst Scheme.forgetToTop f g]
    have : x in Set.range (pullback.fst f.base g.base) := by
      rw [TopCat.pullback_fst_range f.base g.base]
      use y
    obtain ⟨a, ha⟩ := this
    use (Preserve

Depends on / 依赖: Iso.inv_hom_id_assoc, PreservesPullback, PreservesPullback.iso, PreservesPullback.iso_hom_fst, Scheme, Scheme.forgetToTop, Set.range, TopCat, TopCat.comp_app, TopCat.pullback_fst_range, comp_app, f.base, forgetToTop, g.base, inv_hom_id_assoc, iso_hom_fst, pullback, pullback.fst, pullback_fst_range
-/
instance : IsJointlySurjectivePreserving @IsOpenImmersion where
  exists_preimage_fst_triplet_of_prop {X Y S f g} _ hg x y h := by
    rw [← show _ = (pullback.fst _ _ : pullback f g ⟶ _).base from
        PreservesPullback.iso_hom_fst Scheme.forgetToTop f g]
    have : x in Set.range (pullback.fst f.base g.base) := by
      rw [TopCat.pullback_fst_range f.base g.base]
      use y
    obtain ⟨a, ha⟩ := this
    use (PreservesPullback.iso Scheme.forgetToTop f g).inv a
    rwa [← TopCat.comp_app, Iso.inv_hom_id_assoc]

/--
Definition of `jointlySurjectivePrecoverage` / `jointlySurjectivePrecoverage` 的定义

English:
abbreviation jointlySurjectivePrecoverage
  signature: : Precoverage Scheme.{u}
  body: Types.jointlySurjectivePrecoverage.comap Scheme.forget

中文:
缩写 jointlySurjectivePrecoverage
  签名: : Precoverage Scheme.{u}
  定义体: Types.jointlySurjectivePrecoverage.comap Scheme.forget

Depends on / 依赖: Scheme, Scheme.forget, Types.jointlySurjectivePrecoverage.comap, forget, jointlySurjectivePrecoverage
-/
abbrev jointlySurjectivePrecoverage : Precoverage Scheme.{u} :=
  Types.jointlySurjectivePrecoverage.comap Scheme.forget

variable (P : MorphismProperty Scheme.{u})

/--
Definition of `precoverage` / `precoverage` 的定义

English:
definition precoverage
  signature: : Precoverage Scheme.{u}
  body: jointlySurjectivePrecoverage ⊓ P.precoverage

@[simp]

中文:
定义 precoverage
  签名: : Precoverage Scheme.{u}
  定义体: jointlySurjectivePrecoverage ⊓ P.precoverage

@[simp]

Depends on / 依赖: P.precoverage, jointlySurjectivePrecoverage, precoverage
-/
def precoverage : Precoverage Scheme.{u} :=
  jointlySurjectivePrecoverage ⊓ P.precoverage

@[simp]
/--
lemma `ofArrows_mem_precoverage_iff` / 引理 `ofArrows_mem_precoverage_iff`

English:
lemma ofArrows_mem_precoverage_iff
  statement: {S : Scheme.{u}} {ι : Type*} {X : ι -> Scheme.{u}}
  proof: by
  simp_rw [← Scheme.forget_map', ← Scheme.forget_obj,
    ← Presieve.ofArrows_mem_comap_jointlySurjectivePrecoverage_iff]
  exact ⟨fun hmem => ⟨hmem.1, fun i => hmem.2 ⟨i⟩⟩, fun h => ⟨h.1, fun {Y} g ⟨i⟩ => h.2 i⟩⟩

@[simp]

中文:
引理 ofArrows_mem_precoverage_iff
  结论: {S : Scheme.{u}} {ι : 类型} {X : ι -> Scheme.{u}}
  证明: by
  simp_rw [← Scheme.forget_map', ← Scheme.forget_obj,
    ← Presieve.ofArrows_mem_comap_jointlySurjectivePrecoverage_iff]
  exact ⟨fun hmem => ⟨hmem.1, fun i => hmem.2 ⟨i⟩⟩, fun h => ⟨h.1, fun {Y} g ⟨i⟩ => h.2 i⟩⟩

@[simp]

Depends on / 依赖: Presieve, Presieve.ofArrows_mem_comap_jointlySurjectivePrecoverage_iff, Scheme, Scheme.forget_map, Scheme.forget_obj, forget_map, forget_obj, ofArrows_mem_comap_jointlySurjectivePrecoverage_iff, simp_rw
-/
lemma ofArrows_mem_precoverage_iff {S : Scheme.{u}} {ι : Type*} {X : ι -> Scheme.{u}}
    {f : forall i, X i ⟶ S} :
    .ofArrows X f in precoverage P S ↔ (forall x, exists i, x in Set.range (f i)) ∧ forall i, P (f i) := by
  simp_rw [← Scheme.forget_map', ← Scheme.forget_obj,
    ← Presieve.ofArrows_mem_comap_jointlySurjectivePrecoverage_iff]
  exact ⟨fun hmem => ⟨hmem.1, fun i => hmem.2 ⟨i⟩⟩, fun h => ⟨h.1, fun {Y} g ⟨i⟩ => h.2 i⟩⟩

@[simp]
/--
lemma `singleton_mem_precoverage_iff` / 引理 `singleton_mem_precoverage_iff`

English:
lemma singleton_mem_precoverage_iff
  given: {X S : Scheme.{u}} (f : X ⟶ S)
  proof: by
  rw [← Presieve.ofArrows_pUnit.{0}]; rw [ofArrows_mem_precoverage_iff]
  aesop

中文:
引理 singleton_mem_precoverage_iff
  条件: {X S : Scheme.{u}} (f : X ⟶ S)
  证明: by
  rw [← Presieve.ofArrows_pUnit.{0}]; rw [ofArrows_mem_precoverage_iff]
  aesop

Depends on / 依赖: Presieve, Presieve.ofArrows_pUnit, ofArrows_mem_precoverage_iff, ofArrows_pUnit
-/
lemma singleton_mem_precoverage_iff {X S : Scheme.{u}} (f : X ⟶ S) :
    Presieve.singleton f in precoverage P S ↔ Function.Surjective f.base ∧ P f := by
  rw [← Presieve.ofArrows_pUnit.{0}]; rw [ofArrows_mem_precoverage_iff]
  aesop

/--
lemma `bot_mem_precoverage` / 引理 `bot_mem_precoverage`

English:
lemma bot_mem_precoverage
  given: (X : Scheme.{u}) [IsEmpty X]
  statement: ⊥ in Scheme.precoverage P X
  proof: ⟨fun x => ‹IsEmpty X›.elim x, P.bot_mem_precoverage _⟩

中文:
引理 bot_mem_precoverage
  条件: (X : Scheme.{u}) [IsEmpty X]
  结论: ⊥ in Scheme.precoverage P X
  证明: ⟨fun x => ‹IsEmpty X›.elim x, P.bot_mem_precoverage _⟩

Depends on / 依赖: IsEmpty, P.bot_mem_precoverage, bot_mem_precoverage
-/
lemma bot_mem_precoverage (X : Scheme.{u}) [IsEmpty X] : ⊥ in Scheme.precoverage P X :=
  ⟨fun x => ‹IsEmpty X›.elim x, P.bot_mem_precoverage _⟩

/--
lemma `precoverage_mono` / 引理 `precoverage_mono`

English:
lemma precoverage_mono
  given: {P Q : MorphismProperty Scheme.{u}} (h : P <= Q)
  proof: by
  grw [precoverage, precoverage, MorphismProperty.precoverage_monotone h]

中文:
引理 precoverage_mono
  条件: {P Q : Morphism命题erty Scheme.{u}} (h : P <= Q)
  证明: by
  grw [precoverage, precoverage, MorphismProperty.precoverage_monotone h]

Depends on / 依赖: MorphismProperty, MorphismProperty.precoverage_monotone, precoverage, precoverage_monotone
-/
lemma precoverage_mono {P Q : MorphismProperty Scheme.{u}} (h : P <= Q) :
    precoverage P <= precoverage Q := by
  grw [precoverage, precoverage, MorphismProperty.precoverage_monotone h]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsStableUnderComposition]
  signature: : (precoverage P).IsStableUnderComposition
  body: by
  dsimp only [precoverage]; infer_instance

中文:
实例 [P.IsStableUnderComposition]
  签名: : (precoverage P).IsStableUnderComposition
  定义体: by
  dsimp only [precoverage]; infer_instance

Depends on / 依赖: infer_instance, precoverage
-/
instance [P.IsStableUnderComposition] : (precoverage P).IsStableUnderComposition := by
  dsimp only [precoverage]; infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.ContainsIdentities]
  signature: [P.RespectsIso]
  body: by
  dsimp only [precoverage]; infer_instance

中文:
实例 [P.ContainsIdentities]
  签名: [P.RespectsIso]
  定义体: by
  dsimp only [precoverage]; infer_instance

Depends on / 依赖: infer_instance, precoverage
-/
instance [P.ContainsIdentities] [P.RespectsIso] : (precoverage P).HasIsos := by
  dsimp only [precoverage]; infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.HasPullbacks]
  signature: : (precoverage P).HasPullbacks where
  body: ⟨fun hg => P.hasPullback _ (hR.2 hg)⟩

中文:
实例 [P.HasPullbacks]
  签名: : (precoverage P).HasPullbacks where
  定义体: ⟨fun hg => P.hasPullback _ (hR.2 hg)⟩

Depends on / 依赖: P.hasPullback, hasPullback
-/
instance [P.HasPullbacks] : (precoverage P).HasPullbacks where
  hasPullbacks_of_mem _ hR := ⟨fun hg => P.hasPullback _ (hR.2 hg)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsJointlySurjectivePreserving
  signature: P] [P.IsStableUnderBaseChange] :
  body: by
    rw [ofArrows_mem_precoverage_iff] at hf ⊢
    refine ⟨fun x => ?_, fun i => P.of_isPullback (H i).flip (hf.2 i)⟩
    obtain ⟨i, y, hy⟩ := hf.1 (g x)
    have := (H i).hasPullback
    obtain ⟨w, hw⟩ := IsJointlySurjectivePreserving.exists_preimage_fst_triplet_of_prop (hf.2 i)
      (f := g) x 

中文:
实例 [IsJointlySurjectivePreserving
  签名: P] [P.IsStableUnderBaseChange] :
  定义体: by
    rw [ofArrows_mem_precoverage_iff] at hf ⊢
    refine ⟨fun x => ?_, fun i => P.of_isPullback (H i).flip (hf.2 i)⟩
    obtain ⟨i, y, hy⟩ := hf.1 (g x)
    have := (H i).hasPullback
    obtain ⟨w, hw⟩ := IsJointlySurjectivePreserving.exists_preimage_fst_triplet_of_prop (hf.2 i)
      (f := g) x 

Depends on / 依赖: IsJointlySurjectivePreserving, IsJointlySurjectivePreserving.exists_preimage_fst_triplet_of_prop, P.of_isPullback, Scheme, Scheme.Hom.comp_apply, comp_apply, exists_preimage_fst_triplet_of_prop, hasPullback, hy.symm, isoPullback, isoPullback.inv, ofArrows_mem_precoverage_iff, of_isPullback
-/
instance [IsJointlySurjectivePreserving P] [P.IsStableUnderBaseChange] :
    (precoverage P).IsStableUnderBaseChange where
  mem_coverings_of_isPullback {ι} S X f hf Y g T p₁ p₂ H := by
    rw [ofArrows_mem_precoverage_iff] at hf ⊢
    refine ⟨fun x => ?_, fun i => P.of_isPullback (H i).flip (hf.2 i)⟩
    obtain ⟨i, y, hy⟩ := hf.1 (g x)
    have := (H i).hasPullback
    obtain ⟨w, hw⟩ := IsJointlySurjectivePreserving.exists_preimage_fst_triplet_of_prop (hf.2 i)
      (f := g) x y hy.symm
    use i, (H i).isoPullback.inv w
    simpa [← Scheme.Hom.comp_apply]

/--
Definition of `zariskiPrecoverage` / `zariskiPrecoverage` 的定义

English:
abbreviation zariskiPrecoverage
  signature: : Precoverage Scheme.{u}
  body: precoverage @IsOpenImmersion

中文:
缩写 zariskiPrecoverage
  签名: : Precoverage Scheme.{u}
  定义体: precoverage @IsOpenImmersion

Depends on / 依赖: IsOpenImmersion, precoverage
-/
abbrev zariskiPrecoverage : Precoverage Scheme.{u} := precoverage @IsOpenImmersion

end AlgebraicGeometry.Scheme
