/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.EpiMono
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# Families of functors which jointly reflect isomorphisms

Let `Fᵢ : C ⥤ Dᵢ` be a family of functors. The family is said to jointly reflect
isomorphisms (resp. monomorphisms, resp. epimorphisms) if every `f : X ⟶ Y`
in `C` for which `Fᵢ.map f` is an isomorphism (resp. monomorphism, resp. epimorphism)
for all `i` is an isomorphism.

-/

public section

namespace CategoryTheory

open Category Limits

variable {C : Type*} [Category C] {I : Type*} {D : I -> Type*} [forall i, Category (D i)]

/--
Definition of `JointlyReflectIsomorphisms` / `JointlyReflectIsomorphisms` 的定义

English:
structure JointlyReflectIsomorphisms
  parameters: (F : forall i, C ⥤ D i)
  axioms and operations (1):
    - isIso({X Y : C} (f : X ⟶ Y) [forall i, IsIso ((F i).map f)]) : IsIso f

中文:
结构 JointlyReflectIsomorphisms
  参数: (F : 对任意 i, C ⥤ D i)
  公理与运算 (1 个):
    - isIso({X Y : C} (f : X ⟶ Y) [对任意 i, IsIso ((F i).map f)]) : IsIso f
-/
structure JointlyReflectIsomorphisms (F : forall i, C ⥤ D i) : Prop where
  isIso {X Y : C} (f : X ⟶ Y) [forall i, IsIso ((F i).map f)] : IsIso f

/--
Definition of `JointlyReflectMonomorphisms` / `JointlyReflectMonomorphisms` 的定义

English:
structure JointlyReflectMonomorphisms
  parameters: (F : forall i, C ⥤ D i)
  axioms and operations (1):
    - mono({X Y : C} (f : X ⟶ Y) [forall i, Mono ((F i).map f)]) : Mono f

中文:
结构 JointlyReflectMonomorphisms
  参数: (F : 对任意 i, C ⥤ D i)
  公理与运算 (1 个):
    - mono({X Y : C} (f : X ⟶ Y) [对任意 i, Mono ((F i).map f)]) : Mono f
-/
structure JointlyReflectMonomorphisms (F : forall i, C ⥤ D i) : Prop where
  mono {X Y : C} (f : X ⟶ Y) [forall i, Mono ((F i).map f)] : Mono f

/--
Definition of `JointlyReflectEpimorphisms` / `JointlyReflectEpimorphisms` 的定义

English:
structure JointlyReflectEpimorphisms
  parameters: (F : forall i, C ⥤ D i)
  axioms and operations (1):
    - epi({X Y : C} (f : X ⟶ Y) [forall i, Epi ((F i).map f)]) : Epi f

中文:
结构 JointlyReflectEpimorphisms
  参数: (F : 对任意 i, C ⥤ D i)
  公理与运算 (1 个):
    - epi({X Y : C} (f : X ⟶ Y) [对任意 i, Epi ((F i).map f)]) : Epi f
-/
structure JointlyReflectEpimorphisms (F : forall i, C ⥤ D i) : Prop where
  epi {X Y : C} (f : X ⟶ Y) [forall i, Epi ((F i).map f)] : Epi f

/--
Definition of `JointlyFaithful` / `JointlyFaithful` 的定义

English:
structure JointlyFaithful
  parameters: (F : forall i, C ⥤ D i)
  axioms and operations (1):
    - map_injective({X Y : C} {f g : X ⟶ Y} (h : forall i, (F i).map f = (F i).map g)) : f = g

中文:
结构 JointlyFaithful
  参数: (F : 对任意 i, C ⥤ D i)
  公理与运算 (1 个):
    - map_injective({X Y : C} {f g : X ⟶ Y} (h : 对任意 i, (F i).map f = (F i).map g)) : f = g
-/
structure JointlyFaithful (F : forall i, C ⥤ D i) : Prop where
  map_injective {X Y : C} {f g : X ⟶ Y} (h : forall i, (F i).map f = (F i).map g) : f = g

variable {F : forall i, C ⥤ D i}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `JointlyFaithful.of_jointly_reflects_isIso_of_mono` / 引理 `JointlyFaithful.of_jointly_reflects_isIso_of_mono`

English:
lemma JointlyFaithful.of_jointly_reflects_isIso_of_mono
  statement: [HasEqualizers C]
  proof: have :=
      hF (equalizer.ι f g) (fun i => by
        let hc := isLimitForkMapOfIsLimit (F i) _ (equalizerIsEqualizer f g)
        obtain ⟨l, hl⟩ := Fork.IsLimit.lift' hc (𝟙 _) (by simpa using hfg i)
        exact ⟨l, Fork.IsLimit.hom_ext hc (by cat_disch), by cat_disch⟩)
    eq_of_epi_equalizer

中文:
引理 JointlyFaithful.of_jointly_reflects_isIso_of_mono
  结论: [HasEqualizers C]
  证明: have :=
      hF (equalizer.ι f g) (fun i => by
        let hc := isLimitForkMapOfIsLimit (F i) _ (equalizerIsEqualizer f g)
        obtain ⟨l, hl⟩ := Fork.IsLimit.lift' hc (𝟙 _) (by simpa using hfg i)
        exact ⟨l, Fork.IsLimit.hom_ext hc (by cat_disch), by cat_disch⟩)
    eq_of_epi_equalizer

Depends on / 依赖: Fork.IsLimit.hom_ext, Fork.IsLimit.lift, IsLimit, cat_disch, eq_of_epi_equalizer, equalizer, equalizerIsEqualizer, hom_ext, isLimitForkMapOfIsLimit
-/
lemma JointlyFaithful.of_jointly_reflects_isIso_of_mono [HasEqualizers C]
    [forall i, PreservesLimitsOfShape WalkingParallelPair (F i)]
    (hF : forall ⦃X Y : C⦄ (f : X ⟶ Y) [Mono f],
      (forall i, IsIso ((F i).map f)) -> IsIso f) :
    JointlyFaithful F where
  map_injective {X Y} f g hfg :=
    have :=
      hF (equalizer.ι f g) (fun i => by
        let hc := isLimitForkMapOfIsLimit (F i) _ (equalizerIsEqualizer f g)
        obtain ⟨l, hl⟩ := Fork.IsLimit.lift' hc (𝟙 _) (by simpa using hfg i)
        exact ⟨l, Fork.IsLimit.hom_ext hc (by cat_disch), by cat_disch⟩)
    eq_of_epi_equalizer

namespace JointlyReflectIsomorphisms

variable (h : JointlyReflectIsomorphisms F)

include h

/--
lemma `isIso_iff` / 引理 `isIso_iff`

English:
lemma isIso_iff
  given: {X Y : C} (f : X ⟶ Y)
  proof: ⟨fun _ _ => inferInstance, fun _ => h.isIso f⟩

中文:
引理 isIso_iff
  条件: {X Y : C} (f : X ⟶ Y)
  证明: ⟨fun _ _ => inferInstance, fun _ => h.isIso f⟩

Depends on / 依赖: h.isIso
-/
lemma isIso_iff {X Y : C} (f : X ⟶ Y) :
    IsIso f ↔ forall i, IsIso ((F i).map f) :=
  ⟨fun _ _ => inferInstance, fun _ => h.isIso f⟩

/--
lemma `mono` / 引理 `mono`

English:
lemma mono
  statement: {X Y : C} (f : X ⟶ Y) [hf : forall i, Mono ((F i).map f)]
  proof: by
  have hc := pullbackIsPullback f f
  rw [mono_iff_isIso_fst hc]; rw [h.isIso_iff]
  intro i
  exact (mono_iff_isIso_fst ((isLimitMapConePullbackConeEquiv (F i) pullback.condition).1
    (isLimitOfPreserves (F i) hc))).1 (hf i)

中文:
引理 mono
  结论: {X Y : C} (f : X ⟶ Y) [hf : 对任意 i, Mono ((F i).map f)]
  证明: by
  have hc := pullbackIsPullback f f
  rw [mono_iff_isIso_fst hc]; rw [h.isIso_iff]
  intro i
  exact (mono_iff_isIso_fst ((isLimitMapConePullbackConeEquiv (F i) pullback.condition).1
    (isLimitOfPreserves (F i) hc))).1 (hf i)

Depends on / 依赖: condition, h.isIso_iff, isIso_iff, isLimitMapConePullbackConeEquiv, isLimitOfPreserves, mono_iff_isIso_fst, pullback, pullback.condition, pullbackIsPullback
-/
lemma mono {X Y : C} (f : X ⟶ Y) [hf : forall i, Mono ((F i).map f)]
    [forall i, PreservesLimit (cospan f f) (F i)] [HasPullback f f] :
    Mono f := by
  have hc := pullbackIsPullback f f
  rw [mono_iff_isIso_fst hc]; rw [h.isIso_iff]
  intro i
  exact (mono_iff_isIso_fst ((isLimitMapConePullbackConeEquiv (F i) pullback.condition).1
    (isLimitOfPreserves (F i) hc))).1 (hf i)

/--
lemma `jointlyReflectMonomorphisms` / 引理 `jointlyReflectMonomorphisms`

English:
lemma jointlyReflectMonomorphisms
  statement: [forall i, PreservesLimitsOfShape WalkingCospan (F i)]
  proof: h.mono f

中文:
引理 jointlyReflectMonomorphisms
  结论: [对任意 i, PreservesLimitsOfShape WalkingCospan (F i)]
  证明: h.mono f

Depends on / 依赖: h.mono
-/
lemma jointlyReflectMonomorphisms [forall i, PreservesLimitsOfShape WalkingCospan (F i)]
    [HasPullbacks C] :
    JointlyReflectMonomorphisms F where
  mono f _ := h.mono f

/--
lemma `epi` / 引理 `epi`

English:
lemma epi
  statement: {X Y : C} (f : X ⟶ Y) [hf : forall i, Epi ((F i).map f)]
  proof: by
  have hc := pushoutIsPushout f f
  rw [epi_iff_isIso_inl hc]; rw [h.isIso_iff]
  intro i
  exact (epi_iff_isIso_inl ((isColimitMapCoconePushoutCoconeEquiv (F i) pushout.condition).1
    (isColimitOfPreserves (F i) hc))).1 (hf i)

中文:
引理 epi
  结论: {X Y : C} (f : X ⟶ Y) [hf : 对任意 i, Epi ((F i).map f)]
  证明: by
  have hc := pushoutIsPushout f f
  rw [epi_iff_isIso_inl hc]; rw [h.isIso_iff]
  intro i
  exact (epi_iff_isIso_inl ((isColimitMapCoconePushoutCoconeEquiv (F i) pushout.condition).1
    (isColimitOfPreserves (F i) hc))).1 (hf i)

Depends on / 依赖: condition, epi_iff_isIso_inl, h.isIso_iff, isColimitMapCoconePushoutCoconeEquiv, isColimitOfPreserves, isIso_iff, pushout, pushout.condition, pushoutIsPushout
-/
lemma epi {X Y : C} (f : X ⟶ Y) [hf : forall i, Epi ((F i).map f)]
    [forall i, PreservesColimit (span f f) (F i)] [HasPushout f f] : Epi f := by
  have hc := pushoutIsPushout f f
  rw [epi_iff_isIso_inl hc]; rw [h.isIso_iff]
  intro i
  exact (epi_iff_isIso_inl ((isColimitMapCoconePushoutCoconeEquiv (F i) pushout.condition).1
    (isColimitOfPreserves (F i) hc))).1 (hf i)

/--
lemma `jointlyReflectEpimorphisms` / 引理 `jointlyReflectEpimorphisms`

English:
lemma jointlyReflectEpimorphisms
  statement: [forall i, PreservesColimitsOfShape WalkingSpan (F i)]
  proof: h.epi f

中文:
引理 jointlyReflectEpimorphisms
  结论: [对任意 i, PreservesColimitsOfShape WalkingSpan (F i)]
  证明: h.epi f

Depends on / 依赖: h.epi
-/
lemma jointlyReflectEpimorphisms [forall i, PreservesColimitsOfShape WalkingSpan (F i)]
    [HasPushouts C] :
    JointlyReflectEpimorphisms F where
  epi f _ := h.epi f

/--
lemma `jointlyFaithful` / 引理 `jointlyFaithful`

English:
lemma jointlyFaithful
  given: [forall i, PreservesLimitsOfShape WalkingParallelPair (F i)] [HasEqualizers C]
  proof: .of_jointly_reflects_isIso_of_mono (fun _ _ _ _ _ => h.isIso _)

中文:
引理 jointlyFaithful
  条件: [对任意 i, PreservesLimitsOfShape WalkingParallelPair (F i)] [HasEqualizers C]
  证明: .of_jointly_reflects_isIso_of_mono (fun _ _ _ _ _ => h.isIso _)

Depends on / 依赖: h.isIso, of_jointly_reflects_isIso_of_mono
-/
lemma jointlyFaithful [forall i, PreservesLimitsOfShape WalkingParallelPair (F i)] [HasEqualizers C] :
    JointlyFaithful F :=
  .of_jointly_reflects_isIso_of_mono (fun _ _ _ _ _ => h.isIso _)

end JointlyReflectIsomorphisms

/--
lemma `JointlyReflectMonomorphisms.mono_iff` / 引理 `JointlyReflectMonomorphisms.mono_iff`

English:
lemma JointlyReflectMonomorphisms.mono_iff
  statement: (h : JointlyReflectMonomorphisms F)
  proof: ⟨fun _ _ => inferInstance, fun _ => h.mono f⟩

中文:
引理 JointlyReflectMonomorphisms.mono_iff
  结论: (h : JointlyReflectMonomorphisms F)
  证明: ⟨fun _ _ => inferInstance, fun _ => h.mono f⟩

Depends on / 依赖: h.mono
-/
lemma JointlyReflectMonomorphisms.mono_iff (h : JointlyReflectMonomorphisms F)
    [forall i, (F i).PreservesMonomorphisms] {X Y : C} (f : X ⟶ Y) :
    Mono f ↔ forall i, Mono ((F i).map f) :=
  ⟨fun _ _ => inferInstance, fun _ => h.mono f⟩

/--
lemma `JointlyReflectEpimorphisms.epi_iff` / 引理 `JointlyReflectEpimorphisms.epi_iff`

English:
lemma JointlyReflectEpimorphisms.epi_iff
  statement: (h : JointlyReflectEpimorphisms F)
  proof: ⟨fun _ _ => inferInstance, fun _ => h.epi f⟩

中文:
引理 JointlyReflectEpimorphisms.epi_iff
  结论: (h : JointlyReflectEpimorphisms F)
  证明: ⟨fun _ _ => inferInstance, fun _ => h.epi f⟩

Depends on / 依赖: h.epi
-/
lemma JointlyReflectEpimorphisms.epi_iff (h : JointlyReflectEpimorphisms F)
    [forall i, (F i).PreservesEpimorphisms] {X Y : C} (f : X ⟶ Y) :
    Epi f ↔ forall i, Epi ((F i).map f) :=
  ⟨fun _ _ => inferInstance, fun _ => h.epi f⟩

namespace JointlyFaithful

/--
lemma `jointlyReflectMonomorphisms` / 引理 `jointlyReflectMonomorphisms`

English:
lemma jointlyReflectMonomorphisms
  given: (h : JointlyFaithful F)
  proof: ⟨fun {Z} g₁ g₂ hg => h.map_injective (fun i => by
    simp only [← cancel_mono ((F i).map f), ← Functor.map_comp, hg])⟩

中文:
引理 jointlyReflectMonomorphisms
  条件: (h : JointlyFaithful F)
  证明: ⟨fun {Z} g₁ g₂ hg => h.map_injective (fun i => by
    simp only [← cancel_mono ((F i).map f), ← Functor.map_comp, hg])⟩

Depends on / 依赖: Functor, Functor.map_comp, cancel_mono, h.map_injective, map_comp, map_injective
-/
lemma jointlyReflectMonomorphisms (h : JointlyFaithful F) :
    JointlyReflectMonomorphisms F where
  mono {X Y} f _ := ⟨fun {Z} g₁ g₂ hg => h.map_injective (fun i => by
    simp only [← cancel_mono ((F i).map f), ← Functor.map_comp, hg])⟩

/--
lemma `jointlyReflectEpimorphisms` / 引理 `jointlyReflectEpimorphisms`

English:
lemma jointlyReflectEpimorphisms
  given: (h : JointlyFaithful F)
  proof: ⟨fun {Z} g₁ g₂ hg => h.map_injective (fun i => by
    simp only [← cancel_epi ((F i).map f), ← Functor.map_comp, hg])⟩

中文:
引理 jointlyReflectEpimorphisms
  条件: (h : JointlyFaithful F)
  证明: ⟨fun {Z} g₁ g₂ hg => h.map_injective (fun i => by
    simp only [← cancel_epi ((F i).map f), ← Functor.map_comp, hg])⟩

Depends on / 依赖: Functor, Functor.map_comp, cancel_epi, h.map_injective, map_comp, map_injective
-/
lemma jointlyReflectEpimorphisms (h : JointlyFaithful F) :
    JointlyReflectEpimorphisms F where
  epi {X Y} f _ := ⟨fun {Z} g₁ g₂ hg => h.map_injective (fun i => by
    simp only [← cancel_epi ((F i).map f), ← Functor.map_comp, hg])⟩

/--
lemma `jointlyReflectsIsomorphisms` / 引理 `jointlyReflectsIsomorphisms`

English:
lemma jointlyReflectsIsomorphisms
  given: [Balanced C] (h : JointlyFaithful F)
  proof: have := h.jointlyReflectMonomorphisms.mono f
    have := h.jointlyReflectEpimorphisms.epi f
    Balanced.isIso_of_mono_of_epi f

中文:
引理 jointlyReflectsIsomorphisms
  条件: [Balanced C] (h : JointlyFaithful F)
  证明: have := h.jointlyReflectMonomorphisms.mono f
    have := h.jointlyReflectEpimorphisms.epi f
    Balanced.isIso_of_mono_of_epi f

Depends on / 依赖: Balanced, Balanced.isIso_of_mono_of_epi, h.jointlyReflectEpimorphisms.epi, h.jointlyReflectMonomorphisms.mono, isIso_of_mono_of_epi, jointlyReflectEpimorphisms, jointlyReflectMonomorphisms
-/
lemma jointlyReflectsIsomorphisms [Balanced C] (h : JointlyFaithful F) :
    JointlyReflectIsomorphisms F where
  isIso f _ :=
    have := h.jointlyReflectMonomorphisms.mono f
    have := h.jointlyReflectEpimorphisms.epi f
    Balanced.isIso_of_mono_of_epi f

end JointlyFaithful

end CategoryTheory
