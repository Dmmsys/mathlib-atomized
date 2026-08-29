/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.CategoryTheory.Sites.Hypercover.SheafOfTypes
public import Mathlib.CategoryTheory.MorphismProperty.Local

/-!
# Covers in subcanonical topologies

In this file we provide API related to covers in subcanonical topologies.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

namespace GrothendieckTopology.OneHypercover

variable {J : GrothendieckTopology C} [J.Subcanonical]

/--
Definition of `glueMorphisms` / `glueMorphisms` 的定义

English:
definition glueMorphisms
  signature: {S T : C} (E : J.OneHypercover S) (f : forall i, E.X i ⟶ T)
  body: (E.isStronglySheafFor
    (Subcanonical.isSheaf_of_isRepresentable (CategoryTheory.yoneda.obj T))).amalgamate f h

中文:
定义 glueMorphisms
  签名: {S T : C} (E : J.OneHypercover S) (f : 对任意 i, E.X i ⟶ T)
  定义体: (E.isStronglySheafFor
    (Subcanonical.isSheaf_of_isRepresentable (CategoryTheory.yoneda.obj T))).amalgamate f h

Depends on / 依赖: CategoryTheory, CategoryTheory.yoneda.obj, E.isStronglySheafFor, Subcanonical, Subcanonical.isSheaf_of_isRepresentable, amalgamate, isSheaf_of_isRepresentable, isStronglySheafFor, yoneda
-/
noncomputable def glueMorphisms {S T : C} (E : J.OneHypercover S) (f : forall i, E.X i ⟶ T)
    (h : forall ⦃i j : E.I₀⦄ (k : E.I₁ i j), E.p₁ k ≫ f i = E.p₂ k ≫ f j) :
    S ⟶ T :=
  (E.isStronglySheafFor
    (Subcanonical.isSheaf_of_isRepresentable (CategoryTheory.yoneda.obj T))).amalgamate f h

variable {S T : C} (E : J.OneHypercover S) (f : forall i, E.X i ⟶ T)
  (h : forall ⦃i j : E.I₀⦄ (k : E.I₁ i j), E.p₁ k ≫ f i = E.p₂ k ≫ f j)

@[reassoc (attr := simp)]
/--
lemma `f_glueMorphisms` / 引理 `f_glueMorphisms`

English:
lemma f_glueMorphisms
  given: (i : E.I₀)
  statement: E.f i ≫ E.glueMorphisms f h = f i
  proof: (E.isStronglySheafFor
    (Subcanonical.isSheaf_of_isRepresentable (CategoryTheory.yoneda.obj T))).map_amalgamate _ _ i

中文:
引理 f_glueMorphisms
  条件: (i : E.I₀)
  结论: E.f i ≫ E.glueMorphisms f h = f i
  证明: (E.isStronglySheafFor
    (Subcanonical.isSheaf_of_isRepresentable (CategoryTheory.yoneda.obj T))).map_amalgamate _ _ i

Depends on / 依赖: CategoryTheory, CategoryTheory.yoneda.obj, E.isStronglySheafFor, Subcanonical, Subcanonical.isSheaf_of_isRepresentable, isSheaf_of_isRepresentable, isStronglySheafFor, map_amalgamate, yoneda
-/
lemma f_glueMorphisms (i : E.I₀) : E.f i ≫ E.glueMorphisms f h = f i :=
  (E.isStronglySheafFor
    (Subcanonical.isSheaf_of_isRepresentable (CategoryTheory.yoneda.obj T))).map_amalgamate _ _ i

end GrothendieckTopology.OneHypercover

namespace Precoverage.ZeroHypercover

variable {J : Precoverage C} [J.toGrothendieck.Subcanonical]

/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  statement: {X Y : C} (𝒰 : J.ZeroHypercover X) {f g : X ⟶ Y}
  proof: by
  have hs : 𝒰.presieve₀.IsSheafFor (yoneda.obj Y) :=
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _).isSheafFor_of_mem_precoverage
      𝒰.mem₀
  exact 𝒰.ext_of_isSeparatedFor hs.isSeparatedFor fun i => by simp [h i]

中文:
引理 hom_ext
  结论: {X Y : C} (𝒰 : J.ZeroHypercover X) {f g : X ⟶ Y}
  证明: by
  have hs : 𝒰.presieve₀.IsSheafFor (yoneda.obj Y) :=
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _).isSheafFor_of_mem_precoverage
      𝒰.mem₀
  exact 𝒰.ext_of_isSeparatedFor hs.isSeparatedFor fun i => by simp [h i]

Depends on / 依赖: GrothendieckTopology, GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable, IsSheafFor, Subcanonical, ext_of_isSeparatedFor, hs.isSeparatedFor, isSeparatedFor, isSheafFor_of_mem_precoverage, isSheaf_of_isRepresentable, yoneda, yoneda.obj
-/
lemma hom_ext {X Y : C} (𝒰 : J.ZeroHypercover X) {f g : X ⟶ Y}
    (h : forall i, 𝒰.f i ≫ f = 𝒰.f i ≫ g) : f = g := by
  have hs : 𝒰.presieve₀.IsSheafFor (yoneda.obj Y) :=
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _).isSheafFor_of_mem_precoverage
      𝒰.mem₀
  exact 𝒰.ext_of_isSeparatedFor hs.isSeparatedFor fun i => by simp [h i]

/--
Definition of `glueMorphisms` / `glueMorphisms` 的定义

English:
definition glueMorphisms
  signature: {S T : C} (𝒰 : J.ZeroHypercover S) [𝒰.HasPullbacks]
  body: 𝒰.toOneHypercover.glueMorphisms f fun i j _ => hf i j

@[reassoc (attr := simp)]

中文:
定义 glueMorphisms
  签名: {S T : C} (𝒰 : J.ZeroHypercover S) [𝒰.有Pullbacks]
  定义体: 𝒰.toOneHypercover.glueMorphisms f fun i j _ => hf i j

@[reassoc (attr := simp)]

Depends on / 依赖: glueMorphisms, toOneHypercover, toOneHypercover.glueMorphisms
-/
noncomputable def glueMorphisms {S T : C} (𝒰 : J.ZeroHypercover S) [𝒰.HasPullbacks]
    (f : forall i, 𝒰.X i ⟶ T)
    (hf : forall i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ f i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ f j) :
    S ⟶ T :=
  𝒰.toOneHypercover.glueMorphisms f fun i j _ => hf i j

@[reassoc (attr := simp)]
/--
lemma `f_glueMorphisms` / 引理 `f_glueMorphisms`

English:
lemma f_glueMorphisms
  statement: {S T : C} (𝒰 : J.ZeroHypercover S) [𝒰.HasPullbacks]
  proof: 𝒰.toOneHypercover.f_glueMorphisms _ _ _

中文:
引理 f_glueMorphisms
  结论: {S T : C} (𝒰 : J.ZeroHypercover S) [𝒰.有Pullbacks]
  证明: 𝒰.toOneHypercover.f_glueMorphisms _ _ _

Depends on / 依赖: f_glueMorphisms, toOneHypercover, toOneHypercover.f_glueMorphisms
-/
lemma f_glueMorphisms {S T : C} (𝒰 : J.ZeroHypercover S) [𝒰.HasPullbacks]
    (f : forall i, 𝒰.X i ⟶ T)
    (hf : forall i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ f i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ f j)
    (i : 𝒰.I₀) :
    𝒰.f i ≫ 𝒰.glueMorphisms f hf = f i :=
  𝒰.toOneHypercover.f_glueMorphisms _ _ _

open MorphismProperty

variable [Limits.HasPullbacks C] [J.IsStableUnderBaseChange]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (isomorphisms C).IsLocalAtTarget J
  body: by
  refine .mk_of_isStableUnderBaseChange fun {X Y} f 𝒰 (H : forall i, IsIso _) => ⟨?_, ?_, ?_⟩
  · refine 𝒰.glueMorphisms (fun i => inv (pullback.snd f (𝒰.f i)) ≫ pullback.fst _ _) fun i j => ?_
    let f := pullback.map (pullback.fst f (𝒰.f i) ≫ f) (𝒰.f j) (𝒰.f i) (𝒰.f j) (pullback.snd _ _)
      (𝟙 _) (𝟙 _) (by simp [pullback.condition]) (by simp)
    rw [← cancel_epi ((pullbackRightPullbackFstIso _ _ _).hom ≫ f)]
    simp [pullback.condition, f]
  · exact (𝒰.pullback₁ f).hom_ext fun i => by simp [pullback.condition_assoc]
  · exact 𝒰.hom_ext fun i => by simp [pullback.condition]

中文:
实例 :
  签名: (isomorphisms C).是LocalAtTarget J
  定义体: by
  refine .mk_of_isStableUnderBaseChange fun {X Y} f 𝒰 (H : forall i, IsIso _) => ⟨?_, ?_, ?_⟩
  · refine 𝒰.glueMorphisms (fun i => inv (pullback.snd f (𝒰.f i)) ≫ pullback.fst _ _) fun i j => ?_
    let f := pullback.map (pullback.fst f (𝒰.f i) ≫ f) (𝒰.f j) (𝒰.f i) (𝒰.f j) (pullback.snd _ _)
      (𝟙 _) (𝟙 _) (by simp [pullback.condition]) (by simp)
    rw [← cancel_epi ((pullbackRightPullbackFstIso _ _ _).hom ≫ f)]
    simp [pullback.condition, f]
  · exact (𝒰.pullback₁ f).hom_ext fun i => by simp [pullback.condition_assoc]
  · exact 𝒰.hom_ext fun i => by simp [pullback.condition]

Depends on / 依赖: cancel_epi, conditio, condition, glueMorphisms, hom_ext, mk_of_isStableUnderBaseChange, pullback, pullback.conditio, pullback.condition, pullback.fst, pullback.map, pullback.snd, pullbackRightPullbackFstIso
-/
instance : (isomorphisms C).IsLocalAtTarget J := by
  refine .mk_of_isStableUnderBaseChange fun {X Y} f 𝒰 (H : forall i, IsIso _) => ⟨?_, ?_, ?_⟩
  · refine 𝒰.glueMorphisms (fun i => inv (pullback.snd f (𝒰.f i)) ≫ pullback.fst _ _) fun i j => ?_
    let f := pullback.map (pullback.fst f (𝒰.f i) ≫ f) (𝒰.f j) (𝒰.f i) (𝒰.f j) (pullback.snd _ _)
      (𝟙 _) (𝟙 _) (by simp [pullback.condition]) (by simp)
    rw [← cancel_epi ((pullbackRightPullbackFstIso _ _ _).hom ≫ f)]
    simp [pullback.condition, f]
  · exact (𝒰.pullback₁ f).hom_ext fun i => by simp [pullback.condition_assoc]
  · exact 𝒰.hom_ext fun i => by simp [pullback.condition]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `isPullback_of_forall_isPullback` / 引理 `isPullback_of_forall_isPullback`

English:
lemma isPullback_of_forall_isPullback
  statement: {P X Y Z : C} (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z)
  proof: by
  have h : fst ≫ f = snd ≫ g := (𝒰.pullback₁ fst).hom_ext fun i => by
    simpa [pullback.condition_assoc] using (H i).w
  suffices IsIso (pullback.lift fst snd h) from
    .of_iso_pullback ⟨h⟩ (asIso (pullback.lift _ _ h)) (by simp) (by simp)
  simp_rw [← isomorphisms.iff, IsLocalAtTarget.iff_of_zeroHypercover (P := isomorphisms C)
    (𝒰.pullbackCoverOfLeft f g), isomorphisms.iff]
  intro i
  let m := pullback.map (𝒰.f i ≫ f) g f g (𝒰.f i) (𝟙 Y) (𝟙 Z) (by simp) (by simp)
  have : IsPullback (pullback.fst (𝒰.f i ≫ f) g) m (𝒰.f i) (pullback.fst _ _) := by
    simpa [← IsPullback.paste_vert_iff (.of_hasPullback _ _), m] using .of_hasPullback _ _
  have H' : IsPullback (pullback.fst fst (𝒰.f i))
      (pullback.lift (pullback.snd _ _) (pullback.fst _ _ ≫ snd)
        (by simp [← h, pullback.condition_assoc]))
      (pullback.lift fst snd h) m := by
    rw [← IsPullback.paste_vert_iff this.flip (by ext <;> simp [m]; rw [pullback.condition])]
    simpa using .of_hasPullback _ _
  have heq : pullback.snd (pullback.lift fst snd h) ((𝒰.pullbackCoverOfLeft f g).f i) =
      H'.isoPullback.inv ≫ (H i).isoPullback.hom := by
    rw [Iso.eq_inv_comp]
    cat_disch
  rw [heq]
  infer_instance

中文:
引理 isPullback_of_对任意_isPullback
  结论: {P X Y Z : C} (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z)
  证明: by
  have h : fst ≫ f = snd ≫ g := (𝒰.pullback₁ fst).hom_ext fun i => by
    simpa [pullback.condition_assoc] using (H i).w
  suffices IsIso (pullback.lift fst snd h) from
    .of_iso_pullback ⟨h⟩ (asIso (pullback.lift _ _ h)) (by simp) (by simp)
  simp_rw [← isomorphisms.iff, IsLocalAtTarget.iff_of_zeroHypercover (P := isomorphisms C)
    (𝒰.pullbackCoverOfLeft f g), isomorphisms.iff]
  intro i
  let m := pullback.map (𝒰.f i ≫ f) g f g (𝒰.f i) (𝟙 Y) (𝟙 Z) (by simp) (by simp)
  have : IsPullback (pullback.fst (𝒰.f i ≫ f) g) m (𝒰.f i) (pullback.fst _ _) := by
    simpa [← IsPullback.paste_vert_iff (.of_hasPullback _ _), m] using .of_hasPullback _ _
  have H' : IsPullback (pullback.fst fst (𝒰.f i))
      (pullback.lift (pullback.snd _ _) (pullback.fst _ _ ≫ snd)
        (by simp [← h, pullback.condition_assoc]))
      (pullback.lift fst snd h) m := by
    rw [← IsPullback.paste_vert_iff this.flip (by ext <;> simp [m]; rw [pullback.condition])]
    simpa using .of_hasPullback _ _
  have heq : pullback.snd (pullback.lift fst snd h) ((𝒰.pullbackCoverOfLeft f g).f i) =
      H'.isoPullback.inv ≫ (H i).isoPullback.hom := by
    rw [Iso.eq_inv_comp]
    cat_disch
  rw [heq]
  infer_instance

Depends on / 依赖: IsLocalAtTarget, IsLocalAtTarget.iff_of_zeroHypercover, IsPullback, condition_assoc, hom_ext, iff_of_zeroHypercover, isomorphisms, isomorphisms.iff, of_iso_pullback, pullback, pullback.condition_assoc, pullback.fst, pullback.lift, pullback.map, pullbackCoverOfLeft, simp_rw
-/
lemma isPullback_of_forall_isPullback {P X Y Z : C} (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z)
    (g : Y ⟶ Z)
    -- TODO: after refactoring `MorphismProperty.IsLocalAtTarget` to allow covers
    -- in an arbitrary universe, replace `v` by an arbitrary universe
    (𝒰 : Precoverage.ZeroHypercover.{v} J X)
    (H : forall i, IsPullback (pullback.snd fst _) (pullback.fst fst (𝒰.f i) ≫ snd) (𝒰.f i ≫ f) g) :
    IsPullback fst snd f g := by
  have h : fst ≫ f = snd ≫ g := (𝒰.pullback₁ fst).hom_ext fun i => by
    simpa [pullback.condition_assoc] using (H i).w
  suffices IsIso (pullback.lift fst snd h) from
    .of_iso_pullback ⟨h⟩ (asIso (pullback.lift _ _ h)) (by simp) (by simp)
  simp_rw [← isomorphisms.iff, IsLocalAtTarget.iff_of_zeroHypercover (P := isomorphisms C)
    (𝒰.pullbackCoverOfLeft f g), isomorphisms.iff]
  intro i
  let m := pullback.map (𝒰.f i ≫ f) g f g (𝒰.f i) (𝟙 Y) (𝟙 Z) (by simp) (by simp)
  have : IsPullback (pullback.fst (𝒰.f i ≫ f) g) m (𝒰.f i) (pullback.fst _ _) := by
    simpa [← IsPullback.paste_vert_iff (.of_hasPullback _ _), m] using .of_hasPullback _ _
  have H' : IsPullback (pullback.fst fst (𝒰.f i))
      (pullback.lift (pullback.snd _ _) (pullback.fst _ _ ≫ snd)
        (by simp [← h, pullback.condition_assoc]))
      (pullback.lift fst snd h) m := by
    rw [← IsPullback.paste_vert_iff this.flip (by ext <;> simp [m]; rw [pullback.condition])]
    simpa using .of_hasPullback _ _
  have heq : pullback.snd (pullback.lift fst snd h) ((𝒰.pullbackCoverOfLeft f g).f i) =
      H'.isoPullback.inv ≫ (H i).isoPullback.hom := by
    rw [Iso.eq_inv_comp]
    cat_disch
  rw [heq]
  infer_instance

end Precoverage.ZeroHypercover

end CategoryTheory
