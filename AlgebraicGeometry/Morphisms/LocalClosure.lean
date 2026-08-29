/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Basic

/-!
# Local closure of morphism properties

We define the source local closure of a property `P` w.r.t. a morphism property `W` and show it
inherits stability properties from `P`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry

variable (W : MorphismProperty Scheme.{u})

/--
Definition of `sourceLocalClosure` / `sourceLocalClosure` 的定义

English:
definition sourceLocalClosure
  signature: (P : MorphismProperty Scheme.{u})
  body: fun X _ f => exists (𝒰 : Scheme.Cover.{u} (Scheme.precoverage W) X), forall (i : 𝒰.I₀), P (𝒰.f i ≫ f)

中文:
定义 sourceLocalClosure
  签名: (P : MorphismProperty 概形.{u})
  定义体: fun X _ f => exists (𝒰 : Scheme.Cover.{u} (Scheme.precoverage W) X), forall (i : 𝒰.I₀), P (𝒰.f i ≫ f)

Depends on / 依赖: Scheme, Scheme.Cover, Scheme.precoverage, precoverage
-/
def sourceLocalClosure (P : MorphismProperty Scheme.{u}) : MorphismProperty Scheme.{u} :=
  fun X _ f => exists (𝒰 : Scheme.Cover.{u} (Scheme.precoverage W) X), forall (i : 𝒰.I₀), P (𝒰.f i ≫ f)

namespace sourceLocalClosure

variable {W} {P Q : MorphismProperty Scheme.{u}} {X Y : Scheme.{u}}

/--
Definition of `cover` / `cover` 的定义

English:
definition cover
  signature: {f : X ⟶ Y} (hf : sourceLocalClosure W P f)
  body: hf.choose

中文:
定义 cover
  签名: {f : X ⟶ Y} (hf : sourceLocalClosure W P f)
  定义体: hf.choose

Depends on / 依赖: hf.choose
-/
noncomputable def cover {f : X ⟶ Y} (hf : sourceLocalClosure W P f) :
    Scheme.Cover.{u} (Scheme.precoverage W) X :=
  hf.choose

/--
lemma `property_coverMap_comp` / 引理 `property_coverMap_comp`

English:
lemma property_coverMap_comp
  given: {f : X ⟶ Y} (hf : sourceLocalClosure W P f) (i : hf.cover.I₀)
  proof: hf.choose_spec i

中文:
引理 property_coverMap_comp
  条件: {f : X ⟶ Y} (hf : sourceLocalClosure W P f) (i : hf.cover.I₀)
  证明: hf.choose_spec i

Depends on / 依赖: choose_spec, hf.choose_spec
-/
lemma property_coverMap_comp {f : X ⟶ Y} (hf : sourceLocalClosure W P f) (i : hf.cover.I₀) :
    P (hf.cover.f i ≫ f) :=
  hf.choose_spec i

set_option backward.defeqAttrib.useBackward true in
/--
lemma `le` / 引理 `le`

English:
lemma le
  given: [W.ContainsIdentities] [W.RespectsIso]
  statement: P <= sourceLocalClosure W P
  proof: fun X Y f hf => ⟨X.coverOfIsIso (𝟙 X), by simpa⟩

中文:
引理 le
  条件: [W.余ntainsIdentities] [W.RespectsIso]
  结论: P <= sourceLocalClosure W P
  证明: fun X Y f hf => ⟨X.coverOfIsIso (𝟙 X), by simpa⟩

Depends on / 依赖: X.coverOfIsIso, coverOfIsIso
-/
lemma le [W.ContainsIdentities] [W.RespectsIso] : P <= sourceLocalClosure W P :=
  fun X Y f hf => ⟨X.coverOfIsIso (𝟙 X), by simpa⟩

/--
lemma `iff_forall_exists` / 引理 `iff_forall_exists`

English:
lemma iff_forall_exists
  given: [P.RespectsIso] {f : X ⟶ Y}
  proof: by
  refine ⟨fun ⟨𝒰, hf⟩ x => ?_, fun H => ?_⟩
  · refine ⟨(𝒰.f (𝒰.idx x)).opensRange, 𝒰.covers x, ?_⟩
    rw [← Scheme.Hom.isoOpensRange_inv_comp]; rw [Category.assoc]; rw [P.cancel_left_of_respectsIso]
    apply hf
  · choose U hx hf using H
    exact ⟨.mkOfCovers X (fun x => U x) (fun _ => (U _).ι) (fun x => ⟨x, ⟨x, hx x⟩, rfl⟩)
      fun _ => inferInstance, hf⟩

中文:
引理 iff_对任意_存在
  条件: [P.RespectsIso] {f : X ⟶ Y}
  证明: by
  refine ⟨fun ⟨𝒰, hf⟩ x => ?_, fun H => ?_⟩
  · refine ⟨(𝒰.f (𝒰.idx x)).opensRange, 𝒰.covers x, ?_⟩
    rw [← Scheme.Hom.isoOpensRange_inv_comp]; rw [Category.assoc]; rw [P.cancel_left_of_respectsIso]
    apply hf
  · choose U hx hf using H
    exact ⟨.mkOfCovers X (fun x => U x) (fun _ => (U _).ι) (fun x => ⟨x, ⟨x, hx x⟩, rfl⟩)
      fun _ => inferInstance, hf⟩

Depends on / 依赖: Category, Category.assoc, ComposableArrows, P.cancel_left_of_respectsIso, Scheme, Scheme.Hom.isoOpensRange_inv_comp, cancel_left_of_respectsIso, covers, isoOpensRange_inv_comp, mkOfCovers, opensRange, unop.len
-/
lemma iff_forall_exists [P.RespectsIso] {f : X ⟶ Y} :
    sourceLocalClosure IsOpenImmersion P f ↔ forall (x : X), exists (U : X.Opens), x in U ∧ P (U.ι ≫ f) := by
  refine ⟨fun ⟨𝒰, hf⟩ x => ?_, fun H => ?_⟩
  · refine ⟨(𝒰.f (𝒰.idx x)).opensRange, 𝒰.covers x, ?_⟩
    rw [← Scheme.Hom.isoOpensRange_inv_comp]; rw [Category.assoc]; rw [P.cancel_left_of_respectsIso]
    apply hf
  · choose U hx hf using H
    exact ⟨.mkOfCovers X (fun x => U x) (fun _ => (U _).ι) (fun x => ⟨x, ⟨x, hx x⟩, rfl⟩)
      fun _ => inferInstance, hf⟩

variable [W.IsStableUnderBaseChange] [Scheme.IsJointlySurjectivePreserving W]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.RespectsLeft
  signature: Q] [Q.IsStableUnderBaseChange] :
  body: by
  refine ⟨fun {X Y} Z f hf g ⟨𝒰, hg⟩ => ⟨𝒰.pullback₁ f, fun i => ?_⟩⟩
  simpa [pullback.condition_assoc] using
    RespectsLeft.precomp (Q := Q) _ (Q.pullback_snd _ _ hf) _ (hg i)

中文:
实例 [P.RespectsLeft
  签名: Q] [Q.是StableUnderBaseChange] :
  定义体: by
  refine ⟨fun {X Y} Z f hf g ⟨𝒰, hg⟩ => ⟨𝒰.pullback₁ f, fun i => ?_⟩⟩
  simpa [pullback.condition_assoc] using
    RespectsLeft.precomp (Q := Q) _ (Q.pullback_snd _ _ hf) _ (hg i)

Depends on / 依赖: Q.pullback_snd, RespectsLeft, RespectsLeft.precomp, condition_assoc, precomp, pullback, pullback.condition_assoc, pullback_snd
-/
instance [P.RespectsLeft Q] [Q.IsStableUnderBaseChange] :
    (sourceLocalClosure W P).RespectsLeft Q := by
  refine ⟨fun {X Y} Z f hf g ⟨𝒰, hg⟩ => ⟨𝒰.pullback₁ f, fun i => ?_⟩⟩
  simpa [pullback.condition_assoc] using
    RespectsLeft.precomp (Q := Q) _ (Q.pullback_snd _ _ hf) _ (hg i)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.RespectsRight
  signature: Q] : (sourceLocalClosure W P).RespectsRight Q
  body: by
  refine ⟨fun {X Y} Z f hf g ⟨𝒰, hg⟩ => ⟨𝒰, fun i => ?_⟩⟩
  rw [← Category.assoc]
  exact RespectsRight.postcomp _ hf _ (hg i)

中文:
实例 [P.RespectsRight
  签名: Q] : (sourceLocalClosure W P).RespectsRight Q
  定义体: by
  refine ⟨fun {X Y} Z f hf g ⟨𝒰, hg⟩ => ⟨𝒰, fun i => ?_⟩⟩
  rw [← Category.assoc]
  exact RespectsRight.postcomp _ hf _ (hg i)

Depends on / 依赖: Category, Category.assoc, RespectsRight, RespectsRight.postcomp, postcomp
-/
instance [P.RespectsRight Q] : (sourceLocalClosure W P).RespectsRight Q := by
  refine ⟨fun {X Y} Z f hf g ⟨𝒰, hg⟩ => ⟨𝒰, fun i => ?_⟩⟩
  rw [← Category.assoc]
  exact RespectsRight.postcomp _ hf _ (hg i)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.RespectsIso]
  signature: : (sourceLocalClosure W P).RespectsIso where

中文:
实例 [P.RespectsIso]
  签名: : (sourceLocalClosure W P).RespectsIso where
-/
instance [P.RespectsIso] : (sourceLocalClosure W P).RespectsIso where

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.RespectsIso]
  signature: [P.RespectsLeft @IsOpenImmersion]
  body: by
  refine .mk_of_iff_of_zeroHypercover fun f 𝒰 => ?_
  refine ⟨fun ⟨𝒱, h⟩ => fun i => ⟨𝒱.pullback₁ (𝒰.f i), fun j => ?_⟩, fun h => ?_⟩
  · simpa [pullback.condition_assoc] using
      RespectsLeft.precomp (Q := @IsOpenImmersion) _ inferInstance _ (h j)
  · choose 𝒱 h𝒱 using h
    exact ⟨(Scheme.Cover.ulift 𝒰).bind (fun i => Scheme.Cover.ulift (𝒱 _)), fun i => h𝒱 _ _⟩

中文:
实例 [P.RespectsIso]
  签名: [P.RespectsLeft @是开浸入]
  定义体: by
  refine .mk_of_iff_of_zeroHypercover fun f 𝒰 => ?_
  refine ⟨fun ⟨𝒱, h⟩ => fun i => ⟨𝒱.pullback₁ (𝒰.f i), fun j => ?_⟩, fun h => ?_⟩
  · simpa [pullback.condition_assoc] using
      RespectsLeft.precomp (Q := @IsOpenImmersion) _ inferInstance _ (h j)
  · choose 𝒱 h𝒱 using h
    exact ⟨(Scheme.Cover.ulift 𝒰).bind (fun i => Scheme.Cover.ulift (𝒱 _)), fun i => h𝒱 _ _⟩

Depends on / 依赖: IsOpenImmersion, RespectsLeft, RespectsLeft.precomp, Scheme, Scheme.Cover.ulift, condition_assoc, mk_of_iff_of_zeroHypercover, precomp, pullback, pullback.condition_assoc
-/
instance [P.RespectsIso] [P.RespectsLeft @IsOpenImmersion] :
    IsZariskiLocalAtSource (sourceLocalClosure IsOpenImmersion P) := by
  refine .mk_of_iff_of_zeroHypercover fun f 𝒰 => ?_
  refine ⟨fun ⟨𝒱, h⟩ => fun i => ⟨𝒱.pullback₁ (𝒰.f i), fun j => ?_⟩, fun h => ?_⟩
  · simpa [pullback.condition_assoc] using
      RespectsLeft.precomp (Q := @IsOpenImmersion) _ inferInstance _ (h j)
  · choose 𝒱 h𝒱 using h
    exact ⟨(Scheme.Cover.ulift 𝒰).bind (fun i => Scheme.Cover.ulift (𝒱 _)), fun i => h𝒱 _ _⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsStableUnderBaseChange]
  signature: : (sourceLocalClosure W P).IsStableUnderBaseChange
  body: by
  refine .mk' fun X Y S f g _ ⟨𝒰, hg⟩ => ⟨𝒰.pullback₁ (pullback.snd f g), fun i => ?_⟩
  simpa [← pullbackLeftPullbackSndIso_hom_fst, P.cancel_left_of_respectsIso] using
    P.pullback_fst _ _ (hg i)

中文:
实例 [P.是StableUnderBaseChange]
  签名: : (sourceLocalClosure W P).是StableUnderBaseChange
  定义体: by
  refine .mk' fun X Y S f g _ ⟨𝒰, hg⟩ => ⟨𝒰.pullback₁ (pullback.snd f g), fun i => ?_⟩
  simpa [← pullbackLeftPullbackSndIso_hom_fst, P.cancel_left_of_respectsIso] using
    P.pullback_fst _ _ (hg i)

Depends on / 依赖: P.cancel_left_of_respectsIso, P.pullback_fst, cancel_left_of_respectsIso, pullback, pullback.snd, pullbackLeftPullbackSndIso_hom_fst, pullback_fst
-/
instance [P.IsStableUnderBaseChange] : (sourceLocalClosure W P).IsStableUnderBaseChange := by
  refine .mk' fun X Y S f g _ ⟨𝒰, hg⟩ => ⟨𝒰.pullback₁ (pullback.snd f g), fun i => ?_⟩
  simpa [← pullbackLeftPullbackSndIso_hom_fst, P.cancel_left_of_respectsIso] using
    P.pullback_fst _ _ (hg i)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [W.ContainsIdentities]
  signature: [P.ContainsIdentities]
  body: ⟨fun X => ⟨X.coverOfIsIso (𝟙 X), fun _ => P.id_mem _⟩⟩

中文:
实例 [W.余ntainsIdentities]
  签名: [P.余ntainsIdentities]
  定义体: ⟨fun X => ⟨X.coverOfIsIso (𝟙 X), fun _ => P.id_mem _⟩⟩

Depends on / 依赖: P.id_mem, X.coverOfIsIso, coverOfIsIso, id_mem
-/
instance [W.ContainsIdentities] [P.ContainsIdentities] :
    (sourceLocalClosure W P).ContainsIdentities :=
  ⟨fun X => ⟨X.coverOfIsIso (𝟙 X), fun _ => P.id_mem _⟩⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [W.IsStableUnderComposition]
  signature: [P.IsStableUnderBaseChange] [P.IsStableUnderComposition]
  body: by
  refine ⟨fun {X Y Z} f g ⟨𝒰, hf⟩ ⟨𝒱, hg⟩ => ?_⟩
  refine ⟨𝒰.bind fun i => (𝒱.pullback₁ (𝒰.f i ≫ f)), fun ⟨l, r⟩ => ?_⟩
  simpa [← pullbackRightPullbackFstIso_inv_snd_fst_assoc, pullback.condition_assoc] using
    P.comp_mem _ _ (P.pullback_snd _ _ (hf _)) (hg r)

中文:
实例 [W.是StableUnderComposition]
  签名: [P.是StableUnderBaseChange] [P.是StableUnderComposition]
  定义体: by
  refine ⟨fun {X Y Z} f g ⟨𝒰, hf⟩ ⟨𝒱, hg⟩ => ?_⟩
  refine ⟨𝒰.bind fun i => (𝒱.pullback₁ (𝒰.f i ≫ f)), fun ⟨l, r⟩ => ?_⟩
  simpa [← pullbackRightPullbackFstIso_inv_snd_fst_assoc, pullback.condition_assoc] using
    P.comp_mem _ _ (P.pullback_snd _ _ (hf _)) (hg r)

Depends on / 依赖: P.comp_mem, P.pullback_snd, comp_mem, condition_assoc, pullback, pullback.condition_assoc, pullbackRightPullbackFstIso_inv_snd_fst_assoc, pullback_snd
-/
instance [W.IsStableUnderComposition] [P.IsStableUnderBaseChange] [P.IsStableUnderComposition] :
    (sourceLocalClosure W P).IsStableUnderComposition := by
  refine ⟨fun {X Y Z} f g ⟨𝒰, hf⟩ ⟨𝒱, hg⟩ => ?_⟩
  refine ⟨𝒰.bind fun i => (𝒱.pullback₁ (𝒰.f i ≫ f)), fun ⟨l, r⟩ => ?_⟩
  simpa [← pullbackRightPullbackFstIso_inv_snd_fst_assoc, pullback.condition_assoc] using
    P.comp_mem _ _ (P.pullback_snd _ _ (hf _)) (hg r)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [W.IsMultiplicative]
  signature: [P.IsStableUnderBaseChange] [P.IsMultiplicative]

中文:
实例 [W.是Multiplicative]
  签名: [P.是StableUnderBaseChange] [P.是Multiplicative]
-/
instance [W.IsMultiplicative] [P.IsStableUnderBaseChange] [P.IsMultiplicative] :
    (sourceLocalClosure W P).IsMultiplicative where

end sourceLocalClosure

end AlgebraicGeometry
