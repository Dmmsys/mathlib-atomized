/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Local
public import Mathlib.CategoryTheory.Sites.MorphismProperty

/-!
# Local closure of morphism properties

We define the source local closure of a morphism property `P` w.r.t. a precoverage `K` as the
weakest property containing `P` that is `K`-local on the source.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits MorphismProperty

variable {C : Type u} [Category.{v} C]

namespace CategoryTheory.MorphismProperty

variable {K : Precoverage C}

/--
Inductive type `sourceLocalClosure` / 归纳类型 `sourceLocalClosure`

English:
inductive sourceLocalClosure
  parameters: (K : Precoverage C) (P : MorphismProperty C)
  constructors (4):
    - of: {X Y : C} (f : X ⟶ Y) : P f -> sourceLocalClosure K P f
    - of_iso: {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') (e : Arrow.mk f ≅ Arrow.mk g) : sourceLocalClosure K P f -> sourceLocalClosure K P g
    - comp: {X Y : C} (f : X ⟶ Y) (hf : sourceLocalClosure K P f) (R : Presieve X) (hR : R in K X) {U : C} (g : U ⟶ X) : R g -> sourceLocalClosure K P (g ≫ f)
    - of_presieve: {X Y : C} (f : X ⟶ Y) (R : Presieve X) (hR : R in K X) (h : forall (U : C) (g : U ⟶ X), R g -> sourceLocalClosure K P (g ≫ f)) : sourceLocalClosure K P f

中文:
归纳类型 sourceLocalClosure
  参数: (K : Precoverage C) (P : MorphismProperty C)
  构造子 (4 个):
    - of: {X Y : C} (f : X ⟶ Y) : P f -> sourceLocalClosure K P f
    - of_iso: {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') (e : 箭头.mk f ≅ 箭头.mk g) : sourceLocalClosure K P f -> sourceLocalClosure K P g
    - comp: {X Y : C} (f : X ⟶ Y) (hf : sourceLocalClosure K P f) (R : Presieve X) (hR : R in K X) {U : C} (g : U ⟶ X) : R g -> sourceLocalClosure K P (g ≫ f)
    - of_presieve: {X Y : C} (f : X ⟶ Y) (R : Presieve X) (hR : R in K X) (h : 对任意 (U : C) (g : U ⟶ X), R g -> sourceLocalClosure K P (g ≫ f)) : sourceLocalClosure K P f
-/
inductive sourceLocalClosure (K : Precoverage C) (P : MorphismProperty C) : MorphismProperty C
  /-- Force `P ≤ sourceLocalClosure K P`. -/
  | of {X Y : C} (f : X ⟶ Y) : P f -> sourceLocalClosure K P f
  /-- Force `RespectsIso`. -/
  | of_iso {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') (e : Arrow.mk f ≅ Arrow.mk g) :
      sourceLocalClosure K P f -> sourceLocalClosure K P g
  | comp {X Y : C} (f : X ⟶ Y) (hf : sourceLocalClosure K P f) (R : Presieve X) (hR : R in K X)
      {U : C} (g : U ⟶ X) : R g -> sourceLocalClosure K P (g ≫ f)
  | of_presieve {X Y : C} (f : X ⟶ Y) (R : Presieve X) (hR : R in K X)
      (h : forall (U : C) (g : U ⟶ X), R g -> sourceLocalClosure K P (g ≫ f)) :
      sourceLocalClosure K P f

namespace sourceLocalClosure

attribute [grind .] of

variable {P Q : MorphismProperty C} {X Y : C}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (sourceLocalClosure K P).IsLocalAtSource K
  body: .of_iso _ _ (Arrow.isoMk' _ _ (asIso i).symm (.refl _)) hf
  postcomp i hi f hf := .of_iso _ _ (Arrow.isoMk' _ _ (.refl _) (asIso i)) hf
  comp hR _ g hg hf := .comp _ hf _ hR _ hg
  of_forall_comp hR h := .of_presieve _ _ hR h

中文:
实例 :
  签名: (sourceLocalClosure K P).是LocalAtSource K
  定义体: .of_iso _ _ (Arrow.isoMk' _ _ (asIso i).symm (.refl _)) hf
  postcomp i hi f hf := .of_iso _ _ (Arrow.isoMk' _ _ (.refl _) (asIso i)) hf
  comp hR _ g hg hf := .comp _ hf _ hR _ hg
  of_forall_comp hR h := .of_presieve _ _ hR h

Depends on / 依赖: Arrow.isoMk, of_iso
-/
instance : (sourceLocalClosure K P).IsLocalAtSource K where
  precomp i hi f hf := .of_iso _ _ (Arrow.isoMk' _ _ (asIso i).symm (.refl _)) hf
  postcomp i hi f hf := .of_iso _ _ (Arrow.isoMk' _ _ (.refl _) (asIso i)) hf
  comp hR _ g hg hf := .comp _ hf _ hR _ hg
  of_forall_comp hR h := .of_presieve _ _ hR h

/--
lemma `le` / 引理 `le`

English:
lemma le
  statement: P <= sourceLocalClosure K P
  proof: fun _ _ _ => .of _

中文:
引理 le
  结论: P <= sourceLocalClosure K P
  证明: fun _ _ _ => .of _
-/
lemma le : P <= sourceLocalClosure K P :=
  fun _ _ _ => .of _

/--
lemma `le_of_isLocalAtSource` / 引理 `le_of_isLocalAtSource`

English:
lemma le_of_isLocalAtSource
  given: (h : P <= Q) [Q.IsLocalAtSource K]
  statement: sourceLocalClosure K P <= Q
  proof: by
  intro X Y f hf
  induction hf with
  | of f hf => exact h _ hf
  | of_iso f g e _ hf => rwa [Q.arrow_mk_iso_iff e.symm]
  | comp f hf R hR g hg ih => apply IsLocalAtSource.comp hR _ hg ih
  | of_presieve f R hR h ih => apply IsLocalAtSource.of_forall_comp hR fun U g hg => ih _ _ hg

中文:
引理 le_of_isLocalAtSource
  条件: (h : P <= Q) [Q.是LocalAtSource K]
  结论: sourceLocalClosure K P <= Q
  证明: by
  intro X Y f hf
  induction hf with
  | of f hf => exact h _ hf
  | of_iso f g e _ hf => rwa [Q.arrow_mk_iso_iff e.symm]
  | comp f hf R hR g hg ih => apply IsLocalAtSource.comp hR _ hg ih
  | of_presieve f R hR h ih => apply IsLocalAtSource.of_forall_comp hR fun U g hg => ih _ _ hg

Depends on / 依赖: IsLocalAtSource, IsLocalAtSource.comp, IsLocalAtSource.of_forall_comp, Q.arrow_mk_iso_iff, arrow_mk_iso_iff, e.symm, of_forall_comp, of_iso, of_presieve
-/
lemma le_of_isLocalAtSource (h : P <= Q) [Q.IsLocalAtSource K] : sourceLocalClosure K P <= Q := by
  intro X Y f hf
  induction hf with
  | of f hf => exact h _ hf
  | of_iso f g e _ hf => rwa [Q.arrow_mk_iso_iff e.symm]
  | comp f hf R hR g hg ih => apply IsLocalAtSource.comp hR _ hg ih
  | of_presieve f R hR h ih => apply IsLocalAtSource.of_forall_comp hR fun U g hg => ih _ _ hg

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.ContainsIdentities]
  signature: : ContainsIdentities (sourceLocalClosure K P) where
  body: le _ (P.id_mem _)

中文:
实例 [P.余ntainsIdentities]
  签名: : 余ntainsIdentities (sourceLocalClosure K P) where
  定义体: le _ (P.id_mem _)

Depends on / 依赖: A.unop, P.id_mem, ShortComplex, ShortComplex.ab_exact_iff, T.coyoneda_exact, T.mor, T.obj, ab_exact_iff, id_mem
-/
instance [P.ContainsIdentities] : ContainsIdentities (sourceLocalClosure K P) where
  id_mem _ := le _ (P.id_mem _)

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsStableUnderBaseChange]
  signature: [K.IsStableUnderBaseChange] [HasPullbacks C]
  body: by
    induction hf generalizing W snd with
    | of f' hf' => exact .of _ (P.of_isPullback h hf')
    | of_iso f' g' e hf' ih =>
      exact ih _ (g ≫ e.inv.right) (fst ≫ e.inv.left) _ (h.paste_horiz (.of_horiz_isIso ⟨e.inv.w⟩))
    | comp f' hf' R hR g' hg' ih =>
      let u : W ⟶ pullback g f' :=

中文:
实例 [P.是StableUnderBaseChange]
  签名: [K.是StableUnderBaseChange] [有Pullbacks C]
  定义体: by
    induction hf generalizing W snd with
    | of f' hf' => exact .of _ (P.of_isPullback h hf')
    | of_iso f' g' e hf' ih =>
      exact ih _ (g ≫ e.inv.right) (fst ≫ e.inv.left) _ (h.paste_horiz (.of_horiz_isIso ⟨e.inv.w⟩))
    | comp f' hf' R hR g' hg' ih =>
      let u : W ⟶ pullback g f' :=

Depends on / 依赖: IsPullback, IsPullback.isoPullback, P.of_isPullback, ShortComplex, ShortComplex.ab_exact_iff, T.mor, T.obj, Triangle, Triangle.yoneda_exact, ab_exact_iff, e.inv.left, e.inv.right, e.inv.w, generalizing, h.paste_horiz, h.w.symm, isoPullback, of_bot, of_h, of_horiz_isIso
-/
instance [P.IsStableUnderBaseChange] [K.IsStableUnderBaseChange] [HasPullbacks C] :
    IsStableUnderBaseChange (sourceLocalClosure K P) where
  of_isPullback {Y} X W Z g f fst snd h hf := by
    induction hf generalizing W snd with
    | of f' hf' => exact .of _ (P.of_isPullback h hf')
    | of_iso f' g' e hf' ih =>
      exact ih _ (g ≫ e.inv.right) (fst ≫ e.inv.left) _ (h.paste_horiz (.of_horiz_isIso ⟨e.inv.w⟩))
    | comp f' hf' R hR g' hg' ih =>
      let u : W ⟶ pullback g f' := pullback.lift snd (fst ≫ g') (by simp [h.w.symm])
      have : snd = u ≫ pullback.fst g f' := by simp [u]
      rw [this] at h ⊢
      let e : W ≅ pullback g' (pullback.snd g f') :=
        IsPullback.isoPullback (.of_bot h (by simp [u]) (.flip <| .of_hasPullback _ _))
      rw [← (sourceLocalClosure K P).cancel_left_of_respectsIso e.inv]; rw [← Category.assoc]
      refine .comp _ (ih _ _ _ _ (.flip (.of_hasPullback _ _))) _
        (K.pullbackArrows_mem (pullback.snd _ _) hR) _ ?_
      simpa [e, u] using .mk _ _ hg'
    | of_presieve f R hR h ih =>
      refine .of_presieve _ _ (K.pullbackArrows_mem fst hR) ?_
      intro U v ⟨Z, u, hu⟩
      exact ih _ _ hu _ g (pullback.fst _ _) _ (.paste_vert (.of_hasPullback _ _) h)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `sourceLocalClosure_iff_of_respectsLeft` / 引理 `sourceLocalClosure_iff_of_respectsLeft`

English:
lemma sourceLocalClosure_iff_of_respectsLeft
  statement: [P.RespectsIso] [P.RespectsLeft K.morphismProperty]
  proof: by
  refine ⟨?_, ?_⟩
  · intro h
    induction h with
    | of f hf => exact ⟨.singleton (𝟙 _), K.mem_coverings_of_isIso _, fun U g ⟨⟩ => by simpa⟩
    | of_iso f g e hf h =>
      obtain ⟨R, hR, h⟩ := h
      rw [K.mem_iff_exists_zeroHypercover] at hR
      obtain ⟨E, rfl⟩ := hR
      refine ⟨_, (E

中文:
引理 sourceLocalClosure_iff_of_respectsLeft
  结论: [P.RespectsIso] [P.RespectsLeft K.morphismProperty]
  证明: by
  refine ⟨?_, ?_⟩
  · intro h
    induction h with
    | of f hf => exact ⟨.singleton (𝟙 _), K.mem_coverings_of_isIso _, fun U g ⟨⟩ => by simpa⟩
    | of_iso f g e hf h =>
      obtain ⟨R, hR, h⟩ := h
      rw [K.mem_iff_exists_zeroHypercover] at hR
      obtain ⟨E, rfl⟩ := hR
      refine ⟨_, (E

Depends on / 依赖: Arrow.mk_hom, Arrow.mk_left, Arrow.mk_right, Arrow.w_mk_right, Category, Category.assoc, E.pushforward, K.mem_coverings_of_isIso, K.mem_iff_exists_zeroHypercover, P.cancel_right_of_respectsIso, cancel_right_of_respectsIso, e.hom.left, mem_coverings_of_isIso, mem_iff_exists_zeroHypercover, mk_hom, mk_left, mk_right, of_iso, pushforward, singleton
-/
lemma sourceLocalClosure_iff_of_respectsLeft [P.RespectsIso] [P.RespectsLeft K.morphismProperty]
    [K.HasIsos] [K.IsStableUnderBaseChange] [K.IsStableUnderComposition] [K.HasPullbacks] {X Y : C}
    {f : X ⟶ Y} :
    sourceLocalClosure K P f ↔ exists R in K X, forall (U : C) (g : U ⟶ X), R g -> P (g ≫ f) := by
  refine ⟨?_, ?_⟩
  · intro h
    induction h with
    | of f hf => exact ⟨.singleton (𝟙 _), K.mem_coverings_of_isIso _, fun U g ⟨⟩ => by simpa⟩
    | of_iso f g e hf h =>
      obtain ⟨R, hR, h⟩ := h
      rw [K.mem_iff_exists_zeroHypercover] at hR
      obtain ⟨E, rfl⟩ := hR
      refine ⟨_, (E.pushforward e.hom.left (K.mem_coverings_of_isIso _)).mem₀, ?_⟩
      intro U v ⟨i⟩
      dsimp
      simp only [Category.assoc, Arrow.w_mk_right, Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom]
      rw [← Category.assoc]; rw [P.cancel_right_of_respectsIso]
      exact h _ _ ⟨i⟩
    | comp f hf R hR g hg ih =>
      obtain ⟨S, hS, h⟩ := ih
      rw [K.mem_iff_exists_zeroHypercover] at hS hR
      obtain ⟨E, rfl⟩ := hS
      obtain ⟨F, rfl⟩ := hR
      refine ⟨(E.pullback₁ g).presieve₀, (E.pullback₁ g).mem₀, ?_⟩
      intro U v ⟨i⟩
      dsimp
      rw [pullback.condition_assoc]
      refine RespectsLeft.precomp (Q := K.morphismProperty) _ ?_ _ ?_
      · obtain ⟨j⟩ := hg
        exact (F.pullback₂ (E.f i)).morphismProperty j
      · exact h _ _ ⟨i⟩
    | of_presieve f R hR h ih =>
      rw [K.mem_iff_exists_zeroHypercover] at hR
      obtain ⟨E, rfl⟩ := hR
      choose S hS h' using fun i : E.I₀ => ih _ _ ⟨i⟩
      simp_rw [K.mem_iff_exists_zeroHypercover] at hS
      choose F hF using hS
      refine ⟨_, (E.bind F).mem₀, fun U g ⟨j⟩ => ?_⟩
      dsimp
      rw [Category.assoc]
      exact h' _ _ _ (by simp [hF])
  · intro ⟨R, hR, h⟩
    exact .of_presieve _ _ hR (by grind)

end sourceLocalClosure

end CategoryTheory.MorphismProperty
