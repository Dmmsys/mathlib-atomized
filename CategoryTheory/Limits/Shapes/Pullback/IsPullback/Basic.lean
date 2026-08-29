/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Joël Riou, Calle Sönne
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# Pullback and pushout squares

We restate some results about pullbacks/pushouts in the language of `IsPullback` and `IsPushout`,
among which the pasting lemmas
-/

@[expose] public section

noncomputable section

open CategoryTheory

open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]

namespace IsPullback

variable {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
theorem `of_is_product` / 定理 `of_is_product`

English:
theorem of_is_product
  given: {c : BinaryFan X Y} (h : Limits.IsLimit c) (t : IsTerminal Z)
  proof: of_isLimit
    (isPullbackOfIsTerminalIsProduct _ _ _ _ t
      (IsLimit.ofIsoLimit h
        (Limits.Cone.ext (Iso.refl c.pt)
          (by
            rintro ⟨⟨⟩⟩ <;> simp))))

中文:
定理 of_is_product
  条件: {c : BinaryFan X Y} (h : Limits.是极限 c) (t : 是终止 Z)
  证明: of_isLimit
    (isPullbackOfIsTerminalIsProduct _ _ _ _ t
      (IsLimit.ofIsoLimit h
        (Limits.Cone.ext (Iso.refl c.pt)
          (by
            rintro ⟨⟨⟩⟩ <;> simp))))

Depends on / 依赖: IsLimit, IsLimit.ofIsoLimit, Iso.refl, Limits, Limits.Cone.ext, c.pt, isPullbackOfIsTerminalIsProduct, ofIsoLimit, of_isLimit
-/
theorem of_is_product {c : BinaryFan X Y} (h : Limits.IsLimit c) (t : IsTerminal Z) :
    IsPullback c.fst c.snd (t.from _) (t.from _) :=
  of_isLimit
    (isPullbackOfIsTerminalIsProduct _ _ _ _ t
      (IsLimit.ofIsoLimit h
        (Limits.Cone.ext (Iso.refl c.pt)
          (by
            rintro ⟨⟨⟩⟩ <;> simp))))

/--
theorem `of_is_product'` / 定理 `of_is_product'`

English:
theorem of_is_product'
  given: (h : Limits.IsLimit (BinaryFan.mk fst snd)) (t : IsTerminal Z)
  proof: of_is_product h t

中文:
定理 of_is_product'
  条件: (h : Limits.是极限 (BinaryFan.mk fst snd)) (t : 是终止 Z)
  证明: of_is_product h t

Depends on / 依赖: of_is_product
-/
theorem of_is_product' (h : Limits.IsLimit (BinaryFan.mk fst snd)) (t : IsTerminal Z) :
    IsPullback fst snd (t.from _) (t.from _) :=
  of_is_product h t

variable (X Y) in
/--
theorem `of_hasBinaryProduct'` / 定理 `of_hasBinaryProduct'`

English:
theorem of_hasBinaryProduct'
  given: [HasBinaryProduct X Y] [HasTerminal C]
  proof: of_is_product (limit.isLimit _) terminalIsTerminal

中文:
定理 of_hasBinaryProduct'
  条件: [HasBinaryProduct X Y] [有终止 C]
  证明: of_is_product (limit.isLimit _) terminalIsTerminal

Depends on / 依赖: isLimit, limit.isLimit, of_is_product, terminalIsTerminal
-/
theorem of_hasBinaryProduct' [HasBinaryProduct X Y] [HasTerminal C] :
    IsPullback Limits.prod.fst Limits.prod.snd (terminal.from X) (terminal.from Y) :=
  of_is_product (limit.isLimit _) terminalIsTerminal

/--
theorem `of_iso_pullback` / 定理 `of_iso_pullback`

English:
theorem of_iso_pullback
  statement: (h : CommSq fst snd f g) [HasPullback f g] (i : P ≅ pullback f g)
  proof: of_isLimit' h
    (Limits.IsLimit.ofIsoLimit (limit.isLimit _)
      (@PullbackCone.ext _ _ _ _ _ _ _ (PullbackCone.mk _ _ _) _ i w₁.symm w₂.symm).symm)

中文:
定理 of_iso_pullback
  结论: (h : 交换Sq fst snd f g) [HasPullback f g] (i : P ≅ pullback f g)
  证明: of_isLimit' h
    (Limits.IsLimit.ofIsoLimit (limit.isLimit _)
      (@PullbackCone.ext _ _ _ _ _ _ _ (PullbackCone.mk _ _ _) _ i w₁.symm w₂.symm).symm)

Depends on / 依赖: IsLimit, Limits, Limits.IsLimit.ofIsoLimit, PullbackCone, PullbackCone.ext, PullbackCone.mk, isLimit, limit.isLimit, ofIsoLimit, of_isLimit
-/
theorem of_iso_pullback (h : CommSq fst snd f g) [HasPullback f g] (i : P ≅ pullback f g)
    (w₁ : i.hom ≫ pullback.fst _ _ = fst) (w₂ : i.hom ≫ pullback.snd _ _ = snd) :
      IsPullback fst snd f g :=
  of_isLimit' h
    (Limits.IsLimit.ofIsoLimit (limit.isLimit _)
      (@PullbackCone.ext _ _ _ _ _ _ _ (PullbackCone.mk _ _ _) _ i w₁.symm w₂.symm).symm)

/--
theorem `of_horiz_isIso_mono` / 定理 `of_horiz_isIso_mono`

English:
theorem of_horiz_isIso_mono
  given: [IsIso fst] [Mono g] (sq : CommSq fst snd f g)
  proof: of_isLimit' sq
    (by
      refine
        PullbackCone.IsLimit.mk _ (fun s => s.fst ≫ inv fst) (by simp)
          (fun s => ?_) (by cat_disch)
      simp only [← cancel_mono g, Category.assoc, ← sq.w, IsIso.inv_hom_id_assoc, s.condition])

中文:
定理 of_horiz_isIso_mono
  条件: [是同构 fst] [单态射 g] (sq : 交换Sq fst snd f g)
  证明: of_isLimit' sq
    (by
      refine
        PullbackCone.IsLimit.mk _ (fun s => s.fst ≫ inv fst) (by simp)
          (fun s => ?_) (by cat_disch)
      simp only [← cancel_mono g, Category.assoc, ← sq.w, IsIso.inv_hom_id_assoc, s.condition])

Depends on / 依赖: Category, Category.assoc, IsIso.inv_hom_id_assoc, IsLimit, PullbackCone, PullbackCone.IsLimit.mk, cancel_mono, cat_disch, condition, inv_hom_id_assoc, of_isLimit, s.condition, s.fst, sq.w
-/
theorem of_horiz_isIso_mono [IsIso fst] [Mono g] (sq : CommSq fst snd f g) :
    IsPullback fst snd f g :=
  of_isLimit' sq
    (by
      refine
        PullbackCone.IsLimit.mk _ (fun s => s.fst ≫ inv fst) (by simp)
          (fun s => ?_) (by cat_disch)
      simp only [← cancel_mono g, Category.assoc, ← sq.w, IsIso.inv_hom_id_assoc, s.condition])

/--
theorem `of_horiz_isIso` / 定理 `of_horiz_isIso`

English:
theorem of_horiz_isIso
  given: [IsIso fst] [IsIso g] (sq : CommSq fst snd f g)
  proof: of_horiz_isIso_mono sq

中文:
定理 of_horiz_isIso
  条件: [是同构 fst] [是同构 g] (sq : 交换Sq fst snd f g)
  证明: of_horiz_isIso_mono sq

Depends on / 依赖: of_horiz_isIso_mono
-/
theorem of_horiz_isIso [IsIso fst] [IsIso g] (sq : CommSq fst snd f g) :
    IsPullback fst snd f g :=
  of_horiz_isIso_mono sq

/--
lemma `of_iso` / 引理 `of_iso`

English:
lemma of_iso
  statement: (h : IsPullback fst snd f g)
  proof: by
    rw [← cancel_epi e₁.hom]; rw [← reassoc_of% commfst]; rw [← commf]; rw [← reassoc_of% commsnd]; rw [← commg]; rw [h.w_assoc]
  isLimit' :=
    ⟨(IsLimit.postcomposeInvEquiv
        (cospanExt e₂ e₃ e₄ commf.symm commg.symm) _).1
          (IsLimit.ofIsoLimit h.isLimit (by
            refine P

中文:
引理 of_iso
  结论: (h : 是拉回 fst snd f g)
  证明: by
    rw [← cancel_epi e₁.hom]; rw [← reassoc_of% commfst]; rw [← commf]; rw [← reassoc_of% commsnd]; rw [← commg]; rw [h.w_assoc]
  isLimit' :=
    ⟨(IsLimit.postcomposeInvEquiv
        (cospanExt e₂ e₃ e₄ commf.symm commg.symm) _).1
          (IsLimit.ofIsoLimit h.isLimit (by
            refine P

Depends on / 依赖: Category, Category.comp_id, IsLimit, IsLimit.ofIsoLimit, IsLimit.postcomposeInvEquiv, PullbackCone, PullbackCone.ext, cancel_epi, commf.symm, commfst, commg.symm, commsnd, comp_id, cospanExt, h.isLimit, h.w_assoc, hom_inv_id, isLimit, ofIsoLimit, postcomposeInvEquiv
-/
lemma of_iso (h : IsPullback fst snd f g)
    {P' X' Y' Z' : C} {fst' : P' ⟶ X'} {snd' : P' ⟶ Y'} {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'}
    (e₁ : P ≅ P') (e₂ : X ≅ X') (e₃ : Y ≅ Y') (e₄ : Z ≅ Z')
    (commfst : fst ≫ e₂.hom = e₁.hom ≫ fst')
    (commsnd : snd ≫ e₃.hom = e₁.hom ≫ snd')
    (commf : f ≫ e₄.hom = e₂.hom ≫ f')
    (commg : g ≫ e₄.hom = e₃.hom ≫ g') :
    IsPullback fst' snd' f' g' where
  w := by
    rw [← cancel_epi e₁.hom]; rw [← reassoc_of% commfst]; rw [← commf]; rw [← reassoc_of% commsnd]; rw [← commg]; rw [h.w_assoc]
  isLimit' :=
    ⟨(IsLimit.postcomposeInvEquiv
        (cospanExt e₂ e₃ e₄ commf.symm commg.symm) _).1
          (IsLimit.ofIsoLimit h.isLimit (by
            refine PullbackCone.ext e₁ ?_ ?_
            · change fst = e₁.hom ≫ fst' ≫ e₂.inv
              rw [← reassoc_of% commfst]; rw [e₂.hom_inv_id]; rw [Category.comp_id]
            · change snd = e₁.hom ≫ snd' ≫ e₃.inv
              rw [← reassoc_of% commsnd]; rw [e₃.hom_inv_id]; rw [Category.comp_id]))⟩

/--
lemma `of_iso'` / 引理 `of_iso'`

English:
lemma of_iso'
  statement: (h : IsPullback fst snd f g)
  proof: by
  apply h.of_iso e₁.symm e₂.symm e₃.symm e₄.symm
  · simp only [Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, ← commfst, Iso.inv_hom_id_assoc]
  · simp only [Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, ← commsnd, Iso.inv_hom_id_assoc]
  · simp only [Iso.symm_hom, Iso.comp_inv_eq, Category.ass

中文:
引理 of_iso'
  结论: (h : 是拉回 fst snd f g)
  证明: by
  apply h.of_iso e₁.symm e₂.symm e₃.symm e₄.symm
  · simp only [Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, ← commfst, Iso.inv_hom_id_assoc]
  · simp only [Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, ← commsnd, Iso.inv_hom_id_assoc]
  · simp only [Iso.symm_hom, Iso.comp_inv_eq, Category.ass

Depends on / 依赖: Category, Category.assoc, Iso.comp_inv_eq, Iso.inv_hom_id_assoc, Iso.symm_hom, commfst, commsnd, comp_inv_eq, h.of_iso, inv_hom_id_assoc, of_iso, symm_hom
-/
lemma of_iso' (h : IsPullback fst snd f g)
    {P' X' Y' Z' : C} {fst' : P' ⟶ X'} {snd' : P' ⟶ Y'} {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'}
    (e₁ : P' ≅ P) (e₂ : X' ≅ X) (e₃ : Y' ≅ Y) (e₄ : Z' ≅ Z)
    (commfst : e₁.hom ≫ fst = fst' ≫ e₂.hom)
    (commsnd : e₁.hom ≫ snd = snd' ≫ e₃.hom)
    (commf : e₂.hom ≫ f = f' ≫ e₄.hom)
    (commg : e₃.hom ≫ g = g' ≫ e₄.hom) :
    IsPullback fst' snd' f' g' := by
  apply h.of_iso e₁.symm e₂.symm e₃.symm e₄.symm
  · simp only [Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, ← commfst, Iso.inv_hom_id_assoc]
  · simp only [Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, ← commsnd, Iso.inv_hom_id_assoc]
  · simp only [Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, ← commf, Iso.inv_hom_id_assoc]
  · simp only [Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, ← commg, Iso.inv_hom_id_assoc]

section

variable {P X Y : C} {fst : P ⟶ X} {snd : P ⟶ X} {f : X ⟶ Y}

/--
lemma `isIso_fst_of_mono` / 引理 `isIso_fst_of_mono`

English:
lemma isIso_fst_of_mono
  given: (h : IsPullback fst snd f f) (inst : Mono f := by infer_instance)
  proof: h.cone.isIso_fst_of_mono_of_isLimit h.isLimit

中文:
引理 isIso_fst_of_mono
  条件: (h : 是拉回 fst snd f f) (inst : 单态射 f := by infer_instance)
  证明: h.cone.isIso_fst_of_mono_of_isLimit h.isLimit

Depends on / 依赖: h.cone.isIso_fst_of_mono_of_isLimit, h.isLimit, infer_instance, isIso_fst_of_mono_of_isLimit, isLimit
-/
lemma isIso_fst_of_mono (h : IsPullback fst snd f f) (inst : Mono f := by infer_instance) :
    IsIso fst := h.cone.isIso_fst_of_mono_of_isLimit h.isLimit

/--
lemma `isIso_snd_iso_of_mono` / 引理 `isIso_snd_iso_of_mono`

English:
lemma isIso_snd_iso_of_mono
  given: (h : IsPullback fst snd f f) (inst : Mono f := by infer_instance)
  proof: h.cone.isIso_snd_of_mono_of_isLimit h.isLimit

中文:
引理 isIso_snd_iso_of_mono
  条件: (h : 是拉回 fst snd f f) (inst : 单态射 f := by infer_instance)
  证明: h.cone.isIso_snd_of_mono_of_isLimit h.isLimit

Depends on / 依赖: HasPullback, HasPullbacksAlong, HasPullbacksAlong.hasPullback, IsPullback, IsPullback.hasPullback, IsPullback.of_hasPullback, IsPullback.paste_horiz, P.pullback_snd, h.cone.isIso_snd_of_mono_of_isLimit, h.isLimit, hasPullback, infer_instance, isIso_snd_of_mono_of_isLimit, isLimit, of_hasPullback, paste_horiz, pullback, pullback.snd, pullback_snd
-/
lemma isIso_snd_iso_of_mono (h : IsPullback fst snd f f) (inst : Mono f := by infer_instance) :
    IsIso snd := h.cone.isIso_snd_of_mono_of_isLimit h.isLimit

end

section

/--
lemma `mono_fst_of_mono` / 引理 `mono_fst_of_mono`

English:
lemma mono_fst_of_mono
  given: (h : IsPullback fst snd f g) (inst : Mono g := by infer_instance)
  proof: by
  constructor
  intro W fst' snd' heq
  exact h.hom_ext heq (by simp [← cancel_mono g, ← h.w, reassoc_of% heq])

中文:
引理 mono_fst_of_mono
  条件: (h : 是拉回 fst snd f g) (inst : 单态射 g := by infer_instance)
  证明: by
  constructor
  intro W fst' snd' heq
  exact h.hom_ext heq (by simp [← cancel_mono g, ← h.w, reassoc_of% heq])

Depends on / 依赖: HasPullback, HasPullbacksAlong, HasPullbacksAlong.hasPullback, IsPullback, IsPullback.of_hasPullback, IsPullback.of_right, IsStableUnderBaseChangeAlong, IsStableUnderBaseChangeAlong.of_isPullback, cancel_mono, h.hom_ext, hasPullback, hom_ext, infer_instance, of_hasPullback, of_isPullback, of_right, reassoc_of
-/
lemma mono_fst_of_mono (h : IsPullback fst snd f g) (inst : Mono g := by infer_instance) :
    Mono fst := by
  constructor
  intro W fst' snd' heq
  exact h.hom_ext heq (by simp [← cancel_mono g, ← h.w, reassoc_of% heq])

/--
lemma `mono_snd_of_mono` / 引理 `mono_snd_of_mono`

English:
lemma mono_snd_of_mono
  given: (h : IsPullback fst snd f g) (inst : Mono f := by infer_instance)
  proof: h.flip.mono_fst_of_mono

中文:
引理 mono_snd_of_mono
  条件: (h : 是拉回 fst snd f g) (inst : 单态射 f := by infer_instance)
  证明: h.flip.mono_fst_of_mono

Depends on / 依赖: HasPushout, HasPushoutsAlong, HasPushoutsAlong.hasPushout, IsPushout, IsPushout.hasPushout, IsPushout.paste_vert, P.pushout_inr, h.flip.mono_fst_of_mono, hasPushout, infer_instance, mono_fst_of_mono, of_hasPushout, paste_vert, pushout, pushout.inr, pushout_inr
-/
lemma mono_snd_of_mono (h : IsPullback fst snd f g) (inst : Mono f := by infer_instance) :
    Mono snd :=
  h.flip.mono_fst_of_mono

/--
lemma `isIso_fst_of_isIso` / 引理 `isIso_fst_of_isIso`

English:
lemma isIso_fst_of_isIso
  given: (h : IsPullback fst snd f g) (inst : IsIso g := by infer_instance)
  proof: by
  have := h.hasPullback
  rw [← h.isoPullback_hom_fst]
  infer_instance

中文:
引理 isIso_fst_of_isIso
  条件: (h : 是拉回 fst snd f g) (inst : 是同构 g := by infer_instance)
  证明: by
  have := h.hasPullback
  rw [← h.isoPullback_hom_fst]
  infer_instance

Depends on / 依赖: HasPushout, HasPushoutsAlong, HasPushoutsAlong.hasPushout, IsPushout, IsPushout.of_hasPushout, IsPushout.of_left, IsStableUnderCobaseChangeAlong, IsStableUnderCobaseChangeAlong.of_isPushout, h.hasPullback, h.isoPullback_hom_fst, hasPullback, hasPushout, infer_instance, isoPullback_hom_fst, of_hasPushout, of_isPushout, of_left, right.flip
-/
lemma isIso_fst_of_isIso (h : IsPullback fst snd f g) (inst : IsIso g := by infer_instance) :
    IsIso fst := by
  have := h.hasPullback
  rw [← h.isoPullback_hom_fst]
  infer_instance

/--
lemma `isIso_snd_of_isIso` / 引理 `isIso_snd_of_isIso`

English:
lemma isIso_snd_of_isIso
  given: (h : IsPullback fst snd f g) (inst : IsIso f := by infer_instance)
  proof: h.flip.isIso_fst_of_isIso

中文:
引理 isIso_snd_of_isIso
  条件: (h : 是拉回 fst snd f g) (inst : 是同构 f := by infer_instance)
  证明: h.flip.isIso_fst_of_isIso

Depends on / 依赖: h.flip.isIso_fst_of_isIso, infer_instance, isIso_fst_of_isIso
-/
lemma isIso_snd_of_isIso (h : IsPullback fst snd f g) (inst : IsIso f := by infer_instance) :
    IsIso snd :=
  h.flip.isIso_fst_of_isIso

end

section
-- Objects here are arranged in a 3x2 grid, and indexed by their xy coordinates.
-- Morphisms are named `hᵢⱼ` for a horizontal morphism starting at `(i,j)`,
-- and `vᵢⱼ` for a vertical morphism starting at `(i,j)`.
/--
theorem `paste_vert` / 定理 `paste_vert`

English:
theorem paste_vert
  statement: {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂}
  proof: of_isLimit (pasteHorizIsPullback rfl t.isLimit s.isLimit)

中文:
定理 paste_vert
  结论: {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂}
  证明: of_isLimit (pasteHorizIsPullback rfl t.isLimit s.isLimit)

Depends on / 依赖: isLimit, of_isLimit, pasteHorizIsPullback, s.isLimit, t.isLimit
-/
theorem paste_vert {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂}
    {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ X₃₁} {v₂₂ : X₂₂ ⟶ X₃₂}
    (s : IsPullback h₁₁ v₁₁ v₁₂ h₂₁) (t : IsPullback h₂₁ v₂₁ v₂₂ h₃₁) :
    IsPullback h₁₁ (v₁₁ ≫ v₂₁) (v₁₂ ≫ v₂₂) h₃₁ :=
  of_isLimit (pasteHorizIsPullback rfl t.isLimit s.isLimit)

/--
theorem `paste_horiz` / 定理 `paste_horiz`

English:
theorem paste_horiz
  statement: {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃}
  proof: (paste_vert s.flip t.flip).flip

中文:
定理 paste_horiz
  结论: {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃}
  证明: (paste_vert s.flip t.flip).flip

Depends on / 依赖: paste_vert, s.flip, t.flip
-/
theorem paste_horiz {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃}
    {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₃ ⟶ X₂₃}
    (s : IsPullback h₁₁ v₁₁ v₁₂ h₂₁) (t : IsPullback h₁₂ v₁₂ v₁₃ h₂₂) :
    IsPullback (h₁₁ ≫ h₁₂) v₁₁ v₁₃ (h₂₁ ≫ h₂₂) :=
  (paste_vert s.flip t.flip).flip

/--
theorem `of_bot` / 定理 `of_bot`

English:
theorem of_bot
  statement: {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂}
  proof: of_isLimit (leftSquareIsPullback (PullbackCone.mk h₁₁ _ p) rfl t.isLimit s.isLimit)

中文:
定理 of_bot
  结论: {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂}
  证明: of_isLimit (leftSquareIsPullback (PullbackCone.mk h₁₁ _ p) rfl t.isLimit s.isLimit)

Depends on / 依赖: PullbackCone, PullbackCone.mk, isLimit, leftSquareIsPullback, of_isLimit, s.isLimit, t.isLimit
-/
theorem of_bot {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂}
    {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ X₃₁} {v₂₂ : X₂₂ ⟶ X₃₂}
    (s : IsPullback h₁₁ (v₁₁ ≫ v₂₁) (v₁₂ ≫ v₂₂) h₃₁) (p : h₁₁ ≫ v₁₂ = v₁₁ ≫ h₂₁)
    (t : IsPullback h₂₁ v₂₁ v₂₂ h₃₁) : IsPullback h₁₁ v₁₁ v₁₂ h₂₁ :=
  of_isLimit (leftSquareIsPullback (PullbackCone.mk h₁₁ _ p) rfl t.isLimit s.isLimit)

/--
theorem `of_right` / 定理 `of_right`

English:
theorem of_right
  statement: {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂}
  proof: (of_bot s.flip p.symm t.flip).flip

中文:
定理 of_right
  结论: {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂}
  证明: (of_bot s.flip p.symm t.flip).flip

Depends on / 依赖: of_bot, p.symm, s.flip, t.flip
-/
theorem of_right {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂}
    {h₂₂ : X₂₂ ⟶ X₂₃} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₃ ⟶ X₂₃}
    (s : IsPullback (h₁₁ ≫ h₁₂) v₁₁ v₁₃ (h₂₁ ≫ h₂₂)) (p : h₁₁ ≫ v₁₂ = v₁₁ ≫ h₂₁)
    (t : IsPullback h₁₂ v₁₂ v₁₃ h₂₂) : IsPullback h₁₁ v₁₁ v₁₂ h₂₁ :=
  (of_bot s.flip p.symm t.flip).flip

/--
theorem `paste_vert_iff` / 定理 `paste_vert_iff`

English:
theorem paste_vert_iff
  statement: {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂}
  proof: ⟨fun h => h.of_bot e s, fun h => h.paste_vert s⟩

中文:
定理 paste_vert_iff
  结论: {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂}
  证明: ⟨fun h => h.of_bot e s, fun h => h.paste_vert s⟩

Depends on / 依赖: h.of_bot, h.paste_vert, of_bot, paste_vert
-/
theorem paste_vert_iff {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂}
    {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ X₃₁} {v₂₂ : X₂₂ ⟶ X₃₂}
    (s : IsPullback h₂₁ v₂₁ v₂₂ h₃₁) (e : h₁₁ ≫ v₁₂ = v₁₁ ≫ h₂₁) :
    IsPullback h₁₁ (v₁₁ ≫ v₂₁) (v₁₂ ≫ v₂₂) h₃₁ ↔ IsPullback h₁₁ v₁₁ v₁₂ h₂₁ :=
  ⟨fun h => h.of_bot e s, fun h => h.paste_vert s⟩

/--
theorem `paste_horiz_iff` / 定理 `paste_horiz_iff`

English:
theorem paste_horiz_iff
  statement: {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃}
  proof: ⟨fun h => h.of_right e s, fun h => h.paste_horiz s⟩

中文:
定理 paste_horiz_iff
  结论: {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃}
  证明: ⟨fun h => h.of_right e s, fun h => h.paste_horiz s⟩

Depends on / 依赖: h.of_right, h.paste_horiz, of_right, paste_horiz
-/
theorem paste_horiz_iff {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃}
    {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₃ ⟶ X₂₃}
    (s : IsPullback h₁₂ v₁₂ v₁₃ h₂₂) (e : h₁₁ ≫ v₁₂ = v₁₁ ≫ h₂₁) :
    IsPullback (h₁₁ ≫ h₁₂) v₁₁ v₁₃ (h₂₁ ≫ h₂₂) ↔ IsPullback h₁₁ v₁₁ v₁₂ h₂₁ :=
  ⟨fun h => h.of_right e s, fun h => h.paste_horiz s⟩

/--
theorem `of_right'` / 定理 `of_right'`

English:
theorem of_right'
  statement: {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂}
  proof: of_right ((t.lift_fst _ _ _) ▸ s) (t.lift_snd _ _ _) t

中文:
定理 of_right'
  结论: {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂}
  证明: of_right ((t.lift_fst _ _ _) ▸ s) (t.lift_snd _ _ _) t

Depends on / 依赖: lift_fst, lift_snd, of_right, t.lift_fst, t.lift_snd
-/
theorem of_right' {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂}
    {h₂₂ : X₂₂ ⟶ X₂₃} {h₁₃ : X₁₁ ⟶ X₁₃} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₃ ⟶ X₂₃}
    (s : IsPullback h₁₃ v₁₁ v₁₃ (h₂₁ ≫ h₂₂)) (t : IsPullback h₁₂ v₁₂ v₁₃ h₂₂) :
    IsPullback (t.lift h₁₃ (v₁₁ ≫ h₂₁) (by rw [s.w, Category.assoc])) v₁₁ v₁₂ h₂₁ :=
  of_right ((t.lift_fst _ _ _) ▸ s) (t.lift_snd _ _ _) t

/--
theorem `of_bot'` / 定理 `of_bot'`

English:
theorem of_bot'
  statement: {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂}
  proof: of_bot ((t.lift_snd _ _ _) ▸ s) (by simp only [lift_fst]) t

中文:
定理 of_bot'
  结论: {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂}
  证明: of_bot ((t.lift_snd _ _ _) ▸ s) (by simp only [lift_fst]) t

Depends on / 依赖: lift_fst, lift_snd, of_bot, t.lift_snd
-/
theorem of_bot' {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂}
    {h₃₁ : X₃₁ ⟶ X₃₂} {v₃₁ : X₁₁ ⟶ X₃₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ X₃₁} {v₂₂ : X₂₂ ⟶ X₃₂}
    (s : IsPullback h₁₁ v₃₁ (v₁₂ ≫ v₂₂) h₃₁) (t : IsPullback h₂₁ v₂₁ v₂₂ h₃₁) :
    IsPullback h₁₁ (t.lift (h₁₁ ≫ v₁₂) v₃₁ (by rw [Category.assoc, s.w])) v₁₂ h₂₁ :=
  of_bot ((t.lift_snd _ _ _) ▸ s) (by simp only [lift_fst]) t

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasPullbacksAlong
  signature: f] (h
  body: IsPullback.hasPullback (IsPullback.of_bot' (IsPullback.of_hasPullback (h ≫ g) f)
    (IsPullback.of_hasPullback g f))

中文:
实例 [有PullbacksAlong
  签名: f] (h
  定义体: IsPullback.hasPullback (IsPullback.of_bot' (IsPullback.of_hasPullback (h ≫ g) f)
    (IsPullback.of_hasPullback g f))

Depends on / 依赖: IsPullback, IsPullback.hasPullback, IsPullback.of_bot, IsPullback.of_hasPullback, hasPullback, of_bot, of_hasPullback
-/
instance [HasPullbacksAlong f] (h : P ⟶ Y) : HasPullback h (pullback.fst g f) :=
  IsPullback.hasPullback (IsPullback.of_bot' (IsPullback.of_hasPullback (h ≫ g) f)
    (IsPullback.of_hasPullback g f))

/--
theorem `of_vert_isIso_mono` / 定理 `of_vert_isIso_mono`

English:
theorem of_vert_isIso_mono
  given: [IsIso snd] [Mono f] (sq : CommSq fst snd f g)
  proof: IsPullback.flip (of_horiz_isIso_mono sq.flip)

中文:
定理 of_vert_isIso_mono
  条件: [是同构 snd] [单态射 f] (sq : 交换Sq fst snd f g)
  证明: IsPullback.flip (of_horiz_isIso_mono sq.flip)

Depends on / 依赖: IsPullback, IsPullback.flip, of_horiz_isIso_mono, sq.flip
-/
theorem of_vert_isIso_mono [IsIso snd] [Mono f] (sq : CommSq fst snd f g) :
    IsPullback fst snd f g :=
  IsPullback.flip (of_horiz_isIso_mono sq.flip)

/--
theorem `of_vert_isIso` / 定理 `of_vert_isIso`

English:
theorem of_vert_isIso
  given: [IsIso snd] [IsIso f] (sq : CommSq fst snd f g)
  proof: of_vert_isIso_mono sq

中文:
定理 of_vert_isIso
  条件: [是同构 snd] [是同构 f] (sq : 交换Sq fst snd f g)
  证明: of_vert_isIso_mono sq

Depends on / 依赖: of_vert_isIso_mono
-/
theorem of_vert_isIso [IsIso snd] [IsIso f] (sq : CommSq fst snd f g) :
    IsPullback fst snd f g :=
  of_vert_isIso_mono sq

/--
lemma `of_id_fst` / 引理 `of_id_fst`

English:
lemma of_id_fst
  statement: IsPullback (𝟙 _) f f (𝟙 _)
  proof: IsPullback.of_horiz_isIso ⟨by simp⟩

中文:
引理 of_id_fst
  结论: 是拉回 (𝟙 _) f f (𝟙 _)
  证明: IsPullback.of_horiz_isIso ⟨by simp⟩

Depends on / 依赖: IsPullback, IsPullback.of_horiz_isIso, of_horiz_isIso
-/
lemma of_id_fst : IsPullback (𝟙 _) f f (𝟙 _) := IsPullback.of_horiz_isIso ⟨by simp⟩

/--
lemma `of_id_snd` / 引理 `of_id_snd`

English:
lemma of_id_snd
  statement: IsPullback f (𝟙 _) (𝟙 _) f
  proof: IsPullback.of_vert_isIso ⟨by simp⟩

中文:
引理 of_id_snd
  结论: 是拉回 f (𝟙 _) (𝟙 _) f
  证明: IsPullback.of_vert_isIso ⟨by simp⟩

Depends on / 依赖: IsPullback, IsPullback.of_vert_isIso, of_vert_isIso
-/
lemma of_id_snd : IsPullback f (𝟙 _) (𝟙 _) f := IsPullback.of_vert_isIso ⟨by simp⟩

/--
lemma `id_vert` / 引理 `id_vert`

English:
lemma id_vert
  given: (f : X ⟶ Z)
  statement: IsPullback f (𝟙 X) (𝟙 Z) f
  proof: of_vert_isIso ⟨by simp only [Category.id_comp, Category.comp_id]⟩

中文:
引理 id_vert
  条件: (f : X ⟶ Z)
  结论: 是拉回 f (𝟙 X) (𝟙 Z) f
  证明: of_vert_isIso ⟨by simp only [Category.id_comp, Category.comp_id]⟩

Depends on / 依赖: Category, Category.comp_id, Category.id_comp, comp_id, id_comp, of_vert_isIso
-/
lemma id_vert (f : X ⟶ Z) : IsPullback f (𝟙 X) (𝟙 Z) f :=
  of_vert_isIso ⟨by simp only [Category.id_comp, Category.comp_id]⟩

/--
lemma `id_horiz` / 引理 `id_horiz`

English:
lemma id_horiz
  given: (f : X ⟶ Z)
  statement: IsPullback (𝟙 X) f f (𝟙 Z)
  proof: of_horiz_isIso ⟨by simp only [Category.id_comp, Category.comp_id]⟩

中文:
引理 id_horiz
  条件: (f : X ⟶ Z)
  结论: 是拉回 (𝟙 X) f f (𝟙 Z)
  证明: of_horiz_isIso ⟨by simp only [Category.id_comp, Category.comp_id]⟩

Depends on / 依赖: Category, Category.comp_id, Category.id_comp, comp_id, id_comp, of_horiz_isIso
-/
lemma id_horiz (f : X ⟶ Z) : IsPullback (𝟙 X) f f (𝟙 Z) :=
  of_horiz_isIso ⟨by simp only [Category.id_comp, Category.comp_id]⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `of_prod_fst_with_id` / 引理 `of_prod_fst_with_id`

English:
lemma of_prod_fst_with_id
  statement: {A B : C} (f : A ⟶ B) (X : C) [HasBinaryProduct A X]
  proof: ⟨PullbackCone.isLimitAux' _ (fun s => by
    refine ⟨prod.lift s.fst (s.snd ≫ prod.snd), ?_, ?_, ?_⟩
    · simp
    · ext
      · simp [PullbackCone.condition]
      · simp
    · intro m h₁ h₂
      dsimp at m h₁ h₂ ⊢
      ext
      · simpa using h₁
      · simp [← h₂])⟩

中文:
引理 of_prod_fst_with_id
  结论: {A B : C} (f : A ⟶ B) (X : C) [HasBinaryProduct A X]
  证明: ⟨PullbackCone.isLimitAux' _ (fun s => by
    refine ⟨prod.lift s.fst (s.snd ≫ prod.snd), ?_, ?_, ?_⟩
    · simp
    · ext
      · simp [PullbackCone.condition]
      · simp
    · intro m h₁ h₂
      dsimp at m h₁ h₂ ⊢
      ext
      · simpa using h₁
      · simp [← h₂])⟩

Depends on / 依赖: PullbackCone, PullbackCone.condition, PullbackCone.isLimitAux, condition, isLimitAux, prod.lift, prod.snd, s.fst, s.snd
-/
lemma of_prod_fst_with_id {A B : C} (f : A ⟶ B) (X : C) [HasBinaryProduct A X]
    [HasBinaryProduct B X] :
    IsPullback prod.fst (prod.map f (𝟙 X)) f prod.fst where
  isLimit' := ⟨PullbackCone.isLimitAux' _ (fun s => by
    refine ⟨prod.lift s.fst (s.snd ≫ prod.snd), ?_, ?_, ?_⟩
    · simp
    · ext
      · simp [PullbackCone.condition]
      · simp
    · intro m h₁ h₂
      dsimp at m h₁ h₂ ⊢
      ext
      · simpa using h₁
      · simp [← h₂])⟩

set_option backward.isDefEq.respectTransparency false in
/--
lemma `of_isLimit_binaryFan_of_isTerminal` / 引理 `of_isLimit_binaryFan_of_isTerminal`

English:
lemma of_isLimit_binaryFan_of_isTerminal
  proof: ⟨PullbackCone.IsLimit.mk _
    (fun s => BinaryFan.IsLimit.lift hc s.fst s.snd) (by simp) (by simp)
    (fun s m h₁ h₂ => by apply BinaryFan.IsLimit.hom_ext hc <;> cat_disch)⟩

中文:
引理 of_isLimit_binaryFan_of_isTerminal
  证明: ⟨PullbackCone.IsLimit.mk _
    (fun s => BinaryFan.IsLimit.lift hc s.fst s.snd) (by simp) (by simp)
    (fun s m h₁ h₂ => by apply BinaryFan.IsLimit.hom_ext hc <;> cat_disch)⟩

Depends on / 依赖: IsLimit, PullbackCone, PullbackCone.IsLimit.mk
-/
lemma of_isLimit_binaryFan_of_isTerminal
    {X Y : C} {c : BinaryFan X Y} (hc : IsLimit c)
    {T : C} (hT : IsTerminal T) :
    IsPullback c.fst c.snd (hT.from _) (hT.from _) where
  isLimit' := ⟨PullbackCone.IsLimit.mk _
    (fun s => BinaryFan.IsLimit.lift hc s.fst s.snd) (by simp) (by simp)
    (fun s m h₁ h₂ => by apply BinaryFan.IsLimit.hom_ext hc <;> cat_disch)⟩
end

/--
lemma `mk'` / 引理 `mk'`

English:
lemma mk'
  statement: {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
  proof: w
  isLimit' := by
    let l (s : PullbackCone f g) := exists_lift _ _ s.condition
    exact ⟨PullbackCone.IsLimit.mk _
      (fun s => (l s).choose)
      (fun s => (l s).choose_spec.1)
      (fun s => (l s).choose_spec.2)
      (fun s m h₁ h₂ => hom_ext
        (h₁.trans (l s).choose_spec.1.symm)


中文:
引理 mk'
  结论: {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
  证明: w
  isLimit' := by
    let l (s : PullbackCone f g) := exists_lift _ _ s.condition
    exact ⟨PullbackCone.IsLimit.mk _
      (fun s => (l s).choose)
      (fun s => (l s).choose_spec.1)
      (fun s => (l s).choose_spec.2)
      (fun s m h₁ h₂ => hom_ext
        (h₁.trans (l s).choose_spec.1.symm)

-/
lemma mk' {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (w : fst ≫ f = snd ≫ g)
    (hom_ext : forall ⦃T : C⦄ ⦃φ φ' : T ⟶ P⦄ (_ : φ ≫ fst = φ' ≫ fst)
      (_ : φ ≫ snd = φ' ≫ snd), φ = φ')
    (exists_lift : forall ⦃T : C⦄ (a : T ⟶ X) (b : T ⟶ Y)
      (_ : a ≫ f = b ≫ g), exists (l : T ⟶ P), l ≫ fst = a ∧ l ≫ snd = b) :
    IsPullback fst snd f g where
  w := w
  isLimit' := by
    let l (s : PullbackCone f g) := exists_lift _ _ s.condition
    exact ⟨PullbackCone.IsLimit.mk _
      (fun s => (l s).choose)
      (fun s => (l s).choose_spec.1)
      (fun s => (l s).choose_spec.2)
      (fun s m h₁ h₂ => hom_ext
        (h₁.trans (l s).choose_spec.1.symm)
        (h₂.trans (l s).choose_spec.2.symm))⟩

/--
lemma `paste_twist_right` / 引理 `paste_twist_right`

English:
lemma paste_twist_right
  statement: {X Y Z S : C} {f : X ⟶ S} {g : Y ⟶ S} {i : Z ⟶ S}
  proof: by
  refine .of_right ?_ ht₂ hfi
  rw [← hrw]; rw [ht₁]
  exact .paste_horiz hsndfgr hfg

中文:
引理 paste_twist_right
  结论: {X Y Z S : C} {f : X ⟶ S} {g : Y ⟶ S} {i : Z ⟶ S}
  证明: by
  refine .of_right ?_ ht₂ hfi
  rw [← hrw]; rw [ht₁]
  exact .paste_horiz hsndfgr hfg

Depends on / 依赖: hsndfgr, of_right, paste_horiz
-/
lemma paste_twist_right {X Y Z S : C} {f : X ⟶ S} {g : Y ⟶ S} {i : Z ⟶ S}
    {Pfg : C} {fstfg : Pfg ⟶ X} {sndfg : Pfg ⟶ Y} (hfg : IsPullback fstfg sndfg f g)
    {Pfi : C} {fstfi : Pfi ⟶ X} {sndfi : Pfi ⟶ Z} (hfi : IsPullback fstfi sndfi f i)
    {R : C} (rY : R ⟶ Y) (rZ : R ⟶ Z) (hrw : rY ≫ g = rZ ≫ i)
    {Psndfgr : C} (fstsndfgr : Psndfgr ⟶ Pfg) (sndsndfgr : Psndfgr ⟶ R)
    (hsndfgr : IsPullback fstsndfgr sndsndfgr sndfg rY)
    {t : Psndfgr ⟶ Pfi} (ht₁ : t ≫ fstfi = fstsndfgr ≫ fstfg) (ht₂ : t ≫ sndfi = sndsndfgr ≫ rZ) :
    IsPullback t sndsndfgr sndfi rZ := by
  refine .of_right ?_ ht₂ hfi
  rw [← hrw]; rw [ht₁]
  exact .paste_horiz hsndfgr hfg

set_option backward.isDefEq.respectTransparency false in
/--
lemma `map_fst_comp_fst_snd_comp_fst` / 引理 `map_fst_comp_fst_snd_comp_fst`

English:
lemma map_fst_comp_fst_snd_comp_fst
  statement: {X Y Z U S : C} (f : X ⟶ S) (g : Y ⟶ S) (i : Z ⟶ S)
  proof: paste_twist_right (.of_hasPullback f g) (.of_hasPullback f i) (h ≫ pullback.snd _ _)
    (h ≫ pullback.fst _ _) (by simp [pullback.condition]) _ _ (.of_hasPullback _ _) (by simp)
    (by simp)

中文:
引理 map_fst_comp_fst_snd_comp_fst
  结论: {X Y Z U S : C} (f : X ⟶ S) (g : Y ⟶ S) (i : Z ⟶ S)
  证明: paste_twist_right (.of_hasPullback f g) (.of_hasPullback f i) (h ≫ pullback.snd _ _)
    (h ≫ pullback.fst _ _) (by simp [pullback.condition]) _ _ (.of_hasPullback _ _) (by simp)
    (by simp)

Depends on / 依赖: condition, of_hasPullback, paste_twist_right, pullback, pullback.condition, pullback.fst, pullback.snd
-/
lemma map_fst_comp_fst_snd_comp_fst {X Y Z U S : C} (f : X ⟶ S) (g : Y ⟶ S) (i : Z ⟶ S)
    [HasPullback i g] (h : U ⟶ pullback i g) [HasPullback f g] [HasPullback (pullback.snd f g)
    (h ≫ pullback.snd i g)] [HasPullback f i] :
    IsPullback
      (pullback.map (pullback.snd f g) (h ≫ pullback.snd i g) f i (pullback.fst f g)
        (h ≫ pullback.fst i g) g
        pullback.condition.symm (by simp [pullback.condition]))
      (pullback.snd (pullback.snd f g) (h ≫ pullback.snd i g))
      (pullback.snd f i)
      (h ≫ pullback.fst i g) :=
  paste_twist_right (.of_hasPullback f g) (.of_hasPullback f i) (h ≫ pullback.snd _ _)
    (h ≫ pullback.fst _ _) (by simp [pullback.condition]) _ _ (.of_hasPullback _ _) (by simp)
    (by simp)

end IsPullback
namespace IsPushout

variable {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
theorem `of_is_coproduct` / 定理 `of_is_coproduct`

English:
theorem of_is_coproduct
  given: {c : BinaryCofan X Y} (h : Limits.IsColimit c) (t : IsInitial Z)
  proof: of_isColimit
    (isPushoutOfIsInitialIsCoproduct _ _ _ _ t
      (IsColimit.ofIsoColimit h
        (Limits.Cocone.ext (Iso.refl c.pt)
          (by
            rintro ⟨⟨⟩⟩ <;> simp))))

中文:
定理 of_is_coproduct
  条件: {c : BinaryCofan X Y} (h : Limits.是余极限 c) (t : IsInitial Z)
  证明: of_isColimit
    (isPushoutOfIsInitialIsCoproduct _ _ _ _ t
      (IsColimit.ofIsoColimit h
        (Limits.Cocone.ext (Iso.refl c.pt)
          (by
            rintro ⟨⟨⟩⟩ <;> simp))))

Depends on / 依赖: Cocone, IsColimit, IsColimit.ofIsoColimit, Iso.refl, Limits, Limits.Cocone.ext, c.pt, isPushoutOfIsInitialIsCoproduct, ofIsoColimit, of_isColimit
-/
theorem of_is_coproduct {c : BinaryCofan X Y} (h : Limits.IsColimit c) (t : IsInitial Z) :
    IsPushout (t.to _) (t.to _) c.inl c.inr :=
  of_isColimit
    (isPushoutOfIsInitialIsCoproduct _ _ _ _ t
      (IsColimit.ofIsoColimit h
        (Limits.Cocone.ext (Iso.refl c.pt)
          (by
            rintro ⟨⟨⟩⟩ <;> simp))))

/--
theorem `of_is_coproduct'` / 定理 `of_is_coproduct'`

English:
theorem of_is_coproduct'
  given: (h : Limits.IsColimit (BinaryCofan.mk inl inr)) (t : IsInitial Z)
  proof: of_is_coproduct h t

中文:
定理 of_is_coproduct'
  条件: (h : Limits.是余极限 (BinaryCofan.mk inl inr)) (t : IsInitial Z)
  证明: of_is_coproduct h t

Depends on / 依赖: of_is_coproduct
-/
theorem of_is_coproduct' (h : Limits.IsColimit (BinaryCofan.mk inl inr)) (t : IsInitial Z) :
    IsPushout (t.to _) (t.to _) inl inr :=
  of_is_coproduct h t

variable (X Y) in
/--
theorem `of_hasBinaryCoproduct'` / 定理 `of_hasBinaryCoproduct'`

English:
theorem of_hasBinaryCoproduct'
  given: [HasBinaryCoproduct X Y] [HasInitial C]
  proof: of_is_coproduct (colimit.isColimit _) initialIsInitial

中文:
定理 of_hasBinaryCoproduct'
  条件: [HasBinaryCoproduct X Y] [HasInitial C]
  证明: of_is_coproduct (colimit.isColimit _) initialIsInitial

Depends on / 依赖: colimit, colimit.isColimit, initialIsInitial, isColimit, of_is_coproduct
-/
theorem of_hasBinaryCoproduct' [HasBinaryCoproduct X Y] [HasInitial C] :
    IsPushout (initial.to _) (initial.to _) (coprod.inl : X ⟶ _) (coprod.inr : Y ⟶ _) :=
  of_is_coproduct (colimit.isColimit _) initialIsInitial

/--
theorem `of_iso_pushout` / 定理 `of_iso_pushout`

English:
theorem of_iso_pushout
  statement: (h : CommSq f g inl inr) [HasPushout f g] (i : P ≅ pushout f g)
  proof: of_isColimit' h
    (Limits.IsColimit.ofIsoColimit (colimit.isColimit _)
      (PushoutCocone.ext (s := PushoutCocone.mk ..) i w₁ w₂).symm)

中文:
定理 of_iso_pushout
  结论: (h : 交换Sq f g inl inr) [HasPushout f g] (i : P ≅ pushout f g)
  证明: of_isColimit' h
    (Limits.IsColimit.ofIsoColimit (colimit.isColimit _)
      (PushoutCocone.ext (s := PushoutCocone.mk ..) i w₁ w₂).symm)

Depends on / 依赖: IsColimit, Limits, Limits.IsColimit.ofIsoColimit, PushoutCocone, PushoutCocone.ext, PushoutCocone.mk, colimit, colimit.isColimit, isColimit, ofIsoColimit, of_isColimit
-/
theorem of_iso_pushout (h : CommSq f g inl inr) [HasPushout f g] (i : P ≅ pushout f g)
    (w₁ : inl ≫ i.hom = pushout.inl _ _) (w₂ : inr ≫ i.hom = pushout.inr _ _) :
      IsPushout f g inl inr :=
  of_isColimit' h
    (Limits.IsColimit.ofIsoColimit (colimit.isColimit _)
      (PushoutCocone.ext (s := PushoutCocone.mk ..) i w₁ w₂).symm)

/--
lemma `of_iso` / 引理 `of_iso`

English:
lemma of_iso
  statement: (h : IsPushout f g inl inr)
  proof: by
    rw [← cancel_epi e₁.hom]; rw [← reassoc_of% commf]; rw [← comminl]; rw [← reassoc_of% commg]; rw [← comminr]; rw [h.w_assoc]
  isColimit' :=
    ⟨(IsColimit.precomposeHomEquiv
        (spanExt e₁ e₂ e₃ commf.symm commg.symm) _).1
          (IsColimit.ofIsoColimit h.isColimit
            (Push

中文:
引理 of_iso
  结论: (h : 是推出 f g inl inr)
  证明: by
    rw [← cancel_epi e₁.hom]; rw [← reassoc_of% commf]; rw [← comminl]; rw [← reassoc_of% commg]; rw [← comminr]; rw [h.w_assoc]
  isColimit' :=
    ⟨(IsColimit.precomposeHomEquiv
        (spanExt e₁ e₂ e₃ commf.symm commg.symm) _).1
          (IsColimit.ofIsoColimit h.isColimit
            (Push

Depends on / 依赖: IsColimit, IsColimit.ofIsoColimit, IsColimit.precomposeHomEquiv, PushoutCocone, PushoutCocone.ext, cancel_epi, commf.symm, commg.symm, comminl, comminr, h.isColimit, h.w_assoc, isColimit, ofIsoColimit, precomposeHomEquiv, reassoc_of, spanExt, w_assoc
-/
lemma of_iso (h : IsPushout f g inl inr)
    {Z' X' Y' P' : C} {f' : Z' ⟶ X'} {g' : Z' ⟶ Y'} {inl' : X' ⟶ P'} {inr' : Y' ⟶ P'}
    (e₁ : Z ≅ Z') (e₂ : X ≅ X') (e₃ : Y ≅ Y') (e₄ : P ≅ P')
    (commf : f ≫ e₂.hom = e₁.hom ≫ f')
    (commg : g ≫ e₃.hom = e₁.hom ≫ g')
    (comminl : inl ≫ e₄.hom = e₂.hom ≫ inl')
    (comminr : inr ≫ e₄.hom = e₃.hom ≫ inr') :
    IsPushout f' g' inl' inr' where
  w := by
    rw [← cancel_epi e₁.hom]; rw [← reassoc_of% commf]; rw [← comminl]; rw [← reassoc_of% commg]; rw [← comminr]; rw [h.w_assoc]
  isColimit' :=
    ⟨(IsColimit.precomposeHomEquiv
        (spanExt e₁ e₂ e₃ commf.symm commg.symm) _).1
          (IsColimit.ofIsoColimit h.isColimit
            (PushoutCocone.ext e₄ comminl comminr))⟩

/--
lemma `of_iso'` / 引理 `of_iso'`

English:
lemma of_iso'
  statement: {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}
  proof: by
  apply h.of_iso e₁.symm e₂.symm e₃.symm e₄.symm
  · simp only [Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, ← commf, Iso.inv_hom_id_assoc]
  · simp only [Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, ← commg, Iso.inv_hom_id_assoc]
  · simp only [Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, 

中文:
引理 of_iso'
  结论: {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}
  证明: by
  apply h.of_iso e₁.symm e₂.symm e₃.symm e₄.symm
  · simp only [Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, ← commf, Iso.inv_hom_id_assoc]
  · simp only [Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, ← commg, Iso.inv_hom_id_assoc]
  · simp only [Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, 

Depends on / 依赖: Category, Category.assoc, Iso.comp_inv_eq, Iso.inv_hom_id_assoc, Iso.symm_hom, comminl, comminr, comp_inv_eq, h.of_iso, inv_hom_id_assoc, of_iso, symm_hom
-/
lemma of_iso' {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}
    (h : IsPushout f g inl inr)
    {Z' X' Y' P' : C} {f' : Z' ⟶ X'} {g' : Z' ⟶ Y'} {inl' : X' ⟶ P'} {inr' : Y' ⟶ P'}
    (e₁ : Z' ≅ Z) (e₂ : X' ≅ X) (e₃ : Y' ≅ Y) (e₄ : P' ≅ P)
    (commf : e₁.hom ≫ f = f' ≫ e₂.hom)
    (commg : e₁.hom ≫ g = g' ≫ e₃.hom)
    (comminl : e₂.hom ≫ inl = inl' ≫ e₄.hom)
    (comminr : e₃.hom ≫ inr = inr' ≫ e₄.hom) :
    IsPushout f' g' inl' inr' := by
  apply h.of_iso e₁.symm e₂.symm e₃.symm e₄.symm
  · simp only [Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, ← commf, Iso.inv_hom_id_assoc]
  · simp only [Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, ← commg, Iso.inv_hom_id_assoc]
  · simp only [Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, ← comminl, Iso.inv_hom_id_assoc]
  · simp only [Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, ← comminr, Iso.inv_hom_id_assoc]

section

variable {P X Y : C} {inl : X ⟶ P} {inr : X ⟶ P} {f : Y ⟶ X}

/--
lemma `isIso_inl_iso_of_epi` / 引理 `isIso_inl_iso_of_epi`

English:
lemma isIso_inl_iso_of_epi
  given: (h : IsPushout f f inl inr) (inst : Epi f := by infer_instance)
  proof: h.cocone.isIso_inl_of_epi_of_isColimit h.isColimit

中文:
引理 isIso_inl_iso_of_epi
  条件: (h : 是推出 f f inl inr) (inst : 满态射 f := by infer_instance)
  证明: h.cocone.isIso_inl_of_epi_of_isColimit h.isColimit

Depends on / 依赖: cocone, h.cocone.isIso_inl_of_epi_of_isColimit, h.isColimit, infer_instance, isColimit, isIso_inl_of_epi_of_isColimit
-/
lemma isIso_inl_iso_of_epi (h : IsPushout f f inl inr) (inst : Epi f := by infer_instance) :
    IsIso inl := h.cocone.isIso_inl_of_epi_of_isColimit h.isColimit

/--
lemma `isIso_inr_iso_of_epi` / 引理 `isIso_inr_iso_of_epi`

English:
lemma isIso_inr_iso_of_epi
  given: (h : IsPushout f f inl inr) (inst : Epi f := by infer_instance)
  proof: h.cocone.isIso_inr_of_epi_of_isColimit h.isColimit

中文:
引理 isIso_inr_iso_of_epi
  条件: (h : 是推出 f f inl inr) (inst : 满态射 f := by infer_instance)
  证明: h.cocone.isIso_inr_of_epi_of_isColimit h.isColimit

Depends on / 依赖: cocone, h.cocone.isIso_inr_of_epi_of_isColimit, h.isColimit, infer_instance, isColimit, isIso_inr_of_epi_of_isColimit
-/
lemma isIso_inr_iso_of_epi (h : IsPushout f f inl inr) (inst : Epi f := by infer_instance) :
    IsIso inr := h.cocone.isIso_inr_of_epi_of_isColimit h.isColimit

end

section

/--
lemma `epi_inl_of_epi` / 引理 `epi_inl_of_epi`

English:
lemma epi_inl_of_epi
  given: (h : IsPushout f g inl inr) (inst : Epi g := by infer_instance)
  proof: by
  constructor
  intro W fst' snd' heq
  exact h.hom_ext heq (by simp [← cancel_epi g, ← h.w_assoc, heq])

中文:
引理 epi_inl_of_epi
  条件: (h : 是推出 f g inl inr) (inst : 满态射 g := by infer_instance)
  证明: by
  constructor
  intro W fst' snd' heq
  exact h.hom_ext heq (by simp [← cancel_epi g, ← h.w_assoc, heq])

Depends on / 依赖: cancel_epi, h.hom_ext, h.w_assoc, hom_ext, infer_instance, w_assoc
-/
lemma epi_inl_of_epi (h : IsPushout f g inl inr) (inst : Epi g := by infer_instance) :
    Epi inl := by
  constructor
  intro W fst' snd' heq
  exact h.hom_ext heq (by simp [← cancel_epi g, ← h.w_assoc, heq])

/--
lemma `epi_inr_of_epi` / 引理 `epi_inr_of_epi`

English:
lemma epi_inr_of_epi
  given: (h : IsPushout f g inl inr) (inst : Epi f := by infer_instance)
  proof: h.flip.epi_inl_of_epi

中文:
引理 epi_inr_of_epi
  条件: (h : 是推出 f g inl inr) (inst : 满态射 f := by infer_instance)
  证明: h.flip.epi_inl_of_epi

Depends on / 依赖: epi_inl_of_epi, h.flip.epi_inl_of_epi, infer_instance
-/
lemma epi_inr_of_epi (h : IsPushout f g inl inr) (inst : Epi f := by infer_instance) :
    Epi inr := h.flip.epi_inl_of_epi

/--
lemma `isIso_inl_of_isIso` / 引理 `isIso_inl_of_isIso`

English:
lemma isIso_inl_of_isIso
  given: (h : IsPushout f g inl inr) (inst : IsIso g := by infer_instance)
  proof: by
  have := h.hasPushout
  rw [← h.inl_isoPushout_inv]
  infer_instance

中文:
引理 isIso_inl_of_isIso
  条件: (h : 是推出 f g inl inr) (inst : 是同构 g := by infer_instance)
  证明: by
  have := h.hasPushout
  rw [← h.inl_isoPushout_inv]
  infer_instance

Depends on / 依赖: h.hasPushout, h.inl_isoPushout_inv, hasPushout, infer_instance, inl_isoPushout_inv
-/
lemma isIso_inl_of_isIso (h : IsPushout f g inl inr) (inst : IsIso g := by infer_instance) :
    IsIso inl := by
  have := h.hasPushout
  rw [← h.inl_isoPushout_inv]
  infer_instance

/--
lemma `isIso_inr_of_isIso` / 引理 `isIso_inr_of_isIso`

English:
lemma isIso_inr_of_isIso
  given: (h : IsPushout f g inl inr) (inst : IsIso f := by infer_instance)
  proof: h.flip.isIso_inl_of_isIso

中文:
引理 isIso_inr_of_isIso
  条件: (h : 是推出 f g inl inr) (inst : 是同构 f := by infer_instance)
  证明: h.flip.isIso_inl_of_isIso

Depends on / 依赖: h.flip.isIso_inl_of_isIso, infer_instance, isIso_inl_of_isIso
-/
lemma isIso_inr_of_isIso (h : IsPushout f g inl inr) (inst : IsIso f := by infer_instance) :
    IsIso inr := h.flip.isIso_inl_of_isIso

end

-- Objects here are arranged in a 3x2 grid, and indexed by their xy coordinates.
-- Morphisms are named `hᵢⱼ` for a horizontal morphism starting at `(i,j)`,
-- and `vᵢⱼ` for a vertical morphism starting at `(i,j)`.
/--
theorem `paste_vert` / 定理 `paste_vert`

English:
theorem paste_vert
  statement: {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂}
  proof: of_isColimit (pasteHorizIsPushout rfl s.isColimit t.isColimit)

中文:
定理 paste_vert
  结论: {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂}
  证明: of_isColimit (pasteHorizIsPushout rfl s.isColimit t.isColimit)

Depends on / 依赖: isColimit, of_isColimit, pasteHorizIsPushout, s.isColimit, t.isColimit
-/
theorem paste_vert {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂}
    {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ X₃₁} {v₂₂ : X₂₂ ⟶ X₃₂}
    (s : IsPushout h₁₁ v₁₁ v₁₂ h₂₁) (t : IsPushout h₂₁ v₂₁ v₂₂ h₃₁) :
    IsPushout h₁₁ (v₁₁ ≫ v₂₁) (v₁₂ ≫ v₂₂) h₃₁ :=
  of_isColimit (pasteHorizIsPushout rfl s.isColimit t.isColimit)

/--
theorem `paste_horiz` / 定理 `paste_horiz`

English:
theorem paste_horiz
  statement: {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃}
  proof: (paste_vert s.flip t.flip).flip

中文:
定理 paste_horiz
  结论: {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃}
  证明: (paste_vert s.flip t.flip).flip

Depends on / 依赖: paste_vert, s.flip, t.flip
-/
theorem paste_horiz {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃}
    {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₃ ⟶ X₂₃}
    (s : IsPushout h₁₁ v₁₁ v₁₂ h₂₁) (t : IsPushout h₁₂ v₁₂ v₁₃ h₂₂) :
    IsPushout (h₁₁ ≫ h₁₂) v₁₁ v₁₃ (h₂₁ ≫ h₂₂) :=
  (paste_vert s.flip t.flip).flip

/--
theorem `of_top` / 定理 `of_top`

English:
theorem of_top
  statement: {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂}
  proof: of_isColimit rightSquareIsPushout
    (PushoutCocone.mk _ _ p) (cocone_inr _) t.isColimit s.isColimit

中文:
定理 of_top
  结论: {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂}
  证明: of_isColimit rightSquareIsPushout
    (PushoutCocone.mk _ _ p) (cocone_inr _) t.isColimit s.isColimit

Depends on / 依赖: PushoutCocone, PushoutCocone.mk, cocone_inr, isColimit, of_isColimit, rightSquareIsPushout, s.isColimit, t.isColimit
-/
theorem of_top {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂}
    {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ X₃₁} {v₂₂ : X₂₂ ⟶ X₃₂}
    (s : IsPushout h₁₁ (v₁₁ ≫ v₂₁) (v₁₂ ≫ v₂₂) h₃₁) (p : h₂₁ ≫ v₂₂ = v₂₁ ≫ h₃₁)
    (t : IsPushout h₁₁ v₁₁ v₁₂ h₂₁) : IsPushout h₂₁ v₂₁ v₂₂ h₃₁ :=
of_isColimit rightSquareIsPushout
    (PushoutCocone.mk _ _ p) (cocone_inr _) t.isColimit s.isColimit

/--
theorem `of_left` / 定理 `of_left`

English:
theorem of_left
  statement: {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂}
  proof: (of_top s.flip p.symm t.flip).flip

中文:
定理 of_left
  结论: {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂}
  证明: (of_top s.flip p.symm t.flip).flip

Depends on / 依赖: of_top, p.symm, s.flip, t.flip
-/
theorem of_left {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂}
    {h₂₂ : X₂₂ ⟶ X₂₃} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₃ ⟶ X₂₃}
    (s : IsPushout (h₁₁ ≫ h₁₂) v₁₁ v₁₃ (h₂₁ ≫ h₂₂)) (p : h₁₂ ≫ v₁₃ = v₁₂ ≫ h₂₂)
    (t : IsPushout h₁₁ v₁₁ v₁₂ h₂₁) : IsPushout h₁₂ v₁₂ v₁₃ h₂₂ :=
  (of_top s.flip p.symm t.flip).flip

/--
theorem `paste_vert_iff` / 定理 `paste_vert_iff`

English:
theorem paste_vert_iff
  statement: {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂}
  proof: ⟨fun h => h.of_top e s, s.paste_vert⟩

中文:
定理 paste_vert_iff
  结论: {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂}
  证明: ⟨fun h => h.of_top e s, s.paste_vert⟩

Depends on / 依赖: h.of_top, of_top, paste_vert, s.paste_vert
-/
theorem paste_vert_iff {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂}
    {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ X₃₁} {v₂₂ : X₂₂ ⟶ X₃₂}
    (s : IsPushout h₁₁ v₁₁ v₁₂ h₂₁) (e : h₂₁ ≫ v₂₂ = v₂₁ ≫ h₃₁) :
    IsPushout h₁₁ (v₁₁ ≫ v₂₁) (v₁₂ ≫ v₂₂) h₃₁ ↔ IsPushout h₂₁ v₂₁ v₂₂ h₃₁ :=
  ⟨fun h => h.of_top e s, s.paste_vert⟩

/--
theorem `paste_horiz_iff` / 定理 `paste_horiz_iff`

English:
theorem paste_horiz_iff
  statement: {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃}
  proof: ⟨fun h => h.of_left e s, s.paste_horiz⟩

中文:
定理 paste_horiz_iff
  结论: {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃}
  证明: ⟨fun h => h.of_left e s, s.paste_horiz⟩

Depends on / 依赖: h.of_left, of_left, paste_horiz, s.paste_horiz
-/
theorem paste_horiz_iff {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃}
    {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₃ ⟶ X₂₃}
    (s : IsPushout h₁₁ v₁₁ v₁₂ h₂₁) (e : h₁₂ ≫ v₁₃ = v₁₂ ≫ h₂₂) :
    IsPushout (h₁₁ ≫ h₁₂) v₁₁ v₁₃ (h₂₁ ≫ h₂₂) ↔ IsPushout h₁₂ v₁₂ v₁₃ h₂₂ :=
  ⟨fun h => h.of_left e s, s.paste_horiz⟩

/--
theorem `of_top'` / 定理 `of_top'`

English:
theorem of_top'
  statement: {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂}
  proof: of_top ((t.inl_desc _ _ _).symm ▸ s) (t.inr_desc _ _ _) t

中文:
定理 of_top'
  结论: {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂}
  证明: of_top ((t.inl_desc _ _ _).symm ▸ s) (t.inr_desc _ _ _) t

Depends on / 依赖: inl_desc, inr_desc, of_top, t.inl_desc, t.inr_desc
-/
theorem of_top' {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂}
    {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₂ ⟶ X₃₂} {v₂₁ : X₂₁ ⟶ X₃₁}
    (s : IsPushout h₁₁ (v₁₁ ≫ v₂₁) v₁₃ h₃₁) (t : IsPushout h₁₁ v₁₁ v₁₂ h₂₁) :
      IsPushout h₂₁ v₂₁ (t.desc v₁₃ (v₂₁ ≫ h₃₁) (by rw [s.w, Category.assoc])) h₃₁ :=
  of_top ((t.inl_desc _ _ _).symm ▸ s) (t.inr_desc _ _ _) t

/--
theorem `of_left'` / 定理 `of_left'`

English:
theorem of_left'
  statement: {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂}
  proof: of_left ((t.inr_desc _ _ _).symm ▸ s) (by simp only [inl_desc]) t

中文:
定理 of_left'
  结论: {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂}
  证明: of_left ((t.inr_desc _ _ _).symm ▸ s) (by simp only [inl_desc]) t

Depends on / 依赖: inl_desc, inr_desc, of_left, t.inr_desc
-/
theorem of_left' {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂}
    {h₂₃ : X₂₁ ⟶ X₂₃} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₃ ⟶ X₂₃}
    (s : IsPushout (h₁₁ ≫ h₁₂) v₁₁ v₁₃ h₂₃) (t : IsPushout h₁₁ v₁₁ v₁₂ h₂₁) :
    IsPushout h₁₂ v₁₂ v₁₃ (t.desc (h₁₂ ≫ v₁₃) h₂₃ (by rw [← Category.assoc, s.w])) :=
  of_left ((t.inr_desc _ _ _).symm ▸ s) (by simp only [inl_desc]) t

/--
theorem `of_horiz_isIso_epi` / 定理 `of_horiz_isIso_epi`

English:
theorem of_horiz_isIso_epi
  given: [Epi f] [IsIso inr] (sq : CommSq f g inl inr)
  statement: IsPushout f g inl inr
  proof: of_isColimit' sq
    (by
      refine
        PushoutCocone.IsColimit.mk _ (fun s => inv inr ≫ s.inr) (fun s => ?_)
          (by simp) (by simp)
      simp only [← cancel_epi f, s.condition, sq.w_assoc, IsIso.hom_inv_id_assoc])

中文:
定理 of_horiz_isIso_epi
  条件: [满态射 f] [是同构 inr] (sq : 交换Sq f g inl inr)
  结论: 是推出 f g inl inr
  证明: of_isColimit' sq
    (by
      refine
        PushoutCocone.IsColimit.mk _ (fun s => inv inr ≫ s.inr) (fun s => ?_)
          (by simp) (by simp)
      simp only [← cancel_epi f, s.condition, sq.w_assoc, IsIso.hom_inv_id_assoc])

Depends on / 依赖: IsColimit, IsIso.hom_inv_id_assoc, PushoutCocone, PushoutCocone.IsColimit.mk, cancel_epi, condition, hom_inv_id_assoc, of_isColimit, s.condition, s.inr, sq.w_assoc, w_assoc
-/
theorem of_horiz_isIso_epi [Epi f] [IsIso inr] (sq : CommSq f g inl inr) : IsPushout f g inl inr :=
  of_isColimit' sq
    (by
      refine
        PushoutCocone.IsColimit.mk _ (fun s => inv inr ≫ s.inr) (fun s => ?_)
          (by simp) (by simp)
      simp only [← cancel_epi f, s.condition, sq.w_assoc, IsIso.hom_inv_id_assoc])

/--
theorem `of_horiz_isIso` / 定理 `of_horiz_isIso`

English:
theorem of_horiz_isIso
  given: [IsIso f] [IsIso inr] (sq : CommSq f g inl inr)
  statement: IsPushout f g inl inr
  proof: of_horiz_isIso_epi sq

中文:
定理 of_horiz_isIso
  条件: [是同构 f] [是同构 inr] (sq : 交换Sq f g inl inr)
  结论: 是推出 f g inl inr
  证明: of_horiz_isIso_epi sq

Depends on / 依赖: of_horiz_isIso_epi
-/
theorem of_horiz_isIso [IsIso f] [IsIso inr] (sq : CommSq f g inl inr) : IsPushout f g inl inr :=
  of_horiz_isIso_epi sq

/--
theorem `of_vert_isIso_epi` / 定理 `of_vert_isIso_epi`

English:
theorem of_vert_isIso_epi
  given: [Epi g] [IsIso inl] (sq : CommSq f g inl inr)
  statement: IsPushout f g inl inr
  proof: (of_horiz_isIso_epi sq.flip).flip

中文:
定理 of_vert_isIso_epi
  条件: [满态射 g] [是同构 inl] (sq : 交换Sq f g inl inr)
  结论: 是推出 f g inl inr
  证明: (of_horiz_isIso_epi sq.flip).flip

Depends on / 依赖: of_horiz_isIso_epi, sq.flip
-/
theorem of_vert_isIso_epi [Epi g] [IsIso inl] (sq : CommSq f g inl inr) : IsPushout f g inl inr :=
  (of_horiz_isIso_epi sq.flip).flip

/--
theorem `of_vert_isIso` / 定理 `of_vert_isIso`

English:
theorem of_vert_isIso
  given: [IsIso g] [IsIso inl] (sq : CommSq f g inl inr)
  statement: IsPushout f g inl inr
  proof: of_vert_isIso_epi sq

中文:
定理 of_vert_isIso
  条件: [是同构 g] [是同构 inl] (sq : 交换Sq f g inl inr)
  结论: 是推出 f g inl inr
  证明: of_vert_isIso_epi sq

Depends on / 依赖: of_vert_isIso_epi
-/
theorem of_vert_isIso [IsIso g] [IsIso inl] (sq : CommSq f g inl inr) : IsPushout f g inl inr :=
  of_vert_isIso_epi sq

/--
lemma `of_id_fst` / 引理 `of_id_fst`

English:
lemma of_id_fst
  statement: IsPushout (𝟙 _) f f (𝟙 _)
  proof: IsPushout.of_horiz_isIso ⟨by simp⟩

中文:
引理 of_id_fst
  结论: 是推出 (𝟙 _) f f (𝟙 _)
  证明: IsPushout.of_horiz_isIso ⟨by simp⟩

Depends on / 依赖: IsPushout, IsPushout.of_horiz_isIso, of_horiz_isIso
-/
lemma of_id_fst : IsPushout (𝟙 _) f f (𝟙 _) := IsPushout.of_horiz_isIso ⟨by simp⟩

/--
lemma `of_id_snd` / 引理 `of_id_snd`

English:
lemma of_id_snd
  statement: IsPushout f (𝟙 _) (𝟙 _) f
  proof: IsPushout.of_vert_isIso ⟨by simp⟩

中文:
引理 of_id_snd
  结论: 是推出 f (𝟙 _) (𝟙 _) f
  证明: IsPushout.of_vert_isIso ⟨by simp⟩

Depends on / 依赖: IsPushout, IsPushout.of_vert_isIso, of_vert_isIso
-/
lemma of_id_snd : IsPushout f (𝟙 _) (𝟙 _) f := IsPushout.of_vert_isIso ⟨by simp⟩

/--
lemma `id_vert` / 引理 `id_vert`

English:
lemma id_vert
  given: (f : X ⟶ Z)
  statement: IsPushout f (𝟙 X) (𝟙 Z) f
  proof: of_vert_isIso ⟨by simp only [Category.id_comp, Category.comp_id]⟩

中文:
引理 id_vert
  条件: (f : X ⟶ Z)
  结论: 是推出 f (𝟙 X) (𝟙 Z) f
  证明: of_vert_isIso ⟨by simp only [Category.id_comp, Category.comp_id]⟩

Depends on / 依赖: Category, Category.comp_id, Category.id_comp, comp_id, id_comp, of_vert_isIso
-/
lemma id_vert (f : X ⟶ Z) : IsPushout f (𝟙 X) (𝟙 Z) f :=
  of_vert_isIso ⟨by simp only [Category.id_comp, Category.comp_id]⟩

/--
lemma `id_horiz` / 引理 `id_horiz`

English:
lemma id_horiz
  given: (f : X ⟶ Z)
  statement: IsPushout (𝟙 X) f f (𝟙 Z)
  proof: of_horiz_isIso ⟨by simp only [Category.id_comp, Category.comp_id]⟩

中文:
引理 id_horiz
  条件: (f : X ⟶ Z)
  结论: 是推出 (𝟙 X) f f (𝟙 Z)
  证明: of_horiz_isIso ⟨by simp only [Category.id_comp, Category.comp_id]⟩

Depends on / 依赖: Category, Category.comp_id, Category.id_comp, comp_id, id_comp, of_horiz_isIso
-/
lemma id_horiz (f : X ⟶ Z) : IsPushout (𝟙 X) f f (𝟙 Z) :=
  of_horiz_isIso ⟨by simp only [Category.id_comp, Category.comp_id]⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `of_coprod_inl_with_id` / 引理 `of_coprod_inl_with_id`

English:
lemma of_coprod_inl_with_id
  statement: {A B : C} (f : A ⟶ B) (X : C) [HasBinaryCoproduct A X]
  proof: by simp
  isColimit' := ⟨PushoutCocone.isColimitAux' _ (fun s => by
    refine ⟨coprod.desc s.inr (coprod.inr ≫ s.inl), ?_, ?_, ?_⟩
    · ext
      · simp [PushoutCocone.condition]
      · simp
    · simp
    · intro m h₁ h₂
      dsimp at m h₁ h₂ ⊢
      ext
      · simpa using h₂
      · simp [← h

中文:
引理 of_coprod_inl_with_id
  结论: {A B : C} (f : A ⟶ B) (X : C) [HasBinaryCoproduct A X]
  证明: by simp
  isColimit' := ⟨PushoutCocone.isColimitAux' _ (fun s => by
    refine ⟨coprod.desc s.inr (coprod.inr ≫ s.inl), ?_, ?_, ?_⟩
    · ext
      · simp [PushoutCocone.condition]
      · simp
    · simp
    · intro m h₁ h₂
      dsimp at m h₁ h₂ ⊢
      ext
      · simpa using h₂
      · simp [← h

Depends on / 依赖: PushoutCocone, PushoutCocone.condition, PushoutCocone.isColimitAux, condition, coprod, coprod.desc, coprod.inr, isColimit, isColimitAux, s.inl, s.inr
-/
lemma of_coprod_inl_with_id {A B : C} (f : A ⟶ B) (X : C) [HasBinaryCoproduct A X]
    [HasBinaryCoproduct B X] :
    IsPushout coprod.inl f (coprod.map f (𝟙 X)) coprod.inl where
  w := by simp
  isColimit' := ⟨PushoutCocone.isColimitAux' _ (fun s => by
    refine ⟨coprod.desc s.inr (coprod.inr ≫ s.inl), ?_, ?_, ?_⟩
    · ext
      · simp [PushoutCocone.condition]
      · simp
    · simp
    · intro m h₁ h₂
      dsimp at m h₁ h₂ ⊢
      ext
      · simpa using h₂
      · simp [← h₁])⟩

set_option backward.isDefEq.respectTransparency false in
/--
lemma `of_isColimit_binaryCofan_of_isInitial` / 引理 `of_isColimit_binaryCofan_of_isInitial`

English:
lemma of_isColimit_binaryCofan_of_isInitial
  proof: hI.hom_ext _ _
  isColimit' := ⟨PushoutCocone.IsColimit.mk _
    (fun s => BinaryCofan.IsColimit.desc hc s.inr s.inl) (by simp) (by simp)
    (fun s m h₁ h₂ => by apply BinaryCofan.IsColimit.hom_ext hc <;> cat_disch)⟩

中文:
引理 of_isColimit_binaryCofan_of_isInitial
  证明: hI.hom_ext _ _
  isColimit' := ⟨PushoutCocone.IsColimit.mk _
    (fun s => BinaryCofan.IsColimit.desc hc s.inr s.inl) (by simp) (by simp)
    (fun s m h₁ h₂ => by apply BinaryCofan.IsColimit.hom_ext hc <;> cat_disch)⟩

Depends on / 依赖: hI.hom_ext, hom_ext
-/
lemma of_isColimit_binaryCofan_of_isInitial
    {X Y : C} {c : BinaryCofan X Y} (hc : IsColimit c)
    {I : C} (hI : IsInitial I) :
    IsPushout (hI.to _) (hI.to _) c.inr c.inl where
  w := hI.hom_ext _ _
  isColimit' := ⟨PushoutCocone.IsColimit.mk _
    (fun s => BinaryCofan.IsColimit.desc hc s.inr s.inl) (by simp) (by simp)
    (fun s m h₁ h₂ => by apply BinaryCofan.IsColimit.hom_ext hc <;> cat_disch)⟩

/--
lemma `mk'` / 引理 `mk'`

English:
lemma mk'
  statement: {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}
  proof: w
  isColimit' := by
    let l (s : PushoutCocone f g) := exists_desc _ _ s.condition
    exact ⟨PushoutCocone.IsColimit.mk _
      (fun s => (l s).choose)
      (fun s => (l s).choose_spec.1)
      (fun s => (l s).choose_spec.2)
      (fun s m h₁ h₂ => hom_ext
        (h₁.trans (l s).choose_spec.1.

中文:
引理 mk'
  结论: {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}
  证明: w
  isColimit' := by
    let l (s : PushoutCocone f g) := exists_desc _ _ s.condition
    exact ⟨PushoutCocone.IsColimit.mk _
      (fun s => (l s).choose)
      (fun s => (l s).choose_spec.1)
      (fun s => (l s).choose_spec.2)
      (fun s m h₁ h₂ => hom_ext
        (h₁.trans (l s).choose_spec.1.
-/
lemma mk' {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}
    (w : f ≫ inl = g ≫ inr)
    (hom_ext : forall ⦃T : C⦄ ⦃φ φ' : P ⟶ T⦄ (_ : inl ≫ φ = inl ≫ φ')
      (_ : inr ≫ φ = inr ≫ φ'), φ = φ')
    (exists_desc : forall ⦃T : C⦄ (a : X ⟶ T) (b : Y ⟶ T)
      (_ : f ≫ a = g ≫ b), exists (l : P ⟶ T), inl ≫ l = a ∧ inr ≫ l = b) :
    IsPushout f g inl inr where
  w := w
  isColimit' := by
    let l (s : PushoutCocone f g) := exists_desc _ _ s.condition
    exact ⟨PushoutCocone.IsColimit.mk _
      (fun s => (l s).choose)
      (fun s => (l s).choose_spec.1)
      (fun s => (l s).choose_spec.2)
      (fun s m h₁ h₂ => hom_ext
        (h₁.trans (l s).choose_spec.1.symm)
        (h₂.trans (l s).choose_spec.2.symm))⟩

end IsPushout

section Equalizer

variable {X Y Z : C} {f f' : X ⟶ Y} {g g' : Y ⟶ Z}

/--
Definition of `IsPullback.isLimitFork` / `IsPullback.isLimitFork` 的定义

English:
definition IsPullback.isLimitFork
  signature: (H : IsPullback f f g g')
  body: by
  fapply Fork.IsLimit.mk
  · exact fun s => H.isLimit.lift (PullbackCone.mk s.ι s.ι s.condition)
  · exact fun s => H.isLimit.fac _ WalkingCospan.left
  · intro s m e
    apply PullbackCone.IsLimit.hom_ext H.isLimit <;> refine e.trans ?_ <;> symm <;>
      exact H.isLimit.fac _ _

中文:
定义 是拉回.isLimitFork
  签名: (H : 是拉回 f f g g')
  定义体: by
  fapply Fork.IsLimit.mk
  · exact fun s => H.isLimit.lift (PullbackCone.mk s.ι s.ι s.condition)
  · exact fun s => H.isLimit.fac _ WalkingCospan.left
  · intro s m e
    apply PullbackCone.IsLimit.hom_ext H.isLimit <;> refine e.trans ?_ <;> symm <;>
      exact H.isLimit.fac _ _

Depends on / 依赖: Fork.IsLimit.mk, H.isLimit, H.isLimit.fac, H.isLimit.lift, IsLimit, PullbackCone, PullbackCone.IsLimit.hom_ext, PullbackCone.mk, WalkingCospan, WalkingCospan.left, condition, e.trans, fapply, hom_ext, isLimit, s.condition
-/
noncomputable def IsPullback.isLimitFork (H : IsPullback f f g g') : IsLimit (Fork.ofι f H.w) := by
  fapply Fork.IsLimit.mk
  · exact fun s => H.isLimit.lift (PullbackCone.mk s.ι s.ι s.condition)
  · exact fun s => H.isLimit.fac _ WalkingCospan.left
  · intro s m e
    apply PullbackCone.IsLimit.hom_ext H.isLimit <;> refine e.trans ?_ <;> symm <;>
      exact H.isLimit.fac _ _

/--
Definition of `IsPushout.isLimitFork` / `IsPushout.isLimitFork` 的定义

English:
definition IsPushout.isLimitFork
  signature: (H : IsPushout f f' g g)
  body: by
  fapply Cofork.IsColimit.mk
  · exact fun s => H.isColimit.desc (PushoutCocone.mk s.π s.π s.condition)
  · exact fun s => H.isColimit.fac _ WalkingSpan.left
  · intro s m e
    apply PushoutCocone.IsColimit.hom_ext H.isColimit <;> refine e.trans ?_ <;> symm <;>
      exact H.isColimit.fac _ _

中文:
定义 是推出.isLimitFork
  签名: (H : 是推出 f f' g g)
  定义体: by
  fapply Cofork.IsColimit.mk
  · exact fun s => H.isColimit.desc (PushoutCocone.mk s.π s.π s.condition)
  · exact fun s => H.isColimit.fac _ WalkingSpan.left
  · intro s m e
    apply PushoutCocone.IsColimit.hom_ext H.isColimit <;> refine e.trans ?_ <;> symm <;>
      exact H.isColimit.fac _ _

Depends on / 依赖: Cofork, Cofork.IsColimit.mk, H.isColimit, H.isColimit.desc, H.isColimit.fac, IsColimit, PushoutCocone, PushoutCocone.IsColimit.hom_ext, PushoutCocone.mk, WalkingSpan, WalkingSpan.left, condition, e.trans, fapply, hom_ext, isColimit, s.condition
-/
noncomputable def IsPushout.isLimitFork (H : IsPushout f f' g g) :
    IsColimit (Cofork.ofπ g H.w) := by
  fapply Cofork.IsColimit.mk
  · exact fun s => H.isColimit.desc (PushoutCocone.mk s.π s.π s.condition)
  · exact fun s => H.isColimit.fac _ WalkingSpan.left
  · intro s m e
    apply PushoutCocone.IsColimit.hom_ext H.isColimit <;> refine e.trans ?_ <;> symm <;>
      exact H.isColimit.fac _ _

end Equalizer

section Functor

variable {D : Type u₂} [Category.{v₂} D]
variable (F : C ⥤ D) {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Functor.map_isPullback` / 定理 `Functor.map_isPullback`

English:
theorem Functor.map_isPullback
  given: [PreservesLimit (cospan h i) F] (s : IsPullback f g h i)
  proof: by
  refine
    IsPullback.of_isLimit' (F.map_commSq s.toCommSq)
      (IsLimit.equivOfNatIsoOfIso (cospanCompIso F h i) _ _ (WalkingCospan.ext ?_ ?_ ?_)
        (isLimitOfPreserves F s.isLimit))
  · rfl
  · simp
  · simp

中文:
定理 函子.map_isPullback
  条件: [保持极限 (cospan h i) F] (s : 是拉回 f g h i)
  证明: by
  refine
    IsPullback.of_isLimit' (F.map_commSq s.toCommSq)
      (IsLimit.equivOfNatIsoOfIso (cospanCompIso F h i) _ _ (WalkingCospan.ext ?_ ?_ ?_)
        (isLimitOfPreserves F s.isLimit))
  · rfl
  · simp
  · simp

Depends on / 依赖: F.map_commSq, IsLimit, IsLimit.equivOfNatIsoOfIso, IsPullback, IsPullback.of_isLimit, WalkingCospan, WalkingCospan.ext, cospanCompIso, equivOfNatIsoOfIso, isLimit, isLimitOfPreserves, map_commSq, of_isLimit, s.isLimit, s.toCommSq, toCommSq
-/
theorem Functor.map_isPullback [PreservesLimit (cospan h i) F] (s : IsPullback f g h i) :
    IsPullback (F.map f) (F.map g) (F.map h) (F.map i) := by
  refine
    IsPullback.of_isLimit' (F.map_commSq s.toCommSq)
      (IsLimit.equivOfNatIsoOfIso (cospanCompIso F h i) _ _ (WalkingCospan.ext ?_ ?_ ?_)
        (isLimitOfPreserves F s.isLimit))
  · rfl
  · simp
  · simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `Functor.map_isPushout` / 定理 `Functor.map_isPushout`

English:
theorem Functor.map_isPushout
  given: [PreservesColimit (span f g) F] (s : IsPushout f g h i)
  proof: by
  refine
    IsPushout.of_isColimit' (F.map_commSq s.toCommSq)
      (IsColimit.equivOfNatIsoOfIso (spanCompIso F f g) _ _ (WalkingSpan.ext ?_ ?_ ?_)
        (isColimitOfPreserves F s.isColimit))
  · rfl
  · simp
  · simp

alias IsPullback.map := Functor.map_isPullback

alias IsPushout.map := Fun

中文:
定理 函子.map_isPushout
  条件: [保持余极限 (span f g) F] (s : 是推出 f g h i)
  证明: by
  refine
    IsPushout.of_isColimit' (F.map_commSq s.toCommSq)
      (IsColimit.equivOfNatIsoOfIso (spanCompIso F f g) _ _ (WalkingSpan.ext ?_ ?_ ?_)
        (isColimitOfPreserves F s.isColimit))
  · rfl
  · simp
  · simp

alias IsPullback.map := Functor.map_isPullback

alias IsPushout.map := Fun

Depends on / 依赖: F.map_commSq, IsColimit, IsColimit.equivOfNatIsoOfIso, IsPushout, IsPushout.of_isColimit, WalkingSpan, WalkingSpan.ext, equivOfNatIsoOfIso, isColimit, isColimitOfPreserves, map_commSq, of_isColimit, s.isColimit, s.toCommSq, spanCompIso, toCommSq
-/
theorem Functor.map_isPushout [PreservesColimit (span f g) F] (s : IsPushout f g h i) :
    IsPushout (F.map f) (F.map g) (F.map h) (F.map i) := by
  refine
    IsPushout.of_isColimit' (F.map_commSq s.toCommSq)
      (IsColimit.equivOfNatIsoOfIso (spanCompIso F f g) _ _ (WalkingSpan.ext ?_ ?_ ?_)
        (isColimitOfPreserves F s.isColimit))
  · rfl
  · simp
  · simp

alias IsPullback.map := Functor.map_isPullback

alias IsPushout.map := Functor.map_isPushout

/--
theorem `IsPullback.of_map` / 定理 `IsPullback.of_map`

English:
theorem IsPullback.of_map
  statement: [ReflectsLimit (cospan h i) F] (e : f ≫ h = g ≫ i)
  proof: by
refine ⟨⟨e⟩, ⟨isLimitOfReflects F ?_⟩⟩
  refine
    (IsLimit.equivOfNatIsoOfIso (cospanCompIso F h i) _ _ (WalkingCospan.ext ?_ ?_ ?_)).symm
      H.isLimit
  exacts [Iso.refl _, (Category.comp_id _).trans (Category.id_comp _).symm,
    (Category.comp_id _).trans (Category.id_comp _).symm]

中文:
定理 是拉回.of_map
  结论: [反映极限 (cospan h i) F] (e : f ≫ h = g ≫ i)
  证明: by
refine ⟨⟨e⟩, ⟨isLimitOfReflects F ?_⟩⟩
  refine
    (IsLimit.equivOfNatIsoOfIso (cospanCompIso F h i) _ _ (WalkingCospan.ext ?_ ?_ ?_)).symm
      H.isLimit
  exacts [Iso.refl _, (Category.comp_id _).trans (Category.id_comp _).symm,
    (Category.comp_id _).trans (Category.id_comp _).symm]
-/
theorem IsPullback.of_map [ReflectsLimit (cospan h i) F] (e : f ≫ h = g ≫ i)
    (H : IsPullback (F.map f) (F.map g) (F.map h) (F.map i)) : IsPullback f g h i := by
refine ⟨⟨e⟩, ⟨isLimitOfReflects F ?_⟩⟩
  refine
    (IsLimit.equivOfNatIsoOfIso (cospanCompIso F h i) _ _ (WalkingCospan.ext ?_ ?_ ?_)).symm
      H.isLimit
  exacts [Iso.refl _, (Category.comp_id _).trans (Category.id_comp _).symm,
    (Category.comp_id _).trans (Category.id_comp _).symm]

/--
theorem `IsPullback.of_map_of_faithful` / 定理 `IsPullback.of_map_of_faithful`

English:
theorem IsPullback.of_map_of_faithful
  statement: [ReflectsLimit (cospan h i) F] [F.Faithful]
  proof: H.of_map F (F.map_injective <| by simpa only [F.map_comp] using H.w)

中文:
定理 是拉回.of_map_of_faithful
  结论: [反映极限 (cospan h i) F] [F.忠实]
  证明: H.of_map F (F.map_injective <| by simpa only [F.map_comp] using H.w)

Depends on / 依赖: F.map_comp, F.map_injective, H.of_map, map_comp, map_injective, of_map
-/
theorem IsPullback.of_map_of_faithful [ReflectsLimit (cospan h i) F] [F.Faithful]
    (H : IsPullback (F.map f) (F.map g) (F.map h) (F.map i)) : IsPullback f g h i :=
  H.of_map F (F.map_injective <| by simpa only [F.map_comp] using H.w)

/--
theorem `IsPullback.map_iff` / 定理 `IsPullback.map_iff`

English:
theorem IsPullback.map_iff
  statement: {D : Type*} [Category* D] (F : C ⥤ D) [PreservesLimit (cospan h i) F]
  proof: ⟨fun h => h.of_map F e, fun h => h.map F⟩

中文:
定理 是拉回.map_iff
  结论: {D : 类型} [范畴* D] (F : C ⥤ D) [保持极限 (cospan h i) F]
  证明: ⟨fun h => h.of_map F e, fun h => h.map F⟩
-/
theorem IsPullback.map_iff {D : Type*} [Category* D] (F : C ⥤ D) [PreservesLimit (cospan h i) F]
    [ReflectsLimit (cospan h i) F] (e : f ≫ h = g ≫ i) :
    IsPullback (F.map f) (F.map g) (F.map h) (F.map i) ↔ IsPullback f g h i :=
  ⟨fun h => h.of_map F e, fun h => h.map F⟩

/--
theorem `IsPushout.of_map` / 定理 `IsPushout.of_map`

English:
theorem IsPushout.of_map
  statement: [ReflectsColimit (span f g) F] (e : f ≫ h = g ≫ i)
  proof: by
refine ⟨⟨e⟩, ⟨isColimitOfReflects F ?_⟩⟩
  refine
    (IsColimit.equivOfNatIsoOfIso (spanCompIso F f g) _ _ (WalkingSpan.ext ?_ ?_ ?_)).symm
      H.isColimit
  exacts [Iso.refl _, (Category.comp_id _).trans (Category.id_comp _),
    (Category.comp_id _).trans (Category.id_comp _)]

中文:
定理 是推出.of_map
  结论: [反映余极限 (span f g) F] (e : f ≫ h = g ≫ i)
  证明: by
refine ⟨⟨e⟩, ⟨isColimitOfReflects F ?_⟩⟩
  refine
    (IsColimit.equivOfNatIsoOfIso (spanCompIso F f g) _ _ (WalkingSpan.ext ?_ ?_ ?_)).symm
      H.isColimit
  exacts [Iso.refl _, (Category.comp_id _).trans (Category.id_comp _),
    (Category.comp_id _).trans (Category.id_comp _)]
-/
theorem IsPushout.of_map [ReflectsColimit (span f g) F] (e : f ≫ h = g ≫ i)
    (H : IsPushout (F.map f) (F.map g) (F.map h) (F.map i)) : IsPushout f g h i := by
refine ⟨⟨e⟩, ⟨isColimitOfReflects F ?_⟩⟩
  refine
    (IsColimit.equivOfNatIsoOfIso (spanCompIso F f g) _ _ (WalkingSpan.ext ?_ ?_ ?_)).symm
      H.isColimit
  exacts [Iso.refl _, (Category.comp_id _).trans (Category.id_comp _),
    (Category.comp_id _).trans (Category.id_comp _)]

/--
theorem `IsPushout.of_map_of_faithful` / 定理 `IsPushout.of_map_of_faithful`

English:
theorem IsPushout.of_map_of_faithful
  statement: [ReflectsColimit (span f g) F] [F.Faithful]
  proof: H.of_map F (F.map_injective <| by simpa only [F.map_comp] using H.w)

中文:
定理 是推出.of_map_of_faithful
  结论: [反映余极限 (span f g) F] [F.忠实]
  证明: H.of_map F (F.map_injective <| by simpa only [F.map_comp] using H.w)

Depends on / 依赖: F.map_comp, F.map_injective, H.of_map, map_comp, map_injective, of_map
-/
theorem IsPushout.of_map_of_faithful [ReflectsColimit (span f g) F] [F.Faithful]
    (H : IsPushout (F.map f) (F.map g) (F.map h) (F.map i)) : IsPushout f g h i :=
  H.of_map F (F.map_injective <| by simpa only [F.map_comp] using H.w)

/--
theorem `IsPushout.map_iff` / 定理 `IsPushout.map_iff`

English:
theorem IsPushout.map_iff
  statement: {D : Type*} [Category* D] (F : C ⥤ D) [PreservesColimit (span f g) F]
  proof: ⟨fun h => h.of_map F e, fun h => h.map F⟩

中文:
定理 是推出.map_iff
  结论: {D : 类型} [范畴* D] (F : C ⥤ D) [保持余极限 (span f g) F]
  证明: ⟨fun h => h.of_map F e, fun h => h.map F⟩
-/
theorem IsPushout.map_iff {D : Type*} [Category* D] (F : C ⥤ D) [PreservesColimit (span f g) F]
    [ReflectsColimit (span f g) F] (e : f ≫ h = g ≫ i) :
    IsPushout (F.map f) (F.map g) (F.map h) (F.map i) ↔ IsPushout f g h i :=
  ⟨fun h => h.of_map F e, fun h => h.map F⟩

variable {F} in
/--
lemma `IsPullback.preservesLimit_cospan_iff` / 引理 `IsPullback.preservesLimit_cospan_iff`

English:
lemma IsPullback.preservesLimit_cospan_iff
  statement: {P X Y Z : C} {fst : P ⟶ X}
  proof: by
  refine ⟨fun _ => h.map _, fun hF => ?_⟩
  apply preservesLimit_of_preserves_limit_cone h.isLimit
  exact (PullbackCone.isLimitMapConeEquiv _ _).symm hF.isLimit

中文:
引理 是拉回.preservesLimit_cospan_iff
  结论: {P X Y Z : C} {fst : P ⟶ X}
  证明: by
  refine ⟨fun _ => h.map _, fun hF => ?_⟩
  apply preservesLimit_of_preserves_limit_cone h.isLimit
  exact (PullbackCone.isLimitMapConeEquiv _ _).symm hF.isLimit

Depends on / 依赖: PullbackCone, PullbackCone.isLimitMapConeEquiv, h.isLimit, h.map, hF.isLimit, isLimit, isLimitMapConeEquiv, preservesLimit_of_preserves_limit_cone
-/
lemma IsPullback.preservesLimit_cospan_iff {P X Y Z : C} {fst : P ⟶ X}
    {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) :
    PreservesLimit (cospan f g) F ↔ IsPullback (F.map fst) (F.map snd) (F.map f) (F.map g) := by
  refine ⟨fun _ => h.map _, fun hF => ?_⟩
  apply preservesLimit_of_preserves_limit_cone h.isLimit
  exact (PullbackCone.isLimitMapConeEquiv _ _).symm hF.isLimit

variable {F} in
/--
lemma `IsPushout.preservesColimit_span_iff` / 引理 `IsPushout.preservesColimit_span_iff`

English:
lemma IsPushout.preservesColimit_span_iff
  statement: {P X Y Z : C} {inl : X ⟶ P}
  proof: by
  refine ⟨fun _ => h.map _, fun hF => ?_⟩
  apply preservesColimit_of_preserves_colimit_cocone h.isColimit
  exact (PushoutCocone.isColimitMapCoconeEquiv _ _).symm hF.isColimit

中文:
引理 是推出.preservesColimit_span_iff
  结论: {P X Y Z : C} {inl : X ⟶ P}
  证明: by
  refine ⟨fun _ => h.map _, fun hF => ?_⟩
  apply preservesColimit_of_preserves_colimit_cocone h.isColimit
  exact (PushoutCocone.isColimitMapCoconeEquiv _ _).symm hF.isColimit

Depends on / 依赖: PushoutCocone, PushoutCocone.isColimitMapCoconeEquiv, h.isColimit, h.map, hF.isColimit, isColimit, isColimitMapCoconeEquiv, preservesColimit_of_preserves_colimit_cocone
-/
lemma IsPushout.preservesColimit_span_iff {P X Y Z : C} {inl : X ⟶ P}
    {inr : Y ⟶ P} {f : Z ⟶ X} {g : Z ⟶ Y} (h : IsPushout f g inl inr) :
    PreservesColimit (span f g) F ↔ IsPushout (F.map f) (F.map g) (F.map inl) (F.map inr) := by
  refine ⟨fun _ => h.map _, fun hF => ?_⟩
  apply preservesColimit_of_preserves_colimit_cocone h.isColimit
  exact (PushoutCocone.isColimitMapCoconeEquiv _ _).symm hF.isColimit

variable {F} in
/--
lemma `Limits.preservesLimitsOfShape_walkingCospan_of_forall_isPullback` / 引理 `Limits.preservesLimitsOfShape_walkingCospan_of_forall_isPullback`

English:
lemma Limits.preservesLimitsOfShape_walkingCospan_of_forall_isPullback
  proof: by
  suffices h : forall {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z), PreservesLimit (cospan f g) F from
    ⟨fun {K} => preservesLimit_of_iso_diagram _ (Limits.diagramIsoCospan K).symm⟩
  intro X Y Z f g
  refine .mk' fun h => ?_
  obtain ⟨P, fst, snd, h, h'⟩ := H f g
  rwa [h.preservesLimit_cospan_iff]

中文:
引理 Limits.preservesLimitsOfShape_walkingCospan_of_对任意_isPullback
  证明: by
  suffices h : forall {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z), PreservesLimit (cospan f g) F from
    ⟨fun {K} => preservesLimit_of_iso_diagram _ (Limits.diagramIsoCospan K).symm⟩
  intro X Y Z f g
  refine .mk' fun h => ?_
  obtain ⟨P, fst, snd, h, h'⟩ := H f g
  rwa [h.preservesLimit_cospan_iff]

Depends on / 依赖: Limits, Limits.diagramIsoCospan, PreservesLimit, cospan, diagramIsoCospan, h.preservesLimit_cospan_iff, preservesLimit_cospan_iff, preservesLimit_of_iso_diagram
-/
lemma Limits.preservesLimitsOfShape_walkingCospan_of_forall_isPullback
    (H : forall ⦃X Y Z : C⦄ (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g],
      exists (P : C) (fst : P ⟶ X) (snd : P ⟶ Y),
        IsPullback fst snd f g ∧ IsPullback (F.map fst) (F.map snd) (F.map f) (F.map g)) :
    PreservesLimitsOfShape WalkingCospan F := by
  suffices h : forall {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z), PreservesLimit (cospan f g) F from
    ⟨fun {K} => preservesLimit_of_iso_diagram _ (Limits.diagramIsoCospan K).symm⟩
  intro X Y Z f g
  refine .mk' fun h => ?_
  obtain ⟨P, fst, snd, h, h'⟩ := H f g
  rwa [h.preservesLimit_cospan_iff]

variable {F} in
/--
lemma `Limits.preservesColimitsOfShape_walkingCospan_of_forall_isPushout` / 引理 `Limits.preservesColimitsOfShape_walkingCospan_of_forall_isPushout`

English:
lemma Limits.preservesColimitsOfShape_walkingCospan_of_forall_isPushout
  proof: by
  suffices h : forall {X Y Z : C} (f : Z ⟶ X) (g : Z ⟶ Y), PreservesColimit (span f g) F from
    ⟨fun {K} => preservesColimit_of_iso_diagram _ (diagramIsoSpan K).symm⟩
  intro X Y Z f g
  refine .mk' fun h => ?_
  obtain ⟨P, fst, snd, h, h'⟩ := H f g
  rwa [h.preservesColimit_span_iff]

中文:
引理 Limits.preservesColimitsOfShape_walkingCospan_of_对任意_isPushout
  证明: by
  suffices h : forall {X Y Z : C} (f : Z ⟶ X) (g : Z ⟶ Y), PreservesColimit (span f g) F from
    ⟨fun {K} => preservesColimit_of_iso_diagram _ (diagramIsoSpan K).symm⟩
  intro X Y Z f g
  refine .mk' fun h => ?_
  obtain ⟨P, fst, snd, h, h'⟩ := H f g
  rwa [h.preservesColimit_span_iff]

Depends on / 依赖: PreservesColimit, diagramIsoSpan, h.preservesColimit_span_iff, preservesColimit_of_iso_diagram, preservesColimit_span_iff
-/
lemma Limits.preservesColimitsOfShape_walkingCospan_of_forall_isPushout
    (H : forall ⦃X Y Z : C⦄ (f : Z ⟶ X) (g : Z ⟶ Y) [HasPushout f g],
      exists (P : C) (inl : X ⟶ P) (inr : Y ⟶ P),
        IsPushout f g inl inr ∧ IsPushout (F.map f) (F.map g) (F.map inl) (F.map inr)) :
    PreservesColimitsOfShape WalkingSpan F := by
  suffices h : forall {X Y Z : C} (f : Z ⟶ X) (g : Z ⟶ Y), PreservesColimit (span f g) F from
    ⟨fun {K} => preservesColimit_of_iso_diagram _ (diagramIsoSpan K).symm⟩
  intro X Y Z f g
  refine .mk' fun h => ?_
  obtain ⟨P, fst, snd, h, h'⟩ := H f g
  rwa [h.preservesColimit_span_iff]

/--
lemma `IsPullback.app` / 引理 `IsPullback.app`

English:
lemma IsPullback.app
  statement: [HasPullbacks D] {F₁ F₂ F₃ F₄ : C ⥤ D}
  proof: h.map ((evaluation _ _).obj X)

中文:
引理 是拉回.app
  结论: [有Pullbacks D] {F₁ F₂ F₃ F₄ : C ⥤ D}
  证明: h.map ((evaluation _ _).obj X)

Depends on / 依赖: evaluation, h.map
-/
lemma IsPullback.app [HasPullbacks D] {F₁ F₂ F₃ F₄ : C ⥤ D}
    {f₁ : F₁ ⟶ F₂} {f₂ : F₁ ⟶ F₃} {f₃ : F₂ ⟶ F₄} {f₄ : F₃ ⟶ F₄} (h : IsPullback f₁ f₂ f₃ f₄)
    (X : C) : IsPullback (f₁.app X) (f₂.app X) (f₃.app X) (f₄.app X) :=
  h.map ((evaluation _ _).obj X)

/--
lemma `IsPullback.of_forall_isPullback_app` / 引理 `IsPullback.of_forall_isPullback_app`

English:
lemma IsPullback.of_forall_isPullback_app
  statement: {F₁ F₂ F₃ F₄ : C ⥤ D}
  proof: by
    ext X
    simpa using (h X).w
  isLimit' := ⟨evaluationJointlyReflectsLimits _ fun X =>
    (PullbackCone.isLimitMapConeEquiv _ _).symm (h X).isLimit⟩

中文:
引理 是拉回.of_对任意_isPullback_app
  结论: {F₁ F₂ F₃ F₄ : C ⥤ D}
  证明: by
    ext X
    simpa using (h X).w
  isLimit' := ⟨evaluationJointlyReflectsLimits _ fun X =>
    (PullbackCone.isLimitMapConeEquiv _ _).symm (h X).isLimit⟩

Depends on / 依赖: A.hom, A.prop, HasPullbacksAlong, HasPullbacksAlong.hasPullback, PullbackCone, PullbackCone.isLimitMapConeEquiv, evaluationJointlyReflectsLimits, hasPullback, isLimit, isLimitMapConeEquiv
-/
lemma IsPullback.of_forall_isPullback_app {F₁ F₂ F₃ F₄ : C ⥤ D}
    {f₁ : F₁ ⟶ F₂} {f₂ : F₁ ⟶ F₃} {f₃ : F₂ ⟶ F₄} {f₄ : F₃ ⟶ F₄}
    (h : forall (X : C), IsPullback (f₁.app X) (f₂.app X) (f₃.app X) (f₄.app X)) :
    IsPullback f₁ f₂ f₃ f₄ where
  w := by
    ext X
    simpa using (h X).w
  isLimit' := ⟨evaluationJointlyReflectsLimits _ fun X =>
    (PullbackCone.isLimitMapConeEquiv _ _).symm (h X).isLimit⟩

/--
lemma `IsPullback.iff_app` / 引理 `IsPullback.iff_app`

English:
lemma IsPullback.iff_app
  statement: [HasPullbacks D] {F₁ F₂ F₃ F₄ : C ⥤ D}
  proof: ⟨.app, .of_forall_isPullback_app⟩

中文:
引理 是拉回.iff_app
  结论: [有Pullbacks D] {F₁ F₂ F₃ F₄ : C ⥤ D}
  证明: ⟨.app, .of_forall_isPullback_app⟩

Depends on / 依赖: A.hom, A.prop, HasPullbacksAlong, HasPullbacksAlong.hasPullback, IsPullback, IsPullback.of_hasPullback, IsStableUnderBaseChangeAlong, IsStableUnderBaseChangeAlong.of_isPullback, hasPullback, of_forall_isPullback_app, of_hasPullback, of_isPullback, pullback, pullback.snd
-/
lemma IsPullback.iff_app [HasPullbacks D] {F₁ F₂ F₃ F₄ : C ⥤ D}
    {f₁ : F₁ ⟶ F₂} {f₂ : F₁ ⟶ F₃} {f₃ : F₂ ⟶ F₄} {f₄ : F₃ ⟶ F₄} :
    IsPullback f₁ f₂ f₃ f₄ ↔ forall (X : C), IsPullback (f₁.app X) (f₂.app X) (f₃.app X) (f₄.app X) :=
  ⟨.app, .of_forall_isPullback_app⟩

/--
lemma `IsPushout.app` / 引理 `IsPushout.app`

English:
lemma IsPushout.app
  statement: [HasPushouts D] {F₁ F₂ F₃ F₄ : C ⥤ D}
  proof: h.map ((evaluation _ _).obj X)

中文:
引理 是推出.app
  结论: [有Pushouts D] {F₁ F₂ F₃ F₄ : C ⥤ D}
  证明: h.map ((evaluation _ _).obj X)

Depends on / 依赖: evaluation, h.map
-/
lemma IsPushout.app [HasPushouts D] {F₁ F₂ F₃ F₄ : C ⥤ D}
    {f₁ : F₁ ⟶ F₂} {f₂ : F₁ ⟶ F₃} {f₃ : F₂ ⟶ F₄} {f₄ : F₃ ⟶ F₄} (h : IsPushout f₁ f₂ f₃ f₄)
    (X : C) : IsPushout (f₁.app X) (f₂.app X) (f₃.app X) (f₄.app X) :=
  h.map ((evaluation _ _).obj X)

/--
lemma `IsPushout.of_forall_isPushout_app` / 引理 `IsPushout.of_forall_isPushout_app`

English:
lemma IsPushout.of_forall_isPushout_app
  statement: {F₁ F₂ F₃ F₄ : C ⥤ D}
  proof: by
    ext X
    simpa using (h X).w
  isColimit' := ⟨evaluationJointlyReflectsColimits _ fun X =>
    (PushoutCocone.isColimitMapCoconeEquiv _ _).symm (h X).isColimit⟩

中文:
引理 是推出.of_对任意_isPushout_app
  结论: {F₁ F₂ F₃ F₄ : C ⥤ D}
  证明: by
    ext X
    simpa using (h X).w
  isColimit' := ⟨evaluationJointlyReflectsColimits _ fun X =>
    (PushoutCocone.isColimitMapCoconeEquiv _ _).symm (h X).isColimit⟩

Depends on / 依赖: PushoutCocone, PushoutCocone.isColimitMapCoconeEquiv, evaluationJointlyReflectsColimits, isColimit, isColimitMapCoconeEquiv
-/
lemma IsPushout.of_forall_isPushout_app {F₁ F₂ F₃ F₄ : C ⥤ D}
    {f₁ : F₁ ⟶ F₂} {f₂ : F₁ ⟶ F₃} {f₃ : F₂ ⟶ F₄} {f₄ : F₃ ⟶ F₄}
    (h : forall (X : C), IsPushout (f₁.app X) (f₂.app X) (f₃.app X) (f₄.app X)) :
    IsPushout f₁ f₂ f₃ f₄ where
  w := by
    ext X
    simpa using (h X).w
  isColimit' := ⟨evaluationJointlyReflectsColimits _ fun X =>
    (PushoutCocone.isColimitMapCoconeEquiv _ _).symm (h X).isColimit⟩

/--
lemma `IsPushout.iff_app` / 引理 `IsPushout.iff_app`

English:
lemma IsPushout.iff_app
  statement: [HasPushouts D] {F₁ F₂ F₃ F₄ : C ⥤ D}
  proof: ⟨.app, .of_forall_isPushout_app⟩

中文:
引理 是推出.iff_app
  结论: [有Pushouts D] {F₁ F₂ F₃ F₄ : C ⥤ D}
  证明: ⟨.app, .of_forall_isPushout_app⟩

Depends on / 依赖: of_forall_isPushout_app
-/
lemma IsPushout.iff_app [HasPushouts D] {F₁ F₂ F₃ F₄ : C ⥤ D}
    {f₁ : F₁ ⟶ F₂} {f₂ : F₁ ⟶ F₃} {f₃ : F₂ ⟶ F₄} {f₄ : F₃ ⟶ F₄} :
    IsPushout f₁ f₂ f₃ f₄ ↔ forall (X : C), IsPushout (f₁.app X) (f₂.app X) (f₃.app X) (f₄.app X) :=
  ⟨.app, .of_forall_isPushout_app⟩

end Functor

section Thin

variable [Quiver.IsThin C]

/--
lemma `isPullback_iff_isLimit_binaryFan_of_isThin` / 引理 `isPullback_iff_isLimit_binaryFan_of_isThin`

English:
lemma isPullback_iff_isLimit_binaryFan_of_isThin
  statement: {P X Y Z : C}
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact ⟨BinaryFan.IsLimit.mk _ (fun u v => h.lift u v (by subsingleton))
      (by subsingleton) (by subsingleton) (by subsingleton)⟩
  · exact ⟨⟨by subsingleton⟩,
      ⟨PullbackCone.IsLimit.mk _ (fun s => BinaryFan.IsLimit.lift h.some s.fst s.snd)
      (b

中文:
引理 isPullback_iff_isLimit_binaryFan_of_isThin
  结论: {P X Y Z : C}
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact ⟨BinaryFan.IsLimit.mk _ (fun u v => h.lift u v (by subsingleton))
      (by subsingleton) (by subsingleton) (by subsingleton)⟩
  · exact ⟨⟨by subsingleton⟩,
      ⟨PullbackCone.IsLimit.mk _ (fun s => BinaryFan.IsLimit.lift h.some s.fst s.snd)
      (b

Depends on / 依赖: BinaryFan, BinaryFan.IsLimit.lift, BinaryFan.IsLimit.mk, IsLimit, PullbackCone, PullbackCone.IsLimit.mk, h.lift, h.some, s.fst, s.snd, subsingleton
-/
lemma isPullback_iff_isLimit_binaryFan_of_isThin {P X Y Z : C}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} :
    IsPullback fst snd f g ↔ Nonempty (IsLimit (BinaryFan.mk fst snd)) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact ⟨BinaryFan.IsLimit.mk _ (fun u v => h.lift u v (by subsingleton))
      (by subsingleton) (by subsingleton) (by subsingleton)⟩
  · exact ⟨⟨by subsingleton⟩,
      ⟨PullbackCone.IsLimit.mk _ (fun s => BinaryFan.IsLimit.lift h.some s.fst s.snd)
      (by subsingleton) (by subsingleton) (by subsingleton)⟩⟩

/--
lemma `isPushout_iff_isColimit_binaryCofan_of_isThin` / 引理 `isPushout_iff_isColimit_binaryCofan_of_isThin`

English:
lemma isPushout_iff_isColimit_binaryCofan_of_isThin
  statement: {P X Y Z : C}
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact ⟨BinaryCofan.IsColimit.mk _ (fun u v => h.desc u v (by subsingleton))
      (by subsingleton) (by subsingleton) (by subsingleton)⟩
  · exact ⟨⟨by subsingleton⟩,
      ⟨PushoutCocone.IsColimit.mk _ (fun s => BinaryCofan.IsColimit.desc h.some s.inl s.in

中文:
引理 isPushout_iff_isColimit_binaryCofan_of_isThin
  结论: {P X Y Z : C}
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact ⟨BinaryCofan.IsColimit.mk _ (fun u v => h.desc u v (by subsingleton))
      (by subsingleton) (by subsingleton) (by subsingleton)⟩
  · exact ⟨⟨by subsingleton⟩,
      ⟨PushoutCocone.IsColimit.mk _ (fun s => BinaryCofan.IsColimit.desc h.some s.inl s.in

Depends on / 依赖: BinaryCofan, BinaryCofan.IsColimit.desc, BinaryCofan.IsColimit.mk, IsColimit, PushoutCocone, PushoutCocone.IsColimit.mk, h.desc, h.some, s.inl, s.inr, subsingleton
-/
lemma isPushout_iff_isColimit_binaryCofan_of_isThin {P X Y Z : C}
    {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P} :
    IsPushout f g inl inr ↔ Nonempty (IsColimit (BinaryCofan.mk inl inr)) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact ⟨BinaryCofan.IsColimit.mk _ (fun u v => h.desc u v (by subsingleton))
      (by subsingleton) (by subsingleton) (by subsingleton)⟩
  · exact ⟨⟨by subsingleton⟩,
      ⟨PushoutCocone.IsColimit.mk _ (fun s => BinaryCofan.IsColimit.desc h.some s.inl s.inr)
      (by subsingleton) (by subsingleton) (by subsingleton)⟩⟩

variable {D : Type*} [Category* D] [Quiver.IsThin D] (F : C ⥤ D)

instance (priority := low) [PreservesLimitsOfShape (Discrete WalkingPair) F] :
    PreservesLimitsOfShape WalkingCospan F := by
  refine preservesLimitsOfShape_walkingCospan_of_forall_isPullback fun X Y Z f g hfg => ?_
  use pullback f g, pullback.fst f g, pullback.snd f g, .of_hasPullback f g
  rw [isPullback_iff_isLimit_binaryFan_of_isThin]
  refine ⟨(BinaryFan.mk (pullback.fst f g) (pullback.snd f g)).isLimitMapConeEquiv ?_⟩
  apply isLimitOfPreserves _ (Nonempty.some ?_)
  rw [← CategoryTheory.isPullback_iff_isLimit_binaryFan_of_isThin (f := f) (g := g)]
  exact .of_hasPullback f g

instance (priority := low) [PreservesColimitsOfShape (Discrete WalkingPair) F] :
    PreservesColimitsOfShape WalkingSpan F := by
  refine preservesColimitsOfShape_walkingCospan_of_forall_isPushout fun X Y Z f g hfg => ?_
  use pushout f g, pushout.inl f g, pushout.inr f g, .of_hasPushout f g
  rw [isPushout_iff_isColimit_binaryCofan_of_isThin]
  refine ⟨(BinaryCofan.mk (pushout.inl f g) (pushout.inr f g)).isColimitMapConeEquiv ?_⟩
  apply isColimitOfPreserves _ (Nonempty.some ?_)
  rw [← CategoryTheory.isPushout_iff_isColimit_binaryCofan_of_isThin (f := f) (g := g)]
  exact .of_hasPushout f g

end Thin

section IsPullbackOverPullback

open Limits

variable {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullbacksAlong g]

namespace IsPullback

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `isoOverPullback` / `isoOverPullback` 的定义

English:
definition isoOverPullback
  signature: {P : C} {fst : P ⟶ X} {snd : P ⟶ Y}
  body: Over.isoMk (h.isoIsPullback _ _ (IsPullback.of_hasPullback f g)) (by simp)

中文:
定义 isoOverPullback
  签名: {P : C} {fst : P ⟶ X} {snd : P ⟶ Y}
  定义体: Over.isoMk (h.isoIsPullback _ _ (IsPullback.of_hasPullback f g)) (by simp)

Depends on / 依赖: IsPullback, IsPullback.of_hasPullback, Over.isoMk, h.isoIsPullback, isoIsPullback, of_hasPullback
-/
noncomputable def isoOverPullback {P : C} {fst : P ⟶ X} {snd : P ⟶ Y}
    (h : IsPullback fst snd f g) :
    Over.mk fst ≅ Over.mk (pullback.fst f g) :=
  Over.isoMk (h.isoIsPullback _ _ (IsPullback.of_hasPullback f g)) (by simp)

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `isoOverPullback_hom_left_comp_snd` / 引理 `isoOverPullback_hom_left_comp_snd`

English:
lemma isoOverPullback_hom_left_comp_snd
  statement: {P : C} {fst : P ⟶ X} {snd : P ⟶ Y}
  proof: h.isoIsPullback_hom_snd _ _ (IsPullback.of_hasPullback f g)

中文:
引理 isoOverPullback_hom_left_comp_snd
  结论: {P : C} {fst : P ⟶ X} {snd : P ⟶ Y}
  证明: h.isoIsPullback_hom_snd _ _ (IsPullback.of_hasPullback f g)

Depends on / 依赖: IsPullback, IsPullback.of_hasPullback, h.isoIsPullback_hom_snd, isoIsPullback_hom_snd, of_hasPullback
-/
lemma isoOverPullback_hom_left_comp_snd {P : C} {fst : P ⟶ X} {snd : P ⟶ Y}
    (h : IsPullback fst snd f g) :
    dsimp% h.isoOverPullback.hom.left ≫ pullback.snd f g = snd :=
  h.isoIsPullback_hom_snd _ _ (IsPullback.of_hasPullback f g)

set_option backward.defeqAttrib.useBackward true in
/--
lemma `of_over_iso` / 引理 `of_over_iso`

English:
lemma of_over_iso
  statement: {P : C} {p : P ⟶ X}
  proof: (IsPullback.of_hasPullback f g).of_iso'
    ((Over.forget X).mapIso e) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simpa using Over.w e.hom) (by simp) (by simp) (by simp)

中文:
引理 of_over_iso
  结论: {P : C} {p : P ⟶ X}
  证明: (IsPullback.of_hasPullback f g).of_iso'
    ((Over.forget X).mapIso e) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simpa using Over.w e.hom) (by simp) (by simp) (by simp)

Depends on / 依赖: IsPullback, IsPullback.of_hasPullback, Iso.refl, Over.forget, Over.w, e.hom, forget, mapIso, of_hasPullback, of_iso
-/
lemma of_over_iso {P : C} {p : P ⟶ X}
    (e : Over.mk p ≅ Over.mk (pullback.fst f g)) :
    IsPullback p (e.hom.left ≫ pullback.snd f g) f g :=
  (IsPullback.of_hasPullback f g).of_iso'
    ((Over.forget X).mapIso e) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simpa using Over.w e.hom) (by simp) (by simp) (by simp)

set_option backward.defeqAttrib.useBackward true in
/--
lemma `iff_exists_over_iso` / 引理 `iff_exists_over_iso`

English:
lemma iff_exists_over_iso
  given: {P : C} {p : P ⟶ X} {q : P ⟶ Y}
  proof: by
  constructor
  · intro h
    exact ⟨h.isoOverPullback, by simp⟩
  · rintro ⟨e, rfl⟩
    exact of_over_iso e

中文:
引理 iff_存在_over_iso
  条件: {P : C} {p : P ⟶ X} {q : P ⟶ Y}
  证明: by
  constructor
  · intro h
    exact ⟨h.isoOverPullback, by simp⟩
  · rintro ⟨e, rfl⟩
    exact of_over_iso e

Depends on / 依赖: Over.mapPullbackAdj, h.isoOverPullback, isLeftAdjoint, isoOverPullback, mapPullbackAdj, of_over_iso
-/
lemma iff_exists_over_iso {P : C} {p : P ⟶ X} {q : P ⟶ Y} :
    IsPullback p q f g ↔
    exists e : Over.mk p ≅ Over.mk (pullback.fst f g),
      q = e.hom.left ≫ pullback.snd f g := by
  constructor
  · intro h
    exact ⟨h.isoOverPullback, by simp⟩
  · rintro ⟨e, rfl⟩
    exact of_over_iso e

end IsPullback

end IsPullbackOverPullback

namespace Limits

instance {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) {X' : C} (i : X' ⟶ X) [IsIso i] [HasPullback f g] :
    HasPullback (i ≫ f) g :=
  IsPullback.paste_vert
    (IsPullback.of_vert_isIso_mono (fst := pullback.fst _ _ ≫ inv i) (snd := 𝟙 (pullback f g)) <|
      ⟨by simp⟩) (.of_hasPullback f g) |>.hasPullback

@[simp]
/--
lemma `HasPullback.comp_left_left_iff_of_isIso` / 引理 `HasPullback.comp_left_left_iff_of_isIso`

English:
lemma HasPullback.comp_left_left_iff_of_isIso
  proof: by
  refine ⟨fun h => ?_, fun _ => inferInstance⟩
  rw [← IsIso.inv_hom_id_assoc i f]
  infer_instance

中文:
引理 HasPullback.comp_left_left_iff_of_isIso
  证明: by
  refine ⟨fun h => ?_, fun _ => inferInstance⟩
  rw [← IsIso.inv_hom_id_assoc i f]
  infer_instance

Depends on / 依赖: IsIso.inv_hom_id_assoc, infer_instance, inv_hom_id_assoc
-/
lemma HasPullback.comp_left_left_iff_of_isIso
    {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {X' : C} (i : X' ⟶ X) [IsIso i] :
    HasPullback (i ≫ f) g ↔ HasPullback f g := by
  refine ⟨fun h => ?_, fun _ => inferInstance⟩
  rw [← IsIso.inv_hom_id_assoc i f]
  infer_instance

instance {X Y Z Z' : C} {f : X ⟶ Z} {g : Y ⟶ Z'} (i : Z ⟶ Z') [IsIso i] [HasPullback (f ≫ i) g] :
    HasPullback f (g ≫ inv i) := by
  simpa using hasPullback_of_comp_mono (f ≫ i) g (inv i)

/--
lemma `HasPullback.comp_left_right_iff_of_isIso` / 引理 `HasPullback.comp_left_right_iff_of_isIso`

English:
lemma HasPullback.comp_left_right_iff_of_isIso
  proof: ⟨fun h => inferInstance, fun h => by simpa using hasPullback_of_comp_mono f (g ≫ inv i) i⟩

中文:
引理 HasPullback.comp_left_right_iff_of_isIso
  证明: ⟨fun h => inferInstance, fun h => by simpa using hasPullback_of_comp_mono f (g ≫ inv i) i⟩

Depends on / 依赖: hasPullback_of_comp_mono
-/
lemma HasPullback.comp_left_right_iff_of_isIso
    {X Y Z Z' : C} {f : X ⟶ Z} {g : Y ⟶ Z'} (i : Z ⟶ Z') [IsIso i] :
    HasPullback (f ≫ i) g ↔ HasPullback f (g ≫ inv i) :=
  ⟨fun h => inferInstance, fun h => by simpa using hasPullback_of_comp_mono f (g ≫ inv i) i⟩

instance {X Y Z : C} (f : Z ⟶ X) (g : Z ⟶ Y) {X' : C} (i : X ⟶ X') [IsIso i] [HasPushout f g] :
    HasPushout (f ≫ i) g :=
  IsPushout.paste_horiz (.of_hasPushout f g)
    (IsPushout.of_horiz_isIso_epi (inl := inv i ≫ pushout.inl _ _) (inr := 𝟙 (pushout f g)) <|
      ⟨by simp⟩) |>.hasPushout

@[simp]
/--
lemma `HasPushout.comp_left_left_iff_of_isIso` / 引理 `HasPushout.comp_left_left_iff_of_isIso`

English:
lemma HasPushout.comp_left_left_iff_of_isIso
  proof: by
  refine ⟨fun h => ?_, fun _ => inferInstance⟩
  rw [← Category.comp_id f]; rw [← IsIso.hom_inv_id i]; rw [← Category.assoc]
  infer_instance

中文:
引理 HasPushout.comp_left_left_iff_of_isIso
  证明: by
  refine ⟨fun h => ?_, fun _ => inferInstance⟩
  rw [← Category.comp_id f]; rw [← IsIso.hom_inv_id i]; rw [← Category.assoc]
  infer_instance

Depends on / 依赖: Category, Category.assoc, Category.comp_id, IsIso.hom_inv_id, comp_id, hom_inv_id, infer_instance
-/
lemma HasPushout.comp_left_left_iff_of_isIso
    {X Y Z : C} {f : Z ⟶ X} {g : Z ⟶ Y} {X' : C} (i : X ⟶ X') [IsIso i] :
    HasPushout (f ≫ i) g ↔ HasPushout f g := by
  refine ⟨fun h => ?_, fun _ => inferInstance⟩
  rw [← Category.comp_id f]; rw [← IsIso.hom_inv_id i]; rw [← Category.assoc]
  infer_instance

instance {X Y Z Z' : C} {f : Z ⟶ X} {g : Z' ⟶ Y} (i : Z' ⟶ Z) [IsIso i] [HasPushout (i ≫ f) g] :
    HasPushout f (inv i ≫ g) := by
  simpa using hasPushout_of_epi_comp (i ≫ f) g (inv i)

/--
lemma `HasPushout.comp_left_right_iff_of_isIso` / 引理 `HasPushout.comp_left_right_iff_of_isIso`

English:
lemma HasPushout.comp_left_right_iff_of_isIso
  proof: ⟨fun h => inferInstance, fun h => by simpa using hasPushout_of_epi_comp f (inv i ≫ g) i⟩

中文:
引理 HasPushout.comp_left_right_iff_of_isIso
  证明: ⟨fun h => inferInstance, fun h => by simpa using hasPushout_of_epi_comp f (inv i ≫ g) i⟩

Depends on / 依赖: hasPushout_of_epi_comp
-/
lemma HasPushout.comp_left_right_iff_of_isIso
    {X Y Z Z' : C} {f : Z ⟶ X} {g : Z' ⟶ Y} (i : Z' ⟶ Z) [IsIso i] :
    HasPushout (i ≫ f) g ↔ HasPushout f (inv i ≫ g) :=
  ⟨fun h => inferInstance, fun h => by simpa using hasPushout_of_epi_comp f (inv i ≫ g) i⟩

end Limits

end CategoryTheory
