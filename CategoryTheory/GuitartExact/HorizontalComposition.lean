/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.GuitartExact.Opposite

/-!
# Horizontal composition of Guitart exact squares

In this file, we show that the horizontal composition of Guitart exact squares
is Guitart exact.

-/

@[expose] public section

namespace CategoryTheory

open Category

variable {C₁ C₂ C₃ D₁ D₂ D₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
  [Category* D₁] [Category* D₂] [Category* D₃]

namespace TwoSquare

section WhiskerHorizontal

variable {T : C₁ ⥤ D₁} {L : C₁ ⥤ C₂} {R : D₁ ⥤ D₂} {B : C₂ ⥤ D₂} (w : TwoSquare T L R B)
  {T' : C₁ ⥤ D₁} {B' : C₂ ⥤ D₂}

/-- Given `w : TwoSquare T L R B`, one may obtain a 2-square `TwoSquare T' L R B'` if we
provide natural transformations `α : T ⟶ T'` and `β : B' ⟶ B`. -/
@[simps!]
/--
Definition of `whiskerHorizontal` / `whiskerHorizontal` 的定义

English:
definition whiskerHorizontal
  signature: (α : T' ⟶ T) (β : B ⟶ B')
  body: (w.whiskerTop α).whiskerBottom β

中文:
定义 whiskerHorizontal
  签名: (α : T' ⟶ T) (β : B ⟶ B')
  定义体: (w.whiskerTop α).whiskerBottom β

Depends on / 依赖: w.whiskerTop, whiskerBottom, whiskerTop
-/
def whiskerHorizontal (α : T' ⟶ T) (β : B ⟶ B') :
    TwoSquare T' L R B' :=
  (w.whiskerTop α).whiskerBottom β

namespace GuitartExact

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `whiskerHorizontal` / 引理 `whiskerHorizontal`

English:
lemma whiskerHorizontal
  given: [w.GuitartExact] (α : T ≅ T') (β : B ≅ B')
  proof: by
  rw [guitartExact_iff_final]
  intro X₂
  let e : costructuredArrowRightwards (w.whiskerHorizontal α.inv β.hom) X₂ ≅
      w.costructuredArrowRightwards X₂ ⋙ (CostructuredArrow.mapIso (β.app X₂)).functor :=
    NatIso.ofComponents (fun f => CostructuredArrow.isoMk (α.symm.app f.left))
  rw [Func

中文:
引理 whiskerHorizontal
  条件: [w.GuitartExact] (α : T ≅ T') (β : B ≅ B')
  证明: by
  rw [guitartExact_iff_final]
  intro X₂
  let e : costructuredArrowRightwards (w.whiskerHorizontal α.inv β.hom) X₂ ≅
      w.costructuredArrowRightwards X₂ ⋙ (CostructuredArrow.mapIso (β.app X₂)).functor :=
    NatIso.ofComponents (fun f => CostructuredArrow.isoMk (α.symm.app f.left))
  rw [Func

Depends on / 依赖: CostructuredArrow, CostructuredArrow.isoMk, CostructuredArrow.mapIso, Functor, Functor.final_natIso_iff, NatIso, NatIso.ofComponents, costructuredArrowRightwards, f.left, final_natIso_iff, functor, guitartExact_iff_final, infer_instance, mapIso, ofComponents, symm.app, w.costructuredArrowRightwards, w.whiskerHorizontal, whiskerHorizontal
-/
lemma whiskerHorizontal [w.GuitartExact] (α : T ≅ T') (β : B ≅ B') :
    (w.whiskerHorizontal α.inv β.hom).GuitartExact := by
  rw [guitartExact_iff_final]
  intro X₂
  let e : costructuredArrowRightwards (w.whiskerHorizontal α.inv β.hom) X₂ ≅
      w.costructuredArrowRightwards X₂ ⋙ (CostructuredArrow.mapIso (β.app X₂)).functor :=
    NatIso.ofComponents (fun f => CostructuredArrow.isoMk (α.symm.app f.left))
  rw [Functor.final_natIso_iff e]
  infer_instance

/-- A 2-square is Guitart exact iff it is so after replacing the top and bottom functors by
isomorphic functors. -/
@[simp]
/--
lemma `whiskerHorizontal_iff` / 引理 `whiskerHorizontal_iff`

English:
lemma whiskerHorizontal_iff
  given: (α : T ≅ T') (β : B ≅ B')
  proof: by
  rw [← guitartExact_op_iff]; rw [← w.guitartExact_op_iff]; rw [← whiskerVertical_iff w.op (NatIso.op α.symm) (NatIso.op β.symm)]
  rfl

中文:
引理 whiskerHorizontal_iff
  条件: (α : T ≅ T') (β : B ≅ B')
  证明: by
  rw [← guitartExact_op_iff]; rw [← w.guitartExact_op_iff]; rw [← whiskerVertical_iff w.op (NatIso.op α.symm) (NatIso.op β.symm)]
  rfl

Depends on / 依赖: NatIso, NatIso.op, guitartExact_op_iff, w.guitartExact_op_iff, w.op, whiskerVertical_iff
-/
lemma whiskerHorizontal_iff (α : T ≅ T') (β : B ≅ B') :
    (w.whiskerHorizontal α.inv β.hom).GuitartExact ↔ w.GuitartExact := by
  rw [← guitartExact_op_iff]; rw [← w.guitartExact_op_iff]; rw [← whiskerVertical_iff w.op (NatIso.op α.symm) (NatIso.op β.symm)]
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [w.GuitartExact]
  signature: (α : T' ⟶ T) (β : B ⟶ B')
  body: whiskerHorizontal w (asIso α).symm (asIso β)

中文:
实例 [w.GuitartExact]
  签名: (α : T' ⟶ T) (β : B ⟶ B')
  定义体: whiskerHorizontal w (asIso α).symm (asIso β)

Depends on / 依赖: whiskerHorizontal
-/
instance [w.GuitartExact] (α : T' ⟶ T) (β : B ⟶ B')
    [IsIso α] [IsIso β] : (w.whiskerHorizontal α β).GuitartExact :=
  whiskerHorizontal w (asIso α).symm (asIso β)

end GuitartExact

end WhiskerHorizontal

section HorizontalComposition

variable {V₁ : C₁ ⥤ D₁} {T₁ : C₁ ⥤ C₂} {B₁ : D₁ ⥤ D₂} {V₂ : C₂ ⥤ D₂}
  (w : TwoSquare T₁ V₁ V₂ B₁)
  {T₂ : C₂ ⥤ C₃} {B₂ : D₂ ⥤ D₃} {V₃ : C₃ ⥤ D₃}
  (w' : TwoSquare T₂ V₂ V₃ B₂)

/-- The horizontal composition of 2-squares. (Variant where we allow the replacement of
the horizontal compositions by isomorphic functors.) -/
@[simps!]
/--
Definition of `hComp'` / `hComp'` 的定义

English:
definition hComp'
  signature: {T₁₂ : C₁ ⥤ C₃} {B₁₂ : D₁ ⥤ D₃} (eT : T₁ ⋙ T₂ ≅ T₁₂) (eB : B₁ ⋙ B₂ ≅ B₁₂)
  body: (w ≫ₕ w').whiskerHorizontal eT.inv eB.hom

中文:
定义 hComp'
  签名: {T₁₂ : C₁ ⥤ C₃} {B₁₂ : D₁ ⥤ D₃} (eT : T₁ ⋙ T₂ ≅ T₁₂) (eB : B₁ ⋙ B₂ ≅ B₁₂)
  定义体: (w ≫ₕ w').whiskerHorizontal eT.inv eB.hom

Depends on / 依赖: eB.hom, eT.inv, whiskerHorizontal
-/
def hComp' {T₁₂ : C₁ ⥤ C₃} {B₁₂ : D₁ ⥤ D₃} (eT : T₁ ⋙ T₂ ≅ T₁₂) (eB : B₁ ⋙ B₂ ≅ B₁₂) :
    TwoSquare T₁₂ V₁ V₃ B₁₂ :=
  (w ≫ₕ w').whiskerHorizontal eT.inv eB.hom

namespace GuitartExact

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `hComp` / 实例 `hComp`

English:
instance hComp
  signature: [w.GuitartExact] [w'.GuitartExact]
  body: by
  rw [← guitartExact_op_iff]
  have : (w ≫ₕ w').op = w.op ≫ᵥ w'.op := by ext; simp
  rw [this]
  exact inferInstanceAs (w.op ≫ᵥ w'.op).GuitartExact

中文:
实例 hComp
  签名: [w.GuitartExact] [w'.GuitartExact]
  定义体: by
  rw [← guitartExact_op_iff]
  have : (w ≫ₕ w').op = w.op ≫ᵥ w'.op := by ext; simp
  rw [this]
  exact inferInstanceAs (w.op ≫ᵥ w'.op).GuitartExact

Depends on / 依赖: GuitartExact, guitartExact_op_iff, w.op
-/
instance hComp [w.GuitartExact] [w'.GuitartExact] :
    (w ≫ₕ w').GuitartExact := by
  rw [← guitartExact_op_iff]
  have : (w ≫ₕ w').op = w.op ≫ᵥ w'.op := by ext; simp
  rw [this]
  exact inferInstanceAs (w.op ≫ᵥ w'.op).GuitartExact

/--
Instance `hComp'` / 实例 `hComp'`

English:
instance hComp'
  signature: {T₁₂ : C₁ ⥤ C₃} {B₁₂ : D₁ ⥤ D₃} (eT : T₁ ⋙ T₂ ≅ T₁₂) (eB : B₁ ⋙ B₂ ≅ B₁₂)
  body: by
  dsimp only [TwoSquare.hComp']
  infer_instance

中文:
实例 hComp'
  签名: {T₁₂ : C₁ ⥤ C₃} {B₁₂ : D₁ ⥤ D₃} (eT : T₁ ⋙ T₂ ≅ T₁₂) (eB : B₁ ⋙ B₂ ≅ B₁₂)
  定义体: by
  dsimp only [TwoSquare.hComp']
  infer_instance

Depends on / 依赖: TwoSquare, TwoSquare.hComp, infer_instance
-/
instance hComp' {T₁₂ : C₁ ⥤ C₃} {B₁₂ : D₁ ⥤ D₃} (eT : T₁ ⋙ T₂ ≅ T₁₂) (eB : B₁ ⋙ B₂ ≅ B₁₂)
    [w.GuitartExact] [w'.GuitartExact] :
    (w.hComp' w' eT eB).GuitartExact := by
  dsimp only [TwoSquare.hComp']
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `costructuredArrowRightwardsComp` / `costructuredArrowRightwardsComp` 的定义

English:
definition costructuredArrowRightwardsComp
  signature: (Y₁ : D₁)
  body: NatIso.ofComponents (fun _ => CostructuredArrow.isoMk (Iso.refl _))

中文:
定义 costructuredArrowRightwardsComp
  签名: (Y₁ : D₁)
  定义体: NatIso.ofComponents (fun _ => CostructuredArrow.isoMk (Iso.refl _))

Depends on / 依赖: CostructuredArrow, CostructuredArrow.isoMk, Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def costructuredArrowRightwardsComp (Y₁ : D₁) :
    w.costructuredArrowRightwards Y₁ ⋙ w'.costructuredArrowRightwards (B₁.obj Y₁) ≅
      (w ≫ₕ w').costructuredArrowRightwards Y₁ :=
  NatIso.ofComponents (fun _ => CostructuredArrow.isoMk (Iso.refl _))

/--
lemma `of_hComp` / 引理 `of_hComp`

English:
lemma of_hComp
  given: [B₁.EssSurj] [w.GuitartExact] [(w ≫ₕ w').GuitartExact]
  proof: by
  rw [guitartExact_iff_final]
  intro Y₂
  rw [costructuredArrowRightwards_final_iff_of_iso _ (B₁.objObjPreimageIso Y₂).symm]
  have : (w.costructuredArrowRightwards (B₁.objPreimage Y₂) ⋙
      w'.costructuredArrowRightwards (B₁.obj (B₁.objPreimage Y₂))).Final :=
    (Functor.final_of_natIso (cos

中文:
引理 of_hComp
  条件: [B₁.EssSurj] [w.GuitartExact] [(w ≫ₕ w').GuitartExact]
  证明: by
  rw [guitartExact_iff_final]
  intro Y₂
  rw [costructuredArrowRightwards_final_iff_of_iso _ (B₁.objObjPreimageIso Y₂).symm]
  have : (w.costructuredArrowRightwards (B₁.objPreimage Y₂) ⋙
      w'.costructuredArrowRightwards (B₁.obj (B₁.objPreimage Y₂))).Final :=
    (Functor.final_of_natIso (cos

Depends on / 依赖: Functor, Functor.final_of_final_comp, Functor.final_of_natIso, costructuredArrowRightwards, costructuredArrowRightwardsComp, costructuredArrowRightwards_final_iff_of_iso, final_of_final_comp, final_of_natIso, guitartExact_iff_final, objObjPreimageIso, objPreimage, w.costructuredArrowRightwards
-/
lemma of_hComp [B₁.EssSurj] [w.GuitartExact] [(w ≫ₕ w').GuitartExact] :
    w'.GuitartExact := by
  rw [guitartExact_iff_final]
  intro Y₂
  rw [costructuredArrowRightwards_final_iff_of_iso _ (B₁.objObjPreimageIso Y₂).symm]
  have : (w.costructuredArrowRightwards (B₁.objPreimage Y₂) ⋙
      w'.costructuredArrowRightwards (B₁.obj (B₁.objPreimage Y₂))).Final :=
    (Functor.final_of_natIso (costructuredArrowRightwardsComp w w' _).symm :)
  exact Functor.final_of_final_comp (w.costructuredArrowRightwards (B₁.objPreimage Y₂)) _

/--
lemma `of_hComp'` / 引理 `of_hComp'`

English:
lemma of_hComp'
  statement: {T₁₂ : C₁ ⥤ C₃} {B₁₂ : D₁ ⥤ D₃} (eT : T₁ ⋙ T₂ ≅ T₁₂) (eB : B₁ ⋙ B₂ ≅ B₁₂)
  proof: by
  dsimp [TwoSquare.hComp'] at h
  rw [whiskerHorizontal_iff] at h
  exact of_hComp w w'

中文:
引理 of_hComp'
  结论: {T₁₂ : C₁ ⥤ C₃} {B₁₂ : D₁ ⥤ D₃} (eT : T₁ ⋙ T₂ ≅ T₁₂) (eB : B₁ ⋙ B₂ ≅ B₁₂)
  证明: by
  dsimp [TwoSquare.hComp'] at h
  rw [whiskerHorizontal_iff] at h
  exact of_hComp w w'

Depends on / 依赖: TwoSquare, TwoSquare.hComp, of_hComp, whiskerHorizontal_iff
-/
lemma of_hComp' {T₁₂ : C₁ ⥤ C₃} {B₁₂ : D₁ ⥤ D₃} (eT : T₁ ⋙ T₂ ≅ T₁₂) (eB : B₁ ⋙ B₂ ≅ B₁₂)
    [B₁.EssSurj] [w.GuitartExact] [h : (w.hComp' w' eT eB).GuitartExact] :
    w'.GuitartExact := by
  dsimp [TwoSquare.hComp'] at h
  rw [whiskerHorizontal_iff] at h
  exact of_hComp w w'

/--
lemma `hComp_iff_of_essSurj` / 引理 `hComp_iff_of_essSurj`

English:
lemma hComp_iff_of_essSurj
  given: [B₁.EssSurj] [w.GuitartExact]
  proof: ⟨fun _ => of_hComp w w', fun _ => inferInstance⟩

中文:
引理 hComp_iff_of_essSurj
  条件: [B₁.EssSurj] [w.GuitartExact]
  证明: ⟨fun _ => of_hComp w w', fun _ => inferInstance⟩

Depends on / 依赖: of_hComp
-/
lemma hComp_iff_of_essSurj [B₁.EssSurj] [w.GuitartExact] :
    (w ≫ₕ w').GuitartExact ↔ w'.GuitartExact :=
  ⟨fun _ => of_hComp w w', fun _ => inferInstance⟩

/--
lemma `hComp'_iff_of_essSurj` / 引理 `hComp'_iff_of_essSurj`

English:
lemma hComp'_iff_of_essSurj
  proof: ⟨fun _ => of_hComp' w w' eT eB, fun _ => inferInstance⟩

中文:
引理 hComp'_iff_of_essSurj
  证明: ⟨fun _ => of_hComp' w w' eT eB, fun _ => inferInstance⟩
-/
lemma hComp'_iff_of_essSurj
    {T₁₂ : C₁ ⥤ C₃} {B₁₂ : D₁ ⥤ D₃} (eT : T₁ ⋙ T₂ ≅ T₁₂) (eB : B₁ ⋙ B₂ ≅ B₁₂)
    [B₁.EssSurj] [w.GuitartExact] :
    (w.hComp' w' eT eB).GuitartExact ↔ w'.GuitartExact :=
  ⟨fun _ => of_hComp' w w' eT eB, fun _ => inferInstance⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `hComp_iff_of_equivalences` / 引理 `hComp_iff_of_equivalences`

English:
lemma hComp_iff_of_equivalences
  statement: (eT : C₂ ≌ C₃) (eB : D₂ ≌ D₃)
  proof: by
  let w'' : V₂.op ⋙ eB.op.functor ≅ eT.op.functor ⋙ V₃.op := NatIso.op w'
  have : (w ≫ₕ w'.hom).op = (w.op ≫ᵥ w''.hom) := by ext; simp [w'']
  rw [← guitartExact_op_iff]; rw [← guitartExact_op_iff w]; rw [← vComp_iff_of_equivalences _ _ _ w'']; rw [this]
  rfl

中文:
引理 hComp_iff_of_equivalences
  结论: (eT : C₂ ≌ C₃) (eB : D₂ ≌ D₃)
  证明: by
  let w'' : V₂.op ⋙ eB.op.functor ≅ eT.op.functor ⋙ V₃.op := NatIso.op w'
  have : (w ≫ₕ w'.hom).op = (w.op ≫ᵥ w''.hom) := by ext; simp [w'']
  rw [← guitartExact_op_iff]; rw [← guitartExact_op_iff w]; rw [← vComp_iff_of_equivalences _ _ _ w'']; rw [this]
  rfl

Depends on / 依赖: NatIso, NatIso.op, eB.op.functor, eT.op.functor, functor, guitartExact_op_iff, vComp_iff_of_equivalences, w.op
-/
lemma hComp_iff_of_equivalences (eT : C₂ ≌ C₃) (eB : D₂ ≌ D₃)
    (w' : eT.functor ⋙ V₃ ≅ V₂ ⋙ eB.functor) :
    (w ≫ₕ w'.hom).GuitartExact ↔ w.GuitartExact := by
  let w'' : V₂.op ⋙ eB.op.functor ≅ eT.op.functor ⋙ V₃.op := NatIso.op w'
  have : (w ≫ₕ w'.hom).op = (w.op ≫ᵥ w''.hom) := by ext; simp [w'']
  rw [← guitartExact_op_iff]; rw [← guitartExact_op_iff w]; rw [← vComp_iff_of_equivalences _ _ _ w'']; rw [this]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `hComp'_iff_of_equivalences` / 引理 `hComp'_iff_of_equivalences`

English:
lemma hComp'_iff_of_equivalences
  statement: (E : C₂ ≌ C₃) (E' : D₂ ≌ D₃)
  proof: by
  rw [← hComp_iff_of_equivalences w E E' w']; rw [TwoSquare.hComp']; rw [whiskerHorizontal_iff]

中文:
引理 hComp'_iff_of_equivalences
  结论: (E : C₂ ≌ C₃) (E' : D₂ ≌ D₃)
  证明: by
  rw [← hComp_iff_of_equivalences w E E' w']; rw [TwoSquare.hComp']; rw [whiskerHorizontal_iff]
-/
lemma hComp'_iff_of_equivalences (E : C₂ ≌ C₃) (E' : D₂ ≌ D₃)
    (w' : E.functor ⋙ V₃ ≅ V₂ ⋙ E'.functor)
    {T₁₂ : C₁ ⥤ C₃} {B₁₂ : D₁ ⥤ D₃} (eT : T₁ ⋙ E.functor ≅ T₁₂)
    (eB : B₁ ⋙ E'.functor ≅ B₁₂) :
    (w.hComp' w'.hom eT eB).GuitartExact ↔ w.GuitartExact := by
  rw [← hComp_iff_of_equivalences w E E' w']; rw [TwoSquare.hComp']; rw [whiskerHorizontal_iff]

end GuitartExact

end HorizontalComposition

end TwoSquare

end CategoryTheory
