/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Idempotents.Karoubi

/-!
# Idempotent completeness and functor categories

In this file we define an instance `functor_category_isIdempotentComplete` expressing
that a functor category `J ⥤ C` is idempotent complete when the target category `C` is.

We also provide a fully faithful functor
`karoubiFunctorCategoryEmbedding : Karoubi (J ⥤ C) ⥤ (J ⥤ Karoubi C)` for all categories
`J` and `C`.

-/

@[expose] public section


open CategoryTheory

open CategoryTheory.Category

open CategoryTheory.Idempotents.Karoubi

open CategoryTheory.Limits

namespace CategoryTheory

namespace Idempotents

variable {J C : Type*} [Category* J] [Category* C] (P Q : Karoubi (J ⥤ C)) (f : P ⟶ Q) (X : J)

@[reassoc (attr := simp)]
/--
theorem `app_idem` / 定理 `app_idem`

English:
theorem app_idem
  statement: P.p.app X ≫ P.p.app X = P.p.app X
  proof: congr_app P.idem X

中文:
定理 app_idem
  结论: P.p.app X ≫ P.p.app X = P.p.app X
  证明: congr_app P.idem X

Depends on / 依赖: P.idem, congr_app
-/
theorem app_idem : P.p.app X ≫ P.p.app X = P.p.app X :=
  congr_app P.idem X

variable {P Q}

@[reassoc (attr := simp)]
/--
theorem `app_p_comp` / 定理 `app_p_comp`

English:
theorem app_p_comp
  statement: P.p.app X ≫ f.f.app X = f.f.app X
  proof: congr_app (p_comp f) X

@[reassoc (attr := simp)]

中文:
定理 app_p_comp
  结论: P.p.app X ≫ f.f.app X = f.f.app X
  证明: congr_app (p_comp f) X

@[reassoc (attr := simp)]

Depends on / 依赖: congr_app, p_comp
-/
theorem app_p_comp : P.p.app X ≫ f.f.app X = f.f.app X :=
  congr_app (p_comp f) X

@[reassoc (attr := simp)]
/--
theorem `app_comp_p` / 定理 `app_comp_p`

English:
theorem app_comp_p
  statement: f.f.app X ≫ Q.p.app X = f.f.app X
  proof: congr_app (comp_p f) X

@[reassoc]

中文:
定理 app_comp_p
  结论: f.f.app X ≫ Q.p.app X = f.f.app X
  证明: congr_app (comp_p f) X

@[reassoc]

Depends on / 依赖: comp_p, congr_app
-/
theorem app_comp_p : f.f.app X ≫ Q.p.app X = f.f.app X :=
  congr_app (comp_p f) X

@[reassoc]
/--
theorem `app_p_comm` / 定理 `app_p_comm`

English:
theorem app_p_comm
  statement: P.p.app X ≫ f.f.app X = f.f.app X ≫ Q.p.app X
  proof: congr_app (p_comm f) X

中文:
定理 app_p_comm
  结论: P.p.app X ≫ f.f.app X = f.f.app X ≫ Q.p.app X
  证明: congr_app (p_comm f) X

Depends on / 依赖: congr_app, p_comm
-/
theorem app_p_comm : P.p.app X ≫ f.f.app X = f.f.app X ≫ Q.p.app X :=
  congr_app (p_comm f) X

variable (J C)

set_option backward.isDefEq.respectTransparency false in
/--
Instance `functor_category_isIdempotentComplete` / 实例 `functor_category_isIdempotentComplete`

English:
instance functor_category_isIdempotentComplete
  signature: [IsIdempotentComplete C]
  body: by
  refine ⟨fun F p hp => ?_⟩
  have hC := (isIdempotentComplete_iff_hasEqualizer_of_id_and_idempotent C).mp inferInstance
  have : forall j : J, HasEqualizer (𝟙 _) (p.app j) := fun j => hC _ _ (congr_app hp j)
  /- We construct the direct factor `Y` associated to `p : F ⟶ F` by computing
      the

中文:
实例 functor_category_isIdempotentComplete
  签名: [是IdempotentComplete C]
  定义体: by
  refine ⟨fun F p hp => ?_⟩
  have hC := (isIdempotentComplete_iff_hasEqualizer_of_id_and_idempotent C).mp inferInstance
  have : forall j : J, HasEqualizer (𝟙 _) (p.app j) := fun j => hC _ _ (congr_app hp j)
  /- We construct the direct factor `Y` associated to `p : F ⟶ F` by computing
      the

Depends on / 依赖: HasEqualizer, congr_app, isIdempotentComplete_iff_hasEqualizer_of_id_and_idempotent, p.app
-/
instance functor_category_isIdempotentComplete [IsIdempotentComplete C] :
    IsIdempotentComplete (J ⥤ C) := by
  refine ⟨fun F p hp => ?_⟩
  have hC := (isIdempotentComplete_iff_hasEqualizer_of_id_and_idempotent C).mp inferInstance
  have : forall j : J, HasEqualizer (𝟙 _) (p.app j) := fun j => hC _ _ (congr_app hp j)
  /- We construct the direct factor `Y` associated to `p : F ⟶ F` by computing
      the equalizer of the identity and `p.app j` on each object `(j : J)`. -/
  let Y : J ⥤ C :=
    { obj := fun j => Limits.equalizer (𝟙 _) (p.app j)
      map := fun {j j'} φ =>
        equalizer.lift (Limits.equalizer.ι (𝟙 _) (p.app j) ≫ F.map φ)
          (by rw [comp_id, assoc, p.naturality φ, ← assoc, ← Limits.equalizer.condition, comp_id]) }
  let i : Y ⟶ F :=
    { app := fun j => equalizer.ι _ _
      naturality := fun _ _ _ => by rw [equalizer.lift_ι] }
  let e : F ⟶ Y :=
    { app := fun j =>
        equalizer.lift (p.app j) (by simpa only [comp_id] using! (congr_app hp j).symm)
      naturality := fun j j' φ => equalizer.hom_ext (by simp [Y]) }
  use Y, i, e
  constructor
  · ext j
    dsimp
    rw [assoc]; rw [equalizer.lift_ι]; rw [← equalizer.condition]; rw [id_comp]; rw [comp_id]
  · ext j
    simp [Y, i, e]
namespace KaroubiFunctorCategoryEmbedding

variable {J C}

set_option backward.isDefEq.respectTransparency.types false in
/-- On objects, the functor which sends a formal direct factor `P` of a
functor `F : J ⥤ C` to the functor `J ⥤ Karoubi C` which sends `(j : J)` to
the corresponding direct factor of `F.obj j`. -/
@[simps]
/--
Definition of `obj` / `obj` 的定义

English:
definition obj
  signature: (P : Karoubi (J ⥤ C))
  body: ⟨P.X.obj j, P.p.app j, congr_app P.idem j⟩
  map {j j'} φ :=
    { f := P.p.app j ≫ P.X.map φ
      comm := by
        simp only [NatTrans.naturality, assoc]
        have h := congr_app P.idem j
        rw [NatTrans.comp_app] at h
        rw [reassoc_of% h]; rw [reassoc_of% h] }

中文:
定义 obj
  签名: (P : Karoubi (J ⥤ C))
  定义体: ⟨P.X.obj j, P.p.app j, congr_app P.idem j⟩
  map {j j'} φ :=
    { f := P.p.app j ≫ P.X.map φ
      comm := by
        simp only [NatTrans.naturality, assoc]
        have h := congr_app P.idem j
        rw [NatTrans.comp_app] at h
        rw [reassoc_of% h]; rw [reassoc_of% h] }

Depends on / 依赖: P.X.obj, P.idem, P.p.app, congr_app
-/
def obj (P : Karoubi (J ⥤ C)) : J ⥤ Karoubi C where
  obj j := ⟨P.X.obj j, P.p.app j, congr_app P.idem j⟩
  map {j j'} φ :=
    { f := P.p.app j ≫ P.X.map φ
      comm := by
        simp only [NatTrans.naturality, assoc]
        have h := congr_app P.idem j
        rw [NatTrans.comp_app] at h
        rw [reassoc_of% h]; rw [reassoc_of% h] }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Tautological action on maps of the functor `Karoubi (J ⥤ C) ⥤ (J ⥤ Karoubi C)`. -/
@[simps]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: {P Q : Karoubi (J ⥤ C)} (f : P ⟶ Q)
  body: ⟨f.f.app j, congr_app f.comm j⟩

中文:
定义 map
  签名: {P Q : Karoubi (J ⥤ C)} (f : P ⟶ Q)
  定义体: ⟨f.f.app j, congr_app f.comm j⟩

Depends on / 依赖: congr_app, f.comm, f.f.app
-/
def map {P Q : Karoubi (J ⥤ C)} (f : P ⟶ Q) : obj P ⟶ obj Q where
  app j := ⟨f.f.app j, congr_app f.comm j⟩

end KaroubiFunctorCategoryEmbedding

/-- The tautological fully faithful functor `Karoubi (J ⥤ C) ⥤ (J ⥤ Karoubi C)`. -/
@[simps]
/--
Definition of `karoubiFunctorCategoryEmbedding` / `karoubiFunctorCategoryEmbedding` 的定义

English:
definition karoubiFunctorCategoryEmbedding
  signature: : Karoubi (J ⥤ C) ⥤ J ⥤ Karoubi C where
  body: KaroubiFunctorCategoryEmbedding.obj
  map := KaroubiFunctorCategoryEmbedding.map

中文:
定义 karoubiFunctorCategoryEmbedding
  签名: : Karoubi (J ⥤ C) ⥤ J ⥤ Karoubi C where
  定义体: KaroubiFunctorCategoryEmbedding.obj
  map := KaroubiFunctorCategoryEmbedding.map

Depends on / 依赖: KaroubiFunctorCategoryEmbedding, KaroubiFunctorCategoryEmbedding.obj
-/
def karoubiFunctorCategoryEmbedding : Karoubi (J ⥤ C) ⥤ J ⥤ Karoubi C where
  obj := KaroubiFunctorCategoryEmbedding.obj
  map := KaroubiFunctorCategoryEmbedding.map

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (karoubiFunctorCategoryEmbedding J C).Full
  body: ⟨{f :=
        { app := fun j => (f.app j).f
          naturality := fun j j' φ => by
            rw [← Karoubi.comp_p_assoc]
            have h := hom_ext_iff.mp (f.naturality φ)
            dsimp [karoubiFunctorCategoryEmbedding] at h
            simp only [assoc, h.symm, karoubiFunctorCategoryEmb

中文:
实例 :
  签名: (karoubiFunctorCategoryEmbedding J C).满
  定义体: ⟨{f :=
        { app := fun j => (f.app j).f
          naturality := fun j j' φ => by
            rw [← Karoubi.comp_p_assoc]
            have h := hom_ext_iff.mp (f.naturality φ)
            dsimp [karoubiFunctorCategoryEmbedding] at h
            simp only [assoc, h.symm, karoubiFunctorCategoryEmb

Depends on / 依赖: Karoubi, Karoubi.comp_p_assoc, KaroubiFunctorCategoryEmbedding, KaroubiFunctorCategoryEmbedding.obj_obj_p, P.p.naturality_assoc, comp_p_assoc, f.app, f.naturality, h.symm, hom_ext_iff, hom_ext_iff.mp, karoubiFunctorCategoryEmbedding, karoubiFunctorCategoryEmbedding_obj, naturality, naturality_assoc, obj_obj_p, p_comp
-/
instance : (karoubiFunctorCategoryEmbedding J C).Full where
  map_surjective {P Q} f :=
    ⟨{f :=
        { app := fun j => (f.app j).f
          naturality := fun j j' φ => by
            rw [← Karoubi.comp_p_assoc]
            have h := hom_ext_iff.mp (f.naturality φ)
            dsimp [karoubiFunctorCategoryEmbedding] at h
            simp only [assoc, h.symm, karoubiFunctorCategoryEmbedding_obj,
              KaroubiFunctorCategoryEmbedding.obj_obj_p]
            rw [← P.p.naturality_assoc]
            exact congrArg _ (p_comp (f.app _)).symm }
      comm := by
        ext j
        exact (f.app j).comm }, rfl⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (karoubiFunctorCategoryEmbedding J C).Faithful
  body: by
    ext j
    exact hom_ext_iff.mp (congr_app h j)

中文:
实例 :
  签名: (karoubiFunctorCategoryEmbedding J C).忠实
  定义体: by
    ext j
    exact hom_ext_iff.mp (congr_app h j)

Depends on / 依赖: congr_app, hom_ext_iff, hom_ext_iff.mp
-/
instance : (karoubiFunctorCategoryEmbedding J C).Faithful where
  map_injective h := by
    ext j
    exact hom_ext_iff.mp (congr_app h j)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
theorem `toKaroubi_comp_karoubiFunctorCategoryEmbedding` / 定理 `toKaroubi_comp_karoubiFunctorCategoryEmbedding`

English:
theorem toKaroubi_comp_karoubiFunctorCategoryEmbedding
  proof: by
  apply Functor.ext
  · intro X Y f
    ext j
    simp
  · intro X
    apply Functor.ext
    · intro j j' φ
      ext
      simp
    · intro j
      rfl

中文:
定理 toKaroubi_comp_karoubiFunctorCategoryEmbedding
  证明: by
  apply Functor.ext
  · intro X Y f
    ext j
    simp
  · intro X
    apply Functor.ext
    · intro j j' φ
      ext
      simp
    · intro j
      rfl

Depends on / 依赖: Functor, Functor.ext
-/
theorem toKaroubi_comp_karoubiFunctorCategoryEmbedding :
    toKaroubi _ ⋙ karoubiFunctorCategoryEmbedding J C =
      (Functor.whiskeringRight J _ _).obj (toKaroubi C) := by
  apply Functor.ext
  · intro X Y f
    ext j
    simp
  · intro X
    apply Functor.ext
    · intro j j' φ
      ext
      simp
    · intro j
      rfl

end Idempotents

end CategoryTheory
