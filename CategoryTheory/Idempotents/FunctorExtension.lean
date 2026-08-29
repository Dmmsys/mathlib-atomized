/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Idempotents.Karoubi

/-!
# Extension of functors to the idempotent completion

In this file, we construct an extension `functorExtension₁`
of functors `C ⥤ Karoubi D` to functors `Karoubi C ⥤ Karoubi D`. This results in an
equivalence `karoubiUniversal₁ C D : (C ⥤ Karoubi D) ≌ (Karoubi C ⥤ Karoubi D)`.

We also construct an extension `functorExtension₂` of functors
`(C ⥤ D) ⥤ (Karoubi C ⥤ Karoubi D)`. Moreover,
when `D` is idempotent complete, we get equivalences
`karoubiUniversal₂ C D : C ⥤ D ≌ Karoubi C ⥤ Karoubi D`
and `karoubiUniversal C D : C ⥤ D ≌ Karoubi C ⥤ D`.

-/

@[expose] public section

namespace CategoryTheory

namespace Idempotents

open Category Karoubi CategoryTheory.Functor

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `natTrans_eq` / 定理 `natTrans_eq`

English:
theorem natTrans_eq
  given: {F G : Karoubi C ⥤ D} (φ : F ⟶ G) (P : Karoubi C)
  proof: by
  rw [← φ.naturality]; rw [← assoc]; rw [← F.map_comp]
  conv_lhs => rw [← id_comp (φ.app P), ← F.map_id]
  congr
  apply decompId

中文:
定理 natTrans_eq
  条件: {F G : Karoubi C ⥤ D} (φ : F ⟶ G) (P : Karoubi C)
  证明: by
  rw [← φ.naturality]; rw [← assoc]; rw [← F.map_comp]
  conv_lhs => rw [← id_comp (φ.app P), ← F.map_id]
  congr
  apply decompId

Depends on / 依赖: F.map_comp, F.map_id, conv_lhs, decompId, id_comp, map_comp, map_id, naturality
-/
theorem natTrans_eq {F G : Karoubi C ⥤ D} (φ : F ⟶ G) (P : Karoubi C) :
    φ.app P = F.map (decompId_i P) ≫ φ.app P.X ≫ G.map (decompId_p P) := by
  rw [← φ.naturality]; rw [← assoc]; rw [← F.map_comp]
  conv_lhs => rw [← id_comp (φ.app P), ← F.map_id]
  congr
  apply decompId

namespace FunctorExtension₁

set_option linter.style.longLine false in
/-- The canonical extension of a functor `C ⥤ Karoubi D` to a functor
`Karoubi C ⥤ Karoubi D` -/
@[simps]
/--
Definition of `obj` / `obj` 的定义

English:
definition obj
  signature: (F : C ⥤ Karoubi D)
  body: ⟨(F.obj P.X).X, (F.map P.p).f, by simpa only [F.map_comp, hom_ext_iff] using! F.congr_map P.idem⟩
  map f := ⟨(F.map f.f).f, by simpa only [F.map_comp, hom_ext_iff] using! F.congr_map f.comm⟩

中文:
定义 obj
  签名: (F : C ⥤ Karoubi D)
  定义体: ⟨(F.obj P.X).X, (F.map P.p).f, by simpa only [F.map_comp, hom_ext_iff] using! F.congr_map P.idem⟩
  map f := ⟨(F.map f.f).f, by simpa only [F.map_comp, hom_ext_iff] using! F.congr_map f.comm⟩

Depends on / 依赖: F.congr_map, F.map, F.map_comp, F.obj, P.idem, congr_map, f.comm, hom_ext_iff, map_comp
-/
def obj (F : C ⥤ Karoubi D) : Karoubi C ⥤ Karoubi D where
  obj P :=
    ⟨(F.obj P.X).X, (F.map P.p).f, by simpa only [F.map_comp, hom_ext_iff] using! F.congr_map P.idem⟩
  map f := ⟨(F.map f.f).f, by simpa only [F.map_comp, hom_ext_iff] using! F.congr_map f.comm⟩

set_option backward.isDefEq.respectTransparency false in
/-- Extension of a natural transformation `φ` between functors
`C ⥤ Karoubi D` to a natural transformation between the
extension of these functors to `Karoubi C ⥤ Karoubi D` -/
@[simps]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: {F G : C ⥤ Karoubi D} (φ : F ⟶ G)
  body: { f := (F.map P.p).f ≫ (φ.app P.X).f
      comm := by
        have h := φ.naturality P.p
        have h' := F.congr_map P.idem
        simp only [hom_ext_iff, Karoubi.comp_f, F.map_comp] at h h'
        simp only [obj_obj_p, assoc, ← h]
        slice_lhs 1 3 => rw [h', h'] }
  naturality _ _ f := by

中文:
定义 map
  签名: {F G : C ⥤ Karoubi D} (φ : F ⟶ G)
  定义体: { f := (F.map P.p).f ≫ (φ.app P.X).f
      comm := by
        have h := φ.naturality P.p
        have h' := F.congr_map P.idem
        simp only [hom_ext_iff, Karoubi.comp_f, F.map_comp] at h h'
        simp only [obj_obj_p, assoc, ← h]
        slice_lhs 1 3 => rw [h', h'] }
  naturality _ _ f := by

Depends on / 依赖: F.congr_map, F.map, F.map_comp, Functor, Functor.map_comp, Karoubi, Karoubi.comp_f, P.idem, comp_f, comp_p, congr_map, hom_ext_iff, map_comp, naturality, obj_obj_p, p_comp, slice_lhs, slice_rhs
-/
def map {F G : C ⥤ Karoubi D} (φ : F ⟶ G) : obj F ⟶ obj G where
  app P :=
    { f := (F.map P.p).f ≫ (φ.app P.X).f
      comm := by
        have h := φ.naturality P.p
        have h' := F.congr_map P.idem
        simp only [hom_ext_iff, Karoubi.comp_f, F.map_comp] at h h'
        simp only [obj_obj_p, assoc, ← h]
        slice_lhs 1 3 => rw [h', h'] }
  naturality _ _ f := by
    ext
    dsimp [obj]
    have h := φ.naturality f.f
    have h' := F.congr_map (comp_p f)
    have h'' := F.congr_map (p_comp f)
    simp only [hom_ext_iff, Functor.map_comp, comp_f] at h h' h'' ⊢
    slice_rhs 2 3 => rw [← h]
    slice_lhs 1 2 => rw [h']
    slice_rhs 1 2 => rw [h'']

end FunctorExtension₁

variable (C D E)

set_option backward.isDefEq.respectTransparency false in
/-- The canonical functor `(C ⥤ Karoubi D) ⥤ (Karoubi C ⥤ Karoubi D)` -/
@[simps]
/--
Definition of `functorExtension₁` / `functorExtension₁` 的定义

English:
definition functorExtension₁
  signature: : (C ⥤ Karoubi D) ⥤ Karoubi C ⥤ Karoubi D where
  body: FunctorExtension₁.obj
  map := FunctorExtension₁.map
  map_id F := by
    ext P
    exact comp_p (F.map P.p)
  map_comp {F G H} φ φ' := by
    ext P
    simp only [comp_f, FunctorExtension₁.map_app_f, NatTrans.comp_app, assoc]
    have h := φ.naturality P.p
    have h' := F.congr_map P.idem
    simp

中文:
定义 functorExtension₁
  签名: : (C ⥤ Karoubi D) ⥤ Karoubi C ⥤ Karoubi D where
  定义体: FunctorExtension₁.obj
  map := FunctorExtension₁.map
  map_id F := by
    ext P
    exact comp_p (F.map P.p)
  map_comp {F G H} φ φ' := by
    ext P
    simp only [comp_f, FunctorExtension₁.map_app_f, NatTrans.comp_app, assoc]
    have h := φ.naturality P.p
    have h' := F.congr_map P.idem
    simp
-/
def functorExtension₁ : (C ⥤ Karoubi D) ⥤ Karoubi C ⥤ Karoubi D where
  obj := FunctorExtension₁.obj
  map := FunctorExtension₁.map
  map_id F := by
    ext P
    exact comp_p (F.map P.p)
  map_comp {F G H} φ φ' := by
    ext P
    simp only [comp_f, FunctorExtension₁.map_app_f, NatTrans.comp_app, assoc]
    have h := φ.naturality P.p
    have h' := F.congr_map P.idem
    simp only [hom_ext_iff, comp_f, F.map_comp] at h h'
    slice_rhs 2 3 => rw [← h]
    slice_rhs 1 2 => rw [h']
    simp only [assoc]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The natural isomorphism expressing that functors `Karoubi C ⥤ Karoubi D` obtained
using `functorExtension₁` actually extend the original functors `C ⥤ Karoubi D`. -/
@[simps!]
/--
Definition of `functorExtension₁CompWhiskeringLeftToKaroubiIso` / `functorExtension₁CompWhiskeringLeftToKaroubiIso` 的定义

English:
definition functorExtension₁CompWhiskeringLeftToKaroubiIso
  signature: :
  body: NatIso.ofComponents
    (fun F => NatIso.ofComponents
      (fun X =>
        { hom := { f := (F.obj X).p }
          inv := { f := (F.obj X).p } })
      (fun {X Y} f => by simp))
    (by cat_disch)

中文:
定义 functorExtension₁CompWhiskeringLeftToKaroubiIso
  签名: :
  定义体: NatIso.ofComponents
    (fun F => NatIso.ofComponents
      (fun X =>
        { hom := { f := (F.obj X).p }
          inv := { f := (F.obj X).p } })
      (fun {X Y} f => by simp))
    (by cat_disch)

Depends on / 依赖: F.obj, NatIso, NatIso.ofComponents, cat_disch, ofComponents
-/
def functorExtension₁CompWhiskeringLeftToKaroubiIso :
    functorExtension₁ C D ⋙ (whiskeringLeft C (Karoubi C) (Karoubi D)).obj (toKaroubi C) ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun F => NatIso.ofComponents
      (fun X =>
        { hom := { f := (F.obj X).p }
          inv := { f := (F.obj X).p } })
      (fun {X Y} f => by simp))
    (by cat_disch)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `KaroubiUniversal₁.counitIso` / `KaroubiUniversal₁.counitIso` 的定义

English:
definition KaroubiUniversal₁.counitIso
  signature: :
  body: NatIso.ofComponents
    (fun G =>
      { hom :=
          { app := fun P =>
              { f := (G.map (decompId_p P)).f
                comm := by
                  simpa only [hom_ext_iff, G.map_comp, G.map_id] using!
                    G.congr_map
                      (show (toKaroubi C).map 

中文:
定义 KaroubiUniversal₁.counitIso
  签名: :
  定义体: NatIso.ofComponents
    (fun G =>
      { hom :=
          { app := fun P =>
              { f := (G.map (decompId_p P)).f
                comm := by
                  simpa only [hom_ext_iff, G.map_comp, G.map_id] using!
                    G.congr_map
                      (show (toKaroubi C).map 

Depends on / 依赖: G.congr_map, G.map, G.map_comp, G.map_id, NatIso, NatIso.ofComponents, P.decompId_p, congr_map, decompId_i, decompId_p, decompId_p_naturality, hom_ext_iff, map_comp, map_id, naturality, ofComponents, toKaroubi
-/
def KaroubiUniversal₁.counitIso :
    (whiskeringLeft C (Karoubi C) (Karoubi D)).obj (toKaroubi C) ⋙ functorExtension₁ C D ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun G =>
      { hom :=
          { app := fun P =>
              { f := (G.map (decompId_p P)).f
                comm := by
                  simpa only [hom_ext_iff, G.map_comp, G.map_id] using!
                    G.congr_map
                      (show (toKaroubi C).map P.p ≫ P.decompId_p ≫ 𝟙 _ = P.decompId_p by simp) }
            naturality := fun P Q f => by
              simpa only [hom_ext_iff, G.map_comp]
                using! (G.congr_map (decompId_p_naturality f)).symm }
        inv :=
          { app := fun P =>
              { f := (G.map (decompId_i P)).f
                comm := by
                  simpa only [hom_ext_iff, G.map_comp, G.map_id] using!
                    G.congr_map
                      (show 𝟙 _ ≫ P.decompId_i ≫ (toKaroubi C).map P.p = P.decompId_i by simp) }
            naturality := fun P Q f => by
              simpa only [hom_ext_iff, G.map_comp] using! G.congr_map (decompId_i_naturality f) }
        hom_inv_id := by
          ext P
          simpa only [hom_ext_iff, G.map_comp, G.map_id] using! G.congr_map P.decomp_p.symm
        inv_hom_id := by
          ext P
          simpa only [hom_ext_iff, G.map_comp, G.map_id] using! G.congr_map P.decompId.symm })
    (fun {X Y} φ => by
      ext P
      dsimp
      rw [natTrans_eq φ P]; rw [P.decomp_p]
      simp only [Functor.map_comp, comp_f, assoc]
      rfl)

attribute [simps!] KaroubiUniversal₁.counitIso

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The equivalence of categories `(C ⥤ Karoubi D) ≌ (Karoubi C ⥤ Karoubi D)`. -/
@[simps]
/--
Definition of `karoubiUniversal₁` / `karoubiUniversal₁` 的定义

English:
definition karoubiUniversal₁
  signature: : C ⥤ Karoubi D ≌ Karoubi C ⥤ Karoubi D where
  body: functorExtension₁ C D
  inverse := (whiskeringLeft C (Karoubi C) (Karoubi D)).obj (toKaroubi C)
  unitIso := (functorExtension₁CompWhiskeringLeftToKaroubiIso C D).symm
  counitIso := KaroubiUniversal₁.counitIso C D
  functor_unitIso_comp F := by
    ext P
    dsimp
    rw [comp_p]; rw [← comp_f]; rw

中文:
定义 karoubiUniversal₁
  签名: : C ⥤ Karoubi D ≌ Karoubi C ⥤ Karoubi D where
  定义体: functorExtension₁ C D
  inverse := (whiskeringLeft C (Karoubi C) (Karoubi D)).obj (toKaroubi C)
  unitIso := (functorExtension₁CompWhiskeringLeftToKaroubiIso C D).symm
  counitIso := KaroubiUniversal₁.counitIso C D
  functor_unitIso_comp F := by
    ext P
    dsimp
    rw [comp_p]; rw [← comp_f]; rw
-/
def karoubiUniversal₁ : C ⥤ Karoubi D ≌ Karoubi C ⥤ Karoubi D where
  functor := functorExtension₁ C D
  inverse := (whiskeringLeft C (Karoubi C) (Karoubi D)).obj (toKaroubi C)
  unitIso := (functorExtension₁CompWhiskeringLeftToKaroubiIso C D).symm
  counitIso := KaroubiUniversal₁.counitIso C D
  functor_unitIso_comp F := by
    ext P
    dsimp
    rw [comp_p]; rw [← comp_f]; rw [← F.map_comp]; rw [P.idem]

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `functorExtension₁Comp` / `functorExtension₁Comp` 的定义

English:
definition functorExtension₁Comp
  signature: (F : C ⥤ Karoubi D) (G : D ⥤ Karoubi E)
  body: Iso.refl _

中文:
定义 functorExtension₁Comp
  签名: (F : C ⥤ Karoubi D) (G : D ⥤ Karoubi E)
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def functorExtension₁Comp (F : C ⥤ Karoubi D) (G : D ⥤ Karoubi E) :
    (functorExtension₁ C E).obj (F ⋙ (functorExtension₁ D E).obj G) ≅
      (functorExtension₁ C D).obj F ⋙ (functorExtension₁ D E).obj G :=
  Iso.refl _

set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical functor `(C ⥤ D) ⥤ (Karoubi C ⥤ Karoubi D)` -/
@[simps!]
/--
Definition of `functorExtension₂` / `functorExtension₂` 的定义

English:
definition functorExtension₂
  signature: : (C ⥤ D) ⥤ Karoubi C ⥤ Karoubi D
  body: (whiskeringRight C D (Karoubi D)).obj (toKaroubi D) ⋙ functorExtension₁ C D

中文:
定义 functorExtension₂
  签名: : (C ⥤ D) ⥤ Karoubi C ⥤ Karoubi D
  定义体: (whiskeringRight C D (Karoubi D)).obj (toKaroubi D) ⋙ functorExtension₁ C D

Depends on / 依赖: Karoubi, toKaroubi, whiskeringRight
-/
def functorExtension₂ : (C ⥤ D) ⥤ Karoubi C ⥤ Karoubi D :=
  (whiskeringRight C D (Karoubi D)).obj (toKaroubi D) ⋙ functorExtension₁ C D

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The natural isomorphism expressing that functors `Karoubi C ⥤ Karoubi D` obtained
using `functorExtension₂` actually extend the original functors `C ⥤ D`. -/
@[simps!]
/--
Definition of `functorExtension₂CompWhiskeringLeftToKaroubiIso` / `functorExtension₂CompWhiskeringLeftToKaroubiIso` 的定义

English:
definition functorExtension₂CompWhiskeringLeftToKaroubiIso
  signature: :
  body: NatIso.ofComponents
    (fun F => NatIso.ofComponents
      (fun X =>
        { hom := { f := 𝟙 _ }
          inv := { f := 𝟙 _ } })
      (by simp))
    (by cat_disch)

中文:
定义 functorExtension₂CompWhiskeringLeftToKaroubiIso
  签名: :
  定义体: NatIso.ofComponents
    (fun F => NatIso.ofComponents
      (fun X =>
        { hom := { f := 𝟙 _ }
          inv := { f := 𝟙 _ } })
      (by simp))
    (by cat_disch)

Depends on / 依赖: NatIso, NatIso.ofComponents, cat_disch, ofComponents
-/
def functorExtension₂CompWhiskeringLeftToKaroubiIso :
    functorExtension₂ C D ⋙ (whiskeringLeft C (Karoubi C) (Karoubi D)).obj (toKaroubi C) ≅
      (whiskeringRight C D (Karoubi D)).obj (toKaroubi D) :=
  NatIso.ofComponents
    (fun F => NatIso.ofComponents
      (fun X =>
        { hom := { f := 𝟙 _ }
          inv := { f := 𝟙 _ } })
      (by simp))
    (by cat_disch)

section IsIdempotentComplete

variable [IsIdempotentComplete D]

/-- The equivalence of categories `(C ⥤ D) ≌ (Karoubi C ⥤ Karoubi D)` when `D`
is idempotent complete. -/
@[simp]
/--
Definition of `karoubiUniversal₂` / `karoubiUniversal₂` 的定义

English:
definition karoubiUniversal₂
  signature: : C ⥤ D ≌ Karoubi C ⥤ Karoubi D
  body: (Equivalence.congrRight (toKaroubi D).asEquivalence).trans (karoubiUniversal₁ C D)

中文:
定义 karoubiUniversal₂
  签名: : C ⥤ D ≌ Karoubi C ⥤ Karoubi D
  定义体: (Equivalence.congrRight (toKaroubi D).asEquivalence).trans (karoubiUniversal₁ C D)

Depends on / 依赖: Equivalence, Equivalence.congrRight, asEquivalence, congrRight, toKaroubi
-/
noncomputable def karoubiUniversal₂ : C ⥤ D ≌ Karoubi C ⥤ Karoubi D :=
  (Equivalence.congrRight (toKaroubi D).asEquivalence).trans (karoubiUniversal₁ C D)

/--
theorem `karoubiUniversal₂_functor_eq` / 定理 `karoubiUniversal₂_functor_eq`

English:
theorem karoubiUniversal₂_functor_eq
  statement: (karoubiUniversal₂ C D).functor = functorExtension₂ C D
  proof: rfl

中文:
定理 karoubiUniversal₂_functor_eq
  结论: (karoubiUniversal₂ C D).functor = functorExtension₂ C D
  证明: rfl
-/
theorem karoubiUniversal₂_functor_eq : (karoubiUniversal₂ C D).functor = functorExtension₂ C D :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (functorExtension₂ C D).IsEquivalence
  body: by
  rw [← karoubiUniversal₂_functor_eq]
  infer_instance

中文:
实例 :
  签名: (functorExtension₂ C D).IsEquivalence
  定义体: by
  rw [← karoubiUniversal₂_functor_eq]
  infer_instance

Depends on / 依赖: infer_instance
-/
noncomputable instance : (functorExtension₂ C D).IsEquivalence := by
  rw [← karoubiUniversal₂_functor_eq]
  infer_instance

/-- The extension of functors functor `(C ⥤ D) ⥤ (Karoubi C ⥤ D)`
when `D` is idempotent complete. -/
@[simps!]
/--
Definition of `functorExtension` / `functorExtension` 的定义

English:
definition functorExtension
  signature: : (C ⥤ D) ⥤ Karoubi C ⥤ D
  body: functorExtension₂ C D ⋙
    (whiskeringRight (Karoubi C) (Karoubi D) D).obj (toKaroubiEquivalence D).inverse

中文:
定义 functorExtension
  签名: : (C ⥤ D) ⥤ Karoubi C ⥤ D
  定义体: functorExtension₂ C D ⋙
    (whiskeringRight (Karoubi C) (Karoubi D) D).obj (toKaroubiEquivalence D).inverse

Depends on / 依赖: Karoubi, inverse, toKaroubiEquivalence, whiskeringRight
-/
noncomputable def functorExtension : (C ⥤ D) ⥤ Karoubi C ⥤ D :=
  functorExtension₂ C D ⋙
    (whiskeringRight (Karoubi C) (Karoubi D) D).obj (toKaroubiEquivalence D).inverse

/-- The equivalence `(C ⥤ D) ≌ (Karoubi C ⥤ D)` when `D` is idempotent complete. -/
@[simp]
/--
Definition of `karoubiUniversal` / `karoubiUniversal` 的定义

English:
definition karoubiUniversal
  signature: : C ⥤ D ≌ Karoubi C ⥤ D
  body: (karoubiUniversal₂ C D).trans (Equivalence.congrRight (toKaroubi D).asEquivalence.symm)

中文:
定义 karoubiUniversal
  签名: : C ⥤ D ≌ Karoubi C ⥤ D
  定义体: (karoubiUniversal₂ C D).trans (Equivalence.congrRight (toKaroubi D).asEquivalence.symm)

Depends on / 依赖: Equivalence, Equivalence.congrRight, asEquivalence, asEquivalence.symm, congrRight, toKaroubi
-/
noncomputable def karoubiUniversal : C ⥤ D ≌ Karoubi C ⥤ D :=
  (karoubiUniversal₂ C D).trans (Equivalence.congrRight (toKaroubi D).asEquivalence.symm)

/--
theorem `karoubiUniversal_functor_eq` / 定理 `karoubiUniversal_functor_eq`

English:
theorem karoubiUniversal_functor_eq
  statement: (karoubiUniversal C D).functor = functorExtension C D
  proof: rfl

中文:
定理 karoubiUniversal_functor_eq
  结论: (karoubiUniversal C D).functor = functorExtension C D
  证明: rfl
-/
theorem karoubiUniversal_functor_eq : (karoubiUniversal C D).functor = functorExtension C D :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (functorExtension C D).IsEquivalence
  body: by
  rw [← karoubiUniversal_functor_eq]
  infer_instance

中文:
实例 :
  签名: (functorExtension C D).IsEquivalence
  定义体: by
  rw [← karoubiUniversal_functor_eq]
  infer_instance

Depends on / 依赖: infer_instance, karoubiUniversal_functor_eq
-/
noncomputable instance : (functorExtension C D).IsEquivalence := by
  rw [← karoubiUniversal_functor_eq]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ((whiskeringLeft C (Karoubi C) D).obj (toKaroubi C)).IsEquivalence
  body: by
  have : ((whiskeringLeft C (Karoubi C) D).obj (toKaroubi C) ⋙
    (whiskeringRight C D (Karoubi D)).obj (toKaroubi D) ⋙
    (whiskeringRight C (Karoubi D) D).obj (Functor.inv (toKaroubi D))).IsEquivalence := by
    change (karoubiUniversal C D).inverse.IsEquivalence
    infer_instance
  exact Fu

中文:
实例 :
  签名: ((whiskeringLeft C (Karoubi C) D).obj (toKaroubi C)).IsEquivalence
  定义体: by
  have : ((whiskeringLeft C (Karoubi C) D).obj (toKaroubi C) ⋙
    (whiskeringRight C D (Karoubi D)).obj (toKaroubi D) ⋙
    (whiskeringRight C (Karoubi D) D).obj (Functor.inv (toKaroubi D))).IsEquivalence := by
    change (karoubiUniversal C D).inverse.IsEquivalence
    infer_instance
  exact Fu

Depends on / 依赖: Functor, Functor.inv, Functor.isEquivalence_of_comp_right, IsEquivalence, Karoubi, infer_instance, inverse, inverse.IsEquivalence, isEquivalence_of_comp_right, karoubiUniversal, toKaroubi, whiskeringLeft, whiskeringRight
-/
instance : ((whiskeringLeft C (Karoubi C) D).obj (toKaroubi C)).IsEquivalence := by
  have : ((whiskeringLeft C (Karoubi C) D).obj (toKaroubi C) ⋙
    (whiskeringRight C D (Karoubi D)).obj (toKaroubi D) ⋙
    (whiskeringRight C (Karoubi D) D).obj (Functor.inv (toKaroubi D))).IsEquivalence := by
    change (karoubiUniversal C D).inverse.IsEquivalence
    infer_instance
  exact Functor.isEquivalence_of_comp_right _
    ((whiskeringRight C _ _).obj (toKaroubi D) ⋙
      (whiskeringRight C (Karoubi D) D).obj (Functor.inv (toKaroubi D)))

variable {C D}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
theorem `whiskeringLeft_obj_preimage_app` / 定理 `whiskeringLeft_obj_preimage_app`

English:
theorem whiskeringLeft_obj_preimage_app
  statement: {F G : Karoubi C ⥤ D}
  proof: by
  rw [natTrans_eq]
  congr 2
  rw [← congr_app (((whiskeringLeft _ _ _).obj (toKaroubi _)).map_preimage τ) P.X]
  dsimp
  congr

中文:
定理 whiskeringLeft_obj_preimage_app
  结论: {F G : Karoubi C ⥤ D}
  证明: by
  rw [natTrans_eq]
  congr 2
  rw [← congr_app (((whiskeringLeft _ _ _).obj (toKaroubi _)).map_preimage τ) P.X]
  dsimp
  congr

Depends on / 依赖: congr_app, map_preimage, natTrans_eq, toKaroubi, whiskeringLeft
-/
theorem whiskeringLeft_obj_preimage_app {F G : Karoubi C ⥤ D}
    (τ : toKaroubi _ ⋙ F ⟶ toKaroubi _ ⋙ G) (P : Karoubi C) :
    (((whiskeringLeft _ _ _).obj (toKaroubi _)).preimage τ).app P =
      F.map P.decompId_i ≫ τ.app P.X ≫ G.map P.decompId_p := by
  rw [natTrans_eq]
  congr 2
  rw [← congr_app (((whiskeringLeft _ _ _).obj (toKaroubi _)).map_preimage τ) P.X]
  dsimp
  congr

end IsIdempotentComplete

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable {C D} in
/--
Definition of `whiskeringLeftObjToKaroubiFullyFaithful` / `whiskeringLeftObjToKaroubiFullyFaithful` 的定义

English:
definition whiskeringLeftObjToKaroubiFullyFaithful
  signature: :
  body: { app P := F.map P.decompId_i ≫ τ.app P.X ≫ G.map P.decompId_p
      naturality X Y f := by
        dsimp at τ ⊢
        have h₁ : f ≫ Y.decompId_i = X.decompId_i ≫ (toKaroubi C).map f.f := by simp
        have h₂ := τ.naturality f.f
        have h₃ : X.decompId_p ≫ f = (toKaroubi C).map f.f ≫ Y.dec

中文:
定义 whiskeringLeftObjToKaroubiFullyFaithful
  签名: :
  定义体: { app P := F.map P.decompId_i ≫ τ.app P.X ≫ G.map P.decompId_p
      naturality X Y f := by
        dsimp at τ ⊢
        have h₁ : f ≫ Y.decompId_i = X.decompId_i ≫ (toKaroubi C).map f.f := by simp
        have h₂ := τ.naturality f.f
        have h₃ : X.decompId_p ≫ f = (toKaroubi C).map f.f ≫ Y.dec

Depends on / 依赖: Category, Category.assoc, F.map, F.map_comp_assoc, G.map, G.map_comp, P.decompId_i, P.decompId_p, X.decompId_i, X.decompId_p, Y.decompId_i, Y.decompId_p, decompId_i, decompId_p, map_comp, map_comp_assoc, naturality, preimage_map, reassoc_of, toKaroubi
-/
def whiskeringLeftObjToKaroubiFullyFaithful :
    ((Functor.whiskeringLeft C (Karoubi C) D).obj (toKaroubi C)).FullyFaithful where
  preimage {F G} τ :=
    { app P := F.map P.decompId_i ≫ τ.app P.X ≫ G.map P.decompId_p
      naturality X Y f := by
        dsimp at τ ⊢
        have h₁ : f ≫ Y.decompId_i = X.decompId_i ≫ (toKaroubi C).map f.f := by simp
        have h₂ := τ.naturality f.f
        have h₃ : X.decompId_p ≫ f = (toKaroubi C).map f.f ≫ Y.decompId_p := by simp
        dsimp at h₂
        rw [Category.assoc]; rw [Category.assoc]; rw [← F.map_comp_assoc]; rw [h₁]; rw [F.map_comp_assoc]; rw [reassoc_of% h₂]; rw [← G.map_comp]; rw [← h₃]; rw [G.map_comp] }
  preimage_map {F G} τ := by ext X; exact (natTrans_eq _ _).symm
  map_preimage {F G} τ := by
    ext X
    dsimp
    rw [Karoubi.decompId_i_toKaroubi]; rw [Karoubi.decompId_p_toKaroubi]; rw [Functor.map_id]; rw [Category.id_comp]
    change _ ≫ G.map (𝟙 _) = _
    simp

end Idempotents

end CategoryTheory
