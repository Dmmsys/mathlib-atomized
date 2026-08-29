/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Equivalence

/-!
# 2-commutative squares of functors

Similarly to `Mathlib/CategoryTheory/CommSq.lean`, which defines the notion of commutative squares,
this file introduces the notion of 2-commutative squares of functors.

If `T : C₁ ⥤ C₂`, `L : C₁ ⥤ C₃`, `R : C₂ ⥤ C₄`, `B : C₃ ⥤ C₄` are functors,
then `[CatCommSq T L R B]` contains the datum of an isomorphism `T ⋙ R ≅ L ⋙ B`.

Future work: using this notion in the development of the localization of categories
(e.g. localization of adjunctions).

-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

namespace CategoryTheory

open Category CategoryTheory.Functor

variable {C₁ C₂ C₃ C₄ C₅ C₆ : Type*} [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]
  [Category* C₅] [Category* C₆]

/-- `CatCommSq T L R B` expresses that there is a 2-commutative square of functors, where
the functors `T`, `L`, `R` and `B` are respectively the left, top, right and bottom functors
of the square. -/
@[ext]
/--
Definition of `CatCommSq` / `CatCommSq` 的定义

English:
class CatCommSq
  parameters: (T : C₁ ⥤ C₂) (L : C₁ ⥤ C₃) (R : C₂ ⥤ C₄) (B : C₃ ⥤ C₄)
  axioms and operations (1):
    - iso((T) (L) (R) (B)) : T ⋙ R ≅ L ⋙ B

中文:
类 CatCommSq
  参数: (T : C₁ ⥤ C₂) (L : C₁ ⥤ C₃) (R : C₂ ⥤ C₄) (B : C₃ ⥤ C₄)
  公理与运算 (1 个):
    - iso((T) (L) (R) (B)) : T ⋙ R ≅ L ⋙ B
-/
class CatCommSq (T : C₁ ⥤ C₂) (L : C₁ ⥤ C₃) (R : C₂ ⥤ C₄) (B : C₃ ⥤ C₄) where
  /-- Assuming `[CatCommSq T L R B]`, `iso T L R B` is the isomorphism `T ⋙ R ≅ L ⋙ B`
  given by the 2-commutative square. -/
  iso (T) (L) (R) (B) : T ⋙ R ≅ L ⋙ B

variable (T : C₁ ⥤ C₂) (L : C₁ ⥤ C₃) (R : C₂ ⥤ C₄) (B : C₃ ⥤ C₄)

namespace CatCommSq

/-- The vertical identity `CatCommSq` -/
@[instance_reducible, simps!]
/--
Definition of `vId` / `vId` 的定义

English:
definition vId
  signature: : CatCommSq T (𝟭 C₁) (𝟭 C₂) T where
  body: Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm

中文:
定义 vId
  签名: : CatCommSq T (𝟭 C₁) (𝟭 C₂) T where
  定义体: Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm

Depends on / 依赖: Functor, Functor.leftUnitor, Functor.rightUnitor, leftUnitor, rightUnitor
-/
def vId : CatCommSq T (𝟭 C₁) (𝟭 C₂) T where
  iso := Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm

/-- The horizontal identity `CatCommSq` -/
@[simps!, instance_reducible]
/--
Definition of `hId` / `hId` 的定义

English:
definition hId
  signature: : CatCommSq (𝟭 C₁) L L (𝟭 C₃) where
  body: Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm

@[reassoc (attr := simp)]

中文:
定义 hId
  签名: : CatCommSq (𝟭 C₁) L L (𝟭 C₃) where
  定义体: Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm

@[reassoc (attr := simp)]

Depends on / 依赖: Functor, Functor.leftUnitor, Functor.rightUnitor, leftUnitor, rightUnitor
-/
def hId : CatCommSq (𝟭 C₁) L L (𝟭 C₃) where
  iso := Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm

@[reassoc (attr := simp)]
/--
lemma `iso_hom_naturality` / 引理 `iso_hom_naturality`

English:
lemma iso_hom_naturality
  given: [h : CatCommSq T L R B] {x y : C₁} (f : x ⟶ y)
  proof: (iso T L R B).hom.naturality f

@[reassoc (attr := simp)]

中文:
引理 iso_hom_naturality
  条件: [h : CatCommSq T L R B] {x y : C₁} (f : x ⟶ y)
  证明: (iso T L R B).hom.naturality f

@[reassoc (attr := simp)]

Depends on / 依赖: hom.naturality, naturality
-/
lemma iso_hom_naturality [h : CatCommSq T L R B] {x y : C₁} (f : x ⟶ y) :
    R.map (T.map f) ≫ (iso T L R B).hom.app y = (iso T L R B).hom.app x ≫ B.map (L.map f) :=
  (iso T L R B).hom.naturality f

@[reassoc (attr := simp)]
/--
lemma `iso_inv_naturality` / 引理 `iso_inv_naturality`

English:
lemma iso_inv_naturality
  given: [h : CatCommSq T L R B] {x y : C₁} (f : x ⟶ y)
  proof: (iso T L R B).inv.naturality f

中文:
引理 iso_inv_naturality
  条件: [h : CatCommSq T L R B] {x y : C₁} (f : x ⟶ y)
  证明: (iso T L R B).inv.naturality f

Depends on / 依赖: inv.naturality, naturality
-/
lemma iso_inv_naturality [h : CatCommSq T L R B] {x y : C₁} (f : x ⟶ y) :
    B.map (L.map f) ≫ (iso T L R B).inv.app y = (iso T L R B).inv.app x ≫ R.map (T.map f) :=
  (iso T L R B).inv.naturality f

/-- Horizontal composition of 2-commutative squares -/
@[simps!, instance_reducible]
/--
Definition of `hComp` / `hComp` 的定义

English:
definition hComp
  signature: (T₁ : C₁ ⥤ C₂) (T₂ : C₂ ⥤ C₃) (V₁ : C₁ ⥤ C₄) (V₂ : C₂ ⥤ C₅) (V₃ : C₃ ⥤ C₆)
  body: associator _ _ _ ≪≫ isoWhiskerLeft T₁ (iso T₂ V₂ V₃ B₂) ≪≫
    (associator _ _ _).symm ≪≫ isoWhiskerRight (iso T₁ V₁ V₂ B₁) B₂ ≪≫
    associator _ _ _

中文:
定义 hComp
  签名: (T₁ : C₁ ⥤ C₂) (T₂ : C₂ ⥤ C₃) (V₁ : C₁ ⥤ C₄) (V₂ : C₂ ⥤ C₅) (V₃ : C₃ ⥤ C₆)
  定义体: associator _ _ _ ≪≫ isoWhiskerLeft T₁ (iso T₂ V₂ V₃ B₂) ≪≫
    (associator _ _ _).symm ≪≫ isoWhiskerRight (iso T₁ V₁ V₂ B₁) B₂ ≪≫
    associator _ _ _

Depends on / 依赖: associator, isoWhiskerLeft
-/
def hComp (T₁ : C₁ ⥤ C₂) (T₂ : C₂ ⥤ C₃) (V₁ : C₁ ⥤ C₄) (V₂ : C₂ ⥤ C₅) (V₃ : C₃ ⥤ C₆)
    (B₁ : C₄ ⥤ C₅) (B₂ : C₅ ⥤ C₆) [CatCommSq T₁ V₁ V₂ B₁] [CatCommSq T₂ V₂ V₃ B₂] :
    CatCommSq (T₁ ⋙ T₂) V₁ V₃ (B₁ ⋙ B₂) where
  iso := associator _ _ _ ≪≫ isoWhiskerLeft T₁ (iso T₂ V₂ V₃ B₂) ≪≫
    (associator _ _ _).symm ≪≫ isoWhiskerRight (iso T₁ V₁ V₂ B₁) B₂ ≪≫
    associator _ _ _

/--
Definition of `hComp'` / `hComp'` 的定义

English:
abbreviation hComp'
  signature: {T₁ : C₁ ⥤ C₂} {T₂ : C₂ ⥤ C₃} {V₁ : C₁ ⥤ C₄} {V₂ : C₂ ⥤ C₅} {V₃ : C₃ ⥤ C₆}
  body: letI := S₁
  letI := S₂
  hComp _ _ _ V₂ _ _ _

中文:
缩写 hComp'
  签名: {T₁ : C₁ ⥤ C₂} {T₂ : C₂ ⥤ C₃} {V₁ : C₁ ⥤ C₄} {V₂ : C₂ ⥤ C₅} {V₃ : C₃ ⥤ C₆}
  定义体: letI := S₁
  letI := S₂
  hComp _ _ _ V₂ _ _ _
-/
abbrev hComp' {T₁ : C₁ ⥤ C₂} {T₂ : C₂ ⥤ C₃} {V₁ : C₁ ⥤ C₄} {V₂ : C₂ ⥤ C₅} {V₃ : C₃ ⥤ C₆}
    {B₁ : C₄ ⥤ C₅} {B₂ : C₅ ⥤ C₆} (S₁ : CatCommSq T₁ V₁ V₂ B₁) (S₂ : CatCommSq T₂ V₂ V₃ B₂) :
    CatCommSq (T₁ ⋙ T₂) V₁ V₃ (B₁ ⋙ B₂) :=
  letI := S₁
  letI := S₂
  hComp _ _ _ V₂ _ _ _

/-- Vertical composition of 2-commutative squares -/
@[simps!, instance_reducible]
/--
Definition of `vComp` / `vComp` 的定义

English:
definition vComp
  signature: (L₁ : C₁ ⥤ C₂) (L₂ : C₂ ⥤ C₃) (H₁ : C₁ ⥤ C₄) (H₂ : C₂ ⥤ C₅) (H₃ : C₃ ⥤ C₆)
  body: (associator _ _ _).symm ≪≫ isoWhiskerRight (iso H₁ L₁ R₁ H₂) R₂ ≪≫
      associator _ _ _ ≪≫ isoWhiskerLeft L₁ (iso H₂ L₂ R₂ H₃) ≪≫
      (associator _ _ _).symm

中文:
定义 vComp
  签名: (L₁ : C₁ ⥤ C₂) (L₂ : C₂ ⥤ C₃) (H₁ : C₁ ⥤ C₄) (H₂ : C₂ ⥤ C₅) (H₃ : C₃ ⥤ C₆)
  定义体: (associator _ _ _).symm ≪≫ isoWhiskerRight (iso H₁ L₁ R₁ H₂) R₂ ≪≫
      associator _ _ _ ≪≫ isoWhiskerLeft L₁ (iso H₂ L₂ R₂ H₃) ≪≫
      (associator _ _ _).symm

Depends on / 依赖: associator, isoWhiskerRight
-/
def vComp (L₁ : C₁ ⥤ C₂) (L₂ : C₂ ⥤ C₃) (H₁ : C₁ ⥤ C₄) (H₂ : C₂ ⥤ C₅) (H₃ : C₃ ⥤ C₆)
    (R₁ : C₄ ⥤ C₅) (R₂ : C₅ ⥤ C₆) [CatCommSq H₁ L₁ R₁ H₂] [CatCommSq H₂ L₂ R₂ H₃] :
    CatCommSq H₁ (L₁ ⋙ L₂) (R₁ ⋙ R₂) H₃ where
  iso := (associator _ _ _).symm ≪≫ isoWhiskerRight (iso H₁ L₁ R₁ H₂) R₂ ≪≫
      associator _ _ _ ≪≫ isoWhiskerLeft L₁ (iso H₂ L₂ R₂ H₃) ≪≫
      (associator _ _ _).symm

/--
Definition of `vComp'` / `vComp'` 的定义

English:
abbreviation vComp'
  signature: {L₁ : C₁ ⥤ C₂} {L₂ : C₂ ⥤ C₃} {H₁ : C₁ ⥤ C₄} {H₂ : C₂ ⥤ C₅} {H₃ : C₃ ⥤ C₆}
  body: letI := S₁
  letI := S₂
  vComp _ _ _ H₂ _ _ _

中文:
缩写 vComp'
  签名: {L₁ : C₁ ⥤ C₂} {L₂ : C₂ ⥤ C₃} {H₁ : C₁ ⥤ C₄} {H₂ : C₂ ⥤ C₅} {H₃ : C₃ ⥤ C₆}
  定义体: letI := S₁
  letI := S₂
  vComp _ _ _ H₂ _ _ _
-/
abbrev vComp' {L₁ : C₁ ⥤ C₂} {L₂ : C₂ ⥤ C₃} {H₁ : C₁ ⥤ C₄} {H₂ : C₂ ⥤ C₅} {H₃ : C₃ ⥤ C₆}
    {R₁ : C₄ ⥤ C₅} {R₂ : C₅ ⥤ C₆} (S₁ : CatCommSq H₁ L₁ R₁ H₂) (S₂ : CatCommSq H₂ L₂ R₂ H₃) :
    CatCommSq H₁ (L₁ ⋙ L₂) (R₁ ⋙ R₂) H₃ :=
  letI := S₁
  letI := S₂
  vComp _ _ _ H₂ _ _ _

section

variable (T : C₁ ≌ C₂) (L : C₁ ⥤ C₃) (R : C₂ ⥤ C₄) (B : C₃ ≌ C₄)

/-- Horizontal inverse of a 2-commutative square -/
@[simps!, instance_reducible]
/--
Definition of `hInv` / `hInv` 的定义

English:
definition hInv
  signature: (_ : CatCommSq T.functor L R B.functor)
  body: isoWhiskerLeft _ (L.rightUnitor.symm ≪≫ isoWhiskerLeft L B.unitIso ≪≫
      (associator _ _ _).symm ≪≫
      isoWhiskerRight (iso T.functor L R B.functor).symm B.inverse ≪≫
      associator _ _ _) ≪≫ (associator _ _ _).symm ≪≫
      isoWhiskerRight T.counitIso _ ≪≫ leftUnitor _

中文:
定义 hInv
  签名: (_ : CatCommSq T.functor L R B.functor)
  定义体: isoWhiskerLeft _ (L.rightUnitor.symm ≪≫ isoWhiskerLeft L B.unitIso ≪≫
      (associator _ _ _).symm ≪≫
      isoWhiskerRight (iso T.functor L R B.functor).symm B.inverse ≪≫
      associator _ _ _) ≪≫ (associator _ _ _).symm ≪≫
      isoWhiskerRight T.counitIso _ ≪≫ leftUnitor _

Depends on / 依赖: B.unitIso, L.rightUnitor.symm, isoWhiskerLeft, rightUnitor, unitIso
-/
def hInv (_ : CatCommSq T.functor L R B.functor) : CatCommSq T.inverse R L B.inverse where
  iso := isoWhiskerLeft _ (L.rightUnitor.symm ≪≫ isoWhiskerLeft L B.unitIso ≪≫
      (associator _ _ _).symm ≪≫
      isoWhiskerRight (iso T.functor L R B.functor).symm B.inverse ≪≫
      associator _ _ _) ≪≫ (associator _ _ _).symm ≪≫
      isoWhiskerRight T.counitIso _ ≪≫ leftUnitor _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `hInv_hInv` / 引理 `hInv_hInv`

English:
lemma hInv_hInv
  given: (h : CatCommSq T.functor L R B.functor)
  proof: by
  ext X
  rw [← cancel_mono (B.functor.map (L.map (T.unitIso.hom.app X)))]
  rw [← Functor.comp_map]
  erw [← h.iso.hom.naturality (T.unitIso.hom.app X)]
  rw [hInv_iso_hom_app]
  simp only [Equivalence.symm_functor]
  rw [hInv_iso_inv_app]
  dsimp
  simp only [Functor.comp_obj, assoc, ← Functor.

中文:
引理 hInv_hInv
  条件: (h : CatCommSq T.functor L R B.functor)
  证明: by
  ext X
  rw [← cancel_mono (B.functor.map (L.map (T.unitIso.hom.app X)))]
  rw [← Functor.comp_map]
  erw [← h.iso.hom.naturality (T.unitIso.hom.app X)]
  rw [hInv_iso_hom_app]
  simp only [Equivalence.symm_functor]
  rw [hInv_iso_inv_app]
  dsimp
  simp only [Functor.comp_obj, assoc, ← Functor.

Depends on / 依赖: B.functor.map, Equivalence, Equivalence.counitInv_app_functor, Equivalence.counitInv_functor_comp, Equivalence.fun_inv_map, Equivalence.symm_functor, Functor, Functor.comp_map, Functor.comp_obj, Functor.map_comp, Functor.map_id, Iso.inv_hom_id_app, Iso.inv_hom_id_app_assoc, L.map, T.unitIso.hom.app, cancel_mono, comp_id, comp_map, comp_obj, counitInv_app_functor
-/
lemma hInv_hInv (h : CatCommSq T.functor L R B.functor) :
    hInv T.symm R L B.symm (hInv T L R B h) = h := by
  ext X
  rw [← cancel_mono (B.functor.map (L.map (T.unitIso.hom.app X)))]
  rw [← Functor.comp_map]
  erw [← h.iso.hom.naturality (T.unitIso.hom.app X)]
  rw [hInv_iso_hom_app]
  simp only [Equivalence.symm_functor]
  rw [hInv_iso_inv_app]
  dsimp
  simp only [Functor.comp_obj, assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    Equivalence.counitInv_app_functor, Functor.map_id]
  simp only [Functor.map_comp, Equivalence.fun_inv_map, assoc,
    Equivalence.counitInv_functor_comp, comp_id, Iso.inv_hom_id_app_assoc]

/--
Definition of `hInvEquiv` / `hInvEquiv` 的定义

English:
definition hInvEquiv
  signature: : CatCommSq T.functor L R B.functor ≃ CatCommSq T.inverse R L B.inverse where
  body: hInv T L R B
  invFun := hInv T.symm R L B.symm
  left_inv := hInv_hInv T L R B
  right_inv := hInv_hInv T.symm R L B.symm

中文:
定义 hInvEquiv
  签名: : CatCommSq T.functor L R B.functor ≃ CatCommSq T.inverse R L B.inverse where
  定义体: hInv T L R B
  invFun := hInv T.symm R L B.symm
  left_inv := hInv_hInv T L R B
  right_inv := hInv_hInv T.symm R L B.symm
-/
def hInvEquiv : CatCommSq T.functor L R B.functor ≃ CatCommSq T.inverse R L B.inverse where
  toFun := hInv T L R B
  invFun := hInv T.symm R L B.symm
  left_inv := hInv_hInv T L R B
  right_inv := hInv_hInv T.symm R L B.symm

end

section

variable (T : C₁ ⥤ C₂) (L : C₁ ≌ C₃) (R : C₂ ≌ C₄) (B : C₃ ⥤ C₄)

/-- Vertical inverse of a 2-commutative square -/
@[simps!, instance_reducible]
/--
Definition of `vInv` / `vInv` 的定义

English:
definition vInv
  signature: (_ : CatCommSq T L.functor R.functor B)
  body: isoWhiskerRight (B.leftUnitor.symm ≪≫ isoWhiskerRight L.counitIso.symm B ≪≫
      associator _ _ _ ≪≫
      isoWhiskerLeft L.inverse (iso T L.functor R.functor B).symm) R.inverse ≪≫
      associator _ _ _ ≪≫ isoWhiskerLeft _ (associator _ _ _) ≪≫
      (associator _ _ _).symm ≪≫ isoWhiskerLeft _ R.u

中文:
定义 vInv
  签名: (_ : CatCommSq T L.functor R.functor B)
  定义体: isoWhiskerRight (B.leftUnitor.symm ≪≫ isoWhiskerRight L.counitIso.symm B ≪≫
      associator _ _ _ ≪≫
      isoWhiskerLeft L.inverse (iso T L.functor R.functor B).symm) R.inverse ≪≫
      associator _ _ _ ≪≫ isoWhiskerLeft _ (associator _ _ _) ≪≫
      (associator _ _ _).symm ≪≫ isoWhiskerLeft _ R.u

Depends on / 依赖: B.leftUnitor.symm, L.counitIso.symm, counitIso, isoWhiskerRight, leftUnitor
-/
def vInv (_ : CatCommSq T L.functor R.functor B) : CatCommSq B L.inverse R.inverse T where
  iso := isoWhiskerRight (B.leftUnitor.symm ≪≫ isoWhiskerRight L.counitIso.symm B ≪≫
      associator _ _ _ ≪≫
      isoWhiskerLeft L.inverse (iso T L.functor R.functor B).symm) R.inverse ≪≫
      associator _ _ _ ≪≫ isoWhiskerLeft _ (associator _ _ _) ≪≫
      (associator _ _ _).symm ≪≫ isoWhiskerLeft _ R.unitIso.symm ≪≫
      rightUnitor _

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `vInv_vInv` / 引理 `vInv_vInv`

English:
lemma vInv_vInv
  given: (h : CatCommSq T L.functor R.functor B)
  proof: by
  ext X
  rw [vInv_iso_hom_app]
  dsimp
  rw [vInv_iso_inv_app]
  rw [← cancel_mono (B.map (L.functor.map (NatTrans.app L.unitIso.hom X)))]
  rw [← Functor.comp_map]
  dsimp
  simp only [Functor.map_comp, Equivalence.fun_inv_map, Functor.comp_obj,
    Functor.id_obj, assoc, Iso.inv_hom_id_app_ass

中文:
引理 vInv_vInv
  条件: (h : CatCommSq T L.functor R.functor B)
  证明: by
  ext X
  rw [vInv_iso_hom_app]
  dsimp
  rw [vInv_iso_inv_app]
  rw [← cancel_mono (B.map (L.functor.map (NatTrans.app L.unitIso.hom X)))]
  rw [← Functor.comp_map]
  dsimp
  simp only [Functor.map_comp, Equivalence.fun_inv_map, Functor.comp_obj,
    Functor.id_obj, assoc, Iso.inv_hom_id_app_ass

Depends on / 依赖: B.map, B.map_comp, Equivalence, Equivalence.fun_inv_map, Functor, Functor.comp_map, Functor.comp_obj, Functor.id_obj, Functor.map_comp, Iso.inv_hom_id, Iso.inv_hom_id_app, Iso.inv_hom_id_app_assoc, L.counit_app_functor, L.functor.map, L.functor.map_comp, L.functor.map_id, L.unitIso.hom, NatTrans, NatTrans.app, NatTrans.comp_app
-/
lemma vInv_vInv (h : CatCommSq T L.functor R.functor B) :
    vInv B L.symm R.symm T (vInv T L R B h) = h := by
  ext X
  rw [vInv_iso_hom_app]
  dsimp
  rw [vInv_iso_inv_app]
  rw [← cancel_mono (B.map (L.functor.map (NatTrans.app L.unitIso.hom X)))]
  rw [← Functor.comp_map]
  dsimp
  simp only [Functor.map_comp, Equivalence.fun_inv_map, Functor.comp_obj,
    Functor.id_obj, assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app, comp_id]
  rw [← B.map_comp]; rw [L.counit_app_functor]; rw [← L.functor.map_comp]; rw [← NatTrans.comp_app]; rw [Iso.inv_hom_id]; rw [NatTrans.id_app]; rw [L.functor.map_id]
  simp

/--
Definition of `vInvEquiv` / `vInvEquiv` 的定义

English:
definition vInvEquiv
  signature: : CatCommSq T L.functor R.functor B ≃ CatCommSq B L.inverse R.inverse T where
  body: vInv T L R B
  invFun := vInv B L.symm R.symm T
  left_inv := vInv_vInv T L R B
  right_inv := vInv_vInv B L.symm R.symm T

中文:
定义 vInvEquiv
  签名: : CatCommSq T L.functor R.functor B ≃ CatCommSq B L.inverse R.inverse T where
  定义体: vInv T L R B
  invFun := vInv B L.symm R.symm T
  left_inv := vInv_vInv T L R B
  right_inv := vInv_vInv B L.symm R.symm T
-/
def vInvEquiv : CatCommSq T L.functor R.functor B ≃ CatCommSq B L.inverse R.inverse T where
  toFun := vInv T L R B
  invFun := vInv B L.symm R.symm T
  left_inv := vInv_vInv T L R B
  right_inv := vInv_vInv B L.symm R.symm T

end

end CatCommSq

end CategoryTheory
