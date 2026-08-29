/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.SmallHom
public import Mathlib.CategoryTheory.Shift.ShiftedHom
public import Mathlib.CategoryTheory.Shift.Localization

/-!
# Shrinking morphisms in localized categories equipped with shifts

If `C` is a category equipped with a shift by an additive monoid `M`,
and `W : MorphismProperty C` is compatible with the shift,
we define a type-class `HasSmallLocalizedShiftedHom.{w} W X Y` which
says that all the types of morphisms from `X⟦a⟧` to `Y⟦b⟧` in the
localized category are `w`-small for a certain universe. Then,
we define types `SmallShiftedHom.{w} W X Y m : Type w` for all `m : M`,
and endow these with a composition which transports the composition
on the types `ShiftedHom (L.obj X) (L.obj Y) m` when `L : C ⥤ D` is
any localization functor for `W`.

-/

@[expose] public section

universe w'' w w' v₁ v₂ v₁' v₂' u₁ u₂ u₁' u₂'

namespace CategoryTheory

open Category

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (W : MorphismProperty C) {M : Type w'} [AddMonoid M] [HasShift C M] [HasShift D M]

namespace Localization

section

variable (X Y : C)
variable (M)

/--
Definition of `HasSmallLocalizedShiftedHom` / `HasSmallLocalizedShiftedHom` 的定义

English:
abbreviation HasSmallLocalizedShiftedHom
  signature: : Prop
  body: forall (a b : M), HasSmallLocalizedHom.{w} W (X⟦a⟧) (Y⟦b⟧)

中文:
缩写 HasSmallLocalizedShiftedHom
  签名: : 命题
  定义体: forall (a b : M), HasSmallLocalizedHom.{w} W (X⟦a⟧) (Y⟦b⟧)

Depends on / 依赖: HasSmallLocalizedHom
-/
abbrev HasSmallLocalizedShiftedHom : Prop :=
  forall (a b : M), HasSmallLocalizedHom.{w} W (X⟦a⟧) (Y⟦b⟧)

set_option backward.defeqAttrib.useBackward true in
/--
lemma `hasSmallLocalizedShiftedHom_iff` / 引理 `hasSmallLocalizedShiftedHom_iff`

English:
lemma hasSmallLocalizedShiftedHom_iff
  proof: by
  dsimp [HasSmallLocalizedShiftedHom]
  have eq := fun (a b : M) => small_congr.{w}
    (Iso.homCongr ((L.commShiftIso a).app X) ((L.commShiftIso b).app Y))
  dsimp at eq
  simp only [hasSmallLocalizedHom_iff _ L, eq]

中文:
引理 hasSmallLocalizedShiftedHom_iff
  证明: by
  dsimp [HasSmallLocalizedShiftedHom]
  have eq := fun (a b : M) => small_congr.{w}
    (Iso.homCongr ((L.commShiftIso a).app X) ((L.commShiftIso b).app Y))
  dsimp at eq
  simp only [hasSmallLocalizedHom_iff _ L, eq]

Depends on / 依赖: HasSmallLocalizedShiftedHom, Iso.homCongr, L.commShiftIso, commShiftIso, hasSmallLocalizedHom_iff, homCongr, small_congr
-/
lemma hasSmallLocalizedShiftedHom_iff
    (L : C ⥤ D) [L.IsLocalization W] [L.CommShift M] (X Y : C) :
    HasSmallLocalizedShiftedHom.{w} W M X Y ↔
      forall (a b : M), Small.{w} ((L.obj X)⟦a⟧ ⟶ (L.obj Y)⟦b⟧) := by
  dsimp [HasSmallLocalizedShiftedHom]
  have eq := fun (a b : M) => small_congr.{w}
    (Iso.homCongr ((L.commShiftIso a).app X) ((L.commShiftIso b).app Y))
  dsimp at eq
  simp only [hasSmallLocalizedHom_iff _ L, eq]

variable {Y} in
/--
lemma `hasSmallLocalizedShiftedHom_iff_target` / 引理 `hasSmallLocalizedShiftedHom_iff_target`

English:
lemma hasSmallLocalizedShiftedHom_iff_target
  statement: [W.IsCompatibleWithShift M]
  proof: forall_congr' (fun a => forall_congr' (fun b =>
    hasSmallLocalizedHom_iff_target W (X⟦a⟧) (f⟦b⟧') (W.shift hf b)))

中文:
引理 hasSmallLocalizedShiftedHom_iff_target
  结论: [W.是余mpatibleWithShift M]
  证明: forall_congr' (fun a => forall_congr' (fun b =>
    hasSmallLocalizedHom_iff_target W (X⟦a⟧) (f⟦b⟧') (W.shift hf b)))

Depends on / 依赖: W.shift, forall_congr, hasSmallLocalizedHom_iff_target
-/
lemma hasSmallLocalizedShiftedHom_iff_target [W.IsCompatibleWithShift M]
    {Y' : C} (f : Y ⟶ Y') (hf : W f) :
    HasSmallLocalizedShiftedHom.{w} W M X Y ↔ HasSmallLocalizedShiftedHom.{w} W M X Y' :=
  forall_congr' (fun a => forall_congr' (fun b =>
    hasSmallLocalizedHom_iff_target W (X⟦a⟧) (f⟦b⟧') (W.shift hf b)))

variable {X} in
/--
lemma `hasSmallLocalizedShiftedHom_iff_source` / 引理 `hasSmallLocalizedShiftedHom_iff_source`

English:
lemma hasSmallLocalizedShiftedHom_iff_source
  statement: [W.IsCompatibleWithShift M]
  proof: forall_congr' (fun a => forall_congr' (fun b =>
    hasSmallLocalizedHom_iff_source W (f⟦a⟧') (W.shift hf a) (Y⟦b⟧)))

中文:
引理 hasSmallLocalizedShiftedHom_iff_source
  结论: [W.是余mpatibleWithShift M]
  证明: forall_congr' (fun a => forall_congr' (fun b =>
    hasSmallLocalizedHom_iff_source W (f⟦a⟧') (W.shift hf a) (Y⟦b⟧)))

Depends on / 依赖: W.shift, forall_congr, hasSmallLocalizedHom_iff_source
-/
lemma hasSmallLocalizedShiftedHom_iff_source [W.IsCompatibleWithShift M]
    {X' : C} (f : X ⟶ X') (hf : W f) (Y : C) :
    HasSmallLocalizedShiftedHom.{w} W M X Y ↔ HasSmallLocalizedShiftedHom.{w} W M X' Y :=
  forall_congr' (fun a => forall_congr' (fun b =>
    hasSmallLocalizedHom_iff_source W (f⟦a⟧') (W.shift hf a) (Y⟦b⟧)))

variable [HasSmallLocalizedShiftedHom.{w} W M X Y]

include M in
/--
lemma `hasSmallLocalizedHom_of_hasSmallLocalizedShiftedHom₀` / 引理 `hasSmallLocalizedHom_of_hasSmallLocalizedShiftedHom₀`

English:
lemma hasSmallLocalizedHom_of_hasSmallLocalizedShiftedHom₀
  proof: (hasSmallLocalizedHom_iff_of_isos W
    ((shiftFunctorZero C M).app X) ((shiftFunctorZero C M).app Y)).1 inferInstance

中文:
引理 hasSmallLocalizedHom_of_hasSmallLocalizedShiftedHom₀
  证明: (hasSmallLocalizedHom_iff_of_isos W
    ((shiftFunctorZero C M).app X) ((shiftFunctorZero C M).app Y)).1 inferInstance

Depends on / 依赖: hasSmallLocalizedHom_iff_of_isos, shiftFunctorZero
-/
lemma hasSmallLocalizedHom_of_hasSmallLocalizedShiftedHom₀ :
    HasSmallLocalizedHom.{w} W X Y :=
  (hasSmallLocalizedHom_iff_of_isos W
    ((shiftFunctorZero C M).app X) ((shiftFunctorZero C M).app Y)).1 inferInstance

variable {M}

instance (m : M) : HasSmallLocalizedHom.{w} W X (Y⟦m⟧) :=
  (hasSmallLocalizedHom_iff_of_isos W
    ((shiftFunctorZero C M).app X) (Iso.refl (Y⟦m⟧))).1 inferInstance

instance (m : M) : HasSmallLocalizedHom.{w} W (X⟦m⟧) Y :=
  (hasSmallLocalizedHom_iff_of_isos W
    (Iso.refl (X⟦m⟧)) ((shiftFunctorZero C M).app Y)).1 inferInstance

instance (m m' n : M) : HasSmallLocalizedHom.{w} W (X⟦m⟧⟦m'⟧) (Y⟦n⟧) :=
  (hasSmallLocalizedHom_iff_of_isos W
    ((shiftFunctorAdd C m m').app X) (Iso.refl (Y⟦n⟧))).1 inferInstance

instance (m n n' : M) : HasSmallLocalizedHom.{w} W (X⟦m⟧) (Y⟦n⟧⟦n'⟧) :=
  (hasSmallLocalizedHom_iff_of_isos W
    (Iso.refl (X⟦m⟧)) ((shiftFunctorAdd C n n').app Y)).1 inferInstance

end

namespace SmallHom

variable {W}
variable [W.IsCompatibleWithShift M] (L : C ⥤ D) [L.IsLocalization W] [L.CommShift M]
  {X Y : C} [HasSmallLocalizedHom.{w} W X Y]
  (f : SmallHom.{w} W X Y) (a : M) [HasSmallLocalizedHom.{w} W (X⟦a⟧) (Y⟦a⟧)]

/--
Definition of `shift` / `shift` 的定义

English:
definition shift
  signature: : SmallHom.{w} W (X⟦a⟧) (Y⟦a⟧)
  body: (W.shiftLocalizerMorphism a).smallHomMap f

中文:
定义 shift
  签名: : SmallHom.{w} W (X⟦a⟧) (Y⟦a⟧)
  定义体: (W.shiftLocalizerMorphism a).smallHomMap f

Depends on / 依赖: W.shiftLocalizerMorphism, shiftLocalizerMorphism, smallHomMap
-/
noncomputable def shift : SmallHom.{w} W (X⟦a⟧) (Y⟦a⟧) :=
  (W.shiftLocalizerMorphism a).smallHomMap f

/--
lemma `equiv_shift` / 引理 `equiv_shift`

English:
lemma equiv_shift
  statement: equiv W L (f.shift a) =
  proof: (W.shiftLocalizerMorphism a).equiv_smallHomMap _ _ _ (L.commShiftIso a) f

中文:
引理 equiv_shift
  结论: equiv W L (f.shift a) =
  证明: (W.shiftLocalizerMorphism a).equiv_smallHomMap _ _ _ (L.commShiftIso a) f

Depends on / 依赖: L.commShiftIso, W.shiftLocalizerMorphism, commShiftIso, equiv_smallHomMap, shiftLocalizerMorphism
-/
lemma equiv_shift : equiv W L (f.shift a) =
    (L.commShiftIso a).hom.app X ≫ (equiv W L f)⟦a⟧' ≫ (L.commShiftIso a).inv.app Y :=
  (W.shiftLocalizerMorphism a).equiv_smallHomMap _ _ _ (L.commShiftIso a) f

end SmallHom

/--
Definition of `SmallShiftedHom` / `SmallShiftedHom` 的定义

English:
definition SmallShiftedHom
  signature: (X Y : C) [HasSmallLocalizedShiftedHom.{w} W M X Y] (m : M)
  body: SmallHom W X (Y⟦m⟧)

中文:
定义 SmallShiftedHom
  签名: (X Y : C) [HasSmallLocalizedShiftedHom.{w} W M X Y] (m : M)
  定义体: SmallHom W X (Y⟦m⟧)

Depends on / 依赖: SmallHom
-/
def SmallShiftedHom (X Y : C) [HasSmallLocalizedShiftedHom.{w} W M X Y] (m : M) : Type w :=
  SmallHom W X (Y⟦m⟧)

namespace SmallShiftedHom

section

variable [W.IsCompatibleWithShift M] {X Y Z : C}

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: {m : M} [HasSmallLocalizedShiftedHom.{w} W M X Y] (f : ShiftedHom X Y m)
  body: SmallHom.mk _ f

中文:
定义 mk
  签名: {m : M} [HasSmallLocalizedShiftedHom.{w} W M X Y] (f : ShiftedHom X Y m)
  定义体: SmallHom.mk _ f

Depends on / 依赖: Category, SmallHom, SmallHom.mk, cat_disch, inv.app, shiftFunctor, shiftFunctorAdd, t.Category
-/
noncomputable def mk {m : M} [HasSmallLocalizedShiftedHom.{w} W M X Y] (f : ShiftedHom X Y m) :
    SmallShiftedHom.{w} W X Y m :=
  SmallHom.mk _ f

variable {W}

/--
Definition of `shift` / `shift` 的定义

English:
definition shift
  signature: {a : M} [HasSmallLocalizedShiftedHom.{w} W M X Y]
  body: (SmallHom.shift f n).comp (SmallHom.mk W ((shiftFunctorAdd' C a n a' h).inv.app Y))

中文:
定义 shift
  签名: {a : M} [HasSmallLocalizedShiftedHom.{w} W M X Y]
  定义体: (SmallHom.shift f n).comp (SmallHom.mk W ((shiftFunctorAdd' C a n a' h).inv.app Y))

Depends on / 依赖: SmallHom, SmallHom.mk, SmallHom.shift, inv.app, shiftFunctorAdd
-/
noncomputable def shift {a : M} [HasSmallLocalizedShiftedHom.{w} W M X Y]
    [HasSmallLocalizedShiftedHom.{w} W M Y Y]
    (f : SmallShiftedHom.{w} W X Y a) (n a' : M) (h : a + n = a') :
    SmallHom.{w} W (X⟦n⟧) (Y⟦a'⟧) :=
  (SmallHom.shift f n).comp (SmallHom.mk W ((shiftFunctorAdd' C a n a' h).inv.app Y))

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: {a b c : M} [HasSmallLocalizedShiftedHom.{w} W M X Y]
  body: SmallHom.comp f (g.shift a c h)

中文:
定义 comp
  签名: {a b c : M} [HasSmallLocalizedShiftedHom.{w} W M X Y]
  定义体: SmallHom.comp f (g.shift a c h)

Depends on / 依赖: SmallHom, SmallHom.comp, g.shift
-/
noncomputable def comp {a b c : M} [HasSmallLocalizedShiftedHom.{w} W M X Y]
    [HasSmallLocalizedShiftedHom.{w} W M Y Z] [HasSmallLocalizedShiftedHom.{w} W M X Z]
    [HasSmallLocalizedShiftedHom.{w} W M Z Z]
    (f : SmallShiftedHom.{w} W X Y a) (g : SmallShiftedHom.{w} W Y Z b) (h : b + a = c) :
    SmallShiftedHom.{w} W X Z c :=
  SmallHom.comp f (g.shift a c h)

variable (W) in
/--
Definition of `mk₀` / `mk₀` 的定义

English:
definition mk₀
  signature: [HasSmallLocalizedShiftedHom.{w} W M X Y]
  body: SmallShiftedHom.mk _ (ShiftedHom.mk₀ _ hm₀ f)

中文:
定义 mk₀
  签名: [HasSmallLocalizedShiftedHom.{w} W M X Y]
  定义体: SmallShiftedHom.mk _ (ShiftedHom.mk₀ _ hm₀ f)

Depends on / 依赖: ShiftedHom, ShiftedHom.mk, SmallShiftedHom, SmallShiftedHom.mk
-/
noncomputable def mk₀ [HasSmallLocalizedShiftedHom.{w} W M X Y]
    (m₀ : M) (hm₀ : m₀ = 0) (f : X ⟶ Y) :
    SmallShiftedHom.{w} W X Y m₀ :=
  SmallShiftedHom.mk _ (ShiftedHom.mk₀ _ hm₀ f)

/--
Definition of `mk₀Inv` / `mk₀Inv` 的定义

English:
definition mk₀Inv
  signature: [HasSmallLocalizedShiftedHom.{w} W M Y X] [W.RespectsIso]
  body: SmallHom.mkInv ((shiftFunctorZero' C m₀ hm₀).hom.app X ≫ f)
    (MorphismProperty.RespectsIso.precomp _ _ _ hf)

中文:
定义 mk₀Inv
  签名: [HasSmallLocalizedShiftedHom.{w} W M Y X] [W.RespectsIso]
  定义体: SmallHom.mkInv ((shiftFunctorZero' C m₀ hm₀).hom.app X ≫ f)
    (MorphismProperty.RespectsIso.precomp _ _ _ hf)

Depends on / 依赖: MorphismProperty, MorphismProperty.RespectsIso.precomp, RespectsIso, SmallHom, SmallHom.mkInv, hom.app, precomp, shiftFunctorZero
-/
noncomputable def mk₀Inv [HasSmallLocalizedShiftedHom.{w} W M Y X] [W.RespectsIso]
    (m₀ : M) (hm₀ : m₀ = 0) (f : X ⟶ Y) (hf : W f) :
    SmallShiftedHom.{w} W Y X m₀ :=
  SmallHom.mkInv ((shiftFunctorZero' C m₀ hm₀).hom.app X ≫ f)
    (MorphismProperty.RespectsIso.precomp _ _ _ hf)

end

section

variable (L : C ⥤ D) [L.IsLocalization W] [L.CommShift M]
  {X Y Z T : C}

/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: [HasSmallLocalizedShiftedHom.{w} W M X Y] {m : M}
  body: (SmallHom.equiv W L).trans ((L.commShiftIso m).app Y).homToEquiv

中文:
定义 equiv
  签名: [HasSmallLocalizedShiftedHom.{w} W M X Y] {m : M}
  定义体: (SmallHom.equiv W L).trans ((L.commShiftIso m).app Y).homToEquiv

Depends on / 依赖: L.commShiftIso, SmallHom, SmallHom.equiv, commShiftIso, homToEquiv
-/
noncomputable def equiv [HasSmallLocalizedShiftedHom.{w} W M X Y] {m : M} :
    SmallShiftedHom.{w} W X Y m ≃ ShiftedHom (L.obj X) (L.obj Y) m :=
  (SmallHom.equiv W L).trans ((L.commShiftIso m).app Y).homToEquiv

/--
lemma `equiv_apply` / 引理 `equiv_apply`

English:
lemma equiv_apply
  statement: [HasSmallLocalizedShiftedHom.{w} W M X Y] {m : M}
  proof: rfl

中文:
引理 equiv_apply
  结论: [HasSmallLocalizedShiftedHom.{w} W M X Y] {m : M}
  证明: rfl
-/
lemma equiv_apply [HasSmallLocalizedShiftedHom.{w} W M X Y] {m : M}
    (f : SmallShiftedHom.{w} W X Y m) :
    equiv W L f = (SmallHom.equiv W L) f ≫ ((L.commShiftIso m).app Y).hom :=
  rfl

section
variable [W.IsCompatibleWithShift M]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `equiv_shift'` / 引理 `equiv_shift'`

English:
lemma equiv_shift'
  statement: {a : M} [HasSmallLocalizedShiftedHom.{w} W M X Y]
  proof: by
  simp only [shift, SmallHom.equiv_comp, SmallHom.equiv_shift, SmallHom.equiv_mk, assoc,
    L.commShiftIso_add' h, Functor.CommShift.isoAdd'_inv_app, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app, Functor.comp_obj, comp_id]

中文:
引理 equiv_shift'
  结论: {a : M} [HasSmallLocalizedShiftedHom.{w} W M X Y]
  证明: by
  simp only [shift, SmallHom.equiv_comp, SmallHom.equiv_shift, SmallHom.equiv_mk, assoc,
    L.commShiftIso_add' h, Functor.CommShift.isoAdd'_inv_app, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app, Functor.comp_obj, comp_id]

Depends on / 依赖: CommShift, Functor, Functor.CommShift.isoAdd, Functor.comp_obj, Functor.map_comp_assoc, Iso.hom_inv_id_app, Iso.inv_hom_id_app_assoc, L.commShiftIso_add, SmallHom, SmallHom.equiv_comp, SmallHom.equiv_mk, SmallHom.equiv_shift, _inv_app, commShiftIso_add, comp_id, comp_obj, equiv_comp, equiv_mk, equiv_shift, hom_inv_id_app
-/
lemma equiv_shift' {a : M} [HasSmallLocalizedShiftedHom.{w} W M X Y]
    [HasSmallLocalizedShiftedHom.{w} W M Y Y]
    (f : SmallShiftedHom.{w} W X Y a) (n a' : M) (h : a + n = a') :
    SmallHom.equiv W L (f.shift n a' h) = (L.commShiftIso n).hom.app X ≫
      (SmallHom.equiv W L f)⟦n⟧' ≫ ((L.commShiftIso a).hom.app Y)⟦n⟧' ≫
        (shiftFunctorAdd' D a n a' h).inv.app (L.obj Y) ≫ (L.commShiftIso a').inv.app Y := by
  simp only [shift, SmallHom.equiv_comp, SmallHom.equiv_shift, SmallHom.equiv_mk, assoc,
    L.commShiftIso_add' h, Functor.CommShift.isoAdd'_inv_app, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app, Functor.comp_obj, comp_id]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `equiv_shift` / 引理 `equiv_shift`

English:
lemma equiv_shift
  statement: {a : M} [HasSmallLocalizedShiftedHom.{w} W M X Y]
  proof: by
  dsimp [equiv]
  erw [equiv_shift']
  simp only [Functor.comp_obj, assoc, Iso.inv_hom_id_app, comp_id, Functor.map_comp]
  rfl

中文:
引理 equiv_shift
  结论: {a : M} [HasSmallLocalizedShiftedHom.{w} W M X Y]
  证明: by
  dsimp [equiv]
  erw [equiv_shift']
  simp only [Functor.comp_obj, assoc, Iso.inv_hom_id_app, comp_id, Functor.map_comp]
  rfl

Depends on / 依赖: Functor, Functor.comp_obj, Functor.map_comp, Iso.inv_hom_id_app, comp_id, comp_obj, equiv_shift, injection, inv_hom_id_app, map_comp
-/
lemma equiv_shift {a : M} [HasSmallLocalizedShiftedHom.{w} W M X Y]
    [HasSmallLocalizedShiftedHom.{w} W M Y Y]
    (f : SmallShiftedHom.{w} W X Y a) (n a' : M) (h : a + n = a') :
    equiv W L (f.shift n a' h) = (L.commShiftIso n).hom.app X ≫ (equiv W L f)⟦n⟧' ≫
      (shiftFunctorAdd' D a n a' h).inv.app (L.obj Y) := by
  dsimp [equiv]
  erw [equiv_shift']
  simp only [Functor.comp_obj, assoc, Iso.inv_hom_id_app, comp_id, Functor.map_comp]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `equiv_comp` / 引理 `equiv_comp`

English:
lemma equiv_comp
  statement: [HasSmallLocalizedShiftedHom.{w} W M X Y]
  proof: by
  dsimp [comp, equiv, ShiftedHom.comp]
  erw [SmallHom.equiv_comp]
  simp only [equiv_shift', Functor.comp_obj, assoc, Iso.inv_hom_id_app,
    comp_id, Functor.map_comp]
  rfl

中文:
引理 equiv_comp
  结论: [HasSmallLocalizedShiftedHom.{w} W M X Y]
  证明: by
  dsimp [comp, equiv, ShiftedHom.comp]
  erw [SmallHom.equiv_comp]
  simp only [equiv_shift', Functor.comp_obj, assoc, Iso.inv_hom_id_app,
    comp_id, Functor.map_comp]
  rfl

Depends on / 依赖: Functor, Functor.comp_obj, Functor.map_comp, Iso.inv_hom_id_app, ShiftedHom, ShiftedHom.comp, SmallHom, SmallHom.equiv_comp, comp_id, comp_obj, equiv_comp, equiv_shift, inv_hom_id_app, map_comp
-/
lemma equiv_comp [HasSmallLocalizedShiftedHom.{w} W M X Y]
    [HasSmallLocalizedShiftedHom.{w} W M Y Z] [HasSmallLocalizedShiftedHom.{w} W M X Z]
    [HasSmallLocalizedShiftedHom.{w} W M Z Z] {a b c : M}
    (f : SmallShiftedHom.{w} W X Y a) (g : SmallShiftedHom.{w} W Y Z b) (h : b + a = c) :
    equiv W L (f.comp g h) = (equiv W L f).comp (equiv W L g) h := by
  dsimp [comp, equiv, ShiftedHom.comp]
  erw [SmallHom.equiv_comp]
  simp only [equiv_shift', Functor.comp_obj, assoc, Iso.inv_hom_id_app,
    comp_id, Functor.map_comp]
  rfl

end

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `equiv_mk` / 引理 `equiv_mk`

English:
lemma equiv_mk
  given: [HasSmallLocalizedShiftedHom.{w} W M X Y] {m : M} (f : ShiftedHom X Y m)
  proof: ((L.commShiftIso m).app Y).homToEquiv.symm.injective
    ((Equiv.symm_apply_apply ..).trans (by simp [ShiftedHom.map, mk]))

中文:
引理 equiv_mk
  条件: [HasSmallLocalizedShiftedHom.{w} W M X Y] {m : M} (f : ShiftedHom X Y m)
  证明: ((L.commShiftIso m).app Y).homToEquiv.symm.injective
    ((Equiv.symm_apply_apply ..).trans (by simp [ShiftedHom.map, mk]))

Depends on / 依赖: Equiv.symm_apply_apply, L.commShiftIso, ShiftedHom, ShiftedHom.map, commShiftIso, homToEquiv, homToEquiv.symm.injective, injective, symm_apply_apply
-/
lemma equiv_mk [HasSmallLocalizedShiftedHom.{w} W M X Y] {m : M} (f : ShiftedHom X Y m) :
    equiv W L (.mk _ f) = f.map L :=
  ((L.commShiftIso m).app Y).homToEquiv.symm.injective
    ((Equiv.symm_apply_apply ..).trans (by simp [ShiftedHom.map, mk]))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `equiv_mk₀` / 引理 `equiv_mk₀`

English:
lemma equiv_mk₀
  statement: [HasSmallLocalizedShiftedHom.{w} W M X Y]
  proof: by
  subst hm₀
  dsimp [equiv, mk₀]
  erw [SmallHom.equiv_mk, Functor.map_comp]
  dsimp [equiv, mk₀, ShiftedHom.mk₀, shiftFunctorZero']
  simp only [comp_id, L.commShiftIso_zero, Functor.CommShift.isoZero_hom_app, assoc,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.id_obj, Functor.map_id, id_comp]

中文:
引理 equiv_mk₀
  结论: [HasSmallLocalizedShiftedHom.{w} W M X Y]
  证明: by
  subst hm₀
  dsimp [equiv, mk₀]
  erw [SmallHom.equiv_mk, Functor.map_comp]
  dsimp [equiv, mk₀, ShiftedHom.mk₀, shiftFunctorZero']
  simp only [comp_id, L.commShiftIso_zero, Functor.CommShift.isoZero_hom_app, assoc,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.id_obj, Functor.map_id, id_comp]

Depends on / 依赖: CommShift, Functor, Functor.CommShift.isoZero_hom_app, Functor.id_obj, Functor.map_comp, Functor.map_comp_assoc, Functor.map_id, Iso.inv_hom_id_app, L.commShiftIso_zero, ShiftedHom, ShiftedHom.mk, SmallHom, SmallHom.equiv_mk, commShiftIso_zero, comp_id, equiv_mk, id_comp, id_obj, inv_hom_id_app, isoZero_hom_app
-/
lemma equiv_mk₀ [HasSmallLocalizedShiftedHom.{w} W M X Y]
    (m₀ : M) (hm₀ : m₀ = 0) (f : X ⟶ Y) :
    equiv W L (SmallShiftedHom.mk₀ W m₀ hm₀ f) =
      ShiftedHom.mk₀ m₀ hm₀ (L.map f) := by
  subst hm₀
  dsimp [equiv, mk₀]
  erw [SmallHom.equiv_mk, Functor.map_comp]
  dsimp [equiv, mk₀, ShiftedHom.mk₀, shiftFunctorZero']
  simp only [comp_id, L.commShiftIso_zero, Functor.CommShift.isoZero_hom_app, assoc,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.id_obj, Functor.map_id, id_comp]

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `equiv_mk₀Inv` / 引理 `equiv_mk₀Inv`

English:
lemma equiv_mk₀Inv
  statement: [HasSmallLocalizedShiftedHom.{w} W M Y X] [W.RespectsIso]
  proof: by
  have hf' : W ((shiftFunctorZero' C m₀ hm₀).hom.app X ≫ f) :=
    MorphismProperty.RespectsIso.precomp _ _ _ hf
  refine (SmallHom.equiv_mkInv L _ hf' =≫ _).trans ?_
  rw [← cancel_epi (isoOfHom L W _ hf').hom]; rw [Iso.hom_inv_id_assoc]
  simp [ShiftedHom.mk₀, Functor.commShiftIso_zero' _ _ m₀ hm₀]

中文:
引理 equiv_mk₀Inv
  结论: [HasSmallLocalizedShiftedHom.{w} W M Y X] [W.RespectsIso]
  证明: by
  have hf' : W ((shiftFunctorZero' C m₀ hm₀).hom.app X ≫ f) :=
    MorphismProperty.RespectsIso.precomp _ _ _ hf
  refine (SmallHom.equiv_mkInv L _ hf' =≫ _).trans ?_
  rw [← cancel_epi (isoOfHom L W _ hf').hom]; rw [Iso.hom_inv_id_assoc]
  simp [ShiftedHom.mk₀, Functor.commShiftIso_zero' _ _ m₀ hm₀]

Depends on / 依赖: Functor, Functor.commShiftIso_zero, Iso.hom_inv_id_assoc, MorphismProperty, MorphismProperty.RespectsIso.precomp, RespectsIso, ShiftedHom, ShiftedHom.mk, SmallHom, SmallHom.equiv_mkInv, cancel_epi, commShiftIso_zero, equiv_mkInv, hom.app, hom_inv_id_assoc, isoOfHom, precomp, shiftFunctorZero
-/
lemma equiv_mk₀Inv [HasSmallLocalizedShiftedHom.{w} W M Y X] [W.RespectsIso]
    (m₀ : M) (hm₀ : m₀ = 0) (f : X ⟶ Y) (hf : W f) :
    equiv W L (mk₀Inv m₀ hm₀ f hf) =
      ShiftedHom.mk₀ m₀ hm₀ ((isoOfHom L W f hf).inv) := by
  have hf' : W ((shiftFunctorZero' C m₀ hm₀).hom.app X ≫ f) :=
    MorphismProperty.RespectsIso.precomp _ _ _ hf
  refine (SmallHom.equiv_mkInv L _ hf' =≫ _).trans ?_
  rw [← cancel_epi (isoOfHom L W _ hf').hom]; rw [Iso.hom_inv_id_assoc]
  simp [ShiftedHom.mk₀, Functor.commShiftIso_zero' _ _ m₀ hm₀]

end

section

variable [W.IsCompatibleWithShift M]

/--
lemma `comp_assoc` / 引理 `comp_assoc`

English:
lemma comp_assoc
  statement: {X Y Z T : C} {a₁ a₂ a₃ a₁₂ a₂₃ a : M}
  proof: by
  apply (equiv W W.Q).injective
  simp only [equiv_comp, ShiftedHom.comp_assoc _ _ _ h₁₂ h₂₃ h]

中文:
引理 comp_assoc
  结论: {X Y Z T : C} {a₁ a₂ a₃ a₁₂ a₂₃ a : M}
  证明: by
  apply (equiv W W.Q).injective
  simp only [equiv_comp, ShiftedHom.comp_assoc _ _ _ h₁₂ h₂₃ h]

Depends on / 依赖: ShiftedHom, ShiftedHom.comp_assoc, comp_assoc, equiv_comp, injective
-/
lemma comp_assoc {X Y Z T : C} {a₁ a₂ a₃ a₁₂ a₂₃ a : M}
    [HasSmallLocalizedShiftedHom.{w} W M X Y] [HasSmallLocalizedShiftedHom.{w} W M X Z]
    [HasSmallLocalizedShiftedHom.{w} W M X T] [HasSmallLocalizedShiftedHom.{w} W M Y Z]
    [HasSmallLocalizedShiftedHom.{w} W M Y T] [HasSmallLocalizedShiftedHom.{w} W M Z T]
    [HasSmallLocalizedShiftedHom.{w} W M Z Z] [HasSmallLocalizedShiftedHom.{w} W M T T]
    (α : SmallShiftedHom.{w} W X Y a₁) (β : SmallShiftedHom.{w} W Y Z a₂)
    (γ : SmallShiftedHom.{w} W Z T a₃)
    (h₁₂ : a₂ + a₁ = a₁₂) (h₂₃ : a₃ + a₂ = a₂₃) (h : a₃ + a₂ + a₁ = a) :
    (α.comp β h₁₂).comp γ (show a₃ + a₁₂ = a by rw [← h₁₂, ← add_assoc, h]) =
      α.comp (β.comp γ h₂₃) (by rw [← h₂₃, h]) := by
  apply (equiv W W.Q).injective
  simp only [equiv_comp, ShiftedHom.comp_assoc _ _ _ h₁₂ h₂₃ h]

end

variable {W} in
@[simp]
/--
lemma `mk₀_comp_mk₀Inv` / 引理 `mk₀_comp_mk₀Inv`

English:
lemma mk₀_comp_mk₀Inv
  statement: {X Y : C} [HasSmallLocalizedShiftedHom.{w} W M X Y]
  proof: (equiv W W.Q).injective (by simp [equiv_comp])

中文:
引理 mk₀_comp_mk₀Inv
  结论: {X Y : C} [HasSmallLocalizedShiftedHom.{w} W M X Y]
  证明: (equiv W W.Q).injective (by simp [equiv_comp])

Depends on / 依赖: equiv_comp, injective
-/
lemma mk₀_comp_mk₀Inv {X Y : C} [HasSmallLocalizedShiftedHom.{w} W M X Y]
    [HasSmallLocalizedShiftedHom.{w} W M Y Y]
    [HasSmallLocalizedShiftedHom.{w} W M Y X] [W.IsCompatibleWithShift M] [W.RespectsIso]
    (m₀ : M) (hm₀ : m₀ = 0) (f : Y ⟶ X) (hf : W f) :
    (mk₀ W m₀ hm₀ f).comp (mk₀Inv m₀ hm₀ f hf) (by subst hm₀; simp) =
      mk₀ W m₀ hm₀ (𝟙 Y) :=
  (equiv W W.Q).injective (by simp [equiv_comp])

variable {W} in
@[simp]
/--
lemma `mk₀Inv_comp_mk₀` / 引理 `mk₀Inv_comp_mk₀`

English:
lemma mk₀Inv_comp_mk₀
  statement: {X Y : C} [HasSmallLocalizedShiftedHom.{w} W M X Y]
  proof: (equiv W W.Q).injective (by simp [equiv_comp])

中文:
引理 mk₀Inv_comp_mk₀
  结论: {X Y : C} [HasSmallLocalizedShiftedHom.{w} W M X Y]
  证明: (equiv W W.Q).injective (by simp [equiv_comp])

Depends on / 依赖: equiv_comp, injective
-/
lemma mk₀Inv_comp_mk₀ {X Y : C} [HasSmallLocalizedShiftedHom.{w} W M X Y]
    [HasSmallLocalizedShiftedHom.{w} W M X X]
    [HasSmallLocalizedShiftedHom.{w} W M Y X] [W.IsCompatibleWithShift M] [W.RespectsIso]
    (m₀ : M) (hm₀ : m₀ = 0) (f : Y ⟶ X) (hf : W f) :
    (mk₀Inv m₀ hm₀ f hf).comp (mk₀ W m₀ hm₀ f) (by subst hm₀; simp) =
      mk₀ W m₀ hm₀ (𝟙 X) :=
  (equiv W W.Q).injective (by simp [equiv_comp])

variable {W} in
@[simp]
/--
lemma `comp_mk₀_id` / 引理 `comp_mk₀_id`

English:
lemma comp_mk₀_id
  statement: {X Y : C} [HasSmallLocalizedShiftedHom.{w} W M X Y]
  proof: (equiv W W.Q).injective (by simp [equiv_comp])

中文:
引理 comp_mk₀_id
  结论: {X Y : C} [HasSmallLocalizedShiftedHom.{w} W M X Y]
  证明: (equiv W W.Q).injective (by simp [equiv_comp])

Depends on / 依赖: equiv_comp, injective
-/
lemma comp_mk₀_id {X Y : C} [HasSmallLocalizedShiftedHom.{w} W M X Y]
    [HasSmallLocalizedShiftedHom.{w} W M Y Y]
    [W.IsCompatibleWithShift M] {m : M}
    (α : SmallShiftedHom.{w} W X Y m) (m₀ : M) (hm₀ : m₀ = 0) :
    α.comp (mk₀ W m₀ hm₀ (𝟙 Y)) (by simp_all) = α :=
  (equiv W W.Q).injective (by simp [equiv_comp])

variable {W} in
@[simp]
/--
lemma `mk₀_id_comp` / 引理 `mk₀_id_comp`

English:
lemma mk₀_id_comp
  statement: {X Y : C} [HasSmallLocalizedShiftedHom.{w} W M X Y]
  proof: (equiv W W.Q).injective (by simp [equiv_comp])

中文:
引理 mk₀_id_comp
  结论: {X Y : C} [HasSmallLocalizedShiftedHom.{w} W M X Y]
  证明: (equiv W W.Q).injective (by simp [equiv_comp])

Depends on / 依赖: equiv_comp, injective
-/
lemma mk₀_id_comp {X Y : C} [HasSmallLocalizedShiftedHom.{w} W M X Y]
    [HasSmallLocalizedShiftedHom.{w} W M X X]
    [HasSmallLocalizedShiftedHom.{w} W M Y Y]
    [W.IsCompatibleWithShift M] {m : M}
    (α : SmallShiftedHom.{w} W X Y m) (m₀ : M) (hm₀ : m₀ = 0) :
    (mk₀ W m₀ hm₀ (𝟙 X)).comp α (by simp_all) = α :=
  (equiv W W.Q).injective (by simp [equiv_comp])

variable {W} in
/-- The postcomposition on the types `SmallShiftedHom W` with a morphism
which satisfies `W` is a bijection. -/
@[simps!]
/--
Definition of `postcompEquiv` / `postcompEquiv` 的定义

English:
definition postcompEquiv
  signature: {X Y Z : C}
  body: α.comp (mk₀ _ _ rfl f) (zero_add _)
  invFun β := β.comp (mk₀Inv _ rfl _ hf) (zero_add _)
  left_inv α := by simp [comp_assoc]
  right_inv β := by simp [comp_assoc]

中文:
定义 postcompEquiv
  签名: {X Y Z : C}
  定义体: α.comp (mk₀ _ _ rfl f) (zero_add _)
  invFun β := β.comp (mk₀Inv _ rfl _ hf) (zero_add _)
  left_inv α := by simp [comp_assoc]
  right_inv β := by simp [comp_assoc]

Depends on / 依赖: zero_add
-/
noncomputable def postcompEquiv {X Y Z : C}
    [W.RespectsIso] [W.IsCompatibleWithShift M]
    [HasSmallLocalizedShiftedHom.{w} W M X Y]
    [HasSmallLocalizedShiftedHom.{w} W M Y Z]
    [HasSmallLocalizedShiftedHom.{w} W M X Z]
    [HasSmallLocalizedShiftedHom.{w} W M Z Y]
    [HasSmallLocalizedShiftedHom.{w} W M Y Y]
    [HasSmallLocalizedShiftedHom.{w} W M Z Z]
    (f : Y ⟶ Z) (hf : W f) {a : M} :
    SmallShiftedHom.{w} W X Y a ≃ SmallShiftedHom.{w} W X Z a where
  toFun α := α.comp (mk₀ _ _ rfl f) (zero_add _)
  invFun β := β.comp (mk₀Inv _ rfl _ hf) (zero_add _)
  left_inv α := by simp [comp_assoc]
  right_inv β := by simp [comp_assoc]

variable {W} in
/-- The precomposition on the types `SmallShiftedHom W` with a morphism
which satisfies `W` is a bijection. -/
@[simps!]
/--
Definition of `precompEquiv` / `precompEquiv` 的定义

English:
definition precompEquiv
  signature: {X Y Z : C}
  body: (mk₀ _ _ rfl f).comp α (add_zero _)
  invFun β := (mk₀Inv _ rfl _ hf).comp β (add_zero _)
  left_inv α := by simp [← comp_assoc]
  right_inv β := by simp [← comp_assoc]

中文:
定义 precompEquiv
  签名: {X Y Z : C}
  定义体: (mk₀ _ _ rfl f).comp α (add_zero _)
  invFun β := (mk₀Inv _ rfl _ hf).comp β (add_zero _)
  left_inv α := by simp [← comp_assoc]
  right_inv β := by simp [← comp_assoc]

Depends on / 依赖: add_zero
-/
noncomputable def precompEquiv {X Y Z : C}
    [W.RespectsIso] [W.IsCompatibleWithShift M]
    [HasSmallLocalizedShiftedHom.{w} W M X X]
    [HasSmallLocalizedShiftedHom.{w} W M Y Y]
    [HasSmallLocalizedShiftedHom.{w} W M X Y]
    [HasSmallLocalizedShiftedHom.{w} W M Y X]
    [HasSmallLocalizedShiftedHom.{w} W M Y Z]
    [HasSmallLocalizedShiftedHom.{w} W M X Z]
    [HasSmallLocalizedShiftedHom.{w} W M Z Z]
    (f : X ⟶ Y) (hf : W f) {a : M} :
    SmallShiftedHom.{w} W Y Z a ≃ SmallShiftedHom.{w} W X Z a where
  toFun α := (mk₀ _ _ rfl f).comp α (add_zero _)
  invFun β := (mk₀Inv _ rfl _ hf).comp β (add_zero _)
  left_inv α := by simp [← comp_assoc]
  right_inv β := by simp [← comp_assoc]

section ChangeOfUniverse

variable {W}

/--
Definition of `chgUniv` / `chgUniv` 的定义

English:
definition chgUniv
  signature: {X Y : C} {m : M}
  body: SmallHom.chgUniv

中文:
定义 chgUniv
  签名: {X Y : C} {m : M}
  定义体: SmallHom.chgUniv

Depends on / 依赖: SmallHom, SmallHom.chgUniv, chgUniv
-/
noncomputable def chgUniv {X Y : C} {m : M}
    [HasSmallLocalizedShiftedHom.{w} W M X Y]
    [HasSmallLocalizedShiftedHom.{w''} W M X Y] :
    SmallShiftedHom.{w} W X Y m ≃ SmallShiftedHom.{w''} W X Y m :=
  SmallHom.chgUniv

set_option backward.isDefEq.respectTransparency false in
/--
lemma `equiv_chgUniv` / 引理 `equiv_chgUniv`

English:
lemma equiv_chgUniv
  statement: (L : C ⥤ D) [L.IsLocalization W] [L.CommShift M] {X Y : C} {m : M}
  proof: by
  dsimp [equiv]
  congr
  apply SmallHom.equiv_chgUniv

中文:
引理 equiv_chgUniv
  结论: (L : C ⥤ D) [L.是Localization W] [L.交换Shift M] {X Y : C} {m : M}
  证明: by
  dsimp [equiv]
  congr
  apply SmallHom.equiv_chgUniv

Depends on / 依赖: SmallHom, SmallHom.equiv_chgUniv, equiv_chgUniv
-/
lemma equiv_chgUniv (L : C ⥤ D) [L.IsLocalization W] [L.CommShift M] {X Y : C} {m : M}
    [HasSmallLocalizedShiftedHom.{w} W M X Y]
    [HasSmallLocalizedShiftedHom.{w''} W M X Y]
    (e : SmallShiftedHom.{w} W X Y m) :
    equiv W L (chgUniv.{w''} e) = equiv W L e := by
  dsimp [equiv]
  congr
  apply SmallHom.equiv_chgUniv

end ChangeOfUniverse

end SmallShiftedHom

end Localization

namespace LocalizerMorphism

open Localization

variable {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
  {D₁ : Type u₁'} [Category.{v₁'} D₁] {D₂ : Type u₂'} [Category.{v₂'} D₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}
  (Φ : LocalizerMorphism W₁ W₂)
  (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂) [L₁.IsLocalization W₁] [L₂.IsLocalization W₂]
  {M : Type w'} [AddMonoid M] [HasShift C₁ M] [HasShift C₂ M]
  [HasShift D₁ M] [HasShift D₂ M] [L₁.CommShift M] [L₂.CommShift M]
  [Φ.functor.CommShift M]
  {X₁ Y₁ Z₁ : C₁} {X₂ Y₂ Z₂ : C₂}
  [HasSmallLocalizedShiftedHom.{w} W₁ M X₁ Y₁] [HasSmallLocalizedShiftedHom.{w''} W₂ M X₂ X₂]
  [HasSmallLocalizedShiftedHom.{w''} W₂ M X₂ Y₂] [HasSmallLocalizedShiftedHom.{w''} W₂ M Y₂ Y₂]
  (eX : Φ.functor.obj X₁ ≅ X₂) (eY : Φ.functor.obj Y₁ ≅ Y₂)
  (eZ : Φ.functor.obj Z₁ ≅ Z₂)

/--
Definition of `smallShiftedHomMap` / `smallShiftedHomMap` 的定义

English:
definition smallShiftedHomMap
  signature: {m : M} (f : SmallShiftedHom.{w} W₁ X₁ Y₁ m)
  body: have := hasSmallLocalizedHom_of_hasSmallLocalizedShiftedHom₀.{w''} W₂ M X₂ X₂
  Φ.smallHomMap' eX ((Φ.functor.commShiftIso m).app Y₁ ≪≫ (shiftFunctor _ _).mapIso eY) f

中文:
定义 smallShiftedHomMap
  签名: {m : M} (f : SmallShiftedHom.{w} W₁ X₁ Y₁ m)
  定义体: have := hasSmallLocalizedHom_of_hasSmallLocalizedShiftedHom₀.{w''} W₂ M X₂ X₂
  Φ.smallHomMap' eX ((Φ.functor.commShiftIso m).app Y₁ ≪≫ (shiftFunctor _ _).mapIso eY) f

Depends on / 依赖: commShiftIso, functor, functor.commShiftIso, mapIso, shiftFunctor, smallHomMap
-/
noncomputable def smallShiftedHomMap {m : M} (f : SmallShiftedHom.{w} W₁ X₁ Y₁ m) :
      SmallShiftedHom.{w''} W₂ X₂ Y₂ m :=
  have := hasSmallLocalizedHom_of_hasSmallLocalizedShiftedHom₀.{w''} W₂ M X₂ X₂
  Φ.smallHomMap' eX ((Φ.functor.commShiftIso m).app Y₁ ≪≫ (shiftFunctor _ _).mapIso eY) f

set_option backward.defeqAttrib.useBackward true in
/--
lemma `equiv_smallShiftedHomMap` / 引理 `equiv_smallShiftedHomMap`

English:
lemma equiv_smallShiftedHomMap
  statement: (G : D₁ ⥤ D₂) [G.CommShift M]
  proof: by
  have := hasSmallLocalizedHom_of_hasSmallLocalizedShiftedHom₀.{w''} W₂ M X₂ X₂
  apply ((L₂.commShiftIso m).app Y₂).homToEquiv.symm.injective
  simp only [Functor.comp_obj, SmallShiftedHom.equiv_apply, Iso.app_hom,
    Iso.homToEquiv_symm_apply, Iso.app_inv, assoc, Iso.hom_inv_id_app, comp_id]
  refine (Φ.equiv_smallHomMap' L₁ L₂ _ _ G e f).trans ?_
  simp only [Functor.comp_obj, NatTrans.app_shift,
    Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_inv_app, assoc,
    Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp, ShiftedHom.map,
    ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp,
    Functor.commShiftIso_inv_naturality]
  nth_rw 2 [← Functor.map_comp_assoc]
  simp

中文:
引理 equiv_smallShiftedHomMap
  结论: (G : D₁ ⥤ D₂) [G.交换Shift M]
  证明: by
  have := hasSmallLocalizedHom_of_hasSmallLocalizedShiftedHom₀.{w''} W₂ M X₂ X₂
  apply ((L₂.commShiftIso m).app Y₂).homToEquiv.symm.injective
  simp only [Functor.comp_obj, SmallShiftedHom.equiv_apply, Iso.app_hom,
    Iso.homToEquiv_symm_apply, Iso.app_inv, assoc, Iso.hom_inv_id_app, comp_id]
  refine (Φ.equiv_smallHomMap' L₁ L₂ _ _ G e f).trans ?_
  simp only [Functor.comp_obj, NatTrans.app_shift,
    Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_inv_app, assoc,
    Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp, ShiftedHom.map,
    ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp,
    Functor.commShiftIso_inv_naturality]
  nth_rw 2 [← Functor.map_comp_assoc]
  simp

Depends on / 依赖: Functor, Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_inv_app, Functor.comp_obj, Iso.app_hom, Iso.app_inv, Iso.homToEquiv_symm_apply, Iso.hom_inv_id_app, Iso.trans_hom, NatTrans, NatTrans.app_shift, SmallShiftedHom, SmallShiftedHom.equiv_apply, app_hom, app_inv, app_shift, commShiftIso, commShiftIso_comp_hom_app, commShiftIso_comp_inv_app, comp_id
-/
lemma equiv_smallShiftedHomMap (G : D₁ ⥤ D₂) [G.CommShift M]
    (e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ G) [NatTrans.CommShift e.hom M]
    {m : M} (f : SmallShiftedHom.{w} W₁ X₁ Y₁ m) :
    SmallShiftedHom.equiv W₂ L₂ (Φ.smallShiftedHomMap eX eY f) =
      (ShiftedHom.mk₀ 0 rfl (L₂.map eX.inv ≫ e.hom.app _)).comp
        (((SmallShiftedHom.equiv W₁ L₁ f).map G).comp
          ((ShiftedHom.mk₀ 0 rfl (e.inv.app _ ≫ L₂.map eY.hom)))
          (zero_add m)) (add_zero m) := by
  have := hasSmallLocalizedHom_of_hasSmallLocalizedShiftedHom₀.{w''} W₂ M X₂ X₂
  apply ((L₂.commShiftIso m).app Y₂).homToEquiv.symm.injective
  simp only [Functor.comp_obj, SmallShiftedHom.equiv_apply, Iso.app_hom,
    Iso.homToEquiv_symm_apply, Iso.app_inv, assoc, Iso.hom_inv_id_app, comp_id]
  refine (Φ.equiv_smallHomMap' L₁ L₂ _ _ G e f).trans ?_
  simp only [Functor.comp_obj, NatTrans.app_shift,
    Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_inv_app, assoc,
    Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp, ShiftedHom.map,
    ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp,
    Functor.commShiftIso_inv_naturality]
  nth_rw 2 [← Functor.map_comp_assoc]
  simp

variable [W₁.IsCompatibleWithShift M] [W₂.IsCompatibleWithShift M]

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `smallShiftedHomMap_mk` / 引理 `smallShiftedHomMap_mk`

English:
lemma smallShiftedHomMap_mk
  given: {m : M} (f : ShiftedHom X₁ Y₁ m)
  proof: by
  apply (SmallShiftedHom.equiv W₂ W₂.Q).injective
  let e := CatCommSq.iso Φ.functor W₁.Q W₂.Q (Φ.localizedFunctor W₁.Q W₂.Q)
  simp only [Φ.equiv_smallShiftedHomMap W₁.Q W₂.Q _ _ (Φ.localizedFunctor W₁.Q W₂.Q) e,
    Functor.comp_obj, ShiftedHom.map, SmallShiftedHom.equiv_mk, Functor.map_comp, assoc,
    ShiftedHom.comp_mk₀, NatTrans.shift_app, Functor.commShiftIso_comp_inv_app,
    Functor.commShiftIso_comp_hom_app, Iso.hom_inv_id_app_assoc, ShiftedHom.mk₀_comp,
    Functor.commShiftIso_hom_naturality]
  nth_rw 2 [← Functor.map_comp_assoc]
  simp [reassoc_of% (NatIso.naturality_2 e f)]

中文:
引理 smallShiftedHomMap_mk
  条件: {m : M} (f : ShiftedHom X₁ Y₁ m)
  证明: by
  apply (SmallShiftedHom.equiv W₂ W₂.Q).injective
  let e := CatCommSq.iso Φ.functor W₁.Q W₂.Q (Φ.localizedFunctor W₁.Q W₂.Q)
  simp only [Φ.equiv_smallShiftedHomMap W₁.Q W₂.Q _ _ (Φ.localizedFunctor W₁.Q W₂.Q) e,
    Functor.comp_obj, ShiftedHom.map, SmallShiftedHom.equiv_mk, Functor.map_comp, assoc,
    ShiftedHom.comp_mk₀, NatTrans.shift_app, Functor.commShiftIso_comp_inv_app,
    Functor.commShiftIso_comp_hom_app, Iso.hom_inv_id_app_assoc, ShiftedHom.mk₀_comp,
    Functor.commShiftIso_hom_naturality]
  nth_rw 2 [← Functor.map_comp_assoc]
  simp [reassoc_of% (NatIso.naturality_2 e f)]

Depends on / 依赖: CatCommSq, CatCommSq.iso, Functor, Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_inv_app, Functor.commShiftIso_hom_naturality, Functor.comp_obj, Functor.map_comp, Iso.hom_inv_id_app_assoc, NatTrans, NatTrans.shift_app, ShiftedHom, ShiftedHom.comp_mk, ShiftedHom.map, ShiftedHom.mk, SmallShiftedHom, SmallShiftedHom.equiv, SmallShiftedHom.equiv_mk, commShiftIso_comp_hom_app, commShiftIso_comp_inv_app
-/
lemma smallShiftedHomMap_mk {m : M} (f : ShiftedHom X₁ Y₁ m) :
    Φ.smallShiftedHomMap eX eY (.mk _ f) =
      .mk _ ((ShiftedHom.mk₀ _ rfl eX.inv).comp
        ((f.map Φ.functor).comp (.mk₀ _ rfl eY.hom) (zero_add m)) (add_zero _)) := by
  apply (SmallShiftedHom.equiv W₂ W₂.Q).injective
  let e := CatCommSq.iso Φ.functor W₁.Q W₂.Q (Φ.localizedFunctor W₁.Q W₂.Q)
  simp only [Φ.equiv_smallShiftedHomMap W₁.Q W₂.Q _ _ (Φ.localizedFunctor W₁.Q W₂.Q) e,
    Functor.comp_obj, ShiftedHom.map, SmallShiftedHom.equiv_mk, Functor.map_comp, assoc,
    ShiftedHom.comp_mk₀, NatTrans.shift_app, Functor.commShiftIso_comp_inv_app,
    Functor.commShiftIso_comp_hom_app, Iso.hom_inv_id_app_assoc, ShiftedHom.mk₀_comp,
    Functor.commShiftIso_hom_naturality]
  nth_rw 2 [← Functor.map_comp_assoc]
  simp [reassoc_of% (NatIso.naturality_2 e f)]

/--
lemma `smallShiftedHomMap_mk₀` / 引理 `smallShiftedHomMap_mk₀`

English:
lemma smallShiftedHomMap_mk₀
  given: (m₀ : M) (hm₀ : m₀ = 0) (f : X₁ ⟶ Y₁)
  proof: by
  simp [SmallShiftedHom.mk₀]

中文:
引理 smallShiftedHomMap_mk₀
  条件: (m₀ : M) (hm₀ : m₀ = 0) (f : X₁ ⟶ Y₁)
  证明: by
  simp [SmallShiftedHom.mk₀]

Depends on / 依赖: SmallShiftedHom, SmallShiftedHom.mk
-/
lemma smallShiftedHomMap_mk₀ (m₀ : M) (hm₀ : m₀ = 0) (f : X₁ ⟶ Y₁) :
    Φ.smallShiftedHomMap eX eY (.mk₀ _ _ hm₀ f) =
      .mk₀ _ _ hm₀ (eX.inv ≫ Φ.functor.map f ≫ eY.hom) := by
  simp [SmallShiftedHom.mk₀]

set_option backward.defeqAttrib.useBackward true in
/--
lemma `smallShiftedHomMap_comp` / 引理 `smallShiftedHomMap_comp`

English:
lemma smallShiftedHomMap_comp
  proof: by
  apply (SmallShiftedHom.equiv W₂ W₂.Q).injective
  let e := CatCommSq.iso Φ.functor W₁.Q W₂.Q (Φ.localizedFunctor W₁.Q W₂.Q)
  simp only [Φ.equiv_smallShiftedHomMap W₁.Q W₂.Q _ _ (Φ.localizedFunctor W₁.Q W₂.Q) e,
    SmallShiftedHom.equiv_comp, ShiftedHom.map_comp]
  rw [ShiftedHom.comp_assoc _ _ _ _ (zero_add b) (by simpa)]; rw [ShiftedHom.comp_assoc _ _ _ _ h (by simpa)]; rw [ShiftedHom.comp_assoc _ _ _ _ (add_zero b) (by simpa)]; rw [← ShiftedHom.comp_assoc _ _ _ (add_zero 0) (add_zero b) (by simp)]; rw [ShiftedHom.mk₀_comp_mk₀]
  simp

中文:
引理 smallShiftedHomMap_comp
  证明: by
  apply (SmallShiftedHom.equiv W₂ W₂.Q).injective
  let e := CatCommSq.iso Φ.functor W₁.Q W₂.Q (Φ.localizedFunctor W₁.Q W₂.Q)
  simp only [Φ.equiv_smallShiftedHomMap W₁.Q W₂.Q _ _ (Φ.localizedFunctor W₁.Q W₂.Q) e,
    SmallShiftedHom.equiv_comp, ShiftedHom.map_comp]
  rw [ShiftedHom.comp_assoc _ _ _ _ (zero_add b) (by simpa)]; rw [ShiftedHom.comp_assoc _ _ _ _ h (by simpa)]; rw [ShiftedHom.comp_assoc _ _ _ _ (add_zero b) (by simpa)]; rw [← ShiftedHom.comp_assoc _ _ _ (add_zero 0) (add_zero b) (by simp)]; rw [ShiftedHom.mk₀_comp_mk₀]
  simp

Depends on / 依赖: CatCommSq, CatCommSq.iso, ShiftedHom, ShiftedHom.comp_assoc, ShiftedHom.map_comp, SmallShiftedHom, SmallShiftedHom.equiv, SmallShiftedHom.equiv_comp, add_zero, comp_assoc, equiv_comp, equiv_smallShiftedHomMap, functor, injective, localizedFunctor, map_comp, zero_add
-/
lemma smallShiftedHomMap_comp
    [HasSmallLocalizedShiftedHom.{w} W₁ M Y₁ Z₁] [HasSmallLocalizedShiftedHom.{w''} W₂ M Z₂ Z₂]
    [HasSmallLocalizedShiftedHom.{w''} W₂ M Y₂ Z₂] [HasSmallLocalizedShiftedHom.{w} W₁ M X₁ Z₁]
    [HasSmallLocalizedShiftedHom.{w} W₁ M Z₁ Z₁] [HasSmallLocalizedShiftedHom.{w''} W₂ M X₂ Z₂]
    {a b c : M} (f : SmallShiftedHom.{w} W₁ X₁ Y₁ a) (g : SmallShiftedHom.{w} W₁ Y₁ Z₁ b)
    (h : b + a = c) :
    Φ.smallShiftedHomMap eX eZ (f.comp g h) =
      (Φ.smallShiftedHomMap eX eY f).comp (Φ.smallShiftedHomMap eY eZ g) h := by
  apply (SmallShiftedHom.equiv W₂ W₂.Q).injective
  let e := CatCommSq.iso Φ.functor W₁.Q W₂.Q (Φ.localizedFunctor W₁.Q W₂.Q)
  simp only [Φ.equiv_smallShiftedHomMap W₁.Q W₂.Q _ _ (Φ.localizedFunctor W₁.Q W₂.Q) e,
    SmallShiftedHom.equiv_comp, ShiftedHom.map_comp]
  rw [ShiftedHom.comp_assoc _ _ _ _ (zero_add b) (by simpa)]; rw [ShiftedHom.comp_assoc _ _ _ _ h (by simpa)]; rw [ShiftedHom.comp_assoc _ _ _ _ (add_zero b) (by simpa)]; rw [← ShiftedHom.comp_assoc _ _ _ (add_zero 0) (add_zero b) (by simp)]; rw [ShiftedHom.mk₀_comp_mk₀]
  simp

end LocalizerMorphism

end CategoryTheory
