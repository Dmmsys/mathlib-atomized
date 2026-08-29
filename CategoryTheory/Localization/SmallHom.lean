/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.HomEquiv
public import Mathlib.Logic.Small.Defs

/-!
# Shrinking morphisms in localized categories

Given a class of morphisms `W : MorphismProperty C`, and two objects `X` and `Y`,
we introduce a type-class `HasSmallLocalizedHom.{w} W X Y` which expresses
that in the localized category with respect to `W`, the type of morphisms from `X`
to `Y` is `w`-small for a certain universe `w`. Under this assumption,
we define `SmallHom.{w} W X Y : Type w` as the shrunk type. For any localization
functor `L : C ⥤ D` for `W`, we provide a bijection
`SmallHom.equiv.{w} W L : SmallHom.{w} W X Y ≃ (L.obj X ⟶ L.obj Y)` that is compatible
with the composition of morphisms.

-/

@[expose] public section

universe w'' w w' v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

namespace CategoryTheory

open Category

namespace Localization

variable {C : Type u₁} [Category.{v₁} C] (W : MorphismProperty C)
  {D : Type u₂} [Category.{v₂} D]
  {D' : Type u₃} [Category.{v₃} D']

section

variable (L : C ⥤ D) [L.IsLocalization W] (X Y Z : C)

/-- This property holds if the type of morphisms between `X` and `Y`
in the localized category with respect to `W : MorphismProperty C`
is small. -/
-- After https://github.com/leanprover/lean4/pull/12286 and
-- https://github.com/leanprover/lean4/pull/12423, the universe `w` would default to a
-- universe output parameter. See Note [universe output parameters and typeclass caching].
@[univ_out_params]
/--
Definition of `HasSmallLocalizedHom` / `HasSmallLocalizedHom` 的定义

English:
class HasSmallLocalizedHom
  parameters: : Prop where
  axioms and operations (1):
    - small : Small.{w} (W.Q.obj X ⟶ W.Q.obj Y)

中文:
类 有SmallLocalized态射
  参数: : 命题 where
  公理与运算 (1 个):
    - small : Small.{w} (W.Q.obj X ⟶ W.Q.obj Y)
-/
class HasSmallLocalizedHom : Prop where
  small : Small.{w} (W.Q.obj X ⟶ W.Q.obj Y)

attribute [instance] HasSmallLocalizedHom.small

variable {X Y Z}

/--
lemma `hasSmallLocalizedHom_iff` / 引理 `hasSmallLocalizedHom_iff`

English:
lemma hasSmallLocalizedHom_iff
  proof: by
  constructor
  · intro h
    exact small_map (homEquiv W W.Q L).symm
  · intro h
    exact ⟨small_map (homEquiv W W.Q L)⟩

include L in

中文:
引理 hasSmallLocalizedHom_iff
  证明: by
  constructor
  · intro h
    exact small_map (homEquiv W W.Q L).symm
  · intro h
    exact ⟨small_map (homEquiv W W.Q L)⟩

include L in

Depends on / 依赖: homEquiv, small_map
-/
lemma hasSmallLocalizedHom_iff :
    HasSmallLocalizedHom.{w} W X Y ↔ Small.{w} (L.obj X ⟶ L.obj Y) := by
  constructor
  · intro h
    exact small_map (homEquiv W W.Q L).symm
  · intro h
    exact ⟨small_map (homEquiv W W.Q L)⟩

include L in
/--
lemma `hasSmallLocalizedHom_of_isLocalization` / 引理 `hasSmallLocalizedHom_of_isLocalization`

English:
lemma hasSmallLocalizedHom_of_isLocalization
  proof: by
  rw [hasSmallLocalizedHom_iff W L]
  infer_instance

中文:
引理 hasSmallLocalizedHom_of_isLocalization
  证明: by
  rw [hasSmallLocalizedHom_iff W L]
  infer_instance

Depends on / 依赖: F.shiftIso_add, hasSmallLocalizedHom_iff, infer_instance, shiftIso_add
-/
lemma hasSmallLocalizedHom_of_isLocalization :
    HasSmallLocalizedHom.{v₂} W X Y := by
  rw [hasSmallLocalizedHom_iff W L]
  infer_instance

variable (X Y) in
/--
lemma `small_of_hasSmallLocalizedHom` / 引理 `small_of_hasSmallLocalizedHom`

English:
lemma small_of_hasSmallLocalizedHom
  given: [HasSmallLocalizedHom.{w} W X Y]
  proof: by
  rwa [← hasSmallLocalizedHom_iff W]

中文:
引理 small_of_hasSmallLocalizedHom
  条件: [有SmallLocalized态射.{w} W X Y]
  证明: by
  rwa [← hasSmallLocalizedHom_iff W]

Depends on / 依赖: F.shiftIso_add, hasSmallLocalizedHom_iff, shiftIso_add
-/
lemma small_of_hasSmallLocalizedHom [HasSmallLocalizedHom.{w} W X Y] :
    Small.{w} (L.obj X ⟶ L.obj Y) := by
  rwa [← hasSmallLocalizedHom_iff W]

/--
lemma `hasSmallLocalizedHom_iff_of_isos` / 引理 `hasSmallLocalizedHom_iff_of_isos`

English:
lemma hasSmallLocalizedHom_iff_of_isos
  given: {X' Y' : C} (e : X ≅ X') (e' : Y ≅ Y')
  proof: by
  simp only [hasSmallLocalizedHom_iff W W.Q]
  exact small_congr (Iso.homCongr (W.Q.mapIso e) (W.Q.mapIso e'))

中文:
引理 hasSmallLocalizedHom_iff_of_isos
  条件: {X' Y' : C} (e : X ≅ X') (e' : Y ≅ Y')
  证明: by
  simp only [hasSmallLocalizedHom_iff W W.Q]
  exact small_congr (Iso.homCongr (W.Q.mapIso e) (W.Q.mapIso e'))

Depends on / 依赖: Iso.homCongr, W.Q.mapIso, hasSmallLocalizedHom_iff, homCongr, mapIso, small_congr
-/
lemma hasSmallLocalizedHom_iff_of_isos {X' Y' : C} (e : X ≅ X') (e' : Y ≅ Y') :
    HasSmallLocalizedHom.{w} W X Y ↔ HasSmallLocalizedHom.{w} W X' Y' := by
  simp only [hasSmallLocalizedHom_iff W W.Q]
  exact small_congr (Iso.homCongr (W.Q.mapIso e) (W.Q.mapIso e'))

/--
lemma `hasSmallLocalizedHom_of_isos` / 引理 `hasSmallLocalizedHom_of_isos`

English:
lemma hasSmallLocalizedHom_of_isos
  statement: {X' Y' : C} (e : X ≅ X') (e' : Y ≅ Y')
  proof: by
  rwa [← hasSmallLocalizedHom_iff_of_isos _ e e']

中文:
引理 hasSmallLocalizedHom_of_isos
  结论: {X' Y' : C} (e : X ≅ X') (e' : Y ≅ Y')
  证明: by
  rwa [← hasSmallLocalizedHom_iff_of_isos _ e e']

Depends on / 依赖: hasSmallLocalizedHom_iff_of_isos
-/
lemma hasSmallLocalizedHom_of_isos {X' Y' : C} (e : X ≅ X') (e' : Y ≅ Y')
    [HasSmallLocalizedHom.{w} W X Y] :
    HasSmallLocalizedHom.{w} W X' Y' := by
  rwa [← hasSmallLocalizedHom_iff_of_isos _ e e']

variable (X) in
/--
lemma `hasSmallLocalizedHom_iff_target` / 引理 `hasSmallLocalizedHom_iff_target`

English:
lemma hasSmallLocalizedHom_iff_target
  given: {Y Y' : C} (f : Y ⟶ Y') (hf : W f)
  proof: by
  simp only [hasSmallLocalizedHom_iff W W.Q]
  exact small_congr (Iso.homCongr (Iso.refl _) (Localization.isoOfHom W.Q W f hf))

中文:
引理 hasSmallLocalizedHom_iff_target
  条件: {Y Y' : C} (f : Y ⟶ Y') (hf : W f)
  证明: by
  simp only [hasSmallLocalizedHom_iff W W.Q]
  exact small_congr (Iso.homCongr (Iso.refl _) (Localization.isoOfHom W.Q W f hf))

Depends on / 依赖: Iso.homCongr, Iso.refl, Localization, Localization.isoOfHom, hasSmallLocalizedHom_iff, homCongr, isoOfHom, small_congr
-/
lemma hasSmallLocalizedHom_iff_target {Y Y' : C} (f : Y ⟶ Y') (hf : W f) :
    HasSmallLocalizedHom.{w} W X Y ↔ HasSmallLocalizedHom.{w} W X Y' := by
  simp only [hasSmallLocalizedHom_iff W W.Q]
  exact small_congr (Iso.homCongr (Iso.refl _) (Localization.isoOfHom W.Q W f hf))

/--
lemma `hasSmallLocalizedHom_iff_source` / 引理 `hasSmallLocalizedHom_iff_source`

English:
lemma hasSmallLocalizedHom_iff_source
  given: {X' : C} (f : X ⟶ X') (hf : W f) (Y : C)
  proof: by
  simp only [hasSmallLocalizedHom_iff W W.Q]
  exact small_congr (Iso.homCongr (Localization.isoOfHom W.Q W f hf) (Iso.refl _))

中文:
引理 hasSmallLocalizedHom_iff_source
  条件: {X' : C} (f : X ⟶ X') (hf : W f) (Y : C)
  证明: by
  simp only [hasSmallLocalizedHom_iff W W.Q]
  exact small_congr (Iso.homCongr (Localization.isoOfHom W.Q W f hf) (Iso.refl _))

Depends on / 依赖: Iso.homCongr, Iso.refl, Localization, Localization.isoOfHom, hasSmallLocalizedHom_iff, homCongr, isoOfHom, small_congr
-/
lemma hasSmallLocalizedHom_iff_source {X' : C} (f : X ⟶ X') (hf : W f) (Y : C) :
    HasSmallLocalizedHom.{w} W X Y ↔ HasSmallLocalizedHom.{w} W X' Y := by
  simp only [hasSmallLocalizedHom_iff W W.Q]
  exact small_congr (Iso.homCongr (Localization.isoOfHom W.Q W f hf) (Iso.refl _))

end

/--
Definition of `SmallHom` / `SmallHom` 的定义

English:
definition SmallHom
  signature: (X Y : C) [HasSmallLocalizedHom.{w} W X Y]
  body: Shrink.{w} (W.Q.obj X ⟶ W.Q.obj Y)

中文:
定义 SmallHom
  签名: (X Y : C) [有SmallLocalized态射.{w} W X Y]
  定义体: Shrink.{w} (W.Q.obj X ⟶ W.Q.obj Y)

Depends on / 依赖: Shrink, W.Q.obj
-/
def SmallHom (X Y : C) [HasSmallLocalizedHom.{w} W X Y] : Type w :=
  Shrink.{w} (W.Q.obj X ⟶ W.Q.obj Y)

namespace SmallHom

/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: (L : C ⥤ D) [L.IsLocalization W] {X Y : C}
  body: letI := small_of_hasSmallLocalizedHom.{w} W W.Q X Y
  (equivShrink _).symm.trans (homEquiv W W.Q L)

中文:
定义 equiv
  签名: (L : C ⥤ D) [L.是Localization W] {X Y : C}
  定义体: letI := small_of_hasSmallLocalizedHom.{w} W W.Q X Y
  (equivShrink _).symm.trans (homEquiv W W.Q L)

Depends on / 依赖: equivShrink, homEquiv, small_of_hasSmallLocalizedHom, symm.trans
-/
noncomputable def equiv (L : C ⥤ D) [L.IsLocalization W] {X Y : C}
    [HasSmallLocalizedHom.{w} W X Y] :
    SmallHom.{w} W X Y ≃ (L.obj X ⟶ L.obj Y) :=
  letI := small_of_hasSmallLocalizedHom.{w} W W.Q X Y
  (equivShrink _).symm.trans (homEquiv W W.Q L)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `equiv_equiv_symm` / 引理 `equiv_equiv_symm`

English:
lemma equiv_equiv_symm
  statement: (L : C ⥤ D) [L.IsLocalization W]
  proof: by
  dsimp [equiv]
  rw [Equiv.symm_apply_apply]; rw [homEquiv_trans]
  apply homEquiv_eq

中文:
引理 equiv_equiv_symm
  结论: (L : C ⥤ D) [L.是Localization W]
  证明: by
  dsimp [equiv]
  rw [Equiv.symm_apply_apply]; rw [homEquiv_trans]
  apply homEquiv_eq

Depends on / 依赖: Equiv.symm_apply_apply, homEquiv_eq, homEquiv_trans, symm_apply_apply
-/
lemma equiv_equiv_symm (L : C ⥤ D) [L.IsLocalization W]
    (L' : C ⥤ D') [L'.IsLocalization W] (G : D ⥤ D')
    (e : L ⋙ G ≅ L') {X Y : C} [HasSmallLocalizedHom.{w} W X Y]
    (f : L.obj X ⟶ L.obj Y) :
    equiv W L' ((equiv W L).symm f) =
      e.inv.app X ≫ G.map f ≫ e.hom.app Y := by
  dsimp [equiv]
  rw [Equiv.symm_apply_apply]; rw [homEquiv_trans]
  apply homEquiv_eq

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: {X Y : C} [HasSmallLocalizedHom.{w} W X Y] (f : X ⟶ Y)
  body: (equiv.{w} W W.Q).symm (W.Q.map f)

中文:
定义 mk
  签名: {X Y : C} [有SmallLocalized态射.{w} W X Y] (f : X ⟶ Y)
  定义体: (equiv.{w} W W.Q).symm (W.Q.map f)

Depends on / 依赖: W.Q.map
-/
noncomputable def mk {X Y : C} [HasSmallLocalizedHom.{w} W X Y] (f : X ⟶ Y) :
    SmallHom.{w} W X Y :=
  (equiv.{w} W W.Q).symm (W.Q.map f)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `equiv_mk` / 引理 `equiv_mk`

English:
lemma equiv_mk
  statement: (L : C ⥤ D) [L.IsLocalization W] {X Y : C}
  proof: by
  simp [equiv, mk]

中文:
引理 equiv_mk
  结论: (L : C ⥤ D) [L.是Localization W] {X Y : C}
  证明: by
  simp [equiv, mk]
-/
lemma equiv_mk (L : C ⥤ D) [L.IsLocalization W] {X Y : C}
    [HasSmallLocalizedHom.{w} W X Y] (f : X ⟶ Y) :
    equiv.{w} W L (mk W f) = L.map f := by
  simp [equiv, mk]

variable {W}

/--
Definition of `mkInv` / `mkInv` 的定义

English:
definition mkInv
  signature: {X Y : C} (f : Y ⟶ X) (hf : W f) [HasSmallLocalizedHom.{w} W X Y]
  body: (equiv.{w} W W.Q).symm (Localization.isoOfHom W.Q W f hf).inv

中文:
定义 mkInv
  签名: {X Y : C} (f : Y ⟶ X) (hf : W f) [有SmallLocalized态射.{w} W X Y]
  定义体: (equiv.{w} W W.Q).symm (Localization.isoOfHom W.Q W f hf).inv

Depends on / 依赖: Localization, Localization.isoOfHom, isoOfHom
-/
noncomputable def mkInv {X Y : C} (f : Y ⟶ X) (hf : W f) [HasSmallLocalizedHom.{w} W X Y] :
    SmallHom.{w} W X Y :=
  (equiv.{w} W W.Q).symm (Localization.isoOfHom W.Q W f hf).inv

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `equiv_mkInv` / 引理 `equiv_mkInv`

English:
lemma equiv_mkInv
  statement: (L : C ⥤ D) [L.IsLocalization W] {X Y : C} (f : Y ⟶ X) (hf : W f)
  proof: by
  simp only [equiv, mkInv, Equiv.symm_trans_apply, Equiv.symm_symm, homEquiv_symm_apply,
    Equiv.trans_apply, Equiv.symm_apply_apply, homEquiv_isoOfHom_inv]

中文:
引理 equiv_mkInv
  结论: (L : C ⥤ D) [L.是Localization W] {X Y : C} (f : Y ⟶ X) (hf : W f)
  证明: by
  simp only [equiv, mkInv, Equiv.symm_trans_apply, Equiv.symm_symm, homEquiv_symm_apply,
    Equiv.trans_apply, Equiv.symm_apply_apply, homEquiv_isoOfHom_inv]

Depends on / 依赖: Equiv.symm_apply_apply, Equiv.symm_symm, Equiv.symm_trans_apply, Equiv.trans_apply, homEquiv_isoOfHom_inv, homEquiv_symm_apply, symm_apply_apply, symm_symm, symm_trans_apply, trans_apply
-/
lemma equiv_mkInv (L : C ⥤ D) [L.IsLocalization W] {X Y : C} (f : Y ⟶ X) (hf : W f)
    [HasSmallLocalizedHom.{w} W X Y] :
    equiv.{w} W L (mkInv f hf) = (Localization.isoOfHom L W f hf).inv := by
  simp only [equiv, mkInv, Equiv.symm_trans_apply, Equiv.symm_symm, homEquiv_symm_apply,
    Equiv.trans_apply, Equiv.symm_apply_apply, homEquiv_isoOfHom_inv]

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: {X Y Z : C} [HasSmallLocalizedHom.{w} W X Y]
  body: (equiv W W.Q).symm (equiv W W.Q α ≫ equiv W W.Q β)

中文:
定义 comp
  签名: {X Y Z : C} [有SmallLocalized态射.{w} W X Y]
  定义体: (equiv W W.Q).symm (equiv W W.Q α ≫ equiv W W.Q β)
-/
noncomputable def comp {X Y Z : C} [HasSmallLocalizedHom.{w} W X Y]
    [HasSmallLocalizedHom.{w} W Y Z] [HasSmallLocalizedHom.{w} W X Z]
    (α : SmallHom.{w} W X Y) (β : SmallHom.{w} W Y Z) :
    SmallHom.{w} W X Z :=
  (equiv W W.Q).symm (equiv W W.Q α ≫ equiv W W.Q β)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `equiv_comp` / 引理 `equiv_comp`

English:
lemma equiv_comp
  statement: (L : C ⥤ D) [L.IsLocalization W] {X Y Z : C} [HasSmallLocalizedHom.{w} W X Y]
  proof: by
  let := small_of_hasSmallLocalizedHom.{w} W W.Q X Y
  let := small_of_hasSmallLocalizedHom.{w} W W.Q Y Z
  obtain ⟨α, rfl⟩ := (equivShrink _).surjective α
  obtain ⟨β, rfl⟩ := (equivShrink _).surjective β
  dsimp [equiv, comp]
  rw [Equiv.symm_apply_apply]
  simp only [homEquiv_refl, homEquiv_co

中文:
引理 equiv_comp
  结论: (L : C ⥤ D) [L.是Localization W] {X Y Z : C} [有SmallLocalized态射.{w} W X Y]
  证明: by
  let := small_of_hasSmallLocalizedHom.{w} W W.Q X Y
  let := small_of_hasSmallLocalizedHom.{w} W W.Q Y Z
  obtain ⟨α, rfl⟩ := (equivShrink _).surjective α
  obtain ⟨β, rfl⟩ := (equivShrink _).surjective β
  dsimp [equiv, comp]
  rw [Equiv.symm_apply_apply]
  simp only [homEquiv_refl, homEquiv_co

Depends on / 依赖: Equiv.symm_apply_apply, equivShrink, homEquiv_comp, homEquiv_refl, small_of_hasSmallLocalizedHom, surjective, symm_apply_apply
-/
lemma equiv_comp (L : C ⥤ D) [L.IsLocalization W] {X Y Z : C} [HasSmallLocalizedHom.{w} W X Y]
    [HasSmallLocalizedHom.{w} W Y Z] [HasSmallLocalizedHom.{w} W X Z]
    (α : SmallHom.{w} W X Y) (β : SmallHom.{w} W Y Z) :
    equiv W L (α.comp β) = equiv W L α ≫ equiv W L β := by
  let := small_of_hasSmallLocalizedHom.{w} W W.Q X Y
  let := small_of_hasSmallLocalizedHom.{w} W W.Q Y Z
  obtain ⟨α, rfl⟩ := (equivShrink _).surjective α
  obtain ⟨β, rfl⟩ := (equivShrink _).surjective β
  dsimp [equiv, comp]
  rw [Equiv.symm_apply_apply]
  simp only [homEquiv_refl, homEquiv_comp]

section

variable {X Y Z T : C}

/--
lemma `mk_comp_mk` / 引理 `mk_comp_mk`

English:
lemma mk_comp_mk
  statement: [HasSmallLocalizedHom.{w} W X Y] [HasSmallLocalizedHom.{w} W Y Z]
  proof: (equiv W W.Q).injective (by simp [equiv_comp])

@[simp]

中文:
引理 mk_comp_mk
  结论: [有SmallLocalized态射.{w} W X Y] [有SmallLocalized态射.{w} W Y Z]
  证明: (equiv W W.Q).injective (by simp [equiv_comp])

@[simp]

Depends on / 依赖: equiv_comp, injective
-/
lemma mk_comp_mk [HasSmallLocalizedHom.{w} W X Y] [HasSmallLocalizedHom.{w} W Y Z]
    [HasSmallLocalizedHom.{w} W X Z] (f : X ⟶ Y) (g : Y ⟶ Z) :
    (mk W f).comp (mk W g) = mk W (f ≫ g) :=
  (equiv W W.Q).injective (by simp [equiv_comp])

@[simp]
/--
lemma `comp_mk_id` / 引理 `comp_mk_id`

English:
lemma comp_mk_id
  statement: [HasSmallLocalizedHom.{w} W X Y] [HasSmallLocalizedHom.{w} W Y Y]
  proof: (equiv W W.Q).injective (by simp [equiv_comp])

@[simp]

中文:
引理 comp_mk_id
  结论: [有SmallLocalized态射.{w} W X Y] [有SmallLocalized态射.{w} W Y Y]
  证明: (equiv W W.Q).injective (by simp [equiv_comp])

@[simp]

Depends on / 依赖: equiv_comp, injective
-/
lemma comp_mk_id [HasSmallLocalizedHom.{w} W X Y] [HasSmallLocalizedHom.{w} W Y Y]
    (α : SmallHom.{w} W X Y) :
    α.comp (mk W (𝟙 Y)) = α :=
  (equiv W W.Q).injective (by simp [equiv_comp])

@[simp]
/--
lemma `mk_id_comp` / 引理 `mk_id_comp`

English:
lemma mk_id_comp
  statement: [HasSmallLocalizedHom.{w} W X Y] [HasSmallLocalizedHom.{w} W X X]
  proof: (equiv W W.Q).injective (by simp [equiv_comp])

@[simp]

中文:
引理 mk_id_comp
  结论: [有SmallLocalized态射.{w} W X Y] [有SmallLocalized态射.{w} W X X]
  证明: (equiv W W.Q).injective (by simp [equiv_comp])

@[simp]

Depends on / 依赖: equiv_comp, evaluation, injective
-/
lemma mk_id_comp [HasSmallLocalizedHom.{w} W X Y] [HasSmallLocalizedHom.{w} W X X]
    (α : SmallHom.{w} W X Y) :
    (mk W (𝟙 X)).comp α = α :=
  (equiv W W.Q).injective (by simp [equiv_comp])

@[simp]
/--
lemma `comp_assoc` / 引理 `comp_assoc`

English:
lemma comp_assoc
  statement: [HasSmallLocalizedHom.{w} W X Y] [HasSmallLocalizedHom.{w} W X Z]
  proof: by
  apply (equiv W W.Q).injective
  simp only [equiv_comp, assoc]

@[simp]

中文:
引理 comp_assoc
  结论: [有SmallLocalized态射.{w} W X Y] [有SmallLocalized态射.{w} W X Z]
  证明: by
  apply (equiv W W.Q).injective
  simp only [equiv_comp, assoc]

@[simp]

Depends on / 依赖: equiv_comp, injective
-/
lemma comp_assoc [HasSmallLocalizedHom.{w} W X Y] [HasSmallLocalizedHom.{w} W X Z]
    [HasSmallLocalizedHom.{w} W X T] [HasSmallLocalizedHom.{w} W Y Z]
    [HasSmallLocalizedHom.{w} W Y T] [HasSmallLocalizedHom.{w} W Z T]
    (α : SmallHom.{w} W X Y) (β : SmallHom.{w} W Y Z) (γ : SmallHom.{w} W Z T) :
    (α.comp β).comp γ = α.comp (β.comp γ) := by
  apply (equiv W W.Q).injective
  simp only [equiv_comp, assoc]

@[simp]
/--
lemma `mk_comp_mkInv` / 引理 `mk_comp_mkInv`

English:
lemma mk_comp_mkInv
  statement: [HasSmallLocalizedHom.{w} W X Y] [HasSmallLocalizedHom.{w} W Y X]
  proof: (equiv W W.Q).injective (by simp [equiv_comp])

@[simp]

中文:
引理 mk_comp_mkInv
  结论: [有SmallLocalized态射.{w} W X Y] [有SmallLocalized态射.{w} W Y X]
  证明: (equiv W W.Q).injective (by simp [equiv_comp])

@[simp]

Depends on / 依赖: equiv_comp, injective
-/
lemma mk_comp_mkInv [HasSmallLocalizedHom.{w} W X Y] [HasSmallLocalizedHom.{w} W Y X]
    [HasSmallLocalizedHom.{w} W Y Y] (f : Y ⟶ X) (hf : W f) :
    (mk W f).comp (mkInv f hf) = mk W (𝟙 Y) :=
  (equiv W W.Q).injective (by simp [equiv_comp])

@[simp]
/--
lemma `mkInv_comp_mk` / 引理 `mkInv_comp_mk`

English:
lemma mkInv_comp_mk
  statement: [HasSmallLocalizedHom.{w} W X X] [HasSmallLocalizedHom.{w} W X Y]
  proof: (equiv W W.Q).injective (by simp [equiv_comp])

中文:
引理 mkInv_comp_mk
  结论: [有SmallLocalized态射.{w} W X X] [有SmallLocalized态射.{w} W X Y]
  证明: (equiv W W.Q).injective (by simp [equiv_comp])

Depends on / 依赖: equiv_comp, injective
-/
lemma mkInv_comp_mk [HasSmallLocalizedHom.{w} W X X] [HasSmallLocalizedHom.{w} W X Y]
    [HasSmallLocalizedHom.{w} W Y X] (f : Y ⟶ X) (hf : W f) :
    (mkInv f hf).comp (mk W f) = mk W (𝟙 X) :=
  (equiv W W.Q).injective (by simp [equiv_comp])

end

section ChangeOfUniverse

/--
Definition of `chgUniv` / `chgUniv` 的定义

English:
definition chgUniv
  signature: {X Y : C}
  body: (equiv.{w} W W.Q).trans (equiv.{w''} W W.Q).symm

中文:
定义 chgUniv
  签名: {X Y : C}
  定义体: (equiv.{w} W W.Q).trans (equiv.{w''} W W.Q).symm
-/
noncomputable def chgUniv {X Y : C}
    [HasSmallLocalizedHom.{w} W X Y] [HasSmallLocalizedHom.{w''} W X Y] :
    SmallHom.{w} W X Y ≃ SmallHom.{w''} W X Y :=
  (equiv.{w} W W.Q).trans (equiv.{w''} W W.Q).symm

/--
lemma `equiv_chgUniv` / 引理 `equiv_chgUniv`

English:
lemma equiv_chgUniv
  statement: (L : C ⥤ D) [L.IsLocalization W] {X Y : C}
  proof: by
  obtain ⟨f, rfl⟩ := (equiv W W.Q).symm.surjective e
  dsimp [chgUniv]
  simp only [Equiv.apply_symm_apply,
    equiv_equiv_symm W _ _ _ (Localization.compUniqFunctor W.Q L W)]

中文:
引理 equiv_chgUniv
  结论: (L : C ⥤ D) [L.是Localization W] {X Y : C}
  证明: by
  obtain ⟨f, rfl⟩ := (equiv W W.Q).symm.surjective e
  dsimp [chgUniv]
  simp only [Equiv.apply_symm_apply,
    equiv_equiv_symm W _ _ _ (Localization.compUniqFunctor W.Q L W)]

Depends on / 依赖: Equiv.apply_symm_apply, Localization, Localization.compUniqFunctor, apply_symm_apply, chgUniv, compUniqFunctor, equiv_equiv_symm, surjective, symm.surjective
-/
lemma equiv_chgUniv (L : C ⥤ D) [L.IsLocalization W] {X Y : C}
    [HasSmallLocalizedHom.{w} W X Y] [HasSmallLocalizedHom.{w''} W X Y]
    (e : SmallHom.{w} W X Y) :
    equiv W L (chgUniv.{w''} e) = equiv W L e := by
  obtain ⟨f, rfl⟩ := (equiv W W.Q).symm.surjective e
  dsimp [chgUniv]
  simp only [Equiv.apply_symm_apply,
    equiv_equiv_symm W _ _ _ (Localization.compUniqFunctor W.Q L W)]

end ChangeOfUniverse

end SmallHom

end Localization

namespace LocalizerMorphism

open Localization

variable {C₁ : Type u₁} [Category.{v₁} C₁] {W₁ : MorphismProperty C₁}
  {C₂ : Type u₂} [Category.{v₂} C₂] {W₂ : MorphismProperty C₂}
  {D₁ : Type u₃} [Category.{v₃} D₁] {D₂ : Type u₄} [Category.{v₄} D₂]
  (Φ : LocalizerMorphism W₁ W₂) (L₁ : C₁ ⥤ D₁) [L₁.IsLocalization W₁]
  (L₂ : C₂ ⥤ D₂) [L₂.IsLocalization W₂]

section

variable {X Y : C₁}

variable [HasSmallLocalizedHom.{w} W₁ X Y]
  [HasSmallLocalizedHom.{w'} W₂ (Φ.functor.obj X) (Φ.functor.obj Y)]

/--
Definition of `smallHomMap` / `smallHomMap` 的定义

English:
definition smallHomMap
  signature: (f : SmallHom.{w} W₁ X Y)
  body: (SmallHom.equiv W₂ W₂.Q).symm
    (Iso.homCongr ((CatCommSq.iso Φ.functor W₁.Q W₂.Q _).symm.app _)
      ((CatCommSq.iso Φ.functor W₁.Q W₂.Q _).symm.app _)
      ((Φ.localizedFunctor W₁.Q W₂.Q).map ((SmallHom.equiv W₁ W₁.Q) f)))

中文:
定义 smallHomMap
  签名: (f : SmallHom.{w} W₁ X Y)
  定义体: (SmallHom.equiv W₂ W₂.Q).symm
    (Iso.homCongr ((CatCommSq.iso Φ.functor W₁.Q W₂.Q _).symm.app _)
      ((CatCommSq.iso Φ.functor W₁.Q W₂.Q _).symm.app _)
      ((Φ.localizedFunctor W₁.Q W₂.Q).map ((SmallHom.equiv W₁ W₁.Q) f)))

Depends on / 依赖: CatCommSq, CatCommSq.iso, Iso.homCongr, SmallHom, SmallHom.equiv, functor, homCongr, localizedFunctor, symm.app
-/
noncomputable def smallHomMap (f : SmallHom.{w} W₁ X Y) :
    SmallHom.{w'} W₂ (Φ.functor.obj X) (Φ.functor.obj Y) :=
  (SmallHom.equiv W₂ W₂.Q).symm
    (Iso.homCongr ((CatCommSq.iso Φ.functor W₁.Q W₂.Q _).symm.app _)
      ((CatCommSq.iso Φ.functor W₁.Q W₂.Q _).symm.app _)
      ((Φ.localizedFunctor W₁.Q W₂.Q).map ((SmallHom.equiv W₁ W₁.Q) f)))

set_option backward.defeqAttrib.useBackward true in
/--
lemma `equiv_smallHomMap` / 引理 `equiv_smallHomMap`

English:
lemma equiv_smallHomMap
  statement: (G : D₁ ⥤ D₂) (e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ G)
  proof: by
  obtain ⟨g, rfl⟩ := (SmallHom.equiv W₁ W₁.Q).symm.surjective f
  simp only [smallHomMap, Equiv.apply_symm_apply]
  let G' := Φ.localizedFunctor W₁.Q W₂.Q
  let β := CatCommSq.iso Φ.functor W₁.Q W₂.Q G'
  let E₁ := (uniq W₁.Q L₁ W₁).functor
  let α₁ : W₁.Q ⋙ E₁ ≅ L₁ := compUniqFunctor W₁.Q L₁ W₁


中文:
引理 equiv_smallHomMap
  结论: (G : D₁ ⥤ D₂) (e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ G)
  证明: by
  obtain ⟨g, rfl⟩ := (SmallHom.equiv W₁ W₁.Q).symm.surjective f
  simp only [smallHomMap, Equiv.apply_symm_apply]
  let G' := Φ.localizedFunctor W₁.Q W₂.Q
  let β := CatCommSq.iso Φ.functor W₁.Q W₂.Q G'
  let E₁ := (uniq W₁.Q L₁ W₁).functor
  let α₁ : W₁.Q ⋙ E₁ ≅ L₁ := compUniqFunctor W₁.Q L₁ W₁


Depends on / 依赖: CatCommSq, CatCommSq.iso, Equiv.apply_symm_apply, SmallHom, SmallHom.equiv, SmallHom.equiv_equiv_symm, apply_symm_apply, compUniqFunctor, equiv_equiv_symm, functor, inv.app, localizedFunctor, smallHomMap, surjective, symm.surjective
-/
lemma equiv_smallHomMap (G : D₁ ⥤ D₂) (e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ G)
    (f : SmallHom.{w} W₁ X Y) :
    (SmallHom.equiv W₂ L₂) (Φ.smallHomMap f) =
      e.hom.app X ≫ G.map (SmallHom.equiv W₁ L₁ f) ≫ e.inv.app Y := by
  obtain ⟨g, rfl⟩ := (SmallHom.equiv W₁ W₁.Q).symm.surjective f
  simp only [smallHomMap, Equiv.apply_symm_apply]
  let G' := Φ.localizedFunctor W₁.Q W₂.Q
  let β := CatCommSq.iso Φ.functor W₁.Q W₂.Q G'
  let E₁ := (uniq W₁.Q L₁ W₁).functor
  let α₁ : W₁.Q ⋙ E₁ ≅ L₁ := compUniqFunctor W₁.Q L₁ W₁
  let E₂ := (uniq W₂.Q L₂ W₂).functor
  let α₂ : W₂.Q ⋙ E₂ ≅ L₂ := compUniqFunctor W₂.Q L₂ W₂
  rw [SmallHom.equiv_equiv_symm W₁ W₁.Q L₁ E₁ α₁]; rw [SmallHom.equiv_equiv_symm W₂ W₂.Q L₂ E₂ α₂]
  change α₂.inv.app _ ≫ E₂.map (β.hom.app X ≫ G'.map g ≫ β.inv.app Y) ≫ _ = _
  let γ : G' ⋙ E₂ ≅ E₁ ⋙ G := liftNatIso W₁.Q W₁ (W₁.Q ⋙ G' ⋙ E₂) (W₁.Q ⋙ E₁ ⋙ G) _ _
    ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight β.symm E₂ ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ α₂ ≪≫ e ≪≫
      Functor.isoWhiskerRight α₁.symm G ≪≫ Functor.associator _ _ _)
  have hγ : forall (X : C₁), γ.hom.app (W₁.Q.obj X) =
      E₂.map (β.inv.app X) ≫ α₂.hom.app (Φ.functor.obj X) ≫
        e.hom.app X ≫ G.map (α₁.inv.app X) := fun X => by
    simp [γ, id_comp, comp_id]
  simp only [Functor.map_comp, ← NatIso.naturality_1 γ, ← Functor.comp_map,
    ← cancel_epi (e.inv.app X), ← cancel_epi (G.map (α₁.hom.app X)),
    ← cancel_epi (γ.hom.app (W₁.Q.obj X)), assoc, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app, Functor.map_id, id_comp,
    Iso.hom_inv_id_app_assoc]
  simp only [hγ, assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    Functor.map_id, id_comp, Iso.hom_inv_id_app_assoc,
    Iso.hom_inv_id_app, Functor.comp_obj, comp_id]

@[simp]
/--
lemma `smallHomMap_mk` / 引理 `smallHomMap_mk`

English:
lemma smallHomMap_mk
  given: (f : X ⟶ Y)
  proof: by
  apply (SmallHom.equiv W₂ W₂.Q).injective
  simp [Φ.equiv_smallHomMap W₁.Q W₂.Q (Φ.localizedFunctor W₁.Q W₂.Q) (CatCommSq.iso _ _ _ _)]

中文:
引理 smallHomMap_mk
  条件: (f : X ⟶ Y)
  证明: by
  apply (SmallHom.equiv W₂ W₂.Q).injective
  simp [Φ.equiv_smallHomMap W₁.Q W₂.Q (Φ.localizedFunctor W₁.Q W₂.Q) (CatCommSq.iso _ _ _ _)]

Depends on / 依赖: CatCommSq, CatCommSq.iso, SmallHom, SmallHom.equiv, equiv_smallHomMap, injective, localizedFunctor
-/
lemma smallHomMap_mk (f : X ⟶ Y) :
    Φ.smallHomMap (SmallHom.mk _ f) =
      SmallHom.mk _ (Φ.functor.map f) := by
  apply (SmallHom.equiv W₂ W₂.Q).injective
  simp [Φ.equiv_smallHomMap W₁.Q W₂.Q (Φ.localizedFunctor W₁.Q W₂.Q) (CatCommSq.iso _ _ _ _)]

end

section

variable {X Y Z : C₁}

variable [HasSmallLocalizedHom.{w} W₁ X Y] [HasSmallLocalizedHom.{w} W₁ Y Z]
  [HasSmallLocalizedHom.{w} W₁ X Z]
  [HasSmallLocalizedHom.{w'} W₂ (Φ.functor.obj X) (Φ.functor.obj Y)]
  [HasSmallLocalizedHom.{w'} W₂ (Φ.functor.obj Y) (Φ.functor.obj Z)]
  [HasSmallLocalizedHom.{w'} W₂ (Φ.functor.obj X) (Φ.functor.obj Z)]

/--
lemma `smallHomMap_comp` / 引理 `smallHomMap_comp`

English:
lemma smallHomMap_comp
  given: (f : SmallHom.{w} W₁ X Y) (g : SmallHom.{w} W₁ Y Z)
  proof: by
  apply (SmallHom.equiv W₂ W₂.Q).injective
  simp [Φ.equiv_smallHomMap W₁.Q W₂.Q (Φ.localizedFunctor W₁.Q W₂.Q) (CatCommSq.iso _ _ _ _),
    SmallHom.equiv_comp]

中文:
引理 smallHomMap_comp
  条件: (f : SmallHom.{w} W₁ X Y) (g : SmallHom.{w} W₁ Y Z)
  证明: by
  apply (SmallHom.equiv W₂ W₂.Q).injective
  simp [Φ.equiv_smallHomMap W₁.Q W₂.Q (Φ.localizedFunctor W₁.Q W₂.Q) (CatCommSq.iso _ _ _ _),
    SmallHom.equiv_comp]

Depends on / 依赖: CatCommSq, CatCommSq.iso, SmallHom, SmallHom.equiv, SmallHom.equiv_comp, equiv_comp, equiv_smallHomMap, injective, localizedFunctor
-/
lemma smallHomMap_comp (f : SmallHom.{w} W₁ X Y) (g : SmallHom.{w} W₁ Y Z) :
    Φ.smallHomMap (f.comp g) = (Φ.smallHomMap f).comp (Φ.smallHomMap g) := by
  apply (SmallHom.equiv W₂ W₂.Q).injective
  simp [Φ.equiv_smallHomMap W₁.Q W₂.Q (Φ.localizedFunctor W₁.Q W₂.Q) (CatCommSq.iso _ _ _ _),
    SmallHom.equiv_comp]

end

section

variable {X Y : C₁} [HasSmallLocalizedHom.{w} W₁ X Y] {X' Y' : C₂}
  [HasSmallLocalizedHom.{w'} W₂ X' X']
  [HasSmallLocalizedHom.{w'} W₂ X' Y']
  [HasSmallLocalizedHom.{w'} W₂ Y' Y']
  (eX : Φ.functor.obj X ≅ X') (eY : Φ.functor.obj Y ≅ Y')

/--
Definition of `smallHomMap'` / `smallHomMap'` 的定义

English:
definition smallHomMap'
  signature: (f : SmallHom.{w} W₁ X Y)
  body: have := hasSmallLocalizedHom_of_isos.{w'} W₂ eX.symm eY.symm
  have := hasSmallLocalizedHom_of_isos.{w'} W₂ eX.symm (Iso.refl Y')
  have := hasSmallLocalizedHom_of_isos.{w'} W₂ eY.symm (Iso.refl Y')
  have := hasSmallLocalizedHom_of_isos.{w'} W₂ (Iso.refl X') eX.symm
  (SmallHom.mk _ eX.inv).comp ((

中文:
定义 smallHomMap'
  签名: (f : SmallHom.{w} W₁ X Y)
  定义体: have := hasSmallLocalizedHom_of_isos.{w'} W₂ eX.symm eY.symm
  have := hasSmallLocalizedHom_of_isos.{w'} W₂ eX.symm (Iso.refl Y')
  have := hasSmallLocalizedHom_of_isos.{w'} W₂ eY.symm (Iso.refl Y')
  have := hasSmallLocalizedHom_of_isos.{w'} W₂ (Iso.refl X') eX.symm
  (SmallHom.mk _ eX.inv).comp ((

Depends on / 依赖: Iso.refl, SmallHom, SmallHom.mk, eX.inv, eX.symm, eY.hom, eY.symm, hasSmallLocalizedHom_of_isos, smallHomMap
-/
noncomputable def smallHomMap' (f : SmallHom.{w} W₁ X Y) :
    SmallHom.{w'} W₂ X' Y' :=
  have := hasSmallLocalizedHom_of_isos.{w'} W₂ eX.symm eY.symm
  have := hasSmallLocalizedHom_of_isos.{w'} W₂ eX.symm (Iso.refl Y')
  have := hasSmallLocalizedHom_of_isos.{w'} W₂ eY.symm (Iso.refl Y')
  have := hasSmallLocalizedHom_of_isos.{w'} W₂ (Iso.refl X') eX.symm
  (SmallHom.mk _ eX.inv).comp ((Φ.smallHomMap f).comp (SmallHom.mk _ eY.hom))

set_option backward.defeqAttrib.useBackward true in
/--
lemma `equiv_smallHomMap'` / 引理 `equiv_smallHomMap'`

English:
lemma equiv_smallHomMap'
  statement: (G : D₁ ⥤ D₂) (e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ G)
  proof: by
  have := hasSmallLocalizedHom_of_isos.{w'} W₂ eY.symm (Iso.refl Y')
  simp [smallHomMap', SmallHom.equiv_comp, Φ.equiv_smallHomMap L₁ L₂ G e]

@[simp]

中文:
引理 equiv_smallHomMap'
  结论: (G : D₁ ⥤ D₂) (e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ G)
  证明: by
  have := hasSmallLocalizedHom_of_isos.{w'} W₂ eY.symm (Iso.refl Y')
  simp [smallHomMap', SmallHom.equiv_comp, Φ.equiv_smallHomMap L₁ L₂ G e]

@[simp]

Depends on / 依赖: Iso.refl, SmallHom, SmallHom.equiv_comp, eY.symm, equiv_comp, equiv_smallHomMap, hasSmallLocalizedHom_of_isos, smallHomMap
-/
lemma equiv_smallHomMap' (G : D₁ ⥤ D₂) (e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ G)
    (f : SmallHom.{w} W₁ X Y) :
    SmallHom.equiv W₂ L₂ (Φ.smallHomMap' eX eY f) =
      L₂.map eX.inv ≫ e.hom.app X ≫ G.map (SmallHom.equiv W₁ L₁ f) ≫
        e.inv.app Y ≫ L₂.map eY.hom := by
  have := hasSmallLocalizedHom_of_isos.{w'} W₂ eY.symm (Iso.refl Y')
  simp [smallHomMap', SmallHom.equiv_comp, Φ.equiv_smallHomMap L₁ L₂ G e]

@[simp]
/--
lemma `smallHomMap'_mk` / 引理 `smallHomMap'_mk`

English:
lemma smallHomMap'_mk
  given: (f : X ⟶ Y)
  proof: by
  simp [smallHomMap', SmallHom.mk_comp_mk]

中文:
引理 smallHomMap'_mk
  条件: (f : X ⟶ Y)
  证明: by
  simp [smallHomMap', SmallHom.mk_comp_mk]
-/
lemma smallHomMap'_mk (f : X ⟶ Y) :
    Φ.smallHomMap' eX eY (SmallHom.mk _ f) =
      SmallHom.mk _ (eX.inv ≫ Φ.functor.map f ≫ eY.hom) := by
  simp [smallHomMap', SmallHom.mk_comp_mk]

end

section

variable {X Y Z : C₁} [HasSmallLocalizedHom.{w} W₁ X Y] [HasSmallLocalizedHom.{w} W₁ Y Z]
  [HasSmallLocalizedHom.{w} W₁ X Z] {X' Y' Z' : C₂}
  [HasSmallLocalizedHom.{w'} W₂ X' X'] [HasSmallLocalizedHom.{w'} W₂ Y' Y']
  [HasSmallLocalizedHom.{w'} W₂ Z' Z'] [HasSmallLocalizedHom.{w'} W₂ X' Y']
  [HasSmallLocalizedHom.{w'} W₂ Y' Z'] [HasSmallLocalizedHom.{w'} W₂ X' Z']
  (eX : Φ.functor.obj X ≅ X') (eY : Φ.functor.obj Y ≅ Y') (eZ : Φ.functor.obj Z ≅ Z')

/--
lemma `smallHomMap'_comp` / 引理 `smallHomMap'_comp`

English:
lemma smallHomMap'_comp
  given: (f : SmallHom.{w} W₁ X Y) (g : SmallHom.{w} W₁ Y Z)
  proof: by
  have := hasSmallLocalizedHom_of_isos.{w'} W₂ eX.symm eY.symm
  have := hasSmallLocalizedHom_of_isos.{w'} W₂ eY.symm (Iso.refl Y')
  have := hasSmallLocalizedHom_of_isos.{w'} W₂ eX.symm (Iso.refl Z')
  have := hasSmallLocalizedHom_of_isos.{w'} W₂ eY.symm eZ.symm
  have := hasSmallLocalizedHom_of

中文:
引理 smallHomMap'_comp
  条件: (f : SmallHom.{w} W₁ X Y) (g : SmallHom.{w} W₁ Y Z)
  证明: by
  have := hasSmallLocalizedHom_of_isos.{w'} W₂ eX.symm eY.symm
  have := hasSmallLocalizedHom_of_isos.{w'} W₂ eY.symm (Iso.refl Y')
  have := hasSmallLocalizedHom_of_isos.{w'} W₂ eX.symm (Iso.refl Z')
  have := hasSmallLocalizedHom_of_isos.{w'} W₂ eY.symm eZ.symm
  have := hasSmallLocalizedHom_of
-/
lemma smallHomMap'_comp (f : SmallHom.{w} W₁ X Y) (g : SmallHom.{w} W₁ Y Z) :
    Φ.smallHomMap' eX eZ (f.comp g) =
      (Φ.smallHomMap' eX eY f).comp (Φ.smallHomMap' eY eZ g) := by
  have := hasSmallLocalizedHom_of_isos.{w'} W₂ eX.symm eY.symm
  have := hasSmallLocalizedHom_of_isos.{w'} W₂ eY.symm (Iso.refl Y')
  have := hasSmallLocalizedHom_of_isos.{w'} W₂ eX.symm (Iso.refl Z')
  have := hasSmallLocalizedHom_of_isos.{w'} W₂ eY.symm eZ.symm
  have := hasSmallLocalizedHom_of_isos.{w'} W₂ eY.symm (Iso.refl Z')
  have := hasSmallLocalizedHom_of_isos.{w'} W₂ (Iso.refl Y') eY.symm
  have := hasSmallLocalizedHom_of_isos.{w'} W₂ eY.symm eY.symm
  simp only [smallHomMap', smallHomMap_comp, SmallHom.comp_assoc]
  congr 2
  rw [← SmallHom.comp_assoc]; rw [SmallHom.mk_comp_mk]; rw [eY.hom_inv_id]; rw [SmallHom.mk_id_comp]

end

end LocalizerMorphism

end CategoryTheory
