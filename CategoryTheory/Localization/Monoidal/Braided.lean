/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Localization.Monoidal.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Multifunctor

/-!

# Localization of symmetric monoidal categories

Let `C` be a monoidal category equipped with a class of morphisms `W` which
is compatible with the monoidal category structure. The file
`Mathlib.CategoryTheory.Localization.Monoidal.Basic` constructs a monoidal structure on
the localized on `D` such that the localization functor is monoidal.

In this file we promote this monoidal structure to a braided structure in the case where `C` is
braided, in such a way that the localization functor is braided. If `C` is symmetric monoidal, then
the monoidal structure on `D` is also symmetric.
-/

@[expose] public section

open CategoryTheory Category MonoidalCategory BraidedCategory Functor

namespace CategoryTheory.Localization.Monoidal

variable {C D : Type*} [Category* C] [Category* D] (L : C ⥤ D) (W : MorphismProperty C)
  [MonoidalCategory C] [W.IsMonoidal] [L.IsLocalization W]
  {unit : D} (ε : L.obj (𝟙_ C) ≅ unit)

local notation "L'" => toMonoidalCategory L W ε

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (L').IsLocalization W
  body: inferInstanceAs (L.IsLocalization W)

中文:
实例 :
  签名: (L').是Localization W
  定义体: inferInstanceAs (L.IsLocalization W)

Depends on / 依赖: IsLocalization, L.IsLocalization
-/
instance : (L').IsLocalization W := inferInstanceAs (L.IsLocalization W)

section Braided

variable [BraidedCategory C]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Lifting₂ L' L' W W ((curriedTensor C).flip ⋙ (whiskeringRight C C
  body: inferInstanceAs (Lifting₂ L' L' W W (((curriedTensor C) ⋙ (whiskeringRight C C
    (LocalizedMonoidal L W ε)).obj L')).flip (tensorBifunctor L W ε).flip)

中文:
实例 :
  签名: Lifting₂ L' L' W W ((curriedTensor C).flip ⋙ (whiskeringRight C C
  定义体: inferInstanceAs (Lifting₂ L' L' W W (((curriedTensor C) ⋙ (whiskeringRight C C
    (LocalizedMonoidal L W ε)).obj L')).flip (tensorBifunctor L W ε).flip)

Depends on / 依赖: LocalizedMonoidal, curriedTensor, tensorBifunctor, whiskeringRight
-/
noncomputable instance : Lifting₂ L' L' W W ((curriedTensor C).flip ⋙ (whiskeringRight C C
    (LocalizedMonoidal L W ε)).obj L') (tensorBifunctor L W ε).flip :=
  inferInstanceAs (Lifting₂ L' L' W W (((curriedTensor C) ⋙ (whiskeringRight C C
    (LocalizedMonoidal L W ε)).obj L')).flip (tensorBifunctor L W ε).flip)

/--
Definition of `braidingNatIso` / `braidingNatIso` 的定义

English:
definition braidingNatIso
  signature: : tensorBifunctor L W ε ≅ (tensorBifunctor L W ε).flip
  body: lift₂NatIso L' L' W W
    ((curriedTensor C) ⋙ (whiskeringRight C C
      (LocalizedMonoidal L W ε)).obj L')
    (((curriedTensor C).flip ⋙ (whiskeringRight C C
      (LocalizedMonoidal L W ε)).obj L'))
    _ _ (isoWhiskerRight (curriedBraidingNatIso C) _)

中文:
定义 braiding自然数Iso
  签名: : tensorBifunctor L W ε ≅ (tensorBifunctor L W ε).flip
  定义体: lift₂NatIso L' L' W W
    ((curriedTensor C) ⋙ (whiskeringRight C C
      (LocalizedMonoidal L W ε)).obj L')
    (((curriedTensor C).flip ⋙ (whiskeringRight C C
      (LocalizedMonoidal L W ε)).obj L'))
    _ _ (isoWhiskerRight (curriedBraidingNatIso C) _)

Depends on / 依赖: LocalizedMonoidal, curriedBraidingNatIso, curriedTensor, isoWhiskerRight, whiskeringRight
-/
noncomputable def braidingNatIso : tensorBifunctor L W ε ≅ (tensorBifunctor L W ε).flip :=
  lift₂NatIso L' L' W W
    ((curriedTensor C) ⋙ (whiskeringRight C C
      (LocalizedMonoidal L W ε)).obj L')
    (((curriedTensor C).flip ⋙ (whiskeringRight C C
      (LocalizedMonoidal L W ε)).obj L'))
    _ _ (isoWhiskerRight (curriedBraidingNatIso C) _)

/--
lemma `braidingNatIso_hom_app` / 引理 `braidingNatIso_hom_app`

English:
lemma braidingNatIso_hom_app
  given: (X Y : C)
  proof: by
  simp [braidingNatIso, lift₂NatIso]
  rfl

#adaptation_note

中文:
引理 braiding自然数Iso_hom_app
  条件: (X Y : C)
  证明: by
  simp [braidingNatIso, lift₂NatIso]
  rfl

#adaptation_note

Depends on / 依赖: braidingNatIso
-/
lemma braidingNatIso_hom_app (X Y : C) :
    ((braidingNatIso L W ε).hom.app ((L').obj X)).app ((L').obj Y) =
      (Functor.LaxMonoidal.μ (L') X Y) ≫
        (L').map (β_ X Y).hom ≫
          (Functor.OplaxMonoidal.δ (L') Y X) := by
  simp [braidingNatIso, lift₂NatIso]
  rfl

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/--
lemma `braidingNatIso_hom_app_naturality_μ_left` / 引理 `braidingNatIso_hom_app_naturality_μ_left`

English:
lemma braidingNatIso_hom_app_naturality_μ_left
  given: (X Y Z : C)
  proof: (((braidingNatIso L W ε).hom.app ((L').obj X)).naturality ((Functor.LaxMonoidal.μ (L') Y Z))).symm

#adaptation_note

中文:
引理 braiding自然数Iso_hom_app_naturality_μ_left
  条件: (X Y Z : C)
  证明: (((braidingNatIso L W ε).hom.app ((L').obj X)).naturality ((Functor.LaxMonoidal.μ (L') Y Z))).symm

#adaptation_note

Depends on / 依赖: Functor, Functor.LaxMonoidal, LaxMonoidal, braidingNatIso, hom.app, naturality
-/
lemma braidingNatIso_hom_app_naturality_μ_left (X Y Z : C) :
    ((braidingNatIso L W ε).hom.app ((L').obj X)).app ((L').obj Y otimes (L').obj Z) ≫
      (Functor.LaxMonoidal.μ (L') Y Z) ▷ (L').obj X =
        (L').obj X ◁ (Functor.LaxMonoidal.μ (L') Y Z) ≫
          ((braidingNatIso L W ε).hom.app ((L').obj X)).app ((L').obj (Y otimes Z)) :=
  (((braidingNatIso L W ε).hom.app ((L').obj X)).naturality ((Functor.LaxMonoidal.μ (L') Y Z))).symm

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/--
lemma `braidingNatIso_hom_app_naturality_μ_right` / 引理 `braidingNatIso_hom_app_naturality_μ_right`

English:
lemma braidingNatIso_hom_app_naturality_μ_right
  given: (X Y Z : C)
  proof: (NatTrans.congr_app ((braidingNatIso L W ε).hom.naturality
    ((Functor.LaxMonoidal.μ (L') X Y))) ((L').obj Z)).symm

中文:
引理 braiding自然数Iso_hom_app_naturality_μ_right
  条件: (X Y Z : C)
  证明: (NatTrans.congr_app ((braidingNatIso L W ε).hom.naturality
    ((Functor.LaxMonoidal.μ (L') X Y))) ((L').obj Z)).symm

Depends on / 依赖: Functor, Functor.LaxMonoidal, LaxMonoidal, NatTrans, NatTrans.congr_app, braidingNatIso, congr_app, hom.naturality, naturality
-/
lemma braidingNatIso_hom_app_naturality_μ_right (X Y Z : C) :
    ((braidingNatIso L W ε).hom.app ((L').obj X otimes (L').obj Y)).app ((L').obj Z) ≫
      (L').obj Z ◁ (Functor.LaxMonoidal.μ (L') X Y) =
        (Functor.LaxMonoidal.μ (L') X Y) ▷ (L').obj Z ≫
          ((braidingNatIso L W ε).hom.app ((L').obj (X otimes Y))).app ((L').obj Z) :=
  (NatTrans.congr_app ((braidingNatIso L W ε).hom.naturality
    ((Functor.LaxMonoidal.μ (L') X Y))) ((L').obj Z)).symm

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `map_hexagon_forward` / 引理 `map_hexagon_forward`

English:
lemma map_hexagon_forward
  given: (X Y Z : C)
  proof: by
  simp only [associator_hom, Iso.app_hom, braidingNatIso_hom_app]
  slice_rhs 0 4 =>
    simp only [Functor.flip_obj_obj, Functor.CoreMonoidal.toMonoidal_toLaxMonoidal,
      Functor.CoreMonoidal.toMonoidal_toOplaxMonoidal, comp_whiskerRight, assoc,
      Functor.Monoidal.whiskerRight_δ_μ_assoc, Functor.LaxMonoidal.μ_natural_left]
  slice_lhs 6 7 =>
    rw [braidingNatIso_hom_app_naturality_μ_left]; rw [braidingNatIso_hom_app]
  simp

中文:
引理 map_hexagon_forward
  条件: (X Y Z : C)
  证明: by
  simp only [associator_hom, Iso.app_hom, braidingNatIso_hom_app]
  slice_rhs 0 4 =>
    simp only [Functor.flip_obj_obj, Functor.CoreMonoidal.toMonoidal_toLaxMonoidal,
      Functor.CoreMonoidal.toMonoidal_toOplaxMonoidal, comp_whiskerRight, assoc,
      Functor.Monoidal.whiskerRight_δ_μ_assoc, Functor.LaxMonoidal.μ_natural_left]
  slice_lhs 6 7 =>
    rw [braidingNatIso_hom_app_naturality_μ_left]; rw [braidingNatIso_hom_app]
  simp

Depends on / 依赖: CoreMonoidal, Functor, Functor.CoreMonoidal.toMonoidal_toLaxMonoidal, Functor.CoreMonoidal.toMonoidal_toOplaxMonoidal, Functor.LaxMonoidal, Functor.Monoidal.whiskerRight_, Functor.flip_obj_obj, Iso.app_hom, LaxMonoidal, Monoidal, app_hom, associator_hom, braidingNatIso_hom_app, comp_whiskerRight, flip_obj_obj, linear_of_localization, slice_lhs, slice_rhs, toMonoidal_toLaxMonoidal, toMonoidal_toOplaxMonoidal
-/
lemma map_hexagon_forward (X Y Z : C) :
    (α_ ((L').obj X) ((L').obj Y) ((L').obj Z)).hom ≫
      (((braidingNatIso L W ε).app ((L').obj X)).app (((L').obj Y) otimes ((L').obj Z))).hom ≫
        (α_ ((L').obj Y) ((L').obj Z) ((L').obj X)).hom =
      (((braidingNatIso L W ε).app ((L').obj X)).app ((L').obj Y)).hom ▷ ((L').obj Z) ≫
        (α_ ((L').obj Y) ((L').obj X) ((L').obj Z)).hom ≫
        ((L').obj Y) ◁ (((braidingNatIso L W ε).app ((L').obj X)).app ((L').obj Z)).hom := by
  simp only [associator_hom, Iso.app_hom, braidingNatIso_hom_app]
  slice_rhs 0 4 =>
    simp only [Functor.flip_obj_obj, Functor.CoreMonoidal.toMonoidal_toLaxMonoidal,
      Functor.CoreMonoidal.toMonoidal_toOplaxMonoidal, comp_whiskerRight, assoc,
      Functor.Monoidal.whiskerRight_δ_μ_assoc, Functor.LaxMonoidal.μ_natural_left]
  slice_lhs 6 7 =>
    rw [braidingNatIso_hom_app_naturality_μ_left]; rw [braidingNatIso_hom_app]
  simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `map_hexagon_reverse` / 引理 `map_hexagon_reverse`

English:
lemma map_hexagon_reverse
  given: (X Y Z : C)
  proof: by
  simp only [associator_inv, Iso.app_hom, braidingNatIso_hom_app]
  slice_rhs 0 4 =>
    simp only [Functor.flip_obj_obj, Functor.CoreMonoidal.toMonoidal_toLaxMonoidal,
      Functor.CoreMonoidal.toMonoidal_toOplaxMonoidal, MonoidalCategory.whiskerLeft_comp, assoc,
      Functor.Monoidal.whiskerLeft_δ_μ, comp_id]
  slice_lhs 6 7 =>
    rw [braidingNatIso_hom_app_naturality_μ_right]; rw [braidingNatIso_hom_app]
  simp

中文:
引理 map_hexagon_reverse
  条件: (X Y Z : C)
  证明: by
  simp only [associator_inv, Iso.app_hom, braidingNatIso_hom_app]
  slice_rhs 0 4 =>
    simp only [Functor.flip_obj_obj, Functor.CoreMonoidal.toMonoidal_toLaxMonoidal,
      Functor.CoreMonoidal.toMonoidal_toOplaxMonoidal, MonoidalCategory.whiskerLeft_comp, assoc,
      Functor.Monoidal.whiskerLeft_δ_μ, comp_id]
  slice_lhs 6 7 =>
    rw [braidingNatIso_hom_app_naturality_μ_right]; rw [braidingNatIso_hom_app]
  simp

Depends on / 依赖: CoreMonoidal, Functor, Functor.CoreMonoidal.toMonoidal_toLaxMonoidal, Functor.CoreMonoidal.toMonoidal_toOplaxMonoidal, Functor.Monoidal.whiskerLeft_, Functor.flip_obj_obj, Iso.app_hom, Monoidal, MonoidalCategory, MonoidalCategory.whiskerLeft_comp, app_hom, associator_inv, braidingNatIso_hom_app, comp_id, flip_obj_obj, slice_lhs, slice_rhs, toMonoidal_toLaxMonoidal, toMonoidal_toOplaxMonoidal, whiskerLeft_comp
-/
lemma map_hexagon_reverse (X Y Z : C) :
    (α_ ((L').obj X) ((L').obj Y) ((L').obj Z)).inv ≫
      (((braidingNatIso L W ε).app ((L').obj X otimes (L').obj Y)).app ((L').obj Z)).hom ≫
        (α_ ((L').obj Z) ((L').obj X) ((L').obj Y)).inv =
      ((L').obj X) ◁ (((braidingNatIso L W ε).app ((L').obj Y)).app ((L').obj Z)).hom ≫
        (α_ ((L').obj X) ((L').obj Z) ((L').obj Y)).inv ≫
        (((braidingNatIso L W ε).app ((L').obj X)).app ((L').obj Z)).hom ▷ ((L').obj Y) := by
  simp only [associator_inv, Iso.app_hom, braidingNatIso_hom_app]
  slice_rhs 0 4 =>
    simp only [Functor.flip_obj_obj, Functor.CoreMonoidal.toMonoidal_toLaxMonoidal,
      Functor.CoreMonoidal.toMonoidal_toOplaxMonoidal, MonoidalCategory.whiskerLeft_comp, assoc,
      Functor.Monoidal.whiskerLeft_δ_μ, comp_id]
  slice_lhs 6 7 =>
    rw [braidingNatIso_hom_app_naturality_μ_right]; rw [braidingNatIso_hom_app]
  simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: BraidedCategory (LocalizedMonoidal L W ε)
  body: by
  refine .ofBifunctor (braidingNatIso L W ε) ?_ ?_
  · apply natTrans₃_ext (L') (L') (L') W W W
    simpa using! map_hexagon_forward _ _ _
  · apply natTrans₃_ext (L') (L') (L') W W W
    simpa using! map_hexagon_reverse _ _ _

中文:
实例 :
  签名: 辫范畴 (LocalizedMonoidal L W ε)
  定义体: by
  refine .ofBifunctor (braidingNatIso L W ε) ?_ ?_
  · apply natTrans₃_ext (L') (L') (L') W W W
    simpa using! map_hexagon_forward _ _ _
  · apply natTrans₃_ext (L') (L') (L') W W W
    simpa using! map_hexagon_reverse _ _ _

Depends on / 依赖: braidingNatIso, map_hexagon_forward, map_hexagon_reverse, ofBifunctor
-/
noncomputable instance : BraidedCategory (LocalizedMonoidal L W ε) := by
  refine .ofBifunctor (braidingNatIso L W ε) ?_ ?_
  · apply natTrans₃_ext (L') (L') (L') W W W
    simpa using! map_hexagon_forward _ _ _
  · apply natTrans₃_ext (L') (L') (L') W W W
    simpa using! map_hexagon_reverse _ _ _

/--
lemma `β_hom_app` / 引理 `β_hom_app`

English:
lemma β_hom_app
  given: (X Y : C)
  proof: braidingNatIso_hom_app L W ε X Y

中文:
引理 β_hom_app
  条件: (X Y : C)
  证明: braidingNatIso_hom_app L W ε X Y

Depends on / 依赖: braidingNatIso_hom_app
-/
lemma β_hom_app (X Y : C) :
    (β_ ((L').obj X) ((L').obj Y)).hom =
      (Functor.LaxMonoidal.μ (L') X Y) ≫
        (L').map (β_ X Y).hom ≫
          (Functor.OplaxMonoidal.δ (L') Y X) :=
  braidingNatIso_hom_app L W ε X Y

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (toMonoidalCategory L W ε).Braided
  body: by simp [β_hom_app]

中文:
实例 :
  签名: (toMonoidalCategory L W ε).辫
  定义体: by simp [β_hom_app]
-/
noncomputable instance : (toMonoidalCategory L W ε).Braided where
  braided X Y := by simp [β_hom_app]

end Braided

section Symmetric

variable [SymmetricCategory C]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SymmetricCategory (LocalizedMonoidal L W ε)
  body: by
  refine .ofCurried (natTrans₂_ext (L') (L') W W fun X Y => ?_)
  simp [-Functor.map_braiding, β_hom_app, ← Functor.map_comp_assoc]

中文:
实例 :
  签名: 对称范畴 (LocalizedMonoidal L W ε)
  定义体: by
  refine .ofCurried (natTrans₂_ext (L') (L') W W fun X Y => ?_)
  simp [-Functor.map_braiding, β_hom_app, ← Functor.map_comp_assoc]

Depends on / 依赖: Functor, Functor.map_braiding, Functor.map_comp_assoc, map_braiding, map_comp_assoc, ofCurried
-/
noncomputable instance : SymmetricCategory (LocalizedMonoidal L W ε) := by
  refine .ofCurried (natTrans₂_ext (L') (L') W W fun X Y => ?_)
  simp [-Functor.map_braiding, β_hom_app, ← Functor.map_comp_assoc]

end Symmetric

end CategoryTheory.Localization.Monoidal
