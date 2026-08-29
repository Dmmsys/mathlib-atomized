/-
Copyright (c) 2025 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Module.CharacterModule
public import Mathlib.Algebra.Group.Equiv.Basic

/-!
# Existence of "big" colimits in the category of additive commutative groups

If `F : J ⥤ AddCommGrpCat.{w}` is a functor, we show that `F` admits a colimit if and only
if `Colimits.Quot F` (the quotient of the direct sum of the commutative groups `F.obj j`
by the relations given by the morphisms in the diagram) is `w`-small.

-/

public section

universe w u v

open CategoryTheory Limits

namespace AddCommGrpCat

variable {J : Type u} [Category.{v} J] {F : J ⥤ AddCommGrpCat.{w}} (c : Cocone F)

open Colimits

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `isColimit_iff_bijective_desc` / 引理 `isColimit_iff_bijective_desc`

English:
lemma isColimit_iff_bijective_desc
  given: [DecidableEq J]
  proof: by
  refine ⟨fun ⟨hc⟩ => ?_, fun h => Nonempty.intro (isColimit_of_bijective_desc F c h)⟩
  change Function.Bijective (Quot.desc F c).toIntLinearMap
  rw [← CharacterModule.dual_bijective_iff_bijective]
  refine ⟨fun χ ψ eq => ?_, fun χ => ?_⟩
  · apply AddEquiv.ulift.symm.addMonoidHomCongrRightEquiv.injective
    apply ofHom_injective
    refine hc.hom_ext (fun j => ?_)
    ext x
    erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, ← Quot.ι_desc _ c j x]
    exact DFunLike.congr_fun eq (Quot.ι F j x)
  · set c' : Cocone F :=
      { pt := AddCommGrpCat.of (ULift (AddCircle (1 : Rat)))
        ι :=
          { app j := AddCommGrpCat.ofHom (((@AddEquiv.ulift _ _).symm.toAddMonoidHom.comp χ).comp
                       (Quot.ι F j))
            naturality {j j'} u := by
              ext
              dsimp
              rw [Quot.map_ι F (f := u)] } }
    use AddEquiv.ulift.toAddMonoidHom.comp (hc.desc c').hom
    refine Quot.addMonoidHom_ext _ (fun j x => ?_)
    dsimp
    rw [Quot.ι_desc]
    change AddEquiv.ulift ((c.ι.app j ≫ hc.desc c') x) = _
    rw [hc.fac]
    dsimp [c']
    rw [AddEquiv.apply_symm_apply]

中文:
引理 isColimit_iff_bijective_desc
  条件: [DecidableEq J]
  证明: by
  refine ⟨fun ⟨hc⟩ => ?_, fun h => Nonempty.intro (isColimit_of_bijective_desc F c h)⟩
  change Function.Bijective (Quot.desc F c).toIntLinearMap
  rw [← CharacterModule.dual_bijective_iff_bijective]
  refine ⟨fun χ ψ eq => ?_, fun χ => ?_⟩
  · apply AddEquiv.ulift.symm.addMonoidHomCongrRightEquiv.injective
    apply ofHom_injective
    refine hc.hom_ext (fun j => ?_)
    ext x
    erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, ← Quot.ι_desc _ c j x]
    exact DFunLike.congr_fun eq (Quot.ι F j x)
  · set c' : Cocone F :=
      { pt := AddCommGrpCat.of (ULift (AddCircle (1 : Rat)))
        ι :=
          { app j := AddCommGrpCat.ofHom (((@AddEquiv.ulift _ _).symm.toAddMonoidHom.comp χ).comp
                       (Quot.ι F j))
            naturality {j j'} u := by
              ext
              dsimp
              rw [Quot.map_ι F (f := u)] } }
    use AddEquiv.ulift.toAddMonoidHom.comp (hc.desc c').hom
    refine Quot.addMonoidHom_ext _ (fun j x => ?_)
    dsimp
    rw [Quot.ι_desc]
    change AddEquiv.ulift ((c.ι.app j ≫ hc.desc c') x) = _
    rw [hc.fac]
    dsimp [c']
    rw [AddEquiv.apply_symm_apply]

Depends on / 依赖: AddEquiv, AddEquiv.ulift.symm.addMonoidHomCongrRightEquiv.injective, Bijective, CharacterModule, CharacterModule.dual_bijective_iff_bijective, ConcreteCategory, ConcreteCategory.comp_apply, DFunLike, DFunLike.congr_fun, Function, Function.Bijective, Nonempty, Nonempty.intro, Quot.desc, addMonoidHomCongrRightEquiv, comp_apply, congr_fun, dual_bijective_iff_bijective, hc.hom_ext, hom_ext
-/
lemma isColimit_iff_bijective_desc [DecidableEq J] :
     Nonempty (IsColimit c) ↔ Function.Bijective (Quot.desc F c) := by
  refine ⟨fun ⟨hc⟩ => ?_, fun h => Nonempty.intro (isColimit_of_bijective_desc F c h)⟩
  change Function.Bijective (Quot.desc F c).toIntLinearMap
  rw [← CharacterModule.dual_bijective_iff_bijective]
  refine ⟨fun χ ψ eq => ?_, fun χ => ?_⟩
  · apply AddEquiv.ulift.symm.addMonoidHomCongrRightEquiv.injective
    apply ofHom_injective
    refine hc.hom_ext (fun j => ?_)
    ext x
    erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, ← Quot.ι_desc _ c j x]
    exact DFunLike.congr_fun eq (Quot.ι F j x)
  · set c' : Cocone F :=
      { pt := AddCommGrpCat.of (ULift (AddCircle (1 : Rat)))
        ι :=
          { app j := AddCommGrpCat.ofHom (((@AddEquiv.ulift _ _).symm.toAddMonoidHom.comp χ).comp
                       (Quot.ι F j))
            naturality {j j'} u := by
              ext
              dsimp
              rw [Quot.map_ι F (f := u)] } }
    use AddEquiv.ulift.toAddMonoidHom.comp (hc.desc c').hom
    refine Quot.addMonoidHom_ext _ (fun j x => ?_)
    dsimp
    rw [Quot.ι_desc]
    change AddEquiv.ulift ((c.ι.app j ≫ hc.desc c') x) = _
    rw [hc.fac]
    dsimp [c']
    rw [AddEquiv.apply_symm_apply]

/--
lemma `hasColimit_iff_small_quot` / 引理 `hasColimit_iff_small_quot`

English:
lemma hasColimit_iff_small_quot
  given: [DecidableEq J]
  statement: HasColimit F ↔ Small.{w} (Quot F)
  proof: ⟨fun _ => Small.mk ⟨_, ⟨(Equiv.ofBijective _ ((isColimit_iff_bijective_desc (colimit.cocone F)).mp
    ⟨colimit.isColimit _⟩))⟩⟩, hasColimit_of_small_quot F⟩

中文:
引理 hasColimit_iff_small_quot
  条件: [DecidableEq J]
  结论: 有余极限 F ↔ Small.{w} (商 F)
  证明: ⟨fun _ => Small.mk ⟨_, ⟨(Equiv.ofBijective _ ((isColimit_iff_bijective_desc (colimit.cocone F)).mp
    ⟨colimit.isColimit _⟩))⟩⟩, hasColimit_of_small_quot F⟩

Depends on / 依赖: Equiv.ofBijective, Small.mk, cocone, colimit, colimit.cocone, colimit.isColimit, hasColimit_of_small_quot, isColimit, isColimit_iff_bijective_desc, ofBijective
-/
lemma hasColimit_iff_small_quot [DecidableEq J] : HasColimit F ↔ Small.{w} (Quot F) :=
  ⟨fun _ => Small.mk ⟨_, ⟨(Equiv.ofBijective _ ((isColimit_iff_bijective_desc (colimit.cocone F)).mp
    ⟨colimit.isColimit _⟩))⟩⟩, hasColimit_of_small_quot F⟩

end AddCommGrpCat
