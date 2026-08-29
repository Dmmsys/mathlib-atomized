/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Johan Commelin
-/
module

public import Mathlib.Analysis.Normed.Group.SemiNormedGrp
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Analysis.Normed.Group.HomCompletion

/-!
# Completions of normed groups

This file contains an API for completions of seminormed groups (basic facts about
objects and morphisms).

## Main definitions

- `SemiNormedGrp.Completion : SemiNormedGrp ⥤ SemiNormedGrp` : the completion of a
  seminormed group (defined as a functor on `SemiNormedGrp` to itself).
- `SemiNormedGrp.Completion.lift (f : V ⟶ W) : (Completion.obj V ⟶ W)` : a normed group hom
  from `V` to complete `W` extends ("lifts") to a seminormed group hom from the completion of
  `V` to `W`.

## Projects

1. Construct the category of complete seminormed groups, say `CompleteSemiNormedGrp`
  and promote the `Completion` functor below to a functor landing in this category.
2. Prove that the functor `Completion : SemiNormedGrp ⥤ CompleteSemiNormedGrp`
  is left adjoint to the forgetful functor.

-/

@[expose] public section

noncomputable section

universe u

open UniformSpace MulOpposite CategoryTheory NormedAddGroupHom


namespace SemiNormedGrp

/-- The completion of a seminormed group, as an endofunctor on `SemiNormedGrp`. -/
@[simps]
/--
Definition of `completion` / `completion` 的定义

English:
definition completion
  signature: : SemiNormedGrp.{u} ⥤ SemiNormedGrp.{u} where
  body: SemiNormedGrp.of (Completion V)
  map f := SemiNormedGrp.ofHom f.hom.completion
  map_id _ := SemiNormedGrp.hom_ext completion_id
  map_comp f g := SemiNormedGrp.hom_ext (completion_comp f.hom g.hom).symm

中文:
定义 completion
  签名: : SemiNormedGrp.{u} ⥤ SemiNormedGrp.{u} where
  定义体: SemiNormedGrp.of (Completion V)
  map f := SemiNormedGrp.ofHom f.hom.completion
  map_id _ := SemiNormedGrp.hom_ext completion_id
  map_comp f g := SemiNormedGrp.hom_ext (completion_comp f.hom g.hom).symm

Depends on / 依赖: Completion, SemiNormedGrp, SemiNormedGrp.of
-/
def completion : SemiNormedGrp.{u} ⥤ SemiNormedGrp.{u} where
  obj V := SemiNormedGrp.of (Completion V)
  map f := SemiNormedGrp.ofHom f.hom.completion
  map_id _ := SemiNormedGrp.hom_ext completion_id
  map_comp f g := SemiNormedGrp.hom_ext (completion_comp f.hom g.hom).symm

/--
Instance `completion_completeSpace` / 实例 `completion_completeSpace`

English:
instance completion_completeSpace
  signature: {V : SemiNormedGrp}
  body: Completion.completeSpace _

中文:
实例 completion_completeSpace
  签名: {V : SemiNormedGrp}
  定义体: Completion.completeSpace _

Depends on / 依赖: Completion, Completion.completeSpace, completeSpace
-/
instance completion_completeSpace {V : SemiNormedGrp} : CompleteSpace (completion.obj V) :=
  Completion.completeSpace _

/--
Definition of `completion.incl` / `completion.incl` 的定义

English:
definition completion.incl
  signature: {V : SemiNormedGrp}
  body: ofHom
  { toFun v := (v : Completion V)
    map_add' := Completion.coe_add
    bound' := ⟨1, fun v => by simp⟩ }

中文:
定义 completion.incl
  签名: {V : SemiNormedGrp}
  定义体: ofHom
  { toFun v := (v : Completion V)
    map_add' := Completion.coe_add
    bound' := ⟨1, fun v => by simp⟩ }

Depends on / 依赖: Completion, Completion.coe_add, coe_add, map_add
-/
def completion.incl {V : SemiNormedGrp} : V ⟶ completion.obj V :=
  ofHom
  { toFun v := (v : Completion V)
    map_add' := Completion.coe_add
    bound' := ⟨1, fun v => by simp⟩ }

/--
theorem `completion.norm_incl_eq` / 定理 `completion.norm_incl_eq`

English:
theorem completion.norm_incl_eq
  given: {V : SemiNormedGrp} {v : V}
  statement: ‖completion.incl v‖ = ‖v‖
  proof: UniformSpace.Completion.norm_coe _

中文:
定理 completion.norm_incl_eq
  条件: {V : SemiNormedGrp} {v : V}
  结论: ‖completion.incl v‖ = ‖v‖
  证明: UniformSpace.Completion.norm_coe _

Depends on / 依赖: Completion, UniformSpace, UniformSpace.Completion.norm_coe, norm_coe
-/
theorem completion.norm_incl_eq {V : SemiNormedGrp} {v : V} : ‖completion.incl v‖ = ‖v‖ :=
  UniformSpace.Completion.norm_coe _

/--
theorem `completion.map_normNoninc` / 定理 `completion.map_normNoninc`

English:
theorem completion.map_normNoninc
  given: {V W : SemiNormedGrp} {f : V ⟶ W} (hf : f.hom.NormNoninc)
  proof: NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one.2
(NormedAddGroupHom.norm_completion f.hom).le.trans
      NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one.1 hf

中文:
定理 completion.map_normNoninc
  条件: {V W : SemiNormedGrp} {f : V ⟶ W} (hf : f.hom.NormNoninc)
  证明: NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one.2
(NormedAddGroupHom.norm_completion f.hom).le.trans
      NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one.1 hf

Depends on / 依赖: NormNoninc, NormedAddGroupHom, NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one, NormedAddGroupHom.norm_completion, f.hom, le.trans, normNoninc_iff_norm_le_one, norm_completion
-/
theorem completion.map_normNoninc {V W : SemiNormedGrp} {f : V ⟶ W} (hf : f.hom.NormNoninc) :
    (completion.map f).hom.NormNoninc :=
NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one.2
(NormedAddGroupHom.norm_completion f.hom).le.trans
      NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one.1 hf

variable (V W : SemiNormedGrp)

/--
Definition of `completion.mapHom` / `completion.mapHom` 的定义

English:
definition completion.mapHom
  signature: (V W : SemiNormedGrp.{u})
  body: @AddMonoidHom.mk' _ _ (_) (_) completion.map fun f g =>
    SemiNormedGrp.hom_ext (f.hom.completion_add g.hom)

中文:
定义 completion.mapHom
  签名: (V W : SemiNormedGrp.{u})
  定义体: @AddMonoidHom.mk' _ _ (_) (_) completion.map fun f g =>
    SemiNormedGrp.hom_ext (f.hom.completion_add g.hom)

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mk, SemiNormedGrp, SemiNormedGrp.hom_ext, completion, completion.map, completion_add, f.hom.completion_add, g.hom, hom_ext
-/
def completion.mapHom (V W : SemiNormedGrp.{u}) :
     (V ⟶ W) ->+ (completion.obj V ⟶ completion.obj W) :=
  @AddMonoidHom.mk' _ _ (_) (_) completion.map fun f g =>
    SemiNormedGrp.hom_ext (f.hom.completion_add g.hom)

/--
theorem `completion.map_zero` / 定理 `completion.map_zero`

English:
theorem completion.map_zero
  given: (V W : SemiNormedGrp)
  statement: completion.map (0 : V ⟶ W) = 0
  proof: (completion.mapHom V W).map_zero

中文:
定理 completion.map_zero
  条件: (V W : SemiNormedGrp)
  结论: completion.map (0 : V ⟶ W) = 0
  证明: (completion.mapHom V W).map_zero

Depends on / 依赖: completion, completion.mapHom, mapHom, map_zero
-/
theorem completion.map_zero (V W : SemiNormedGrp) : completion.map (0 : V ⟶ W) = 0 :=
  (completion.mapHom V W).map_zero

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Preadditive SemiNormedGrp.{u}

中文:
实例 :
  签名: 预加性 SemiNormedGrp.{u}
-/
instance : Preadditive SemiNormedGrp.{u} where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Functor.Additive completion
  body: SemiNormedGrp.hom_ext NormedAddGroupHom.completion_add _ _

中文:
实例 :
  签名: 函子.加性 completion
  定义体: SemiNormedGrp.hom_ext NormedAddGroupHom.completion_add _ _

Depends on / 依赖: NormedAddGroupHom, NormedAddGroupHom.completion_add, SemiNormedGrp, SemiNormedGrp.hom_ext, completion_add, hom_ext
-/
instance : Functor.Additive completion where
map_add := SemiNormedGrp.hom_ext NormedAddGroupHom.completion_add _ _

/--
Definition of `completion.lift` / `completion.lift` 的定义

English:
definition completion.lift
  signature: {V W : SemiNormedGrp} [CompleteSpace W] [T0Space W] (f : V ⟶ W)
  body: ofHom
  { toFun := f.hom.extension
    map_add' := f.hom.extension.toAddMonoidHom.map_add'
    bound' := f.hom.extension.bound' }

中文:
定义 completion.lift
  签名: {V W : SemiNormedGrp} [完备空间 W] [T0空间 W] (f : V ⟶ W)
  定义体: ofHom
  { toFun := f.hom.extension
    map_add' := f.hom.extension.toAddMonoidHom.map_add'
    bound' := f.hom.extension.bound' }

Depends on / 依赖: extension, f.hom.extension, f.hom.extension.bound, f.hom.extension.toAddMonoidHom.map_add, map_add, toAddMonoidHom
-/
def completion.lift {V W : SemiNormedGrp} [CompleteSpace W] [T0Space W] (f : V ⟶ W) :
    completion.obj V ⟶ W :=
  ofHom
  { toFun := f.hom.extension
    map_add' := f.hom.extension.toAddMonoidHom.map_add'
    bound' := f.hom.extension.bound' }

/--
theorem `completion.lift_comp_incl` / 定理 `completion.lift_comp_incl`

English:
theorem completion.lift_comp_incl
  statement: {V W : SemiNormedGrp} [CompleteSpace W] [T0Space W]
  proof: ext NormedAddGroupHom.extension_coe _

中文:
定理 completion.lift_comp_incl
  结论: {V W : SemiNormedGrp} [完备空间 W] [T0空间 W]
  证明: ext NormedAddGroupHom.extension_coe _

Depends on / 依赖: NormedAddGroupHom, NormedAddGroupHom.extension_coe, extension_coe
-/
theorem completion.lift_comp_incl {V W : SemiNormedGrp} [CompleteSpace W] [T0Space W]
    (f : V ⟶ W) : completion.incl ≫ completion.lift f = f :=
ext NormedAddGroupHom.extension_coe _

/--
theorem `completion.lift_unique` / 定理 `completion.lift_unique`

English:
theorem completion.lift_unique
  statement: {V W : SemiNormedGrp} [CompleteSpace W] [T0Space W]
  proof: fun h => SemiNormedGrp.hom_ext (NormedAddGroupHom.extension_unique _ fun v =>
    ((SemiNormedGrp.ext_iff.1 h) v).symm).symm

中文:
定理 completion.lift_unique
  结论: {V W : SemiNormedGrp} [完备空间 W] [T0空间 W]
  证明: fun h => SemiNormedGrp.hom_ext (NormedAddGroupHom.extension_unique _ fun v =>
    ((SemiNormedGrp.ext_iff.1 h) v).symm).symm

Depends on / 依赖: NormedAddGroupHom, NormedAddGroupHom.extension_unique, SemiNormedGrp, SemiNormedGrp.ext_iff, SemiNormedGrp.hom_ext, ext_iff, extension_unique, hom_ext
-/
theorem completion.lift_unique {V W : SemiNormedGrp} [CompleteSpace W] [T0Space W]
    (f : V ⟶ W) (g : completion.obj V ⟶ W) : completion.incl ≫ g = f -> g = completion.lift f :=
  fun h => SemiNormedGrp.hom_ext (NormedAddGroupHom.extension_unique _ fun v =>
    ((SemiNormedGrp.ext_iff.1 h) v).symm).symm

end SemiNormedGrp
