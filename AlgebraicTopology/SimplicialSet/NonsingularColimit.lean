/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.SemiSimplexCategory
public import Mathlib.AlgebraicTopology.SimplicialSet.Nonsingular
public import Mathlib.AlgebraicTopology.SimplicialSet.NonDegenerateSimplicesColimit

/-!
# Nonsingular simplicial sets, as colimits of standard simplices

In the file `Mathlib/AlgebraicTopology/SimplicialSet/NonDegenerateSimplicesColimit.lean`,
it was shown that any simplicial set `X` is the colimit (indexed by the type `X.N`
of nondegenerate simplices) of its monogenous subcomplexes.

In this file, we assume that `X` is nonsingular, in which case its monogenous subcomplexes
identify to standard simplices. This allows to show that `X` is the colimit
of `Δ[x.dim]` for `x : X.N`.

-/

@[expose] public section

universe u

open CategoryTheory Simplicial Limits

namespace SSet

variable (X : SSet.{u}) [X.Nonsingular]

namespace N

set_option backward.isDefEq.respectTransparency false in
/-- If `X` is a nonsingular simplicial set, this is the functor
`X.N ⥤ SemiSimplexCategory` which sends a nondegenerate
simplex `s : X.N` to `⦋s.dim⦌ₛ`. -/
@[simps obj map]
/--
Definition of `toSemiSimplexCategory` / `toSemiSimplexCategory` 的定义

English:
definition toSemiSimplexCategory
  signature: : X.N ⥤ SemiSimplexCategory where
  body: ⦋s.dim⦌ₛ
  map f := SemiSimplexCategory.homOfMono (N.monoOfLE (leOfHom f))
  map_id _ := SemiSimplexCategory.toSimplexCategory.map_injective (by simp)
  map_comp _ _ := SemiSimplexCategory.toSimplexCategory.map_injective (by simp)

中文:
定义 toSemiSimplexCategory
  签名: : X.N ⥤ SemiSimplexCategory where
  定义体: ⦋s.dim⦌ₛ
  map f := SemiSimplexCategory.homOfMono (N.monoOfLE (leOfHom f))
  map_id _ := SemiSimplexCategory.toSimplexCategory.map_injective (by simp)
  map_comp _ _ := SemiSimplexCategory.toSimplexCategory.map_injective (by simp)

Depends on / 依赖: s.dim
-/
noncomputable def toSemiSimplexCategory : X.N ⥤ SemiSimplexCategory where
  obj s := ⦋s.dim⦌ₛ
  map f := SemiSimplexCategory.homOfMono (N.monoOfLE (leOfHom f))
  map_id _ := SemiSimplexCategory.toSimplexCategory.map_injective (by simp)
  map_comp _ _ := SemiSimplexCategory.toSimplexCategory.map_injective (by simp)

end N

/--
Definition of `functorN'` / `functorN'` 的定义

English:
abbreviation functorN'
  signature: : X.N ⥤ SSet.{u}
  body: N.toSemiSimplexCategory X ⋙ SemiSimplexCategory.toSimplexCategory ⋙ SSet.stdSimplex

中文:
缩写 functorN'
  签名: : X.N ⥤ SSet.{u}
  定义体: N.toSemiSimplexCategory X ⋙ SemiSimplexCategory.toSimplexCategory ⋙ SSet.stdSimplex

Depends on / 依赖: N.toSemiSimplexCategory, SSet.stdSimplex, SemiSimplexCategory, SemiSimplexCategory.toSimplexCategory, stdSimplex, toSemiSimplexCategory, toSimplexCategory
-/
noncomputable abbrev functorN' : X.N ⥤ SSet.{u} :=
    N.toSemiSimplexCategory X ⋙ SemiSimplexCategory.toSimplexCategory ⋙ SSet.stdSimplex

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `functorN'Iso` / `functorN'Iso` 的定义

English:
definition functorN'Iso
  signature: : X.functorN' ≅ X.functorN
  body: NatIso.ofComponents (fun x => Nonsingular.iso _ x.nonDegenerate) (fun _ => by
    simp [← cancel_mono (Subcomplex.ι _)])

中文:
定义 functorN'Iso
  签名: : X.functorN' ≅ X.functorN
  定义体: NatIso.ofComponents (fun x => Nonsingular.iso _ x.nonDegenerate) (fun _ => by
    simp [← cancel_mono (Subcomplex.ι _)])
-/
noncomputable def functorN'Iso : X.functorN' ≅ X.functorN :=
  NatIso.ofComponents (fun x => Nonsingular.iso _ x.nonDegenerate) (fun _ => by
    simp [← cancel_mono (Subcomplex.ι _)])

/-- If `X` is a nonsingular simplicial set, this is the cocone consisting
of the (mono)morphisms `Δ[x.dim] ⟶ X` for all nondegenerate simplices `x : X.N`. -/
@[simps]
/--
Definition of `coconeN'` / `coconeN'` 的定义

English:
definition coconeN'
  signature: : Cocone X.functorN' where
  body: X
  ι.app s := yonedaEquiv.symm s.simplex
  ι.naturality _ _ f := N.stdSimplex_map_monoOfLE_yonedaEquiv_symm_simplex (leOfHom f)

中文:
定义 coconeN'
  签名: : Cocone X.functorN' where
  定义体: X
  ι.app s := yonedaEquiv.symm s.simplex
  ι.naturality _ _ f := N.stdSimplex_map_monoOfLE_yonedaEquiv_symm_simplex (leOfHom f)
-/
noncomputable def coconeN' : Cocone X.functorN' where
  pt := X
  ι.app s := yonedaEquiv.symm s.simplex
  ι.naturality _ _ f := N.stdSimplex_map_monoOfLE_yonedaEquiv_symm_simplex (leOfHom f)

/--
Definition of `isColimitCoconeN'` / `isColimitCoconeN'` 的定义

English:
definition isColimitCoconeN'
  signature: : IsColimit X.coconeN'
  body: (IsColimit.equivOfNatIsoOfIso
    X.functorN'Iso.symm _ _ (Cocone.ext (Iso.refl _))).1 X.isColimitCoconeN

中文:
定义 isColimitCoconeN'
  签名: : IsColimit X.coconeN'
  定义体: (IsColimit.equivOfNatIsoOfIso
    X.functorN'Iso.symm _ _ (Cocone.ext (Iso.refl _))).1 X.isColimitCoconeN

Depends on / 依赖: Cocone, Cocone.ext, IsColimit, IsColimit.equivOfNatIsoOfIso, Iso.refl, Iso.symm, X.functorN, X.isColimitCoconeN, equivOfNatIsoOfIso, functorN, isColimitCoconeN
-/
noncomputable def isColimitCoconeN' : IsColimit X.coconeN' :=
  (IsColimit.equivOfNatIsoOfIso
    X.functorN'Iso.symm _ _ (Cocone.ext (Iso.refl _))).1 X.isColimitCoconeN

end SSet
