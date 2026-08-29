/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# The pseudofunctors which send a commutative ring to its category of modules

In this file, we construct the pseudofunctors
`CommRingCat.moduleCatRestrictScalarsPseudofunctor` and
`RingCat.moduleCatRestrictScalarsPseudofunctor` which send a (commutative) ring
to its category of modules: the contravariant functoriality is given
by the restriction of scalars functors.

We also define a pseudofunctor
`CommRingCat.moduleCatExtendScalarsPseudofunctor`: the covariant functoriality
is given by the extension of scalars functors.

-/

@[expose] public section

universe v u

open CategoryTheory ModuleCat

/-- The pseudofunctor from `LocallyDiscrete CommRingCatᵒᵖ` to `Cat` which sends
a commutative ring `R` to its category of modules. The functoriality is given by
the restriction of scalars. -/
@[simps! obj map mapId mapComp]
/--
Definition of `CommRingCat.moduleCatRestrictScalarsPseudofunctor` / `CommRingCat.moduleCatRestrictScalarsPseudofunctor` 的定义

English:
definition CommRingCat.moduleCatRestrictScalarsPseudofunctor
  signature: :
  body: LocallyDiscrete.mkPseudofunctor
    (fun R => Cat.of (ModuleCat.{v} R.unop))
    (fun f => (restrictScalars f.unop.hom).toCatHom)
    (fun R => Cat.Hom.isoMk (restrictScalarsId R.unop))
    (fun f g => Cat.Hom.isoMk <| restrictScalarsComp g.unop.hom f.unop.hom)

中文:
定义 交换环范畴.moduleCatRestrictScalarsPseudofunctor
  签名: :
  定义体: LocallyDiscrete.mkPseudofunctor
    (fun R => Cat.of (ModuleCat.{v} R.unop))
    (fun f => (restrictScalars f.unop.hom).toCatHom)
    (fun R => Cat.Hom.isoMk (restrictScalarsId R.unop))
    (fun f g => Cat.Hom.isoMk <| restrictScalarsComp g.unop.hom f.unop.hom)

Depends on / 依赖: Cat.Hom.isoMk, Cat.of, LocallyDiscrete, LocallyDiscrete.mkPseudofunctor, ModuleCat, R.unop, f.unop.hom, g.unop.hom, mkPseudofunctor, restrictScalars, restrictScalarsComp, restrictScalarsId, toCatHom
-/
noncomputable def CommRingCat.moduleCatRestrictScalarsPseudofunctor :
    Pseudofunctor (LocallyDiscrete CommRingCat.{u}ᵒᵖ) Cat :=
  LocallyDiscrete.mkPseudofunctor
    (fun R => Cat.of (ModuleCat.{v} R.unop))
    (fun f => (restrictScalars f.unop.hom).toCatHom)
    (fun R => Cat.Hom.isoMk (restrictScalarsId R.unop))
    (fun f g => Cat.Hom.isoMk <| restrictScalarsComp g.unop.hom f.unop.hom)

/-- The pseudofunctor from `LocallyDiscrete RingCatᵒᵖ` to `Cat` which sends a ring `R`
to its category of modules. The functoriality is given by the restriction of scalars. -/
@[simps! obj map mapId mapComp]
/--
Definition of `RingCat.moduleCatRestrictScalarsPseudofunctor` / `RingCat.moduleCatRestrictScalarsPseudofunctor` 的定义

English:
definition RingCat.moduleCatRestrictScalarsPseudofunctor
  signature: :
  body: LocallyDiscrete.mkPseudofunctor
    (fun R => Cat.of (ModuleCat.{v} R.unop))
    (fun f => (restrictScalars f.unop.hom).toCatHom)
    (fun R => Cat.Hom.isoMk <| restrictScalarsId R.unop)
    (fun f g => Cat.Hom.isoMk <| restrictScalarsComp g.unop.hom f.unop.hom)

中文:
定义 环范畴.moduleCatRestrictScalarsPseudofunctor
  签名: :
  定义体: LocallyDiscrete.mkPseudofunctor
    (fun R => Cat.of (ModuleCat.{v} R.unop))
    (fun f => (restrictScalars f.unop.hom).toCatHom)
    (fun R => Cat.Hom.isoMk <| restrictScalarsId R.unop)
    (fun f g => Cat.Hom.isoMk <| restrictScalarsComp g.unop.hom f.unop.hom)

Depends on / 依赖: Cat.Hom.isoMk, Cat.of, LocallyDiscrete, LocallyDiscrete.mkPseudofunctor, ModuleCat, R.unop, f.unop.hom, g.unop.hom, mkPseudofunctor, restrictScalars, restrictScalarsComp, restrictScalarsId, toCatHom
-/
noncomputable def RingCat.moduleCatRestrictScalarsPseudofunctor :
    Pseudofunctor (LocallyDiscrete RingCat.{u}ᵒᵖ) Cat :=
  LocallyDiscrete.mkPseudofunctor
    (fun R => Cat.of (ModuleCat.{v} R.unop))
    (fun f => (restrictScalars f.unop.hom).toCatHom)
    (fun R => Cat.Hom.isoMk <| restrictScalarsId R.unop)
    (fun f g => Cat.Hom.isoMk <| restrictScalarsComp g.unop.hom f.unop.hom)

/-- The pseudofunctor from `LocallyDiscrete CommRingCat` to `Cat` which sends
a commutative ring `R` to its category of modules. The functoriality is given by
the extension of scalars. -/
@[simps! obj map mapId mapComp]
/--
Definition of `CommRingCat.moduleCatExtendScalarsPseudofunctor` / `CommRingCat.moduleCatExtendScalarsPseudofunctor` 的定义

English:
definition CommRingCat.moduleCatExtendScalarsPseudofunctor
  signature: :
  body: by
  refine LocallyDiscrete.mkPseudofunctor
    (fun R => Cat.of (ModuleCat.{u} R))
    (fun f => (extendScalars f.hom).toCatHom)
    (fun R => Cat.Hom.isoMk <| extendScalarsId R)
    (fun f g => Cat.Hom.isoMk <| extendScalarsComp f.hom g.hom) ?_ ?_ ?_
  · intros; ext1; apply extendScalars_assoc'
  

中文:
定义 交换环范畴.moduleCatExtendScalarsPseudofunctor
  签名: :
  定义体: by
  refine LocallyDiscrete.mkPseudofunctor
    (fun R => Cat.of (ModuleCat.{u} R))
    (fun f => (extendScalars f.hom).toCatHom)
    (fun R => Cat.Hom.isoMk <| extendScalarsId R)
    (fun f g => Cat.Hom.isoMk <| extendScalarsComp f.hom g.hom) ?_ ?_ ?_
  · intros; ext1; apply extendScalars_assoc'
  

Depends on / 依赖: Cat.Hom.isoMk, Cat.of, LocallyDiscrete, LocallyDiscrete.mkPseudofunctor, ModuleCat, extendScalars, extendScalarsComp, extendScalarsId, extendScalars_assoc, extendScalars_comp_id, extendScalars_id_comp, f.hom, g.hom, intros, mkPseudofunctor, toCatHom
-/
noncomputable def CommRingCat.moduleCatExtendScalarsPseudofunctor :
    Pseudofunctor (LocallyDiscrete CommRingCat.{u}) Cat := by
  refine LocallyDiscrete.mkPseudofunctor
    (fun R => Cat.of (ModuleCat.{u} R))
    (fun f => (extendScalars f.hom).toCatHom)
    (fun R => Cat.Hom.isoMk <| extendScalarsId R)
    (fun f g => Cat.Hom.isoMk <| extendScalarsComp f.hom g.hom) ?_ ?_ ?_
  · intros; ext1; apply extendScalars_assoc'
  · intros; ext1; apply extendScalars_id_comp
  · intros; ext1; apply extendScalars_comp_id
