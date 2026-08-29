/-
Copyright (c) 2025 Fabian Odermatt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Odermatt, Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy

/-!
# Homotopy invariance of simplicial homology

This file proves that homotopic morphisms of simplicial sets induce
the same maps on singular homology (with coefficients in an object `R`
of a preadditive category `C` with coproducts).

First, in the case where the homotopy between two morphisms of simplicial sets
`f : X ⟶ Y` and `g : X ⟶ Y` is given as combinatorial simplicial homotopy
(`SimplicialObject.Homotopy`), i.e. as family of morphisms `X _⦋n⦌ ⟶ Y _⦋n + 1⦌`,
we use the fact that we still have a similar kind of homotopy between
the corresponding morphisms on the simplicial objects in `C` that are
obtained after applying the "free object" functor `sigmaConst.obj R : Type _ ⥤ C`
degreewise, and that a combinatoral homotopy of simplicial objects
in a preadditive category induces a homotopy on the alternating face map
complexes (see `SimplicialObject.Homotopy.toChainHomotopy`, which is defined
in the file `Mathlib/AlgebraicTopology/SimplicialObject/ChainHomotopy.lean`).

Secondly, in the case where the homotopy between `f` and `g` is given
by a usual homotopy of morphisms of simplicial sets (`SSet.Homotopy`),
i.e. by a morphism `h : X ⊗ Δ[1] ⟶ Y`, we apply the construction above
to the combinatorial simplicial homotopy that is deduced from `h` by
using the definition `SSet.Homotopy.toSimplicialObjectHomotopy` from the file
`Mathlib/AlgebraicTopology/SimplicialSet/Homotopy.lean`.

-/

@[expose] public section

/-! The invariance of singular homology (of topological spaces)
is obtained in the file
`Mathlib/AlgebraicTopology/SingularHomology/HomotopyInvariance.lean`. -/
assert_not_exists TopologicalSpace

universe v u w

open CategoryTheory Limits AlgebraicTopology.SSet

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
  {X Y : SSet.{w}} {f g : X ⟶ Y}

namespace CategoryTheory.SimplicialObject.Homotopy

/--
Definition of `sSetChainComplexMap` / `sSetChainComplexMap` 的定义

English:
definition sSetChainComplexMap
  body: toChainHomotopy (H.whiskerRight _)

@[deprecated (since := "2026-04-05")]
alias singularChainComplexFunctorObjMap :=
  sSetChainComplexMap

@[deprecated (since := "2026-03-24")]
alias _root_.singularChainComplexFunctor_mapHomotopy_of_simplicialHomotopy :=
  sSetChainComplexMap

中文:
定义 sSetChainComplexMap
  定义体: toChainHomotopy (H.whiskerRight _)

@[deprecated (since := "2026-04-05")]
alias singularChainComplexFunctorObjMap :=
  sSetChainComplexMap

@[deprecated (since := "2026-03-24")]
alias _root_.singularChainComplexFunctor_mapHomotopy_of_simplicialHomotopy :=
  sSetChainComplexMap

Depends on / 依赖: H.whiskerRight, toChainHomotopy, whiskerRight
-/
noncomputable def sSetChainComplexMap
    (H : SimplicialObject.Homotopy f g) (R : C) :
    _root_.Homotopy (SSet.chainComplexMap f R) (SSet.chainComplexMap g R) :=
  toChainHomotopy (H.whiskerRight _)

@[deprecated (since := "2026-04-05")]
alias singularChainComplexFunctorObjMap :=
  sSetChainComplexMap

@[deprecated (since := "2026-03-24")]
alias _root_.singularChainComplexFunctor_mapHomotopy_of_simplicialHomotopy :=
  sSetChainComplexMap

open HomologicalComplex in
/--
theorem `congr_sSetHomologyMap` / 定理 `congr_sSetHomologyMap`

English:
theorem congr_sSetHomologyMap
  statement: [CategoryWithHomology C]
  proof: (H.sSetChainComplexMap R).homologyMap_eq n

@[deprecated (since := "2026-03-24")]
alias singularChainComplexFunctor_map_homology_eq_of_simplicialHomotopy :=
  congr_sSetHomologyMap

@[deprecated (since := "2026-04-05")] alias congr_homologyMap_singularChainComplexFunctor :=
  congr_sSetHomologyMap

中文:
定理 congr_sSetHomologyMap
  结论: [带同调范畴 C]
  证明: (H.sSetChainComplexMap R).homologyMap_eq n

@[deprecated (since := "2026-03-24")]
alias singularChainComplexFunctor_map_homology_eq_of_simplicialHomotopy :=
  congr_sSetHomologyMap

@[deprecated (since := "2026-04-05")] alias congr_homologyMap_singularChainComplexFunctor :=
  congr_sSetHomologyMap

Depends on / 依赖: H.sSetChainComplexMap, homologyMap_eq, sSetChainComplexMap
-/
theorem congr_sSetHomologyMap [CategoryWithHomology C]
    (H : SimplicialObject.Homotopy f g) (R : C) (n : Nat) :
    SSet.homologyMap f R n = SSet.homologyMap g R n :=
  (H.sSetChainComplexMap R).homologyMap_eq n

@[deprecated (since := "2026-03-24")]
alias singularChainComplexFunctor_map_homology_eq_of_simplicialHomotopy :=
  congr_sSetHomologyMap

@[deprecated (since := "2026-04-05")] alias congr_homologyMap_singularChainComplexFunctor :=
  congr_sSetHomologyMap

end CategoryTheory.SimplicialObject.Homotopy

namespace SSet.Homotopy

/--
Definition of `chainComplexMap` / `chainComplexMap` 的定义

English:
definition chainComplexMap
  body: H.toSimplicialObjectHomotopy.sSetChainComplexMap R

@[deprecated (since := "2026-04-05")]
alias singularChainComplexFunctorObjMap := chainComplexMap

中文:
定义 chainComplexMap
  定义体: H.toSimplicialObjectHomotopy.sSetChainComplexMap R

@[deprecated (since := "2026-04-05")]
alias singularChainComplexFunctorObjMap := chainComplexMap

Depends on / 依赖: H.toSimplicialObjectHomotopy.sSetChainComplexMap, sSetChainComplexMap, toSimplicialObjectHomotopy
-/
noncomputable def chainComplexMap
    (H : SSet.Homotopy f g) (R : C) :
    _root_.Homotopy (SSet.chainComplexMap f R) (SSet.chainComplexMap g R) :=
  H.toSimplicialObjectHomotopy.sSetChainComplexMap R

@[deprecated (since := "2026-04-05")]
alias singularChainComplexFunctorObjMap := chainComplexMap

open HomologicalComplex in
/--
theorem `congr_homologyMap` / 定理 `congr_homologyMap`

English:
theorem congr_homologyMap
  statement: [CategoryWithHomology C]
  proof: (H.chainComplexMap R).homologyMap_eq n

@[deprecated (since := "2026-04-05")]
alias congr_homologyMap_singularChainComplexFunctor := congr_homologyMap

中文:
定理 congr_homologyMap
  结论: [带同调范畴 C]
  证明: (H.chainComplexMap R).homologyMap_eq n

@[deprecated (since := "2026-04-05")]
alias congr_homologyMap_singularChainComplexFunctor := congr_homologyMap

Depends on / 依赖: H.chainComplexMap, chainComplexMap, homologyMap_eq
-/
theorem congr_homologyMap [CategoryWithHomology C]
    (H : SSet.Homotopy f g) (R : C) (n : Nat) :
    SSet.homologyMap f R n = SSet.homologyMap g R n :=
  (H.chainComplexMap R).homologyMap_eq n

@[deprecated (since := "2026-04-05")]
alias congr_homologyMap_singularChainComplexFunctor := congr_homologyMap

end SSet.Homotopy
