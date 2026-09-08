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
If `f` and `g` are simplicially homotopic maps of simplicial sets,
then they induce chain-homotopic maps on the singular chain complexes
with coefficients in `R`. The assumption is in `SimplicialObject.Homotopy`,
see also `SSet.Homotopy.chainComplexMap` for the
variant using `SSet.Homotopy` as an assumption.
-/
/-
**CategoryTheory.SimplicialObject.Homotopy.sSetChainComplexMap** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.SimplicialObject.Homotopy`。
形式化陈述：sSetChainComplexMap (H : SimplicialObject.Homotopy f g) (R : C) : _root_.H
omotopy (SSet.chainComplexMap f R) (SSet.chainComplexMap g R)
参数：H : SimplicialObject.Homotopy f g；R : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` and `g` are simplicially homotopic maps of simplicial sets,
then they induce chain-homotopic maps on the singular chain complexes
with coefficients in `R`. The assumption is in `SimplicialObject.Homotopy`,
see also `SSet.Homotopy.chainComplexMap` for the
variant using `SSet.Homotopy` as an assumption.
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
Simplicially homotopic maps of simplicial sets induce the same map on
homology of the singular chain complex (with coefficients in `R`).
The assumption is in `SimplicialObject.Homotopy`,
see also `SSet.Homotopy.congr_homologyMap` for the
variant using `SSet.Homotopy` as an assumption.
-/
/-
**CategoryTheory.SimplicialObject.Homotopy.congr_sSetHomologyMap** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.SimplicialObject.Homotopy`。
形式化陈述：congr_sSetHomologyMap [CategoryWithHomology C] (H : SimplicialObject.Homot
opy f g) (R : C) (n : Nat) : SSet.homologyMap f R n = SSet.homologyMap g R n
参数：H : SimplicialObject.Homotopy f g；R : C；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Homotopy.homologyMap_eq`：Homotopy.homologyMap_eq (ho : Homotopy f g) (i 
: ι) [K.HasHomology i] [L.HasHomology i] : homologyMap f i = homologyMap g i
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…

--- 原说明 ---
Simplicially homotopic maps of simplicial sets induce the same map on
homology of the singular chain complex (with coefficients in `R`).
The assumption is in `SimplicialObject.Homotopy`,
see also `SSet.Homotopy.congr_homologyMap` for the
variant using `SSet.Homotopy` as an assumption.
-/
theorem congr_sSetHomologyMap [CategoryWithHomology C]
    (H : SimplicialObject.Homotopy f g) (R : C) (n : ℕ) :
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
If `f` and `g` are homotopic maps of simplicial sets, then they induce chain-homotopic
maps on the singular chain complexes with coefficients in `R`.
-/
/-
**SSet.Homotopy.chainComplexMap** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Homotopy`。
形式化陈述：chainComplexMap (H : SSet.Homotopy f g) (R : C) : _root_.Homotopy (SSet.ch
ainComplexMap f R) (SSet.chainComplexMap g R)
参数：H : SSet.Homotopy f g；R : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` and `g` are homotopic maps of simplicial sets, then they induce chain-hom
otopic
maps on the singular chain complexes with coefficients in `R`.
-/
noncomputable def chainComplexMap
    (H : SSet.Homotopy f g) (R : C) :
    _root_.Homotopy (SSet.chainComplexMap f R) (SSet.chainComplexMap g R)  :=
  H.toSimplicialObjectHomotopy.sSetChainComplexMap R

@[deprecated (since := "2026-04-05")]
alias singularChainComplexFunctorObjMap := chainComplexMap

open HomologicalComplex in
/--
Homotopic maps of simplicial sets induce the same map on homology of the singular
chain complex (with coefficients in `R`).
-/
/-
**SSet.Homotopy.congr_homologyMap** 是 Mathlib 中的一个定理，位于命名空间 `SSet.Homotopy`。
形式化陈述：congr_homologyMap [CategoryWithHomology C] (H : SSet.Homotopy f g) (R : C)
 (n : Nat) : SSet.homologyMap f R n = SSet.homologyMap g R n
参数：H : SSet.Homotopy f g；R : C；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Homotopy.homologyMap_eq`：Homotopy.homologyMap_eq (ho : Homotopy f g) (i 
: ι) [K.HasHomology i] [L.HasHomology i] : homologyMap f i = homologyMap g i
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…

--- 原说明 ---
Homotopic maps of simplicial sets induce the same map on homology of the singula
r
chain complex (with coefficients in `R`).
-/
theorem congr_homologyMap [CategoryWithHomology C]
    (H : SSet.Homotopy f g) (R : C) (n : ℕ) :
    SSet.homologyMap f R n = SSet.homologyMap g R n :=
  (H.chainComplexMap R).homologyMap_eq n

@[deprecated (since := "2026-04-05")]
alias congr_homologyMap_singularChainComplexFunctor := congr_homologyMap

end SSet.Homotopy

