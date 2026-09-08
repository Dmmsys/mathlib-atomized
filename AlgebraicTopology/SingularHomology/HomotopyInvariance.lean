/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Fabian Odermatt
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomotopyInvariance
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Topology.Homotopy.TopCat.ToSSet

/-!
# Homotopy invariance of singular homology

In this file, we show that for any homotopy `H : TopCat.Homotopy f g`
between two morphisms `f : X ⟶ Y` and `g : X ⟶ Y` in `TopCat`,
the corresponding morphisms on the singular chain complexes
are homotopic, and in particular the induced morphisms
on singular homology are equal.

The proof proceeds by observing that this result is a particular
case of the homotopy invariance of the homology of simplicial sets
(see the file `Mathlib/AlgebraicTopology/SingularHomology/HomotopyInvariance.lean`),
applied to the morphisms `TopCat.toSSet.map f` and `TopCat.toSSet.map g`
between the singular simplicial sets of `X` and `Y`. That the homotopy `H`
induces a homotopy between these morphisms of simplicial sets
is the definition `TopCat.Homotopy.toSSet` which appeared in the file
`Mathlib/Topology/Homotopy/TopCat/ToSSet.lean`.

This result was first formalized in Lean 3 in 2022 by
Brendan Seamus Murphy (with a different proof).

-/

@[expose] public section

universe v u w

open AlgebraicTopology CategoryTheory Limits

namespace TopCat.Homotopy

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
  {X Y : TopCat.{w}} {f g : X ⟶ Y}

/-- Two homotopic morphisms in `TopCat` induce homotopic morphisms on the
singular chain complexes with coefficients in `R` (e.g. `R := ℤ` considered as
an object of the category of abelian groups). -/
/-
**TopCat.Homotopy.singularChainComplexFunctorObjMap** 是 Mathlib 中的一个定义，位于命名空间 `T
opCat.Homotopy`。
形式化陈述：singularChainComplexFunctorObjMap (H : TopCat.Homotopy f g) (R : C) : _roo
t_.Homotopy (((singularChainComplexFunctor C).obj R).map f) (((singularChainComp
lexFunctor C).obj R).map g)
参数：H : TopCat.Homotopy f g；R : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two homotopic morphisms in `TopCat` induce homotopic morphisms on the
singular chain complexes with coefficients in `R` (e.g. `R := ℤ` considered as
an object of the category of abelian groups).
-/
noncomputable def singularChainComplexFunctorObjMap (H : TopCat.Homotopy f g) (R : C) :
    _root_.Homotopy (((singularChainComplexFunctor C).obj R).map f)
      (((singularChainComplexFunctor C).obj R).map g) :=
  H.toSSet.chainComplexMap R

open HomologicalComplex in
/-- Two homotopic morphisms in `TopCat` induce equal morphisms on the
singular homology with coefficients in `R` (e.g. `R := ℤ` considered as
an object of the category of abelian groups). -/
/-
**TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor** 是 Mathlib 中的一个
引理，位于命名空间 `TopCat.Homotopy`。
形式化陈述：congr_homologyMap_singularChainComplexFunctor [CategoryWithHomology C] (H 
: TopCat.Homotopy f g) (R : C) (n : Nat) : homologyMap (((singularChainComplexFu
nctor C).obj R).map f) n = homologyMap (((singularChainComplexFunctor C).obj R).
map g) n
参数：H : TopCat.Homotopy f g；R : C；n : Nat。
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
Two homotopic morphisms in `TopCat` induce equal morphisms on the
singular homology with coefficients in `R` (e.g. `R := ℤ` considered as
an object of the category of abelian groups).
-/
lemma congr_homologyMap_singularChainComplexFunctor [CategoryWithHomology C]
    (H : TopCat.Homotopy f g) (R : C) (n : ℕ) :
    homologyMap (((singularChainComplexFunctor C).obj R).map f) n =
    homologyMap (((singularChainComplexFunctor C).obj R).map g) n :=
  (H.singularChainComplexFunctorObjMap R).homologyMap_eq n

end TopCat.Homotopy

