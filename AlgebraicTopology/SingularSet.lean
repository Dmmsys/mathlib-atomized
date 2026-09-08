/-
Copyright (c) 2023 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kim Morrison, Adam Topaz
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.AlgebraicTopology.TopologicalSimplex
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Category.TopCat.ULift

/-!
# The singular simplicial set of a topological space and geometric realization of a simplicial set

The *singular simplicial set* `TopCat.toSSet.obj X` of a topological space `X`
has `n`-simplices which identify to continuous maps `stdSimplex ℝ (Fin (n + 1)) → X`,
where `stdSimplex ℝ (Fin (n + 1))` is the standard topological `n`-simplex,
defined as the subtype of `Fin (n + 1) → ℝ` consisting of functions `f`
such that `0 ≤ f i` for all `i` and `∑ i, f i = 1`.

The *geometric realization* functor `SSet.toTop` is left adjoint to `TopCat.toSSet`.
It is the left Kan extension of `SimplexCategory.toTop` along the Yoneda embedding.

## Main definitions

* `TopCat.toSSet : TopCat ⥤ SSet` is the functor
  assigning the singular simplicial set to a topological space.
* `SSet.toTop : SSet ⥤ TopCat` is the functor
  assigning the geometric realization to a simplicial set.
* `sSetTopAdj : SSet.toTop ⊣ TopCat.toSSet` is the adjunction between these two functors.

## TODO (@joelriou)

- Show that the singular simplicial set is a Kan complex.
- Show the adjunction `sSetTopAdj` is a Quillen equivalence.

-/

@[expose] public section

universe u

open CategoryTheory

/-- The functor associating the *singular simplicial set* to a topological space.

Let `X : TopCat.{u}` be a topological space.
Then the singular simplicial set of `X`
has as `n`-simplices the continuous maps `ULift.{u} (stdSimplex ℝ (Fin (n + 1))) → X`.
Here, `stdSimplex ℝ (Fin (n + 1))` is the standard topological `n`-simplex,
defined as `{ f : Fin (n + 1) → ℝ // (∀ i, 0 ≤ f i) ∧ ∑ i, f i = 1 }` with its subspace topology. -/
/-
**TopCat.toSSet** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：TopCat.toSSet : TopCat.{u} ⥤ SSet.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor associating the *singular simplicial set* to a topological space.

Let `X : TopCat.{u}` be a topological space.
Then the singular simplicial set of `X`
has as `n`-simplices the continuous maps `ULift.{u} (stdSimplex ℝ (Fin (n + 1)))
 → X`.
Here, `stdSimplex ℝ (Fin (n + 1))` is the standard topological `n`-simplex,
defined as `{ f : Fin (n + 1) → ℝ // (∀ i, 0 ≤ f i) ∧ ∑ i, f i = 1 }` with its s
ubspace topology.
-/
noncomputable def TopCat.toSSet : TopCat.{u} ⥤ SSet.{u} :=
  Presheaf.restrictedULiftYoneda.{0} SimplexCategory.toTop.{u}

/-- If `X : TopCat.{u}` and `n : SimplexCategoryᵒᵖ`,
then `(toSSet.obj X).obj n` identifies to the type of continuous
maps from the standard simplex `stdSimplex ℝ (Fin (n.unop.len + 1))` to `X`. -/
/-
**TopCat.toSSetObjEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：TopCat.toSSetObjEquiv (X : TopCat.{u}) (n : SimplexCategoryᵒᵖ) : (toSSet.o
bj X).obj n ≃ C(stdSimplex Real (Fin (n.unop.len + 1)), X)
参数：X : TopCat.{u}；n : SimplexCategoryᵒᵖ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
If `X : TopCat.{u}` and `n : SimplexCategoryᵒᵖ`,
then `(toSSet.obj X).obj n` identifies to the type of continuous
maps from the standard simplex `stdSimplex ℝ (Fin (n.unop.len + 1))` to `X`.
-/
noncomputable def TopCat.toSSetObjEquiv (X : TopCat.{u}) (n : SimplexCategoryᵒᵖ) :
    (toSSet.obj X).obj n ≃ C(stdSimplex ℝ (Fin (n.unop.len + 1)), X) :=
  Equiv.ulift.{0}.trans (ConcreteCategory.homEquiv.trans
    (Homeomorph.ulift.continuousMapCongr (.refl _)))

set_option backward.isDefEq.respectTransparency.types false in
/-- The *geometric realization functor* is
the left Kan extension of `SimplexCategory.toTop` along the Yoneda embedding.

It is left adjoint to `TopCat.toSSet`, as witnessed by `sSetTopAdj`. -/
/-
**SSet.toTop** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：SSet.toTop : SSet.{u} ⥤ TopCat.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The *geometric realization functor* is
the left Kan extension of `SimplexCategory.toTop` along the Yoneda embedding.

It is left adjoint to `TopCat.toSSet`, as witnessed by `sSetTopAdj`.
-/
noncomputable def SSet.toTop : SSet.{u} ⥤ TopCat.{u} :=
  stdSimplex.{u}.leftKanExtension SimplexCategory.toTop

/-- The geometric realization of a simplicial set. -/
scoped[Simplicial] notation "|" X "|" => SSet.toTop.obj X

set_option backward.isDefEq.respectTransparency false in
/-- Geometric realization is left adjoint to the singular simplicial set construction. -/
/-
**sSetTopAdj** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：sSetTopAdj : SSet.toTop.{u} ⊣ TopCat.toSSet.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Geometric realization is left adjoint to the singular simplicial set constructio
n.
-/
noncomputable def sSetTopAdj : SSet.toTop.{u} ⊣ TopCat.toSSet.{u} :=
  Presheaf.uliftYonedaAdjunction
    (SSet.stdSimplex.{u}.leftKanExtension SimplexCategory.toTop)
    (SSet.stdSimplex.{u}.leftKanExtensionUnit SimplexCategory.toTop)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SSet.toTop.{u}.IsLeftAdjoint := sSetTopAdj.isLeftAdjoint
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : TopCat.toSSet.{u}.IsRightAdjoint := sSetTopAdj.isRightAdjoint

set_option backward.isDefEq.respectTransparency.types false in
/-- The geometric realization of the representable simplicial sets agree
  with the usual topological simplices. -/
/-
**SSet.toTopSimplex** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：SSet.toTopSimplex : SSet.stdSimplex.{u} ⋙ SSet.toTop ≅ SimplexCategory.toT
op
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The geometric realization of the representable simplicial sets agree
  with the usual topological simplices.
-/
noncomputable def SSet.toTopSimplex :
    SSet.stdSimplex.{u} ⋙ SSet.toTop ≅ SimplexCategory.toTop :=
  Presheaf.isExtensionAlongULiftYoneda _

set_option backward.isDefEq.respectTransparency.types false in
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SSet.toTop.{u}.IsLeftKanExtension SSet.toTopSimplex.inv :=
  inferInstanceAs (Functor.IsLeftKanExtension _
    (SSet.stdSimplex.{u}.leftKanExtensionUnit SimplexCategory.toTop.{u}))

set_option backward.isDefEq.respectTransparency.types false in
/-
**sSetTopAdj_unit_app_app_down** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sSetTopAdj_unit_app_app_down (S : SSet) (m : SimplexCategoryᵒᵖ) (a : S.obj
 m) : ((sSetTopAdj.unit.app S).app m a).down = SSet.toTopSimplex.inv.app _ ≫ SSe
t.toTop.map (SSet.yonedaEquiv.symm a)
参数：S : SSet；m : SimplexCategoryᵒᵖ；a : S.obj m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma sSetTopAdj_unit_app_app_down (S : SSet) (m : SimplexCategoryᵒᵖ) (a : S.obj m) :
    ((sSetTopAdj.unit.app S).app m a).down =
      SSet.toTopSimplex.inv.app _ ≫ SSet.toTop.map (SSet.yonedaEquiv.symm a) := by
  cat_disch

/-- The singular simplicial set of a totally disconnected space is the constant simplicial set. -/
/-
**TopCat.toSSetIsoConst** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：TopCat.toSSetIsoConst (X : TopCat.{u}) [TotallyDisconnectedSpace X] : TopC
at.toSSet.obj X ≅ (Functor.const _).obj X
参数：X : TopCat.{u}。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The singular simplicial set of a totally disconnected space is the constant simp
licial set.
-/
noncomputable def TopCat.toSSetIsoConst (X : TopCat.{u}) [TotallyDisconnectedSpace X] :
    TopCat.toSSet.obj X ≅ (Functor.const _).obj X :=
  (NatIso.ofComponents (fun n ↦ Equiv.toIso
    ((TotallyDisconnectedSpace.continuousMapEquivOfConnectedSpace _ X).symm.trans
      (X.toSSetObjEquiv n).symm))).symm

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical map `Δ[n] ⟶ Simp(Δₜ[n])` (where `Δₜ[n]` is the topological `n`-simplex). -/
/-
**SSet.stdSimplexToTop** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
形式化陈述：SSet.stdSimplex ⟶ SimplexCategory.toTop.{u}.comp TopCat.toSSet
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map `Δ[n] ⟶ Simp(Δₜ[n])` (where `Δₜ[n]` is the topological `n`-sim
plex).
-/
@[simps! -isSimp] noncomputable def SSet.stdSimplexToTop :
    SSet.stdSimplex.{u} ⟶ SimplexCategory.toTop ⋙ TopCat.toSSet :=
  SSet.stdSimplex.whiskerLeft sSetTopAdj.unit ≫
    Functor.whiskerRight SSet.toTopSimplex.hom TopCat.toSSet
