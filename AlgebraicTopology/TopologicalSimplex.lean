/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Adam Topaz, Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Topology.Category.TopCat.ULift

/-!
# Topological simplices

We define the natural functor from `SimplexCategory` to `TopCat` sending `⦋n⦌` to the
topological `n`-simplex.
This is used to define `TopCat.toSSet` in `AlgebraicTopology.SingularSet`.
-/

@[expose] public section

universe u

open CategoryTheory Simplicial

namespace SimplexCategory

attribute [local simp] stdSimplex.map_comp_apply in
/-- The functor `SimplexCategory ⥤ TopCat.{0}`
associating the topological `n`-simplex to `⦋n⦌ : SimplexCategory`. -/
@[simps obj map]
/--
Definition of `toTop₀` / `toTop₀` 的定义

English:
definition toTop₀
  signature: : CosimplicialObject TopCat.{0} where
  body: TopCat.of (stdSimplex Real (Fin (n.len + 1)))
  map f := TopCat.ofHom ⟨_, stdSimplex.continuous_map f⟩

中文:
定义 toTop₀
  签名: : CosimplicialObject 顶元素范畴.{0} where
  定义体: TopCat.of (stdSimplex Real (Fin (n.len + 1)))
  map f := TopCat.ofHom ⟨_, stdSimplex.continuous_map f⟩

Depends on / 依赖: TopCat, TopCat.of, n.len, stdSimplex
-/
noncomputable def toTop₀ : CosimplicialObject TopCat.{0} where
  obj n := TopCat.of (stdSimplex Real (Fin (n.len + 1)))
  map f := TopCat.ofHom ⟨_, stdSimplex.continuous_map f⟩

/-- The functor `SimplexCategory ⥤ TopCat.{u}`
associating the topological `n`-simplex to `⦋n⦌ : SimplexCategory`. -/
@[simps! obj map, pp_with_univ]
/--
Definition of `toTop` / `toTop` 的定义

English:
definition toTop
  signature: : SimplexCategory ⥤ TopCat.{u}
  body: toTop₀ ⋙ TopCat.uliftFunctor

中文:
定义 toTop
  签名: : 单纯形范畴 ⥤ 顶元素范畴.{u}
  定义体: toTop₀ ⋙ TopCat.uliftFunctor

Depends on / 依赖: TopCat, TopCat.uliftFunctor, uliftFunctor
-/
noncomputable def toTop : SimplexCategory ⥤ TopCat.{u} :=
  toTop₀ ⋙ TopCat.uliftFunctor

set_option backward.defeqAttrib.useBackward true in
instance (n : SimplexCategory) : Nonempty (toTop₀.obj n) := by dsimp; infer_instance

instance (n : SimplexCategory) : Nonempty (toTop.{u}.obj n) := inferInstanceAs (Nonempty (ULift _))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Unique (toTop₀.obj ⦋0⦌)
  body: inferInstanceAs (Unique (stdSimplex Real (Fin 1)))

中文:
实例 :
  签名: 唯一 (toTop₀.obj ⦋0⦌)
  定义体: inferInstanceAs (Unique (stdSimplex Real (Fin 1)))

Depends on / 依赖: Unique, stdSimplex
-/
instance : Unique (toTop₀.obj ⦋0⦌) := inferInstanceAs (Unique (stdSimplex Real (Fin 1)))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Unique (toTop.{u}.obj ⦋0⦌)
  body: inferInstanceAs (Unique (ULift _))

中文:
实例 :
  签名: 唯一 (toTop.{u}.obj ⦋0⦌)
  定义体: inferInstanceAs (Unique (ULift _))

Depends on / 依赖: Unique
-/
instance : Unique (toTop.{u}.obj ⦋0⦌) := inferInstanceAs (Unique (ULift _))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance (n : SimplexCategory) : PathConnectedSpace (toTop₀.obj n) := by dsimp; infer_instance

instance (n : SimplexCategory) : PathConnectedSpace (toTop.{u}.obj n) :=
  ULift.up_surjective.pathConnectedSpace continuous_uliftUp

end SimplexCategory
