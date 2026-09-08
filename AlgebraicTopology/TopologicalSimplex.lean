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
/-
**SimplexCategory.toTop** 是 Mathlib 中的一个定义，位于命名空间 `SimplexCategory`。
形式化陈述：toTop : SimplexCategory ⥤ TopCat.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `SimplexCategory ⥤ TopCat.{0}`
associating the topological `n`-simplex to `⦋n⦌ : SimplexCategory`.
-/
noncomputable def toTop₀ : CosimplicialObject TopCat.{0} where
  obj n := TopCat.of (stdSimplex ℝ (Fin (n.len + 1)))
  map f := TopCat.ofHom ⟨_, stdSimplex.continuous_map f⟩

/-- The functor `SimplexCategory ⥤ TopCat.{u}`
associating the topological `n`-simplex to `⦋n⦌ : SimplexCategory`. -/
@[simps! obj map, pp_with_univ]
/-
**SimplexCategory.toTop** 是 Mathlib 中的一个定义，位于命名空间 `SimplexCategory`。
形式化陈述：toTop : SimplexCategory ⥤ TopCat.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `SimplexCategory ⥤ TopCat.{u}`
associating the topological `n`-simplex to `⦋n⦌ : SimplexCategory`.
-/
noncomputable def toTop : SimplexCategory ⥤ TopCat.{u} :=
  toTop₀ ⋙ TopCat.uliftFunctor

set_option backward.defeqAttrib.useBackward true in
/-
**SimplexCategory.** 是 Mathlib 中的一个实例，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : SimplexCategory) : Nonempty (toTop₀.obj n) := by dsimp; infer_instance
/-
**SimplexCategory.** 是 Mathlib 中的一个实例，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : SimplexCategory) : Nonempty (toTop.{u}.obj n) := inferInstanceAs (Nonempty (ULift _))
/-
**SimplexCategory.** 是 Mathlib 中的一个实例，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Unique (toTop₀.obj ⦋0⦌) := inferInstanceAs (Unique (stdSimplex ℝ (Fin 1)))
/-
**SimplexCategory.** 是 Mathlib 中的一个实例，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Unique (toTop.{u}.obj ⦋0⦌) := inferInstanceAs (Unique (ULift _))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**SimplexCategory.** 是 Mathlib 中的一个实例，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : SimplexCategory) : PathConnectedSpace (toTop₀.obj n) := by dsimp; infer_instance
/-
**SimplexCategory.** 是 Mathlib 中的一个实例，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : SimplexCategory) : PathConnectedSpace (toTop.{u}.obj n) :=
  ULift.up_surjective.pathConnectedSpace continuous_uliftUp

end SimplexCategory

