/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Topology.Category.TopCat.Monoidal
public import Mathlib.Topology.Path

/-!
# Paths between points of an object of `TopCat`

This file introduces a structure `TopCat.Path` for paths between
two points of an object `X : TopCat`. The data is defined using
a morphism `I ⟶ X` in the category `TopCat`.

-/

@[expose] public section

universe u

namespace TopCat

variable (X : TopCat.{u})

/-- Given two points `x` and `y` of `X : TopCat`, this is the type
of paths from `x` to `y`, defined using a morphism `I ⟶ X`.
Set `TopCat.pathEquiv` for the relation with `_root_.Path x y`. -/
@[ext]
/-
**TopCat.Path** 是 Mathlib 中的一个归纳类型，位于命名空间 `TopCat`。
形式化陈述：(X : TopCat) → ↑X → ↑X → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two points `x` and `y` of `X : TopCat`, this is the type
of paths from `x` to `y`, defined using a morphism `I ⟶ X`.
Set `TopCat.pathEquiv` for the relation with `_root_.Path x y`.
-/
protected structure Path (x y : X) where
  /-- a morphism from the unit interval -/
  hom : I ⟶ X
  hom₀ : hom 0 = x := by cat_disch
  hom₁ : hom 1 = y := by cat_disch

attribute [simp] Path.hom₀ Path.hom₁

variable {X} in
/-- The bijection between `TopCat.Path X x y` and `_root_.Path x y`. -/
@[simps!]
/-
**TopCat.pathEquiv** 是 Mathlib 中的一个定义，位于命名空间 `TopCat`。
形式化陈述：pathEquiv {x y : X} : X.Path x y ≃ _root_.Path x y where toFun p
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.Path.hom₀`：∀ {X : TopCat} {x y : ↑X} (self : X.Path x y), (Catego
ryTheory.ConcreteCategory.hom self.hom) 0 = x
· 使用定理 `TopCat.Path.hom₁`：∀ {X : TopCat} {x y : ↑X} (self : X.Path x y), (Catego
ryTheory.ConcreteCategory.hom self.hom) 1 = y

--- 原说明 ---
The bijection between `TopCat.Path X x y` and `_root_.Path x y`.
-/
def pathEquiv {x y : X} : X.Path x y ≃ _root_.Path x y where
  toFun p :=
    { toContinuousMap := p.hom.hom.comp TopCat.I.homeomorph.symm
      source' := p.hom₀
      target' := p.hom₁ }
  invFun p :=
    { hom := ofHom (p.toContinuousMap.comp (toContinuousMap TopCat.I.homeomorph))
      hom₀ := p.source'
      hom₁ := p.target' }

end TopCat

