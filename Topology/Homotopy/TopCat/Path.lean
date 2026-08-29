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
/--
Definition of `Path` / `Path` 的定义

English:
structure Path
  parameters: (x y : X)
  axioms and operations (3):
    - hom : I ⟶ X
    - hom₀ : hom 0 = x  [default: by cat_disch]
    - hom₁ : hom 1 = y  [default: by cat_disch]

中文:
结构 道路
  参数: (x y : X)
  公理与运算 (3 个):
    - hom : I ⟶ X
    - hom₀ : hom 0 = x  [默认: by cat_disch]
    - hom₁ : hom 1 = y  [默认: by cat_disch]
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
/--
Definition of `pathEquiv` / `pathEquiv` 的定义

English:
definition pathEquiv
  signature: {x y : X}
  body: { toContinuousMap := p.hom.hom.comp TopCat.I.homeomorph.symm
      source' := p.hom₀
      target' := p.hom₁ }
  invFun p :=
    { hom := ofHom (p.toContinuousMap.comp (toContinuousMap TopCat.I.homeomorph))
      hom₀ := p.source'
      hom₁ := p.target' }

中文:
定义 pathEquiv
  签名: {x y : X}
  定义体: { toContinuousMap := p.hom.hom.comp TopCat.I.homeomorph.symm
      source' := p.hom₀
      target' := p.hom₁ }
  invFun p :=
    { hom := ofHom (p.toContinuousMap.comp (toContinuousMap TopCat.I.homeomorph))
      hom₀ := p.source'
      hom₁ := p.target' }

Depends on / 依赖: TopCat, TopCat.I.homeomorph, TopCat.I.homeomorph.symm, homeomorph, invFun, p.hom, p.hom.hom.comp, p.source, p.target, p.toContinuousMap.comp, source, target, toContinuousMap
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
