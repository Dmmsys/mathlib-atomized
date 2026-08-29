/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.Defs

/-!
# Bundled affine maps between convex spaces

If `X` and `Y` are convex spaces (over `R`), we introduce the type
`ConvexSpace.AffineMap R X Y` of bundled affine maps from `X` to `Y`.

-/

@[expose] public section

variable {R : Type*} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R]

namespace Convexity.ConvexSpace

variable (R) in
/--
Definition of `AffineMap` / `AffineMap` 的定义

English:
structure AffineMap
  axioms and operations (2):
    - toFun : X -> Y
    - isAffineMap_toFun : IsAffineMap R toFun  [default: by fun_prop]

中文:
结构 AffineMap
  公理与运算 (2 个):
    - toFun : X -> Y
    - isAffineMap_toFun : IsAffineMap R toFun  [默认: by fun_prop]
-/
protected structure AffineMap
    (X Y : Type*) [ConvexSpace R X] [ConvexSpace R Y] where
  /-- The underlying map of an affine map between convex spaces. -/
  toFun : X -> Y
  isAffineMap_toFun : IsAffineMap R toFun := by fun_prop

namespace AffineMap

instance {X Y : Type*} [ConvexSpace R X] [ConvexSpace R Y] :
    FunLike (ConvexSpace.AffineMap R X Y) X Y where
  coe := ConvexSpace.AffineMap.toFun
  coe_injective := fun ⟨f, _⟩ ⟨g, _⟩ h => by simpa

initialize_simps_projections ConvexSpace.AffineMap (toFun -> apply)

@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  statement: {X Y : Type*} [ConvexSpace R X] [ConvexSpace R Y]
  proof: DFunLike.coe_injective h

@[fun_prop]

中文:
引理 ext
  结论: {X Y : 类型} [ConvexSpace R X] [ConvexSpace R Y]
  证明: DFunLike.coe_injective h

@[fun_prop]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
lemma ext {X Y : Type*} [ConvexSpace R X] [ConvexSpace R Y]
    {f g : ConvexSpace.AffineMap R X Y} (h : (f : X -> Y) = g) : f = g :=
  DFunLike.coe_injective h

@[fun_prop]
/--
lemma `isAffineMap` / 引理 `isAffineMap`

English:
lemma isAffineMap
  proof: f.isAffineMap_toFun

中文:
引理 isAffineMap
  证明: f.isAffineMap_toFun

Depends on / 依赖: f.isAffineMap_toFun, isAffineMap_toFun
-/
lemma isAffineMap
    {X Y : Type*} [ConvexSpace R X] [ConvexSpace R Y]
    (f : ConvexSpace.AffineMap R X Y) :
    IsAffineMap R f :=
  f.isAffineMap_toFun

/-- The identity map, as a bundled affine map of convex spaces. -/
@[simps, implicit_reducible]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: (X : Type*) [ConvexSpace R X]
  body: _root_.id

中文:
定义 id
  签名: (X : 类型) [ConvexSpace R X]
  定义体: _root_.id

Depends on / 依赖: _root_, _root_.id
-/
def id (X : Type*) [ConvexSpace R X] :
    ConvexSpace.AffineMap R X X where
  toFun := _root_.id

/-- The composition of bundled affine maps between convex spaces. -/
@[simps, implicit_reducible]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  body: g ∘ f

@[simp]

中文:
定义 comp
  定义体: g ∘ f

@[simp]
-/
def comp
    {X Y Z : Type*} [ConvexSpace R X] [ConvexSpace R Y] [ConvexSpace R Z]
    (g : ConvexSpace.AffineMap R Y Z) (f : ConvexSpace.AffineMap R X Y) :
    ConvexSpace.AffineMap R X Z where
  toFun := g ∘ f

@[simp]
/--
lemma `coe_comp` / 引理 `coe_comp`

English:
lemma coe_comp
  proof: rfl

@[simp]

中文:
引理 coe_comp
  证明: rfl

@[simp]
-/
lemma coe_comp
    {X Y Z : Type*} [ConvexSpace R X] [ConvexSpace R Y] [ConvexSpace R Z]
    (g : ConvexSpace.AffineMap R Y Z) (f : ConvexSpace.AffineMap R X Y) :
    ⇑(g.comp f) = g ∘ f := rfl

@[simp]
/--
lemma `id_comp` / 引理 `id_comp`

English:
lemma id_comp
  proof: rfl

@[simp]

中文:
引理 id_comp
  证明: rfl

@[simp]
-/
lemma id_comp
    {X Y : Type*} [ConvexSpace R X] [ConvexSpace R Y]
    (f : ConvexSpace.AffineMap R X Y) :
    (AffineMap.id _).comp f = f := rfl

@[simp]
/--
lemma `comp_id` / 引理 `comp_id`

English:
lemma comp_id
  proof: rfl

中文:
引理 comp_id
  证明: rfl
-/
lemma comp_id
    {X Y : Type*} [ConvexSpace R X] [ConvexSpace R Y]
    (f : ConvexSpace.AffineMap R X Y) :
    f.comp (.id _) = f := rfl

/--
lemma `assoc` / 引理 `assoc`

English:
lemma assoc
  statement: {X Y Z T : Type*}
  proof: rfl

中文:
引理 assoc
  结论: {X Y Z T : 类型}
  证明: rfl
-/
lemma assoc {X Y Z T : Type*}
    [ConvexSpace R X] [ConvexSpace R Y] [ConvexSpace R Z] [ConvexSpace R T]
    (f₁ : ConvexSpace.AffineMap R Z T) (f₂ : ConvexSpace.AffineMap R Y Z)
    (f₃ : ConvexSpace.AffineMap R X Y) :
    (f₁.comp f₂).comp f₃ = f₁.comp (f₂.comp f₃) :=
  rfl

/-- A constant map between convex spaces, as a bundled affine map. -/
@[simps, implicit_reducible]
/--
Definition of `const` / `const` 的定义

English:
definition const
  signature: {X Y : Type*} [ConvexSpace R X] [ConvexSpace R Y] (y : Y)
  body: y

中文:
定义 const
  签名: {X Y : 类型} [ConvexSpace R X] [ConvexSpace R Y] (y : Y)
  定义体: y
-/
def const {X Y : Type*} [ConvexSpace R X] [ConvexSpace R Y] (y : Y) :
    ConvexSpace.AffineMap R X Y where
  toFun _ := y

end AffineMap

end Convexity.ConvexSpace
