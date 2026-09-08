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
/-- The type of (bundled) affine maps between two convex spaces. -/
/-
**Convexity.ConvexSpace.AffineMap** 是 Mathlib 中的一个归纳类型，位于命名空间 `Convexity.ConvexS
pace`。
形式化陈述：(R : Type u_1) →   [inst : PartialOrder R] →     [inst_1 : Semiring R] →  
     [inst_2 : IsStrictOrderedRing R] →         (X : Type u_2) → (Y : Type u_3) 
→ [Convexity.ConvexSpace R X] → [Convexity.ConvexSpace R Y] → Type (max u_2 u_3)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of (bundled) affine maps between two convex spaces.
-/
protected structure AffineMap
    (X Y : Type*) [ConvexSpace R X] [ConvexSpace R Y] where
  /-- The underlying map of an affine map between convex spaces. -/
  toFun : X → Y
  isAffineMap_toFun : IsAffineMap R toFun := by fun_prop

namespace AffineMap

/-
**Convexity.ConvexSpace.AffineMap.** 是 Mathlib 中的一个实例，位于命名空间 `Convexity.ConvexSp
ace.AffineMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : Type*} [ConvexSpace R X] [ConvexSpace R Y] :
    FunLike (ConvexSpace.AffineMap R X Y) X Y where
  coe := ConvexSpace.AffineMap.toFun
  coe_injective := fun ⟨f, _⟩ ⟨g, _⟩ h ↦ by simpa

initialize_simps_projections ConvexSpace.AffineMap (toFun → apply)

@[ext]
/-
**Convexity.ConvexSpace.AffineMap.ext** 是 Mathlib 中的一个引理，位于命名空间 `Convexity.Conve
xSpace.AffineMap`。
形式化陈述：ext {X Y : Type*} [ConvexSpace R X] [ConvexSpace R Y] {f g : ConvexSpace.A
ffineMap R X Y} (h : (f : X -> Y) = g) : f = g
参数：h : (f : X -> Y) = g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
lemma ext {X Y : Type*} [ConvexSpace R X] [ConvexSpace R Y]
    {f g : ConvexSpace.AffineMap R X Y} (h : (f : X → Y) = g) : f = g :=
  DFunLike.coe_injective h

@[fun_prop]
/-
**Convexity.ConvexSpace.AffineMap.isAffineMap** 是 Mathlib 中的一个引理，位于命名空间 `Convexi
ty.ConvexSpace.AffineMap`。
形式化陈述：isAffineMap {X Y : Type*} [ConvexSpace R X] [ConvexSpace R Y] (f : ConvexS
pace.AffineMap R X Y) : IsAffineMap R f
参数：f : ConvexSpace.AffineMap R X Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convexity.ConvexSpace.AffineMap.isAffineMap_toFun`：∀ {R : Type u_1} [ins
t : PartialOrder R] [inst_1 : Semiring R] [inst_2 : IsStrictOrderedRing R] {X : 
Type u_2}   {Y : Type u_3} [inst_3 : Co…
-/
lemma isAffineMap
    {X Y : Type*} [ConvexSpace R X] [ConvexSpace R Y]
    (f : ConvexSpace.AffineMap R X Y) :
    IsAffineMap R f :=
  f.isAffineMap_toFun

/-- The identity map, as a bundled affine map of convex spaces. -/
@[simps, implicit_reducible]
/-
**Convexity.ConvexSpace.AffineMap.id** 是 Mathlib 中的一个定义，位于命名空间 `Convexity.Convex
Space.AffineMap`。
形式化陈述：id (X : Type*) [ConvexSpace R X] : ConvexSpace.AffineMap R X X where toFun
参数：X : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity map, as a bundled affine map of convex spaces.
-/
def id (X : Type*) [ConvexSpace R X] :
    ConvexSpace.AffineMap R X X where
  toFun := _root_.id

/-- The composition of bundled affine maps between convex spaces. -/
@[simps, implicit_reducible]
/-
**Convexity.ConvexSpace.AffineMap.comp** 是 Mathlib 中的一个定义，位于命名空间 `Convexity.Conv
exSpace.AffineMap`。
形式化陈述：comp {X Y Z : Type*} [ConvexSpace R X] [ConvexSpace R Y] [ConvexSpace R Z]
 (g : ConvexSpace.AffineMap R Y Z) (f : ConvexSpace.AffineMap R X Y) : ConvexSpa
ce.AffineMap R X Z where toFun
参数：g : ConvexSpace.AffineMap R Y Z；f : ConvexSpace.AffineMap R X Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of bundled affine maps between convex spaces.
-/
def comp
    {X Y Z : Type*} [ConvexSpace R X] [ConvexSpace R Y] [ConvexSpace R Z]
    (g : ConvexSpace.AffineMap R Y Z) (f : ConvexSpace.AffineMap R X Y) :
    ConvexSpace.AffineMap R X Z where
  toFun := g ∘ f

@[simp]
/-
**Convexity.ConvexSpace.AffineMap.coe_comp** 是 Mathlib 中的一个引理，位于命名空间 `Convexity.
ConvexSpace.AffineMap`。
形式化陈述：coe_comp {X Y Z : Type*} [ConvexSpace R X] [ConvexSpace R Y] [ConvexSpace 
R Z] (g : ConvexSpace.AffineMap R Y Z) (f : ConvexSpace.AffineMap R X Y) : ⇑(g.c
omp f) = g ∘ f
参数：g : ConvexSpace.AffineMap R Y Z；f : ConvexSpace.AffineMap R X Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_comp
    {X Y Z : Type*} [ConvexSpace R X] [ConvexSpace R Y] [ConvexSpace R Z]
    (g : ConvexSpace.AffineMap R Y Z) (f : ConvexSpace.AffineMap R X Y) :
    ⇑(g.comp f) = g ∘ f := rfl

@[simp]
/-
**Convexity.ConvexSpace.AffineMap.id_comp** 是 Mathlib 中的一个引理，位于命名空间 `Convexity.C
onvexSpace.AffineMap`。
形式化陈述：id_comp {X Y : Type*} [ConvexSpace R X] [ConvexSpace R Y] (f : ConvexSpace
.AffineMap R X Y) : (AffineMap.id _).comp f = f
参数：f : ConvexSpace.AffineMap R X Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma id_comp
    {X Y : Type*} [ConvexSpace R X] [ConvexSpace R Y]
    (f : ConvexSpace.AffineMap R X Y) :
    (AffineMap.id _).comp f = f := rfl

@[simp]
/-
**Convexity.ConvexSpace.AffineMap.comp_id** 是 Mathlib 中的一个引理，位于命名空间 `Convexity.C
onvexSpace.AffineMap`。
形式化陈述：comp_id {X Y : Type*} [ConvexSpace R X] [ConvexSpace R Y] (f : ConvexSpace
.AffineMap R X Y) : f.comp (.id _) = f
参数：f : ConvexSpace.AffineMap R X Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comp_id
    {X Y : Type*} [ConvexSpace R X] [ConvexSpace R Y]
    (f : ConvexSpace.AffineMap R X Y) :
    f.comp (.id _) = f := rfl
/-
**Convexity.ConvexSpace.AffineMap.assoc** 是 Mathlib 中的一个引理，位于命名空间 `Convexity.Con
vexSpace.AffineMap`。
形式化陈述：assoc {X Y Z T : Type*} [ConvexSpace R X] [ConvexSpace R Y] [ConvexSpace R
 Z] [ConvexSpace R T] (f₁ : ConvexSpace.AffineMap R Z T) (f₂ : ConvexSpace.Affin
eMap R Y Z) (f₃ : ConvexSpace.AffineMap R X Y) : (f₁.comp f₂).comp f₃ = f₁.comp 
(f₂.comp f₃)
参数：f₁ : ConvexSpace.AffineMap R Z T；f₂ : ConvexSpace.AffineMap R Y Z；f₃ : Convex
Space.AffineMap R X Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma assoc {X Y Z T : Type*}
    [ConvexSpace R X] [ConvexSpace R Y] [ConvexSpace R Z] [ConvexSpace R T]
    (f₁ : ConvexSpace.AffineMap R Z T) (f₂ : ConvexSpace.AffineMap R Y Z)
    (f₃ : ConvexSpace.AffineMap R X Y) :
    (f₁.comp f₂).comp f₃ = f₁.comp (f₂.comp f₃) :=
  rfl

/-- A constant map between convex spaces, as a bundled affine map. -/
@[simps, implicit_reducible]
/-
**Convexity.ConvexSpace.AffineMap.const** 是 Mathlib 中的一个定义，位于命名空间 `Convexity.Con
vexSpace.AffineMap`。
形式化陈述：const {X Y : Type*} [ConvexSpace R X] [ConvexSpace R Y] (y : Y) : ConvexSp
ace.AffineMap R X Y where toFun _
参数：y : Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A constant map between convex spaces, as a bundled affine map.
-/
def const {X Y : Type*} [ConvexSpace R X] [ConvexSpace R Y] (y : Y) :
    ConvexSpace.AffineMap R X Y where
  toFun _ := y

end AffineMap

end Convexity.ConvexSpace

