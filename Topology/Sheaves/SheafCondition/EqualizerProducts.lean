/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections

/-!
# The sheaf condition in terms of an equalizer of products

Here we set up the machinery for the "usual" definition of the sheaf condition,
e.g. as in https://stacks.math.columbia.edu/tag/0072
in terms of an equalizer diagram where the two objects are
`∏ᶜ F.obj (U i)` and `∏ᶜ F.obj (U i) ⊓ (U j)`.

We show that this sheaf condition is equivalent to the "pairwise intersections" sheaf condition when
the presheaf is valued in a category with products, and thereby equivalent to the default sheaf
condition.
-/

@[expose] public section


universe v' v u

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopologicalSpace.Opens

namespace TopCat

variable {C : Type u} [Category.{v} C] [HasProducts.{v'} C]
variable {X : TopCat.{v'}} (F : Presheaf C X) {ι : Type v'} (U : ι → Opens X)

namespace Presheaf

namespace SheafConditionEqualizerProducts

/-- The product of the sections of a presheaf over a family of open sets. -/
/-
**TopCat.Presheaf.SheafConditionEqualizerProducts.piOpens** 是 Mathlib 中的一个定义，位于命
名空间 `TopCat.Presheaf.SheafConditionEqualizerProducts`。
形式化陈述：piOpens : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of the sections of a presheaf over a family of open sets.
-/
def piOpens : C :=
  ∏ᶜ fun i : ι => F.obj (op (U i))

/-- The product of the sections of a presheaf over the pairwise intersections of
a family of open sets.
-/
/-
**TopCat.Presheaf.SheafConditionEqualizerProducts.piInters** 是 Mathlib 中的一个定义，位于
命名空间 `TopCat.Presheaf.SheafConditionEqualizerProducts`。
形式化陈述：piInters : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of the sections of a presheaf over the pairwise intersections of
a family of open sets.
-/
def piInters : C :=
  ∏ᶜ fun p : ι × ι => F.obj (op (U p.1 ⊓ U p.2))

/-- The morphism `Π F.obj (U i) ⟶ Π F.obj (U i) ⊓ (U j)` whose components
are given by the restriction maps from `U i` to `U i ⊓ U j`.
-/
/-
**TopCat.Presheaf.SheafConditionEqualizerProducts.leftRes** 是 Mathlib 中的一个定义，位于命
名空间 `TopCat.Presheaf.SheafConditionEqualizerProducts`。
形式化陈述：leftRes : piOpens F U ⟶ piInters.{v'} F U
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `Π F.obj (U i) ⟶ Π F.obj (U i) ⊓ (U j)` whose components
are given by the restriction maps from `U i` to `U i ⊓ U j`.
-/
def leftRes : piOpens F U ⟶ piInters.{v'} F U :=
  Pi.lift fun p : ι × ι => Pi.π _ p.1 ≫ F.map (infLELeft (U p.1) (U p.2)).op

/-- The morphism `Π F.obj (U i) ⟶ Π F.obj (U i) ⊓ (U j)` whose components
are given by the restriction maps from `U j` to `U i ⊓ U j`.
-/
/-
**TopCat.Presheaf.SheafConditionEqualizerProducts.rightRes** 是 Mathlib 中的一个定义，位于
命名空间 `TopCat.Presheaf.SheafConditionEqualizerProducts`。
形式化陈述：rightRes : piOpens F U ⟶ piInters.{v'} F U
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `Π F.obj (U i) ⟶ Π F.obj (U i) ⊓ (U j)` whose components
are given by the restriction maps from `U j` to `U i ⊓ U j`.
-/
def rightRes : piOpens F U ⟶ piInters.{v'} F U :=
  Pi.lift fun p : ι × ι => Pi.π _ p.2 ≫ F.map (infLERight (U p.1) (U p.2)).op

/-- The morphism `F.obj U ⟶ Π F.obj (U i)` whose components
are given by the restriction maps from `U j` to `U i ⊓ U j`.
-/
/-
**TopCat.Presheaf.SheafConditionEqualizerProducts.res** 是 Mathlib 中的一个定义，位于命名空间 
`TopCat.Presheaf.SheafConditionEqualizerProducts`。
形式化陈述：res : F.obj (op (iSup U)) ⟶ piOpens.{v'} F U
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `F.obj U ⟶ Π F.obj (U i)` whose components
are given by the restriction maps from `U j` to `U i ⊓ U j`.
-/
def res : F.obj (op (iSup U)) ⟶ piOpens.{v'} F U :=
  Pi.lift fun i : ι => F.map (TopologicalSpace.Opens.leSupr U i).op

set_option backward.isDefEq.respectTransparency false in
@[simp, elementwise]
/-
**TopCat.Presheaf.SheafConditionEqualizerProducts.res_** 是 Mathlib 中的一个定理，位于命名空间
 `TopCat.Presheaf.SheafConditionEqualizerProducts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem res_π (i : ι) : res F U ≫ limit.π _ ⟨i⟩ = F.map (Opens.leSupr U i).op := by
  rw [res, limit.lift_π, Fan.mk_π_app]

/-- Copy of `limit.hom_ext`, specialized to `piOpens` for use by the `ext` tactic. -/
/-
**TopCat.Presheaf.SheafConditionEqualizerProducts.piOpens.hom_ext** 是 Mathlib 中的
一个定理，位于命名空间 `TopCat.Presheaf.SheafConditionEqualizerProducts.piOpens`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasProducts C] {X : TopCat}   (F : TopCat.Presheaf C X) {ι : Type
 v'} (U : ι → TopologicalSpace.Opens ↑X) {X_1 : C}   {f f' : X_1 ⟶ TopCat.Preshe
af.SheafConditionEqualizerProducts.piOpens F U},   (∀ (j : CategoryTheory.Discre
te ι),       CategoryTheory.CategoryStruct.comp f           (CategoryTheory.Limi
ts.limit.π (CategoryTheory.Discrete.functor fun i => F.obj (Opposite.op (U i))) 
j) =         CategoryTheory.CategoryStruct.comp f'           (CategoryTheory.Lim
its.limit.π (CategoryTheory.Discrete.functor fun i => F.obj (Opposite.op (U i)))
 j)) →     f = f'
参数：F : TopCat.Presheaf C X；U : ι → TopologicalSpace.Opens ↑X；∀ (j : CategoryTheo
ry.Discrete ι),       CategoryTheory.CategoryStruct.comp f           (CategoryTh
eory.Limits.limit.π (CategoryTheory.Discrete.functor fun i => F.obj (Opposite.op
 (U i))) j) =         CategoryTheory.CategoryStruct.comp f'           (CategoryT
heory.Limits.limit.π (CategoryTheory.Discrete.functor fun i => F.obj (Opposite.o
p (U i))) j)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.limit.hom_ext`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…

--- 原说明 ---
Copy of `limit.hom_ext`, specialized to `piOpens` for use by the `ext` tactic.
-/
@[ext] theorem piOpens.hom_ext
    {X : C} {f f' : X ⟶ piOpens F U} (w : ∀ j, f ≫ limit.π _ j = f' ≫ limit.π _ j) : f = f' :=
  limit.hom_ext w

/-- Copy of `limit.hom_ext`, specialized to `piInters` for use by the `ext` tactic. -/
/-
**TopCat.Presheaf.SheafConditionEqualizerProducts.piInters.hom_ext** 是 Mathlib 中
的一个定理，位于命名空间 `TopCat.Presheaf.SheafConditionEqualizerProducts.piInters`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasProducts C] {X : TopCat}   (F : TopCat.Presheaf C X) {ι : Type
 v'} (U : ι → TopologicalSpace.Opens ↑X) {X_1 : C}   {f f' : X_1 ⟶ TopCat.Preshe
af.SheafConditionEqualizerProducts.piInters F U},   (∀ (j : CategoryTheory.Discr
ete (ι × ι)),       CategoryTheory.CategoryStruct.comp f           (CategoryTheo
ry.Limits.limit.π (CategoryTheory.Discrete.functor fun p => F.obj (Opposite.op (
U p.1 ⊓ U p.2)))             j) =         CategoryTheory.CategoryStruct.comp f' 
          (CategoryTheory.Limits.limit.π (CategoryTheory.Discrete.functor fun p 
=> F.obj (Opposite.op (U p.1 ⊓ U p.2)))             j)) →     f = f'
参数：F : TopCat.Presheaf C X；U : ι → TopologicalSpace.Opens ↑X；∀ (j : CategoryTheo
ry.Discrete (ι × ι)),       CategoryTheory.CategoryStruct.comp f           (Cate
goryTheory.Limits.limit.π (CategoryTheory.Discrete.functor fun p => F.obj (Oppos
ite.op (U p.1 ⊓ U p.2)))             j) =         CategoryTheory.CategoryStruct.
comp f'           (CategoryTheory.Limits.limit.π (CategoryTheory.Discrete.functo
r fun p => F.obj (Opposite.op (U p.1 ⊓ U p.2)))             j)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.limit.hom_ext`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…

--- 原说明 ---
Copy of `limit.hom_ext`, specialized to `piInters` for use by the `ext` tactic.
-/
@[ext] theorem piInters.hom_ext
    {X : C} {f f' : X ⟶ piInters F U} (w : ∀ j, f ≫ limit.π _ j = f' ≫ limit.π _ j) : f = f' :=
  limit.hom_ext w

set_option backward.isDefEq.respectTransparency false in
@[elementwise]
/-
**TopCat.Presheaf.SheafConditionEqualizerProducts.w** 是 Mathlib 中的一个定理，位于命名空间 `T
opCat.Presheaf.SheafConditionEqualizerProducts`。
形式化陈述：w : res F U ≫ leftRes F U = res F U ≫ rightRes F U
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.Presheaf.SheafConditionEqualizerProducts.piInters.hom_ext`：∀ {C :
 Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limi
ts.HasProducts C] {X : TopCat}   (F : TopCat.Presheaf …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
-/
theorem w : res F U ≫ leftRes F U = res F U ≫ rightRes F U := by
  dsimp [res, leftRes, rightRes]
  ext
  simp only [limit.lift_π, limit.lift_π_assoc, Fan.mk_π_app, Category.assoc]
  rw [← F.map_comp]
  rw [← F.map_comp]
  congr 1

/-- The equalizer diagram for the sheaf condition.
-/
/-
**TopCat.Presheaf.SheafConditionEqualizerProducts.diagram** 是 Mathlib 中的一个缩写定义，位
于命名空间 `TopCat.Presheaf.SheafConditionEqualizerProducts`。
形式化陈述：diagram : WalkingParallelPair ⥤ C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equalizer diagram for the sheaf condition.
-/
abbrev diagram : WalkingParallelPair ⥤ C :=
  parallelPair (leftRes.{v'} F U) (rightRes F U)

/-- The restriction map `F.obj U ⟶ Π F.obj (U i)` gives a cone over the equalizer diagram
for the sheaf condition. The sheaf condition asserts this cone is a limit cone.
-/
/-
**TopCat.Presheaf.SheafConditionEqualizerProducts.fork** 是 Mathlib 中的一个定义，位于命名空间
 `TopCat.Presheaf.SheafConditionEqualizerProducts`。
形式化陈述：fork : Fork.{v} (leftRes F U) (rightRes F U)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.Presheaf.SheafConditionEqualizerProducts.w`：w : res F U ≫ leftRes
 F U = res F U ≫ rightRes F U

--- 原说明 ---
The restriction map `F.obj U ⟶ Π F.obj (U i)` gives a cone over the equalizer di
agram
for the sheaf condition. The sheaf condition asserts this cone is a limit cone.
-/
def fork : Fork.{v} (leftRes F U) (rightRes F U) :=
  Fork.ofι _ (w F U)

@[simp]
/-
**TopCat.Presheaf.SheafConditionEqualizerProducts.fork_pt** 是 Mathlib 中的一个定理，位于命
名空间 `TopCat.Presheaf.SheafConditionEqualizerProducts`。
形式化陈述：fork_pt : (fork F U).pt = F.obj (op (iSup U))
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fork_pt : (fork F U).pt = F.obj (op (iSup U)) :=
  rfl

@[simp]
/-
**TopCat.Presheaf.SheafConditionEqualizerProducts.fork_** 是 Mathlib 中的一个定理，位于命名空
间 `TopCat.Presheaf.SheafConditionEqualizerProducts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fork_ι : (fork F U).ι = res F U :=
  rfl

@[simp]
/-
**TopCat.Presheaf.SheafConditionEqualizerProducts.fork_** 是 Mathlib 中的一个定理，位于命名空
间 `TopCat.Presheaf.SheafConditionEqualizerProducts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fork_π_app_walkingParallelPair_zero : (fork F U).π.app WalkingParallelPair.zero = res F U :=
  rfl

@[simp]
/-
**TopCat.Presheaf.SheafConditionEqualizerProducts.fork_** 是 Mathlib 中的一个定理，位于命名空
间 `TopCat.Presheaf.SheafConditionEqualizerProducts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fork_π_app_walkingParallelPair_one :
    (fork F U).π.app WalkingParallelPair.one = res F U ≫ leftRes F U :=
  rfl

variable {F} {G : Presheaf C X}

/-- Isomorphic presheaves have isomorphic `piOpens` for any cover `U`. -/
@[simp]
/-
**TopCat.Presheaf.SheafConditionEqualizerProducts.piOpens.isoOfIso** 是 Mathlib 中
的一个定义，位于命名空间 `TopCat.Presheaf.SheafConditionEqualizerProducts.piOpens`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasProducts C] →       {X : TopCat} →         {F : TopCat
.Presheaf C X} →           {ι : Type v'} →             (U : ι → TopologicalSpace
.Opens ↑X) →               {G : TopCat.Presheaf C X} →                 (F ≅ G) →
                   (TopCat.Presheaf.SheafConditionEqualizerProducts.piOpens F U 
≅                     TopCat.Presheaf.SheafConditionEqualizerProducts.piOpens G 
U)
参数：U : ι → TopologicalSpace.Opens ↑X；F ≅ G；TopCat.Presheaf.SheafConditionEqualiz
erProducts.piOpens F U ≅                     TopCat.Presheaf.SheafConditionEqual
izerProducts.piOpens G U。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Isomorphic presheaves have isomorphic `piOpens` for any cover `U`.
-/
def piOpens.isoOfIso (α : F ≅ G) : piOpens F U ≅ piOpens.{v'} G U :=
  Pi.mapIso fun _ => α.app _

/-- Isomorphic presheaves have isomorphic `piInters` for any cover `U`. -/
@[simp]
/-
**TopCat.Presheaf.SheafConditionEqualizerProducts.piInters.isoOfIso** 是 Mathlib 
中的一个定义，位于命名空间 `TopCat.Presheaf.SheafConditionEqualizerProducts.piInters`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasProducts C] →       {X : TopCat} →         {F : TopCat
.Presheaf C X} →           {ι : Type v'} →             (U : ι → TopologicalSpace
.Opens ↑X) →               {G : TopCat.Presheaf C X} →                 (F ≅ G) →
                   (TopCat.Presheaf.SheafConditionEqualizerProducts.piInters F U
 ≅                     TopCat.Presheaf.SheafConditionEqualizerProducts.piInters 
G U)
参数：U : ι → TopologicalSpace.Opens ↑X；F ≅ G；TopCat.Presheaf.SheafConditionEqualiz
erProducts.piInters F U ≅                     TopCat.Presheaf.SheafConditionEqua
lizerProducts.piInters G U。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Isomorphic presheaves have isomorphic `piInters` for any cover `U`.
-/
def piInters.isoOfIso (α : F ≅ G) : piInters F U ≅ piInters.{v'} G U :=
  Pi.mapIso fun _ => α.app _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Isomorphic presheaves have isomorphic sheaf condition diagrams. -/
/-
**TopCat.Presheaf.SheafConditionEqualizerProducts.diagram.isoOfIso** 是 Mathlib 中
的一个定义，位于命名空间 `TopCat.Presheaf.SheafConditionEqualizerProducts.diagram`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasProducts C] →       {X : TopCat} →         {F : TopCat
.Presheaf C X} →           {ι : Type v'} →             (U : ι → TopologicalSpace
.Opens ↑X) →               {G : TopCat.Presheaf C X} →                 (F ≅ G) →
                   (TopCat.Presheaf.SheafConditionEqualizerProducts.diagram F U 
≅                     TopCat.Presheaf.SheafConditionEqualizerProducts.diagram G 
U)
参数：U : ι → TopologicalSpace.Opens ↑X；F ≅ G；TopCat.Presheaf.SheafConditionEqualiz
erProducts.diagram F U ≅                     TopCat.Presheaf.SheafConditionEqual
izerProducts.diagram G U。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Isomorphic presheaves have isomorphic sheaf condition diagrams.
-/
def diagram.isoOfIso (α : F ≅ G) : diagram F U ≅ diagram.{v'} G U :=
  NatIso.ofComponents (by
    rintro ⟨⟩
    · exact piOpens.isoOfIso U α
    · exact piInters.isoOfIso U α)
    (by
      rintro ⟨⟩ ⟨⟩ ⟨⟩
      · simp
      · dsimp
        refine Pi.hom_ext _ _ fun b ↦ ?_
        simp [leftRes]
      · dsimp [diagram]
        refine Pi.hom_ext _ _ fun b ↦ ?_
        simp [rightRes]
      · simp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `F G : Presheaf C X` are isomorphic presheaves,
then the `fork F U`, the canonical cone of the sheaf condition diagram for `F`,
is isomorphic to `fork F G` postcomposed with the corresponding isomorphism between
sheaf condition diagrams.
-/
/-
**TopCat.Presheaf.SheafConditionEqualizerProducts.fork.isoOfIso** 是 Mathlib 中的一个
定义，位于命名空间 `TopCat.Presheaf.SheafConditionEqualizerProducts.fork`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasProducts C] →       {X : TopCat} →         {F : TopCat
.Presheaf C X} →           {ι : Type v'} →             (U : ι → TopologicalSpace
.Opens ↑X) →               {G : TopCat.Presheaf C X} →                 (α : F ≅ 
G) →                   TopCat.Presheaf.SheafConditionEqualizerProducts.fork F U 
≅                     (CategoryTheory.Limits.Cone.postcompose                   
        (TopCat.Presheaf.SheafConditionEqualizerProducts.diagram.isoOfIso U α).i
nv).obj                       (TopCat.Presheaf.SheafConditionEqualizerProducts.f
ork G U)
参数：U : ι → TopologicalSpace.Opens ↑X；α : F ≅ G；CategoryTheory.Limits.Cone.postco
mpose                           (TopCat.Presheaf.SheafConditionEqualizerProducts
.diagram.isoOfIso U α).inv；TopCat.Presheaf.SheafConditionEqualizerProducts.fork 
G U。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F G : Presheaf C X` are isomorphic presheaves,
then the `fork F U`, the canonical cone of the sheaf condition diagram for `F`,
is isomorphic to `fork F G` postcomposed with the corresponding isomorphism betw
een
sheaf condition diagrams.
-/
def fork.isoOfIso (α : F ≅ G) :
    fork F U ≅ (Cone.postcompose (diagram.isoOfIso U α).inv).obj (fork G U) := by
  fapply Fork.ext
  · apply α.app
  · dsimp
    refine Pi.hom_ext _ _ fun b ↦ ?_
    dsimp only [Fork.ι]
    simp [res, diagram.isoOfIso]

end SheafConditionEqualizerProducts

/-- The sheaf condition for a `F : Presheaf C X` requires that the morphism
`F.obj U ⟶ ∏ᶜ F.obj (U i)` (where `U` is some open set which is the union of the `U i`)
is the equalizer of the two morphisms
`∏ᶜ F.obj (U i) ⟶ ∏ᶜ F.obj (U i) ⊓ (U j)`.
-/
/-
**TopCat.Presheaf.IsSheafEqualizerProducts** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.Pre
sheaf`。
形式化陈述：IsSheafEqualizerProducts (F : Presheaf.{v', v, u} C X) : Prop
参数：F : Presheaf.{v', v, u} C X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sheaf condition for a `F : Presheaf C X` requires that the morphism
`F.obj U ⟶ ∏ᶜ F.obj (U i)` (where `U` is some open set which is the union of the
 `U i`)
is the equalizer of the two morphisms
`∏ᶜ F.obj (U i) ⟶ ∏ᶜ F.obj (U i) ⊓ (U j)`.
-/
def IsSheafEqualizerProducts (F : Presheaf.{v', v, u} C X) : Prop :=
  ∀ ⦃ι : Type v'⦄ (U : ι → Opens X), Nonempty (IsLimit (SheafConditionEqualizerProducts.fork F U))

/-!
The remainder of this file shows that the "equalizer products" sheaf condition is equivalent
to the "pairwise intersections" sheaf condition.
-/


namespace SheafConditionPairwiseIntersections

open CategoryTheory.Pairwise CategoryTheory.Pairwise.Hom

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Implementation of `SheafConditionPairwiseIntersections.coneEquiv`. -/
@[simps]
/-
**TopCat.Presheaf.SheafConditionPairwiseIntersections.coneEquivFunctorObj** 是 Ma
thlib 中的一个定义，位于命名空间 `TopCat.Presheaf.SheafConditionPairwiseIntersections`。
形式化陈述：coneEquivFunctorObj (c : Cone ((diagram U).op ⋙ F)) : Cone (SheafCondition
EqualizerProducts.diagram F U) where pt
参数：c : Cone ((diagram U).op ⋙ F)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Implementation of `SheafConditionPairwiseIntersections.coneEquiv`.
-/
def coneEquivFunctorObj (c : Cone ((diagram U).op ⋙ F)) :
    Cone (SheafConditionEqualizerProducts.diagram F U) where
  pt := c.pt
  π :=
    { app := fun Z =>
        WalkingParallelPair.casesOn Z (Pi.lift fun i : ι => c.π.app (op (single i)))
          (Pi.lift fun b : ι × ι => c.π.app (op (pair b.1 b.2)))
      naturality := fun Y Z f => by
        cases Y <;> cases Z <;> cases f
        · dsimp
          ext
          simp
        · dsimp
          ext ij
          rcases ij with ⟨i, j⟩
          simpa [SheafConditionEqualizerProducts.leftRes]
            using! c.π.naturality (Quiver.Hom.op (Hom.left i j))
        · dsimp
          ext ij
          rcases ij with ⟨i, j⟩
          simpa [SheafConditionEqualizerProducts.rightRes]
            using! c.π.naturality (Quiver.Hom.op (Hom.right i j))
        · dsimp
          ext
          simp }

section

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Implementation of `SheafConditionPairwiseIntersections.coneEquiv`. -/
@[simps!]
/-
**TopCat.Presheaf.SheafConditionPairwiseIntersections.coneEquivFunctor** 是 Mathl
ib 中的一个定义，位于命名空间 `TopCat.Presheaf.SheafConditionPairwiseIntersections`。
形式化陈述：coneEquivFunctor : Limits.Cone ((diagram U).op ⋙ F) ⥤ Limits.Cone (SheafCo
nditionEqualizerProducts.diagram F U) where obj c
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Implementation of `SheafConditionPairwiseIntersections.coneEquiv`.
-/
def coneEquivFunctor :
    Limits.Cone ((diagram U).op ⋙ F) ⥤
      Limits.Cone (SheafConditionEqualizerProducts.diagram F U) where
  obj c := coneEquivFunctorObj F U c
  map {c c'} f :=
    { hom := f.hom
      w := fun j => by
        cases j <;>
          · dsimp
            ext
            simp }

end

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Implementation of `SheafConditionPairwiseIntersections.coneEquiv`. -/
@[simps]
/-
**TopCat.Presheaf.SheafConditionPairwiseIntersections.coneEquivInverseObj** 是 Ma
thlib 中的一个定义，位于命名空间 `TopCat.Presheaf.SheafConditionPairwiseIntersections`。
形式化陈述：coneEquivInverseObj (c : Limits.Cone (SheafConditionEqualizerProducts.diag
ram F U)) : Limits.Cone ((diagram U).op ⋙ F) where pt
参数：c : Limits.Cone (SheafConditionEqualizerProducts.diagram F U)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Implementation of `SheafConditionPairwiseIntersections.coneEquiv`.
-/
def coneEquivInverseObj (c : Limits.Cone (SheafConditionEqualizerProducts.diagram F U)) :
    Limits.Cone ((diagram U).op ⋙ F) where
  pt := c.pt
  π :=
    { app := by
        intro x
        induction x with | op x => ?_
        rcases x with (⟨i⟩ | ⟨i, j⟩)
        · exact c.π.app WalkingParallelPair.zero ≫ Pi.π _ i
        · exact c.π.app WalkingParallelPair.one ≫ Pi.π _ (i, j)
      naturality := by
        intro x y f
        induction x with | op x => ?_
        induction y with | op y => ?_
        have ef : f = f.unop.op := rfl
        revert ef
        generalize f.unop = f'
        rintro rfl
        rcases x with (⟨i⟩ | ⟨⟩) <;> rcases y with (⟨⟩ | ⟨j, j⟩) <;> rcases f' with ⟨⟩
        · dsimp
          rw [F.map_id]
          simp
        · dsimp
          simp only [Category.id_comp, Category.assoc]
          have h := c.π.naturality WalkingParallelPairHom.left
          dsimp [SheafConditionEqualizerProducts.leftRes] at h
          simp only [Category.id_comp] at h
          have h' := h =≫ Pi.π _ (i, j)
          rw [h']
          simp only [Category.assoc, limit.lift_π, Fan.mk_π_app]
          rfl
        · dsimp
          simp only [Category.id_comp, Category.assoc]
          have h := c.π.naturality WalkingParallelPairHom.right
          dsimp [SheafConditionEqualizerProducts.rightRes] at h
          simp only [Category.id_comp] at h
          have h' := h =≫ Pi.π _ (j, i)
          rw [h']
          simp
          rfl
        · dsimp
          rw [F.map_id]
          simp }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Implementation of `SheafConditionPairwiseIntersections.coneEquiv`. -/
@[simps!]
/-
**TopCat.Presheaf.SheafConditionPairwiseIntersections.coneEquivInverse** 是 Mathl
ib 中的一个定义，位于命名空间 `TopCat.Presheaf.SheafConditionPairwiseIntersections`。
形式化陈述：coneEquivInverse : Limits.Cone (SheafConditionEqualizerProducts.diagram F 
U) ⥤ Limits.Cone ((diagram U).op ⋙ F) where obj c
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Implementation of `SheafConditionPairwiseIntersections.coneEquiv`.
-/
def coneEquivInverse :
    Limits.Cone (SheafConditionEqualizerProducts.diagram F U) ⥤
      Limits.Cone ((diagram U).op ⋙ F) where
  obj c := coneEquivInverseObj F U c
  map {c c'} f :=
    { hom := f.hom
      w := by
        intro x
        induction x with | op x => ?_
        rcases x with (⟨i⟩ | ⟨i, j⟩)
        · dsimp
          dsimp only [Fork.ι]
          rw [← f.w WalkingParallelPair.zero, Category.assoc]
        · dsimp
          rw [← f.w WalkingParallelPair.one, Category.assoc] }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Implementation of `SheafConditionPairwiseIntersections.coneEquiv`. -/
@[simps]
/-
**TopCat.Presheaf.SheafConditionPairwiseIntersections.coneEquivUnitIsoApp** 是 Ma
thlib 中的一个定义，位于命名空间 `TopCat.Presheaf.SheafConditionPairwiseIntersections`。
形式化陈述：coneEquivUnitIsoApp (c : Cone ((diagram U).op ⋙ F)) : (𝟭 (Cone ((diagram U
).op ⋙ F))).obj c ≅ (coneEquivFunctor F U ⋙ coneEquivInverse F U).obj c where ho
m
参数：c : Cone ((diagram U).op ⋙ F)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Implementation of `SheafConditionPairwiseIntersections.coneEquiv`.
-/
def coneEquivUnitIsoApp (c : Cone ((diagram U).op ⋙ F)) :
    (𝟭 (Cone ((diagram U).op ⋙ F))).obj c ≅
      (coneEquivFunctor F U ⋙ coneEquivInverse F U).obj c where
  hom :=
    { hom := 𝟙 _
      w := fun j => by
        induction j with | op j => ?_
        rcases j with ⟨⟩ <;>
        · dsimp [coneEquivInverse]
          simp only [Limits.Fan.mk_π_app, Category.id_comp, Limits.limit.lift_π] }
  inv :=
    { hom := 𝟙 _
      w := fun j => by
        induction j with | op j => ?_
        rcases j with ⟨⟩ <;>
        · dsimp [coneEquivInverse]
          simp only [Limits.Fan.mk_π_app, Category.id_comp, Limits.limit.lift_π] }

set_option backward.defeqAttrib.useBackward true in
/-- Implementation of `SheafConditionPairwiseIntersections.coneEquiv`. -/
@[simps!]
/-
**TopCat.Presheaf.SheafConditionPairwiseIntersections.coneEquivUnitIso** 是 Mathl
ib 中的一个定义，位于命名空间 `TopCat.Presheaf.SheafConditionPairwiseIntersections`。
形式化陈述：coneEquivUnitIso : 𝟭 (Limits.Cone ((diagram U).op ⋙ F)) ≅ coneEquivFunctor
 F U ⋙ coneEquivInverse F U
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Implementation of `SheafConditionPairwiseIntersections.coneEquiv`.
-/
def coneEquivUnitIso :
    𝟭 (Limits.Cone ((diagram U).op ⋙ F)) ≅ coneEquivFunctor F U ⋙ coneEquivInverse F U :=
  NatIso.ofComponents (coneEquivUnitIsoApp F U)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Implementation of `SheafConditionPairwiseIntersections.coneEquiv`. -/
@[simps!]
/-
**TopCat.Presheaf.SheafConditionPairwiseIntersections.coneEquivCounitIso** 是 Mat
hlib 中的一个定义，位于命名空间 `TopCat.Presheaf.SheafConditionPairwiseIntersections`。
形式化陈述：coneEquivCounitIso : coneEquivInverse F U ⋙ coneEquivFunctor F U ≅ 𝟭 (Limi
ts.Cone (SheafConditionEqualizerProducts.diagram F U))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Implementation of `SheafConditionPairwiseIntersections.coneEquiv`.
-/
def coneEquivCounitIso :
    coneEquivInverse F U ⋙ coneEquivFunctor F U ≅
      𝟭 (Limits.Cone (SheafConditionEqualizerProducts.diagram F U)) :=
  NatIso.ofComponents
    (fun c =>
      { hom :=
          { hom := 𝟙 _
            w := by
              rintro ⟨_ | _⟩
              · dsimp
                ext
                simp
              · dsimp
                ext
                simp }
        inv :=
          { hom := 𝟙 _
            w := by
              rintro ⟨_ | _⟩
              · dsimp
                ext
                simp
              · dsimp
                ext
                simp } })
    fun {c d} f => by
    ext
    dsimp
    simp only [Category.comp_id, Category.id_comp]

set_option backward.defeqAttrib.useBackward true in
/--
Cones over `diagram U ⋙ F` are the same as a cones over the usual sheaf condition equalizer diagram.
-/
@[simps]
/-
**TopCat.Presheaf.SheafConditionPairwiseIntersections.coneEquiv** 是 Mathlib 中的一个
定义，位于命名空间 `TopCat.Presheaf.SheafConditionPairwiseIntersections`。
形式化陈述：coneEquiv : Limits.Cone ((diagram U).op ⋙ F) ≌ Limits.Cone (SheafCondition
EqualizerProducts.diagram F U) where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Cones over `diagram U ⋙ F` are the same as a cones over the usual sheaf conditio
n equalizer diagram.
-/
def coneEquiv :
    Limits.Cone ((diagram U).op ⋙ F) ≌
      Limits.Cone (SheafConditionEqualizerProducts.diagram F U) where
  functor := coneEquivFunctor F U
  inverse := coneEquivInverse F U
  unitIso := coneEquivUnitIso F U
  counitIso := coneEquivCounitIso F U

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `SheafConditionEqualizerProducts.fork` is an equalizer,
then `F.mapCone (cone U)` is a limit cone.
-/
/-
**TopCat.Presheaf.SheafConditionPairwiseIntersections.isLimitMapConeOfIsLimitShe
afConditionFork** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.Presheaf.SheafConditionPairwis
eIntersections`。
形式化陈述：isLimitMapConeOfIsLimitSheafConditionFork (P : IsLimit (SheafConditionEqua
lizerProducts.fork F U)) : IsLimit (F.mapCone (cocone U).op)
参数：P : IsLimit (SheafConditionEqualizerProducts.fork F U)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `SheafConditionEqualizerProducts.fork` is an equalizer,
then `F.mapCone (cone U)` is a limit cone.
-/
def isLimitMapConeOfIsLimitSheafConditionFork
    (P : IsLimit (SheafConditionEqualizerProducts.fork F U)) : IsLimit (F.mapCone (cocone U).op) :=
  IsLimit.ofIsoLimit ((IsLimit.ofConeEquiv (coneEquiv F U).symm).symm P)
    { hom :=
        { hom := 𝟙 _
          w := by
            intro x
            induction x with | op x => ?_
            rcases x with ⟨⟩
            · simp
              rfl
            · dsimp [coneEquivInverse, SheafConditionEqualizerProducts.res,
                SheafConditionEqualizerProducts.leftRes]
              simp only [limit.lift_π, limit.lift_π_assoc, Category.id_comp, Fan.mk_π_app,
                Category.assoc]
              rw [← F.map_comp]
              rfl }
      inv :=
        { hom := 𝟙 _
          w := by
            intro x
            induction x with | op x => ?_
            rcases x with ⟨⟩
            · simp
              rfl
            · dsimp [coneEquivInverse, SheafConditionEqualizerProducts.res,
                SheafConditionEqualizerProducts.leftRes]
              simp only [limit.lift_π, limit.lift_π_assoc, Category.id_comp, Fan.mk_π_app,
                Category.assoc]
              rw [← F.map_comp]
              rfl } }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `F.mapCone (cone U)` is a limit cone,
then `SheafConditionEqualizerProducts.fork` is an equalizer.
-/
/-
**TopCat.Presheaf.SheafConditionPairwiseIntersections.isLimitSheafConditionForkO
fIsLimitMapCone** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.Presheaf.SheafConditionPairwis
eIntersections`。
形式化陈述：isLimitSheafConditionForkOfIsLimitMapCone (Q : IsLimit (F.mapCone (cocone 
U).op)) : IsLimit (SheafConditionEqualizerProducts.fork F U)
参数：Q : IsLimit (F.mapCone (cocone U).op)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `F.mapCone (cone U)` is a limit cone,
then `SheafConditionEqualizerProducts.fork` is an equalizer.
-/
def isLimitSheafConditionForkOfIsLimitMapCone (Q : IsLimit (F.mapCone (cocone U).op)) :
    IsLimit (SheafConditionEqualizerProducts.fork F U) :=
  IsLimit.ofIsoLimit ((IsLimit.ofConeEquiv (coneEquiv F U)).symm Q)
    { hom :=
        { hom := 𝟙 _
          w := by
            rintro ⟨⟩
            · simp
              rfl
            · dsimp
              ext
              dsimp [coneEquivInverse, SheafConditionEqualizerProducts.res,
                SheafConditionEqualizerProducts.leftRes]
              simp only [limit.lift_π, limit.lift_π_assoc, Category.id_comp, Fan.mk_π_app,
                Category.assoc]
              rw [← F.map_comp]
              rfl }
      inv :=
        { hom := 𝟙 _
          w := by
            rintro ⟨⟩
            · simp
              rfl
            · dsimp
              ext
              dsimp [coneEquivInverse, SheafConditionEqualizerProducts.res,
                SheafConditionEqualizerProducts.leftRes]
              simp only [limit.lift_π, limit.lift_π_assoc, Category.id_comp, Fan.mk_π_app,
                Category.assoc]
              rw [← F.map_comp]
              rfl } }

end SheafConditionPairwiseIntersections

open SheafConditionPairwiseIntersections

/-- The sheaf condition in terms of an equalizer diagram is equivalent
to the default sheaf condition.
-/
/-
**TopCat.Presheaf.isSheaf_iff_isSheafEqualizerProducts** 是 Mathlib 中的一个定理，位于命名空间
 `TopCat.Presheaf`。
形式化陈述：isSheaf_iff_isSheafEqualizerProducts (F : Presheaf C X) : F.IsSheaf ↔ F.Is
SheafEqualizerProducts
参数：F : Presheaf C X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `TopCat.Presheaf.isSheaf_iff_isSheafPairwiseIntersections`：isSheaf_iff_is
SheafPairwiseIntersections : F.IsSheaf ↔ F.IsSheafPairwiseIntersections

--- 原说明 ---
The sheaf condition in terms of an equalizer diagram is equivalent
to the default sheaf condition.
-/
theorem isSheaf_iff_isSheafEqualizerProducts (F : Presheaf C X) :
    F.IsSheaf ↔ F.IsSheafEqualizerProducts :=
  (isSheaf_iff_isSheafPairwiseIntersections F).trans <|
    Iff.intro (fun h _ U => ⟨isLimitSheafConditionForkOfIsLimitMapCone F U (h U).some⟩) fun h _ U =>
      ⟨isLimitMapConeOfIsLimitSheafConditionFork F U (h U).some⟩

end Presheaf

end TopCat

