/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ShrinkYoneda
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Point.Basic

/-!
# Alternative constructor for points

Let `J` be a Grothendieck topology on a category `C`. We provide a constructor
`Point.ofIsCofiltered` for points for `J` which takes as inputs:
- a functor `p : N ⥤ C` where `N` is cofiltered and initially small
- the assumption that for any covering sieve `R` of `X`,
  any morphism `f : p.obj U ⟶ X`, there exists a morphism `g : Y ⟶ X` in `R`,
  a morphism `q : V ⟶ U` in `N` and a morphism `a : p.obj V ⟶ Y` such
  that `a ≫ g = p.map q ≫ f`.
We show that the fiber of a presheaf for the constructed point identifies
to a colimit indexed by the category `N`.

-/

@[expose] public section

universe w v'' v' v u'' u' u

namespace CategoryTheory

open Limits Opposite ConcreteCategory

namespace GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C]

variable [LocallySmall.{w} C] {N : Type u'} [Category.{v'} N]
  (p : N ⥤ C) [InitiallySmall.{w} N]
  {J : GrothendieckTopology C}

namespace ofIsCofiltered

local instance : HasColimitsOfShape Nᵒᵖ (Type w) :=
  hasColimitsOfShape_of_finallySmall _ _

/-- Given a functor `p : N ⥤ C`, this is the functor `C ⥤ Type w` which sends
`X : C` to the colimit of types of morphisms `p.obj U ⟶ X` for `U : N`. -/
/-
**CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered.fiber** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered`。
形式化陈述：fiber : C ⥤ Type w
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered.instHasColimits
OfShapeOppositeType`：∀ {N : Type u'} [inst : CategoryTheory.Category.{v', u'} N]
 [CategoryTheory.InitiallySmall N],   CategoryTheory.Limits.HasColimitsOfShape N
ᵒ…

--- 原说明 ---
Given a functor `p : N ⥤ C`, this is the functor `C ⥤ Type w` which sends
`X : C` to the colimit of types of morphisms `p.obj U ⟶ X` for `U : N`.
-/
noncomputable def fiber : C ⥤ Type w :=
  shrinkYoneda.{w} ⋙ (Functor.whiskeringLeft _ _ (Type w)).obj p.op ⋙ colim

variable {p} in
/-- Constructor for elements in `fiber`. -/
/-
**CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered.fiberMk** 是 Mathlib 中
的一个定义，位于命名空间 `CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered`。
形式化陈述：fiberMk {U : N} {X : C} (f : p.obj U ⟶ X) : (fiber.{w} p).obj X
参数：f : p.obj U ⟶ X。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Constructor for elements in `fiber`.
-/
noncomputable def fiberMk {U : N} {X : C} (f : p.obj U ⟶ X) : (fiber.{w} p).obj X :=
  colimit.ι (p.op ⋙ shrinkYoneda.{w}.obj X) (op U)
    (shrinkYonedaObjObjEquiv.symm f)

variable {p} in
/-
**CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered.fiberMk_jointly_surje
ctive** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.Point.ofIsC
ofiltered`。
形式化陈述：fiberMk_jointly_surjective {X : C} (x : (fiber.{w} p).obj X) : exists (U :
 N) (f : p.obj U ⟶ X), fiberMk f = x
参数：x : (fiber.{w} p).obj X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered.instHasColimits
OfShapeOppositeType`：∀ {N : Type u'} [inst : CategoryTheory.Category.{v', u'} N]
 [CategoryTheory.InitiallySmall N],   CategoryTheory.Limits.HasColimitsOfShape N
ᵒ…
· 使用定理 `CategoryTheory.Limits.Types.jointly_surjective_of_isColimit`：jointly_sur
jective_of_isColimit {F : J ⥤ Type u} {t : Cocone F} (h : IsColimit t) (x : t.pt
) : exists j y, t.ι.app j y = x
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
-/
lemma fiberMk_jointly_surjective {X : C} (x : (fiber.{w} p).obj X) :
    ∃ (U : N) (f : p.obj U ⟶ X), fiberMk f = x := by
  obtain ⟨U, f, rfl⟩ := Types.jointly_surjective_of_isColimit
    (colimit.isColimit (p.op ⋙ shrinkYoneda.{w}.obj X)) x
  obtain ⟨f, rfl⟩ := shrinkYonedaObjObjEquiv.symm.surjective f
  exact ⟨U.unop, f, rfl⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable {p} in
/-
**CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered.exists_of_fiberMk_eq_
fiberMk** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.Point.ofI
sCofiltered`。
形式化陈述：exists_of_fiberMk_eq_fiberMk [IsCofiltered N] {U : N} {X : C} {f₁ f₂ : p.o
bj U ⟶ X} (hf : fiberMk f₁ = fiberMk f₂) : exists (V : N) (g : V ⟶ U), p.map g ≫
 f₁ = p.map g ≫ f₂
参数：hf : fiberMk f₁ = fiberMk f₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered.instHasColimits
OfShapeOppositeType`：∀ {N : Type u'} [inst : CategoryTheory.Category.{v', u'} N]
 [CategoryTheory.InitiallySmall N],   CategoryTheory.Limits.HasColimitsOfShape N
ᵒ…
· 使用定理 `CategoryTheory.Limits.Types.FilteredColimit.isColimit_eq_iff'`：isColimit
_eq_iff' {t : Cocone F} (ht : IsColimit t) {i : J} (x y : F.obj i) : t.ι.app i x
 = t.ι.app i y ↔ exists (j : _) (f : i ⟶ j), F.map …
· 使用定理 `CategoryTheory.IsCofiltered.toIsCofilteredOrEmpty`：∀ {C : Type u} {inst 
: CategoryTheory.Category.{v, u} C} [self : CategoryTheory.IsCofiltered C],   Ca
tegoryTheory.IsCofilteredOrEmpty C
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm`：shrink
Yoneda_obj_map_shrinkYonedaObjObjEquiv_symm {X : C} {Y Y' : Cᵒᵖ} (g : Y ⟶ Y') (f
 : Y.unop ⟶ X) : (shrinkYoneda.obj _).map g (shrinkYon…
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
-/
lemma exists_of_fiberMk_eq_fiberMk [IsCofiltered N]
    {U : N} {X : C} {f₁ f₂ : p.obj U ⟶ X} (hf : fiberMk f₁ = fiberMk f₂) :
    ∃ (V : N) (g : V ⟶ U), p.map g ≫ f₁ = p.map g ≫ f₂ := by
  obtain ⟨V, g, hg⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff'
      (colimit.isColimit (p.op ⋙ shrinkYoneda.{w}.obj X)) _ _).1 hf
  refine ⟨V.unop, g.unop, ?_⟩
  simpa [shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm.{w}] using hg

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered.fiberMk_map_comp** 是 
Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered`
。
形式化陈述：fiberMk_map_comp {U V : N} (g : V ⟶ U) {X : C} (f : p.obj U ⟶ X) : fiberMk
.{w} (p.map g ≫ f) = fiberMk.{w} f
参数：g : V ⟶ U；f : p.obj U ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered.instHasColimits
OfShapeOppositeType`：∀ {N : Type u'} [inst : CategoryTheory.Category.{v', u'} N]
 [CategoryTheory.InitiallySmall N],   CategoryTheory.Limits.HasColimitsOfShape N
ᵒ…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.Limits.colimit.w`：∀ {J : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]   
(F : CategoryTheory.F…
· 使用引理 `CategoryTheory.shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm`：shrink
Yoneda_obj_map_shrinkYonedaObjObjEquiv_symm {X : C} {Y Y' : Cᵒᵖ} (g : Y ⟶ Y') (f
 : Y.unop ⟶ X) : (shrinkYoneda.obj _).map g (shrinkYon…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fiberMk_map_comp {U V : N} (g : V ⟶ U) {X : C} (f : p.obj U ⟶ X) :
    fiberMk.{w} (p.map g ≫ f) = fiberMk.{w} f := by
  simp [fiberMk, ← dsimp% congr_hom (colimit.w (p.op ⋙ shrinkYoneda.{w}.obj X) g.op)
        (shrinkYonedaObjObjEquiv.symm f),
    fiber, shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm.{w}]

@[simp]
/-
**CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered.fiberMk_map** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered`。
形式化陈述：fiberMk_map {U V : N} (g : V ⟶ U) : fiberMk.{w} (p.map g) = fiberMk.{w} (𝟙
 (p.obj U))
参数：g : V ⟶ U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered.fiberMk_map_com
p`：fiberMk_map_comp {U V : N} (g : V ⟶ U) {X : C} (f : p.obj U ⟶ X) : fiberMk.{w
} (p.map g ≫ f) = fiberMk.{w} f
-/
lemma fiberMk_map {U V : N} (g : V ⟶ U) :
    fiberMk.{w} (p.map g) = fiberMk.{w} (𝟙 (p.obj U)) := by
  simpa using fiberMk_map_comp (p := p) g (𝟙 (p.obj U))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered.fiber_map_fiberMk** 是
 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
`。
形式化陈述：fiber_map_fiberMk {U : N} {X : C} (f : p.obj U ⟶ X) {Y : C} (g : X ⟶ Y) : 
(fiber p).map g (fiberMk.{w} f) = fiberMk.{w} (f ≫ g)
参数：f : p.obj U ⟶ X；g : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered.instHasColimits
OfShapeOppositeType`：∀ {N : Type u'} [inst : CategoryTheory.Category.{v', u'} N]
 [CategoryTheory.InitiallySmall N],   CategoryTheory.Limits.HasColimitsOfShape N
ᵒ…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.Limits.ι_colimMap`：∀ {J : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]  
 {F G : CategoryTheory…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用引理 `CategoryTheory.shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm`：shrink
Yoneda_map_app_shrinkYonedaObjObjEquiv_symm {X X' : C} {Y : Cᵒᵖ} (f : Y.unop ⟶ X
) (g : X ⟶ X') : (shrinkYoneda.map g).app _ (shrinkYon…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fiber_map_fiberMk {U : N} {X : C} (f : p.obj U ⟶ X) {Y : C} (g : X ⟶ Y) :
    (fiber p).map g (fiberMk.{w} f) = fiberMk.{w} (f ≫ g) :=
  (congr_hom (ι_colimMap (p.op.whiskerLeft (shrinkYoneda.{w}.map g)) (op U))
    (shrinkYonedaObjObjEquiv.symm f)).trans (by
      simp [fiberMk, shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm.{w}])

/-- A functor `N ⥤ (fiber p).Elements` which is initial when `N`
is cofiltered and initially small. -/
@[simps]
/-
**CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered.functor** 是 Mathlib 中
的一个定义，位于命名空间 `CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered`。
形式化陈述：functor : N ⥤ (fiber.{w} p).Elements where obj U
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `N ⥤ (fiber p).Elements` which is initial when `N`
is cofiltered and initially small.
-/
noncomputable def functor : N ⥤ (fiber.{w} p).Elements where
  obj U := Functor.elementsMk _ (p.obj U) (fiberMk (𝟙 _))
  map {U V} f := CategoryOfElements.homMk _ _ (p.map f) (by simp)

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered.** 是 Mathlib 中的一个实例，位
于命名空间 `CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsCofiltered N] : (functor.{w} p).Initial := by
  refine Functor.initial_of_exists_of_isCofiltered _ ?_ ?_
  · rintro ⟨X, x⟩
    obtain ⟨U, f, rfl⟩ := fiberMk_jointly_surjective x
    exact ⟨U, f, by simp⟩
  · rintro ⟨X, x⟩ V ⟨φ₁, hφ₁⟩ ⟨φ₂, hφ₂⟩
    obtain ⟨U, f, rfl⟩ := fiberMk_jointly_surjective x
    obtain ⟨W, g, hg⟩ := exists_of_fiberMk_eq_fiberMk
      (show fiberMk.{w} φ₁ = fiberMk.{w} φ₂ by simpa using hφ₁.trans hφ₂.symm)
    exact ⟨_, g, by cat_disch⟩
/-
**CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered.** 是 Mathlib 中的一个实例，位
于命名空间 `CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsCofiltered N] :
    InitiallySmall.{w} (fiber.{w} p).Elements :=
  initiallySmall_of_initial_of_initiallySmall (functor.{w} p)
/-
**CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered.** 是 Mathlib 中的一个实例，位
于命名空间 `CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsCofiltered N] :
    IsCofiltered (ofIsCofiltered.fiber p).Elements :=
  IsCofiltered.of_initial (functor.{w} p)

end ofIsCofiltered

variable [IsCofiltered N]
  (hp : ∀ ⦃X : C⦄ (R : Sieve X) (_ : R ∈ J X) ⦃U : N⦄ (f : p.obj U ⟶ X),
    ∃ (Y : C) (g : Y ⟶ X) (_ : R g) (V : N) (q : V ⟶ U) (a : p.obj V ⟶ Y),
      a ≫ g = p.map q ≫ f)

open ofIsCofiltered

/-- Constructor for points of Grothendieck topologies `J : GrothendieckTopology C`
that are given by a functor `p : N ⥤ C` from a cofiltered and initially small
category `N`. -/
@[simps]
/-
**CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：ofIsCofiltered : Point.{w} J where fiber
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for points of Grothendieck topologies `J : GrothendieckTopology C`
that are given by a functor `p : N ⥤ C` from a cofiltered and initially small
category `N`.
-/
noncomputable def ofIsCofiltered :
    Point.{w} J where
  fiber := ofIsCofiltered.fiber p
  jointly_surjective {X} R hR x := by
    obtain ⟨U, f, rfl⟩ := fiberMk_jointly_surjective x
    obtain ⟨Y, g, hg, V, q, a, ha⟩ := hp R hR f
    exact ⟨Y, g, hg, fiberMk a, by simp [ha]⟩

variable {A : Type u''} [Category.{v''} A] [HasColimitsOfSize.{w, w} A]

/-- The canonical maps `P.obj (op (p.obj U)) ⟶ (ofIsCofiltered p hp).presheafFiber.obj P`
that are part of the colimit cocone `presheafFiberOfIsCofilteredCocone`. -/
/-
**CategoryTheory.GrothendieckTopology.Point.toPresheafFiberOfIsCofiltered** 是 Ma
thlib 中的一个定义，位于命名空间 `CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：toPresheafFiberOfIsCofiltered (U : N) (P : Cᵒᵖ ⥤ A) : P.obj (op (p.obj U))
 ⟶ (ofIsCofiltered p hp).presheafFiber.obj P
参数：U : N；P : Cᵒᵖ ⥤ A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical maps `P.obj (op (p.obj U)) ⟶ (ofIsCofiltered p hp).presheafFiber.o
bj P`
that are part of the colimit cocone `presheafFiberOfIsCofilteredCocone`.
-/
noncomputable def toPresheafFiberOfIsCofiltered (U : N) (P : Cᵒᵖ ⥤ A) :
    P.obj (op (p.obj U)) ⟶ (ofIsCofiltered p hp).presheafFiber.obj P :=
  (ofIsCofiltered p hp).toPresheafFiber _ (fiberMk (𝟙 _)) P

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.GrothendieckTopology.Point.toPresheafFiberOfIsCofiltered_w** 是 
Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：toPresheafFiberOfIsCofiltered_w {V U : N} (f : V ⟶ U) (P : Cᵒᵖ ⥤ A) : P.ma
p (p.map f).op ≫ toPresheafFiberOfIsCofiltered p hp V P = toPresheafFiberOfIsCof
iltered p hp U P
参数：f : V ⟶ U；P : Cᵒᵖ ⥤ A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_w`：toPresheafF
iber_w {X Y : C} (f : X ⟶ Y) (x : Φ.fiber.obj X) (P : Cᵒᵖ ⥤ A) : P.map f.op ≫ Φ.
toPresheafFiber X x P = Φ.toPresheafFiber Y (Φ.fi…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered.fiber_map_fiber
Mk`：fiber_map_fiberMk {U : N} {X : C} (f : p.obj U ⟶ X) {Y : C} (g : X ⟶ Y) : (f
iber p).map g (fiberMk.{w} f) = fiberMk.{w} (f ≫ g)
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用引理 `CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered.fiberMk_map`：fi
berMk_map {U V : N} (g : V ⟶ U) : fiberMk.{w} (p.map g) = fiberMk.{w} (𝟙 (p.obj 
U))
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toPresheafFiberOfIsCofiltered_w {V U : N} (f : V ⟶ U) (P : Cᵒᵖ ⥤ A) :
    P.map (p.map f).op ≫ toPresheafFiberOfIsCofiltered p hp V P =
      toPresheafFiberOfIsCofiltered p hp U P := by
  simp [toPresheafFiberOfIsCofiltered]

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.GrothendieckTopology.Point.toPresheafFiberOfIsCofiltered_natura
lity** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：toPresheafFiberOfIsCofiltered_naturality {P Q : Cᵒᵖ ⥤ A} (g : P ⟶ Q) (U : 
N) : toPresheafFiberOfIsCofiltered p hp U P ≫ (ofIsCofiltered p hp).presheafFibe
r.map g = g.app (op (p.obj U)) ≫ toPresheafFiberOfIsCofiltered p hp U Q
参数：g : P ⟶ Q；U : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_naturality`：to
PresheafFiber_naturality {P Q : Cᵒᵖ ⥤ A} (g : P ⟶ Q) (X : C) (x : Φ.fiber.obj X)
 : Φ.toPresheafFiber X x P ≫ Φ.presheafFiber.map g = g.app…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toPresheafFiberOfIsCofiltered_naturality {P Q : Cᵒᵖ ⥤ A} (g : P ⟶ Q) (U : N) :
    toPresheafFiberOfIsCofiltered p hp U P ≫
      (ofIsCofiltered p hp).presheafFiber.map g =
    g.app (op (p.obj U)) ≫ toPresheafFiberOfIsCofiltered p hp U Q := by
  simp [toPresheafFiberOfIsCofiltered]

set_option backward.defeqAttrib.useBackward true in
/-- The (colimit) cocone which, for a point constructed using `Point.ofIsCofiltered`
and a functor `p : N ⥤ C` expresses the fiber of a presheaf as a colimit
indexed indexed by `N`. -/
@[simps]
/-
**CategoryTheory.GrothendieckTopology.Point.presheafFiberOfIsCofilteredCocone** 
是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：presheafFiberOfIsCofilteredCocone (P : Cᵒᵖ ⥤ A) : Cocone (p.op ⋙ P) where 
pt
参数：P : Cᵒᵖ ⥤ A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (colimit) cocone which, for a point constructed using `Point.ofIsCofiltered`
and a functor `p : N ⥤ C` expresses the fiber of a presheaf as a colimit
indexed indexed by `N`.
-/
noncomputable def presheafFiberOfIsCofilteredCocone (P : Cᵒᵖ ⥤ A) :
    Cocone (p.op ⋙ P) where
  pt := (ofIsCofiltered p hp).presheafFiber.obj P
  ι.app U := toPresheafFiberOfIsCofiltered _ _ _ _

/-- For a point constructed using `Point.ofIsCofiltered` and a functor `p : N ⥤ C`,
the fiber of a presheaf can be computed as a colimit indexed by `N`. -/
/-
**CategoryTheory.GrothendieckTopology.Point.isColimitPresheafFiberOfIsCofiltered
Cocone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：isColimitPresheafFiberOfIsCofilteredCocone (P : Cᵒᵖ ⥤ A) : IsColimit (pres
heafFiberOfIsCofilteredCocone p hp P)
参数：P : Cᵒᵖ ⥤ A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a point constructed using `Point.ofIsCofiltered` and a functor `p : N ⥤ C`,
the fiber of a presheaf can be computed as a colimit indexed by `N`.
-/
noncomputable def isColimitPresheafFiberOfIsCofilteredCocone (P : Cᵒᵖ ⥤ A) :
    IsColimit (presheafFiberOfIsCofilteredCocone p hp P) :=
  (Functor.Final.isColimitWhiskerEquiv (functor.{w} p).op _).2
    ((ofIsCofiltered p hp).isColimitPresheafFiberCocone P)

end GrothendieckTopology.Point

end CategoryTheory

