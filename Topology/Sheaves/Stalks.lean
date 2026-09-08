/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Justus Springer
-/
module

public import Mathlib.Topology.Category.TopCat.OpenNhds
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered

/-!
# Stalks

For a presheaf `F` on a topological space `X`, valued in some category `C`, the *stalk* of `F`
at the point `x : X` is defined as the colimit of the composition of the inclusion of categories
`(OpenNhds x)ᵒᵖ ⥤ (Opens X)ᵒᵖ` and the functor `F : (Opens X)ᵒᵖ ⥤ C`.
For an open neighborhood `U` of `x`, we define the map `F.germ x : F.obj (op U) ⟶ F.stalk x` as the
canonical morphism into this colimit.

Taking stalks is functorial: For every point `x : X` we define a functor `stalkFunctor C x`,
sending presheaves on `X` to objects of `C`. Furthermore, for a map `f : X ⟶ Y` between
topological spaces, we define `stalkPushforward` as the induced map on the stalks
`(f _* ℱ).stalk (f x) ⟶ ℱ.stalk x`.

Some lemmas about stalks and germs only hold for certain classes of concrete categories. A basic
property of forgetful functors of categories of algebraic structures (like `MonCat`,
`CommRingCat`,...) is that they preserve filtered colimits. Since stalks are filtered colimits,
this ensures that the stalks of presheaves valued in these categories behave exactly as for
`Type`-valued presheaves. For example, in `exists_germ_eq` we prove that in such a category, every
element of the stalk is the germ of a section.

Furthermore, if we require the forgetful functor to reflect isomorphisms and preserve limits (as
is the case for most algebraic structures), we have access to the unique gluing API and can prove
further properties. Most notably, in `is_iso_iff_stalk_functor_map_iso`, we prove that in such
a category, a morphism of sheaves is an isomorphism if and only if all of its stalk maps are
isomorphisms.

See also the definition of "algebraic structures" in the stacks project:
https://stacks.math.columbia.edu/tag/007L

TODO(@joelriou): refactor the definitions in this file so as to make them
particular cases of general constructions for points of sites from
`Mathlib/CategoryTheory/Sites/Point/Basic.lean`.

-/

@[expose] public section

assert_not_exists IsOrderedMonoid

noncomputable section

universe v u v' u'

open CategoryTheory

open TopCat

open CategoryTheory.Limits CategoryTheory.Functor

open TopologicalSpace Topology

open Opposite

open scoped AlgebraicGeometry

variable {C : Type u} [Category.{v} C]
variable [HasColimits.{v} C]
variable {X Y Z : TopCat.{v}}

namespace TopCat.Presheaf

variable (C) in
/-- Stalks are functorial with respect to morphisms of presheaves over a fixed `X`. -/
/-
**TopCat.Presheaf.stalkFunctor** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.Presheaf`。
形式化陈述：stalkFunctor (x : X) : X.Presheaf C ⥤ C
参数：x : X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Stalks are functorial with respect to morphisms of presheaves over a fixed `X`.
-/
def stalkFunctor (x : X) : X.Presheaf C ⥤ C :=
  (whiskeringLeft _ _ C).obj (OpenNhds.inclusion x).op ⋙ colim

/-- The stalk of a presheaf `F` at a point `x` is calculated as the colimit of the functor
nbhds x ⥤ opens F.X ⥤ C
-/
/-
**TopCat.Presheaf.stalk** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.Presheaf`。
形式化陈述：stalk (ℱ : X.Presheaf C) (x : X) : C
参数：ℱ : X.Presheaf C；x : X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The stalk of a presheaf `F` at a point `x` is calculated as the colimit of the f
unctor
nbhds x ⥤ opens F.X ⥤ C
-/
def stalk (ℱ : X.Presheaf C) (x : X) : C :=
  (stalkFunctor C x).obj ℱ

-- -- colimit ((open_nhds.inclusion x).op ⋙ ℱ)
@[simp]
/-
**TopCat.Presheaf.stalkFunctor_obj** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Presheaf`。
形式化陈述：stalkFunctor_obj (ℱ : X.Presheaf C) (x : X) : (stalkFunctor C x).obj ℱ = ℱ
.stalk x
参数：ℱ : X.Presheaf C；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem stalkFunctor_obj (ℱ : X.Presheaf C) (x : X) : (stalkFunctor C x).obj ℱ = ℱ.stalk x :=
  rfl

/-- The germ of a section of a presheaf over an open at a point of that open.
-/
/-
**TopCat.Presheaf.germ** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.Presheaf`。
形式化陈述：germ (F : X.Presheaf C) (U : Opens X) (x : X) (hx : x in U) : F.obj (op U)
 ⟶ stalk F x
参数：F : X.Presheaf C；U : Opens X；x : X；hx : x in U。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The germ of a section of a presheaf over an open at a point of that open.
-/
def germ (F : X.Presheaf C) (U : Opens X) (x : X) (hx : x ∈ U) : F.obj (op U) ⟶ stalk F x :=
  colimit.ι ((OpenNhds.inclusion x).op ⋙ F) (op ⟨U, hx⟩)

/-- The germ of a global section of a presheaf at a point. -/
/-
**TopCat.Presheaf.** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.Presheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The germ of a global section of a presheaf at a point.
-/
def Γgerm (F : X.Presheaf C) (x : X) : F.obj (op ⊤) ⟶ stalk F x :=
  F.germ ⊤ x True.intro

@[reassoc]
/-
**TopCat.Presheaf.germ_res** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Presheaf`。
形式化陈述：germ_res (F : X.Presheaf C) {U V : Opens X} (i : U ⟶ V) (x : X) (hx : x in
 U) : F.map i.op ≫ F.germ U x hx = F.germ V x (i.le hx)
参数：F : X.Presheaf C；i : U ⟶ V；x : X；hx : x in U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.colimit.w`：∀ {J : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]   
(F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.instHasColimitsOfShapeOfHasColimitsOfSize`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : Catego
ryTheory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
theorem germ_res (F : X.Presheaf C) {U V : Opens X} (i : U ⟶ V) (x : X) (hx : x ∈ U) :
    F.map i.op ≫ F.germ U x hx = F.germ V x (i.le hx) :=
  let i' : (⟨U, hx⟩ : OpenNhds x) ⟶ ⟨V, i.le hx⟩ := i
  colimit.w ((OpenNhds.inclusion x).op ⋙ F) i'.op

/-- A variant of `germ_res` with `op V ⟶ op U`
so that the LHS is more general and simp fires more easier. -/
@[reassoc (attr := simp)]
/-
**TopCat.Presheaf.germ_res'** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Presheaf`。
形式化陈述：germ_res' (F : X.Presheaf C) {U V : Opens X} (i : op V ⟶ op U) (x : X) (hx
 : x in U) : F.map i ≫ F.germ U x hx = F.germ V x (i.unop.le hx)
参数：F : X.Presheaf C；i : op V ⟶ op U；x : X；hx : x in U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.colimit.w`：∀ {J : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]   
(F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.instHasColimitsOfShapeOfHasColimitsOfSize`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : Catego
ryTheory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…

--- 原说明 ---
A variant of `germ_res` with `op V ⟶ op U`
so that the LHS is more general and simp fires more easier.
-/
theorem germ_res' (F : X.Presheaf C) {U V : Opens X} (i : op V ⟶ op U) (x : X) (hx : x ∈ U) :
    F.map i ≫ F.germ U x hx = F.germ V x (i.unop.le hx) :=
  let i' : (⟨U, hx⟩ : OpenNhds x) ⟶ ⟨V, i.unop.le hx⟩ := i.unop
  colimit.w ((OpenNhds.inclusion x).op ⋙ F) i'.op

@[reassoc]
/-
**TopCat.Presheaf.map_germ_eq_** 是 Mathlib 中的一个引理，位于命名空间 `TopCat.Presheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_germ_eq_Γgerm (F : X.Presheaf C) {U : Opens X} {i : U ⟶ ⊤} (x : X) (hx : x ∈ U) :
    F.map i.op ≫ F.germ U x hx = F.Γgerm x :=
  germ_res F i x hx

variable {FC : C → C → Type*} {CC : C → Type*} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]

@[simp]
/-
**TopCat.Presheaf.germ_res_apply** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Presheaf`。
形式化陈述：germ_res_apply (F : X.Presheaf C) {U V : Opens X} (i : U ⟶ V) (x : X) (hx 
: x in U) [ConcreteCategory C FC] (s) : F.germ U x hx (F.map i.op s) = F.germ V 
x (i.le hx) s
参数：F : X.Presheaf C；i : U ⟶ V；x : X；hx : x in U；s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ConcreteCategory.comp_apply`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (
C → Type w)}   {inst_1 : outPara…
· 使用定理 `TopCat.Presheaf.germ_res`：germ_res (F : X.Presheaf C) {U V : Opens X} (i
 : U ⟶ V) (x : X) (hx : x in U) : F.map i.op ≫ F.germ U x hx = F.germ V x (i.le 
hx)
-/
theorem germ_res_apply (F : X.Presheaf C)
    {U V : Opens X} (i : U ⟶ V) (x : X) (hx : x ∈ U) [ConcreteCategory C FC] (s) :
    F.germ U x hx (F.map i.op s) = F.germ V x (i.le hx) s := by
  rw [← ConcreteCategory.comp_apply, germ_res]
/-
**TopCat.Presheaf.germ_res_apply'** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Presheaf`。
形式化陈述：germ_res_apply' (F : X.Presheaf C) {U V : Opens X} (i : op V ⟶ op U) (x : 
X) (hx : x in U) [ConcreteCategory C FC] (s) : F.germ U x hx (F.map i s) = F.ger
m V x (i.unop.le hx) s
参数：F : X.Presheaf C；i : op V ⟶ op U；x : X；hx : x in U；s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ConcreteCategory.comp_apply`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (
C → Type w)}   {inst_1 : outPara…
· 使用定理 `TopCat.Presheaf.germ_res'`：germ_res' (F : X.Presheaf C) {U V : Opens X} 
(i : op V ⟶ op U) (x : X) (hx : x in U) : F.map i ≫ F.germ U x hx = F.germ V x (
i.unop.le hx)
-/
theorem germ_res_apply' (F : X.Presheaf C)
    {U V : Opens X} (i : op V ⟶ op U) (x : X) (hx : x ∈ U) [ConcreteCategory C FC] (s) :
    F.germ U x hx (F.map i s) = F.germ V x (i.unop.le hx) s := by
  rw [← ConcreteCategory.comp_apply, germ_res']
/-
**TopCat.Presheaf.** 是 Mathlib 中的一个引理，位于命名空间 `TopCat.Presheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Γgerm_res_apply (F : X.Presheaf C)
    {U : Opens X} {i : U ⟶ ⊤} (x : X) (hx : x ∈ U) [ConcreteCategory C FC] (s) :
    F.germ U x hx (F.map i.op s) = F.Γgerm x s :=
  F.germ_res_apply i x hx s

/-- A morphism from the stalk of `F` at `x` to some object `Y` is completely determined by its
composition with the `germ` morphisms.
-/
@[ext]
/-
**TopCat.Presheaf.stalk_hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Presheaf`。
形式化陈述：stalk_hom_ext (F : X.Presheaf C) {x} {Y : C} {f₁ f₂ : F.stalk x ⟶ Y} (ih :
 forall (U : Opens X) (hxU : x in U), F.germ U x hxU ≫ f₁ = F.germ U x hxU ≫ f₂)
 : f₁ = f₂
参数：F : X.Presheaf C；ih : forall (U : Opens X) (hxU : x in U), F.germ U x hxU ≫ f
₁ = F.germ U x hxU ≫ f₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.colimit.hom_ext`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u}
 C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…

--- 原说明 ---
A morphism from the stalk of `F` at `x` to some object `Y` is completely determi
ned by its
composition with the `germ` morphisms.
-/
theorem stalk_hom_ext (F : X.Presheaf C) {x} {Y : C} {f₁ f₂ : F.stalk x ⟶ Y}
    (ih : ∀ (U : Opens X) (hxU : x ∈ U), F.germ U x hxU ≫ f₁ = F.germ U x hxU ≫ f₂) : f₁ = f₂ :=
  colimit.hom_ext fun U => by
    induction U with | op U => obtain ⟨U, hxU⟩ := U; exact ih U hxU

set_option backward.isDefEq.respectTransparency false in -- This is needed in Geometry/RingedSpace/Stalks.lean
@[reassoc (attr := simp)]
/-
**TopCat.Presheaf.stalkFunctor_map_germ** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Preshe
af`。
形式化陈述：stalkFunctor_map_germ {F G : X.Presheaf C} (U : Opens X) (x : X) (hx : x i
n U) (f : F ⟶ G) : F.germ U x hx ≫ (stalkFunctor C x).map f = f.app (op U) ≫ G.g
erm U x hx
参数：U : Opens X；x : X；hx : x in U；f : F ⟶ G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.colimit.ι_map`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.instHasColimitsOfShapeOfHasColimitsOfSize`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : Catego
ryTheory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
theorem stalkFunctor_map_germ {F G : X.Presheaf C} (U : Opens X) (x : X) (hx : x ∈ U) (f : F ⟶ G) :
    F.germ U x hx ≫ (stalkFunctor C x).map f = f.app (op U) ≫ G.germ U x hx :=
  colimit.ι_map (whiskerLeft (OpenNhds.inclusion x).op f) (op ⟨U, hx⟩)

set_option backward.isDefEq.respectTransparency false in
/-
**TopCat.Presheaf.stalkFunctor_map_germ_apply** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.
Presheaf`。
形式化陈述：stalkFunctor_map_germ_apply [ConcreteCategory C FC] {F G : X.Presheaf C} (
U : Opens X) (x : X) (hx : x in U) (f : F ⟶ G) (s) : (stalkFunctor C x).map f (F
.germ U x hx s) = G.germ U x hx (f.app (op U) s)
参数：U : Opens X；x : X；hx : x in U；f : F ⟶ G；s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ConcreteCategory.comp_apply`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (
C → Type w)}   {inst_1 : outPara…
· 使用定理 `TopCat.Presheaf.stalkFunctor_map_germ`：stalkFunctor_map_germ {F G : X.Pr
esheaf C} (U : Opens X) (x : X) (hx : x in U) (f : F ⟶ G) : F.germ U x hx ≫ (sta
lkFunctor C x).map f = f.ap…
-/
theorem stalkFunctor_map_germ_apply [ConcreteCategory C FC]
    {F G : X.Presheaf C} (U : Opens X) (x : X) (hx : x ∈ U) (f : F ⟶ G) (s) :
    (stalkFunctor C x).map f (F.germ U x hx s) = G.germ U x hx (f.app (op U) s) := by
  rw [← ConcreteCategory.comp_apply, ← stalkFunctor_map_germ, ConcreteCategory.comp_apply]
  rfl

-- a variant of `stalkFunctor_map_germ_apply` that makes simpNF happy.
@[simp]
/-
**TopCat.Presheaf.stalkFunctor_map_germ_apply'** 是 Mathlib 中的一个定理，位于命名空间 `TopCat
.Presheaf`。
形式化陈述：stalkFunctor_map_germ_apply' [ConcreteCategory C FC] {F G : X.Presheaf C} 
(U : Opens X) (x : X) (hx : x in U) (f : F ⟶ G) (s) : DFunLike.coe (F
参数：U : Opens X；x : X；hx : x in U；f : F ⟶ G；s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.Presheaf.stalkFunctor_map_germ_apply`：stalkFunctor_map_germ_apply
 [ConcreteCategory C FC] {F G : X.Presheaf C} (U : Opens X) (x : X) (hx : x in U
) (f : F ⟶ G) (s) : (stalkFunctor…
-/
theorem stalkFunctor_map_germ_apply' [ConcreteCategory C FC]
    {F G : X.Presheaf C} (U : Opens X) (x : X) (hx : x ∈ U) (f : F ⟶ G) (s) :
    DFunLike.coe (F := ToHom (F.stalk x) (G.stalk x))
        (ConcreteCategory.hom ((stalkFunctor C x).map f)) (F.germ U x hx s) =
      G.germ U x hx (f.app (op U) s) :=
  stalkFunctor_map_germ_apply U x hx f s

variable (C)

/-- For a presheaf `F` on a space `X`, a continuous map `f : X ⟶ Y` induces a morphisms between the
stalk of `f _ * F` at `f x` and the stalk of `F` at `x`.
-/
/-
**TopCat.Presheaf.stalkPushforward** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.Presheaf`。
形式化陈述：stalkPushforward (f : X ⟶ Y) (F : X.Presheaf C) (x : X) : (f _* F).stalk (
f x) ⟶ F.stalk x
参数：f : X ⟶ Y；F : X.Presheaf C；x : X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a presheaf `F` on a space `X`, a continuous map `f : X ⟶ Y` induces a morphi
sms between the
stalk of `f _ * F` at `f x` and the stalk of `F` at `x`.
-/
def stalkPushforward (f : X ⟶ Y) (F : X.Presheaf C) (x : X) : (f _* F).stalk (f x) ⟶ F.stalk x := by
  -- This is a hack; Lean doesn't like to elaborate the term written directly.
  refine ?_ ≫ colimit.pre _ (OpenNhds.map f x).op
  exact colim.map (whiskerRight (NatTrans.op (OpenNhds.inclusionMapIso f x).inv) F)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
/-
**TopCat.Presheaf.stalkPushforward_germ** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Preshe
af`。
形式化陈述：stalkPushforward_germ (f : X ⟶ Y) (F : X.Presheaf C) (U : Opens Y) (x : X)
 (hx : f x in U) : (f _* F).germ U (f x) hx ≫ F.stalkPushforward C f x = F.germ 
((Opens.map f).obj U) x hx
参数：f : X ⟶ Y；F : X.Presheaf C；U : Opens Y；x : X；hx : f x in U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.ι_colimMap_assoc`：∀ {J : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u
} C]   {F G : CategoryTheory…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.colimit.ι_pre`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {K : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} K]   {C : Type u} [inst…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem stalkPushforward_germ (f : X ⟶ Y) (F : X.Presheaf C) (U : Opens Y)
    (x : X) (hx : f x ∈ U) :
      (f _* F).germ U (f x) hx ≫ F.stalkPushforward C f x = F.germ ((Opens.map f).obj U) x hx := by
  simp [germ, stalkPushforward]

-- Here are two other potential solutions, suggested by @fpvandoorn at
-- <https://github.com/leanprover-community/mathlib/pull/1018#discussion_r283978240>
-- However, I can't get the subsequent two proofs to work with either one.
-- def stalkPushforward'' (f : X ⟶ Y) (ℱ : X.Presheaf C) (x : X) :
--   (f _* ℱ).stalk (f x) ⟶ ℱ.stalk x :=
-- colim.map ((Functor.associator _ _ _).inv ≫
--   whiskerRight (NatTrans.op (OpenNhds.inclusionMapIso f x).inv) ℱ) ≫
-- colimit.pre ((OpenNhds.inclusion x).op ⋙ ℱ) (OpenNhds.map f x).op
-- def stalkPushforward''' (f : X ⟶ Y) (ℱ : X.Presheaf C) (x : X) :
--   (f _* ℱ).stalk (f x) ⟶ ℱ.stalk x :=
-- (colim.map (whiskerRight (NatTrans.op (OpenNhds.inclusionMapIso f x).inv) ℱ) :
--   colim.obj ((OpenNhds.inclusion (f x) ⋙ Opens.map f).op ⋙ ℱ) ⟶ _) ≫
-- colimit.pre ((OpenNhds.inclusion x).op ⋙ ℱ) (OpenNhds.map f x).op

namespace stalkPushforward

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**TopCat.Presheaf.stalkPushforward.id** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Presheaf
.stalkPushforward`。
形式化陈述：id (ℱ : X.Presheaf C) (x : X) : ℱ.stalkPushforward C (𝟙 X) x = (stalkFunct
or C x).map (Pushforward.id ℱ).hom
参数：ℱ : X.Presheaf C；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.Presheaf.stalk_hom_ext`：stalk_hom_ext (F : X.Presheaf C) {x} {Y :
 C} {f₁ f₂ : F.stalk x ⟶ Y} (ih : forall (U : Opens X) (hxU : x in U), F.germ U 
x hxU ≫ f₁ = F.germ…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.ι_colimMap_assoc`：∀ {J : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u
} C]   {F G : CategoryTheory…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.colimit.ι_pre`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {K : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} K]   {C : Type u} [inst…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.ι_colimMap`：∀ {J : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]  
 {F G : CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem id (ℱ : X.Presheaf C) (x : X) :
    ℱ.stalkPushforward C (𝟙 X) x = (stalkFunctor C x).map (Pushforward.id ℱ).hom := by
  ext
  simp only [stalkPushforward, germ, colim_map, ι_colimMap_assoc, whiskerRight_app]
  erw [CategoryTheory.Functor.map_id]
  simp [stalkFunctor]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**TopCat.Presheaf.stalkPushforward.comp** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Preshe
af.stalkPushforward`。
形式化陈述：comp (ℱ : X.Presheaf C) (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : ℱ.stalkPushforwa
rd C (f ≫ g) x = (f _* ℱ).stalkPushforward C g (f x) ≫ ℱ.stalkPushforward C f x
参数：ℱ : X.Presheaf C；f : X ⟶ Y；g : Y ⟶ Z；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.Presheaf.stalk_hom_ext`：stalk_hom_ext (F : X.Presheaf C) {x} {Y :
 C} {f₁ f₂ : F.stalk x ⟶ Y} (ih : forall (U : Opens X) (hxU : x in U), F.germ U 
x hxU ≫ f₁ = F.germ…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.ι_colimMap_assoc`：∀ {J : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u
} C]   {F G : CategoryTheory…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.colimit.ι_pre`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {K : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} K]   {C : Type u} [inst…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.colimit.ι_pre_assoc`：∀ {J : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} J] {K : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} K]   {C : Type u} [inst…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comp (ℱ : X.Presheaf C) (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    ℱ.stalkPushforward C (f ≫ g) x =
      (f _* ℱ).stalkPushforward C g (f x) ≫ ℱ.stalkPushforward C f x := by
  ext
  simp [germ, stalkPushforward]
/-
**TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing** 是 Mathli
b 中的一个定理，位于命名空间 `TopCat.Presheaf.stalkPushforward`。
形式化陈述：stalkPushforward_iso_of_isInducing {f : X ⟶ Y} (hf : IsInducing f) (F : X.
Presheaf C) (x : X) : IsIso (F.stalkPushforward _ f x)
参数：hf : IsInducing f；F : X.Presheaf C；x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.initial_of_adjunction`：initial_of_adjunction {L :
 C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) : Initial L
· 使用定理 `CategoryTheory.Functor.Final.comp_hasColimit`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.instHasColimitsOfShapeOfHasColimitsOfSize`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : Catego
ryTheory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `TopCat.Presheaf.stalk_hom_ext`：stalk_hom_ext (F : X.Presheaf C) {x} {Y :
 C} {f₁ f₂ : F.stalk x ⟶ Y} (ih : forall (U : Opens X) (hxU : x in U), F.germ U 
x hxU ≫ f₁ = F.germ…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `TopCat.Presheaf.stalkPushforward_germ`：stalkPushforward_germ (f : X ⟶ Y)
 (F : X.Presheaf C) (U : Opens Y) (x : X) (hx : f x in U) : (f _* F).germ U (f x
) hx ≫ F.stalkPushforward C…
· 使用定理 `CategoryTheory.Limits.colimit.ι_pre`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {K : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} K]   {C : Type u} [inst…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
theorem stalkPushforward_iso_of_isInducing {f : X ⟶ Y} (hf : IsInducing f)
    (F : X.Presheaf C) (x : X) : IsIso (F.stalkPushforward _ f x) := by
  have := Functor.initial_of_adjunction (hf.adjunctionNhds x)
  convert!
    (Functor.Final.colimitIso (OpenNhds.map f x).op ((OpenNhds.inclusion x).op ⋙ F)).isIso_hom
  refine stalk_hom_ext _ fun U hU ↦ (stalkPushforward_germ _ f F _ x hU).trans ?_
  symm
  exact colimit.ι_pre ((OpenNhds.inclusion x).op ⋙ F) (OpenNhds.map f x).op _

end stalkPushforward

section stalkPullback

/-- The morphism `ℱ_{f x} ⟶ (f⁻¹ℱ)ₓ` that factors through `(f_*f⁻¹ℱ)_{f x}`. -/
/-
**TopCat.Presheaf.stalkPullbackHom** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.Presheaf`。
形式化陈述：stalkPullbackHom (f : X ⟶ Y) (F : Y.Presheaf C) (x : X) : F.stalk (f x) ⟶ 
((pullback C f).obj F).stalk x
参数：f : X ⟶ Y；F : Y.Presheaf C；x : X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `ℱ_{f x} ⟶ (f⁻¹ℱ)ₓ` that factors through `(f_*f⁻¹ℱ)_{f x}`.
-/
def stalkPullbackHom (f : X ⟶ Y) (F : Y.Presheaf C) (x : X) :
    F.stalk (f x) ⟶ ((pullback C f).obj F).stalk x :=
  (stalkFunctor _ (f x)).map ((pullbackPushforwardAdjunction C f).unit.app F) ≫
    stalkPushforward _ _ _ x

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**TopCat.Presheaf.germ_stalkPullbackHom** 是 Mathlib 中的一个引理，位于命名空间 `TopCat.Preshe
af`。
形式化陈述：germ_stalkPullbackHom (f : X ⟶ Y) (F : Y.Presheaf C) (x : X) (U : Opens Y)
 (hU : f x in U) : F.germ U (f x) hU ≫ stalkPullbackHom C f F x = ((pullbackPush
forwardAdjunction C f).unit.app F).app _ ≫ ((pullback C f).obj F).germ ((Opens.m
ap f).obj U) x hU
参数：f : X ⟶ Y；F : Y.Presheaf C；x : X；U : Opens Y；hU : f x in U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.ι_colimMap_assoc`：∀ {J : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u
} C]   {F G : CategoryTheory…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.colimit.ι_pre`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {K : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} K]   {C : Type u} [inst…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma germ_stalkPullbackHom
    (f : X ⟶ Y) (F : Y.Presheaf C) (x : X) (U : Opens Y) (hU : f x ∈ U) :
    F.germ U (f x) hU ≫ stalkPullbackHom C f F x =
      ((pullbackPushforwardAdjunction C f).unit.app F).app _ ≫
        ((pullback C f).obj F).germ ((Opens.map f).obj U) x hU := by
  simp [stalkPullbackHom, germ, stalkFunctor, stalkPushforward]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The morphism `(f⁻¹ℱ)(U) ⟶ ℱ_{f(x)}` for some `U ∋ x`. -/
/-
**TopCat.Presheaf.germToPullbackStalk** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.Presheaf
`。
形式化陈述：germToPullbackStalk (f : X ⟶ Y) (F : Y.Presheaf C) (U : Opens X) (x : X) (
hx : x in U) : ((pullback C f).obj F).obj (op U) ⟶ F.stalk (f x)
参数：f : X ⟶ Y；F : Y.Presheaf C；U : Opens X；x : X；hx : x in U。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `(f⁻¹ℱ)(U) ⟶ ℱ_{f(x)}` for some `U ∋ x`.
-/
def germToPullbackStalk (f : X ⟶ Y) (F : Y.Presheaf C) (U : Opens X) (x : X) (hx : x ∈ U) :
    ((pullback C f).obj F).obj (op U) ⟶ F.stalk (f x) :=
  ((Opens.map f).op.isPointwiseLeftKanExtensionLeftKanExtensionUnit F (op U)).desc
    { pt := F.stalk ((f : X → Y) (x : X))
      ι :=
        { app := fun V => F.germ _ (f x) (V.hom.unop.le hx)
          naturality := fun _ _ i => by simp } }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
variable {C} in
@[ext]
/-
**TopCat.Presheaf.pullback_obj_obj_ext** 是 Mathlib 中的一个引理，位于命名空间 `TopCat.Preshea
f`。
形式化陈述：pullback_obj_obj_ext {Z : C} {f : X ⟶ Y} {F : Y.Presheaf C} (U : (Opens X)
ᵒᵖ) {φ ψ : ((pullback C f).obj F).obj U ⟶ Z} (h : forall (V : Opens Y) (hV : U.u
nop <= (Opens.map f).obj V), ((pullbackPushforwardAdjunction C f).unit.app F).ap
p (op V) ≫ ((pullback C f).obj F).map (homOfLE hV).op ≫ φ = ((pullbackPushforwar
dAdjunction C f).unit.app F).app (op V) ≫ ((pullback C f).obj F).map (homOfLE hV
).op ≫ ψ) : φ = ψ
参数：U : (Opens X)ᵒᵖ；(pullback C f).obj F；h : forall (V : Opens Y) (hV : U.unop <=
 (Opens.map f).obj V), ((pullbackPushforwardAdjunction C f).unit.app F).app (op 
V) ≫ ((pullback C f).obj F).map (homOfLE hV).op ≫ φ = ((pullbackPushforwardAdjun
ction C f).unit.app F).app (op V) ≫ ((pullback C f).obj F).map (homOfLE hV).op ≫
 ψ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsColimit.hom_ext`：∀ {J : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃
, u₃} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instHasLeftKanExtension`：∀ {C : Type u_1} {D : Ty
pe u_2} {H : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 :
 CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.instHasColimitsOfShapeOfHasColimitsOfSize`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : Catego
ryTheory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.leOfHom`：leOfHom {x y : X} (h : x ⟶ y) : x <= y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `CategoryTheory.Functor.lanAdjunction_unit`：lanAdjunction_unit : (L.lanAd
junction H).unit = L.lanUnit
-/
lemma pullback_obj_obj_ext {Z : C} {f : X ⟶ Y} {F : Y.Presheaf C} (U : (Opens X)ᵒᵖ)
    {φ ψ : ((pullback C f).obj F).obj U ⟶ Z}
    (h : ∀ (V : Opens Y) (hV : U.unop ≤ (Opens.map f).obj V),
      ((pullbackPushforwardAdjunction C f).unit.app F).app (op V) ≫
        ((pullback C f).obj F).map (homOfLE hV).op ≫ φ =
      ((pullbackPushforwardAdjunction C f).unit.app F).app (op V) ≫
        ((pullback C f).obj F).map (homOfLE hV).op ≫ ψ) : φ = ψ := by
  apply ((Opens.map f).op.isPointwiseLeftKanExtensionLeftKanExtensionUnit F _).hom_ext
  rintro ⟨⟨V⟩, ⟨⟩, ⟨b⟩⟩
  simpa [pullbackPushforwardAdjunction, Functor.lanAdjunction_unit]
    using! h V (leOfHom b)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**TopCat.Presheaf.pullbackPushforwardAdjunction_unit_pullback_map_germToPullback
Stalk** 是 Mathlib 中的一个引理，位于命名空间 `TopCat.Presheaf`。
形式化陈述：pullbackPushforwardAdjunction_unit_pullback_map_germToPullbackStalk (f : X
 ⟶ Y) (F : Y.Presheaf C) (U : Opens X) (x : X) (hx : x in U) (V : Opens Y) (hV :
 U <= (Opens.map f).obj V) : ((pullbackPushforwardAdjunction C f).unit.app F).ap
p (op V) ≫ ((pullback C f).obj F).map (homOfLE hV).op ≫ germToPullbackStalk C f 
F U x hx = F.germ _ (f x) (hV hx)
参数：f : X ⟶ Y；F : Y.Presheaf C；U : Opens X；x : X；hx : x in U；V : Opens Y；hV : U <
= (Opens.map f).obj V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `CategoryTheory.Functor.lanAdjunction_unit`：lanAdjunction_unit : (L.lanAd
junction H).unit = L.lanUnit
· 使用定理 `CategoryTheory.Functor.instHasLeftKanExtension`：∀ {C : Type u_1} {D : Ty
pe u_2} {H : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 :
 CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.instHasColimitsOfShapeOfHasColimitsOfSize`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : Catego
ryTheory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.IsColimit.fac`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃
} C]   {F : CategoryTheor…
-/
lemma pullbackPushforwardAdjunction_unit_pullback_map_germToPullbackStalk
    (f : X ⟶ Y) (F : Y.Presheaf C) (U : Opens X) (x : X) (hx : x ∈ U) (V : Opens Y)
    (hV : U ≤ (Opens.map f).obj V) :
    ((pullbackPushforwardAdjunction C f).unit.app F).app (op V) ≫
      ((pullback C f).obj F).map (homOfLE hV).op ≫ germToPullbackStalk C f F U x hx =
        F.germ _ (f x) (hV hx) := by
  simpa [pullbackPushforwardAdjunction] using!
    ((Opens.map f).op.isPointwiseLeftKanExtensionLeftKanExtensionUnit F (op U)).fac _
      (CostructuredArrow.mk (homOfLE hV).op)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**TopCat.Presheaf.germToPullbackStalk_stalkPullbackHom** 是 Mathlib 中的一个引理，位于命名空间
 `TopCat.Presheaf`。
形式化陈述：germToPullbackStalk_stalkPullbackHom (f : X ⟶ Y) (F : Y.Presheaf C) (U : O
pens X) (x : X) (hx : x in U) : germToPullbackStalk C f F U x hx ≫ stalkPullback
Hom C f F x = ((pullback C f).obj F).germ _ x hx
参数：f : X ⟶ Y；F : Y.Presheaf C；U : Opens X；x : X；hx : x in U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `TopCat.Presheaf.pullback_obj_obj_ext`：pullback_obj_obj_ext {Z : C} {f : 
X ⟶ Y} {F : Y.Presheaf C} (U : (Opens X)ᵒᵖ) {φ ψ : ((pullback C f).obj F).obj U 
⟶ Z} (h : forall (V : Open…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopCat.Presheaf.pullbackPushforwardAdjunction_unit_pullback_map_germToPu
llbackStalk_assoc`：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] [ins
t_1 : CategoryTheory.Limits.HasColimits C] {X Y : TopCat}   (f : X ⟶ Y) (F : To…
· 使用引理 `TopCat.Presheaf.germ_stalkPullbackHom`：germ_stalkPullbackHom (f : X ⟶ Y)
 (F : Y.Presheaf C) (x : X) (U : Opens Y) (hU : f x in U) : F.germ U (f x) hU ≫ 
stalkPullbackHom C f F x = …
· 使用定理 `TopCat.Presheaf.germ_res`：germ_res (F : X.Presheaf C) {U V : Opens X} (i
 : U ⟶ V) (x : X) (hx : x in U) : F.map i.op ≫ F.germ U x hx = F.germ V x (i.le 
hx)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma germToPullbackStalk_stalkPullbackHom
    (f : X ⟶ Y) (F : Y.Presheaf C) (U : Opens X) (x : X) (hx : x ∈ U) :
    germToPullbackStalk C f F U x hx ≫ stalkPullbackHom C f F x =
      ((pullback C f).obj F).germ _ x hx := by
  ext V hV
  dsimp
  simp only [pullbackPushforwardAdjunction_unit_pullback_map_germToPullbackStalk_assoc,
    germ_stalkPullbackHom, germ_res]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**TopCat.Presheaf.pullbackPushforwardAdjunction_unit_app_app_germToPullbackStalk
** 是 Mathlib 中的一个引理，位于命名空间 `TopCat.Presheaf`。
形式化陈述：pullbackPushforwardAdjunction_unit_app_app_germToPullbackStalk (f : X ⟶ Y)
 (F : Y.Presheaf C) (V : (Opens Y)ᵒᵖ) (x : X) (hx : f x in V.unop) : ((pullbackP
ushforwardAdjunction C f).unit.app F).app V ≫ germToPullbackStalk C f F _ x hx =
 F.germ _ (f x) hx
参数：f : X ⟶ Y；F : Y.Presheaf C；V : (Opens Y)ᵒᵖ；x : X；hx : f x in V.unop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用引理 `TopCat.Presheaf.pullbackPushforwardAdjunction_unit_pullback_map_germToPu
llbackStalk`：pullbackPushforwardAdjunction_unit_pullback_map_germToPullbackStalk
 (f : X ⟶ Y) (F : Y.Presheaf C) (U : Opens X) (x : X) (hx : x in U) (V : …
-/
lemma pullbackPushforwardAdjunction_unit_app_app_germToPullbackStalk
    (f : X ⟶ Y) (F : Y.Presheaf C) (V : (Opens Y)ᵒᵖ) (x : X) (hx : f x ∈ V.unop) :
    ((pullbackPushforwardAdjunction C f).unit.app F).app V ≫ germToPullbackStalk C f F _ x hx =
      F.germ _ (f x) hx := by
  simpa using pullbackPushforwardAdjunction_unit_pullback_map_germToPullbackStalk
    C f F ((Opens.map f).obj V.unop) x hx V.unop (by rfl)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The morphism `(f⁻¹ℱ)ₓ ⟶ ℱ_{f(x)}`. -/
/-
**TopCat.Presheaf.stalkPullbackInv** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.Presheaf`。
形式化陈述：stalkPullbackInv (f : X ⟶ Y) (F : Y.Presheaf C) (x : X) : ((pullback C f).
obj F).stalk x ⟶ F.stalk (f x)
参数：f : X ⟶ Y；F : Y.Presheaf C；x : X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `(f⁻¹ℱ)ₓ ⟶ ℱ_{f(x)}`.
-/
def stalkPullbackInv (f : X ⟶ Y) (F : Y.Presheaf C) (x : X) :
    ((pullback C f).obj F).stalk x ⟶ F.stalk (f x) :=
  colimit.desc ((OpenNhds.inclusion x).op ⋙ (Presheaf.pullback C f).obj F)
    { pt := F.stalk (f x)
      ι :=
        { app := fun U => F.germToPullbackStalk _ f (unop U).1 x (unop U).2
          naturality := fun U V i => by
            dsimp
            ext W hW
            dsimp [OpenNhds.inclusion]
            rw [Category.comp_id, ← Functor.map_comp_assoc,
              pullbackPushforwardAdjunction_unit_pullback_map_germToPullbackStalk]
            erw [pullbackPushforwardAdjunction_unit_pullback_map_germToPullbackStalk] } }

@[reassoc (attr := simp)]
/-
**TopCat.Presheaf.germ_stalkPullbackInv** 是 Mathlib 中的一个引理，位于命名空间 `TopCat.Preshe
af`。
形式化陈述：germ_stalkPullbackInv (f : X ⟶ Y) (F : Y.Presheaf C) (x : X) (V : Opens X)
 (hV : x in V) : ((pullback C f).obj F).germ _ x hV ≫ stalkPullbackInv C f F x =
 F.germToPullbackStalk _ f V x hV
参数：f : X ⟶ Y；F : Y.Presheaf C；x : X；V : Opens X；hV : x in V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
-/
lemma germ_stalkPullbackInv (f : X ⟶ Y) (F : Y.Presheaf C) (x : X) (V : Opens X) (hV : x ∈ V) :
    ((pullback C f).obj F).germ _ x hV ≫ stalkPullbackInv C f F x =
    F.germToPullbackStalk _ f V x hV := by
  apply colimit.ι_desc

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism `ℱ_{f(x)} ≅ (f⁻¹ℱ)ₓ`. -/
/-
**TopCat.Presheaf.stalkPullbackIso** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.Presheaf`。
形式化陈述：stalkPullbackIso (f : X ⟶ Y) (F : Y.Presheaf C) (x : X) : F.stalk (f x) ≅ 
((pullback C f).obj F).stalk x where hom
参数：f : X ⟶ Y；F : Y.Presheaf C；x : X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism `ℱ_{f(x)} ≅ (f⁻¹ℱ)ₓ`.
-/
def stalkPullbackIso (f : X ⟶ Y) (F : Y.Presheaf C) (x : X) :
    F.stalk (f x) ≅ ((pullback C f).obj F).stalk x where
  hom := stalkPullbackHom _ _ _ _
  inv := stalkPullbackInv _ _ _ _
  hom_inv_id := by
    ext U hU
    dsimp
    rw [germ_stalkPullbackHom_assoc, germ_stalkPullbackInv, Category.comp_id,
      pullbackPushforwardAdjunction_unit_app_app_germToPullbackStalk]
  inv_hom_id := by
    ext V hV
    dsimp
    rw [germ_stalkPullbackInv_assoc, Category.comp_id, germToPullbackStalk_stalkPullbackHom]

end stalkPullback

section stalkSpecializes

variable {C}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If `x` specializes to `y`, then there is a natural map `F.stalk y ⟶ F.stalk x`. -/
/-
**TopCat.Presheaf.stalkSpecializes** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.Presheaf`。
形式化陈述：stalkSpecializes (F : X.Presheaf C) {x y : X} (h : x ⤳ y) : F.stalk y ⟶ F.
stalk x
参数：F : X.Presheaf C；h : x ⤳ y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `x` specializes to `y`, then there is a natural map `F.stalk y ⟶ F.stalk x`.
-/
noncomputable def stalkSpecializes (F : X.Presheaf C) {x y : X} (h : x ⤳ y) :
    F.stalk y ⟶ F.stalk x := by
  refine colimit.desc _ ⟨_, fun U => ?_, ?_⟩
  · exact
      colimit.ι ((OpenNhds.inclusion x).op ⋙ F)
        (op ⟨(unop U).1, (specializes_iff_forall_open.mp h _ (unop U).1.2 (unop U).2 :)⟩)
  · intro U V i
    dsimp
    rw [Category.comp_id]
    let U' : OpenNhds x := ⟨_, (specializes_iff_forall_open.mp h _ (unop U).1.2 (unop U).2 :)⟩
    let V' : OpenNhds x := ⟨_, (specializes_iff_forall_open.mp h _ (unop V).1.2 (unop V).2 :)⟩
    exact colimit.w ((OpenNhds.inclusion x).op ⋙ F) (show V' ⟶ U' from i.unop).op

@[reassoc (attr := simp), elementwise nosimp]
/-
**TopCat.Presheaf.germ_stalkSpecializes** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Preshe
af`。
形式化陈述：germ_stalkSpecializes (F : X.Presheaf C) {U : Opens X} {y : X} (hy : y in 
U) {x : X} (h : x ⤳ y) : F.germ U y hy ≫ F.stalkSpecializes h = F.germ U x (h.me
m_open U.isOpen hy)
参数：F : X.Presheaf C；hy : y in U；h : x ⤳ y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
-/
theorem germ_stalkSpecializes (F : X.Presheaf C)
    {U : Opens X} {y : X} (hy : y ∈ U) {x : X} (h : x ⤳ y) :
    F.germ U y hy ≫ F.stalkSpecializes h = F.germ U x (h.mem_open U.isOpen hy) :=
  colimit.ι_desc _ _

@[simp]
/-
**TopCat.Presheaf.stalkSpecializes_refl** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Preshe
af`。
形式化陈述：stalkSpecializes_refl (F : X.Presheaf C) (x : X) : F.stalkSpecializes (spe
cializes_refl x) = 𝟙 _
参数：F : X.Presheaf C；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.Presheaf.stalk_hom_ext`：stalk_hom_ext (F : X.Presheaf C) {x} {Y :
 C} {f₁ f₂ : F.stalk x ⟶ Y} (ih : forall (U : Opens X) (hxU : x in U), F.germ U 
x hxU ≫ f₁ = F.germ…
· 使用定理 `specializes_refl`：specializes_refl (x : X) : x ⤳ x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Specializes.mem_open`：Specializes.mem_open (h : x ⤳ y) (hs : IsOpen s) (
hy : y in s) : x in s
· 使用定理 `TopologicalSpace.Opens.isOpen`：∀ {α : Type u_2} [inst : TopologicalSpace
 α] (U : TopologicalSpace.Opens α), IsOpen ↑U
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopCat.Presheaf.germ_stalkSpecializes`：germ_stalkSpecializes (F : X.Pres
heaf C) {U : Opens X} {y : X} (hy : y in U) {x : X} (h : x ⤳ y) : F.germ U y hy 
≫ F.stalkSpecializes h = F.…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem stalkSpecializes_refl (F : X.Presheaf C) (x : X) :
    F.stalkSpecializes (specializes_refl x) = 𝟙 _ := by
  ext
  simp

@[reassoc (attr := simp), elementwise (attr := simp)]
/-
**TopCat.Presheaf.stalkSpecializes_comp** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Preshe
af`。
形式化陈述：stalkSpecializes_comp (F : X.Presheaf C) {x y z : X} (h : x ⤳ y) (h' : y ⤳
 z) : F.stalkSpecializes h' ≫ F.stalkSpecializes h = F.stalkSpecializes (h.trans
 h')
参数：F : X.Presheaf C；h : x ⤳ y；h' : y ⤳ z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.Presheaf.stalk_hom_ext`：stalk_hom_ext (F : X.Presheaf C) {x} {Y :
 C} {f₁ f₂ : F.stalk x ⟶ Y} (ih : forall (U : Opens X) (hxU : x in U), F.germ U 
x hxU ≫ f₁ = F.germ…
· 使用定理 `Specializes.trans`：Specializes.trans : x ⤳ y -> y ⤳ z -> x ⤳ z
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Specializes.mem_open`：Specializes.mem_open (h : x ⤳ y) (hs : IsOpen s) (
hy : y in s) : x in s
· 使用定理 `TopologicalSpace.Opens.isOpen`：∀ {α : Type u_2} [inst : TopologicalSpace
 α] (U : TopologicalSpace.Opens α), IsOpen ↑U
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopCat.Presheaf.germ_stalkSpecializes_assoc`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasColimits C] {X 
: TopCat}   (F : TopCat.Presheaf …
· 使用定理 `TopCat.Presheaf.germ_stalkSpecializes`：germ_stalkSpecializes (F : X.Pres
heaf C) {U : Opens X} {y : X} (hy : y in U) {x : X} (h : x ⤳ y) : F.germ U y hy 
≫ F.stalkSpecializes h = F.…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem stalkSpecializes_comp (F : X.Presheaf C) {x y z : X} (h : x ⤳ y) (h' : y ⤳ z) :
    F.stalkSpecializes h' ≫ F.stalkSpecializes h = F.stalkSpecializes (h.trans h') := by
  ext
  simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
/-
**TopCat.Presheaf.stalkSpecializes_stalkFunctor_map** 是 Mathlib 中的一个定理，位于命名空间 `T
opCat.Presheaf`。
形式化陈述：stalkSpecializes_stalkFunctor_map {F G : X.Presheaf C} (f : F ⟶ G) {x y : 
X} (h : x ⤳ y) : F.stalkSpecializes h ≫ (stalkFunctor C x).map f = (stalkFunctor
 C y).map f ≫ G.stalkSpecializes h
参数：f : F ⟶ G；h : x ⤳ y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.Presheaf.stalk_hom_ext`：stalk_hom_ext (F : X.Presheaf C) {x} {Y :
 C} {f₁ f₂ : F.stalk x ⟶ Y} (ih : forall (U : Opens X) (hxU : x in U), F.germ U 
x hxU ≫ f₁ = F.germ…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Specializes.mem_open`：Specializes.mem_open (h : x ⤳ y) (hs : IsOpen s) (
hy : y in s) : x in s
· 使用定理 `TopologicalSpace.Opens.isOpen`：∀ {α : Type u_2} [inst : TopologicalSpace
 α] (U : TopologicalSpace.Opens α), IsOpen ↑U
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopCat.Presheaf.germ_stalkSpecializes_assoc`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasColimits C] {X 
: TopCat}   (F : TopCat.Presheaf …
· 使用定理 `TopCat.Presheaf.stalkFunctor_map_germ`：stalkFunctor_map_germ {F G : X.Pr
esheaf C} (U : Opens X) (x : X) (hx : x in U) (f : F ⟶ G) : F.germ U x hx ≫ (sta
lkFunctor C x).map f = f.ap…
· 使用定理 `TopCat.Presheaf.stalkFunctor_map_germ_assoc`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasColimits C] {X 
: TopCat}   {F G : TopCat.Preshea…
· 使用定理 `TopCat.Presheaf.germ_stalkSpecializes`：germ_stalkSpecializes (F : X.Pres
heaf C) {U : Opens X} {y : X} (hy : y in U) {x : X} (h : x ⤳ y) : F.germ U y hy 
≫ F.stalkSpecializes h = F.…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem stalkSpecializes_stalkFunctor_map {F G : X.Presheaf C} (f : F ⟶ G) {x y : X} (h : x ⤳ y) :
    F.stalkSpecializes h ≫ (stalkFunctor C x).map f =
      (stalkFunctor C y).map f ≫ G.stalkSpecializes h := by
  ext
  simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
/-
**TopCat.Presheaf.stalkSpecializes_stalkPushforward** 是 Mathlib 中的一个定理，位于命名空间 `T
opCat.Presheaf`。
形式化陈述：stalkSpecializes_stalkPushforward (f : X ⟶ Y) (F : X.Presheaf C) {x y : X}
 (h : x ⤳ y) : (f _* F).stalkSpecializes (f.hom.map_specializes h) ≫ F.stalkPush
forward _ f x = F.stalkPushforward _ f y ≫ F.stalkSpecializes h
参数：f : X ⟶ Y；F : X.Presheaf C；h : x ⤳ y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.Presheaf.stalk_hom_ext`：stalk_hom_ext (F : X.Presheaf C) {x} {Y :
 C} {f₁ f₂ : F.stalk x ⟶ Y} (ih : forall (U : Opens X) (hxU : x in U), F.germ U 
x hxU ≫ f₁ = F.germ…
· 使用定理 `ContinuousMap.map_specializes`：map_specializes (f : C(α, β)) {x y : α} (
h : x ⤳ y) : f x ⤳ f y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Specializes.mem_open`：Specializes.mem_open (h : x ⤳ y) (hs : IsOpen s) (
hy : y in s) : x in s
· 使用定理 `TopologicalSpace.Opens.isOpen`：∀ {α : Type u_2} [inst : TopologicalSpace
 α] (U : TopologicalSpace.Opens α), IsOpen ↑U
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopCat.Presheaf.germ_stalkSpecializes_assoc`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasColimits C] {X 
: TopCat}   (F : TopCat.Presheaf …
· 使用定理 `TopCat.Presheaf.stalkPushforward_germ`：stalkPushforward_germ (f : X ⟶ Y)
 (F : X.Presheaf C) (U : Opens Y) (x : X) (hx : f x in U) : (f _* F).germ U (f x
) hx ≫ F.stalkPushforward C…
· 使用定理 `TopCat.Presheaf.stalkPushforward_germ_assoc`：∀ (C : Type u) [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasColimits C] {X 
Y : TopCat}   (f : X ⟶ Y) (F : To…
· 使用定理 `TopCat.Presheaf.germ_stalkSpecializes`：germ_stalkSpecializes (F : X.Pres
heaf C) {U : Opens X} {y : X} (hy : y in U) {x : X} (h : x ⤳ y) : F.germ U y hy 
≫ F.stalkSpecializes h = F.…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem stalkSpecializes_stalkPushforward (f : X ⟶ Y) (F : X.Presheaf C) {x y : X} (h : x ⤳ y) :
    (f _* F).stalkSpecializes (f.hom.map_specializes h) ≫ F.stalkPushforward _ f x =
      F.stalkPushforward _ f y ≫ F.stalkSpecializes h := by
  ext
  simp

set_option backward.isDefEq.respectTransparency.types false in
/-- The stalks are isomorphic on inseparable points -/
@[simps]
/-
**TopCat.Presheaf.stalkCongr** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.Presheaf`。
形式化陈述：stalkCongr (F : X.Presheaf C) {x y : X} (e : Inseparable x y) : F.stalk x 
≅ F.stalk y
参数：F : X.Presheaf C；e : Inseparable x y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The stalks are isomorphic on inseparable points
-/
def stalkCongr (F : X.Presheaf C) {x y : X}
    (e : Inseparable x y) : F.stalk x ≅ F.stalk y :=
  ⟨F.stalkSpecializes e.ge, F.stalkSpecializes e.le, by simp, by simp⟩

end stalkSpecializes

section Concrete

variable {C} {CC : C → Type v} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
variable [instCC : ConcreteCategory.{v} C FC]

/-
**TopCat.Presheaf.germ_ext** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Presheaf`。
形式化陈述：germ_ext (F : X.Presheaf C) {U V : Opens X} {x : X} {hxU : x in U} {hxV : 
x in V} (W : Opens X) (hxW : x in W) (iWU : W ⟶ U) (iWV : W ⟶ V) {sU : ToType (F
.obj (op U))} {sV : ToType (F.obj (op V))} (ih : F.map iWU.op sU = F.map iWV.op 
sV) : F.germ _ x hxU sU = F.germ _ x hxV sV
参数：F : X.Presheaf C；W : Opens X；hxW : x in W；iWU : W ⟶ U；iWV : W ⟶ V；F.obj (op U
)；F.obj (op V)；ih : F.map iWU.op sU = F.map iWV.op sV。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TopCat.Presheaf.germ_res`：germ_res (F : X.Presheaf C) {U V : Opens X} (i
 : U ⟶ V) (x : X) (hx : x in U) : F.map i.op ≫ F.germ U x hx = F.germ V x (i.le 
hx)
· 使用定理 `CategoryTheory.ConcreteCategory.comp_apply`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (
C → Type w)}   {inst_1 : outPara…
-/
theorem germ_ext (F : X.Presheaf C) {U V : Opens X} {x : X} {hxU : x ∈ U} {hxV : x ∈ V}
    (W : Opens X) (hxW : x ∈ W) (iWU : W ⟶ U) (iWV : W ⟶ V)
    {sU : ToType (F.obj (op U))} {sV : ToType (F.obj (op V))}
    (ih : F.map iWU.op sU = F.map iWV.op sV) :
      F.germ _ x hxU sU = F.germ _ x hxV sV := by
  rw [← F.germ_res iWU x hxW, ← F.germ_res iWV x hxW, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply, ih]

variable [PreservesFilteredColimits (forget C)]

/--
For presheaves valued in a concrete category whose forgetful functor preserves filtered colimits,
every element of the stalk is the germ of a section.
-/
/-
**TopCat.Presheaf.exists_germ_eq** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Presheaf`。
形式化陈述：exists_germ_eq (F : X.Presheaf C) {x : X} (t : ToType (stalk.{v, u} F x)) 
: exists (U : Opens X) (m : x in U) (s : ToType (F.obj (op U))), F.germ _ x m s 
= t
参数：F : X.Presheaf C；t : ToType (stalk.{v, u} F x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.Types.jointly_surjective`：jointly_surjective (F : 
J ⥤ Type u) {t : Cocone F} (h : IsColimit t) (x : t.pt) : exists (j : J) (y : F.
obj j), t.ι.app j y = x
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesFilteredColimitsOfSize.preserves_filtered
_colimits`：∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type
 u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.isCofiltered_of_directed_ge_nonempty`：∀ (α : Type u) [ins
t : Preorder α] [IsCodirectedOrder α] [Nonempty α], CategoryTheory.IsCofiltered 
α
· 使用定理 `SemilatticeInf.instIsCodirectedOrder`：∀ {α : Type u_1} [inst : Semilatti
ceInf α], IsCodirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α

--- 原说明 ---
For presheaves valued in a concrete category whose forgetful functor preserves f
iltered colimits,
every element of the stalk is the germ of a section.
-/
theorem exists_germ_eq (F : X.Presheaf C) {x : X} (t : ToType (stalk.{v, u} F x)) :
    ∃ (U : Opens X) (m : x ∈ U) (s : ToType (F.obj (op U))), F.germ _ x m s = t := by
  obtain ⟨U, s, e⟩ :=
    Types.jointly_surjective.{v, v} _ (isColimitOfPreserves (forget C) (colimit.isColimit _)) t
  revert s e
  induction U with | op U => ?_
  obtain ⟨V, m⟩ := U
  intro s e
  exact ⟨V, m, s, e⟩

@[deprecated (since := "2026-05-16")] alias germ_exist := exists_germ_eq

/-- A version of `exists_germ_eq` that provides a section
over a subset of a given open neighborhood. -/
/-
**TopCat.Presheaf.exists_le_germ_eq** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Presheaf`。
形式化陈述：exists_le_germ_eq (F : X.Presheaf C) {x : X} (t : ToType (stalk.{v, u} F x
)) {V : Opens X} (hV : x in V) : exists U <= V, exists (m : x in U) (s : ToType 
(F.obj (op U))), F.germ _ x m s = t
参数：F : X.Presheaf C；t : ToType (stalk.{v, u} F x)；hV : x in V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.Presheaf.exists_germ_eq`：exists_germ_eq (F : X.Presheaf C) {x : X
} (t : ToType (stalk.{v, u} F x)) : exists (U : Opens X) (m : x in U) (s : ToTyp
e (F.obj (op U))), F…
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `TopCat.Presheaf.germ_res_apply`：germ_res_apply (F : X.Presheaf C) {U V :
 Opens X} (i : U ⟶ V) (x : X) (hx : x in U) [ConcreteCategory C FC] (s) : F.germ
 U x hx (F.map i.op …

--- 原说明 ---
A version of `exists_germ_eq` that provides a section
over a subset of a given open neighborhood.
-/
theorem exists_le_germ_eq (F : X.Presheaf C) {x : X} (t : ToType (stalk.{v, u} F x))
    {V : Opens X} (hV : x ∈ V) :
    ∃ U ≤ V, ∃ (m : x ∈ U) (s : ToType (F.obj (op U))), F.germ _ x m s = t := by
  rcases F.exists_germ_eq t with ⟨U, hxU, s, rfl⟩
  refine ⟨U ⊓ V, inf_le_right, by simp [*], F.map (homOfLE inf_le_left).op s, ?_⟩
  exact germ_res_apply ..

/-- If two sections have the same germ at `x`,
then their restrictions to some open neighborhood `W` of `x` are equal. -/
/-
**TopCat.Presheaf.germ_eq** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Presheaf`。
形式化陈述：germ_eq (F : X.Presheaf C) {U V : Opens X} (x : X) (mU : x in U) (mV : x i
n V) (s : ToType (F.obj (op U))) (t : ToType (F.obj (op V))) (h : F.germ U x mU 
s = F.germ V x mV t) : exists (W : Opens X) (_m : x in W) (iU : W ⟶ U) (iV : W ⟶
 V), F.map iU.op s = F.map iV.op t
参数：F : X.Presheaf C；x : X；mU : x in U；mV : x in V；s : ToType (F.obj (op U))；t : 
ToType (F.obj (op V))；h : F.germ U x mU s = F.germ V x mV t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.instHasColimitsOfShapeOfHasColimitsOfSize`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : Catego
ryTheory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.IsColimit.eq_iff`：∀ {J : Type u_1} {C : Type u_2} 
[inst : CategoryTheory.Category.{v_1, u_1} J]   [inst_1 : CategoryTheory.Categor
y.{v_2, u_2} C] {FC : C → C …
· 使用定理 `CategoryTheory.Limits.PreservesFilteredColimitsOfSize.preserves_filtered
_colimits`：∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type
 u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.isCofiltered_of_directed_ge_nonempty`：∀ (α : Type u) [ins
t : Preorder α] [IsCodirectedOrder α] [Nonempty α], CategoryTheory.IsCofiltered 
α
· 使用定理 `SemilatticeInf.instIsCodirectedOrder`：∀ {α : Type u_1} [inst : Semilatti
ceInf α], IsCodirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `CategoryTheory.IsCofiltered.toIsCofilteredOrEmpty`：∀ {C : Type u} {inst 
: CategoryTheory.Category.{v, u} C} [self : CategoryTheory.IsCofiltered C],   Ca
tegoryTheory.IsCofilteredOrEmpty C
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
If two sections have the same germ at `x`,
then their restrictions to some open neighborhood `W` of `x` are equal.
-/
theorem germ_eq (F : X.Presheaf C) {U V : Opens X} (x : X) (mU : x ∈ U) (mV : x ∈ V)
    (s : ToType (F.obj (op U))) (t : ToType (F.obj (op V)))
    (h : F.germ U x mU s = F.germ V x mV t) :
    ∃ (W : Opens X) (_m : x ∈ W) (iU : W ⟶ U) (iV : W ⟶ V), F.map iU.op s = F.map iV.op t := by
  obtain ⟨W, iU, iV, e⟩ := (colimit.isColimit ((OpenNhds.inclusion x).op ⋙ F)).eq_iff.mp h
  exact ⟨(unop W).1, (unop W).2, iU.unop, iV.unop, e⟩

set_option backward.isDefEq.respectTransparency.types false in
/-
**TopCat.Presheaf.stalkFunctor_map_injective_of_app_injective** 是 Mathlib 中的一个定理
，位于命名空间 `TopCat.Presheaf`。
形式化陈述：stalkFunctor_map_injective_of_app_injective {F G : Presheaf C X} {f : F ⟶ 
G} (h : forall U : Opens X, Function.Injective (f.app (op U))) (x : X) : Functio
n.Injective ((stalkFunctor C x).map f)
参数：h : forall U : Opens X, Function.Injective (f.app (op U))；x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.Presheaf.exists_germ_eq`：exists_germ_eq (F : X.Presheaf C) {x : X
} (t : ToType (stalk.{v, u} F x)) : exists (U : Opens X) (m : x in U) (s : ToTyp
e (F.obj (op U))), F…
· 使用定理 `TopCat.Presheaf.germ_eq`：germ_eq (F : X.Presheaf C) {U V : Opens X} (x :
 X) (mU : x in U) (mV : x in V) (s : ToType (F.obj (op U))) (t : ToType (F.obj (
op V))) (h : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopCat.Presheaf.stalkFunctor_map_germ_apply`：stalkFunctor_map_germ_apply
 [ConcreteCategory C FC] {F G : X.Presheaf C} (U : Opens X) (x : X) (hx : x in U
) (f : F ⟶ G) (s) : (stalkFunctor…
· 使用定理 `CategoryTheory.ConcreteCategory.comp_apply`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (
C → Type w)}   {inst_1 : outPara…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `TopCat.Presheaf.germ_res_apply`：germ_res_apply (F : X.Presheaf C) {U V :
 Opens X} (i : U ⟶ V) (x : X) (hx : x in U) [ConcreteCategory C FC] (s) : F.germ
 U x hx (F.map i.op …
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem stalkFunctor_map_injective_of_app_injective {F G : Presheaf C X} {f : F ⟶ G}
    (h : ∀ U : Opens X, Function.Injective (f.app (op U))) (x : X) :
    Function.Injective ((stalkFunctor C x).map f) := fun s t hst => by
  rcases exists_germ_eq F s with ⟨U₁, hxU₁, s, rfl⟩
  rcases exists_germ_eq F t with ⟨U₂, hxU₂, t, rfl⟩
  rw [stalkFunctor_map_germ_apply, stalkFunctor_map_germ_apply] at hst
  obtain ⟨W, hxW, iWU₁, iWU₂, heq⟩ := G.germ_eq x hxU₁ hxU₂ _ _ hst
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← f.naturality, ← f.naturality,
    ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at heq
  replace heq := h W heq
  convert! congr_arg (F.germ _ x hxW) heq using 1
  exacts [(F.germ_res_apply iWU₁ x hxW s).symm, (F.germ_res_apply iWU₂ x hxW t).symm]

section IsBasis

variable {B : Set (Opens X)} (hB : Opens.IsBasis B)

include hB

set_option backward.isDefEq.respectTransparency.types false in
/-
**TopCat.Presheaf.exists_mem_germ_eq_of_isBasis** 是 Mathlib 中的一个引理，位于命名空间 `TopCa
t.Presheaf`。
形式化陈述：exists_mem_germ_eq_of_isBasis (F : X.Presheaf C) (x : X) (t : ToType (F.st
alk x)) : exists (U : Opens X) (m : x in U) (_ : U in B) (s : ToType (F.obj (op 
U))), F.germ _ x m s = t
参数：F : X.Presheaf C；x : X；t : ToType (F.stalk x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.Presheaf.exists_germ_eq`：exists_germ_eq (F : X.Presheaf C) {x : X
} (t : ToType (stalk.{v, u} F x)) : exists (U : Opens X) (m : x in U) (s : ToTyp
e (F.obj (op U))), F…
· 使用定理 `TopologicalSpace.IsTopologicalBasis.exists_subset_of_mem_open`：∀ {α : Ty
pe u} [t : TopologicalSpace α] {b : Set (Set α)},   TopologicalSpace.IsTopologic
alBasis b → ∀ {a : α} {u : Set α}, a ∈ u → IsOpen u…
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ConcreteCategory.comp_apply`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (
C → Type w)}   {inst_1 : outPara…
· 使用定理 `TopCat.Presheaf.germ_res'`：germ_res' (F : X.Presheaf C) {U V : Opens X} 
(i : op V ⟶ op U) (x : X) (hx : x in U) : F.map i ≫ F.germ U x hx = F.germ V x (
i.unop.le hx)
-/
lemma exists_mem_germ_eq_of_isBasis (F : X.Presheaf C) (x : X) (t : ToType (F.stalk x)) :
    ∃ (U : Opens X) (m : x ∈ U) (_ : U ∈ B) (s : ToType (F.obj (op U))), F.germ _ x m s = t := by
  obtain ⟨U, hxU, s, rfl⟩ := F.exists_germ_eq t
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := hB.exists_subset_of_mem_open hxU U.2
  exact ⟨V, hxV, hV, F.map (homOfLE hVU).op s, by rw [← ConcreteCategory.comp_apply, F.germ_res']⟩

set_option backward.isDefEq.respectTransparency.types false in
/-
**TopCat.Presheaf.germ_eq_of_isBasis** 是 Mathlib 中的一个引理，位于命名空间 `TopCat.Presheaf`
。
形式化陈述：germ_eq_of_isBasis (F : X.Presheaf C) {U V : Opens X} (x : X) (mU : x in U
) (mV : x in V) {s : ToType (F.obj (op U))} {t : ToType (F.obj (op V))} (h : F.g
erm U x mU s = F.germ V x mV t) : exists (W : Opens X) (_ : x in W) (_ : W in B)
 (hWU : W <= U) (hWV : W <= V), F.map (homOfLE hWU).op s = F.map (homOfLE hWV).o
p t
参数：F : X.Presheaf C；x : X；mU : x in U；mV : x in V；F.obj (op U)；F.obj (op V)；h : 
F.germ U x mU s = F.germ V x mV t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.Presheaf.germ_eq`：germ_eq (F : X.Presheaf C) {U V : Opens X} (x :
 X) (mU : x in U) (mV : x in V) (s : ToType (F.obj (op U))) (t : ToType (F.obj (
op V))) (h : …
· 使用定理 `TopologicalSpace.IsTopologicalBasis.exists_subset_of_mem_open`：∀ {α : Ty
pe u} [t : TopologicalSpace α] {b : Set (Set α)},   TopologicalSpace.IsTopologic
alBasis b → ∀ {a : α} {u : Set α}, a ∈ u → IsOpen u…
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `DFunLike.congr_arg`：∀ {F : Sort u_1} {α : Sort u_2} {β : Sort u_3} [i : 
FunLike F α β] (f : F) {x y : α}, x = y → f x = f y
-/
lemma germ_eq_of_isBasis (F : X.Presheaf C) {U V : Opens X} (x : X) (mU : x ∈ U) (mV : x ∈ V)
    {s : ToType (F.obj (op U))} {t : ToType (F.obj (op V))}
    (h : F.germ U x mU s = F.germ V x mV t) :
    ∃ (W : Opens X) (_ : x ∈ W) (_ : W ∈ B) (hWU : W ≤ U) (hWV : W ≤ V),
      F.map (homOfLE hWU).op s = F.map (homOfLE hWV).op t := by
  obtain ⟨W, hxW, hWU, hWV, e⟩ := F.germ_eq x mU mV _ _ h
  obtain ⟨_, ⟨W', hW', rfl⟩, hxW', hW'W⟩ := hB.exists_subset_of_mem_open hxW W.2
  refine ⟨W', hxW', hW', hW'W.trans hWU.le, hW'W.trans hWV.le, ?_⟩
  simpa only [← ConcreteCategory.comp_apply, ← F.map_comp] using!
    DFunLike.congr_arg (ConcreteCategory.hom (F.map (homOfLE hW'W).op)) e
/-
**TopCat.Presheaf.stalkFunctor_map_injective_of_isBasis** 是 Mathlib 中的一个引理，位于命名空
间 `TopCat.Presheaf`。
形式化陈述：stalkFunctor_map_injective_of_isBasis {F G : X.Presheaf C} {α : F ⟶ G} (hα
 : forall U in B, Function.Injective (α.app (op U))) (x : X) : Function.Injectiv
e ((stalkFunctor _ x).map α)
参数：hα : forall U in B, Function.Injective (α.app (op U))；x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `TopCat.Presheaf.exists_mem_germ_eq_of_isBasis`：exists_mem_germ_eq_of_isB
asis (F : X.Presheaf C) (x : X) (t : ToType (F.stalk x)) : exists (U : Opens X) 
(m : x in U) (_ : U in B) (s : ToTy…
· 使用引理 `TopCat.Presheaf.germ_eq_of_isBasis`：germ_eq_of_isBasis (F : X.Presheaf C
) {U V : Opens X} (x : X) (mU : x in U) (mV : x in V) {s : ToType (F.obj (op U))
} {t : ToType (F.obj (op…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopCat.Presheaf.stalkFunctor_map_germ_apply`：stalkFunctor_map_germ_apply
 [ConcreteCategory C FC] {F G : X.Presheaf C} (U : Opens X) (x : X) (hx : x in U
) (f : F ⟶ G) (s) : (stalkFunctor…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `TopCat.Presheaf.germ_res_apply'`：germ_res_apply' (F : X.Presheaf C) {U V
 : Opens X} (i : op V ⟶ op U) (x : X) (hx : x in U) [ConcreteCategory C FC] (s) 
: F.germ U x hx (F.ma…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatTrans.naturality_apply`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {D : Type u_1} [inst_1 : CategoryTheory.Category.{v_1
, u_1} D]   {FD : outParam (D …
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
-/
lemma stalkFunctor_map_injective_of_isBasis
    {F G : X.Presheaf C} {α : F ⟶ G} (hα : ∀ U ∈ B, Function.Injective (α.app (op U))) (x : X) :
    Function.Injective ((stalkFunctor _ x).map α) := by
  intro s t hst
  obtain ⟨U₁, hxU₁, hU₁, s, rfl⟩ := exists_mem_germ_eq_of_isBasis hB _ x s
  obtain ⟨U₂, hxU₂, hU₂, t, rfl⟩ := exists_mem_germ_eq_of_isBasis hB _ x t
  rw [stalkFunctor_map_germ_apply, stalkFunctor_map_germ_apply] at hst
  obtain ⟨W, hxW, hW, iWU₁, iWU₂, heq⟩ := germ_eq_of_isBasis hB _ _ hxU₁ hxU₂ hst
  simp only [← α.naturality_apply, (hα W hW).eq_iff] at heq
  simpa [germ_res_apply'] using congr(F.germ W x hxW $heq)

end IsBasis

variable [HasLimits C] [PreservesLimits (forget C)] [(forget C).ReflectsIsomorphisms]

/-- Let `F` be a sheaf valued in a concrete category, whose forgetful functor reflects isomorphisms,
preserves limits and filtered colimits. Then two sections who agree on every stalk must be equal.
-/
/-
**TopCat.Presheaf.section_ext** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Presheaf`。
形式化陈述：section_ext (F : Sheaf C X) (U : Opens X) (s t : ToType (F.1.obj (op U))) 
(h : forall (x : X) (hx : x in U), F.presheaf.germ U x hx s = F.presheaf.germ U 
x hx t) : s = t
参数：F : Sheaf C X；U : Opens X；s t : ToType (F.1.obj (op U))；h : forall (x : X) (h
x : x in U), F.presheaf.germ U x hx s = F.presheaf.germ U x hx t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.Sheaf.eq_of_locally_eq'`：∀ {C : Type u_1} [inst : CategoryTheory.
Category.{v_1, u_1} C] {FC : C → C → Type u_2} {CC : C → Type u_3}   [inst_1 : (
X Y : C) → FunLike (…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `TopCat.Presheaf.germ_eq`：germ_eq (F : X.Presheaf C) {U V : Opens X} (x :
 X) (mU : x in U) (mV : x in V) (s : ToType (F.obj (op U))) (t : ToType (F.obj (
op V))) (h : …
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
Let `F` be a sheaf valued in a concrete category, whose forgetful functor reflec
ts isomorphisms,
preserves limits and filtered colimits. Then two sections who agree on every sta
lk must be equal.
-/
theorem section_ext (F : Sheaf C X) (U : Opens X) (s t : ToType (F.1.obj (op U)))
    (h : ∀ (x : X) (hx : x ∈ U), F.presheaf.germ U x hx s = F.presheaf.germ U x hx t) : s = t := by
  -- We use `germ_eq` and the axiom of choice, to pick for every point `x` a neighbourhood
  -- `V x`, such that the restrictions of `s` and `t` to `V x` coincide.
  choose V m i₁ i₂ heq using fun x : U => F.presheaf.germ_eq x.1 x.2 x.2 s t (h x.1 x.2)
  -- Since `F` is a sheaf, we can prove the equality locally, if we can show that these
  -- neighborhoods form a cover of `U`.
  apply F.eq_of_locally_eq' V U i₁
  · intro x hxU
    simp only [Opens.mem_iSup]
    exact ⟨⟨x, hxU⟩, m ⟨x, hxU⟩⟩
  · intro x
    rw [heq, Subsingleton.elim (i₁ x) (i₂ x)]

/-
Note that the analogous statement for surjectivity is false: Surjectivity on stalks does not
imply surjectivity of the components of a sheaf morphism. However it does imply that the morphism
is an epi, but this fact is not yet formalized.
-/
set_option backward.isDefEq.respectTransparency.types false in
/-
**TopCat.Presheaf.app_injective_of_stalkFunctor_map_injective** 是 Mathlib 中的一个定理
，位于命名空间 `TopCat.Presheaf`。
形式化陈述：app_injective_of_stalkFunctor_map_injective {F : Sheaf C X} {G : Presheaf 
C X} (f : F.1 ⟶ G) (U : Opens X) (h : forall x in U, Function.Injective ((stalkF
unctor C x).map f)) : Function.Injective (f.app (op U))
参数：f : F.1 ⟶ G；U : Opens X；h : forall x in U, Function.Injective ((stalkFunctor 
C x).map f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.Presheaf.section_ext`：section_ext (F : Sheaf C X) (U : Opens X) (
s t : ToType (F.1.obj (op U))) (h : forall (x : X) (hx : x in U), F.presheaf.ger
m U x hx s = F.pr…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopCat.Presheaf.stalkFunctor_map_germ_apply`：stalkFunctor_map_germ_apply
 [ConcreteCategory C FC] {F G : X.Presheaf C} (U : Opens X) (x : X) (hx : x in U
) (f : F ⟶ G) (s) : (stalkFunctor…

--- 原说明 ---
Note that the analogous statement for surjectivity is false: Surjectivity on sta
lks does not
imply surjectivity of the components of a sheaf morphism. However it does imply 
that the morphism
is an epi, but this fact is not yet formalized.
-/
theorem app_injective_of_stalkFunctor_map_injective {F : Sheaf C X} {G : Presheaf C X} (f : F.1 ⟶ G)
    (U : Opens X) (h : ∀ x ∈ U, Function.Injective ((stalkFunctor C x).map f)) :
    Function.Injective (f.app (op U)) := fun s t hst =>
  section_ext F _ _ _ fun x hx =>
    h x hx <| by rw [stalkFunctor_map_germ_apply, stalkFunctor_map_germ_apply, hst]
/-
**TopCat.Presheaf.app_injective_iff_stalkFunctor_map_injective** 是 Mathlib 中的一个定
理，位于命名空间 `TopCat.Presheaf`。
形式化陈述：app_injective_iff_stalkFunctor_map_injective {F : Sheaf C X} {G : Presheaf
 C X} (f : F.1 ⟶ G) : (forall x : X, Function.Injective ((stalkFunctor C x).map 
f)) ↔ forall U : Opens X, Function.Injective (f.app (op U))
参数：f : F.1 ⟶ G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.Presheaf.app_injective_of_stalkFunctor_map_injective`：app_injecti
ve_of_stalkFunctor_map_injective {F : Sheaf C X} {G : Presheaf C X} (f : F.1 ⟶ G
) (U : Opens X) (h : forall x in U, Function.Inje…
· 使用定理 `TopCat.Presheaf.stalkFunctor_map_injective_of_app_injective`：stalkFuncto
r_map_injective_of_app_injective {F G : Presheaf C X} {f : F ⟶ G} (h : forall U 
: Opens X, Function.Injective (f.app (op U))) (x …
-/
theorem app_injective_iff_stalkFunctor_map_injective {F : Sheaf C X} {G : Presheaf C X}
    (f : F.1 ⟶ G) :
    (∀ x : X, Function.Injective ((stalkFunctor C x).map f)) ↔
      ∀ U : Opens X, Function.Injective (f.app (op U)) :=
  ⟨fun h U => app_injective_of_stalkFunctor_map_injective f U fun x _ => h x,
    stalkFunctor_map_injective_of_app_injective⟩

set_option backward.isDefEq.respectTransparency false in
/-
**TopCat.Presheaf.stalkFunctor_preserves_mono** 是 Mathlib 中的一个实例，位于命名空间 `TopCat.
Presheaf`。
形式化陈述：stalkFunctor_preserves_mono (x : X) : Functor.PreservesMonomorphisms (Shea
f.forget.{v} C X ⋙ stalkFunctor C x)
参数：x : X。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.mono_of_injective`：mono_of_injective {X 
Y : C} (f : X ⟶ Y) (i : Function.Injective f) : Mono f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `TopCat.Presheaf.app_injective_iff_stalkFunctor_map_injective`：app_inject
ive_iff_stalkFunctor_map_injective {F : Sheaf C X} {G : Presheaf C X} (f : F.1 ⟶
 G) : (forall x : X, Function.Injective ((stalkFun…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.ConcreteCategory.mono_iff_injective_of_preservesPullback`
：mono_iff_injective_of_preservesPullback {X Y : C} (f : X ⟶ Y) [PreservesLimitsO
fShape WalkingCospan (forget C)] : Mono f ↔ Function.Injectiv…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesLimits.preservesFiniteLimits`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categor
yTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.NatTrans.mono_iff_mono_app`：∀ {K : Type u} [inst : Catego
ryTheory.Category.{v, u} K] {C : Type u'} [inst_1 : CategoryTheory.Category.{v',
 u'} C]   {F G : CategoryTheory…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimits`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasLimits C],   Cate
goryTheory.Limits.HasFiniteLimits C
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize.preservesLimitsOfShape`：∀ {C
 : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : 
CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.instHasLimitsOfShapeOfHasLimitsOfSize`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTh
eory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.instHasColimitsOfShapeOfHasColimitsOfSize`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : Catego
ryTheory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.PreservesFilteredColimitsOfSize.preserves_filtered
_colimits`：∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type
 u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.isCofiltered_of_directed_ge_nonempty`：∀ (α : Type u) [ins
t : Preorder α] [IsCodirectedOrder α] [Nonempty α], CategoryTheory.IsCofiltered 
α
· 使用定理 `SemilatticeInf.instIsCodirectedOrder`：∀ {α : Type u_1} [inst : Semilatti
ceInf α], IsCodirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
instance stalkFunctor_preserves_mono (x : X) :
    Functor.PreservesMonomorphisms (Sheaf.forget.{v} C X ⋙ stalkFunctor C x) :=
  ⟨@fun _𝓐 _𝓑 f _ =>
    ConcreteCategory.mono_of_injective _ <|
      (app_injective_iff_stalkFunctor_map_injective f.1).mpr
        (fun c =>
          (ConcreteCategory.mono_iff_injective_of_preservesPullback (f.1.app (op c))).mp
            ((NatTrans.mono_iff_mono_app f.1).mp
                (CategoryTheory.presheaf_mono_of_mono ..) <|
              op c))
        x⟩

include instCC in
/-
**TopCat.Presheaf.stalk_mono_of_mono** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Presheaf`
。
形式化陈述：stalk_mono_of_mono {F G : Sheaf C X} (f : F ⟶ G) [Mono f] : forall x, Mono
 (stalkFunctor C x).map f.1
参数：f : F ⟶ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (F : CategoryTheor…
-/
theorem stalk_mono_of_mono {F G : Sheaf C X} (f : F ⟶ G) [Mono f] :
    ∀ x, Mono <| (stalkFunctor C x).map f.1 :=
  fun x => Functor.map_mono (Sheaf.forget.{v} C X ⋙ stalkFunctor C x) f

include instCC in
/-
**TopCat.Presheaf.mono_of_stalk_mono** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Presheaf`
。
形式化陈述：mono_of_stalk_mono {F G : Sheaf C X} (f : F ⟶ G) [forall x, Mono <| (stalk
Functor C x).map f.1] : Mono f
参数：f : F ⟶ G；stalkFunctor C x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Sheaf.Hom.mono_iff_presheaf_mono`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] (J : CategoryTheory.GrothendieckTopology C) (D
 : Type w)   [inst_1 : CategoryTheory…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize.preservesLimitsOfShape`：∀ {C
 : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : 
CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.instHasLimitsOfShapeOfHasLimitsOfSize`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTh
eory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.instHasColimitsOfShapeOfHasColimitsOfSize`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : Catego
ryTheory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.PreservesFilteredColimitsOfSize.preserves_filtered
_colimits`：∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type
 u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.isCofiltered_of_directed_ge_nonempty`：∀ (α : Type u) [ins
t : Preorder α] [IsCodirectedOrder α] [Nonempty α], CategoryTheory.IsCofiltered 
α
· 使用定理 `SemilatticeInf.instIsCodirectedOrder`：∀ {α : Type u_1} [inst : Semilatti
ceInf α], IsCodirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `CategoryTheory.NatTrans.mono_iff_mono_app`：∀ {K : Type u} [inst : Catego
ryTheory.Category.{v, u} K] {C : Type u'} [inst_1 : CategoryTheory.Category.{v',
 u'} C]   {F G : CategoryTheory…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimits`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasLimits C],   Cate
goryTheory.Limits.HasFiniteLimits C
· 使用定理 `CategoryTheory.ConcreteCategory.mono_iff_injective_of_preservesPullback`
：mono_iff_injective_of_preservesPullback {X Y : C} (f : X ⟶ Y) [PreservesLimitsO
fShape WalkingCospan (forget C)] : Mono f ↔ Function.Injectiv…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesLimits.preservesFiniteLimits`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categor
yTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `TopCat.Presheaf.app_injective_of_stalkFunctor_map_injective`：app_injecti
ve_of_stalkFunctor_map_injective {F : Sheaf C X} {G : Presheaf C X} (f : F.1 ⟶ G
) (U : Opens X) (h : forall x in U, Function.Inje…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem mono_of_stalk_mono {F G : Sheaf C X} (f : F ⟶ G) [∀ x, Mono <| (stalkFunctor C x).map f.1] :
    Mono f :=
  (Sheaf.Hom.mono_iff_presheaf_mono _ _ _).mpr <|
    (NatTrans.mono_iff_mono_app _).mpr fun U =>
      (ConcreteCategory.mono_iff_injective_of_preservesPullback _).mpr <|
        app_injective_of_stalkFunctor_map_injective f.1 U.unop fun _x _hx =>
          (ConcreteCategory.mono_iff_injective_of_preservesPullback
            ((stalkFunctor C _).map f.hom)).mp <| inferInstance

include instCC in
/-
**TopCat.Presheaf.mono_iff_stalk_mono** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Presheaf
`。
形式化陈述：mono_iff_stalk_mono {F G : Sheaf C X} (f : F ⟶ G) : Mono f ↔ forall x, Mon
o ((stalkFunctor C x).map f.1)
参数：f : F ⟶ G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.Presheaf.stalk_mono_of_mono`：stalk_mono_of_mono {F G : Sheaf C X}
 (f : F ⟶ G) [Mono f] : forall x, Mono (stalkFunctor C x).map f.1
· 使用定理 `TopCat.Presheaf.mono_of_stalk_mono`：mono_of_stalk_mono {F G : Sheaf C X}
 (f : F ⟶ G) [forall x, Mono <| (stalkFunctor C x).map f.1] : Mono f
-/
theorem mono_iff_stalk_mono {F G : Sheaf C X} (f : F ⟶ G) :
    Mono f ↔ ∀ x, Mono ((stalkFunctor C x).map f.1) :=
  ⟨fun _ => stalk_mono_of_mono _, fun _ => mono_of_stalk_mono _⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- For surjectivity, we are given an arbitrary section `t` and need to find a preimage for it.
We claim that it suffices to find preimages *locally*. That is, for each `x : U` we construct
a neighborhood `V ≤ U` and a section `s : F.obj (op V))` such that `f.app (op V) s` and `t`
agree on `V`. -/
/-
**TopCat.Presheaf.app_surjective_of_injective_of_locally_surjective** 是 Mathlib 
中的一个定理，位于命名空间 `TopCat.Presheaf`。
形式化陈述：app_surjective_of_injective_of_locally_surjective {F G : Sheaf C X} (f : F
 ⟶ G) (U : Opens X) (hinj : forall x in U, Function.Injective ((stalkFunctor C x
).map f.1)) (hsurj : forall (t x) (_ : x in U), exists (V : Opens X) (_ : x in V
) (iVU : V ⟶ U) (s : ToType (F.1.obj (op V))), f.1.app (op V) s = G.1.map iVU.op
 t) : Function.Surjective (f.1.app (op U))
参数：f : F ⟶ G；U : Opens X；hinj : forall x in U, Function.Injective ((stalkFunctor
 C x).map f.1)；hsurj : forall (t x) (_ : x in U), exists (V : Opens X) (_ : x in
 V) (iVU : V ⟶ U) (s : ToType (F.1.obj (op V))), f.1.app (op V) s = G.1.map iVU.
op t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.Presheaf.section_ext`：section_ext (F : Sheaf C X) (U : Opens X) (
s t : ToType (F.1.obj (op U))) (h : forall (x : X) (hx : x in U), F.presheaf.ger
m U x hx s = F.pr…
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopCat.Presheaf.stalkFunctor_map_germ_apply`：stalkFunctor_map_germ_apply
 [ConcreteCategory C FC] {F G : X.Presheaf C} (U : Opens X) (x : X) (hx : x in U
) (f : F ⟶ G) (s) : (stalkFunctor…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.ConcreteCategory.comp_apply`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (
C → Type w)}   {inst_1 : outPara…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `TopCat.Sheaf.existsUnique_gluing'`：∀ {C : Type u_1} [inst : CategoryTheo
ry.Category.{v_1, u_1} C] {FC : C → C → Type u_2} {CC : C → Type u_3}   [inst_1 
: (X Y : C) → FunLike (…
· 使用定理 `TopCat.Sheaf.eq_of_locally_eq'`：∀ {C : Type u_1} [inst : CategoryTheory.
Category.{v_1, u_1} C] {FC : C → C → Type u_2} {CC : C → Type u_3}   [inst_1 : (
X Y : C) → FunLike (…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Subtype.forall'`：∀ {α : Sort u_1} {p : α → Prop} {q : (x : α) → p x → Pr
op}, (∀ (x : α) (h : p x), q x h) ↔ ∀ (x : { a // p a }), q ↑x ⋯

--- 原说明 ---
For surjectivity, we are given an arbitrary section `t` and need to find a preim
age for it.
We claim that it suffices to find preimages *locally*. That is, for each `x : U`
 we construct
a neighborhood `V ≤ U` and a section `s : F.obj (op V))` such that `f.app (op V)
 s` and `t`
agree on `V`.
-/
theorem app_surjective_of_injective_of_locally_surjective {F G : Sheaf C X} (f : F ⟶ G)
    (U : Opens X) (hinj : ∀ x ∈ U, Function.Injective ((stalkFunctor C x).map f.1))
    (hsurj : ∀ (t x) (_ : x ∈ U), ∃ (V : Opens X) (_ : x ∈ V) (iVU : V ⟶ U)
    (s : ToType (F.1.obj (op V))), f.1.app (op V) s = G.1.map iVU.op t) :
    Function.Surjective (f.1.app (op U)) := by
  conv at hsurj =>
    enter [t]
    rw [Subtype.forall' (p := (· ∈ U))]
  intro t
  -- We use the axiom of choice to pick around each point `x` an open neighborhood `V` and a
  -- preimage under `f` on `V`.
  choose V mV iVU sf heq using hsurj t
  -- These neighborhoods clearly cover all of `U`.
  have V_cover : U ≤ iSup V := by
    intro x hxU
    simp only [Opens.mem_iSup]
    exact ⟨⟨x, hxU⟩, mV ⟨x, hxU⟩⟩
  suffices IsCompatible F.obj V sf by
    -- Since `F` is a sheaf, we can glue all the local preimages together to get a global preimage.
    obtain ⟨s, s_spec, -⟩ := F.existsUnique_gluing' V U iVU V_cover sf this
    · use s
      apply G.eq_of_locally_eq' V U iVU V_cover
      intro x
      rw [← ConcreteCategory.comp_apply, ← f.1.naturality, ConcreteCategory.comp_apply, s_spec, heq]
  intro x y
  -- What's left to show here is that the sections `sf` are compatible, i.e. they agree on
  -- the intersections `V x ⊓ V y`. We prove this by showing that all germs are equal.
  apply section_ext
  intro z hz
  -- Here, we need to use injectivity of the stalk maps.
  apply hinj z ((iVU x).le ((inf_le_left : V x ⊓ V y ≤ V x) hz))
  rw [stalkFunctor_map_germ_apply, stalkFunctor_map_germ_apply]
  simp_rw [← ConcreteCategory.comp_apply, f.1.naturality, ConcreteCategory.comp_apply, heq,
    ← ConcreteCategory.comp_apply, ← G.1.map_comp]
  rfl
/-
**TopCat.Presheaf.app_surjective_of_stalkFunctor_map_bijective** 是 Mathlib 中的一个定
理，位于命名空间 `TopCat.Presheaf`。
形式化陈述：app_surjective_of_stalkFunctor_map_bijective {F G : Sheaf C X} (f : F ⟶ G)
 (U : Opens X) (h : forall x in U, Function.Bijective ((stalkFunctor C x).map f.
1)) : Function.Surjective (f.1.app (op U))
参数：f : F ⟶ G；U : Opens X；h : forall x in U, Function.Bijective ((stalkFunctor C 
x).map f.1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.Presheaf.app_surjective_of_injective_of_locally_surjective`：app_s
urjective_of_injective_of_locally_surjective {F G : Sheaf C X} (f : F ⟶ G) (U : 
Opens X) (hinj : forall x in U, Function.Injective ((st…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `TopCat.Presheaf.exists_germ_eq`：exists_germ_eq (F : X.Presheaf C) {x : X
} (t : ToType (stalk.{v, u} F x)) : exists (U : Opens X) (m : x in U) (s : ToTyp
e (F.obj (op U))), F…
· 使用定理 `TopCat.Presheaf.germ_eq`：germ_eq (F : X.Presheaf C) {U V : Opens X} (x :
 X) (mU : x in U) (mV : x in V) (s : ToType (F.obj (op U))) (t : ToType (F.obj (
op V))) (h : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopCat.Presheaf.stalkFunctor_map_germ_apply`：stalkFunctor_map_germ_apply
 [ConcreteCategory C FC] {F G : X.Presheaf C} (U : Opens X) (x : X) (hx : x in U
) (f : F ⟶ G) (s) : (stalkFunctor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ConcreteCategory.comp_apply`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (
C → Type w)}   {inst_1 : outPara…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
theorem app_surjective_of_stalkFunctor_map_bijective {F G : Sheaf C X} (f : F ⟶ G) (U : Opens X)
    (h : ∀ x ∈ U, Function.Bijective ((stalkFunctor C x).map f.1)) :
    Function.Surjective (f.1.app (op U)) := by
  refine app_surjective_of_injective_of_locally_surjective f U (And.left <| h · ·) fun t x hx => ?_
  -- Now we need to prove our initial claim: That we can find preimages of `t` locally.
  -- Since `f` is surjective on stalks, we can find a preimage `s₀` of the germ of `t` at `x`
  obtain ⟨s₀, hs₀⟩ := (h x hx).2 (G.presheaf.germ U x hx t)
  -- ... and this preimage must come from some section `s₁` defined on some open neighborhood `V₁`
  obtain ⟨V₁, hxV₁, s₁, rfl⟩ := F.presheaf.exists_germ_eq s₀
  rename' hs₀ => hs₁
  rw [stalkFunctor_map_germ_apply V₁ x hxV₁ f.1 s₁] at hs₁
  -- Now, the germ of `f.app (op V₁) s₁` equals the germ of `t`, hence they must coincide on
  -- some open neighborhood `V₂`.
  obtain ⟨V₂, hxV₂, iV₂V₁, iV₂U, heq⟩ := G.presheaf.germ_eq x hxV₁ hx _ _ hs₁
  -- The restriction of `s₁` to that neighborhood is our desired local preimage.
  use V₂, hxV₂, iV₂U, F.1.map iV₂V₁.op s₁
  rw [← ConcreteCategory.comp_apply, f.1.naturality, ConcreteCategory.comp_apply, heq]
/-
**TopCat.Presheaf.app_bijective_of_stalkFunctor_map_bijective** 是 Mathlib 中的一个定理
，位于命名空间 `TopCat.Presheaf`。
形式化陈述：app_bijective_of_stalkFunctor_map_bijective {F G : Sheaf C X} (f : F ⟶ G) 
(U : Opens X) (h : forall x in U, Function.Bijective ((stalkFunctor C x).map f.1
)) : Function.Bijective (f.1.app (op U))
参数：f : F ⟶ G；U : Opens X；h : forall x in U, Function.Bijective ((stalkFunctor C 
x).map f.1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.Presheaf.app_injective_of_stalkFunctor_map_injective`：app_injecti
ve_of_stalkFunctor_map_injective {F : Sheaf C X} {G : Presheaf C X} (f : F.1 ⟶ G
) (U : Opens X) (h : forall x in U, Function.Inje…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `TopCat.Presheaf.app_surjective_of_stalkFunctor_map_bijective`：app_surjec
tive_of_stalkFunctor_map_bijective {F G : Sheaf C X} (f : F ⟶ G) (U : Opens X) (
h : forall x in U, Function.Bijective ((stalkFunct…
-/
theorem app_bijective_of_stalkFunctor_map_bijective {F G : Sheaf C X} (f : F ⟶ G) (U : Opens X)
    (h : ∀ x ∈ U, Function.Bijective ((stalkFunctor C x).map f.1)) :
    Function.Bijective (f.1.app (op U)) :=
  ⟨app_injective_of_stalkFunctor_map_injective f.1 U fun x hx => (h x hx).1,
    app_surjective_of_stalkFunctor_map_bijective f U h⟩

include instCC in
/-
**TopCat.Presheaf.app_isIso_of_stalkFunctor_map_iso** 是 Mathlib 中的一个定理，位于命名空间 `T
opCat.Presheaf`。
形式化陈述：app_isIso_of_stalkFunctor_map_iso {F G : Sheaf C X} (f : F ⟶ G) (U : Opens
 X) [forall x : U, IsIso ((stalkFunctor C x.val).map f.1)] : IsIso (f.1.app (op 
U))
参数：f : F ⟶ G；U : Opens X；(stalkFunctor C x.val).map f.1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.isIso_iff_bijective`：isIso_iff_bijective {X Y : Type u} (
f : X ⟶ Y) : IsIso f ↔ Function.Bijective f
· 使用定理 `TopCat.Presheaf.app_bijective_of_stalkFunctor_map_bijective`：app_bijecti
ve_of_stalkFunctor_map_bijective {F G : Sheaf C X} (f : F ⟶ G) (U : Opens X) (h 
: forall x in U, Function.Bijective ((stalkFuncto…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.bijective_iff_isIso_ofHom`：bijective_iff_isIso_ofHom {X Y
 : Type u} (f : X -> Y) : Function.Bijective f ↔ IsIso (ofHom f)
· 使用定理 `CategoryTheory.isIso_of_reflects_iso`：isIso_of_reflects_iso {A B : C} (f
 : A ⟶ B) (F : C ⥤ D) [IsIso (F.map f)] [F.ReflectsIsomorphisms] : IsIso f
-/
theorem app_isIso_of_stalkFunctor_map_iso {F G : Sheaf C X} (f : F ⟶ G) (U : Opens X)
    [∀ x : U, IsIso ((stalkFunctor C x.val).map f.1)] : IsIso (f.1.app (op U)) := by
  -- Since the forgetful functor of `C` reflects isomorphisms, it suffices to see that the
  -- underlying map between types is an isomorphism, i.e. bijective.
  suffices IsIso ((forget C).map (f.1.app (op U))) by
    exact isIso_of_reflects_iso (f.1.app (op U)) (forget C)
  rw [isIso_iff_bijective]
  apply app_bijective_of_stalkFunctor_map_bijective
  intro x hx
  apply (bijective_iff_isIso_ofHom _).mpr
  exact Functor.map_isIso (forget C) ((stalkFunctor C (⟨x, hx⟩ : U).1).map f.1)

include instCC in
-- Making this an instance would cause a loop in typeclass resolution with `Functor.map_isIso`
/-- Let `F` and `G` be sheaves valued in a concrete category, whose forgetful functor reflects
isomorphisms, preserves limits and filtered colimits. Then if the stalk maps of a morphism
`f : F ⟶ G` are all isomorphisms, `f` must be an isomorphism.
-/
/-
**TopCat.Presheaf.isIso_of_stalkFunctor_map_iso** 是 Mathlib 中的一个定理，位于命名空间 `TopCa
t.Presheaf`。
形式化陈述：isIso_of_stalkFunctor_map_iso {F G : Sheaf C X} (f : F ⟶ G) [forall x : X,
 IsIso ((stalkFunctor C x).map f.1)] : IsIso f
参数：f : F ⟶ G；(stalkFunctor C x).map f.1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.Presheaf.app_isIso_of_stalkFunctor_map_iso`：app_isIso_of_stalkFun
ctor_map_iso {F G : Sheaf C X} (f : F ⟶ G) (U : Opens X) [forall x : U, IsIso ((
stalkFunctor C x.val).map f.1)] : IsIso…
· 使用定理 `CategoryTheory.NatIso.isIso_of_isIso_app`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.isIso_of_fully_faithful`：isIso_of_fully_faithful (f : X ⟶
 Y) [IsIso (F.map f)] : IsIso f

--- 原说明 ---
Let `F` and `G` be sheaves valued in a concrete category, whose forgetful functo
r reflects
isomorphisms, preserves limits and filtered colimits. Then if the stalk maps of 
a morphism
`f : F ⟶ G` are all isomorphisms, `f` must be an isomorphism.
-/
theorem isIso_of_stalkFunctor_map_iso {F G : Sheaf C X} (f : F ⟶ G)
    [∀ x : X, IsIso ((stalkFunctor C x).map f.1)] : IsIso f := by
  -- Since the inclusion functor from sheaves to presheaves is fully faithful, it suffices to
  -- show that `f`, as a morphism between _presheaves_, is an isomorphism.
  suffices IsIso ((Sheaf.forget C X).map f) by exact isIso_of_fully_faithful (Sheaf.forget C X) f
  -- We show that all components of `f` are isomorphisms.
  suffices ∀ U : (Opens X)ᵒᵖ, IsIso (f.1.app U) by
    exact @NatIso.isIso_of_isIso_app _ _ _ _ F.1 G.1 f.1 this
  intro U; induction U
  apply app_isIso_of_stalkFunctor_map_iso

include instCC in
/-- Let `F` and `G` be sheaves valued in a concrete category, whose forgetful functor reflects
isomorphisms, preserves limits and filtered colimits. Then a morphism `f : F ⟶ G` is an
isomorphism if and only if all of its stalk maps are isomorphisms.
-/
/-
**TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso** 是 Mathlib 中的一个定理，位于命名空间 `TopC
at.Presheaf`。
形式化陈述：isIso_iff_stalkFunctor_map_iso {F G : Sheaf C X} (f : F ⟶ G) : IsIso f ↔ f
orall x : X, IsIso ((stalkFunctor C x).map f.1)
参数：f : F ⟶ G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.Presheaf.isIso_of_stalkFunctor_map_iso`：isIso_of_stalkFunctor_map
_iso {F G : Sheaf C X} (f : F ⟶ G) [forall x : X, IsIso ((stalkFunctor C x).map 
f.1)] : IsIso f

--- 原说明 ---
Let `F` and `G` be sheaves valued in a concrete category, whose forgetful functo
r reflects
isomorphisms, preserves limits and filtered colimits. Then a morphism `f : F ⟶ G
` is an
isomorphism if and only if all of its stalk maps are isomorphisms.
-/
theorem isIso_iff_stalkFunctor_map_iso {F G : Sheaf C X} (f : F ⟶ G) :
    IsIso f ↔ ∀ x : X, IsIso ((stalkFunctor C x).map f.1) :=
  ⟨fun _ x =>
    @Functor.map_isIso _ _ _ _ _ _ (stalkFunctor C x) f.1 ((Sheaf.forget C X).map_isIso f),
   fun _ => isIso_of_stalkFunctor_map_iso f⟩

end Concrete

end TopCat.Presheaf

