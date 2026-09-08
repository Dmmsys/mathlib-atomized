/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.MonCat.Shrink
public import Mathlib.Algebra.Category.Grp.Shrink
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# The Yoneda embedding for monoid objects for locally small categories

Let `C` be a locally `w`-small category. We define the Yoneda
embedding `shrinkYonedaMon : Mon C ⥤ Cᵒᵖ ⥤ MonCat.{w} w` and its `Grp` analogue.

-/

@[expose] public section

universe w w' v u

namespace CategoryTheory

open Opposite

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C] [CartesianMonoidalCategory C]

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (M : Mon C) (X : Cᵒᵖ) : Small.{w} ((yonedaMon.obj M).obj X) := by
  dsimp
  infer_instance

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (M : Grp C) (X : Cᵒᵖ) : Small.{w} ((yonedaGrp.obj M).obj X) := by
  dsimp
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The Yoneda embedding `Mon C ⥤ Cᵒᵖ ⥤ MonCat.{w}` for a locally `w`-small category `C`. -/
@[simps -isSimp obj map, pp_with_univ]
/-
**CategoryTheory.shrinkYonedaMon** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：shrinkYonedaMon : Mon C ⥤ Cᵒᵖ ⥤ MonCat.{w} where obj X
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instSmallCarrierObjOppositeMonCatMonFunctorYonedaMon`：∀ {
C : Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.LocallySma
ll.{w, v, u} C]   [inst_2 : CategoryTheory.CartesianMonoi…

--- 原说明 ---
The Yoneda embedding `Mon C ⥤ Cᵒᵖ ⥤ MonCat.{w}` for a locally `w`-small category
 `C`.
-/
noncomputable def shrinkYonedaMon :
    Mon C ⥤ Cᵒᵖ ⥤ MonCat.{w} where
  obj X := MonCat.shrinkFunctor (yonedaMon.obj X)
  map f := MonCat.shrinkFunctorMap (yonedaMon.map f)

open MonObj

/-- The type `(shrinkYonedaMon.obj M).obj Y` is equivalent to `Y.unop ⟶ M.X`. -/
/-
**CategoryTheory.shrinkYonedaMonObjObjEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory`。
形式化陈述：shrinkYonedaMonObjObjEquiv {M : Mon C} {Y : Cᵒᵖ} : (shrinkYonedaMon.{w}.ob
j M).obj Y ≃* (Y.unop ⟶ M.X)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type `(shrinkYonedaMon.obj M).obj Y` is equivalent to `Y.unop ⟶ M.X`.
-/
noncomputable def shrinkYonedaMonObjObjEquiv {M : Mon C} {Y : Cᵒᵖ} :
    (shrinkYonedaMon.{w}.obj M).obj Y ≃* (Y.unop ⟶ M.X) :=
  Shrink.mulEquiv

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.shrinkYonedaMon_obj_map_shrinkYonedaMonObjObjEquiv_symm** 是 Mat
hlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：shrinkYonedaMon_obj_map_shrinkYonedaMonObjObjEquiv_symm {M : Mon C} {Y Y' 
: Cᵒᵖ} (g : Y ⟶ Y') (f : Y.unop ⟶ M.X) : (shrinkYonedaMon.{w}.obj _).map g (shri
nkYonedaMonObjObjEquiv.symm f) = shrinkYonedaMonObjObjEquiv.symm (g.unop ≫ f)
参数：g : Y ⟶ Y'；f : Y.unop ⟶ M.X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.instSmallCarrierObjOppositeMonCatMonFunctorYonedaMon`：∀ {
C : Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.LocallySma
ll.{w, v, u} C]   [inst_2 : CategoryTheory.CartesianMonoi…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `MulEquiv.apply_symm_apply`：apply_symm_apply (e : M ≃* N) (y : N) : e (e.
symm y) = y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma shrinkYonedaMon_obj_map_shrinkYonedaMonObjObjEquiv_symm
    {M : Mon C} {Y Y' : Cᵒᵖ} (g : Y ⟶ Y') (f : Y.unop ⟶ M.X) :
    (shrinkYonedaMon.{w}.obj _).map g (shrinkYonedaMonObjObjEquiv.symm f) =
      shrinkYonedaMonObjObjEquiv.symm (g.unop ≫ f) := by
  simp [shrinkYonedaMon, shrinkYonedaMonObjObjEquiv]
/-
**CategoryTheory.shrinkYonedaMonObjObjEquiv_symm_comp** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory`。
形式化陈述：shrinkYonedaMonObjObjEquiv_symm_comp {M : Mon C} {Y Y' : C} (g : Y' ⟶ Y) (
f : Y ⟶ M.X) : shrinkYonedaMonObjObjEquiv.symm (g ≫ f) = (shrinkYonedaMon.obj _)
.map g.op (shrinkYonedaMonObjObjEquiv.symm f)
参数：g : Y' ⟶ Y；f : Y ⟶ M.X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.shrinkYonedaMon_obj_map_shrinkYonedaMonObjObjEquiv_symm`：
shrinkYonedaMon_obj_map_shrinkYonedaMonObjObjEquiv_symm {M : Mon C} {Y Y' : Cᵒᵖ}
 (g : Y ⟶ Y') (f : Y.unop ⟶ M.X) : (shrinkYonedaMon.{w}.obj …
-/
lemma shrinkYonedaMonObjObjEquiv_symm_comp {M : Mon C} {Y Y' : C} (g : Y' ⟶ Y) (f : Y ⟶ M.X) :
    shrinkYonedaMonObjObjEquiv.symm (g ≫ f) =
    (shrinkYonedaMon.obj _).map g.op (shrinkYonedaMonObjObjEquiv.symm f) :=
  (shrinkYonedaMon_obj_map_shrinkYonedaMonObjObjEquiv_symm g.op f).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.shrinkYonedaMon_map_app_shrinkYonedaObjObjEquiv_symm** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：shrinkYonedaMon_map_app_shrinkYonedaObjObjEquiv_symm {M M' : Mon C} {Y : C
ᵒᵖ} (f : Y.unop ⟶ M.X) (g : M ⟶ M') : (shrinkYonedaMon.map g).app _ (shrinkYoned
aMonObjObjEquiv.symm f) = shrinkYonedaMonObjObjEquiv.symm (f ≫ g.hom)
参数：f : Y.unop ⟶ M.X；g : M ⟶ M'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.instSmallCarrierObjOppositeMonCatMonFunctorYonedaMon`：∀ {
C : Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.LocallySma
ll.{w, v, u} C]   [inst_2 : CategoryTheory.CartesianMonoi…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `MulEquiv.apply_symm_apply`：apply_symm_apply (e : M ≃* N) (y : N) : e (e.
symm y) = y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma shrinkYonedaMon_map_app_shrinkYonedaObjObjEquiv_symm
    {M M' : Mon C} {Y : Cᵒᵖ} (f : Y.unop ⟶ M.X) (g : M ⟶ M') :
    (shrinkYonedaMon.map g).app _ (shrinkYonedaMonObjObjEquiv.symm f) =
      shrinkYonedaMonObjObjEquiv.symm (f ≫ g.hom) := by
  simp [shrinkYonedaMon, shrinkYonedaMonObjObjEquiv]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The Yoneda embedding `Grp C ⥤ Cᵒᵖ ⥤ GrpCat.{w}` for a locally `w`-small category `C`. -/
@[simps -isSimp obj map, pp_with_univ]
/-
**CategoryTheory.shrinkYonedaGrp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：shrinkYonedaGrp : Grp C ⥤ Cᵒᵖ ⥤ GrpCat.{w} where obj X
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instSmallCarrierObjOppositeGrpCatGrpFunctorYonedaGrp`：∀ {
C : Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.LocallySma
ll.{w, v, u} C]   [inst_2 : CategoryTheory.CartesianMonoi…

--- 原说明 ---
The Yoneda embedding `Grp C ⥤ Cᵒᵖ ⥤ GrpCat.{w}` for a locally `w`-small category
 `C`.
-/
noncomputable def shrinkYonedaGrp :
    Grp C ⥤ Cᵒᵖ ⥤ GrpCat.{w} where
  obj X := GrpCat.shrinkFunctor (yonedaGrp.obj X)
  map f := GrpCat.shrinkFunctorMap (yonedaGrp.map f)

/-- The type `(shrinkYonedaGrp.obj M).obj Y` is equivalent to `Y.unop ⟶ M.X`. -/
/-
**CategoryTheory.shrinkYonedaGrpObjObjEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory`。
形式化陈述：shrinkYonedaGrpObjObjEquiv {M : Grp C} {Y : Cᵒᵖ} : (shrinkYonedaGrp.{w}.ob
j M).obj Y ≃* (Y.unop ⟶ M.X)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type `(shrinkYonedaGrp.obj M).obj Y` is equivalent to `Y.unop ⟶ M.X`.
-/
noncomputable def shrinkYonedaGrpObjObjEquiv {M : Grp C} {Y : Cᵒᵖ} :
    (shrinkYonedaGrp.{w}.obj M).obj Y ≃* (Y.unop ⟶ M.X) :=
  Shrink.mulEquiv

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.shrinkYonedaGrp_obj_map_shrinkYonedaGrpObjObjEquiv_symm** 是 Mat
hlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：shrinkYonedaGrp_obj_map_shrinkYonedaGrpObjObjEquiv_symm {M : Grp C} {Y Y' 
: Cᵒᵖ} (g : Y ⟶ Y') (f : Y.unop ⟶ M.X) : (shrinkYonedaGrp.{w}.obj _).map g (shri
nkYonedaGrpObjObjEquiv.symm f) = shrinkYonedaGrpObjObjEquiv.symm (g.unop ≫ f)
参数：g : Y ⟶ Y'；f : Y.unop ⟶ M.X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.instSmallCarrierObjOppositeGrpCatGrpFunctorYonedaGrp`：∀ {
C : Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.LocallySma
ll.{w, v, u} C]   [inst_2 : CategoryTheory.CartesianMonoi…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `MulEquiv.apply_symm_apply`：apply_symm_apply (e : M ≃* N) (y : N) : e (e.
symm y) = y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma shrinkYonedaGrp_obj_map_shrinkYonedaGrpObjObjEquiv_symm
    {M : Grp C} {Y Y' : Cᵒᵖ} (g : Y ⟶ Y') (f : Y.unop ⟶ M.X) :
    (shrinkYonedaGrp.{w}.obj _).map g (shrinkYonedaGrpObjObjEquiv.symm f) =
      shrinkYonedaGrpObjObjEquiv.symm (g.unop ≫ f) := by
  simp [shrinkYonedaGrp, shrinkYonedaGrpObjObjEquiv]
/-
**CategoryTheory.shrinkYonedaGrpObjObjEquiv_symm_comp** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory`。
形式化陈述：shrinkYonedaGrpObjObjEquiv_symm_comp {M : Grp C} {Y Y' : C} (g : Y' ⟶ Y) (
f : Y ⟶ M.X) : shrinkYonedaGrpObjObjEquiv.symm (g ≫ f) = (shrinkYonedaGrp.obj _)
.map g.op (shrinkYonedaGrpObjObjEquiv.symm f)
参数：g : Y' ⟶ Y；f : Y ⟶ M.X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.shrinkYonedaGrp_obj_map_shrinkYonedaGrpObjObjEquiv_symm`：
shrinkYonedaGrp_obj_map_shrinkYonedaGrpObjObjEquiv_symm {M : Grp C} {Y Y' : Cᵒᵖ}
 (g : Y ⟶ Y') (f : Y.unop ⟶ M.X) : (shrinkYonedaGrp.{w}.obj …
-/
lemma shrinkYonedaGrpObjObjEquiv_symm_comp {M : Grp C} {Y Y' : C} (g : Y' ⟶ Y) (f : Y ⟶ M.X) :
    shrinkYonedaGrpObjObjEquiv.symm (g ≫ f) =
    (shrinkYonedaGrp.obj _).map g.op (shrinkYonedaGrpObjObjEquiv.symm f) :=
  (shrinkYonedaGrp_obj_map_shrinkYonedaGrpObjObjEquiv_symm g.op f).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.shrinkYonedaGrp_map_app_shrinkYonedaObjObjEquiv_symm** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：shrinkYonedaGrp_map_app_shrinkYonedaObjObjEquiv_symm {M M' : Grp C} {Y : C
ᵒᵖ} (f : Y.unop ⟶ M.X) (g : M ⟶ M') : (shrinkYonedaGrp.map g).app _ (shrinkYoned
aGrpObjObjEquiv.symm f) = shrinkYonedaGrpObjObjEquiv.symm (f ≫ g.hom.hom)
参数：f : Y.unop ⟶ M.X；g : M ⟶ M'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.instSmallCarrierObjOppositeGrpCatGrpFunctorYonedaGrp`：∀ {
C : Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.LocallySma
ll.{w, v, u} C]   [inst_2 : CategoryTheory.CartesianMonoi…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `MulEquiv.apply_symm_apply`：apply_symm_apply (e : M ≃* N) (y : N) : e (e.
symm y) = y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma shrinkYonedaGrp_map_app_shrinkYonedaObjObjEquiv_symm
    {M M' : Grp C} {Y : Cᵒᵖ} (f : Y.unop ⟶ M.X) (g : M ⟶ M') :
    (shrinkYonedaGrp.map g).app _ (shrinkYonedaGrpObjObjEquiv.symm f) =
      shrinkYonedaGrpObjObjEquiv.symm (f ≫ g.hom.hom) := by
  simp [shrinkYonedaGrp, shrinkYonedaGrpObjObjEquiv]

end CategoryTheory

