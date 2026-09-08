/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.EssentiallySmall

/-!
# The Yoneda functor for locally small categories

Let `C` be a locally `w`-small category. We define the Yoneda
embedding `shrinkYoneda : C ⥤ Cᵒᵖ ⥤ Type w`. (See the
file `CategoryTheory.Yoneda` for the other variants `yoneda` and
`uliftYoneda`.)

-/

@[expose] public section

universe w w' w'' v u

namespace CategoryTheory

open Opposite

variable {C : Type u} [Category.{v} C]

namespace FunctorToTypes

/-- A functor to types `F : C ⥤ Type w'` is `w`-small if for any `X : C`,
the type `F.obj X` is `w`-small. -/
@[pp_with_univ]
/-
**CategoryTheory.FunctorToTypes.Small** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
FunctorToTypes`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → CategoryTheory.
Functor C (Type w') → Prop
参数：Type w'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor to types `F : C ⥤ Type w'` is `w`-small if for any `X : C`,
the type `F.obj X` is `w`-small.
-/
protected abbrev Small (F : C ⥤ Type w') := ∀ (X : C), _root_.Small.{w} (F.obj X)

/-- If a functor `F : C ⥤ Type w'` is `w`-small, this is the functor `C ⥤ Type w`
obtained by shrinking `F.obj X` for all `X : C`. -/
@[implicit_reducible, simps obj map, pp_with_univ]
/-
**CategoryTheory.FunctorToTypes.shrink** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.FunctorToTypes`。
形式化陈述：shrink (F : C ⥤ Type w') [FunctorToTypes.Small.{w} F] : C ⥤ Type w where o
bj X
参数：F : C ⥤ Type w'。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If a functor `F : C ⥤ Type w'` is `w`-small, this is the functor `C ⥤ Type w`
obtained by shrinking `F.obj X` for all `X : C`.
-/
noncomputable def shrink (F : C ⥤ Type w') [FunctorToTypes.Small.{w} F] :
    C ⥤ Type w where
  obj X := Shrink.{w} (F.obj X)
  map f := ↾(equivShrink.{w} _ ∘ F.map f ∘ (equivShrink.{w} _).symm)

/-- The natural transformation `shrink.{w} F ⟶ shrink.{w} G` induces by a natural
transformation `τ : F ⟶ G` between `w`-small functors to types. -/
@[implicit_reducible, simps]
/-
**CategoryTheory.FunctorToTypes.shrinkMap** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.FunctorToTypes`。
形式化陈述：shrinkMap {F G : C ⥤ Type w'} (τ : F ⟶ G) [FunctorToTypes.Small.{w} F] [Fu
nctorToTypes.Small.{w} G] : shrink.{w} F ⟶ shrink.{w} G where app X
参数：τ : F ⟶ G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The natural transformation `shrink.{w} F ⟶ shrink.{w} G` induces by a natural
transformation `τ : F ⟶ G` between `w`-small functors to types.
-/
noncomputable def shrinkMap {F G : C ⥤ Type w'} (τ : F ⟶ G) [FunctorToTypes.Small.{w} F]
    [FunctorToTypes.Small.{w} G] :
    shrink.{w} F ⟶ shrink.{w} G where
  app X := ↾(equivShrink.{w} _ ∘ τ.app X ∘ (equivShrink.{w} _).symm)

set_option backward.defeqAttrib.useBackward true in
/-- Shrinking `F` to `Type w` followed by universe lifting is the same as shrinking to
`Type (max w w')`. -/
@[simps! hom_app inv_app]
noncomputable
/-
**CategoryTheory.FunctorToTypes.shrinkCompUliftFunctorIso** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.FunctorToTypes`。
形式化陈述：shrinkCompUliftFunctorIso (F : C ⥤ Type w') [FunctorToTypes.Small.{w} F] [
FunctorToTypes.Small.{max w w''} F] : shrink.{w} F ⋙ uliftFunctor.{w'', w} ≅ shr
ink.{max w w''} F
参数：F : C ⥤ Type w'。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
def shrinkCompUliftFunctorIso (F : C ⥤ Type w') [FunctorToTypes.Small.{w} F]
    [FunctorToTypes.Small.{max w w''} F] :
    shrink.{w} F ⋙ uliftFunctor.{w'', w} ≅ shrink.{max w w''} F :=
  NatIso.ofComponents
    (fun X ↦ Equiv.toIso ((Equiv.ulift.trans (equivShrink _).symm).trans (equivShrink _)))

unif_hint (F : C ⥤ Type w') [FunctorToTypes.Small.{w} F] (X : C) where ⊢
  Shrink (F.obj X) ≟ (FunctorToTypes.shrink F).obj X

end FunctorToTypes

variable [LocallySmall.{w} C]

section Yoneda

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) : FunctorToTypes.Small.{w} (yoneda.obj X) :=
  fun _ ↦ by dsimp; infer_instance

/-- The Yoneda embedding `C ⥤ Cᵒᵖ ⥤ Type w` for a locally `w`-small category `C`. -/
@[simps -isSimp obj map, pp_with_univ]
/-
**CategoryTheory.shrinkYoneda** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：shrinkYoneda : C ⥤ Cᵒᵖ ⥤ Type w where obj X
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instSmallOppositeObjFunctorTypeYoneda`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] [CategoryTheory.LocallySmall.{w, v, u} C]
 (X : C),   CategoryTheory.FunctorToTypes.…

--- 原说明 ---
The Yoneda embedding `C ⥤ Cᵒᵖ ⥤ Type w` for a locally `w`-small category `C`.
-/
noncomputable def shrinkYoneda :
    C ⥤ Cᵒᵖ ⥤ Type w where
  obj X := FunctorToTypes.shrink (yoneda.obj X)
  map f := FunctorToTypes.shrinkMap (yoneda.map f)

set_option backward.isDefEq.respectTransparency.types false in
/-- The type `(shrinkYoneda.obj X).obj Y` is equivalent to `Y.unop ⟶ X`. -/
/-
**CategoryTheory.shrinkYonedaObjObjEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry`。
形式化陈述：shrinkYonedaObjObjEquiv {X : C} {Y : Cᵒᵖ} : ((shrinkYoneda.{w}.obj X).obj 
Y) ≃ (Y.unop ⟶ X)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The type `(shrinkYoneda.obj X).obj Y` is equivalent to `Y.unop ⟶ X`.
-/
noncomputable def shrinkYonedaObjObjEquiv {X : C} {Y : Cᵒᵖ} :
    ((shrinkYoneda.{w}.obj X).obj Y) ≃ (Y.unop ⟶ X) :=
  (equivShrink _).symm
/-
**CategoryTheory.shrinkYoneda_obj_map** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`
。
形式化陈述：shrinkYoneda_obj_map {X : C} {Y Y' : Cᵒᵖ} (g : Y ⟶ Y') (f : (shrinkYoneda.
obj X).obj Y) : (shrinkYoneda.obj _).map g f = shrinkYonedaObjObjEquiv.symm (g.u
nop ≫ shrinkYonedaObjObjEquiv f)
参数：g : Y ⟶ Y'；f : (shrinkYoneda.obj X).obj Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma shrinkYoneda_obj_map {X : C} {Y Y' : Cᵒᵖ} (g : Y ⟶ Y') (f : (shrinkYoneda.obj X).obj Y) :
    (shrinkYoneda.obj _).map g f =
      shrinkYonedaObjObjEquiv.symm (g.unop ≫ shrinkYonedaObjObjEquiv f) :=
  rfl
/-
**CategoryTheory.shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm {X : C} {Y Y' : Cᵒᵖ} (g 
: Y ⟶ Y') (f : Y.unop ⟶ X) : (shrinkYoneda.obj _).map g (shrinkYonedaObjObjEquiv
.symm f) = shrinkYonedaObjObjEquiv.symm (g.unop ≫ f)
参数：g : Y ⟶ Y'；f : Y.unop ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm
    {X : C} {Y Y' : Cᵒᵖ} (g : Y ⟶ Y') (f : Y.unop ⟶ X) :
    (shrinkYoneda.obj _).map g (shrinkYonedaObjObjEquiv.symm f) =
      shrinkYonedaObjObjEquiv.symm (g.unop ≫ f) := by
  simp [shrinkYoneda_obj_map]
/-
**CategoryTheory.shrinkYonedaObjObjEquiv_symm_comp** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory`。
形式化陈述：shrinkYonedaObjObjEquiv_symm_comp {X Y Y' : C} (g : Y' ⟶ Y) (f : Y ⟶ X) : 
shrinkYonedaObjObjEquiv.symm (g ≫ f) = (shrinkYoneda.obj _).map g.op (shrinkYone
daObjObjEquiv.symm f)
参数：g : Y' ⟶ Y；f : Y ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `CategoryTheory.shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm`：shrink
Yoneda_obj_map_shrinkYonedaObjObjEquiv_symm {X : C} {Y Y' : Cᵒᵖ} (g : Y ⟶ Y') (f
 : Y.unop ⟶ X) : (shrinkYoneda.obj _).map g (shrinkYon…
-/
lemma shrinkYonedaObjObjEquiv_symm_comp {X Y Y' : C} (g : Y' ⟶ Y) (f : Y ⟶ X) :
    shrinkYonedaObjObjEquiv.symm (g ≫ f) =
    (shrinkYoneda.obj _).map g.op (shrinkYonedaObjObjEquiv.symm f) :=
  (shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm g.op f).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm {X X' : C} {Y : Cᵒᵖ} (f 
: Y.unop ⟶ X) (g : X ⟶ X') : (shrinkYoneda.map g).app _ (shrinkYonedaObjObjEquiv
.symm f) = shrinkYonedaObjObjEquiv.symm (f ≫ g)
参数：f : Y.unop ⟶ X；g : X ⟶ X'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.instSmallOppositeObjFunctorTypeYoneda`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] [CategoryTheory.LocallySmall.{w, v, u} C]
 (X : C),   CategoryTheory.FunctorToTypes.…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm
    {X X' : C} {Y : Cᵒᵖ} (f : Y.unop ⟶ X) (g : X ⟶ X') :
    (shrinkYoneda.map g).app _ (shrinkYonedaObjObjEquiv.symm f) =
      shrinkYonedaObjObjEquiv.symm (f ≫ g) := by
  simp [shrinkYoneda, shrinkYonedaObjObjEquiv]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.shrinkYonedaObjObjEquiv_map_app** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory`。
形式化陈述：shrinkYonedaObjObjEquiv_map_app {X X' : C} {Y : Cᵒᵖ} (f : (shrinkYoneda.{w
, v, u}.obj X).obj Y) (g : X ⟶ X') : shrinkYonedaObjObjEquiv ((shrinkYoneda.map 
g).app Y f) = shrinkYonedaObjObjEquiv f ≫ g
参数：f : (shrinkYoneda.{w, v, u}.obj X).obj Y；g : X ⟶ X'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.instSmallOppositeObjFunctorTypeYoneda`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] [CategoryTheory.LocallySmall.{w, v, u} C]
 (X : C),   CategoryTheory.FunctorToTypes.…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma shrinkYonedaObjObjEquiv_map_app
    {X X' : C} {Y : Cᵒᵖ} (f : (shrinkYoneda.{w, v, u}.obj X).obj Y) (g : X ⟶ X') :
    shrinkYonedaObjObjEquiv ((shrinkYoneda.map g).app Y f) =
      shrinkYonedaObjObjEquiv f ≫ g := by
  simp [shrinkYoneda, shrinkYonedaObjObjEquiv]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.shrinkYonedaObjObjEquiv_obj_map** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory`。
形式化陈述：shrinkYonedaObjObjEquiv_obj_map {X : C} {Y Y' : Cᵒᵖ} (g : Y ⟶ Y') (f : (sh
rinkYoneda.{w}.obj X).obj Y) : shrinkYonedaObjObjEquiv ((shrinkYoneda.{w}.obj X)
.map g f) = g.unop ≫ shrinkYonedaObjObjEquiv f
参数：g : Y ⟶ Y'；f : (shrinkYoneda.{w}.obj X).obj Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.instSmallOppositeObjFunctorTypeYoneda`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] [CategoryTheory.LocallySmall.{w, v, u} C]
 (X : C),   CategoryTheory.FunctorToTypes.…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma shrinkYonedaObjObjEquiv_obj_map {X : C} {Y Y' : Cᵒᵖ} (g : Y ⟶ Y')
    (f : (shrinkYoneda.{w}.obj X).obj Y) :
    shrinkYonedaObjObjEquiv ((shrinkYoneda.{w}.obj X).map g f) =
      g.unop ≫ shrinkYonedaObjObjEquiv f := by
  simp [shrinkYonedaObjObjEquiv, shrinkYoneda]

set_option backward.isDefEq.respectTransparency false in
/-- The type of natural transformations `shrinkYoneda.{w}.obj X ⟶ P`
with `X : C` and `P : Cᵒᵖ ⥤ Type w` is equivalent to `P.obj (op X)`. -/
/-
**CategoryTheory.shrinkYonedaEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：shrinkYonedaEquiv {X : C} {P : Cᵒᵖ ⥤ Type w} : (shrinkYoneda.{w}.obj X ⟶ P
) ≃ P.obj (op X) where toFun τ
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The type of natural transformations `shrinkYoneda.{w}.obj X ⟶ P`
with `X : C` and `P : Cᵒᵖ ⥤ Type w` is equivalent to `P.obj (op X)`.
-/
noncomputable def shrinkYonedaEquiv {X : C} {P : Cᵒᵖ ⥤ Type w} :
    (shrinkYoneda.{w}.obj X ⟶ P) ≃ P.obj (op X) where
  toFun τ := τ.app _ (equivShrink.{w} _ (𝟙 X))
  invFun x :=
    { app Y := ↾fun f ↦ P.map ((equivShrink.{w} _).symm f).op x
      naturality Y Z g := by ext; simp [shrinkYoneda] }
  left_inv τ := by
    ext Y f
    obtain ⟨f, rfl⟩ := (equivShrink _).surjective f
    simpa [shrinkYoneda] using ((τ.naturality_apply f.op) (equivShrink _ (𝟙 X))).symm
  right_inv x := by simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.map_shrinkYonedaEquiv** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
`。
形式化陈述：map_shrinkYonedaEquiv {X Y : C} {P : Cᵒᵖ ⥤ Type w} (f : shrinkYoneda.obj X
 ⟶ P) (g : Y ⟶ X) : P.map g.op (shrinkYonedaEquiv f) = f.app (op Y) (shrinkYoned
aObjObjEquiv.symm g)
参数：f : shrinkYoneda.obj X ⟶ P；g : Y ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.instSmallOppositeObjFunctorTypeYoneda`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] [CategoryTheory.LocallySmall.{w, v, u} C]
 (X : C),   CategoryTheory.FunctorToTypes.…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_shrinkYonedaEquiv {X Y : C} {P : Cᵒᵖ ⥤ Type w} (f : shrinkYoneda.obj X ⟶ P)
    (g : Y ⟶ X) : P.map g.op (shrinkYonedaEquiv f) =
      f.app (op Y) (shrinkYonedaObjObjEquiv.symm g) := by
  simp [shrinkYonedaObjObjEquiv, shrinkYonedaEquiv, shrinkYoneda,
    ← comp_apply, ← NatTrans.naturality]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.shrinkYonedaEquiv_shrinkYoneda_map** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory`。
形式化陈述：shrinkYonedaEquiv_shrinkYoneda_map {X Y : C} (f : X ⟶ Y) : shrinkYonedaEqu
iv (shrinkYoneda.{w}.map f) = shrinkYonedaObjObjEquiv.symm f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.instSmallOppositeObjFunctorTypeYoneda`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] [CategoryTheory.LocallySmall.{w, v, u} C]
 (X : C),   CategoryTheory.FunctorToTypes.…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma shrinkYonedaEquiv_shrinkYoneda_map {X Y : C} (f : X ⟶ Y) :
    shrinkYonedaEquiv (shrinkYoneda.{w}.map f) = shrinkYonedaObjObjEquiv.symm f := by
  simp [shrinkYonedaEquiv, shrinkYoneda, shrinkYonedaObjObjEquiv]

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.shrinkYonedaEquiv_comp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y`。
形式化陈述：shrinkYonedaEquiv_comp {X : C} {P Q : Cᵒᵖ ⥤ Type w} (α : shrinkYoneda.obj 
X ⟶ P) (β : P ⟶ Q) : shrinkYonedaEquiv (α ≫ β) = β.app _ (shrinkYonedaEquiv α)
参数：α : shrinkYoneda.obj X ⟶ P；β : P ⟶ Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma shrinkYonedaEquiv_comp {X : C} {P Q : Cᵒᵖ ⥤ Type w} (α : shrinkYoneda.obj X ⟶ P)
    (β : P ⟶ Q) :
    shrinkYonedaEquiv (α ≫ β) = β.app _ (shrinkYonedaEquiv α) := by
  simp [shrinkYonedaEquiv]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.shrinkYonedaEquiv_naturality** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory`。
形式化陈述：shrinkYonedaEquiv_naturality {X Y : C} {P : Cᵒᵖ ⥤ Type w} (f : shrinkYoned
a.obj X ⟶ P) (g : Y ⟶ X) : P.map g.op (shrinkYonedaEquiv f) = shrinkYonedaEquiv 
(shrinkYoneda.map g ≫ f)
参数：f : shrinkYoneda.obj X ⟶ P；g : Y ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instSmallOppositeObjFunctorTypeYoneda`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] [CategoryTheory.LocallySmall.{w, v, u} C]
 (X : C),   CategoryTheory.FunctorToTypes.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatTrans.naturality_apply`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {D : Type u_1} [inst_1 : CategoryTheory.Category.{v_1
, u_1} D]   {FD : outParam (D …
-/
lemma shrinkYonedaEquiv_naturality {X Y : C} {P : Cᵒᵖ ⥤ Type w}
    (f : shrinkYoneda.obj X ⟶ P) (g : Y ⟶ X) :
    P.map g.op (shrinkYonedaEquiv f) = shrinkYonedaEquiv (shrinkYoneda.map g ≫ f) := by
  simpa [shrinkYonedaEquiv, shrinkYoneda]
    using (f.naturality_apply g.op ((equivShrink _) (𝟙 _))).symm

@[reassoc]
/-
**CategoryTheory.shrinkYonedaEquiv_symm_map** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory`。
形式化陈述：shrinkYonedaEquiv_symm_map {X Y : Cᵒᵖ} (f : X ⟶ Y) {P : Cᵒᵖ ⥤ Type w} (t :
 P.obj X) : shrinkYonedaEquiv.symm (P.map f t) = shrinkYoneda.map f.unop ≫ shrin
kYonedaEquiv.symm t
参数：f : X ⟶ Y；t : P.obj X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.shrinkYonedaEquiv_naturality`：shrinkYonedaEquiv_naturalit
y {X Y : C} {P : Cᵒᵖ ⥤ Type w} (f : shrinkYoneda.obj X ⟶ P) (g : Y ⟶ X) : P.map 
g.op (shrinkYonedaEquiv f) = shri…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma shrinkYonedaEquiv_symm_map {X Y : Cᵒᵖ} (f : X ⟶ Y) {P : Cᵒᵖ ⥤ Type w} (t : P.obj X) :
    shrinkYonedaEquiv.symm (P.map f t) =
      shrinkYoneda.map f.unop ≫ shrinkYonedaEquiv.symm t :=
  shrinkYonedaEquiv.injective (by
    obtain ⟨t, rfl⟩ := shrinkYonedaEquiv.surjective t
    rw [← shrinkYonedaEquiv_naturality]
    simp)
/-
**CategoryTheory.shrinkYonedaEquiv_symm_app_shrinkYonedaObjObjEquiv_symm** 是 Mat
hlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：shrinkYonedaEquiv_symm_app_shrinkYonedaObjObjEquiv_symm {X : C} {P : Cᵒᵖ ⥤
 Type w} (s : P.obj (op X)) {Y : C} (f : Y ⟶ X) : (shrinkYonedaEquiv.symm s).app
 (op Y) (shrinkYonedaObjObjEquiv.symm f) = P.map f.op s
参数：s : P.obj (op X)；f : Y ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用引理 `CategoryTheory.map_shrinkYonedaEquiv`：map_shrinkYonedaEquiv {X Y : C} {P
 : Cᵒᵖ ⥤ Type w} (f : shrinkYoneda.obj X ⟶ P) (g : Y ⟶ X) : P.map g.op (shrinkYo
nedaEquiv f) = f.app (op Y…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma shrinkYonedaEquiv_symm_app_shrinkYonedaObjObjEquiv_symm {X : C} {P : Cᵒᵖ ⥤ Type w}
    (s : P.obj (op X)) {Y : C} (f : Y ⟶ X) :
    (shrinkYonedaEquiv.symm s).app (op Y) (shrinkYonedaObjObjEquiv.symm f) =
      P.map f.op s := by
  obtain ⟨g, rfl⟩ := shrinkYonedaEquiv.surjective s
  simp [map_shrinkYonedaEquiv]

set_option backward.isDefEq.respectTransparency.types false in
variable (C) in
/-- The functor `shrinkYoneda : C ⥤ Cᵒᵖ ⥤ Type w` for a locally `w`-small category `C`
is fully faithful. -/
/-
**CategoryTheory.fullyFaithfulShrinkYoneda** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory`。
形式化陈述：fullyFaithfulShrinkYoneda : (shrinkYoneda.{w} (C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `shrinkYoneda : C ⥤ Cᵒᵖ ⥤ Type w` for a locally `w`-small category `
C`
is fully faithful.
-/
noncomputable def fullyFaithfulShrinkYoneda :
    (shrinkYoneda.{w} (C := C)).FullyFaithful where
  preimage f := shrinkYonedaObjObjEquiv (shrinkYonedaEquiv f)
  map_preimage f := by
    obtain ⟨f, rfl⟩ := shrinkYonedaEquiv.symm.surjective f
    cat_disch
  preimage_map f := by simp [shrinkYonedaEquiv_shrinkYoneda_map]
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (shrinkYoneda.{w} (C := C)).Faithful := (fullyFaithfulShrinkYoneda C).faithful
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (shrinkYoneda.{w} (C := C)).Full := (fullyFaithfulShrinkYoneda C).full

set_option backward.defeqAttrib.useBackward true in
/-- `shrinkYoneda` at the morphism universe level is `yoneda`. -/
@[simps! hom_app inv_app]
noncomputable
/-
**CategoryTheory.shrinkYonedaIsoYoneda** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
`。
形式化陈述：shrinkYonedaIsoYoneda : shrinkYoneda.{v} ≅ yoneda (C
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.locallySmall_of_univLE`：∀ (C : Type u) [inst : CategoryTh
eory.Category.{v, u} C] [UnivLE.{v, w}], CategoryTheory.LocallySmall.{w, v, u} C
-/
def shrinkYonedaIsoYoneda : shrinkYoneda.{v} ≅ yoneda (C := C) :=
  NatIso.ofComponents
    (fun X ↦ NatIso.ofComponents (fun Y ↦ shrinkYonedaObjObjEquiv.toIso)
      (by intros; ext; simp [shrinkYonedaObjObjEquiv_obj_map]))
    (by intros; ext; simp [shrinkYonedaObjObjEquiv_map_app])

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- `shrinkYoneda` is compatible with `uliftFunctor`. -/
noncomputable
/-
**CategoryTheory.shrinkYonedaUliftFunctorIso** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory`。
形式化陈述：shrinkYonedaUliftFunctorIso [LocallySmall.{max w w'} C] : shrinkYoneda.{w}
 ⋙ (Functor.whiskeringRight Cᵒᵖ _ _).obj uliftFunctor.{w', w} ≅ shrinkYoneda
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instSmallOppositeObjFunctorTypeYoneda`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] [CategoryTheory.LocallySmall.{w, v, u} C]
 (X : C),   CategoryTheory.FunctorToTypes.…
-/
def shrinkYonedaUliftFunctorIso [LocallySmall.{max w w'} C] :
    shrinkYoneda.{w} ⋙ (Functor.whiskeringRight Cᵒᵖ _ _).obj uliftFunctor.{w', w} ≅
      shrinkYoneda :=
  NatIso.ofComponents
    (fun X ↦ FunctorToTypes.shrinkCompUliftFunctorIso.{w, v} (yoneda.obj X))
    fun _ ↦ by ext; simp [shrinkYoneda]

/-- `uliftYoneda` identifies to `shrinkYoneda`. -/
/-
**CategoryTheory.uliftYonedaIsoShrinkYoneda** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory`。
形式化陈述：uliftYonedaIsoShrinkYoneda : uliftYoneda.{w'} (C
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`uliftYoneda` identifies to `shrinkYoneda`.
-/
noncomputable def uliftYonedaIsoShrinkYoneda :
    uliftYoneda.{w'} (C := C) ≅ shrinkYoneda.{max w' v} :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents
    (fun Y ↦ (Equiv.ulift.trans shrinkYonedaObjObjEquiv.symm).toIso) (fun f ↦ by
      ext
      exact (shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm _ _).symm)) (fun g ↦ by
      ext
      exact (shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm _ _).symm)

set_option backward.defeqAttrib.useBackward true in
/-- The functor `shrinkYoneda.{w}` followed by the evaluation
at `Y : Cᵒᵖ` and `uliftFunctor.{v}` identifies to `coyoneda.obj Y` followed
by `uliftFunctor.{w}`. -/
/-
**CategoryTheory.shrinkYonedaCompEvaluationCompUliftFunctorIsoUliftFunctor** 是 M
athlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：shrinkYonedaCompEvaluationCompUliftFunctorIsoUliftFunctor (Y : Cᵒᵖ) : shri
nkYoneda.{w} ⋙ (evaluation Cᵒᵖ _).obj Y ⋙ uliftFunctor.{v} ≅ coyoneda.obj Y ⋙ ul
iftFunctor.{w}
参数：Y : Cᵒᵖ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The functor `shrinkYoneda.{w}` followed by the evaluation
at `Y : Cᵒᵖ` and `uliftFunctor.{v}` identifies to `coyoneda.obj Y` followed
by `uliftFunctor.{w}`.
-/
noncomputable def shrinkYonedaCompEvaluationCompUliftFunctorIsoUliftFunctor (Y : Cᵒᵖ) :
    shrinkYoneda.{w} ⋙ (evaluation Cᵒᵖ _).obj Y ⋙ uliftFunctor.{v} ≅
      coyoneda.obj Y ⋙ uliftFunctor.{w} :=
  NatIso.ofComponents (fun X ↦ (Equiv.ulift.trans
    (shrinkYonedaObjObjEquiv.trans Equiv.ulift.symm)).toIso) (fun f ↦ by
      ext ⟨g⟩
      obtain ⟨g, rfl⟩ := shrinkYonedaObjObjEquiv.symm.surjective g
      simp [shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm])

/-- `shrinkYoneda.obj X` is represented by `X`. -/
@[simps]
noncomputable
/-
**CategoryTheory.shrinkYonedaRepresentableBy** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory`。
形式化陈述：shrinkYonedaRepresentableBy (X : C) : (shrinkYoneda.{w}.obj X).Representab
leBy X where homEquiv
参数：X : C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `CategoryTheory.shrinkYonedaObjObjEquiv_symm_comp`：shrinkYonedaObjObjEqui
v_symm_comp {X Y Y' : C} (g : Y' ⟶ Y) (f : Y ⟶ X) : shrinkYonedaObjObjEquiv.symm
 (g ≫ f) = (shrinkYoneda.obj _).map g.…
-/
def shrinkYonedaRepresentableBy (X : C) : (shrinkYoneda.{w}.obj X).RepresentableBy X where
  homEquiv := shrinkYonedaObjObjEquiv.symm
  homEquiv_comp := shrinkYonedaObjObjEquiv_symm_comp
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) : (shrinkYoneda.{w}.obj X).IsRepresentable :=
  (shrinkYonedaRepresentableBy X).isRepresentable

end Yoneda

section Coyoneda

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : Cᵒᵖ) : FunctorToTypes.Small.{w} (coyoneda.obj X) :=
  fun _ ↦ by dsimp; infer_instance

/-- The co-Yoneda embedding `Cᵒᵖ ⥤ C ⥤ Type w` for a locally `w`-small category `C`. -/
@[pp_with_univ]
/-
**CategoryTheory.shrinkCoyoneda** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：shrinkCoyoneda : Cᵒᵖ ⥤ C ⥤ Type w
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The co-Yoneda embedding `Cᵒᵖ ⥤ C ⥤ Type w` for a locally `w`-small category `C`.
-/
noncomputable abbrev shrinkCoyoneda : Cᵒᵖ ⥤ C ⥤ Type w := shrinkYoneda.flip
/-
**CategoryTheory.shrinkCoyoneda_obj** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：shrinkCoyoneda_obj {X : Cᵒᵖ} : shrinkCoyoneda.obj X = FunctorToTypes.shrin
k (coyoneda.obj X)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma shrinkCoyoneda_obj {X : Cᵒᵖ} :
    shrinkCoyoneda.obj X = FunctorToTypes.shrink (coyoneda.obj X) := rfl
/-
**CategoryTheory.shrinkCoyoneda_map** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：shrinkCoyoneda_map {X Y : Cᵒᵖ} {f : X ⟶ Y} : shrinkCoyoneda.map f = Functo
rToTypes.shrinkMap (coyoneda.map f)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma shrinkCoyoneda_map {X Y : Cᵒᵖ} {f : X ⟶ Y} :
    shrinkCoyoneda.map f = FunctorToTypes.shrinkMap (coyoneda.map f) := rfl

/-- The type `(shrinkCoyoneda.obj X).obj Y` is equivalent to `X.unop ⟶ Y`. -/
/-
**CategoryTheory.shrinkCoyonedaObjObjEquiv** 是 Mathlib 中的一个缩写定义，位于命名空间 `Category
Theory`。
形式化陈述：shrinkCoyonedaObjObjEquiv {X : Cᵒᵖ} {Y : C} : ((shrinkCoyoneda.{w}.obj X).
obj Y) ≃ (X.unop ⟶ Y)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type `(shrinkCoyoneda.obj X).obj Y` is equivalent to `X.unop ⟶ Y`.
-/
noncomputable abbrev shrinkCoyonedaObjObjEquiv {X : Cᵒᵖ} {Y : C} :
    ((shrinkCoyoneda.{w}.obj X).obj Y) ≃ (X.unop ⟶ Y) :=
  shrinkYonedaObjObjEquiv
/-
**CategoryTheory.shrinkCoyoneda_obj_map** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y`。
形式化陈述：shrinkCoyoneda_obj_map {X : Cᵒᵖ} {Y Y' : C} (g : Y ⟶ Y') (f : (shrinkCoyon
eda.obj X).obj Y) : (shrinkCoyoneda.obj _).map g f = shrinkCoyonedaObjObjEquiv.s
ymm (shrinkCoyonedaObjObjEquiv f ≫ g)
参数：g : Y ⟶ Y'；f : (shrinkCoyoneda.obj X).obj Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma shrinkCoyoneda_obj_map {X : Cᵒᵖ} {Y Y' : C} (g : Y ⟶ Y') (f : (shrinkCoyoneda.obj X).obj Y) :
    (shrinkCoyoneda.obj _).map g f =
      shrinkCoyonedaObjObjEquiv.symm (shrinkCoyonedaObjObjEquiv f ≫ g) :=
  rfl
/-
**CategoryTheory.shrinkCoyoneda_obj_map_shrinkCoyonedaObjObjEquiv_symm** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：shrinkCoyoneda_obj_map_shrinkCoyonedaObjObjEquiv_symm {X : Cᵒᵖ} {Y Y' : C}
 (g : Y ⟶ Y') (f : X.unop ⟶ Y) : (shrinkCoyoneda.obj _).map g (shrinkCoyonedaObj
ObjEquiv.symm f) = shrinkCoyonedaObjObjEquiv.symm (f ≫ g)
参数：g : Y ⟶ Y'；f : X.unop ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm`：shrink
Yoneda_map_app_shrinkYonedaObjObjEquiv_symm {X X' : C} {Y : Cᵒᵖ} (f : Y.unop ⟶ X
) (g : X ⟶ X') : (shrinkYoneda.map g).app _ (shrinkYon…
-/
lemma shrinkCoyoneda_obj_map_shrinkCoyonedaObjObjEquiv_symm
    {X : Cᵒᵖ} {Y Y' : C} (g : Y ⟶ Y') (f : X.unop ⟶ Y) :
    (shrinkCoyoneda.obj _).map g (shrinkCoyonedaObjObjEquiv.symm f) =
      shrinkCoyonedaObjObjEquiv.symm (f ≫ g) :=
  shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm f g
/-
**CategoryTheory.shrinkCoyonedaObjObjEquiv_symm_comp** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory`。
形式化陈述：shrinkCoyonedaObjObjEquiv_symm_comp {X Y Y' : C} (g : Y' ⟶ Y) (f : Y ⟶ X) 
: shrinkCoyonedaObjObjEquiv.symm (g ≫ f) = (shrinkCoyoneda.obj _).map f (shrinkC
oyonedaObjObjEquiv.symm g)
参数：g : Y' ⟶ Y；f : Y ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `CategoryTheory.shrinkCoyoneda_obj_map_shrinkCoyonedaObjObjEquiv_symm`：sh
rinkCoyoneda_obj_map_shrinkCoyonedaObjObjEquiv_symm {X : Cᵒᵖ} {Y Y' : C} (g : Y 
⟶ Y') (f : X.unop ⟶ Y) : (shrinkCoyoneda.obj _).map g (shr…
-/
lemma shrinkCoyonedaObjObjEquiv_symm_comp {X Y Y' : C} (g : Y' ⟶ Y) (f : Y ⟶ X) :
    shrinkCoyonedaObjObjEquiv.symm (g ≫ f) =
    (shrinkCoyoneda.obj _).map f (shrinkCoyonedaObjObjEquiv.symm g) :=
  (shrinkCoyoneda_obj_map_shrinkCoyonedaObjObjEquiv_symm f g).symm
/-
**CategoryTheory.shrinkCoyoneda_map_app_shrinkCoyonedaObjObjEquiv_symm** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：shrinkCoyoneda_map_app_shrinkCoyonedaObjObjEquiv_symm {X X' : Cᵒᵖ} {Y : C}
 (f : X.unop ⟶ Y) (g : X ⟶ X') : (shrinkCoyoneda.map g).app _ (shrinkCoyonedaObj
ObjEquiv.symm f) = shrinkCoyonedaObjObjEquiv.symm (g.unop ≫ f)
参数：f : X.unop ⟶ Y；g : X ⟶ X'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm`：shrink
Yoneda_obj_map_shrinkYonedaObjObjEquiv_symm {X : C} {Y Y' : Cᵒᵖ} (g : Y ⟶ Y') (f
 : Y.unop ⟶ X) : (shrinkYoneda.obj _).map g (shrinkYon…
-/
lemma shrinkCoyoneda_map_app_shrinkCoyonedaObjObjEquiv_symm
    {X X' : Cᵒᵖ} {Y : C} (f : X.unop ⟶ Y) (g : X ⟶ X') :
    (shrinkCoyoneda.map g).app _ (shrinkCoyonedaObjObjEquiv.symm f) =
      shrinkCoyonedaObjObjEquiv.symm (g.unop ≫ f) :=
  shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm g f

@[reassoc]
/-
**CategoryTheory.shrinkCoyonedaObjObjEquiv_map_app** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory`。
形式化陈述：shrinkCoyonedaObjObjEquiv_map_app {X X' : Cᵒᵖ} {Y : C} (f : (shrinkCoyoned
a.{w, v, u}.obj X).obj Y) (g : X ⟶ X') : shrinkCoyonedaObjObjEquiv ((shrinkCoyon
eda.map g).app Y f) = g.unop ≫ shrinkCoyonedaObjObjEquiv f
参数：f : (shrinkCoyoneda.{w, v, u}.obj X).obj Y；g : X ⟶ X'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.shrinkYonedaObjObjEquiv_obj_map`：shrinkYonedaObjObjEquiv_
obj_map {X : C} {Y Y' : Cᵒᵖ} (g : Y ⟶ Y') (f : (shrinkYoneda.{w}.obj X).obj Y) :
 shrinkYonedaObjObjEquiv ((shrinkYon…
-/
lemma shrinkCoyonedaObjObjEquiv_map_app
    {X X' : Cᵒᵖ} {Y : C} (f : (shrinkCoyoneda.{w, v, u}.obj X).obj Y) (g : X ⟶ X') :
    shrinkCoyonedaObjObjEquiv ((shrinkCoyoneda.map g).app Y f) =
      g.unop ≫ shrinkCoyonedaObjObjEquiv f :=
  shrinkYonedaObjObjEquiv_obj_map g f

@[reassoc]
/-
**CategoryTheory.shrinkCoyonedaObjObjEquiv_obj_map** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory`。
形式化陈述：shrinkCoyonedaObjObjEquiv_obj_map {X : Cᵒᵖ} {Y Y' : C} (g : Y ⟶ Y') (f : (
shrinkCoyoneda.{w}.obj X).obj Y) : shrinkCoyonedaObjObjEquiv ((shrinkCoyoneda.{w
}.obj X).map g f) = shrinkCoyonedaObjObjEquiv f ≫ g
参数：g : Y ⟶ Y'；f : (shrinkCoyoneda.{w}.obj X).obj Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.shrinkYonedaObjObjEquiv_map_app`：shrinkYonedaObjObjEquiv_
map_app {X X' : C} {Y : Cᵒᵖ} (f : (shrinkYoneda.{w, v, u}.obj X).obj Y) (g : X ⟶
 X') : shrinkYonedaObjObjEquiv ((shr…
-/
lemma shrinkCoyonedaObjObjEquiv_obj_map {X : Cᵒᵖ} {Y Y' : C} (g : Y ⟶ Y')
    (f : (shrinkCoyoneda.{w}.obj X).obj Y) :
    shrinkCoyonedaObjObjEquiv ((shrinkCoyoneda.{w}.obj X).map g f) =
      shrinkCoyonedaObjObjEquiv f ≫ g :=
  shrinkYonedaObjObjEquiv_map_app f g

set_option backward.isDefEq.respectTransparency false in
/-- The type of natural transformations `shrinkCoyoneda.{w}.obj X ⟶ P`
with `X : Cᵒᵖ` and `P : C ⥤ Type w` is equivalent to `P.obj (op X)`. -/
/-
**CategoryTheory.shrinkCoyonedaEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：shrinkCoyonedaEquiv {X : Cᵒᵖ} {P : C ⥤ Type w} : (shrinkCoyoneda.{w}.obj X
 ⟶ P) ≃ P.obj X.unop where toFun τ
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The type of natural transformations `shrinkCoyoneda.{w}.obj X ⟶ P`
with `X : Cᵒᵖ` and `P : C ⥤ Type w` is equivalent to `P.obj (op X)`.
-/
noncomputable def shrinkCoyonedaEquiv {X : Cᵒᵖ} {P : C ⥤ Type w} :
    (shrinkCoyoneda.{w}.obj X ⟶ P) ≃ P.obj X.unop where
  toFun τ := τ.app _ (equivShrink.{w} _ (𝟙 X.unop))
  invFun x :=
    { app Y := ↾fun f ↦ P.map ((equivShrink.{w} _).symm f) x
      naturality Y Z g := by ext; simp [shrinkYoneda] }
  left_inv τ := by
    ext Y f
    obtain ⟨f, rfl⟩ := (equivShrink _).surjective f
    simpa [shrinkYoneda] using ((τ.naturality_apply f) (equivShrink _ (𝟙 X.unop))).symm
  right_inv x := by simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.map_shrinkCoyonedaEquiv** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry`。
形式化陈述：map_shrinkCoyonedaEquiv {X Y : Cᵒᵖ} {P : C ⥤ Type w} (f : shrinkCoyoneda.o
bj X ⟶ P) (g : Y ⟶ X) : P.map g.unop (shrinkCoyonedaEquiv f) = f.app Y.unop (shr
inkCoyonedaObjObjEquiv.symm g.unop)
参数：f : shrinkCoyoneda.obj X ⟶ P；g : Y ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.instSmallOppositeObjFunctorTypeYoneda`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] [CategoryTheory.LocallySmall.{w, v, u} C]
 (X : C),   CategoryTheory.FunctorToTypes.…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_shrinkCoyonedaEquiv {X Y : Cᵒᵖ} {P : C ⥤ Type w} (f : shrinkCoyoneda.obj X ⟶ P)
    (g : Y ⟶ X) : P.map g.unop (shrinkCoyonedaEquiv f) =
      f.app Y.unop (shrinkCoyonedaObjObjEquiv.symm g.unop) := by
  simp [shrinkYonedaObjObjEquiv, shrinkCoyonedaEquiv, shrinkYoneda,
    ← comp_apply, ← NatTrans.naturality]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.shrinkCoyonedaEquiv_shrinkCoyoneda_map** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory`。
形式化陈述：shrinkCoyonedaEquiv_shrinkCoyoneda_map {X Y : Cᵒᵖ} (f : X ⟶ Y) : shrinkCoy
onedaEquiv (shrinkCoyoneda.{w}.map f) = shrinkCoyonedaObjObjEquiv.symm f.unop
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.instSmallOppositeObjFunctorTypeYoneda`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] [CategoryTheory.LocallySmall.{w, v, u} C]
 (X : C),   CategoryTheory.FunctorToTypes.…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma shrinkCoyonedaEquiv_shrinkCoyoneda_map {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    shrinkCoyonedaEquiv (shrinkCoyoneda.{w}.map f) = shrinkCoyonedaObjObjEquiv.symm f.unop := by
  simp [shrinkCoyonedaEquiv, shrinkYoneda, shrinkYonedaObjObjEquiv]

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.shrinkCoyonedaEquiv_comp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory`。
形式化陈述：shrinkCoyonedaEquiv_comp {X : Cᵒᵖ} {P Q : C ⥤ Type w} (α : shrinkCoyoneda.
obj X ⟶ P) (β : P ⟶ Q) : shrinkCoyonedaEquiv (α ≫ β) = β.app _ (shrinkCoyonedaEq
uiv α)
参数：α : shrinkCoyoneda.obj X ⟶ P；β : P ⟶ Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma shrinkCoyonedaEquiv_comp {X : Cᵒᵖ} {P Q : C ⥤ Type w} (α : shrinkCoyoneda.obj X ⟶ P)
    (β : P ⟶ Q) :
    shrinkCoyonedaEquiv (α ≫ β) = β.app _ (shrinkCoyonedaEquiv α) := by
  simp [shrinkCoyonedaEquiv]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.shrinkCoyonedaEquiv_naturality** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory`。
形式化陈述：shrinkCoyonedaEquiv_naturality {X Y : Cᵒᵖ} {P : C ⥤ Type w} (f : shrinkCoy
oneda.obj X ⟶ P) (g : Y ⟶ X) : P.map g.unop (shrinkCoyonedaEquiv f) = shrinkCoyo
nedaEquiv (shrinkCoyoneda.map g ≫ f)
参数：f : shrinkCoyoneda.obj X ⟶ P；g : Y ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instSmallOppositeObjFunctorTypeYoneda`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] [CategoryTheory.LocallySmall.{w, v, u} C]
 (X : C),   CategoryTheory.FunctorToTypes.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatTrans.naturality_apply`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {D : Type u_1} [inst_1 : CategoryTheory.Category.{v_1
, u_1} D]   {FD : outParam (D …
-/
lemma shrinkCoyonedaEquiv_naturality {X Y : Cᵒᵖ} {P : C ⥤ Type w}
    (f : shrinkCoyoneda.obj X ⟶ P) (g : Y ⟶ X) :
    P.map g.unop (shrinkCoyonedaEquiv f) = shrinkCoyonedaEquiv (shrinkCoyoneda.map g ≫ f) := by
  simpa [shrinkCoyonedaEquiv, shrinkYoneda]
    using (f.naturality_apply g.unop ((equivShrink _) (𝟙 _))).symm

@[reassoc]
/-
**CategoryTheory.shrinkCoyonedaEquiv_symm_map** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory`。
形式化陈述：shrinkCoyonedaEquiv_symm_map {X Y : C} (f : X ⟶ Y) {P : C ⥤ Type w} (t : P
.obj X) : shrinkCoyonedaEquiv.symm (P.map f t) = shrinkCoyoneda.map f.op ≫ shrin
kCoyonedaEquiv.symm t
参数：f : X ⟶ Y；t : P.obj X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.shrinkCoyonedaEquiv_naturality`：shrinkCoyonedaEquiv_natur
ality {X Y : Cᵒᵖ} {P : C ⥤ Type w} (f : shrinkCoyoneda.obj X ⟶ P) (g : Y ⟶ X) : 
P.map g.unop (shrinkCoyonedaEquiv f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma shrinkCoyonedaEquiv_symm_map {X Y : C} (f : X ⟶ Y) {P : C ⥤ Type w} (t : P.obj X) :
    shrinkCoyonedaEquiv.symm (P.map f t) =
      shrinkCoyoneda.map f.op ≫ shrinkCoyonedaEquiv.symm t :=
  shrinkCoyonedaEquiv.injective (by
    obtain ⟨t, rfl⟩ := shrinkCoyonedaEquiv.surjective t
    rw [← shrinkCoyonedaEquiv_naturality]
    simp)
/-
**CategoryTheory.shrinkCoyonedaEquiv_symm_app_shrinkCoyonedaObjObjEquiv_symm** 是
 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：shrinkCoyonedaEquiv_symm_app_shrinkCoyonedaObjObjEquiv_symm {X : Cᵒᵖ} {P :
 C ⥤ Type w} (s : P.obj X.unop) {Y : Cᵒᵖ} (f : Y ⟶ X) : (shrinkCoyonedaEquiv.sym
m s).app Y.unop (shrinkCoyonedaObjObjEquiv.symm f.unop) = P.map f.unop s
参数：s : P.obj X.unop；f : Y ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用引理 `CategoryTheory.map_shrinkCoyonedaEquiv`：map_shrinkCoyonedaEquiv {X Y : C
ᵒᵖ} {P : C ⥤ Type w} (f : shrinkCoyoneda.obj X ⟶ P) (g : Y ⟶ X) : P.map g.unop (
shrinkCoyonedaEquiv f) = f.a…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma shrinkCoyonedaEquiv_symm_app_shrinkCoyonedaObjObjEquiv_symm {X : Cᵒᵖ} {P : C ⥤ Type w}
    (s : P.obj X.unop) {Y : Cᵒᵖ} (f : Y ⟶ X) :
    (shrinkCoyonedaEquiv.symm s).app Y.unop (shrinkCoyonedaObjObjEquiv.symm f.unop) =
      P.map f.unop s := by
  obtain ⟨g, rfl⟩ := shrinkCoyonedaEquiv.surjective s
  simp [map_shrinkCoyonedaEquiv]

variable (C) in
/-- The functor `shrinkCoyoneda : Cᵒᵖ ⥤ C ⥤ Type w` for a locally `w`-small category `C`
is fully faithful. -/
/-
**CategoryTheory.fullyFaithfulShrinkCoyoneda** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory`。
形式化陈述：fullyFaithfulShrinkCoyoneda : (shrinkCoyoneda.{w} (C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `shrinkCoyoneda : Cᵒᵖ ⥤ C ⥤ Type w` for a locally `w`-small category
 `C`
is fully faithful.
-/
noncomputable def fullyFaithfulShrinkCoyoneda :
    (shrinkCoyoneda.{w} (C := C)).FullyFaithful where
  preimage f := (shrinkCoyonedaObjObjEquiv (shrinkCoyonedaEquiv f)).op
  map_preimage f := by
    obtain ⟨f, rfl⟩ := shrinkCoyonedaEquiv.symm.surjective f
    cat_disch
  preimage_map f := by
    simp [shrinkCoyonedaEquiv_shrinkCoyoneda_map f]
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (shrinkCoyoneda.{w} (C := C)).Faithful := (fullyFaithfulShrinkCoyoneda C).faithful
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (shrinkCoyoneda.{w} (C := C)).Full := (fullyFaithfulShrinkCoyoneda C).full

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- `shrinkCoyoneda` at the morphism universe level is `coyoneda`. -/
@[simps! hom_app inv_app]
noncomputable
/-
**CategoryTheory.shrinkCoyonedaIsoCoyoneda** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory`。
形式化陈述：shrinkCoyonedaIsoCoyoneda : shrinkCoyoneda.{v} ≅ coyoneda (C
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.locallySmall_of_univLE`：∀ (C : Type u) [inst : CategoryTh
eory.Category.{v, u} C] [UnivLE.{v, w}], CategoryTheory.LocallySmall.{w, v, u} C
-/
def shrinkCoyonedaIsoCoyoneda : shrinkCoyoneda.{v} ≅ coyoneda (C := C) :=
  NatIso.ofComponents
    (fun X ↦ NatIso.ofComponents (fun Y ↦ shrinkCoyonedaObjObjEquiv.toIso)
      (by intros; ext; simp [shrinkYonedaObjObjEquiv_map_app]))
    (by intros; ext; simp [shrinkYonedaObjObjEquiv_obj_map])

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- `shrinkCoyoneda` is compatible with `uliftFunctor`. -/
noncomputable
/-
**CategoryTheory.shrinkCoyonedaUliftFunctorIso** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory`。
形式化陈述：shrinkCoyonedaUliftFunctorIso [LocallySmall.{max w w'} C] : shrinkCoyoneda
.{w} ⋙ (Functor.whiskeringRight Cᵒᵖ _ _).obj uliftFunctor.{w', w} ≅ shrinkCoyone
da
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instLocallySmallOpposite`：∀ (C : Type u) [inst : Category
Theory.Category.{v, u} C] [CategoryTheory.LocallySmall.{w, v, u} C],   CategoryT
heory.LocallySmall.{w, v, u} …
-/
def shrinkCoyonedaUliftFunctorIso [LocallySmall.{max w w'} C] :
    shrinkCoyoneda.{w} ⋙ (Functor.whiskeringRight Cᵒᵖ _ _).obj uliftFunctor.{w', w} ≅
      shrinkCoyoneda :=
  NatIso.ofComponents
    (fun X ↦ FunctorToTypes.shrinkCompUliftFunctorIso.{w, v} (coyoneda.obj X))
    fun _ ↦ by ext; simp [shrinkYoneda]

/-- `uliftCoyoneda` identifies to `shrinkCoyoneda`. -/
/-
**CategoryTheory.uliftYonedaIsoShrinkCoyoneda** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory`。
形式化陈述：uliftYonedaIsoShrinkCoyoneda : uliftCoyoneda.{w'} (C
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`uliftCoyoneda` identifies to `shrinkCoyoneda`.
-/
noncomputable def uliftYonedaIsoShrinkCoyoneda :
    uliftCoyoneda.{w'} (C := C) ≅ shrinkCoyoneda.{max w' v} :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents
    (fun Y ↦ (Equiv.ulift.trans shrinkCoyonedaObjObjEquiv.symm).toIso) (fun f ↦ by
      ext
      exact (shrinkCoyoneda_obj_map_shrinkCoyonedaObjObjEquiv_symm _ _).symm)) (fun g ↦ by
      ext
      exact (shrinkCoyoneda_map_app_shrinkCoyonedaObjObjEquiv_symm _ _).symm)

set_option backward.defeqAttrib.useBackward true in
/-- The functor `shrinkCoyoneda.{w}` followed by the evaluation
at `Y : C` and `uliftFunctor.{v}` identifies to `yoneda.obj Y` followed
by `uliftFunctor.{w}`. -/
/-
**CategoryTheory.shrinkCoyonedaCompEvaluationCompUliftFunctorIsoUliftFunctor** 是
 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：shrinkCoyonedaCompEvaluationCompUliftFunctorIsoUliftFunctor (Y : C) : shri
nkCoyoneda.{w} ⋙ (evaluation C _).obj Y ⋙ uliftFunctor.{v} ≅ yoneda.obj Y ⋙ ulif
tFunctor.{w}
参数：Y : C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The functor `shrinkCoyoneda.{w}` followed by the evaluation
at `Y : C` and `uliftFunctor.{v}` identifies to `yoneda.obj Y` followed
by `uliftFunctor.{w}`.
-/
noncomputable def shrinkCoyonedaCompEvaluationCompUliftFunctorIsoUliftFunctor (Y : C) :
    shrinkCoyoneda.{w} ⋙ (evaluation C _).obj Y ⋙ uliftFunctor.{v} ≅
      yoneda.obj Y ⋙ uliftFunctor.{w} :=
  NatIso.ofComponents (fun X ↦ (Equiv.ulift.trans
    (shrinkCoyonedaObjObjEquiv.trans Equiv.ulift.symm)).toIso) (fun f ↦ by
      ext ⟨g⟩
      obtain ⟨g, rfl⟩ := shrinkCoyonedaObjObjEquiv.symm.surjective g
      simp [shrinkYoneda, shrinkYonedaObjObjEquiv])

/-- `shrinkCoyoneda.obj X` is corepresented by `X`. -/
@[simps]
noncomputable
/-
**CategoryTheory.shrinkCoyonedaCorepresentableBy** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory`。
形式化陈述：shrinkCoyonedaCorepresentableBy (X : Cᵒᵖ) : (shrinkCoyoneda.{w}.obj X).Cor
epresentableBy X.unop where homEquiv
参数：X : Cᵒᵖ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
def shrinkCoyonedaCorepresentableBy (X : Cᵒᵖ) :
    (shrinkCoyoneda.{w}.obj X).CorepresentableBy X.unop where
  homEquiv := shrinkCoyonedaObjObjEquiv.symm
  homEquiv_comp f g := shrinkCoyonedaObjObjEquiv_symm_comp g f
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : Cᵒᵖ) : (shrinkCoyoneda.{w}.obj X).IsCorepresentable :=
  (shrinkCoyonedaCorepresentableBy X).isCorepresentable

end Coyoneda

end CategoryTheory

