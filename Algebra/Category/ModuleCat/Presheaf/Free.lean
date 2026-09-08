/-
Copyright (c) 2024 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Joel Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions

/-!
# The free presheaf of modules on a presheaf of sets

In this file, given a presheaf of rings `R` on a category `C`,
we construct the functor
`PresheafOfModules.free : (Cᵒᵖ ⥤ Type u) ⥤ PresheafOfModules.{u} R`
which sends a presheaf of types to the corresponding presheaf of free modules.
`PresheafOfModules.freeAdjunction` shows that this functor is the left
adjoint to the forget functor.

## Notes

This contribution was created as part of the AIM workshop
"Formalizing algebraic geometry" in June 2024.

-/

@[expose] public section

universe u v₁ u₁

open CategoryTheory

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] (R : Cᵒᵖ ⥤ RingCat.{u})

set_option backward.isDefEq.respectTransparency.types false in
variable {R} in
/-- Given a presheaf of types `F : Cᵒᵖ ⥤ Type u`, this is the presheaf
of modules over `R` which sends `X : Cᵒᵖ` to the free `R.obj X`-module on `F.obj X`. -/
@[simps]
/-
**PresheafOfModules.freeObj** 是 Mathlib 中的一个定义，位于命名空间 `PresheafOfModules`。
形式化陈述：freeObj (F : Cᵒᵖ ⥤ Type u) : PresheafOfModules.{u} R where obj X
参数：F : Cᵒᵖ ⥤ Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a presheaf of types `F : Cᵒᵖ ⥤ Type u`, this is the presheaf
of modules over `R` which sends `X : Cᵒᵖ` to the free `R.obj X`-module on `F.obj
 X`.
-/
noncomputable def freeObj (F : Cᵒᵖ ⥤ Type u) : PresheafOfModules.{u} R where
  obj X := (ModuleCat.free (R.obj X)).obj (F.obj X)
  map {X Y} f := ModuleCat.freeDesc (↾fun x ↦ ModuleCat.freeMk (F.map f x))
  map_id := by aesop

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The free presheaf of modules functor `(Cᵒᵖ ⥤ Type u) ⥤ PresheafOfModules.{u} R`. -/
@[simps]
/-
**PresheafOfModules.free** 是 Mathlib 中的一个定义，位于命名空间 `PresheafOfModules`。
形式化陈述：free : (Cᵒᵖ ⥤ Type u) ⥤ PresheafOfModules.{u} R where obj
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The free presheaf of modules functor `(Cᵒᵖ ⥤ Type u) ⥤ PresheafOfModules.{u} R`.
-/
noncomputable def free : (Cᵒᵖ ⥤ Type u) ⥤ PresheafOfModules.{u} R where
  obj := freeObj
  map {F G} φ := { app := fun X ↦ (ModuleCat.free (R.obj X)).map (φ.app X) }

section

variable {R}

variable {F : Cᵒᵖ ⥤ Type u} {G : PresheafOfModules.{u} R}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The morphism of presheaves of modules `freeObj F ⟶ G` corresponding to
a morphism `F ⟶ G.presheaf ⋙ forget _` of presheaves of types. -/
@[simps]
/-
**PresheafOfModules.freeObjDesc** 是 Mathlib 中的一个定义，位于命名空间 `PresheafOfModules`。
形式化陈述：freeObjDesc (φ : F ⟶ G.presheaf ⋙ forget _) : freeObj F ⟶ G where app X
参数：φ : F ⟶ G.presheaf ⋙ forget _。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism of presheaves of modules `freeObj F ⟶ G` corresponding to
a morphism `F ⟶ G.presheaf ⋙ forget _` of presheaves of types.
-/
noncomputable def freeObjDesc (φ : F ⟶ G.presheaf ⋙ forget _) : freeObj F ⟶ G where
  app X := ModuleCat.freeDesc (φ.app X)
  naturality {X Y} f := by
    dsimp
    ext x
    simpa using! NatTrans.naturality_apply φ f x

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable (F R) in
/-- The unit of `PresheafOfModules.freeAdjunction`. -/
@[simps]
/-
**PresheafOfModules.freeAdjunctionUnit** 是 Mathlib 中的一个定义，位于命名空间 `PresheafOfModu
les`。
形式化陈述：freeAdjunctionUnit : F ⟶ (freeObj (R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unit of `PresheafOfModules.freeAdjunction`.
-/
noncomputable def freeAdjunctionUnit : F ⟶ (freeObj (R := R) F).presheaf ⋙ forget _ where
  app X := ↾fun x ↦ ModuleCat.freeMk x
  naturality X Y f := by ext; simp [presheaf]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The bijection `(freeObj F ⟶ G) ≃ (F ⟶ G.presheaf ⋙ forget _)` when
`F` is a presheaf of types and `G` a presheaf of modules. -/
/-
**PresheafOfModules.freeHomEquiv** 是 Mathlib 中的一个定义，位于命名空间 `PresheafOfModules`。
形式化陈述：freeHomEquiv : (freeObj F ⟶ G) ≃ (F ⟶ G.presheaf ⋙ forget _) where toFun ψ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bijection `(freeObj F ⟶ G) ≃ (F ⟶ G.presheaf ⋙ forget _)` when
`F` is a presheaf of types and `G` a presheaf of modules.
-/
noncomputable def freeHomEquiv : (freeObj F ⟶ G) ≃ (F ⟶ G.presheaf ⋙ forget _) where
  toFun ψ := freeAdjunctionUnit R F ≫ Functor.whiskerRight ((toPresheaf _).map ψ) _
  invFun φ := freeObjDesc φ
  left_inv ψ := by ext1 X; dsimp; ext x; simp [toPresheaf]
  right_inv φ := by ext; simp [toPresheaf]
/-
**PresheafOfModules.free_hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `PresheafOfModules`。
形式化陈述：free_hom_ext {ψ ψ' : freeObj F ⟶ G} (h : freeAdjunctionUnit R F ≫ Functor.
whiskerRight ((toPresheaf _).map ψ) _ = freeAdjunctionUnit R F ≫ Functor.whisker
Right ((toPresheaf _).map ψ') _) : ψ = ψ'
参数：h : freeAdjunctionUnit R F ≫ Functor.whiskerRight ((toPresheaf _).map ψ) _ = 
freeAdjunctionUnit R F ≫ Functor.whiskerRight ((toPresheaf _).map ψ') _。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
lemma free_hom_ext {ψ ψ' : freeObj F ⟶ G}
    (h : freeAdjunctionUnit R F ≫ Functor.whiskerRight ((toPresheaf _).map ψ) _ =
      freeAdjunctionUnit R F ≫ Functor.whiskerRight ((toPresheaf _).map ψ') _) : ψ = ψ' :=
  freeHomEquiv.injective h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable (R) in
/-- The free presheaf of modules functor is left adjoint to the forget functor
`PresheafOfModules.{u} R ⥤ Cᵒᵖ ⥤ Type u`. -/
/-
**PresheafOfModules.freeAdjunction** 是 Mathlib 中的一个定义，位于命名空间 `PresheafOfModules`
。
形式化陈述：freeAdjunction : free.{u} R ⊣ (toPresheaf R ⋙ (Functor.whiskeringRight _ _
 _).obj (forget Ab))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The free presheaf of modules functor is left adjoint to the forget functor
`PresheafOfModules.{u} R ⥤ Cᵒᵖ ⥤ Type u`.
-/
noncomputable def freeAdjunction :
    free.{u} R ⊣ (toPresheaf R ⋙ (Functor.whiskeringRight _ _ _).obj (forget Ab)) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ ↦ freeHomEquiv
      homEquiv_naturality_left_symm := fun {F₁ F₂ G} f g ↦
        free_hom_ext (by ext; simp [freeHomEquiv, toPresheaf])
      homEquiv_naturality_right := fun {F G₁ G₂} f g ↦ rfl }

set_option backward.isDefEq.respectTransparency.types false in
variable (F G) in
@[simp]
/-
**PresheafOfModules.freeAdjunction_homEquiv** 是 Mathlib 中的一个引理，位于命名空间 `PresheafO
fModules`。
形式化陈述：freeAdjunction_homEquiv : (freeAdjunction R).homEquiv F G = freeHomEquiv
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Adjunction.mkOfHomEquiv_homEquiv`：mkOfHomEquiv_homEquiv (
adj : CoreHomEquiv F G) : (mkOfHomEquiv adj).homEquiv = adj.homEquiv
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma freeAdjunction_homEquiv : (freeAdjunction R).homEquiv F G = freeHomEquiv := by
  simp [freeAdjunction, Adjunction.mkOfHomEquiv_homEquiv]

set_option backward.isDefEq.respectTransparency.types false in
variable (R F) in
@[simp]
/-
**PresheafOfModules.freeAdjunction_unit_app** 是 Mathlib 中的一个引理，位于命名空间 `PresheafO
fModules`。
形式化陈述：freeAdjunction_unit_app : (freeAdjunction R).unit.app F = freeAdjunctionUn
it R F
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma freeAdjunction_unit_app :
    (freeAdjunction R).unit.app F = freeAdjunctionUnit R F := rfl

end

end PresheafOfModules

