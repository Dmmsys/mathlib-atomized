/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory

/-!
# Functor categories have chosen finite products

If `C` is a category with chosen finite products, then so is `J ⥤ C`.

-/

@[expose] public section

namespace CategoryTheory

open Limits MonoidalCategory Category CartesianMonoidalCategory

universe v
variable {J C D E : Type*} [Category* J] [Category* C] [Category* D] [Category* E]
  [CartesianMonoidalCategory C] [CartesianMonoidalCategory E]

namespace Functor

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Functor.cartesianMonoidalCategory** 是 Mathlib 中的一个实例，位于命名空间 `Ca
tegoryTheory.Functor`。
形式化陈述：cartesianMonoidalCategory : CartesianMonoidalCategory (J ⥤ C) where fst X 
Y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance cartesianMonoidalCategory : CartesianMonoidalCategory (J ⥤ C) where
  fst X Y := { app _ := CartesianMonoidalCategory.fst _ _ }
  snd X Y := { app _ := CartesianMonoidalCategory.snd _ _ }
  tensorProductIsBinaryProduct X Y :=
    evaluationJointlyReflectsLimits _ (fun j =>
      (IsLimit.postcomposeHomEquiv
        (mapPairIso (by exact Iso.refl _) (by exact Iso.refl _)) _).1
        (IsLimit.ofIsoLimit
          (tensorProductIsBinaryProduct (X := X.obj j) (Y := Y.obj j))
          (Cone.ext (Iso.refl _) (by rintro ⟨_ | _⟩; all_goals cat_disch))))
  isTerminalTensorUnit :=
    evaluationJointlyReflectsLimits _
      fun _ ↦ isLimitChangeEmptyCone _ isTerminalTensorUnit _ (.refl _)
  fst_def X Y := by
    ext
    simp only [Monoidal.tensorObj_obj, fst_def, asEmptyCone_pt, NatTrans.comp_app,
      Monoidal.tensorUnit_obj, Monoidal.whiskerLeft_app, Monoidal.rightUnitor_hom_app,
      Iso.cancel_iso_hom_right]
    congr
    subsingleton
  snd_def X Y := by
    ext
    simp only [Monoidal.tensorObj_obj, snd_def, asEmptyCone_pt, NatTrans.comp_app,
      Monoidal.tensorUnit_obj, Monoidal.whiskerRight_app, Monoidal.leftUnitor_hom_app,
      Iso.cancel_iso_hom_right]
    congr
    subsingleton

@[deprecated (since := "2026-03-07")] alias chosenTerminal := MonoidalCategory.tensorUnit
@[deprecated (since := "2026-03-07")] alias chosenTerminalIsTerminal :=
  CartesianMonoidalCategory.isTerminalTensorUnit

@[deprecated (since := "2026-03-07")] alias chosenProd := MonoidalCategory.tensorObj
@[deprecated (since := "2026-03-07")] alias chosenProd.fst := CartesianMonoidalCategory.fst
@[deprecated (since := "2026-03-07")] alias chosenProd.snd := CartesianMonoidalCategory.snd
@[deprecated (since := "2026-03-07")] alias chosenProd.isLimit :=
  CartesianMonoidalCategory.tensorProductIsBinaryProduct

namespace Monoidal

open CartesianMonoidalCategory

@[simp]
/-
**CategoryTheory.Functor.Monoidal.tensorObj_obj** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Functor.Monoidal`。
形式化陈述：tensorObj_obj (F₁ F₂ : J ⥤ C) (j : J) : (F₁ otimes F₂).obj j = (F₁.obj j) 
otimes (F₂.obj j)
参数：F₁ F₂ : J ⥤ C；j : J。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensorObj_obj (F₁ F₂ : J ⥤ C) (j : J) : (F₁ ⊗ F₂).obj j = (F₁.obj j) ⊗ (F₂.obj j) := rfl

@[simp]
/-
**CategoryTheory.Functor.Monoidal.tensorObj_map** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Functor.Monoidal`。
形式化陈述：tensorObj_map (F₁ F₂ : J ⥤ C) {j j' : J} (f : j ⟶ j') : (F₁ otimes F₂).map
 f = (F₁.map f) otimesₘ (F₂.map f)
参数：F₁ F₂ : J ⥤ C；f : j ⟶ j'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensorObj_map (F₁ F₂ : J ⥤ C) {j j' : J} (f : j ⟶ j') :
    (F₁ ⊗ F₂).map f = (F₁.map f) ⊗ₘ (F₂.map f) := rfl

@[simp]
/-
**CategoryTheory.Functor.Monoidal.fst_app** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Functor.Monoidal`。
形式化陈述：fst_app (F₁ F₂ : J ⥤ C) (j : J) : (fst F₁ F₂).app j = fst (F₁.obj j) (F₂.o
bj j)
参数：F₁ F₂ : J ⥤ C；j : J。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma fst_app (F₁ F₂ : J ⥤ C) (j : J) : (fst F₁ F₂).app j = fst (F₁.obj j) (F₂.obj j) := rfl

@[simp]
/-
**CategoryTheory.Functor.Monoidal.snd_app** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Functor.Monoidal`。
形式化陈述：snd_app (F₁ F₂ : J ⥤ C) (j : J) : (snd F₁ F₂).app j = snd (F₁.obj j) (F₂.o
bj j)
参数：F₁ F₂ : J ⥤ C；j : J。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma snd_app (F₁ F₂ : J ⥤ C) (j : J) : (snd F₁ F₂).app j = snd (F₁.obj j) (F₂.obj j) := rfl

@[simp]
/-
**CategoryTheory.Functor.Monoidal.leftUnitor_hom_app** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Functor.Monoidal`。
形式化陈述：leftUnitor_hom_app (F : J ⥤ C) (j : J) : (fun_ F).hom.app j = (fun_ (F.obj
 j)).hom
参数：F : J ⥤ C；j : J。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma leftUnitor_hom_app (F : J ⥤ C) (j : J) :
    (λ_ F).hom.app j = (λ_ (F.obj j)).hom := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Functor.Monoidal.leftUnitor_inv_app** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Functor.Monoidal`。
形式化陈述：leftUnitor_inv_app (F : J ⥤ C) (j : J) : (fun_ F).inv.app j = (fun_ (F.obj
 j)).inv
参数：F : J ⥤ C；j : J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用引理 `CategoryTheory.Functor.Monoidal.leftUnitor_hom_app`：leftUnitor_hom_app (
F : J ⥤ C) (j : J) : (fun_ F).hom.app j = (fun_ (F.obj j)).hom
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
-/
lemma leftUnitor_inv_app (F : J ⥤ C) (j : J) :
    (λ_ F).inv.app j = (λ_ (F.obj j)).inv := by
  rw [← cancel_mono ((λ_ (F.obj j)).hom), Iso.inv_hom_id, ← leftUnitor_hom_app,
    Iso.inv_hom_id_app]

@[simp]
/-
**CategoryTheory.Functor.Monoidal.rightUnitor_hom_app** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Functor.Monoidal`。
形式化陈述：rightUnitor_hom_app (F : J ⥤ C) (j : J) : (ρ_ F).hom.app j = (ρ_ (F.obj j)
).hom
参数：F : J ⥤ C；j : J。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma rightUnitor_hom_app (F : J ⥤ C) (j : J) :
    (ρ_ F).hom.app j = (ρ_ (F.obj j)).hom := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Functor.Monoidal.rightUnitor_inv_app** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Functor.Monoidal`。
形式化陈述：rightUnitor_inv_app (F : J ⥤ C) (j : J) : (ρ_ F).inv.app j = (ρ_ (F.obj j)
).inv
参数：F : J ⥤ C；j : J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用引理 `CategoryTheory.Functor.Monoidal.rightUnitor_hom_app`：rightUnitor_hom_app
 (F : J ⥤ C) (j : J) : (ρ_ F).hom.app j = (ρ_ (F.obj j)).hom
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
-/
lemma rightUnitor_inv_app (F : J ⥤ C) (j : J) :
    (ρ_ F).inv.app j = (ρ_ (F.obj j)).inv := by
  rw [← cancel_mono ((ρ_ (F.obj j)).hom), Iso.inv_hom_id, ← rightUnitor_hom_app,
    Iso.inv_hom_id_app]
/-
**CategoryTheory.Functor.Monoidal.tensorHom_app_fst** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Functor.Monoidal`。
形式化陈述：tensorHom_app_fst {F₁ F₁' F₂ F₂' : J ⥤ C} (f : F₁ ⟶ F₁') (g : F₂ ⟶ F₂') (j
 : J) : (f otimesₘ g).app j ≫ fst _ _ = fst _ _ ≫ f.app j
参数：f : F₁ ⟶ F₁'；g : F₂ ⟶ F₂'；j : J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.tensorHom_fst`：tensorHom_fst {X
₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) : (f otimesₘ g) ≫ fst _ _ = fst _ _ 
≫ f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma tensorHom_app_fst {F₁ F₁' F₂ F₂' : J ⥤ C} (f : F₁ ⟶ F₁') (g : F₂ ⟶ F₂') (j : J) :
    (f ⊗ₘ g).app j ≫ fst _ _ = fst _ _ ≫ f.app j := by
  simp
/-
**CategoryTheory.Functor.Monoidal.tensorHom_app_snd** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Functor.Monoidal`。
形式化陈述：tensorHom_app_snd {F₁ F₁' F₂ F₂' : J ⥤ C} (f : F₁ ⟶ F₁') (g : F₂ ⟶ F₂') (j
 : J) : (f otimesₘ g).app j ≫ snd _ _ = snd _ _ ≫ g.app j
参数：f : F₁ ⟶ F₁'；g : F₂ ⟶ F₂'；j : J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.tensorHom_snd`：tensorHom_snd {X
₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) : (f otimesₘ g) ≫ snd _ _ = snd _ _ 
≫ g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma tensorHom_app_snd {F₁ F₁' F₂ F₂' : J ⥤ C} (f : F₁ ⟶ F₁') (g : F₂ ⟶ F₂') (j : J) :
    (f ⊗ₘ g).app j ≫ snd _ _ = snd _ _ ≫ g.app j := by
  simp
/-
**CategoryTheory.Functor.Monoidal.whiskerLeft_app_fst** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Functor.Monoidal`。
形式化陈述：whiskerLeft_app_fst (F₁ : J ⥤ C) {F₂ F₂' : J ⥤ C} (g : F₂ ⟶ F₂') (j : J) :
 (F₁ ◁ g).app j ≫ fst _ _ = fst _ _
参数：F₁ : J ⥤ C；g : F₂ ⟶ F₂'；j : J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.whiskerLeft_fst`：whiskerLeft_fs
t (X : C) {Y Z : C} (f : Y ⟶ Z) : X ◁ f ≫ fst _ _ = fst _ _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma whiskerLeft_app_fst (F₁ : J ⥤ C) {F₂ F₂' : J ⥤ C} (g : F₂ ⟶ F₂') (j : J) :
    (F₁ ◁ g).app j ≫ fst _ _ = fst _ _ := by
  simp
/-
**CategoryTheory.Functor.Monoidal.whiskerLeft_app_snd** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Functor.Monoidal`。
形式化陈述：whiskerLeft_app_snd (F₁ : J ⥤ C) {F₂ F₂' : J ⥤ C} (g : F₂ ⟶ F₂') (j : J) :
 (F₁ ◁ g).app j ≫ snd _ _ = snd _ _ ≫ g.app j
参数：F₁ : J ⥤ C；g : F₂ ⟶ F₂'；j : J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.whiskerLeft_snd`：whiskerLeft_sn
d (X : C) {Y Z : C} (f : Y ⟶ Z) : X ◁ f ≫ snd _ _ = snd _ _ ≫ f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma whiskerLeft_app_snd (F₁ : J ⥤ C) {F₂ F₂' : J ⥤ C} (g : F₂ ⟶ F₂') (j : J) :
    (F₁ ◁ g).app j ≫ snd _ _ = snd _ _ ≫ g.app j := by
  simp
/-
**CategoryTheory.Functor.Monoidal.whiskerRight_app_fst** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Functor.Monoidal`。
形式化陈述：whiskerRight_app_fst {F₁ F₁' : J ⥤ C} (f : F₁ ⟶ F₁') (F₂ : J ⥤ C) (j : J) 
: (f ▷ F₂).app j ≫ fst _ _ = fst _ _ ≫ f.app j
参数：f : F₁ ⟶ F₁'；F₂ : J ⥤ C；j : J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.whiskerRight_fst`：whiskerRight_
fst {X Y : C} (f : X ⟶ Y) (Z : C) : f ▷ Z ≫ fst _ _ = fst _ _ ≫ f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma whiskerRight_app_fst {F₁ F₁' : J ⥤ C} (f : F₁ ⟶ F₁') (F₂ : J ⥤ C) (j : J) :
    (f ▷ F₂).app j ≫ fst _ _ = fst _ _ ≫ f.app j := by
  simp
/-
**CategoryTheory.Functor.Monoidal.whiskerRight_app_snd** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Functor.Monoidal`。
形式化陈述：whiskerRight_app_snd {F₁ F₁' : J ⥤ C} (f : F₁ ⟶ F₁') (F₂ : J ⥤ C) (j : J) 
: (f ▷ F₂).app j ≫ snd _ _ = snd _ _
参数：f : F₁ ⟶ F₁'；F₂ : J ⥤ C；j : J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.whiskerRight_snd`：whiskerRight_
snd {X Y : C} (f : X ⟶ Y) (Z : C) : f ▷ Z ≫ snd _ _ = snd _ _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma whiskerRight_app_snd {F₁ F₁' : J ⥤ C} (f : F₁ ⟶ F₁') (F₂ : J ⥤ C) (j : J) :
    (f ▷ F₂).app j ≫ snd _ _ = snd _ _ := by
  simp

@[simp]
/-
**CategoryTheory.Functor.Monoidal.associator_hom_app** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Functor.Monoidal`。
形式化陈述：associator_hom_app (F₁ F₂ F₃ : J ⥤ C) (j : J) : (α_ F₁ F₂ F₃).hom.app j = 
(α_ _ _ _).hom
参数：F₁ F₂ F₃ : J ⥤ C；j : J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma associator_hom_app (F₁ F₂ F₃ : J ⥤ C) (j : J) :
    (α_ F₁ F₂ F₃).hom.app j = (α_ _ _ _).hom := by
  simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Functor.Monoidal.associator_inv_app** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Functor.Monoidal`。
形式化陈述：associator_inv_app (F₁ F₂ F₃ : J ⥤ C) (j : J) : (α_ F₁ F₂ F₃).inv.app j = 
(α_ _ _ _).inv
参数：F₁ F₂ F₃ : J ⥤ C；j : J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用引理 `CategoryTheory.Functor.Monoidal.associator_hom_app`：associator_hom_app (
F₁ F₂ F₃ : J ⥤ C) (j : J) : (α_ F₁ F₂ F₃).hom.app j = (α_ _ _ _).hom
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
-/
lemma associator_inv_app (F₁ F₂ F₃ : J ⥤ C) (j : J) :
    (α_ F₁ F₂ F₃).inv.app j = (α_ _ _ _).inv := by
  rw [← cancel_mono ((α_ _ _ _).hom), Iso.inv_hom_id, ← associator_hom_app, Iso.inv_hom_id_app]

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Functor.Monoidal.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Fun
ctor.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {K : Type*} [Category* K] [HasColimitsOfShape K C]
    [∀ X : C, PreservesColimitsOfShape K (tensorLeft X)] {F : J ⥤ C} :
    PreservesColimitsOfShape K (tensorLeft F) := by
  apply preservesColimitsOfShape_of_evaluation
  intro k
  have : tensorLeft F ⋙ (evaluation J C).obj k ≅ (evaluation J C).obj k ⋙ tensorLeft (F.obj k) :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _)
  exact preservesColimitsOfShape_of_natIso this.symm

set_option backward.defeqAttrib.useBackward true in
/-- A finite-products-preserving functor distributes over the tensor product of functors. -/
@[simps!]
/-
**CategoryTheory.Functor.Monoidal.tensorObjComp** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Functor.Monoidal`。
形式化陈述：tensorObjComp (F G : D ⥤ C) (H : C ⥤ E) [PreservesFiniteProducts H] : (F o
times G) ⋙ H ≅ (F ⋙ H) otimes (G ⋙ H)
参数：F G : D ⥤ C；H : C ⥤ E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A finite-products-preserving functor distributes over the tensor product of func
tors.
-/
noncomputable def tensorObjComp (F G : D ⥤ C) (H : C ⥤ E) [PreservesFiniteProducts H] :
    (F ⊗ G) ⋙ H ≅ (F ⋙ H) ⊗ (G ⋙ H) :=
  NatIso.ofComponents (fun X ↦ prodComparisonIso H (F.obj X) (G.obj X)) fun {X Y} f ↦ by
    dsimp; ext <;> simp [← Functor.map_comp]

/-- A tensor product of representable functors is representable. -/
@[simps]
/-
**CategoryTheory.Functor.Monoidal.RepresentableBy.tensorObj** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.Functor.Monoidal.RepresentableBy`。
形式化陈述：{C : Type u_2} →   [inst : CategoryTheory.Category.{v_2, u_2} C] →     [in
st_1 : CategoryTheory.CartesianMonoidalCategory C] →       {F G : CategoryTheory
.Functor Cᵒᵖ (Type v)} →         {X Y : C} →           F.RepresentableBy X →    
         G.RepresentableBy Y →               (CategoryTheory.MonoidalCategoryStr
uct.tensorObj F G).RepresentableBy                 (CategoryTheory.MonoidalCateg
oryStruct.tensorObj X Y)
参数：Type v；CategoryTheory.MonoidalCategoryStruct.tensorObj F G；CategoryTheory.Mon
oidalCategoryStruct.tensorObj X Y。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
A tensor product of representable functors is representable.
-/
protected def RepresentableBy.tensorObj {F : Cᵒᵖ ⥤ Type v} {G : Cᵒᵖ ⥤ Type v} {X Y : C}
    (h₁ : F.RepresentableBy X) (h₂ : G.RepresentableBy Y) : (F ⊗ G).RepresentableBy (X ⊗ Y) where
  homEquiv {I} := homEquivToProd.trans (h₁.homEquiv.prodCongr h₂.homEquiv)
  homEquiv_comp {I W} f g := by
    refine Prod.ext ?_ ?_
    · change h₁.homEquiv ((f ≫ g) ≫ fst X Y) = F.map f.op (h₁.homEquiv (g ≫ fst X Y))
      simp [h₁.homEquiv_comp]
    · change h₂.homEquiv ((f ≫ g) ≫ snd X Y) = G.map f.op (h₂.homEquiv (g ≫ snd X Y))
      simp [h₂.homEquiv_comp]

end Monoidal

end Functor

end CategoryTheory

