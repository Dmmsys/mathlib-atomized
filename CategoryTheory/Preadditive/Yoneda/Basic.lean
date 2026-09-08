/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Preadditive.Opposite
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.Algebra.Category.Grp.Yoneda

/-!
# The Yoneda embedding for preadditive categories

The Yoneda embedding for preadditive categories sends an object `Y` to the presheaf sending an
object `X` to the group of morphisms `X ⟶ Y`. At each point, we get an additional `End Y`-module
structure.

We also show that this presheaf is additive and that it is compatible with the normal Yoneda
embedding in the expected way and deduce that the preadditive Yoneda embedding is fully faithful.

## TODO
* The Yoneda embedding is additive itself

-/

@[expose] public section


universe v u u₁

open CategoryTheory.Preadditive Opposite CategoryTheory.Limits CategoryTheory.Functor

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The Yoneda embedding for preadditive categories sends an object `Y` to the presheaf sending an
object `X` to the `End Y`-module of morphisms `X ⟶ Y`.
-/
@[simps]
/-
**CategoryTheory.preadditiveYonedaObj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`
。
形式化陈述：preadditiveYonedaObj (Y : C) : Cᵒᵖ ⥤ ModuleCat.{v} (End Y) where obj X
参数：Y : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Yoneda embedding for preadditive categories sends an object `Y` to the presh
eaf sending an
object `X` to the `End Y`-module of morphisms `X ⟶ Y`.
-/
def preadditiveYonedaObj (Y : C) : Cᵒᵖ ⥤ ModuleCat.{v} (End Y) where
  obj X := ModuleCat.of _ (X.unop ⟶ Y)
  map f := ModuleCat.ofHom
    { toFun := fun g => f.unop ≫ g
      map_add' := fun _ _ => comp_add _ _ _ _ _ _
      map_smul' := fun _ _ => Eq.symm <| Category.assoc _ _ _ }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The Yoneda embedding for preadditive categories sends an object `Y` to the presheaf sending an
object `X` to the group of morphisms `X ⟶ Y`. At each point, we get an additional `End Y`-module
structure, see `preadditiveYonedaObj`.
-/
@[simps obj]
/-
**CategoryTheory.preadditiveYoneda** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：preadditiveYoneda : C ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{v} where obj Y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Yoneda embedding for preadditive categories sends an object `Y` to the presh
eaf sending an
object `X` to the group of morphisms `X ⟶ Y`. At each point, we get an additiona
l `End Y`-module
structure, see `preadditiveYonedaObj`.
-/
def preadditiveYoneda : C ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{v} where
  obj Y := preadditiveYonedaObj Y ⋙ forget₂ _ _
  map f :=
    { app := fun _ => AddCommGrpCat.ofHom
        { toFun := fun g => g ≫ f
          map_zero' := Limits.zero_comp
          map_add' := fun _ _ => add_comp _ _ _ _ _ _ }
      naturality := fun _ _ _ => AddCommGrpCat.ext fun _ => Category.assoc _ _ _ }

/-- The Yoneda embedding for preadditive categories sends an object `X` to the copresheaf sending an
object `Y` to the `End X`-module of morphisms `X ⟶ Y`.
-/
@[simps]
/-
**CategoryTheory.preadditiveCoyonedaObj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y`。
形式化陈述：preadditiveCoyonedaObj (X : C) : C ⥤ ModuleCat.{v} (End X)ᵐᵒᵖ where obj Y
参数：X : C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…

--- 原说明 ---
The Yoneda embedding for preadditive categories sends an object `X` to the copre
sheaf sending an
object `Y` to the `End X`-module of morphisms `X ⟶ Y`.
-/
def preadditiveCoyonedaObj (X : C) : C ⥤ ModuleCat.{v} (End X)ᵐᵒᵖ where
  obj Y := ModuleCat.of _ (X ⟶ Y)
  map f := ModuleCat.ofHom
    { toFun := fun g => g ≫ f
      map_add' := fun _ _ => add_comp _ _ _ _ _ _
      map_smul' := fun _ _ => Category.assoc _ _ _ }

set_option backward.isDefEq.respectTransparency.types false in
/-- The Yoneda embedding for preadditive categories sends an object `X` to the copresheaf sending an
object `Y` to the group of morphisms `X ⟶ Y`. At each point, we get an additional `End X`-module
structure, see `preadditiveCoyonedaObj`.
-/
@[simps obj]
/-
**CategoryTheory.preadditiveCoyoneda** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：preadditiveCoyoneda : Cᵒᵖ ⥤ C ⥤ AddCommGrpCat.{v} where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Yoneda embedding for preadditive categories sends an object `X` to the copre
sheaf sending an
object `Y` to the group of morphisms `X ⟶ Y`. At each point, we get an additiona
l `End X`-module
structure, see `preadditiveCoyonedaObj`.
-/
def preadditiveCoyoneda : Cᵒᵖ ⥤ C ⥤ AddCommGrpCat.{v} where
  obj X := preadditiveCoyonedaObj (unop X) ⋙ forget₂ _ _
  map f :=
    { app := fun _ => AddCommGrpCat.ofHom
        { toFun := fun g => f.unop ≫ g
          map_zero' := Limits.comp_zero
          map_add' := fun _ _ => comp_add _ _ _ _ _ _ }
      naturality := fun _ _ _ =>
        AddCommGrpCat.ext fun _ => Eq.symm <| Category.assoc _ _ _ }
/-
**CategoryTheory.additive_yonedaObj** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C] (X : C),   (CategoryTheory.preadditiveYonedaObj X).Additi
ve
参数：X : C；CategoryTheory.preadditiveYonedaObj X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
· 使用定理 `AddHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : Add M] [
inst_1 : Add N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_add' 
: ∀ (x y :…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.preadditiveYonedaObj_map`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] (Y : C) {X Y_1
 : Cᵒᵖ}   (f : X ⟶ Y_1),   (C…
· 使用定理 `LinearMap.mk.congr_simp`：∀ {R : Type u_14} {S : Type u_15} [inst : Semir
ing R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_16}   {M₂ : Type u_17} [i
nst_2 : AddCo…
-/
instance additive_yonedaObj (X : C) : Functor.Additive (preadditiveYonedaObj X) where

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.additive_yonedaObj'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C] (X : C),   (CategoryTheory.preadditiveYoneda.obj X).Addit
ive
参数：X : C；CategoryTheory.preadditiveYoneda.obj X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
· 使用定理 `AddHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : Add M] [
inst_1 : Add N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_add' 
: ∀ (x y :…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.mk.congr_simp`：∀ {R : Type u_14} {S : Type u_15} [inst : Semir
ing R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_16}   {M₂ : Type u_17} [i
nst_2 : AddCo…
-/
instance additive_yonedaObj' (X : C) : Functor.Additive (preadditiveYoneda.obj X) where
/-
**CategoryTheory.additive_coyonedaObj** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`
。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C] (X : C),   (CategoryTheory.preadditiveCoyonedaObj X).Addi
tive
参数：X : C；CategoryTheory.preadditiveCoyonedaObj X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Preadditive.comp_add`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C) (f : P ⟶
 Q)   (g g' : Q ⟶ R),   C…
· 使用定理 `AddHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : Add M] [
inst_1 : Add N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_add' 
: ∀ (x y :…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.preadditiveCoyonedaObj_map`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] (X : C) {X_1
 Y : C}   (f : X_1 ⟶ Y),   (Cat…
· 使用定理 `LinearMap.mk.congr_simp`：∀ {R : Type u_14} {S : Type u_15} [inst : Semir
ing R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_16}   {M₂ : Type u_17} [i
nst_2 : AddCo…
-/
instance additive_coyonedaObj (X : C) : Functor.Additive (preadditiveCoyonedaObj X) where

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.additive_coyonedaObj'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C] (X : Cᵒᵖ),   (CategoryTheory.preadditiveCoyoneda.obj X).A
dditive
参数：X : Cᵒᵖ；CategoryTheory.preadditiveCoyoneda.obj X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Preadditive.comp_add`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C) (f : P ⟶
 Q)   (g g' : Q ⟶ R),   C…
· 使用定理 `AddHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : Add M] [
inst_1 : Add N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_add' 
: ∀ (x y :…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.mk.congr_simp`：∀ {R : Type u_14} {S : Type u_15} [inst : Semir
ing R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_16}   {M₂ : Type u_17} [i
nst_2 : AddCo…
-/
instance additive_coyonedaObj' (X : Cᵒᵖ) : Functor.Additive (preadditiveCoyoneda.obj X) where

/-- Composing the preadditive yoneda embedding with the forgetful functor yields the regular
Yoneda embedding.
-/
@[simp]
/-
**CategoryTheory.whiskering_preadditiveYoneda** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory`。
形式化陈述：whiskering_preadditiveYoneda : preadditiveYoneda ⋙ (whiskeringRight Cᵒᵖ Ad
dCommGrpCat (Type v)).obj (forget AddCommGrpCat) = yoneda
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composing the preadditive yoneda embedding with the forgetful functor yields the
 regular
Yoneda embedding.
-/
theorem whiskering_preadditiveYoneda :
    preadditiveYoneda ⋙
        (whiskeringRight Cᵒᵖ AddCommGrpCat (Type v)).obj (forget AddCommGrpCat) =
      yoneda :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Composing the preadditive yoneda embedding with the forgetful functor yields the regular
Yoneda embedding.
-/
@[simp]
/-
**CategoryTheory.whiskering_preadditiveCoyoneda** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory`。
形式化陈述：whiskering_preadditiveCoyoneda : preadditiveCoyoneda ⋙ (whiskeringRight C 
AddCommGrpCat (Type v)).obj (forget AddCommGrpCat) = coyoneda
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composing the preadditive yoneda embedding with the forgetful functor yields the
 regular
Yoneda embedding.
-/
theorem whiskering_preadditiveCoyoneda :
    preadditiveCoyoneda ⋙
        (whiskeringRight C AddCommGrpCat (Type v)).obj (forget AddCommGrpCat) =
      coyoneda :=
  rfl
/-
**CategoryTheory.full_preadditiveYoneda** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y`。
形式化陈述：full_preadditiveYoneda : (preadditiveYoneda : C ⥤ Cᵒᵖ ⥤ AddCommGrpCat).Ful
l
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.Full.of_comp_faithful`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.instFaithfulForget`：∀ (C : Type u_1) [inst : CategoryTheo
ry.Category.{v_1, u_1} C] {FC : outParam (C → C → Type u_2)}   {CC : outParam (C
 → Type w)} [inst_1 : o…
-/
instance full_preadditiveYoneda : (preadditiveYoneda : C ⥤ Cᵒᵖ ⥤ AddCommGrpCat).Full :=
  let _ : Functor.Full (preadditiveYoneda ⋙
      (whiskeringRight Cᵒᵖ AddCommGrpCat (Type v)).obj (forget AddCommGrpCat)) :=
    Yoneda.yoneda_full
  Functor.Full.of_comp_faithful preadditiveYoneda
    ((whiskeringRight Cᵒᵖ AddCommGrpCat (Type v)).obj (forget AddCommGrpCat))

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.full_preadditiveCoyoneda** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory`。
形式化陈述：full_preadditiveCoyoneda : (preadditiveCoyoneda : Cᵒᵖ ⥤ C ⥤ AddCommGrpCat)
.Full
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.Full.of_comp_faithful`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.instFaithfulForget`：∀ (C : Type u_1) [inst : CategoryTheo
ry.Category.{v_1, u_1} C] {FC : outParam (C → C → Type u_2)}   {CC : outParam (C
 → Type w)} [inst_1 : o…
-/
instance full_preadditiveCoyoneda : (preadditiveCoyoneda : Cᵒᵖ ⥤ C ⥤ AddCommGrpCat).Full :=
  let _ : Functor.Full (preadditiveCoyoneda ⋙
      (whiskeringRight C AddCommGrpCat (Type v)).obj (forget AddCommGrpCat)) :=
    Coyoneda.coyoneda_full
  Functor.Full.of_comp_faithful preadditiveCoyoneda
    ((whiskeringRight C AddCommGrpCat (Type v)).obj (forget AddCommGrpCat))
/-
**CategoryTheory.faithful_preadditiveYoneda** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory`。
形式化陈述：faithful_preadditiveYoneda : (preadditiveYoneda : C ⥤ Cᵒᵖ ⥤ AddCommGrpCat)
.Faithful
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.Faithful.of_comp_eq`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.
{v₂, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.whiskering_preadditiveYoneda`：whiskering_preadditiveYoned
a : preadditiveYoneda ⋙ (whiskeringRight Cᵒᵖ AddCommGrpCat (Type v)).obj (forget
 AddCommGrpCat) = yoneda
-/
instance faithful_preadditiveYoneda : (preadditiveYoneda : C ⥤ Cᵒᵖ ⥤ AddCommGrpCat).Faithful :=
  Functor.Faithful.of_comp_eq whiskering_preadditiveYoneda
/-
**CategoryTheory.faithful_preadditiveCoyoneda** 是 Mathlib 中的一个实例，位于命名空间 `Categor
yTheory`。
形式化陈述：faithful_preadditiveCoyoneda : (preadditiveCoyoneda : Cᵒᵖ ⥤ C ⥤ AddCommGrp
Cat).Faithful
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.Faithful.of_comp_eq`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.
{v₂, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.whiskering_preadditiveCoyoneda`：whiskering_preadditiveCoy
oneda : preadditiveCoyoneda ⋙ (whiskeringRight C AddCommGrpCat (Type v)).obj (fo
rget AddCommGrpCat) = coyoneda
-/
instance faithful_preadditiveCoyoneda :
    (preadditiveCoyoneda : Cᵒᵖ ⥤ C ⥤ AddCommGrpCat).Faithful :=
  Functor.Faithful.of_comp_eq whiskering_preadditiveCoyoneda

section

variable {D : Type u₁} [Category.{v} D] [Preadditive D] (F : C ⥤ D) [F.Additive]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The natural transformation `preadditiveYoneda.obj X ⟶ F.op ⋙ preadditiveYoneda.obj (F.obj X)`
when `F : C ⥤ D` is an additive functor between preadditive categories and `X : C`. -/
@[simps]
/-
**CategoryTheory.preadditiveYonedaMap** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`
。
形式化陈述：preadditiveYonedaMap (X : C) : preadditiveYoneda.obj X ⟶ F.op ⋙ preadditiv
eYoneda.obj (F.obj X) where app Y
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural transformation `preadditiveYoneda.obj X ⟶ F.op ⋙ preadditiveYoneda.o
bj (F.obj X)`
when `F : C ⥤ D` is an additive functor between preadditive categories and `X : 
C`.
-/
def preadditiveYonedaMap (X : C) :
    preadditiveYoneda.obj X ⟶ F.op ⋙ preadditiveYoneda.obj (F.obj X) where
  app Y := AddCommGrpCat.ofHom F.mapAddHom

end

set_option backward.isDefEq.respectTransparency.types false in
/-- The preadditive coyoneda functor for the category `AddCommGrpCat` agrees with
`AddCommGrpCat.coyoneda`. -/
/-
**CategoryTheory._root_.AddCommGrpCat.preadditiveCoyonedaIso** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The preadditive coyoneda functor for the category `AddCommGrpCat` agrees with
`AddCommGrpCat.coyoneda`.
-/
def _root_.AddCommGrpCat.preadditiveCoyonedaIso : preadditiveCoyoneda ≅ AddCommGrpCat.coyoneda :=
  NatIso.ofComponents fun X ↦ NatIso.ofComponents fun Y ↦ AddCommGrpCat.homAddEquiv.toAddCommGrpIso

end CategoryTheory

