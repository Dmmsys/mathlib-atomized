/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Emily Riehl, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.PathCategory.MorphismProperty

/-!
# The category of quivers

The category of (bundled) quivers, and the free/forgetful adjunction between `Cat` and `Quiv`.
-/

@[expose] public section

universe v u v₁ v₂ v₃ u₁ u₂ u₃ w

namespace CategoryTheory

-- intended to be used with explicit universe parameters
set_option linter.checkUnivs false in
/-- Category of quivers. -/
/-
**CategoryTheory.Quiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：Quiv
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Category of quivers.
-/
def Quiv :=
  Bundled Quiver.{v, u}

namespace Quiv

/-
**CategoryTheory.Quiv.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Quiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort Quiv (Type u) where coe := Bundled.α
/-
**CategoryTheory.Quiv.str'** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Quiv`。
形式化陈述：str' (C : Quiv.{v, u}) : Quiver.{v, u} C
参数：C : Quiv.{v, u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance str' (C : Quiv.{v, u}) : Quiver.{v, u} C :=
  C.str

/-- Construct a bundled `Quiv` from the underlying type and the typeclass. -/
/-
**CategoryTheory.Quiv.of** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Quiv`。
形式化陈述：of (C : Type u) [Quiver.{v} C] : Quiv.{v, u}
参数：C : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a bundled `Quiv` from the underlying type and the typeclass.
-/
def of (C : Type u) [Quiver.{v} C] : Quiv.{v, u} :=
  Bundled.of C
/-
**CategoryTheory.Quiv.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Quiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited Quiv :=
  ⟨Quiv.of (Quiver.Empty PEmpty)⟩

/-- Category structure on `Quiv` -/
/-
**CategoryTheory.Quiv.category** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Quiv`。
形式化陈述：category : LargeCategory.{max v u} Quiv.{v, u} where Hom C D
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Category structure on `Quiv`
-/
instance category : LargeCategory.{max v u} Quiv.{v, u} where
  Hom C D := Prefunctor C D
  id C := Prefunctor.id C
  comp F G := Prefunctor.comp F G

/-- The forgetful functor from categories to quivers. -/
@[simps]
/-
**CategoryTheory.Quiv.forget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Quiv`。
形式化陈述：forget : Cat.{v, u} ⥤ Quiv.{v, u} where obj C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from categories to quivers.
-/
def forget : Cat.{v, u} ⥤ Quiv.{v, u} where
  obj C := Quiv.of C
  map F := F.toFunctor.toPrefunctor

/-- The identity in the category of quivers equals the identity prefunctor. -/
/-
**CategoryTheory.Quiv.id_eq_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Quiv`。
形式化陈述：id_eq_id (X : Quiv) : 𝟙 X = 𝟭q X
参数：X : Quiv。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity in the category of quivers equals the identity prefunctor.
-/
theorem id_eq_id (X : Quiv) : 𝟙 X = 𝟭q X := rfl

/-- Composition in the category of quivers equals prefunctor composition. -/
/-
**CategoryTheory.Quiv.comp_eq_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Qui
v`。
形式化陈述：comp_eq_comp {X Y Z : Quiv} (F : X ⟶ Y) (G : Y ⟶ Z) : F ≫ G = F ⋙q G
参数：F : X ⟶ Y；G : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition in the category of quivers equals prefunctor composition.
-/
theorem comp_eq_comp {X Y Z : Quiv} (F : X ⟶ Y) (G : Y ⟶ Z) : F ≫ G = F ⋙q G := rfl

end Quiv

namespace Prefunctor

/-- Prefunctors between quivers define arrows in `Quiv`. -/
/-
**CategoryTheory.Prefunctor.toQuivHom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Prefunctor`。
形式化陈述：toQuivHom {C D : Type u} [Quiver.{v} C] [Quiver.{v} D] (F : C ⥤q D) : Quiv
.of C ⟶ Quiv.of D
参数：F : C ⥤q D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Prefunctors between quivers define arrows in `Quiv`.
-/
def toQuivHom {C D : Type u} [Quiver.{v} C] [Quiver.{v} D] (F : C ⥤q D) :
    Quiv.of C ⟶ Quiv.of D := F

/-- Arrows in `Quiv` define prefunctors. -/
/-
**CategoryTheory.Prefunctor.ofQuivHom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Prefunctor`。
形式化陈述：ofQuivHom {C D : Quiv} (F : C ⟶ D) : C ⥤q D
参数：F : C ⟶ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Arrows in `Quiv` define prefunctors.
-/
def ofQuivHom {C D : Quiv} (F : C ⟶ D) : C ⥤q D := F
/-
**CategoryTheory.Prefunctor.to_ofQuivHom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Prefunctor`。
形式化陈述：∀ {C D : CategoryTheory.Quiv} (F : C ⟶ D),   CategoryTheory.Prefunctor.toQ
uivHom (CategoryTheory.Prefunctor.ofQuivHom F) = F
参数：F : C ⟶ D；CategoryTheory.Prefunctor.ofQuivHom F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem to_ofQuivHom {C D : Quiv} (F : C ⟶ D) : toQuivHom (ofQuivHom F) = F := rfl
/-
**CategoryTheory.Prefunctor.of_toQuivHom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Prefunctor`。
形式化陈述：∀ {C D : Type} [inst : Quiver C] [inst_1 : Quiver D] (F : C ⥤q D),   Categ
oryTheory.Prefunctor.ofQuivHom (CategoryTheory.Prefunctor.toQuivHom F) = F
参数：F : C ⥤q D；CategoryTheory.Prefunctor.toQuivHom F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem of_toQuivHom {C D : Type} [Quiver C] [Quiver D] (F : C ⥤q D) :
    ofQuivHom (toQuivHom F) = F := rfl

end Prefunctor
namespace Cat

/-- A prefunctor `V ⥤q W` induces a functor between the path categories defined by `F.mapPath`. -/
@[simps]
/-
**CategoryTheory.Cat.freeMap** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Cat`。
形式化陈述：freeMap {V W : Type*} [Quiver V] [Quiver W] (F : V ⥤q W) : Paths V ⥤ Paths
 W where obj
参数：F : V ⥤q W。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Prefunctor.mapPath_comp`：∀ {V : Type u₁} [inst : Quiver V] {W : Type u₂}
 [inst_1 : Quiver W] (F : V ⥤q W) {a b : V} (p : Quiver.Path a b) {c : V}   (q :
 Quiver.Path …

--- 原说明 ---
A prefunctor `V ⥤q W` induces a functor between the path categories defined by `
F.mapPath`.
-/
def freeMap {V W : Type*} [Quiver V] [Quiver W] (F : V ⥤q W) : Paths V ⥤ Paths W where
  obj := F.obj
  map := F.mapPath
  map_comp f g := F.mapPath_comp f g

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The functor `free : Quiv ⥤ Cat` preserves identities up to natural isomorphism and in fact up
to equality. -/
@[simps!]
/-
**CategoryTheory.Cat.freeMapIdIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Cat`
。
形式化陈述：freeMapIdIso (V : Type*) [Quiver V] : freeMap (𝟭q V) ≅ 𝟭 _
参数：V : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `free : Quiv ⥤ Cat` preserves identities up to natural isomorphism a
nd in fact up
to equality.
-/
def freeMapIdIso (V : Type*) [Quiver V] : freeMap (𝟭q V) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Cat.freeMap_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Cat`。
形式化陈述：freeMap_id (V : Type*) [Quiver V] : freeMap (𝟭q V) = 𝟭 _
参数：V : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.ext_of_iso`：ext_of_iso {F G : C ⥤ D} (e : F ≅ G) 
(hobj : forall X, F.obj X = G.obj X) (happ : forall X, e.hom.app X = eqToHom (ho
bj X)
-/
theorem freeMap_id (V : Type*) [Quiver V] :
    freeMap (𝟭q V) = 𝟭 _ :=
  Functor.ext_of_iso (freeMapIdIso V) (fun _ ↦ rfl)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The functor `free : Quiv ⥤ Cat` preserves composition up to natural isomorphism and in fact up
to equality. -/
@[simps!]
/-
**CategoryTheory.Cat.freeMapCompIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Ca
t`。
形式化陈述：freeMapCompIso {V₁ : Type u₁} {V₂ : Type u₂} {V₃ : Type u₃} [Quiver.{v₁} V
₁] [Quiver.{v₂} V₂] [Quiver.{v₃} V₃] (F : V₁ ⥤q V₂) (G : V₂ ⥤q V₃) : freeMap (F 
⋙q G) ≅ freeMap F ⋙ freeMap G
参数：F : V₁ ⥤q V₂；G : V₂ ⥤q V₃。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `free : Quiv ⥤ Cat` preserves composition up to natural isomorphism 
and in fact up
to equality.
-/
def freeMapCompIso {V₁ : Type u₁} {V₂ : Type u₂} {V₃ : Type u₃}
    [Quiver.{v₁} V₁] [Quiver.{v₂} V₂] [Quiver.{v₃} V₃] (F : V₁ ⥤q V₂) (G : V₂ ⥤q V₃) :
    freeMap (F ⋙q G) ≅ freeMap F ⋙ freeMap G :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun f ↦ by
    dsimp
    simp only [Category.comp_id, Category.id_comp, Prefunctor.mapPath_comp_apply])

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Cat.freeMap_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Cat`
。
形式化陈述：freeMap_comp {V₁ : Type u₁} {V₂ : Type u₂} {V₃ : Type u₃} [Quiver.{v₁} V₁]
 [Quiver.{v₂} V₂] [Quiver.{v₃} V₃] (F : V₁ ⥤q V₂) (G : V₂ ⥤q V₃) : freeMap (F ⋙q
 G) = freeMap F ⋙ freeMap G
参数：F : V₁ ⥤q V₂；G : V₂ ⥤q V₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.ext_of_iso`：ext_of_iso {F G : C ⥤ D} (e : F ≅ G) 
(hobj : forall X, F.obj X = G.obj X) (happ : forall X, e.hom.app X = eqToHom (ho
bj X)
-/
theorem freeMap_comp {V₁ : Type u₁} {V₂ : Type u₂} {V₃ : Type u₃}
    [Quiver.{v₁} V₁] [Quiver.{v₂} V₂] [Quiver.{v₃} V₃]
    (F : V₁ ⥤q V₂) (G : V₂ ⥤q V₃) :
    freeMap (F ⋙q G) = freeMap F ⋙ freeMap G :=
  Functor.ext_of_iso (freeMapCompIso F G) (fun _ ↦ rfl)

/-- The functor sending each quiver to its path category. -/
@[simps]
/-
**CategoryTheory.Cat.free** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Cat`。
形式化陈述：free : Quiv.{v, u} ⥤ Cat.{max u v, u} where obj V
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor sending each quiver to its path category.
-/
def free : Quiv.{v, u} ⥤ Cat.{max u v, u} where
  obj V := Cat.of (Paths V)
  map F := Functor.toCatHom (freeMap (Prefunctor.ofQuivHom F))
  map_id _ := congr($(freeMap_id _).toCatHom)
  map_comp _ _ := congr($(freeMap_comp _ _).toCatHom)

end Cat

namespace Quiv

section
variable {V W : Quiv} (e : V ≅ W)

/-- An isomorphism of quivers defines an equivalence on carrier types. -/
@[simps]
/-
**CategoryTheory.Quiv.equivOfIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Quiv`
。
形式化陈述：equivOfIso : V ≃ W where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isomorphism of quivers defines an equivalence on carrier types.
-/
def equivOfIso : V ≃ W where
  toFun := e.hom.obj
  invFun := e.inv.obj
  left_inv := Prefunctor.congr_obj e.hom_inv_id
  right_inv := Prefunctor.congr_obj e.inv_hom_id

@[simp]
/-
**CategoryTheory.Quiv.inv_obj_hom_obj_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Quiv`。
形式化陈述：inv_obj_hom_obj_of_iso (X : V) : e.inv.obj (e.hom.obj X) = X
参数：X : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
-/
lemma inv_obj_hom_obj_of_iso (X : V) : e.inv.obj (e.hom.obj X) = X := (equivOfIso e).left_inv X

@[simp]
/-
**CategoryTheory.Quiv.hom_obj_inv_obj_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Quiv`。
形式化陈述：hom_obj_inv_obj_of_iso (Y : W) : e.hom.obj (e.inv.obj Y) = Y
参数：Y : W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
-/
lemma hom_obj_inv_obj_of_iso (Y : W) : e.hom.obj (e.inv.obj Y) = Y := (equivOfIso e).right_inv Y
/-
**CategoryTheory.Quiv.hom_map_inv_map_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Quiv`。
形式化陈述：hom_map_inv_map_of_iso {V W : Quiv} (e : V ≅ W) {X Y : W} (f : X ⟶ Y) : e.
hom.map (e.inv.map f) = Quiver.homOfEq f (by simp) (by simp)
参数：e : V ≅ W；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Prefunctor.comp_map`：∀ {U : Type u_1} [inst : Quiver U] {V : Type u_2} [
inst_1 : Quiver V] {W : Type u_3} [inst_2 : Quiver W] (F : U ⥤q V)   (G : V ⥤q W
) {X Y : …
· 使用定理 `Prefunctor.congr_obj`：congr_obj {U V : Type*} [Quiver U] [Quiver V] {F G
 : U ⥤q V} (e : F = G) (X : U) : F.obj X = G.obj X
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `Prefunctor.congr_hom`：congr_hom {U V : Type*} [Quiver U] [Quiver V] {F G
 : U ⥤q V} (e : F = G) {X Y : U} (f : X ⟶ Y) : Quiver.homOfEq (F.map f) (congr_o
bj e X) (c…
-/
lemma hom_map_inv_map_of_iso {V W : Quiv} (e : V ≅ W) {X Y : W} (f : X ⟶ Y) :
    e.hom.map (e.inv.map f) = Quiver.homOfEq f (by simp) (by simp) := by
  rw [← Prefunctor.comp_map]
  exact (Prefunctor.congr_hom e.inv_hom_id.symm f).symm
/-
**CategoryTheory.Quiv.inv_map_hom_map_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Quiv`。
形式化陈述：inv_map_hom_map_of_iso {V W : Quiv} (e : V ≅ W) {X Y : V} (f : X ⟶ Y) : e.
inv.map (e.hom.map f) = Quiver.homOfEq f (by simp) (by simp)
参数：e : V ≅ W；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Quiv.hom_map_inv_map_of_iso`：hom_map_inv_map_of_iso {V W 
: Quiv} (e : V ≅ W) {X Y : W} (f : X ⟶ Y) : e.hom.map (e.inv.map f) = Quiver.hom
OfEq f (by simp) (by simp)
-/
lemma inv_map_hom_map_of_iso {V W : Quiv} (e : V ≅ W) {X Y : V} (f : X ⟶ Y) :
    e.inv.map (e.hom.map f) = Quiver.homOfEq f (by simp) (by simp) :=
  hom_map_inv_map_of_iso e.symm f

/-- An isomorphism of quivers defines an equivalence on hom types. -/
@[simps]
/-
**CategoryTheory.Quiv.homEquivOfIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Qu
iv`。
形式化陈述：homEquivOfIso {V W : Quiv} (e : V ≅ W) {X Y : V} : (X ⟶ Y) ≃ (e.hom.obj X 
⟶ e.hom.obj Y) where toFun f
参数：e : V ≅ W。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isomorphism of quivers defines an equivalence on hom types.
-/
def homEquivOfIso {V W : Quiv} (e : V ≅ W) {X Y : V} :
    (X ⟶ Y) ≃ (e.hom.obj X ⟶ e.hom.obj Y) where
  toFun f := e.hom.map f
  invFun g := Quiver.homOfEq (e.inv.map g) (by simp) (by simp)
  left_inv f := by simp [inv_map_hom_map_of_iso]
  right_inv g := by simp [hom_map_inv_map_of_iso]

end

section
variable {V W : Type u} [Quiver V] [Quiver W]
  (e : V ≃ W) (he : ∀ X Y : V, (X ⟶ Y) ≃ (e X ⟶ e Y))

include he in
@[simp]
/-
**CategoryTheory.Quiv.homOfEq_map_homOfEq** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Quiv`。
形式化陈述：homOfEq_map_homOfEq {X Y : V} (f : X ⟶ Y) {X' Y' : V} (hX : X = X') (hY : 
Y = Y') {X'' Y'' : W} (hX' : e X' = X'') (hY' : e Y' = Y'') : Quiver.homOfEq (he
 _ _ (Quiver.homOfEq f hX hY)) hX' hY' = Quiver.homOfEq (he _ _ f) (by rw [hX, h
X']) (by rw [hY, hY'])
参数：f : X ⟶ Y；hX : X = X'；hY : Y = Y'；hX' : e X' = X''；hY' : e Y' = Y''。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homOfEq_map_homOfEq {X Y : V} (f : X ⟶ Y) {X' Y' : V} (hX : X = X') (hY : Y = Y')
    {X'' Y'' : W} (hX' : e X' = X'') (hY' : e Y' = Y'') :
    Quiver.homOfEq (he _ _ (Quiver.homOfEq f hX hY)) hX' hY' =
      Quiver.homOfEq (he _ _ f) (by rw [hX, hX']) (by rw [hY, hY']) := by
  subst hX hY hX' hY'
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Compatible equivalences of types and hom-types induce an isomorphism of quivers. -/
/-
**CategoryTheory.Quiv.isoOfEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Quiv`
。
形式化陈述：isoOfEquiv : Quiv.of V ≅ Quiv.of W where hom
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Compatible equivalences of types and hom-types induce an isomorphism of quivers.
-/
def isoOfEquiv : Quiv.of V ≅ Quiv.of W where
  hom := Prefunctor.mk e (he _ _)
  inv :=
    { obj := e.symm
      map {X Y} f := (he _ _).symm (Quiver.homOfEq f (by simp) (by simp)) }
  hom_inv_id := Prefunctor.ext' e.left_inv (fun X Y f ↦ by
    dsimp [Quiv.id_eq_id, Quiv.comp_eq_comp]
    apply (he _ _).injective
    apply Quiver.homOfEq_injective (X' := e X) (Y' := e Y) (by simp) (by simp)
    simp)
  inv_hom_id := Prefunctor.ext' e.right_inv (by simp [Quiv.id_eq_id, Quiv.comp_eq_comp])

end

/-- Any prefunctor into a category lifts to a functor from the path category. -/
@[simps]
/-
**CategoryTheory.Quiv.lift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Quiv`。
形式化陈述：lift {V : Type u} [Quiver.{v} V] {C : Type u₁} [Category.{v₁} C] (F : Pref
unctor V C) : Paths V ⥤ C where obj X
参数：F : Prefunctor V C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any prefunctor into a category lifts to a functor from the path category.
-/
def lift {V : Type u} [Quiver.{v} V] {C : Type u₁} [Category.{v₁} C]
    (F : Prefunctor V C) : Paths V ⥤ C where
  obj X := F.obj X
  map f := composePath (F.mapPath f)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Naturality of `pathComposition`. -/
/-
**CategoryTheory.Quiv.pathCompositionNaturality** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Quiv`。
形式化陈述：pathCompositionNaturality {C : Type u} {D : Type u₁} [Category.{v} C] [Cat
egory.{v₁} D] (F : C ⥤ D) : Cat.freeMap (F.toPrefunctor) ⋙ pathComposition D ≅ p
athComposition C ⋙ F
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Naturality of `pathComposition`.
-/
def pathCompositionNaturality {C : Type u} {D : Type u₁}
    [Category.{v} C] [Category.{v₁} D] (F : C ⥤ D) :
    Cat.freeMap (F.toPrefunctor) ⋙ pathComposition D ≅ pathComposition C ⋙ F :=
  Paths.liftNatIso (fun _ ↦ Iso.refl _) (by simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Naturality of `pathComposition`, which defines a natural transformation
`Quiv.forget ⋙ Cat.free ⟶ 𝟭 _`. -/
/-
**CategoryTheory.Quiv.pathComposition_naturality** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Quiv`。
形式化陈述：pathComposition_naturality {C : Type u} {D : Type u₁} [Category.{v} C] [Ca
tegory.{v₁} D] (F : C ⥤ D) : Cat.freeMap (F.toPrefunctor) ⋙ pathComposition D = 
pathComposition C ⋙ F
参数：F : C ⥤ D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Paths.ext_functor`：ext_functor {C} [Category* C] {F G : P
aths V ⥤ C} (h_obj : F.obj = G.obj) (h : forall (a b : V) (e : a ⟶ b), F.map e.t
oPath = eqToHom (congr…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.composePath_toPath`：composePath_toPath {X Y : C} (f : X ⟶
 Y) : composePath f.toPath = f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
Naturality of `pathComposition`, which defines a natural transformation
`Quiv.forget ⋙ Cat.free ⟶ 𝟭 _`.
-/
theorem pathComposition_naturality {C : Type u} {D : Type u₁}
    [Category.{v} C] [Category.{v₁} D]
    (F : C ⥤ D) : Cat.freeMap (F.toPrefunctor) ⋙ pathComposition D = pathComposition C ⋙ F :=
  Paths.ext_functor rfl (by simp)

/-- Naturality of `Paths.of`, which defines a natural transformation
` 𝟭 _⟶ Cat.free ⋙ Quiv.forget`. -/
/-
**CategoryTheory.Quiv.pathsOf_freeMap_toPrefunctor** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Quiv`。
形式化陈述：pathsOf_freeMap_toPrefunctor {V : Type u} {W : Type u₁} [Quiver.{v} V] [Qu
iver.{v₁} W] (F : V ⥤q W) : Paths.of V ⋙q (Cat.freeMap F).toPrefunctor = F ⋙q Pa
ths.of W
参数：F : V ⥤q W。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Naturality of `Paths.of`, which defines a natural transformation
` 𝟭 _⟶ Cat.free ⋙ Quiv.forget`.
-/
lemma pathsOf_freeMap_toPrefunctor
    {V : Type u} {W : Type u₁} [Quiver.{v} V] [Quiver.{v₁} W] (F : V ⥤q W) :
    Paths.of V ⋙q (Cat.freeMap F).toPrefunctor = F ⋙q Paths.of W := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The left triangle identity of `Cat.free ⊣ Quiv.forget` as a natural isomorphism -/
/-
**CategoryTheory.Quiv.freeMapPathsOfCompPathCompositionIso** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.Quiv`。
形式化陈述：freeMapPathsOfCompPathCompositionIso (V : Type u) [Quiver.{v} V] : Cat.fre
eMap (Paths.of V) ⋙ pathComposition (Paths V) ≅ 𝟭 (Paths V)
参数：V : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left triangle identity of `Cat.free ⊣ Quiv.forget` as a natural isomorphism
-/
def freeMapPathsOfCompPathCompositionIso (V : Type u) [Quiver.{v} V] :
    Cat.freeMap (Paths.of V) ⋙ pathComposition (Paths V) ≅ 𝟭 (Paths V) :=
  Paths.liftNatIso (fun v ↦ Iso.refl _) (by simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Quiv.freeMap_pathsOf_pathComposition** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Quiv`。
形式化陈述：freeMap_pathsOf_pathComposition (V : Type u) [Quiver.{v} V] : Cat.freeMap 
(Paths.of (V
参数：V : Type u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Paths.ext_functor`：ext_functor {C} [Category* C] {F G : P
aths V ⥤ C} (h_obj : F.obj = G.obj) (h : forall (a b : V) (e : a ⟶ b), F.map e.t
oPath = eqToHom (congr…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.composePath_toPath`：composePath_toPath {X Y : C} (f : X ⟶
 Y) : composePath f.toPath = f
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma freeMap_pathsOf_pathComposition (V : Type u) [Quiver.{v} V] :
    Cat.freeMap (Paths.of (V := V)) ⋙ pathComposition (Paths V) = 𝟭 (Paths V) :=
  Paths.ext_functor rfl (by simp)

/-- An unbundled version of the right triangle equality. -/
/-
**CategoryTheory.Quiv.pathsOf_pathComposition_toPrefunctor** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Quiv`。
形式化陈述：pathsOf_pathComposition_toPrefunctor (C : Type u) [Category.{v} C] : Paths
.of C ⋙q (pathComposition C).toPrefunctor = 𝟭q C
参数：C : Type u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…

--- 原说明 ---
An unbundled version of the right triangle equality.
-/
lemma pathsOf_pathComposition_toPrefunctor (C : Type u) [Category.{v} C] :
    Paths.of C ⋙q (pathComposition C).toPrefunctor = 𝟭q C := by
  dsimp only [Prefunctor.comp]
  congr
  funext X Y f
  exact Category.id_comp _

/--
The adjunction between forming the free category on a quiver, and forgetting a category to a quiver.
-/
/-
**CategoryTheory.Quiv.adj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Quiv`。
形式化陈述：adj : Cat.free ⊣ Quiv.forget
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The adjunction between forming the free category on a quiver, and forgetting a c
ategory to a quiver.
-/
def adj : Cat.free ⊣ Quiv.forget :=
  Adjunction.mkOfUnitCounit {
    unit := { app _ := Paths.of _}
    counit := {
      app C := (pathComposition C).toCatHom
      naturality _ _ F := congr($(pathComposition_naturality F.toFunctor).toCatHom)
    }
    left_triangle := by
      ext V
      exact freeMap_pathsOf_pathComposition V
    right_triangle := by
      ext C
      exact pathsOf_pathComposition_toPrefunctor C
  }

/-- The universal property of the path category of a quiver. -/
/-
**CategoryTheory.Quiv.pathsEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Quiv`
。
形式化陈述：pathsEquiv {V : Type u} {C : Type u₁} [Quiver.{v} V] [Category.{v₁} C] : (
Paths V ⥤ C) ≃ V ⥤q C where toFun F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The universal property of the path category of a quiver.
-/
def pathsEquiv {V : Type u} {C : Type u₁} [Quiver.{v} V] [Category.{v₁} C] :
    (Paths V ⥤ C) ≃ V ⥤q C where
  toFun F := (Paths.of V).comp F.toPrefunctor
  invFun G := Cat.freeMap G ⋙ pathComposition C
  left_inv F := by
    dsimp
    rw [Cat.freeMap_comp, Functor.assoc, pathComposition_naturality, ← Functor.assoc,
      freeMap_pathsOf_pathComposition, Functor.id_comp]
  right_inv G := by
    dsimp
    rw [← Functor.toPrefunctor_comp, ← Prefunctor.comp_assoc,
      pathsOf_freeMap_toPrefunctor, Prefunctor.comp_assoc,
      pathsOf_pathComposition_toPrefunctor, Prefunctor.comp_id]

@[simp]
/-
**CategoryTheory.Quiv.adj_homEquiv** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Qui
v`。
形式化陈述：adj_homEquiv {V C : Type u} [Quiver.{max u v} V] [Category.{max u v} C] : 
adj.homEquiv (Quiv.of V) (Cat.of C) = (Cat.Hom.equivFunctor (.of (Paths V)) (.of
 C)).trans (pathsEquiv (V
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma adj_homEquiv {V C : Type u} [Quiver.{max u v} V] [Category.{max u v} C] :
    adj.homEquiv (Quiv.of V) (Cat.of C) =
      (Cat.Hom.equivFunctor (.of (Paths V)) (.of C)).trans (pathsEquiv (V := V) (C := C)) := rfl

end Quiv

end CategoryTheory

