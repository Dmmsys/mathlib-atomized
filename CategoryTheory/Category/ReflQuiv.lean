/-
Copyright (c) 2024 Mario Carneiro and Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Emily Riehl
-/
module

public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Category.Quiv

/-!
# The category of refl quivers

The category `ReflQuiv` of (bundled) reflexive quivers, and the free/forgetful adjunction between
`Cat` and `ReflQuiv`.
-/

@[expose] public section

namespace CategoryTheory
universe v u v₁ v₂ u₁ u₂

set_option linter.checkUnivs false in
/-- Category of refl quivers. -/
/-
**CategoryTheory.ReflQuiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：ReflQuiv
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Category of refl quivers.
-/
def ReflQuiv :=
  Bundled ReflQuiver.{v, u}

namespace ReflQuiv

/-
**CategoryTheory.ReflQuiv.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ReflQuiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort ReflQuiv (Type u) where coe := Bundled.α
/-
**CategoryTheory.ReflQuiv.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ReflQuiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (C : ReflQuiv.{v, u}) : ReflQuiver.{v, u} C := C.str

/-- The underlying quiver of a reflexive quiver -/
/-
**CategoryTheory.ReflQuiv.toQuiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.ReflQ
uiv`。
形式化陈述：toQuiv (C : ReflQuiv.{v, u}) : Quiv.{v, u}
参数：C : ReflQuiv.{v, u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying quiver of a reflexive quiver
-/
def toQuiv (C : ReflQuiv.{v, u}) : Quiv.{v, u} := Quiv.of C.α

/-- Construct a bundled `ReflQuiv` from the underlying type and the typeclass. -/
/-
**CategoryTheory.ReflQuiv.of** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.ReflQuiv`
。
形式化陈述：of (C : Type u) [ReflQuiver.{v} C] : ReflQuiv.{v, u}
参数：C : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a bundled `ReflQuiv` from the underlying type and the typeclass.
-/
def of (C : Type u) [ReflQuiver.{v} C] : ReflQuiv.{v, u} := Bundled.of C
/-
**CategoryTheory.ReflQuiv.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ReflQuiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited ReflQuiv := ⟨ReflQuiv.of (Discrete default)⟩
/-
**CategoryTheory.ReflQuiv.of_val** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.ReflQ
uiv`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.ReflQuiver C], ↑(CategoryTheory.Refl
Quiv.of C) = C
参数：C : Type u；CategoryTheory.ReflQuiv.of C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem of_val (C : Type u) [ReflQuiver C] : (ReflQuiv.of C) = C := rfl

/-- Category structure on `ReflQuiv` -/
/-
**CategoryTheory.ReflQuiv.category** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Ref
lQuiv`。
形式化陈述：category : LargeCategory.{max v u} ReflQuiv.{v, u} where Hom C D
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Category structure on `ReflQuiv`
-/
instance category : LargeCategory.{max v u} ReflQuiv.{v, u} where
  Hom C D := ReflPrefunctor C D
  id C := ReflPrefunctor.id C
  comp F G := ReflPrefunctor.comp F G
/-
**CategoryTheory.ReflQuiv.id_eq_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Ref
lQuiv`。
形式化陈述：id_eq_id (X : ReflQuiv) : 𝟙 X = 𝟭rq X
参数：X : ReflQuiv。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_eq_id (X : ReflQuiv) : 𝟙 X = 𝟭rq X := rfl
/-
**CategoryTheory.ReflQuiv.comp_eq_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.ReflQuiv`。
形式化陈述：comp_eq_comp {X Y Z : ReflQuiv} (F : X ⟶ Y) (G : Y ⟶ Z) : F ≫ G = F ⋙rq G
参数：F : X ⟶ Y；G : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_eq_comp {X Y Z : ReflQuiv} (F : X ⟶ Y) (G : Y ⟶ Z) : F ≫ G = F ⋙rq G := rfl

@[simp]
/-
**CategoryTheory.ReflQuiv.id_obj** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ReflQ
uiv`。
形式化陈述：id_obj (X : ReflQuiv) (x : X) : (ReflPrefunctor.toPrefunctor (𝟙 X)).obj x 
= x
参数：X : ReflQuiv；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma id_obj (X : ReflQuiv) (x : X) : (ReflPrefunctor.toPrefunctor (𝟙 X)).obj x = x := rfl

@[simp]
/-
**CategoryTheory.ReflQuiv.id_map** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ReflQ
uiv`。
形式化陈述：id_map {X : ReflQuiv} {x y : X} (f : x ⟶ y) : (ReflPrefunctor.toPrefunctor
 (𝟙 X)).map f = f
参数：f : x ⟶ y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma id_map {X : ReflQuiv} {x y : X} (f : x ⟶ y) :
    (ReflPrefunctor.toPrefunctor (𝟙 X)).map f = f := rfl

@[simp]
/-
**CategoryTheory.ReflQuiv.comp_obj** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Ref
lQuiv`。
形式化陈述：comp_obj {X Y Z : ReflQuiv} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g).obj 
x = g.obj (f.obj x)
参数：f : X ⟶ Y；g : Y ⟶ Z；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comp_obj {X Y Z : ReflQuiv} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g).obj x = g.obj (f.obj x) := rfl

@[simp]
/-
**CategoryTheory.ReflQuiv.comp_map** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Ref
lQuiv`。
形式化陈述：comp_map {X Y Z : ReflQuiv} (f : X ⟶ Y) (g : Y ⟶ Z) {x y : X} (a : x ⟶ y) 
: (f ≫ g).map a = g.map (f.map a)
参数：f : X ⟶ Y；g : Y ⟶ Z；a : x ⟶ y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comp_map {X Y Z : ReflQuiv} (f : X ⟶ Y) (g : Y ⟶ Z) {x y : X} (a : x ⟶ y) :
    (f ≫ g).map a = g.map (f.map a) := rfl

/-- The forgetful functor from categories to quivers. -/
@[simps]
/-
**CategoryTheory.ReflQuiv.forget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.ReflQ
uiv`。
形式化陈述：forget : Cat.{v, u} ⥤ ReflQuiv.{v, u} where obj C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from categories to quivers.
-/
def forget : Cat.{v, u} ⥤ ReflQuiv.{v, u} where
  obj C := ReflQuiv.of C
  map F := F.toFunctor.toReflPrefunctor
/-
**CategoryTheory.ReflQuiv.forget_faithful** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.ReflQuiv`。
形式化陈述：forget_faithful {C D : Cat.{v, u}} (F G : C ⥤ D) (hyp : forget.map F.toCat
Hom = forget.map G.toCatHom) : F = G
参数：F G : C ⥤ D；hyp : forget.map F.toCatHom = forget.map G.toCatHom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem forget_faithful {C D : Cat.{v, u}} (F G : C ⥤ D)
    (hyp : forget.map F.toCatHom = forget.map G.toCatHom) : F = G := by
  cases F; cases G; cases hyp; rfl
/-
**CategoryTheory.ReflQuiv.forget.Faithful** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.ReflQuiv.forget`。
形式化陈述：CategoryTheory.ReflQuiv.forget.Faithful
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Cat.Hom.ext`：∀ {C D : CategoryTheory.Cat} {x y : C.Hom D}
, x.toFunctor = y.toFunctor → x = y
· 使用定理 `CategoryTheory.ReflQuiv.forget_faithful`：forget_faithful {C D : Cat.{v, 
u}} (F G : C ⥤ D) (hyp : forget.map F.toCatHom = forget.map G.toCatHom) : F = G
-/
instance forget.Faithful : Functor.Faithful (forget) where
  map_injective := fun hyp ↦ Cat.Hom.ext <| forget_faithful _ _ hyp

/-- The forgetful functor from categories to quivers. -/
@[simps]
/-
**CategoryTheory.ReflQuiv.forgetToQuiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.ReflQuiv`。
形式化陈述：forgetToQuiv : ReflQuiv.{v, u} ⥤ Quiv.{v, u} where obj V
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from categories to quivers.
-/
def forgetToQuiv : ReflQuiv.{v, u} ⥤ Quiv.{v, u} where
  obj V := Quiv.of V
  map F := F.toPrefunctor
/-
**CategoryTheory.ReflQuiv.forgetToQuiv_faithful** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.ReflQuiv`。
形式化陈述：forgetToQuiv_faithful {V W : ReflQuiv} (F G : V ⥤rq W) (hyp : forgetToQuiv
.map F = forgetToQuiv.map G) : F = G
参数：F G : V ⥤rq W；hyp : forgetToQuiv.map F = forgetToQuiv.map G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem forgetToQuiv_faithful {V W : ReflQuiv} (F G : V ⥤rq W)
    (hyp : forgetToQuiv.map F = forgetToQuiv.map G) : F = G := by
  cases F; cases G; cases hyp; rfl
/-
**CategoryTheory.ReflQuiv.forgetToQuiv.Faithful** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.ReflQuiv.forgetToQuiv`。
形式化陈述：CategoryTheory.ReflQuiv.forgetToQuiv.Faithful
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ReflQuiv.forgetToQuiv_faithful`：forgetToQuiv_faithful {V 
W : ReflQuiv} (F G : V ⥤rq W) (hyp : forgetToQuiv.map F = forgetToQuiv.map G) : 
F = G
-/
instance forgetToQuiv.Faithful : Functor.Faithful forgetToQuiv where
  map_injective := fun hyp ↦ forgetToQuiv_faithful _ _ hyp
/-
**CategoryTheory.ReflQuiv.forget_forgetToQuiv** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.ReflQuiv`。
形式化陈述：forget_forgetToQuiv : forget ⋙ forgetToQuiv = Quiv.forget
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forget_forgetToQuiv : forget ⋙ forgetToQuiv = Quiv.forget := rfl

set_option backward.isDefEq.respectTransparency false in
/-- An isomorphism of quivers lifts to an isomorphism of reflexive quivers given a suitable
compatibility with the identities. -/
/-
**CategoryTheory.ReflQuiv.isoOfQuivIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.ReflQuiv`。
形式化陈述：isoOfQuivIso {V W : Type u} [ReflQuiver V] [ReflQuiver W] (e : Quiv.of V ≅
 Quiv.of W) (h_id : forall (X : V), e.hom.map (𝟙rq X) = ReflQuiver.id (obj
参数：e : Quiv.of V ≅ Quiv.of W。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isomorphism of quivers lifts to an isomorphism of reflexive quivers given a s
uitable
compatibility with the identities.
-/
def isoOfQuivIso {V W : Type u} [ReflQuiver V] [ReflQuiver W]
    (e : Quiv.of V ≅ Quiv.of W)
    (h_id : ∀ (X : V), e.hom.map (𝟙rq X) = ReflQuiver.id (obj := W) (e.hom.obj X)) :
    ReflQuiv.of V ≅ ReflQuiv.of W where
  hom := ReflPrefunctor.mk e.hom h_id
  inv := ReflPrefunctor.mk e.inv
    (fun Y => (Quiv.homEquivOfIso e).injective (by simp [Quiv.hom_map_inv_map_of_iso, h_id]))
  hom_inv_id := by
    apply forgetToQuiv.map_injective
    exact e.hom_inv_id
  inv_hom_id := by
    apply forgetToQuiv.map_injective
    exact e.inv_hom_id

/-- Compatible equivalences of types and hom-types induce an isomorphism of reflexive quivers. -/
/-
**CategoryTheory.ReflQuiv.isoOfEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.R
eflQuiv`。
形式化陈述：isoOfEquiv {V W : Type u} [ReflQuiver V] [ReflQuiver W] (e : V ≃ W) (he : 
forall (X Y : V), (X ⟶ Y) ≃ (e X ⟶ e Y)) (h_id : forall (X : V), he _ _ (𝟙rq X) 
= ReflQuiver.id (obj
参数：e : V ≃ W；he : forall (X Y : V), (X ⟶ Y) ≃ (e X ⟶ e Y)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Compatible equivalences of types and hom-types induce an isomorphism of reflexiv
e quivers.
-/
def isoOfEquiv {V W : Type u} [ReflQuiver V] [ReflQuiver W] (e : V ≃ W)
    (he : ∀ (X Y : V), (X ⟶ Y) ≃ (e X ⟶ e Y))
    (h_id : ∀ (X : V), he _ _ (𝟙rq X) = ReflQuiver.id (obj := W) (e X)) :
    ReflQuiv.of V ≅ ReflQuiv.of W := isoOfQuivIso (Quiv.isoOfEquiv e he) h_id

end ReflQuiv

namespace ReflPrefunctor

/-- A refl prefunctor can be promoted to a functor if it respects composition. -/
/-
**CategoryTheory.ReflPrefunctor.toFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.ReflPrefunctor`。
形式化陈述：toFunctor {C D : Cat} (F : (ReflQuiv.of C) ⟶ (ReflQuiv.of D)) (hyp : foral
l {X Y Z : ↑C} (f : X ⟶ Y) (g : Y ⟶ Z), F.map (CategoryStruct.comp (obj
参数：F : (ReflQuiv.of C) ⟶ (ReflQuiv.of D)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A refl prefunctor can be promoted to a functor if it respects composition.
-/
def toFunctor {C D : Cat} (F : (ReflQuiv.of C) ⟶ (ReflQuiv.of D))
    (hyp : ∀ {X Y Z : ↑C} (f : X ⟶ Y) (g : Y ⟶ Z),
      F.map (CategoryStruct.comp (obj := C) f g) =
        CategoryStruct.comp (obj := D) (F.map f) (F.map g)) : C ⥤ D where
  obj := F.obj
  map := F.map
  map_id := F.map_id
  map_comp := hyp

end ReflPrefunctor

namespace Cat

variable (V : Type*) [ReflQuiver V]

/-- The hom relation that identifies the specified reflexivity arrows with the nil paths -/
/-
**CategoryTheory.Cat.FreeReflRel** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.Cat
`。
形式化陈述：(V : Type u_1) → [inst : CategoryTheory.ReflQuiver V] → (X Y : CategoryThe
ory.Paths V) → (X ⟶ Y) → (X ⟶ Y) → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The hom relation that identifies the specified reflexivity arrows with the nil p
aths
-/
inductive FreeReflRel : (X Y : Paths V) → (f g : X ⟶ Y) → Prop
  | mk {X : V} : FreeReflRel X X (Quiver.Hom.toPath (𝟙rq X)) .nil

/-- A reflexive quiver generates a free category, defined as a quotient of the free category
on its underlying quiver (called the "path category") by the hom relation that uses the specified
reflexivity arrows as the identity arrows. -/
/-
**CategoryTheory.Cat.FreeRefl** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Cat`。
形式化陈述：FreeRefl
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A reflexive quiver generates a free category, defined as a quotient of the free 
category
on its underlying quiver (called the "path category") by the hom relation that u
ses the specified
reflexivity arrows as the identity arrows.
-/
def FreeRefl := Quotient (C := Paths V) (FreeReflRel V)

namespace FreeRefl

variable {V}

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Cat.FreeRefl.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Cat.Fre
eRefl`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (FreeRefl V) :=
  inferInstanceAs (Category (Quotient _))

/-- Constructor for objects in the free category on a reflexive quiver. -/
/-
**CategoryTheory.Cat.FreeRefl.mk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Cat.F
reeRefl`。
形式化陈述：mk (v : V) : FreeRefl V
参数：v : V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for objects in the free category on a reflexive quiver.
-/
def mk (v : V) : FreeRefl V := (Quotient.functor _).obj v

/-- Induction principle for the objects of the free category on a reflexive quiver. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
/-
**CategoryTheory.Cat.FreeRefl.induction** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Cat.FreeRefl`。
形式化陈述：induction {motive : FreeRefl V -> Sort*} (mk : forall v, motive (mk v)) (x
 : FreeRefl V) : motive x
参数：mk : forall v, motive (mk v)；x : FreeRefl V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Induction principle for the objects of the free category on a reflexive quiver.
-/
def induction {motive : FreeRefl V → Sort*} (mk : ∀ v, motive (mk v)) (x : FreeRefl V) :
    motive x :=
  mk _

variable (V) in
/-- The quotient functor associated to a quotient category defines a natural map from the free
category on the underlying quiver of a refl quiver to the free category on the reflexive quiver. -/
/-
**CategoryTheory.Cat.FreeRefl.quotientFunctor** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Cat.FreeRefl`。
形式化陈述：quotientFunctor : Paths V ⥤ FreeRefl V
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The quotient functor associated to a quotient category defines a natural map fro
m the free
category on the underlying quiver of a refl quiver to the free category on the r
eflexive quiver.
-/
def quotientFunctor : Paths V ⥤ FreeRefl V :=
  Quotient.functor (C := Paths V) (FreeReflRel (V := V))
/-
**CategoryTheory.Cat.FreeRefl.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Cat.Fre
eRefl`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (FreeRefl.quotientFunctor V).Full :=
  Quotient.full_functor _

/-- Constructor for morphisms in `FreeRefl`. -/
/-
**CategoryTheory.Cat.FreeRefl.homMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Ca
t.FreeRefl`。
形式化陈述：homMk {v w : V} (f : v ⟶ w) : mk v ⟶ mk w
参数：f : v ⟶ w。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for morphisms in `FreeRefl`.
-/
def homMk {v w : V} (f : v ⟶ w) : mk v ⟶ mk w := (quotientFunctor V).map f.toPath

@[simp]
/-
**CategoryTheory.Cat.FreeRefl.homMk_id** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Cat.FreeRefl`。
形式化陈述：homMk_id (v : V) : homMk (𝟙rq v) = 𝟙 _
参数：v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Quotient.sound`：∀ {C : Type u_1} [inst : CategoryTheory.C
ategory.{v_1, u_1} C] (r : HomRel C) {a b : C} {f₁ f₂ : a ⟶ b},   r f₁ f₂ → (Cat
egoryTheory.Quotien…
-/
lemma homMk_id (v : V) : homMk (𝟙rq v) = 𝟙 _ :=
  Quotient.sound _ ⟨⟩

@[simp]
/-
**CategoryTheory.Cat.FreeRefl.quotientFunctor_map_nil** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Cat.FreeRefl`。
形式化陈述：quotientFunctor_map_nil (x : Paths V) : (quotientFunctor V).map (.nil : x 
⟶ x) = 𝟙 _
参数：x : Paths V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
-/
lemma quotientFunctor_map_nil (x : Paths V) :
    (quotientFunctor V).map (.nil : x ⟶ x) = 𝟙 _ :=
  Functor.map_id _ _

@[simp]
/-
**CategoryTheory.Cat.FreeRefl.quotientFunctor_map_cons** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Cat.FreeRefl`。
形式化陈述：quotientFunctor_map_cons {x y z : Paths V} (p : x ⟶ y) (q : Quiver.Hom (V
参数：p : x ⟶ y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma quotientFunctor_map_cons {x y z : Paths V}
    (p : x ⟶ y) (q : Quiver.Hom (V := V) y z) :
    (quotientFunctor V).map (p.cons q : x ⟶ z) =
      (quotientFunctor V).map p ≫ homMk q :=
  rfl

variable (V) in
/-- The property of morphisms in `FreeRefl V` which are of the form `homMk f`
for some morphism `f : x ⟶ y` in `V`. -/
/-
**CategoryTheory.Cat.FreeRefl.morphismPropertyHomMk** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Cat.FreeRefl`。
形式化陈述：morphismPropertyHomMk : MorphismProperty (FreeRefl V)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property of morphisms in `FreeRefl V` which are of the form `homMk f`
for some morphism `f : x ⟶ y` in `V`.
-/
def morphismPropertyHomMk : MorphismProperty (FreeRefl V) :=
    .ofHoms (fun (e : Σ (x y : V), x ⟶ y) ↦ homMk e.2.2)
/-
**CategoryTheory.Cat.FreeRefl.morphismPropertyHomMk_homMk** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Cat.FreeRefl`。
形式化陈述：morphismPropertyHomMk_homMk {x y : V} (e : x ⟶ y) : morphismPropertyHomMk 
V (homMk e)
参数：e : x ⟶ y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MorphismProperty.ofHoms_iff`：ofHoms_iff {ι : Type*} {X Y 
: ι -> C} (f : forall i, X i ⟶ Y i) {A B : C} (g : A ⟶ B) : ofHoms f g ↔ exists 
i, Arrow.mk g = Arrow.mk (f i)
-/
lemma morphismPropertyHomMk_homMk {x y : V} (e : x ⟶ y) :
    morphismPropertyHomMk V (homMk e) := by
  dsimp only [morphismPropertyHomMk]
  rw [MorphismProperty.ofHoms_iff]
  exact ⟨⟨x, y, e⟩, rfl⟩

@[elab_as_elim, induction_eliminator]
/-
**CategoryTheory.Cat.FreeRefl.hom_induction** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.Cat.FreeRefl`。
形式化陈述：hom_induction {motive : forall {x y : FreeRefl V} (_ : x ⟶ y), Prop} (id :
 forall (x : V), motive (homMk (𝟙rq x))) (comp_homMk : forall {x y z : V} (f : m
k x ⟶ mk y) (g : y ⟶ z), motive f -> motive (f ≫ homMk g)) {x y : FreeRefl V} (f
 : x ⟶ y) : motive f
参数：_ : x ⟶ y；id : forall (x : V), motive (homMk (𝟙rq x))；comp_homMk : forall {x 
y z : V} (f : mk x ⟶ mk y) (g : y ⟶ z), motive f -> motive (f ≫ homMk g)；f : x ⟶
 y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_surjective`：map_surjective (F : C ⥤ D) [Full 
F] : Function.Surjective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `CategoryTheory.Cat.FreeRefl.instFullPathsQuotientFunctor`：∀ {V : Type u_
1} [inst : CategoryTheory.ReflQuiver V], (CategoryTheory.Cat.FreeRefl.quotientFu
nctor V).Full
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Cat.FreeRefl.homMk_id`：homMk_id (v : V) : homMk (𝟙rq v) =
 𝟙 _
-/
lemma hom_induction {motive : ∀ {x y : FreeRefl V} (_ : x ⟶ y), Prop}
    (id : ∀ (x : V), motive (homMk (𝟙rq x)))
    (comp_homMk : ∀ {x y z : V} (f : mk x ⟶ mk y) (g : y ⟶ z),
      motive f → motive (f ≫ homMk g)) {x y : FreeRefl V} (f : x ⟶ y) :
  motive f := by
    induction x using induction with | _ x
    induction y using induction with | _ y
    obtain ⟨f, rfl⟩ := (quotientFunctor _).map_surjective f
    induction f with
    | nil => simpa using! id x
    | cons _ f h => simpa using! comp_homMk _ f h

open MorphismProperty in
/-
**CategoryTheory.Cat.FreeRefl.multiplicativeClosure_morphismPropertyHomMk** 是 Ma
thlib 中的一个引理，位于命名空间 `CategoryTheory.Cat.FreeRefl`。
形式化陈述：multiplicativeClosure_morphismPropertyHomMk : (morphismPropertyHomMk V).mu
ltiplicativeClosure = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `CategoryTheory.Cat.FreeRefl.hom_induction`：hom_induction {motive : foral
l {x y : FreeRefl V} (_ : x ⟶ y), Prop} (id : forall (x : V), motive (homMk (𝟙rq
 x))) (comp_homMk : forall {x y…
· 使用引理 `CategoryTheory.MorphismProperty.le_multiplicativeClosure`：le_multiplicat
iveClosure : W <= W.multiplicativeClosure
· 使用引理 `CategoryTheory.Cat.FreeRefl.morphismPropertyHomMk_homMk`：morphismPropert
yHomMk_homMk {x y : V} (e : x ⟶ y) : morphismPropertyHomMk V (homMk e)
· 使用引理 `CategoryTheory.MorphismProperty.comp_mem`：comp_mem (W : MorphismProperty
 C) [W.IsStableUnderComposition] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) 
(hg : W g) : W (f ≫ g)
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
· 使用定理 `CategoryTheory.MorphismProperty.instIsMultiplicativeMultiplicativeClosur
e`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (W : CategoryTheory.
MorphismProperty C),   W.multiplicativeClosure.IsMultiplicative
-/
lemma multiplicativeClosure_morphismPropertyHomMk :
    (morphismPropertyHomMk V).multiplicativeClosure = ⊤ :=
  le_antisymm (by simp) (by
    intro _ _ f hf
    clear hf
    induction f using hom_induction with
    | id => exact le_multiplicativeClosure _ _ (morphismPropertyHomMk_homMk _)
    | comp_homMk _ _ h =>
      exact comp_mem _ _ _ h (le_multiplicativeClosure _ _ (morphismPropertyHomMk_homMk _)))
/-
**CategoryTheory.Cat.FreeRefl.morphismProperty_eq_top** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Cat.FreeRefl`。
形式化陈述：morphismProperty_eq_top {W : MorphismProperty (FreeRefl V)} [W.IsMultiplic
ative] (hW : forall {x y : V} (e : x ⟶ y), W (homMk e)) : W = ⊤
参数：FreeRefl V；hW : forall {x y : V} (e : x ⟶ y), W (homMk e)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Cat.FreeRefl.multiplicativeClosure_morphismPropertyHomMk`
：multiplicativeClosure_morphismPropertyHomMk : (morphismPropertyHomMk V).multipl
icativeClosure = ⊤
· 使用引理 `CategoryTheory.MorphismProperty.multiplicativeClosure_le_iff`：multiplica
tiveClosure_le_iff (W' : MorphismProperty C) [W'.IsMultiplicative] : multiplicat
iveClosure W <= W' ↔ W <= W' where .trans h mp h
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma morphismProperty_eq_top {W : MorphismProperty (FreeRefl V)}
    [W.IsMultiplicative] (hW : ∀ {x y : V} (e : x ⟶ y), W (homMk e)) :
    W = ⊤ :=
  le_antisymm (by simp) (by
    rw [← multiplicativeClosure_morphismPropertyHomMk,
      MorphismProperty.multiplicativeClosure_le_iff]
    rintro _ _ _ ⟨h⟩
    apply hW)

section

variable {D : Type*} [Category* D] (F : V ⥤rq D)

set_option backward.isDefEq.respectTransparency.types false in
/-- Constructor for functors from `FreeRefl`.
(See also `lift'` for which the data is unbundled.) -/
/-
**CategoryTheory.Cat.FreeRefl.lift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Cat
.FreeRefl`。
形式化陈述：lift : FreeRefl V ⥤ D
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for functors from `FreeRefl`.
(See also `lift'` for which the data is unbundled.)
-/
def lift : FreeRefl V ⥤ D :=
  Quotient.lift _ (Paths.lift F.toPrefunctor) (by
    rintro _ _ _ _ ⟨h⟩
    simp)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.Cat.FreeRefl.lift_obj** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Cat.FreeRefl`。
形式化陈述：lift_obj (v : V) : (lift F).obj (mk v) = F.obj v
参数：v : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma lift_obj (v : V) : (lift F).obj (mk v) = F.obj v := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.Cat.FreeRefl.lift_map** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Cat.FreeRefl`。
形式化陈述：lift_map {v w : V} (f : v ⟶ w) : (lift F).map (homMk f) = F.map f
参数：f : v ⟶ w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma lift_map {v w : V} (f : v ⟶ w) : (lift F).map (homMk f) = F.map f :=
  Category.id_comp _

end

section

variable {D : Type*} [Category* D]
  (obj : V → D) (map : ∀ {v w : V}, (v ⟶ w) → (obj v ⟶ obj w))
  (map_id : ∀ (v : V), map (𝟙rq v) = 𝟙 _)

set_option backward.isDefEq.respectTransparency.types false in
/-- Constructor for functors from `FreeRefl`.
(See also `lift` for which the data is bundled.) -/
/-
**CategoryTheory.Cat.FreeRefl.lift'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Ca
t.FreeRefl`。
形式化陈述：lift' : FreeRefl V ⥤ D
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for functors from `FreeRefl`.
(See also `lift` for which the data is bundled.)
-/
def lift' : FreeRefl V ⥤ D :=
  lift { obj := obj, map := map, map_id := map_id }

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.Cat.FreeRefl.lift'_obj** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Cat.FreeRefl`。
形式化陈述：∀ {V : Type u_1} [inst : CategoryTheory.ReflQuiver V] {D : Type u_2} [inst
_1 : CategoryTheory.Category.{v_1, u_2} D]   (obj : V → D) (map : {v w : V} → (v
 ⟶ w) → (obj v ⟶ obj w))   (map_id : ∀ (v : V), map (CategoryTheory.ReflQuiver.i
d v) = CategoryTheory.CategoryStruct.id (obj v)) (v : V),   (CategoryTheory.Cat.
FreeRefl.lift' obj (fun {v w} => map) map_id).obj (CategoryTheory.Cat.FreeRefl.m
k v) = obj v
参数：obj : V → D；map : {v w : V} → (v ⟶ w) → (obj v ⟶ obj w)；map_id : ∀ (v : V), m
ap (CategoryTheory.ReflQuiver.id v) = CategoryTheory.CategoryStruct.id (obj v)；v
 : V；CategoryTheory.Cat.FreeRefl.lift' obj (fun {v w} => map) map_id；CategoryThe
ory.Cat.FreeRefl.mk v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma lift'_obj (v : V) :
    (lift' obj map map_id).obj (mk v) = obj v := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.Cat.FreeRefl.lift'_map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Cat.FreeRefl`。
形式化陈述：∀ {V : Type u_1} [inst : CategoryTheory.ReflQuiver V] {D : Type u_2} [inst
_1 : CategoryTheory.Category.{v_1, u_2} D]   (obj : V → D) (map : {v w : V} → (v
 ⟶ w) → (obj v ⟶ obj w))   (map_id : ∀ (v : V), map (CategoryTheory.ReflQuiver.i
d v) = CategoryTheory.CategoryStruct.id (obj v)) {v w : V}   (f : v ⟶ w),   (Cat
egoryTheory.Cat.FreeRefl.lift' obj (fun {v w} => map) map_id).map (CategoryTheor
y.Cat.FreeRefl.homMk f) = map f
参数：obj : V → D；map : {v w : V} → (v ⟶ w) → (obj v ⟶ obj w)；map_id : ∀ (v : V), m
ap (CategoryTheory.ReflQuiver.id v) = CategoryTheory.CategoryStruct.id (obj v)；f
 : v ⟶ w；CategoryTheory.Cat.FreeRefl.lift' obj (fun {v w} => map) map_id；Categor
yTheory.Cat.FreeRefl.homMk f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Cat.FreeRefl.lift_map`：lift_map {v w : V} (f : v ⟶ w) : (
lift F).map (homMk f) = F.map f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lift'_map {v w : V} (f : v ⟶ w) :
    (lift' obj map map_id).map (homMk f) = map f := by
  simp [lift']

end

/-- This is a specialization of `Quotient.lift_unique'` rather than `Quotient.lift_unique`, hence
the prime in the name. -/
/-
**CategoryTheory.Cat.FreeRefl.lift_unique'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Cat.FreeRefl`。
形式化陈述：lift_unique' {V} [ReflQuiver V] {D} [Category* D] (F₁ F₂ : FreeRefl V ⥤ D)
 (h : quotientFunctor V ⋙ F₁ = quotientFunctor V ⋙ F₂) : F₁ = F₂
参数：F₁ F₂ : FreeRefl V ⥤ D；h : quotientFunctor V ⋙ F₁ = quotientFunctor V ⋙ F₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Quotient.lift_unique'`：lift_unique' (F₁ F₂ : Quotient r ⥤
 D) (h : functor r ⋙ F₁ = functor r ⋙ F₂) : F₁ = F₂

--- 原说明 ---
This is a specialization of `Quotient.lift_unique'` rather than `Quotient.lift_u
nique`, hence
the prime in the name.
-/
theorem lift_unique' {V} [ReflQuiver V] {D} [Category* D] (F₁ F₂ : FreeRefl V ⥤ D)
    (h : quotientFunctor V ⋙ F₁ = quotientFunctor V ⋙ F₂) :
    F₁ = F₂ :=
  Quotient.lift_unique' (C := Cat.free.obj (Quiv.of V)) (FreeReflRel (V := V)) _ _ h
/-
**CategoryTheory.Cat.FreeRefl.functor_ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Cat.FreeRefl`。
形式化陈述：functor_ext {D : Type*} [Category* D] {F G : FreeRefl V ⥤ D} (h₁ : forall 
v, F.obj (mk v) = G.obj (mk v)) (h₂ : forall {v w : V} (f : v ⟶ w), F.map (homMk
 f) = eqToHom (h₁ v) ≫ G.map (homMk f) ≫ eqToHom (h₁ w).symm) : F = G
参数：h₁ : forall v, F.obj (mk v) = G.obj (mk v)；h₂ : forall {v w : V} (f : v ⟶ w),
 F.map (homMk f) = eqToHom (h₁ v) ≫ G.map (homMk f) ≫ eqToHom (h₁ w).symm。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Cat.FreeRefl.lift_unique'`：lift_unique' {V} [ReflQuiver V
] {D} [Category* D] (F₁ F₂ : FreeRefl V ⥤ D) (h : quotientFunctor V ⋙ F₁ = quoti
entFunctor V ⋙ F₂) : F₁ = F₂
· 使用定理 `CategoryTheory.Paths.ext_functor`：ext_functor {C} [Category* C] {F G : P
aths V ⥤ C} (h_obj : F.obj = G.obj) (h : forall (a b : V) (e : a ⟶ b), F.map e.t
oPath = eqToHom (congr…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma functor_ext {D : Type*} [Category* D]
    {F G : FreeRefl V ⥤ D} (h₁ : ∀ v, F.obj (mk v) = G.obj (mk v))
    (h₂ : ∀ {v w : V} (f : v ⟶ w), F.map (homMk f) =
      eqToHom (h₁ v) ≫ G.map (homMk f) ≫ eqToHom (h₁ w).symm) : F = G :=
  lift_unique' _ _ (Paths.ext_functor (by ext; apply h₁) (fun _ _ _ ↦ h₂ _))

@[simp]
/-
**CategoryTheory.Cat.FreeRefl.quotientFunctor_map_id** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Cat.FreeRefl`。
形式化陈述：quotientFunctor_map_id (V) [ReflQuiver V] (X : V) : (FreeRefl.quotientFunc
tor V).map (𝟙rq X).toPath = 𝟙 _
参数：V；X : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Quotient.sound`：∀ {C : Type u_1} [inst : CategoryTheory.C
ategory.{v_1, u_1} C] (r : HomRel C) {a b : C} {f₁ f₂ : a ⟶ b},   r f₁ f₂ → (Cat
egoryTheory.Quotien…
-/
lemma quotientFunctor_map_id (V) [ReflQuiver V] (X : V) :
    (FreeRefl.quotientFunctor V).map (𝟙rq X).toPath = 𝟙 _ :=
  Quotient.sound _ .mk

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Cat.FreeRefl.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Cat.Fre
eRefl`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (V : Type*) [ReflQuiver V] [Unique V] : Unique (FreeRefl V) :=
  inferInstanceAs (Unique (Quotient _))

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Cat.FreeRefl.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Cat.Fre
eRefl`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (V : Type*) [ReflQuiver V] [Unique V]
    [∀ (x y : V), Unique (x ⟶ y)] (x y : FreeRefl V) :
    Unique (x ⟶ y) where
  default := homMk default
  uniq f := by
    induction f using hom_induction with
    | id => congr; subsingleton
    | @comp_homMk x y z _ g h =>
      obtain rfl := Subsingleton.elim y z
      obtain rfl := Subsingleton.elim g (𝟙rq _)
      simp [h]
/-
**CategoryTheory.Cat.FreeRefl.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Cat.Fre
eRefl`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (V : Type*) [ReflQuiver V] [Unique V]
    [∀ (x y : V), Subsingleton (x ⟶ y)] (x y : FreeRefl V) :
    Subsingleton (x ⟶ y) :=
  letI (x y : V) : Unique (x ⟶ y) := by
    obtain rfl : x = y := by subsingleton
    exact (unique_iff_subsingleton_and_nonempty _ |>.mpr ⟨inferInstance, ⟨𝟙rq _⟩⟩).some
  inferInstance

end FreeRefl

/-- Given a refl quiver `V`, this is the refl functor `V ⥤rq FreeRefl V` which
is the counit of the adjunction between reflexive quivers and categories. -/
@[simps]
/-
**CategoryTheory.Cat.toFreeRefl** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Cat`。
形式化陈述：toFreeRefl : V ⥤rq FreeRefl V where obj
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a refl quiver `V`, this is the refl functor `V ⥤rq FreeRefl V` which
is the counit of the adjunction between reflexive quivers and categories.
-/
def toFreeRefl : V ⥤rq FreeRefl V where
  obj := .mk
  map := FreeRefl.homMk

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
attribute [local simp] Functor.toReflPrefunctor in
variable {V} in
/-- Constructor for functors from `FreeRefl`. -/
/-
**CategoryTheory.Cat.FreeRefl.lift_spec** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Cat.FreeRefl`。
形式化陈述：∀ {V : Type u_1} [inst : CategoryTheory.ReflQuiver V] {D : Type u_2} [inst
_1 : CategoryTheory.Category.{v_1, u_2} D]   (F : V ⥤rq D), CategoryTheory.Cat.t
oFreeRefl V ⋙rq (CategoryTheory.Cat.FreeRefl.lift F).toReflPrefunctor = F
参数：F : V ⥤rq D；CategoryTheory.Cat.FreeRefl.lift F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ReflPrefunctor.ext`：ext {V : Type u} [ReflQuiver.{v₁} V] 
{W : Type u₂} [ReflQuiver.{v₂} W] {F G : ReflPrefunctor V W} (h_obj : forall X, 
F.obj X = G.obj X) (h_m…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Cat.FreeRefl.lift_map`：lift_map {v w : V} (f : v ⟶ w) : (
lift F).map (homMk f) = F.map f
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
Constructor for functors from `FreeRefl`.
-/
lemma FreeRefl.lift_spec {D : Type*} [Category* D] (F : V ⥤rq D) :
    Cat.toFreeRefl V ⋙rq (Cat.FreeRefl.lift F).toReflPrefunctor = F :=
  ReflPrefunctor.ext (fun v ↦ by simp) (by simp)

variable {V} {W : Type*} [ReflQuiver W] (F : V ⥤rq W)
set_option backward.isDefEq.respectTransparency.types false in
/-- A refl prefunctor `V ⥤rq W` induces a functor `FreeRefl V ⥤ FreeRefl W` defined using
`freeMap` and the quotient functor. -/
/-
**CategoryTheory.Cat.freeReflMap** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Cat`。
形式化陈述：freeReflMap : FreeRefl V ⥤ FreeRefl W
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A refl prefunctor `V ⥤rq W` induces a functor `FreeRefl V ⥤ FreeRefl W` defined 
using
`freeMap` and the quotient functor.
-/
def freeReflMap : FreeRefl V ⥤ FreeRefl W :=
  FreeRefl.lift' (fun v ↦ .mk (F.obj v)) (fun f ↦ FreeRefl.homMk (F.map f))
    (fun v ↦ by simp)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.Cat.freeReflMap_obj** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.C
at`。
形式化陈述：freeReflMap_obj (v : V) : (freeReflMap F).obj (.mk v) = .mk (F.obj v)
参数：v : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma freeReflMap_obj (v : V) : (freeReflMap F).obj (.mk v) = .mk (F.obj v) := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.Cat.freeReflMap_map** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.C
at`。
形式化陈述：freeReflMap_map {v w : V} (f : v ⟶ w) : (freeReflMap F).map (FreeRefl.homM
k f) = FreeRefl.homMk (F.map f)
参数：f : v ⟶ w。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma freeReflMap_map {v w : V} (f : v ⟶ w) :
    (freeReflMap F).map (FreeRefl.homMk f) = FreeRefl.homMk (F.map f) := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Cat.freeReflMap_naturality** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Cat`。
形式化陈述：freeReflMap_naturality {V W : Type*} [ReflQuiver.{v₁} V] [ReflQuiver.{v₂} 
W] (F : V ⥤rq W) : FreeRefl.quotientFunctor V ⋙ freeReflMap F = freeMap F.toPref
unctor ⋙ FreeRefl.quotientFunctor W
参数：F : V ⥤rq W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Paths.ext_functor`：ext_functor {C} [Category* C] {F G : P
aths V ⥤ C} (h_obj : F.obj = G.obj) (h : forall (a b : V) (e : a ⟶ b), F.map e.t
oPath = eqToHom (congr…
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem freeReflMap_naturality
    {V W : Type*} [ReflQuiver.{v₁} V] [ReflQuiver.{v₂} W] (F : V ⥤rq W) :
    FreeRefl.quotientFunctor V ⋙ freeReflMap F =
    freeMap F.toPrefunctor ⋙ FreeRefl.quotientFunctor W :=
  Paths.ext_functor rfl (by cat_disch)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The functor sending a reflexive quiver to the free category it generates, a quotient of
its path category -/
@[simps]
/-
**CategoryTheory.Cat.freeRefl** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Cat`。
形式化陈述：freeRefl : ReflQuiv.{v, u} ⥤ Cat.{max u v, u} where obj V
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor sending a reflexive quiver to the free category it generates, a quot
ient of
its path category
-/
def freeRefl : ReflQuiv.{v, u} ⥤ Cat.{max u v, u} where
  obj V := Cat.of (FreeRefl V)
  map F := (freeReflMap F).toCatHom
  map_id X := by ext1; exact FreeRefl.functor_ext (by simp) (by simp)
  map_comp {X Y Z} f g := by ext1; exact FreeRefl.functor_ext (by simp) (by simp)

set_option backward.isDefEq.respectTransparency.types false in
/-- We will make use of the natural quotient map from the free category on the underlying
quiver of a refl quiver to the free category on the reflexive quiver. -/
/-
**CategoryTheory.Cat.freeReflNatTrans** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Cat`。
形式化陈述：freeReflNatTrans : ReflQuiv.forgetToQuiv ⋙ Cat.free ⟶ freeRefl where app V
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We will make use of the natural quotient map from the free category on the under
lying
quiver of a refl quiver to the free category on the reflexive quiver.
-/
def freeReflNatTrans : ReflQuiv.forgetToQuiv ⋙ Cat.free ⟶ freeRefl where
  app V := (FreeRefl.quotientFunctor V).toCatHom
  naturality v w f := by
    ext1; exact Paths.ext_functor (V := Quiv.of v) (by cat_disch) (by cat_disch)

end Cat

namespace ReflQuiv
open Category

namespace adj

variable {V W : Type*} [ReflQuiver W] [ReflQuiver V]
  {C D : Type*} [Category* C] [Category* D]

set_option backward.isDefEq.respectTransparency false in
/-- Given a reflexive quiver `V` and a category `C`, this is the bijection
between functors `Cat.FreeRefl V ⥤ C` and refl functors `V ⥤rq C`. -/
@[simps]
/-
**CategoryTheory.ReflQuiv.adj.homEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.ReflQuiv.adj`。
形式化陈述：homEquiv : (Cat.FreeRefl V ⥤ C) ≃ V ⥤rq C where toFun F
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Cat.FreeRefl.lift_spec`：∀ {V : Type u_1} [inst : Category
Theory.ReflQuiver V] {D : Type u_2} [inst_1 : CategoryTheory.Category.{v_1, u_2}
 D]   (F : V ⥤rq D), Catego…

--- 原说明 ---
Given a reflexive quiver `V` and a category `C`, this is the bijection
between functors `Cat.FreeRefl V ⥤ C` and refl functors `V ⥤rq C`.
-/
def homEquiv : (Cat.FreeRefl V ⥤ C) ≃ V ⥤rq C where
  toFun F := Cat.toFreeRefl V ⋙rq F.toReflPrefunctor
  invFun := Cat.FreeRefl.lift
  left_inv F := Cat.FreeRefl.functor_ext (by cat_disch) (by cat_disch)
  right_inv := Cat.FreeRefl.lift_spec

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.ReflQuiv.adj.homEquiv_naturality_left_symm** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.ReflQuiv.adj`。
形式化陈述：homEquiv_naturality_left_symm (F : V ⥤rq W) (G : W ⥤rq C) : homEquiv.symm 
(F ⋙rq G) = Cat.freeReflMap F ⋙ homEquiv.symm G
参数：F : V ⥤rq W；G : W ⥤rq C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Cat.FreeRefl.functor_ext`：functor_ext {D : Type*} [Catego
ry* D] {F G : FreeRefl V ⥤ D} (h₁ : forall v, F.obj (mk v) = G.obj (mk v)) (h₂ :
 forall {v w : V} (f : v ⟶ w)…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Cat.FreeRefl.lift_map`：lift_map {v w : V} (f : v ⟶ w) : (
lift F).map (homMk f) = F.map f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.eqToHom_naturality`：eqToHom_naturality {f g : β -> C} (z 
: forall b, f b ⟶ g b) {j j' : β} (w : j = j') : z j ≫ eqToHom (by simp [w]) = e
qToHom (by simp [w]) ≫ …
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma homEquiv_naturality_left_symm (F : V ⥤rq W) (G : W ⥤rq C) :
    homEquiv.symm (F ⋙rq G) = Cat.freeReflMap F ⋙ homEquiv.symm G :=
  Cat.FreeRefl.functor_ext (by simp) (by simp)
/-
**CategoryTheory.ReflQuiv.adj.homEquiv_naturality_right** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.ReflQuiv.adj`。
形式化陈述：homEquiv_naturality_right (F : Cat.FreeRefl V ⥤ C) (G : C ⥤ D) : homEquiv 
(F ⋙ G) = homEquiv F ⋙rq G.toReflPrefunctor
参数：F : Cat.FreeRefl V ⥤ C；G : C ⥤ D。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homEquiv_naturality_right (F : Cat.FreeRefl V ⥤ C) (G : C ⥤ D) :
    homEquiv (F ⋙ G) = homEquiv F ⋙rq G.toReflPrefunctor := rfl

end adj

/--
The adjunction between forming the free category on a reflexive quiver, and forgetting a category
to a reflexive quiver.
-/
/-
**CategoryTheory.ReflQuiv.adj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.ReflQuiv
`。
形式化陈述：adj : Cat.freeRefl.{max u v, u} ⊣ ReflQuiv.forget
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
The adjunction between forming the free category on a reflexive quiver, and forg
etting a category
to a reflexive quiver.
-/
def adj : Cat.freeRefl.{max u v, u} ⊣ ReflQuiv.forget :=
  Adjunction.mkOfHomEquiv
    { homEquiv _ _ := (Cat.Hom.equivFunctor ..).trans adj.homEquiv
      homEquiv_naturality_left_symm _ _ := by ext1; exact adj.homEquiv_naturality_left_symm _ _
      homEquiv_naturality_right _ _ := adj.homEquiv_naturality_right _ _ }

@[simp]
/-
**CategoryTheory.ReflQuiv.adj_unit_app** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.ReflQuiv`。
形式化陈述：adj_unit_app (V) [ReflQuiver V] : adj.unit.app (ReflQuiv.of V) = Cat.toFre
eRefl V
参数：V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma adj_unit_app (V) [ReflQuiver V] :
    adj.unit.app (ReflQuiv.of V) = Cat.toFreeRefl V := rfl
/-
**CategoryTheory.ReflQuiv.adj_counit_app** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.ReflQuiv`。
形式化陈述：adj_counit_app (D : Type u) [Category.{max u v} D] : adj.counit.app (Cat.o
f D) = (Cat.FreeRefl.lift (𝟭rq D)).toCatHom
参数：D : Type u。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma adj_counit_app (D : Type u) [Category.{max u v} D] :
    adj.counit.app (Cat.of D) = (Cat.FreeRefl.lift (𝟭rq D)).toCatHom := rfl

variable {V : Type*} [ReflQuiver V]
  {C : Type*} [Category* C]
/-
**CategoryTheory.ReflQuiv.adj_homEquiv** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.ReflQuiv`。
形式化陈述：adj_homEquiv (V : Type u) [ReflQuiver.{max u v} V] (C : Type u) [Category.
{max u v} C] : (adj).homEquiv (.of V) (.of C) = (Cat.Hom.equivFunctor _ _).trans
 adj.homEquiv
参数：V : Type u；C : Type u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `CategoryTheory.Adjunction.homEquiv_unit`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F : CategoryTheor…
-/
lemma adj_homEquiv (V : Type u) [ReflQuiver.{max u v} V] (C : Type u) [Category.{max u v} C] :
    (adj).homEquiv (.of V) (.of C) = (Cat.Hom.equivFunctor _ _).trans adj.homEquiv := by
  ext F
  apply Adjunction.homEquiv_unit
/-
**CategoryTheory.ReflQuiv.adj.unit.map_app_eq** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.ReflQuiv.adj.unit`。
形式化陈述：∀ (V : Type u) [inst : CategoryTheory.ReflQuiver V],   (CategoryTheory.Ref
lQuiv.adj.unit.app (CategoryTheory.ReflQuiv.of V)).toPrefunctor =     CategoryTh
eory.Quiv.adj.unit.app (CategoryTheory.Quiv.of V) ⋙q       (CategoryTheory.Cat.F
reeRefl.quotientFunctor V).toPrefunctor
参数：V : Type u；CategoryTheory.ReflQuiv.adj.unit.app (CategoryTheory.ReflQuiv.of V
)；CategoryTheory.Quiv.of V；CategoryTheory.Cat.FreeRefl.quotientFunctor V。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma adj.unit.map_app_eq (V : Type u) [ReflQuiver.{max u v} V] :
    (adj.unit.app (.of V)).toPrefunctor = Quiv.adj.unit.app (.of V) ⋙q
      (Cat.FreeRefl.quotientFunctor V).toPrefunctor := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ReflQuiv.adj.counit.comp_app_eq** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.ReflQuiv.adj.counit`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.Category.{max u v, u} C],   (Categor
yTheory.Cat.FreeRefl.quotientFunctor C).comp       (CategoryTheory.ReflQuiv.adj.
counit.app (CategoryTheory.Cat.of C)).toFunctor =     CategoryTheory.pathComposi
tion C
参数：C : Type u；CategoryTheory.Cat.FreeRefl.quotientFunctor C；CategoryTheory.ReflQ
uiv.adj.counit.app (CategoryTheory.Cat.of C)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Paths.ext_functor`：ext_functor {C} [Category* C] {F G : P
aths V ⥤ C} (h_obj : F.obj = G.obj) (h : forall (a b : V) (e : a ⟶ b), F.map e.t
oPath = eqToHom (congr…
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.composePath_toPath`：composePath_toPath {X Y : C} (f : X ⟶
 Y) : composePath f.toPath = f
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用引理 `CategoryTheory.Cat.FreeRefl.lift_map`：lift_map {v w : V} (f : v ⟶ w) : (
lift F).map (homMk f) = F.map f
-/
lemma adj.counit.comp_app_eq (C : Type u) [Category.{max u v} C] :
    Cat.FreeRefl.quotientFunctor C ⋙ (adj.counit.app (.of C)).toFunctor =
      pathComposition _ :=
  Paths.ext_functor rfl (fun _ _ f ↦ by
    dsimp
    simp only [adj_counit_app, composePath_toPath, comp_id, id_comp]
    apply Cat.FreeRefl.lift_map)

end ReflQuiv

end CategoryTheory

