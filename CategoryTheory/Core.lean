/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Control.EquivFunctor

/-!
# The core of a category

The core of a category `C` is the (non-full) subcategory of `C` consisting of all objects,
and all isomorphisms. We construct it as a `CategoryTheory.Groupoid`.

`CategoryTheory.Core.inclusion : Core C ⥤ C` gives the faithful inclusion into the original
category.

Any functor `F` from a groupoid `G` into `C` factors through `CategoryTheory.Core C`,
but this is not functorial with respect to `F`.
-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

namespace CategoryTheory

open CategoryTheory.Functor

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

-- morphism levels before object levels. See note [category theory universes].
/-- The core of a category C is the groupoid whose morphisms are all the
isomorphisms of C. -/
/-
**CategoryTheory.Core** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：Type u₁ → Type u₁
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The core of a category C is the groupoid whose morphisms are all the
isomorphisms of C.
-/
structure Core (C : Type u₁) where
  /-- The object of the base category underlying an object in `Core C`. -/
  of : C

variable {C : Type u₁} [Category.{v₁} C]

/-- The hom-type between two objects of `Core C`.
It is defined as a one-field structure to prevent defeq abuses. -/
@[ext]
/-
**CategoryTheory.CoreHom** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：{C : Type u₁} → [CategoryTheory.Category.{v₁, u₁} C] → CategoryTheory.Core
 C → CategoryTheory.Core C → Type v₁
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The hom-type between two objects of `Core C`.
It is defined as a one-field structure to prevent defeq abuses.
-/
structure CoreHom (X Y : Core C) where
  /-- The isomorphism of objects of `C` underlying a morphism in `Core C`. -/
  iso : X.of ≅ Y.of

@[simps! id_iso inv_iso]
/-
**CategoryTheory.coreCategory** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：coreCategory : Groupoid.{v₁} (Core C) where Hom (X Y : Core C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance coreCategory : Groupoid.{v₁} (Core C) where
  Hom (X Y : Core C) := CoreHom X Y
  id (X : Core C) := .mk <| Iso.refl X.of
  comp f g := .mk <| Iso.trans f.iso g.iso
  inv {_ _} f := .mk <| Iso.symm f.iso

@[simp]
/-
**CategoryTheory.coreCategory_comp_iso** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
`。
形式化陈述：coreCategory_comp_iso {x y z : Core C} (f : x ⟶ y) (g : y ⟶ z) : (f ≫ g).i
so = f.iso ≪≫ g.iso
参数：f : x ⟶ y；g : y ⟶ z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coreCategory_comp_iso {x y z : Core C} (f : x ⟶ y) (g : y ⟶ z) :
    (f ≫ g).iso = f.iso ≪≫ g.iso := rfl

namespace Core

variable (C) in
/-- The core of a category is naturally included in the category. -/
@[simps!]
/-
**CategoryTheory.Core.inclusion** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Core`。
形式化陈述：inclusion : Core C ⥤ C where obj
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The core of a category is naturally included in the category.
-/
def inclusion : Core C ⥤ C where
  obj := of
  map f := f.iso.hom

@[ext]
/-
**CategoryTheory.Core.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Core`。
形式化陈述：hom_ext {X Y : Core C} {f g : X ⟶ Y} (h : f.iso.hom = g.iso.hom) : f = g
参数：h : f.iso.hom = g.iso.hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CoreHom.ext`：∀ {C : Type u₁} {inst : CategoryTheory.Categ
ory.{v₁, u₁} C} {X Y : CategoryTheory.Core C}   {x y : CategoryTheory.CoreHom X 
Y}, x.iso = y.is…
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
-/
theorem hom_ext {X Y : Core C} {f g : X ⟶ Y} (h : f.iso.hom = g.iso.hom) :
    f = g := by
  apply CoreHom.ext
  exact Iso.ext h

/-- Construct an isomorphism in `Core C` from an isomorphism in `C`. -/
@[simps! hom_iso inv_iso]
/-
**CategoryTheory.Core.isoMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Core`。
形式化陈述：isoMk {x y : Core C} (e : x.of ≅ y.of) : x ≅ y
参数：e : x.of ≅ y.of。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Construct an isomorphism in `Core C` from an isomorphism in `C`.
-/
def isoMk {x y : Core C} (e : x.of ≅ y.of) : x ≅ y :=
  Groupoid.isoEquivHom _ _ |>.symm (.mk e)

variable (C)
/-
**CategoryTheory.Core.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Core`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (inclusion C).Faithful where

variable {C} {G : Type u₂} [Groupoid.{v₂} G]

-- Note that this function is not functorial
-- (consider the two functors from [0] to [1], and the natural transformation between them).
/-- A functor from a groupoid to a category C factors through the core of C. -/
@[simps!]
/-
**CategoryTheory.Core.functorToCore** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Co
re`。
形式化陈述：functorToCore (F : G ⥤ C) : G ⥤ Core C where obj X
参数：F : G ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor from a groupoid to a category C factors through the core of C.
-/
def functorToCore (F : G ⥤ C) : G ⥤ Core C where
  obj X := .mk <| F.obj X
  map f := .mk <| { hom := F.map f, inv := F.map (Groupoid.inv f) }

/-- We can functorially associate to any functor from a groupoid to the core of a category `C`,
a functor from the groupoid to `C`, simply by composing with the embedding `Core C ⥤ C`.
-/
@[simps!]
/-
**CategoryTheory.Core.forgetFunctorToCore** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Core`。
形式化陈述：forgetFunctorToCore : (G ⥤ Core C) ⥤ G ⥤ C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We can functorially associate to any functor from a groupoid to the core of a ca
tegory `C`,
a functor from the groupoid to `C`, simply by composing with the embedding `Core
 C ⥤ C`.
-/
def forgetFunctorToCore : (G ⥤ Core C) ⥤ G ⥤ C :=
  (whiskeringRight _ _ _).obj (inclusion C)

end Core

section

namespace Functor

variable {D : Type u₂} [Category.{v₂} D]

/-- A functor `C ⥤ D` induces a functor `Core C ⥤ Core D`. -/
@[simps!]
/-
**CategoryTheory.Functor.core** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor`
。
形式化陈述：core (F : C ⥤ D) : Core C ⥤ Core D
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `C ⥤ D` induces a functor `Core C ⥤ Core D`.
-/
def core (F : C ⥤ D) : Core C ⥤ Core D := Core.functorToCore (Core.inclusion _ ⋙ F)

variable (C) in
/-- The core of the identity functor is the identity functor on the cores. -/
@[simps!]
/-
**CategoryTheory.Functor.coreId** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functo
r`。
形式化陈述：coreId : (𝟭 C).core ≅ 𝟭 (Core C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The core of the identity functor is the identity functor on the cores.
-/
def coreId : (𝟭 C).core ≅ 𝟭 (Core C) := Iso.refl _

/-- The core of the composition of F and G is the composition of the cores. -/
@[simps!]
/-
**CategoryTheory.Functor.coreComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Func
tor`。
形式化陈述：coreComp {E : Type u₃} [Category.{v₃} E] (F : C ⥤ D) (G : D ⥤ E) : (F ⋙ G)
.core ≅ F.core ⋙ G.core
参数：F : C ⥤ D；G : D ⥤ E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The core of the composition of F and G is the composition of the cores.
-/
def coreComp {E : Type u₃} [Category.{v₃} E] (F : C ⥤ D) (G : D ⥤ E) :
    (F ⋙ G).core ≅ F.core ⋙ G.core := Iso.refl _

/-- The natural isomorphism
```
                  F.core
            Core C ⥤ Core D
 inclusion C  ‖          ‖  inclusion D
              V          V
              C    ⥤    D
                    F
```
thought of as pseudonaturality of `inclusion`,
when viewing `Core` as a pseudofunctor.
-/
@[simps!]
/-
**CategoryTheory.Functor.coreCompInclusionIso** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Functor`。
形式化陈述：coreCompInclusionIso (F : C ⥤ D) : F.core ⋙ Core.inclusion D ≅ Core.inclus
ion C ⋙ F
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isomorphism
```
                  F.core
            Core C ⥤ Core D
 inclusion C  ‖          ‖  inclusion D
              V          V
              C    ⥤    D
                    F
```
thought of as pseudonaturality of `inclusion`,
when viewing `Core` as a pseudofunctor.
-/
def coreCompInclusionIso (F : C ⥤ D) :
    F.core ⋙ Core.inclusion D ≅ Core.inclusion C ⋙ F :=
  Iso.refl _
/-
**CategoryTheory.Functor.core_comp_inclusion** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Functor`。
形式化陈述：core_comp_inclusion (F : C ⥤ D) : F.core ⋙ Core.inclusion D = Core.inclusi
on C ⋙ F
参数：F : C ⥤ D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.ext_of_iso`：ext_of_iso {F G : C ⥤ D} (e : F ≅ G) 
(hobj : forall X, F.obj X = G.obj X) (happ : forall X, e.hom.app X = eqToHom (ho
bj X)
-/
lemma core_comp_inclusion (F : C ⥤ D) :
    F.core ⋙ Core.inclusion D = Core.inclusion C ⋙ F :=
  Functor.ext_of_iso (coreCompInclusionIso F) (by cat_disch)

end Functor

namespace Iso

variable {D : Type u₂} [Category.{v₂} D]

set_option backward.isDefEq.respectTransparency.types false in
/-- A natural isomorphism of functors induces a natural isomorphism between their cores. -/
@[simps!]
/-
**CategoryTheory.Iso.core** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：core {F G : C ⥤ D} (α : F ≅ G) : F.core ≅ G.core
参数：α : F ≅ G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
A natural isomorphism of functors induces a natural isomorphism between their co
res.
-/
def core {F G : C ⥤ D} (α : F ≅ G) : F.core ≅ G.core :=
  NatIso.ofComponents
    (fun x ↦ Groupoid.isoEquivHom _ _ |>.symm <| .mk <| α.app x.of)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.Iso.coreComp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：coreComp {F G H : C ⥤ D} (α : F ≅ G) (β : G ≅ H) : (α ≪≫ β).core = α.core 
≪≫ β.core
参数：α : F ≅ G；β : G ≅ H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coreComp {F G H : C ⥤ D} (α : F ≅ G) (β : G ≅ H) : (α ≪≫ β).core = α.core ≪≫ β.core := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.Iso.coreId** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：coreId {F : C ⥤ D} : (Iso.refl F).core = Iso.refl F.core
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coreId {F : C ⥤ D} : (Iso.refl F).core = Iso.refl F.core := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Iso.coreWhiskerLeft** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.I
so`。
形式化陈述：coreWhiskerLeft {E : Type u₃} [Category.{v₃} E] (F : C ⥤ D) {G H : D ⥤ E} 
(η : G ≅ H) : (isoWhiskerLeft F η).core = F.coreComp G ≪≫ isoWhiskerLeft F.core 
η.core ≪≫ (F.coreComp H).symm
参数：F : C ⥤ D；η : G ≅ H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Core.hom_ext`：hom_ext {X Y : Core C} {f g : X ⟶ Y} (h : f
.iso.hom = g.iso.hom) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coreWhiskerLeft {E : Type u₃} [Category.{v₃} E] (F : C ⥤ D) {G H : D ⥤ E} (η : G ≅ H) :
    (isoWhiskerLeft F η).core =
    F.coreComp G ≪≫ isoWhiskerLeft F.core η.core ≪≫ (F.coreComp H).symm := by
  cat_disch

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Iso.coreWhiskerRight** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
Iso`。
形式化陈述：coreWhiskerRight {E : Type u₃} [Category.{v₃} E] {F G : C ⥤ D} (η : F ≅ G)
 (H : D ⥤ E) : (isoWhiskerRight η H).core = F.coreComp H ≪≫ isoWhiskerRight η.co
re H.core ≪≫ (G.coreComp H).symm
参数：η : F ≅ G；H : D ⥤ E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Core.hom_ext`：hom_ext {X Y : Core C} {f g : X ⟶ Y} (h : f
.iso.hom = g.iso.hom) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coreWhiskerRight {E : Type u₃} [Category.{v₃} E] {F G : C ⥤ D} (η : F ≅ G) (H : D ⥤ E) :
    (isoWhiskerRight η H).core =
    F.coreComp H ≪≫ isoWhiskerRight η.core H.core ≪≫ (G.coreComp H).symm := by
  cat_disch

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Iso.coreLeftUnitor** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Is
o`。
形式化陈述：coreLeftUnitor {F : C ⥤ D} : F.leftUnitor.core = (𝟭 C).coreComp F ≪≫ isoWh
iskerRight (Functor.coreId C) _ ≪≫ F.core.leftUnitor
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Core.hom_ext`：hom_ext {X Y : Core C} {f g : X ⟶ Y} (h : f
.iso.hom = g.iso.hom) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coreLeftUnitor {F : C ⥤ D} :
    F.leftUnitor.core =
    (𝟭 C).coreComp F ≪≫ isoWhiskerRight (Functor.coreId C) _ ≪≫ F.core.leftUnitor := by
  cat_disch

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Iso.coreRightUnitor** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.I
so`。
形式化陈述：coreRightUnitor {F : C ⥤ D} : F.rightUnitor.core = (F).coreComp (𝟭 D) ≪≫ i
soWhiskerLeft _ (Functor.coreId D) ≪≫ F.core.rightUnitor
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Core.hom_ext`：hom_ext {X Y : Core C} {f g : X ⟶ Y} (h : f
.iso.hom = g.iso.hom) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coreRightUnitor {F : C ⥤ D} :
    F.rightUnitor.core =
    (F).coreComp (𝟭 D) ≪≫ isoWhiskerLeft _ (Functor.coreId D) ≪≫ F.core.rightUnitor := by
  cat_disch

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Iso.coreAssociator** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Is
o`。
形式化陈述：coreAssociator {E : Type u₃} [Category.{v₃} E] {E' : Type u₄} [Category.{v
₄} E'] (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ E') : (Functor.associator F G H).core = 
(F ⋙ G).coreComp H ≪≫ isoWhiskerRight (F.coreComp G) H.core ≪≫ Functor.associato
r F.core G.core H.core ≪≫ (isoWhiskerLeft F.core (G.coreComp H)).symm ≪≫ (F.core
Comp (G ⋙ H)).symm
参数：F : C ⥤ D；G : D ⥤ E；H : E ⥤ E'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Core.hom_ext`：hom_ext {X Y : Core C} {f g : X ⟶ Y} (h : f
.iso.hom = g.iso.hom) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coreAssociator {E : Type u₃} [Category.{v₃} E] {E' : Type u₄} [Category.{v₄} E']
    (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ E') :
    (Functor.associator F G H).core =
    (F ⋙ G).coreComp H ≪≫ isoWhiskerRight (F.coreComp G) H.core ≪≫
      Functor.associator F.core G.core H.core ≪≫ (isoWhiskerLeft F.core (G.coreComp H)).symm ≪≫
      (F.coreComp (G ⋙ H)).symm := by
  cat_disch

end Iso

namespace Core

variable {G : Type u₂} [Groupoid.{v₂} G]

set_option backward.isDefEq.respectTransparency.types false in
/-- The functor `functorToCore (F ⋙ H)` factors through `functorToCore H`. -/
/-
**CategoryTheory.Core.functorToCoreCompLeftIso** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Core`。
形式化陈述：functorToCoreCompLeftIso {G' : Type u₃} [Groupoid.{v₃} G'] (H : G ⥤ C) (F 
: G' ⥤ G) : functorToCore (F ⋙ H) ≅ F ⋙ functorToCore H
参数：H : G ⥤ C；F : G' ⥤ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `functorToCore (F ⋙ H)` factors through `functorToCore H`.
-/
def functorToCoreCompLeftIso {G' : Type u₃} [Groupoid.{v₃} G'] (H : G ⥤ C) (F : G' ⥤ G) :
    functorToCore (F ⋙ H) ≅ F ⋙ functorToCore H :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Core.functorToCore_comp_left** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Core`。
形式化陈述：functorToCore_comp_left {G' : Type u₃} [Groupoid.{v₃} G'] (H : G ⥤ C) (F :
 G' ⥤ G) : functorToCore (F ⋙ H) = F ⋙ functorToCore H
参数：H : G ⥤ C；F : G' ⥤ G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.ext_of_iso`：ext_of_iso {F G : C ⥤ D} (e : F ≅ G) 
(hobj : forall X, F.obj X = G.obj X) (happ : forall X, e.hom.app X = eqToHom (ho
bj X)
-/
lemma functorToCore_comp_left {G' : Type u₃} [Groupoid.{v₃} G'] (H : G ⥤ C) (F : G' ⥤ G) :
    functorToCore (F ⋙ H) = F ⋙ functorToCore H :=
  Functor.ext_of_iso (functorToCoreCompLeftIso H F) (by cat_disch)

/-- The functor `functorToCore (H ⋙ F)` factors through `functorToCore H`. -/
/-
**CategoryTheory.Core.functorToCoreCompRightIso** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Core`。
形式化陈述：functorToCoreCompRightIso {C' : Type u₄} [Category.{v₄} C'] (H : G ⥤ C) (F
 : C ⥤ C') : functorToCore (H ⋙ F) ≅ functorToCore H ⋙ F.core
参数：H : G ⥤ C；F : C ⥤ C'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `functorToCore (H ⋙ F)` factors through `functorToCore H`.
-/
def functorToCoreCompRightIso {C' : Type u₄} [Category.{v₄} C'] (H : G ⥤ C) (F : C ⥤ C') :
    functorToCore (H ⋙ F) ≅ functorToCore H ⋙ F.core :=
  Iso.refl _
/-
**CategoryTheory.Core.functorToCore_comp_right** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Core`。
形式化陈述：functorToCore_comp_right {C' : Type u₄} [Category.{v₄} C'] (H : G ⥤ C) (F 
: C ⥤ C') : functorToCore (H ⋙ F) = functorToCore H ⋙ F.core
参数：H : G ⥤ C；F : C ⥤ C'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.ext_of_iso`：ext_of_iso {F G : C ⥤ D} (e : F ≅ G) 
(hobj : forall X, F.obj X = G.obj X) (happ : forall X, e.hom.app X = eqToHom (ho
bj X)
-/
lemma functorToCore_comp_right {C' : Type u₄} [Category.{v₄} C'] (H : G ⥤ C) (F : C ⥤ C') :
    functorToCore (H ⋙ F) = functorToCore H ⋙ F.core :=
  Functor.ext_of_iso (functorToCoreCompRightIso H F) (by cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
/-- The functor `functorToCore (𝟭 G)` is a section of `inclusion G`. -/
/-
**CategoryTheory.Core.inclusionCompFunctorToCoreIso** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Core`。
形式化陈述：inclusionCompFunctorToCoreIso : inclusion G ⋙ functorToCore (𝟭 G) ≅ 𝟭 (Cor
e G)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `functorToCore (𝟭 G)` is a section of `inclusion G`.
-/
def inclusionCompFunctorToCoreIso : inclusion G ⋙ functorToCore (𝟭 G) ≅ 𝟭 (Core G) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Core.inclusion_comp_functorToCore** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Core`。
形式化陈述：inclusion_comp_functorToCore : inclusion G ⋙ functorToCore (𝟭 G) = 𝟭 (Core
 G)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.ext_of_iso`：ext_of_iso {F G : C ⥤ D} (e : F ≅ G) 
(hobj : forall X, F.obj X = G.obj X) (happ : forall X, e.hom.app X = eqToHom (ho
bj X)
-/
theorem inclusion_comp_functorToCore : inclusion G ⋙ functorToCore (𝟭 G) = 𝟭 (Core G) :=
  Functor.ext_of_iso inclusionCompFunctorToCoreIso (by cat_disch)

/-- The functor `functorToCore (inclusion C)` is isomorphic to the identity on `Core C`. -/
/-
**CategoryTheory.Core.functorToCoreInclusionIso** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Core`。
形式化陈述：functorToCoreInclusionIso : functorToCore (inclusion C) ≅ 𝟭 (Core C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `functorToCore (inclusion C)` is isomorphic to the identity on `Core
 C`.
-/
def functorToCoreInclusionIso : functorToCore (inclusion C) ≅ 𝟭 (Core C) :=
  Iso.refl _
/-
**CategoryTheory.Core.functorToCore_inclusion** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Core`。
形式化陈述：functorToCore_inclusion : functorToCore (inclusion C) = 𝟭 (Core C)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.ext_of_iso`：ext_of_iso {F G : C ⥤ D} (e : F ≅ G) 
(hobj : forall X, F.obj X = G.obj X) (happ : forall X, e.hom.app X = eqToHom (ho
bj X)
-/
theorem functorToCore_inclusion : functorToCore (inclusion C) = 𝟭 (Core C) :=
  Functor.ext_of_iso functorToCoreInclusionIso (by cat_disch)

end Core

variable (D : Type u₂) [Category.{v₂} D]

namespace Equivalence

set_option backward.isDefEq.respectTransparency.types false in
variable {D} in
/-- Equivalent categories have equivalent cores. -/
@[simps!]
/-
**CategoryTheory.Equivalence.core** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Equi
valence`。
形式化陈述：core (E : C ≌ D) : Core C ≌ Core D where functor
参数：E : C ≌ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalent categories have equivalent cores.
-/
def core (E : C ≌ D) : Core C ≌ Core D where
  functor := E.functor.core
  inverse := E.inverse.core
  unitIso := E.unitIso.core
  counitIso := E.counitIso.core

end Equivalence

set_option backward.isDefEq.respectTransparency.types false in
variable (C) in
/-- Taking the core of a functor is functorial if we discard non-invertible natural
transformations. -/
@[simps!]
/-
**CategoryTheory.coreFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：coreFunctor : Core (C ⥤ D) ⥤ Core C ⥤ Core D where obj F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Taking the core of a functor is functorial if we discard non-invertible natural
transformations.
-/
def coreFunctor : Core (C ⥤ D) ⥤ Core C ⥤ Core D where
  obj F := F.of.core
  map η := η.iso.core.hom

end

/-- `ofEquivFunctor m` lifts a type-level `EquivFunctor`
to a categorical functor `Core (Type u₁) ⥤ Core (Type u₂)`.
-/
/-
**CategoryTheory.ofEquivFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：ofEquivFunctor (m : Type u₁ -> Type u₂) [EquivFunctor m] : Core (Type u₁) 
⥤ Core (Type u₂) where obj x
参数：m : Type u₁ -> Type u₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ofEquivFunctor m` lifts a type-level `EquivFunctor`
to a categorical functor `Core (Type u₁) ⥤ Core (Type u₂)`.
-/
def ofEquivFunctor (m : Type u₁ → Type u₂) [EquivFunctor m] :
    Core (Type u₁) ⥤ Core (Type u₂) where
  obj x := .mk <| m x.of
  map f := .mk <| (EquivFunctor.mapEquiv m f.iso.toEquiv).toIso
  map_id α := by ext x; exact congr_fun (EquivFunctor.map_refl' _) x
  map_comp f g := by
    ext
    simp [Equiv.toIso, EquivFunctor.map_trans']

end CategoryTheory

