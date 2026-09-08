/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne, Joseph Hua
-/
module

public import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete
public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo

/-!
# The Grothendieck and CoGrothendieck constructions

## The Grothendieck construction

Given a category `𝒮` and any pseudofunctor `F` from `𝒮` to `Cat`, we associate to it a category
`∫ F`, defined as follows:
* Objects: pairs `(S, a)` where `S` is an object of the base category and `a` is an object of the
  category `F(S)`.
* Morphisms: morphisms `(R, b) ⟶ (S, a)` are defined as pairs `(f, h)` where `f : R ⟶ S` is a
  morphism in `𝒮` and `h : F(f)(a) ⟶ b`

The category `∫ F` is equipped with a projection functor `∫ F ⥤ 𝒮`,
given by projecting to the first factors, i.e.
* On objects, it sends `(S, a)` to `S`
* On morphisms, it sends `(f, h)` to `f`

## The CoGrothendieck construction

Given a category `𝒮` and any pseudofunctor `F` from `𝒮ᵒᵖ` to `Cat`,
we associate to it a category `∫ᶜ F`, defined as follows:
* Objects: pairs `(S, a)` where `S` is an object of the base category and `a` is an object of the
  category `F(S)`.
* Morphisms: morphisms `(R, b) ⟶ (S, a)` are defined as pairs `(f, h)` where `f : R ⟶ S` is a
  morphism in `𝒮` and `h : b ⟶ F(f)(a)`

The category `∫ᶜ F` is equipped with a functor `∫ᶜ F ⥤ 𝒮`,
given by projecting to the first factors, i.e.
* On objects, it sends `(S, a)` to `S`
* On morphisms, it sends `(f, h)` to `f`

## Naming conventions

The name `Grothendieck` is reserved for the construction on covariant pseudofunctors from `𝒮` to
`Cat`, whereas the word `CoGrothendieck` is used for the contravariant construction.
This is consistent with the convention for the Grothendieck construction on 1-functors
`CategoryTheory.Grothendieck`.

## Future work / TODO

1. Once the bicategory of pseudofunctors has been defined, show that this construction forms a
   pseudofunctor from `LocallyDiscrete 𝒮 ⥤ᵖ Catᵒᵖ` to `Cat`.
2. Deduce the results in `CategoryTheory.Grothendieck` as a specialization of
   `Pseudofunctor.Grothendieck`.

## References
[Vistoli2008] "Notes on Grothendieck Topologies, Fibered Categories and Descent Theory" by
Angelo Vistoli

-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

namespace CategoryTheory.Pseudofunctor

universe w v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory.Functor Category Opposite Discrete Bicategory StrongTrans

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮]

/-- The type of objects in the fibered category associated to a pseudofunctor from a
1-category to Cat. -/
@[ext]
/-
**CategoryTheory.Pseudofunctor.Grothendieck** 是 Mathlib 中的一个归纳类型，位于命名空间 `Categor
yTheory.Pseudofunctor`。
形式化陈述：{𝒮 : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} 𝒮] →     Catego
ryTheory.Pseudofunctor (CategoryTheory.LocallyDiscrete 𝒮) CategoryTheory.Cat → T
ype (max u₁ u₂)
参数：CategoryTheory.LocallyDiscrete 𝒮；max u₁ u₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of objects in the fibered category associated to a pseudofunctor from a
1-category to Cat.
-/
structure Grothendieck (F : LocallyDiscrete 𝒮 ⥤ᵖ Cat.{v₂, u₂}) where
  /-- The underlying object in the base category. -/
  base : 𝒮
  /-- The object in the fiber of the base object. -/
  fiber : F.obj ⟨base⟩

namespace Grothendieck

variable {F : LocallyDiscrete 𝒮 ⥤ᵖ Cat.{v₂, u₂}}

/-- Notation for the Grothendieck category associated to a pseudofunctor `F`. -/
scoped prefix:75 "∫ " => Grothendieck

/-- A morphism in the Grothendieck construction `∫ F` between two points `X Y : ∫ F` consists of
a morphism in the base category `base : X.base ⟶ Y.base` and
a morphism in a fiber `f.fiber : (F.map base).obj X.fiber ⟶ Y.fiber`. -/
/-
**CategoryTheory.Pseudofunctor.Grothendieck.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `Cat
egoryTheory.Pseudofunctor.Grothendieck`。
形式化陈述：{𝒮 : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} 𝒮] →     {F : C
ategoryTheory.Pseudofunctor (CategoryTheory.LocallyDiscrete 𝒮) CategoryTheory.Ca
t} →       F.Grothendieck → F.Grothendieck → Type (max v₁ v₂)
参数：CategoryTheory.LocallyDiscrete 𝒮；max v₁ v₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism in the Grothendieck construction `∫ F` between two points `X Y : ∫ F`
 consists of
a morphism in the base category `base : X.base ⟶ Y.base` and
a morphism in a fiber `f.fiber : (F.map base).obj X.fiber ⟶ Y.fiber`.
-/
structure Hom (X Y : ∫ F) where
  /-- The morphism between base objects. -/
  base : X.base ⟶ Y.base
  /-- The morphism in the fiber over the domain. -/
  fiber : (F.map base.toLoc).toFunctor.obj X.fiber ⟶ Y.fiber

@[simps! id_base id_fiber comp_base comp_fiber]
/-
**CategoryTheory.Pseudofunctor.Grothendieck.categoryStruct** 是 Mathlib 中的一个实例，位于
命名空间 `CategoryTheory.Pseudofunctor.Grothendieck`。
形式化陈述：categoryStruct : CategoryStruct (∫ F) where Hom X Y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance categoryStruct : CategoryStruct (∫ F) where
  Hom X Y := Hom X Y
  id X := {
    base := 𝟙 X.base
    fiber := (F.mapId ⟨X.base⟩).hom.toNatTrans.app X.fiber }
  comp {X _ _} f g := {
    base := f.base ≫ g.base
    fiber := (F.mapComp f.base.toLoc g.base.toLoc).hom.toNatTrans.app X.fiber ≫
      (F.map g.base.toLoc).toFunctor.map f.fiber ≫ g.fiber }
/-
**CategoryTheory.Pseudofunctor.Grothendieck.** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.Pseudofunctor.Grothendieck`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : ∫ F) : Inhabited (Hom X X) :=
  ⟨𝟙 X⟩

section

variable {a b : ∫ F}

@[ext (iff := false)]
/-
**CategoryTheory.Pseudofunctor.Grothendieck.Hom.ext** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Pseudofunctor.Grothendieck.Hom`。
形式化陈述：∀ {𝒮 : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} 𝒮]   {F : Categor
yTheory.Pseudofunctor (CategoryTheory.LocallyDiscrete 𝒮) CategoryTheory.Cat} {a 
b : F.Grothendieck}   (f g : a ⟶ b) (hfg₁ : f.base = g.base),   CategoryTheory.C
ategoryStruct.comp (CategoryTheory.eqToHom ⋯) f.fiber = g.fiber → f = g
参数：CategoryTheory.LocallyDiscrete 𝒮；f g : a ⟶ b；hfg₁ : f.base = g.base；CategoryT
heory.eqToHom ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma Hom.ext (f g : a ⟶ b) (hfg₁ : f.base = g.base)
    (hfg₂ : eqToHom (hfg₁ ▸ rfl) ≫ f.fiber = g.fiber) : f = g := by
  cases f; cases g
  dsimp at hfg₁ hfg₂
  cat_disch
/-
**CategoryTheory.Pseudofunctor.Grothendieck.Hom.ext_iff** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Pseudofunctor.Grothendieck.Hom`。
形式化陈述：∀ {𝒮 : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} 𝒮]   {F : Categor
yTheory.Pseudofunctor (CategoryTheory.LocallyDiscrete 𝒮) CategoryTheory.Cat} {a 
b : F.Grothendieck}   (f g : a ⟶ b),   f = g ↔ ∃ (hfg : f.base = g.base), Catego
ryTheory.CategoryStruct.comp (CategoryTheory.eqToHom ⋯) f.fiber = g.fiber
参数：CategoryTheory.LocallyDiscrete 𝒮；f g : a ⟶ b；hfg : f.base = g.base；CategoryTh
eory.eqToHom ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `CategoryTheory.Pseudofunctor.Grothendieck.Hom.ext`：∀ {𝒮 : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} 𝒮]   {F : CategoryTheory.Pseudofunctor (Cate
goryTheory.LocallyDiscrete 𝒮) CategoryT…
-/
lemma Hom.ext_iff (f g : a ⟶ b) :
    f = g ↔ ∃ (hfg : f.base = g.base), eqToHom (hfg ▸ rfl) ≫ f.fiber = g.fiber where
  mp hfg := by subst hfg; simp
  mpr := fun ⟨hfg₁, hfg₂⟩ => Hom.ext f g hfg₁ hfg₂
/-
**CategoryTheory.Pseudofunctor.Grothendieck.Hom.congr** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Pseudofunctor.Grothendieck.Hom`。
形式化陈述：∀ {𝒮 : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} 𝒮]   {F : Categor
yTheory.Pseudofunctor (CategoryTheory.LocallyDiscrete 𝒮) CategoryTheory.Cat} {a 
b : F.Grothendieck}   {f g : a ⟶ b} (h : f = g), f.fiber = CategoryTheory.Catego
ryStruct.comp (CategoryTheory.eqToHom ⋯) g.fiber
参数：CategoryTheory.LocallyDiscrete 𝒮；h : f = g；CategoryTheory.eqToHom ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Hom.congr {a b : ∫ F} {f g : a ⟶ b} (h : f = g) :
    f.fiber = eqToHom (h ▸ rfl) ≫ g.fiber := by
  subst h
  simp

end

set_option backward.isDefEq.respectTransparency false in
attribute [local simp] PrelaxFunctor.map₂_eqToHom in
/-- The category structure on `∫ F`. -/
/-
**CategoryTheory.Pseudofunctor.Grothendieck.category** 是 Mathlib 中的一个实例，位于命名空间 `
CategoryTheory.Pseudofunctor.Grothendieck`。
形式化陈述：category : Category (∫ F) where toCategoryStruct
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category structure on `∫ F`.
-/
instance category : Category (∫ F) where
  toCategoryStruct := Pseudofunctor.Grothendieck.categoryStruct
  id_comp {a b} f := by
    ext
    · simp
    · simp [F.mapComp_id_left_hom_app, Strict.leftUnitor_eqToIso, ← Functor.map_comp_assoc,
        ← Cat.Hom₂.comp_app]
  comp_id {a b} f := by
    ext
    · simp
    · simp [F.mapComp_id_right_hom_app, Strict.rightUnitor_eqToIso, ← reassoc_of% Cat.Hom₂.comp_app]
  assoc f g h := by
    ext
    · simp
    · simp [mapComp_assoc_right_hom_app_assoc, Strict.associator_eqToIso]

variable (F)

/-- The projection `∫ F ⥤ 𝒮` given by projecting both objects and homs to the first factor. -/
@[simps]
/-
**CategoryTheory.Pseudofunctor.Grothendieck.forget** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Pseudofunctor.Grothendieck`。
形式化陈述：forget (F : Pseudofunctor (LocallyDiscrete 𝒮) Cat.{v₂, u₂}) : ∫ F ⥤ 𝒮 wher
e obj X
参数：F : Pseudofunctor (LocallyDiscrete 𝒮) Cat.{v₂, u₂}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection `∫ F ⥤ 𝒮` given by projecting both objects and homs to the first 
factor.
-/
def forget (F : Pseudofunctor (LocallyDiscrete 𝒮) Cat.{v₂, u₂}) : ∫ F ⥤ 𝒮 where
  obj X := X.base
  map f := f.base

section

attribute [local simp]
  Strict.leftUnitor_eqToIso Strict.rightUnitor_eqToIso Strict.associator_eqToIso

variable {F} {G : Pseudofunctor (LocallyDiscrete 𝒮) Cat.{v₂, u₂}}
  {H : Pseudofunctor (LocallyDiscrete 𝒮) Cat.{v₂, u₂}}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The Grothendieck construction is functorial: a strong natural transformation `α : F ⟶ G`
induces a functor `Grothendieck.map : ∫ F ⥤ ∫ G`. -/
@[simps!]
/-
**CategoryTheory.Pseudofunctor.Grothendieck.map** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Pseudofunctor.Grothendieck`。
形式化陈述：map (α : F ⟶ G) : ∫ F ⥤ ∫ G where obj a
参数：α : F ⟶ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Grothendieck construction is functorial: a strong natural transformation `α 
: F ⟶ G`
induces a functor `Grothendieck.map : ∫ F ⥤ ∫ G`.
-/
def map (α : F ⟶ G) : ∫ F ⥤ ∫ G where
  obj a := {
    base := a.base
    fiber := (α.app ⟨a.base⟩).toFunctor.obj a.fiber }
  map {a b} f := {
    base := f.1
    fiber := (α.naturality f.1.toLoc).inv.toNatTrans.app a.fiber ≫
      (α.app ⟨b.base⟩).toFunctor.map f.2 }
  map_id a := by
    ext
    · dsimp
    · simp [StrongTrans.naturality_id_inv_app, ← map_comp, ← Cat.Hom₂.comp_app]
  map_comp {a b c} f g := by
    ext
    · dsimp
    · simp only [Cat.Hom.comp_toFunctor, comp_obj, categoryStruct_comp_base, Quiver.Hom.comp_toLoc,
        categoryStruct_comp_fiber, eqToHom_refl, map_comp, ← Cat.Hom.comp_map, assoc,
        NatTrans.naturality_assoc]
      simp [naturality_comp_inv_app, ← Functor.map_comp, ← reassoc_of% Cat.Hom₂.comp_app]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Pseudofunctor.Grothendieck.map_id_map** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Pseudofunctor.Grothendieck`。
形式化陈述：map_id_map {x y : ∫ F} (f : x ⟶ y) : (map (𝟙 F)).map f = f
参数：f : x ⟶ y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Pseudofunctor.Grothendieck.Hom.ext`：∀ {𝒮 : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} 𝒮]   {F : CategoryTheory.Pseudofunctor (Cate
goryTheory.LocallyDiscrete 𝒮) CategoryT…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Bicategory.Strict.leftUnitor_eqToIso`：∀ {B : Type u} {ins
t : CategoryTheory.Bicategory B} [self : CategoryTheory.Bicategory.Strict B] {a 
b : B} (f : a ⟶ b),   CategoryTheory.Bica…
· 使用定理 `CategoryTheory.Cat.bicategory.strict`：CategoryTheory.Bicategory.Strict C
ategoryTheory.Cat
· 使用定理 `CategoryTheory.Bicategory.Strict.rightUnitor_eqToIso`：∀ {B : Type u} {in
st : CategoryTheory.Bicategory B} [self : CategoryTheory.Bicategory.Strict B] {a
 b : B} (f : a ⟶ b),   CategoryTheory.Bica…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma map_id_map {x y : ∫ F} (f : x ⟶ y) : (map (𝟙 F)).map f = f := by
  ext <;> simp

@[simp]
/-
**CategoryTheory.Pseudofunctor.Grothendieck.map_comp_forget** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Pseudofunctor.Grothendieck`。
形式化陈述：map_comp_forget (α : F ⟶ G) : map α ⋙ forget G = forget F
参数：α : F ⟶ G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_comp_forget (α : F ⟶ G) : map α ⋙ forget G = forget F := rfl

section

variable (F)

set_option backward.isDefEq.respectTransparency false in
/-- The natural isomorphism witnessing the pseudo-unity constraint of `Grothendieck.map`. -/
/-
**CategoryTheory.Pseudofunctor.Grothendieck.mapIdIso** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Pseudofunctor.Grothendieck`。
形式化陈述：mapIdIso : map (𝟙 F) ≅ 𝟭 (∫ F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isomorphism witnessing the pseudo-unity constraint of `Grothendieck.
map`.
-/
def mapIdIso : map (𝟙 F) ≅ 𝟭 (∫ F) :=
  NatIso.ofComponents (fun _ ↦ eqToIso (by cat_disch))
/-
**CategoryTheory.Pseudofunctor.Grothendieck.map_id_eq** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Pseudofunctor.Grothendieck`。
形式化陈述：map_id_eq : map (𝟙 F) = 𝟭 (∫ F)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.ext_of_iso`：ext_of_iso {F G : C ⥤ D} (e : F ≅ G) 
(hobj : forall X, F.obj X = G.obj X) (happ : forall X, e.hom.app X = eqToHom (ho
bj X)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Bicategory.Strict.id_comp`：∀ {B : Type u} {inst : Categor
yTheory.Bicategory B} [self : CategoryTheory.Bicategory.Strict B] {a b : B} (f :
 a ⟶ b),   CategoryTheory.Cate…
· 使用定理 `CategoryTheory.Cat.bicategory.strict`：CategoryTheory.Bicategory.Strict C
ategoryTheory.Cat
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Bicategory.Strict.comp_id`：∀ {B : Type u} {inst : Categor
yTheory.Bicategory B} [self : CategoryTheory.Bicategory.Strict B] {a b : B} (f :
 a ⟶ b),   CategoryTheory.Cate…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Bicategory.Strict.leftUnitor_eqToIso`：∀ {B : Type u} {ins
t : CategoryTheory.Bicategory B} [self : CategoryTheory.Bicategory.Strict B] {a 
b : B} (f : a ⟶ b),   CategoryTheory.Bica…
· 使用定理 `CategoryTheory.Bicategory.Strict.rightUnitor_eqToIso`：∀ {B : Type u} {in
st : CategoryTheory.Bicategory B} [self : CategoryTheory.Bicategory.Strict B] {a
 b : B} (f : a ⟶ b),   CategoryTheory.Bica…
· 使用定理 `CategoryTheory.eqToHom_trans`：eqToHom_trans {X Y Z : C} (p : X = Y) (q :
 Y = Z) : eqToHom p ≫ eqToHom q = eqToHom (p.trans q)
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Functor.mk.congr_simp`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u
₂} D]   (obj : C → D) (map…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_id_eq : map (𝟙 F) = 𝟭 (∫ F) :=
  Functor.ext_of_iso (mapIdIso F) (fun x ↦ by simp [map]) (fun x ↦ by simp [mapIdIso])

end

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The natural isomorphism witnessing the pseudo-functoriality of `Grothendieck.map`. -/
/-
**CategoryTheory.Pseudofunctor.Grothendieck.mapCompIso** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Pseudofunctor.Grothendieck`。
形式化陈述：mapCompIso (α : F ⟶ G) (β : G ⟶ H) : map (α ≫ β) ≅ map α ⋙ map β
参数：α : F ⟶ G；β : G ⟶ H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isomorphism witnessing the pseudo-functoriality of `Grothendieck.map
`.
-/
def mapCompIso (α : F ⟶ G) (β : G ⟶ H) : map (α ≫ β) ≅ map α ⋙ map β :=
  NatIso.ofComponents (fun _ ↦ eqToIso (by cat_disch)) (fun f ↦ by
    dsimp
    simp only [comp_id, id_comp]
    ext <;> simp)
/-
**CategoryTheory.Pseudofunctor.Grothendieck.map_comp_eq** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Pseudofunctor.Grothendieck`。
形式化陈述：map_comp_eq (α : F ⟶ G) (β : G ⟶ H) : map (α ≫ β) = map α ⋙ map β
参数：α : F ⟶ G；β : G ⟶ H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.ext_of_iso`：ext_of_iso {F G : C ⥤ D} (e : F ≅ G) 
(hobj : forall X, F.obj X = G.obj X) (happ : forall X, e.hom.app X = eqToHom (ho
bj X)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Bicategory.Strict.associator_eqToIso`：∀ {B : Type u} {ins
t : CategoryTheory.Bicategory B} [self : CategoryTheory.Bicategory.Strict B] {a 
b c d : B}   (f : a ⟶ b) (g : b ⟶ c) (h :…
· 使用定理 `CategoryTheory.Cat.bicategory.strict`：CategoryTheory.Bicategory.Strict C
ategoryTheory.Cat
· 使用定理 `CategoryTheory.Functor.mk.congr_simp`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u
₂} D]   (obj : C → D) (map…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_comp_eq (α : F ⟶ G) (β : G ⟶ H) : map (α ≫ β) = map α ⋙ map β :=
  Functor.ext_of_iso (mapCompIso α β) (fun _ ↦ by simp [map]) (fun _ ↦ by simp [mapCompIso])

end

end Grothendieck

/-- The type of objects in the fibered category associated to a contravariant
pseudofunctor from a 1-category to Cat. -/
@[ext]
/-
**CategoryTheory.Pseudofunctor.CoGrothendieck** 是 Mathlib 中的一个归纳类型，位于命名空间 `Categ
oryTheory.Pseudofunctor`。
形式化陈述：{𝒮 : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} 𝒮] →     Catego
ryTheory.Pseudofunctor (CategoryTheory.LocallyDiscrete 𝒮ᵒᵖ) CategoryTheory.Cat →
 Type (max u₁ u₂)
参数：CategoryTheory.LocallyDiscrete 𝒮ᵒᵖ；max u₁ u₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of objects in the fibered category associated to a contravariant
pseudofunctor from a 1-category to Cat.
-/
structure CoGrothendieck (F : LocallyDiscrete 𝒮ᵒᵖ ⥤ᵖ Cat.{v₂, u₂}) where
  /-- The underlying object in the base category. -/
  base : 𝒮
  /-- The object in the fiber of the base object. -/
  fiber : F.obj ⟨op base⟩

namespace CoGrothendieck

variable {F : LocallyDiscrete 𝒮ᵒᵖ ⥤ᵖ Cat.{v₂, u₂}}

/-- Notation for the CoGrothendieck category associated to a pseudofunctor `F`. -/
scoped prefix:75 "∫ᶜ " => CoGrothendieck

/-- A morphism in the CoGrothendieck construction `∫ᶜ F` between two points `X Y : ∫ᶜ F` consists of
a morphism in the base category `base : X.base ⟶ Y.base` and
a morphism in a fiber `f.fiber : X.fiber ⟶ (F.map base.op.toLoc).obj Y.fiber`. -/
/-
**CategoryTheory.Pseudofunctor.CoGrothendieck.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `C
ategoryTheory.Pseudofunctor.CoGrothendieck`。
形式化陈述：{𝒮 : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} 𝒮] →     {F : C
ategoryTheory.Pseudofunctor (CategoryTheory.LocallyDiscrete 𝒮ᵒᵖ) CategoryTheory.
Cat} →       F.CoGrothendieck → F.CoGrothendieck → Type (max v₁ v₂)
参数：CategoryTheory.LocallyDiscrete 𝒮ᵒᵖ；max v₁ v₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism in the CoGrothendieck construction `∫ᶜ F` between two points `X Y : ∫
ᶜ F` consists of
a morphism in the base category `base : X.base ⟶ Y.base` and
a morphism in a fiber `f.fiber : X.fiber ⟶ (F.map base.op.toLoc).obj Y.fiber`.
-/
structure Hom (X Y : ∫ᶜ F) where
  /-- The morphism between base objects. -/
  base : X.base ⟶ Y.base
  /-- The morphism in the fiber over the domain. -/
  fiber : X.fiber ⟶ (F.map base.op.toLoc).toFunctor.obj Y.fiber

@[simps! id_base id_fiber comp_base comp_fiber]
/-
**CategoryTheory.Pseudofunctor.CoGrothendieck.categoryStruct** 是 Mathlib 中的一个实例，
位于命名空间 `CategoryTheory.Pseudofunctor.CoGrothendieck`。
形式化陈述：categoryStruct : CategoryStruct (∫ᶜ F) where Hom X Y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance categoryStruct : CategoryStruct (∫ᶜ F) where
  Hom X Y := Hom X Y
  id X := {
    base := 𝟙 X.base
    fiber := (F.mapId ⟨op X.base⟩).inv.toNatTrans.app X.fiber }
  comp {_ _ Z} f g := {
    base := f.base ≫ g.base
    fiber := f.fiber ≫ (F.map f.base.op.toLoc).toFunctor.map g.fiber ≫
      (F.mapComp g.base.op.toLoc f.base.op.toLoc).inv.toNatTrans.app Z.fiber }
/-
**CategoryTheory.Pseudofunctor.CoGrothendieck.** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.Pseudofunctor.CoGrothendieck`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : ∫ᶜ F) : Inhabited (Hom X X) :=
  ⟨𝟙 X⟩

section

variable {a b : ∫ᶜ F}

@[ext (iff := false)]
/-
**CategoryTheory.Pseudofunctor.CoGrothendieck.Hom.ext** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Pseudofunctor.CoGrothendieck.Hom`。
形式化陈述：∀ {𝒮 : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} 𝒮]   {F : Categor
yTheory.Pseudofunctor (CategoryTheory.LocallyDiscrete 𝒮ᵒᵖ) CategoryTheory.Cat} {
a b : F.CoGrothendieck}   (f g : a ⟶ b) (hfg₁ : f.base = g.base),   f.fiber = Ca
tegoryTheory.CategoryStruct.comp g.fiber (CategoryTheory.eqToHom ⋯) → f = g
参数：CategoryTheory.LocallyDiscrete 𝒮ᵒᵖ；f g : a ⟶ b；hfg₁ : f.base = g.base；Categor
yTheory.eqToHom ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma Hom.ext (f g : a ⟶ b) (hfg₁ : f.base = g.base)
    (hfg₂ : f.fiber = g.fiber ≫ eqToHom (hfg₁ ▸ rfl)) : f = g := by
  cases f; cases g
  dsimp at hfg₁
  cat_disch
/-
**CategoryTheory.Pseudofunctor.CoGrothendieck.Hom.ext_iff** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Pseudofunctor.CoGrothendieck.Hom`。
形式化陈述：∀ {𝒮 : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} 𝒮]   {F : Categor
yTheory.Pseudofunctor (CategoryTheory.LocallyDiscrete 𝒮ᵒᵖ) CategoryTheory.Cat} {
a b : F.CoGrothendieck}   (f g : a ⟶ b),   f = g ↔ ∃ (hfg : f.base = g.base), f.
fiber = CategoryTheory.CategoryStruct.comp g.fiber (CategoryTheory.eqToHom ⋯)
参数：CategoryTheory.LocallyDiscrete 𝒮ᵒᵖ；f g : a ⟶ b；hfg : f.base = g.base；Category
Theory.eqToHom ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.eqToHom_naturality`：eqToHom_naturality {f g : β -> C} (z 
: forall b, f b ⟶ g b) {j j' : β} (w : j = j') : z j ≫ eqToHom (by simp [w]) = e
qToHom (by simp [w]) ≫ …
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Pseudofunctor.CoGrothendieck.Hom.ext`：∀ {𝒮 : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} 𝒮]   {F : CategoryTheory.Pseudofunctor (Ca
tegoryTheory.LocallyDiscrete 𝒮ᵒᵖ) Categor…
-/
lemma Hom.ext_iff (f g : a ⟶ b) :
    f = g ↔ ∃ (hfg : f.base = g.base), f.fiber = g.fiber ≫ eqToHom (hfg ▸ rfl) where
  mp hfg := ⟨by rw [hfg], by simp [hfg]⟩
  mpr := fun ⟨hfg₁, hfg₂⟩ => Hom.ext f g hfg₁ hfg₂
/-
**CategoryTheory.Pseudofunctor.CoGrothendieck.Hom.congr** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Pseudofunctor.CoGrothendieck.Hom`。
形式化陈述：∀ {𝒮 : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} 𝒮]   {F : Categor
yTheory.Pseudofunctor (CategoryTheory.LocallyDiscrete 𝒮ᵒᵖ) CategoryTheory.Cat} {
a b : F.CoGrothendieck}   {f g : a ⟶ b} (h : f = g), f.fiber = CategoryTheory.Ca
tegoryStruct.comp g.fiber (CategoryTheory.eqToHom ⋯)
参数：CategoryTheory.LocallyDiscrete 𝒮ᵒᵖ；h : f = g；CategoryTheory.eqToHom ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.eqToHom_naturality`：eqToHom_naturality {f g : β -> C} (z 
: forall b, f b ⟶ g b) {j j' : β} (w : j = j') : z j ≫ eqToHom (by simp [w]) = e
qToHom (by simp [w]) ≫ …
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma Hom.congr {a b : ∫ᶜ F} {f g : a ⟶ b} (h : f = g) :
    f.fiber = g.fiber ≫ eqToHom (h ▸ rfl) := by
  simp [h]

end

set_option backward.isDefEq.respectTransparency false in
attribute [local simp] PrelaxFunctor.map₂_eqToHom in
/-- The category structure on `∫ᶜ F`. -/
/-
**CategoryTheory.Pseudofunctor.CoGrothendieck.category** 是 Mathlib 中的一个实例，位于命名空间
 `CategoryTheory.Pseudofunctor.CoGrothendieck`。
形式化陈述：category : Category (∫ᶜ F) where toCategoryStruct
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category structure on `∫ᶜ F`.
-/
instance category : Category (∫ᶜ F) where
  toCategoryStruct := Pseudofunctor.CoGrothendieck.categoryStruct
  id_comp {a b} f := by
    ext
    · simp
    · simp [F.mapComp_id_right_inv_app, Strict.rightUnitor_eqToIso, ← NatTrans.naturality_assoc,
        ← Cat.Hom₂.comp_app]
  comp_id {a b} f := by
    ext
    · simp
    · simp [F.mapComp_id_left_inv_app, Strict.leftUnitor_eqToIso, ← Functor.map_comp_assoc,
        ← Cat.Hom₂.comp_app]
  assoc f g h := by
    ext
    · simp
    · simp [← NatTrans.naturality_assoc, F.mapComp_assoc_right_inv_app, Strict.associator_eqToIso]

variable (F)

/-- The projection `∫ᶜ F ⥤ 𝒮` given by projecting both objects and homs to the first factor. -/
@[simps]
/-
**CategoryTheory.Pseudofunctor.CoGrothendieck.forget** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Pseudofunctor.CoGrothendieck`。
形式化陈述：forget (F : LocallyDiscrete 𝒮ᵒᵖ ⥤ᵖ Cat.{v₂, u₂}) : ∫ᶜ F ⥤ 𝒮 where obj X
参数：F : LocallyDiscrete 𝒮ᵒᵖ ⥤ᵖ Cat.{v₂, u₂}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection `∫ᶜ F ⥤ 𝒮` given by projecting both objects and homs to the first
 factor.
-/
def forget (F : LocallyDiscrete 𝒮ᵒᵖ ⥤ᵖ Cat.{v₂, u₂}) : ∫ᶜ F ⥤ 𝒮 where
  obj X := X.base
  map f := f.base

section

attribute [local simp]
  Strict.leftUnitor_eqToIso Strict.rightUnitor_eqToIso Strict.associator_eqToIso

variable {F} {G : LocallyDiscrete 𝒮ᵒᵖ ⥤ᵖ Cat.{v₂, u₂}}
  {H : LocallyDiscrete 𝒮ᵒᵖ ⥤ᵖ Cat.{v₂, u₂}}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The CoGrothendieck construction is functorial: a strong natural transformation `α : F ⟶ G`
induces a functor `CoGrothendieck.map : ∫ᶜ F ⥤ ∫ᶜ G`. -/
@[simps!]
/-
**CategoryTheory.Pseudofunctor.CoGrothendieck.map** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Pseudofunctor.CoGrothendieck`。
形式化陈述：map (α : F ⟶ G) : ∫ᶜ F ⥤ ∫ᶜ G where obj a
参数：α : F ⟶ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The CoGrothendieck construction is functorial: a strong natural transformation `
α : F ⟶ G`
induces a functor `CoGrothendieck.map : ∫ᶜ F ⥤ ∫ᶜ G`.
-/
def map (α : F ⟶ G) : ∫ᶜ F ⥤ ∫ᶜ G where
  obj a := {
    base := a.base
    fiber := (α.app ⟨op a.base⟩).toFunctor.obj a.fiber }
  map {a b} f := {
    base := f.1
    fiber := (α.app ⟨op a.base⟩).toFunctor.map f.2 ≫
      (α.naturality f.1.op.toLoc).hom.toNatTrans.app b.fiber }
  map_id a := by
    ext1
    · dsimp
    · simp [Cat.Hom.comp_toFunctor, naturality_id_hom_app, Cat.Hom.id_toFunctor, ← Category.assoc,
        ← Functor.map_comp, ← Cat.Hom₂.comp_app]
  map_comp {a b c} f g := by
    ext
    · dsimp
    · simp only [categoryStruct_comp_base, op_comp, Quiver.Hom.comp_toLoc,
        categoryStruct_comp_fiber, Cat.Hom.comp_toFunctor, map_comp, naturality_comp_hom_app, assoc,
        eqToHom_refl, comp_id]
      slice_lhs 2 4 => simp [← Cat.Hom.toNatIso_inv, Cat.Hom.comp_toFunctor,
        ← Cat.Hom.toNatIso_hom, ← map_comp, Iso.inv_hom_id_app, comp_obj, map_id, comp_id]
      simp only [assoc, ← reassoc_of% Cat.Hom.comp_map,
        Cat.Hom.comp_toFunctor, Functor.comp_obj, NatTrans.naturality_assoc]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Pseudofunctor.CoGrothendieck.map_id_map** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Pseudofunctor.CoGrothendieck`。
形式化陈述：map_id_map {x y : ∫ᶜ F} (f : x ⟶ y) : (map (𝟙 F)).map f = f
参数：f : x ⟶ y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Pseudofunctor.CoGrothendieck.Hom.ext`：∀ {𝒮 : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} 𝒮]   {F : CategoryTheory.Pseudofunctor (Ca
tegoryTheory.LocallyDiscrete 𝒮ᵒᵖ) Categor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Bicategory.Strict.rightUnitor_eqToIso`：∀ {B : Type u} {in
st : CategoryTheory.Bicategory B} [self : CategoryTheory.Bicategory.Strict B] {a
 b : B} (f : a ⟶ b),   CategoryTheory.Bica…
· 使用定理 `CategoryTheory.Cat.bicategory.strict`：CategoryTheory.Bicategory.Strict C
ategoryTheory.Cat
· 使用定理 `CategoryTheory.Bicategory.Strict.leftUnitor_eqToIso`：∀ {B : Type u} {ins
t : CategoryTheory.Bicategory B} [self : CategoryTheory.Bicategory.Strict B] {a 
b : B} (f : a ⟶ b),   CategoryTheory.Bica…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma map_id_map {x y : ∫ᶜ F} (f : x ⟶ y) : (map (𝟙 F)).map f = f := by
  ext <;> simp

@[simp]
/-
**CategoryTheory.Pseudofunctor.CoGrothendieck.map_comp_forget** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Pseudofunctor.CoGrothendieck`。
形式化陈述：map_comp_forget (α : F ⟶ G) : map α ⋙ forget G = forget F
参数：α : F ⟶ G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_comp_forget (α : F ⟶ G) : map α ⋙ forget G = forget F := rfl

section

variable (F)

set_option backward.isDefEq.respectTransparency false in
/-- The natural isomorphism witnessing the pseudo-unity constraint of `CoGrothendieck.map`. -/
/-
**CategoryTheory.Pseudofunctor.CoGrothendieck.mapIdIso** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Pseudofunctor.CoGrothendieck`。
形式化陈述：mapIdIso : map (𝟙 F) ≅ 𝟭 (∫ᶜ F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isomorphism witnessing the pseudo-unity constraint of `CoGrothendiec
k.map`.
-/
def mapIdIso : map (𝟙 F) ≅ 𝟭 (∫ᶜ F) :=
  NatIso.ofComponents (fun _ ↦ eqToIso (by cat_disch))
/-
**CategoryTheory.Pseudofunctor.CoGrothendieck.map_id_eq** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Pseudofunctor.CoGrothendieck`。
形式化陈述：map_id_eq : map (𝟙 F) = 𝟭 (∫ᶜ F)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.ext_of_iso`：ext_of_iso {F G : C ⥤ D} (e : F ≅ G) 
(hobj : forall X, F.obj X = G.obj X) (happ : forall X, e.hom.app X = eqToHom (ho
bj X)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Bicategory.Strict.comp_id`：∀ {B : Type u} {inst : Categor
yTheory.Bicategory B} [self : CategoryTheory.Bicategory.Strict B] {a b : B} (f :
 a ⟶ b),   CategoryTheory.Cate…
· 使用定理 `CategoryTheory.Cat.bicategory.strict`：CategoryTheory.Bicategory.Strict C
ategoryTheory.Cat
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Bicategory.Strict.id_comp`：∀ {B : Type u} {inst : Categor
yTheory.Bicategory B} [self : CategoryTheory.Bicategory.Strict B] {a b : B} (f :
 a ⟶ b),   CategoryTheory.Cate…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Bicategory.Strict.rightUnitor_eqToIso`：∀ {B : Type u} {in
st : CategoryTheory.Bicategory B} [self : CategoryTheory.Bicategory.Strict B] {a
 b : B} (f : a ⟶ b),   CategoryTheory.Bica…
· 使用定理 `CategoryTheory.Bicategory.Strict.leftUnitor_eqToIso`：∀ {B : Type u} {ins
t : CategoryTheory.Bicategory B} [self : CategoryTheory.Bicategory.Strict B] {a 
b : B} (f : a ⟶ b),   CategoryTheory.Bica…
· 使用定理 `CategoryTheory.eqToHom_trans`：eqToHom_trans {X Y Z : C} (p : X = Y) (q :
 Y = Z) : eqToHom p ≫ eqToHom q = eqToHom (p.trans q)
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Functor.mk.congr_simp`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u
₂} D]   (obj : C → D) (map…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_id_eq : map (𝟙 F) = 𝟭 (∫ᶜ F) :=
  Functor.ext_of_iso (mapIdIso F) (fun x ↦ by simp [map]) (fun x ↦ by simp [mapIdIso])

end

set_option backward.isDefEq.respectTransparency false in
/-- The natural isomorphism witnessing the pseudo-functoriality of `CoGrothendieck.map`. -/
/-
**CategoryTheory.Pseudofunctor.CoGrothendieck.mapCompIso** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Pseudofunctor.CoGrothendieck`。
形式化陈述：mapCompIso (α : F ⟶ G) (β : G ⟶ H) : map (α ≫ β) ≅ map α ⋙ map β
参数：α : F ⟶ G；β : G ⟶ H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isomorphism witnessing the pseudo-functoriality of `CoGrothendieck.m
ap`.
-/
def mapCompIso (α : F ⟶ G) (β : G ⟶ H) : map (α ≫ β) ≅ map α ⋙ map β :=
  NatIso.ofComponents (fun _ ↦ eqToIso (by cat_disch)) (fun f ↦ by
    dsimp
    simp only [comp_id, id_comp]
    ext <;> simp)
/-
**CategoryTheory.Pseudofunctor.CoGrothendieck.map_comp_eq** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Pseudofunctor.CoGrothendieck`。
形式化陈述：map_comp_eq (α : F ⟶ G) (β : G ⟶ H) : map (α ≫ β) = map α ⋙ map β
参数：α : F ⟶ G；β : G ⟶ H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.ext_of_iso`：ext_of_iso {F G : C ⥤ D} (e : F ≅ G) 
(hobj : forall X, F.obj X = G.obj X) (happ : forall X, e.hom.app X = eqToHom (ho
bj X)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Bicategory.Strict.associator_eqToIso`：∀ {B : Type u} {ins
t : CategoryTheory.Bicategory B} [self : CategoryTheory.Bicategory.Strict B] {a 
b c d : B}   (f : a ⟶ b) (g : b ⟶ c) (h :…
· 使用定理 `CategoryTheory.Cat.bicategory.strict`：CategoryTheory.Bicategory.Strict C
ategoryTheory.Cat
· 使用定理 `CategoryTheory.Functor.mk.congr_simp`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u
₂} D]   (obj : C → D) (map…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_comp_eq (α : F ⟶ G) (β : G ⟶ H) : map (α ≫ β) = map α ⋙ map β :=
  Functor.ext_of_iso (mapCompIso α β) (fun _ ↦ by simp [map]) (fun _ ↦ by simp [mapCompIso])

end

end Pseudofunctor.CoGrothendieck

end CategoryTheory

