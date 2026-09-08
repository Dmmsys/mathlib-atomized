/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Adjunction.Reflective
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Limits.Shapes.Images
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
public import Mathlib.CategoryTheory.WithTerminal.Cone
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Monomorphisms over a fixed object

As preparation for defining `Subobject X`, we set up the theory for
`MonoOver X := { f : Over X // Mono f.hom}`.

Here `MonoOver X` is a thin category (a pair of objects has at most one morphism between them),
so we can think of it as a preorder. However as it is not skeletal, it is not yet a partial order.

`Subobject X` will be defined as the skeletalization of `MonoOver X`.

We provide
* `def pullback [HasPullbacks C] (f : X ⟶ Y) : MonoOver Y ⥤ MonoOver X`
* `def map (f : X ⟶ Y) [Mono f] : MonoOver X ⥤ MonoOver Y`
* `def «exists» [HasImages C] (f : X ⟶ Y) : MonoOver X ⥤ MonoOver Y`

and prove their basic properties and relationships.

## Notes

This development originally appeared in Bhavik Mehta's "Topos theory for Lean" repository,
and was ported to mathlib by Kim Morrison.

-/

@[expose] public section


universe w' w v₁ v₂ v₃ u₁ u₂ u₃

noncomputable section

namespace CategoryTheory

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] {X Y Z : C}
variable {D : Type u₂} [Category.{v₂} D]

/-- The object property in `Over X` of the structure morphism being a monomorphism. -/
/-
**CategoryTheory.Over.isMono** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Over`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] → (X : C) → 
CategoryTheory.ObjectProperty (CategoryTheory.Over X)
参数：X : C；CategoryTheory.Over X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The object property in `Over X` of the structure morphism being a monomorphism.
-/
abbrev Over.isMono (X : C) : ObjectProperty (Over X) :=
  fun f : Over X => Mono f.hom

/-- The category of monomorphisms into `X` as a full subcategory of the over category.
This isn't skeletal, so it's not a partial order.

Later we define `Subobject X` as the quotient of this by isomorphisms.
-/
/-
**CategoryTheory.MonoOver** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：MonoOver (X : C)
参数：X : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of monomorphisms into `X` as a full subcategory of the over categor
y.
This isn't skeletal, so it's not a partial order.

Later we define `Subobject X` as the quotient of this by isomorphisms.
-/
abbrev MonoOver (X : C) := (Over.isMono X).FullSubcategory

namespace MonoOver

/-
**CategoryTheory.MonoOver.mono_obj_hom** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.MonoOver`。
形式化陈述：mono_obj_hom (S : MonoOver X) : Mono S.obj.hom
参数：S : MonoOver X。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
-/
instance mono_obj_hom (S : MonoOver X) : Mono S.obj.hom := S.2

/-- Construct a `MonoOver X`. -/
@[simps]
/-
**CategoryTheory.MonoOver.mk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.MonoOver`
。
形式化陈述：mk {X A : C} (f : A ⟶ X) [hf : Mono f] : MonoOver X where obj
参数：f : A ⟶ X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a `MonoOver X`.
-/
def mk {X A : C} (f : A ⟶ X) [hf : Mono f] : MonoOver X where
  obj := Over.mk f
  property := hf

/-- The inclusion from monomorphisms over X to morphisms over X. -/
/-
**CategoryTheory.MonoOver.forget** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Mon
oOver`。
形式化陈述：forget (X : C) : MonoOver X ⥤ Over X
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion from monomorphisms over X to morphisms over X.
-/
abbrev forget (X : C) : MonoOver X ⥤ Over X :=
  ObjectProperty.ι _
/-
**CategoryTheory.MonoOver.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.MonoOver`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeOut (MonoOver X) C where coe Y := Y.obj.left

@[simp]
/-
**CategoryTheory.MonoOver.forget_obj_left** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.MonoOver`。
形式化陈述：forget_obj_left {f} : ((forget X).obj f).left = (f : C)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forget_obj_left {f} : ((forget X).obj f).left = (f : C) :=
  rfl

@[simp]
/-
**CategoryTheory.MonoOver.mk_coe** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.MonoO
ver`。
形式化陈述：mk_coe {X A : C} (f : A ⟶ X) [Mono f] : (mk f : C) = A
参数：f : A ⟶ X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_coe {X A : C} (f : A ⟶ X) [Mono f] : (mk f : C) = A :=
  rfl

/-- Convenience notation for the underlying arrow of a monomorphism over X. -/
/-
**CategoryTheory.MonoOver.arrow** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Mono
Over`。
形式化陈述：arrow (f : MonoOver X) : (f : C) ⟶ X
参数：f : MonoOver X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convenience notation for the underlying arrow of a monomorphism over X.
-/
abbrev arrow (f : MonoOver X) : (f : C) ⟶ X := f.obj.hom

@[simp]
/-
**CategoryTheory.MonoOver.mk_arrow** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Mon
oOver`。
形式化陈述：mk_arrow {X A : C} (f : A ⟶ X) [Mono f] : (mk f).arrow = f
参数：f : A ⟶ X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_arrow {X A : C} (f : A ⟶ X) [Mono f] : (mk f).arrow = f :=
  rfl
/-
**CategoryTheory.MonoOver.forget_obj_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.MonoOver`。
形式化陈述：forget_obj_hom {f} : ((forget X).obj f).hom = f.arrow
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forget_obj_hom {f} : ((forget X).obj f).hom = f.arrow := rfl

/-- The forget functor `MonoOver X ⥤ Over X` is fully faithful. -/
/-
**CategoryTheory.MonoOver.fullyFaithfulForget** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.MonoOver`。
形式化陈述：fullyFaithfulForget (X : C) : (forget X).FullyFaithful
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forget functor `MonoOver X ⥤ Over X` is fully faithful.
-/
def fullyFaithfulForget (X : C) : (forget X).FullyFaithful :=
  ObjectProperty.fullyFaithfulι _
/-
**CategoryTheory.MonoOver.mono** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.MonoOve
r`。
形式化陈述：mono (f : MonoOver X) : Mono f.arrow
参数：f : MonoOver X。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
-/
instance mono (f : MonoOver X) : Mono f.arrow :=
  f.property
/-
**CategoryTheory.MonoOver.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.MonoOver`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : C} {f : MonoOver X} : Mono ((MonoOver.forget X).obj f).hom := f.mono

/-- The category of monomorphisms over X is a thin category,
which makes defining its skeleton easy. -/
/-
**CategoryTheory.MonoOver.isThin** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.MonoO
ver`。
形式化陈述：isThin {X : C} : Quiver.IsThin (MonoOver X)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.InducedCategory.hom_ext`：hom_ext {X Y : InducedCategory D
 F} {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g
· 使用定理 `CategoryTheory.Over.OverMorphism.ext`：∀ {T : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} T] {X : T} {U V : CategoryTheory.Over X} {f g : U ⟶ V},  
 CategoryTheory.Over.Hom.l…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.Over.w`：w : φ.left ≫ g.hom = f.hom

--- 原说明 ---
The category of monomorphisms over X is a thin category,
which makes defining its skeleton easy.
-/
instance isThin {X : C} : Quiver.IsThin (MonoOver X) := fun f g =>
  ⟨by
    intro h₁ h₂
    apply InducedCategory.hom_ext
    apply Over.OverMorphism.ext
    rw [← cancel_mono g.arrow, Over.w h₁.hom, Over.w h₂.hom]⟩

@[reassoc]
/-
**CategoryTheory.MonoOver.w** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.MonoOver`。
形式化陈述：w {f g : MonoOver X} (k : f ⟶ g) : k.hom.left ≫ g.arrow = f.arrow
参数：k : f ⟶ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Over.w`：w : φ.left ≫ g.hom = f.hom
-/
theorem w {f g : MonoOver X} (k : f ⟶ g) : k.hom.left ≫ g.arrow = f.arrow :=
  Over.w _

/-- Convenience constructor for a morphism in monomorphisms over `X`. -/
/-
**CategoryTheory.MonoOver.homMk** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Mono
Over`。
形式化陈述：homMk {f g : MonoOver X} (h : f.obj.left ⟶ g.obj.left) (w : h ≫ g.arrow = 
f.arrow
参数：h : f.obj.left ⟶ g.obj.left。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convenience constructor for a morphism in monomorphisms over `X`.
-/
abbrev homMk {f g : MonoOver X} (h : f.obj.left ⟶ g.obj.left)
    (w : h ≫ g.arrow = f.arrow := by aesop_cat) : f ⟶ g :=
  InducedCategory.homMk (Over.homMk h w)

/-- Convenience constructor for an isomorphism in monomorphisms over `X`. -/
@[simps]
/-
**CategoryTheory.MonoOver.isoMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.MonoOv
er`。
形式化陈述：isoMk {f g : MonoOver X} (h : f.obj.left ≅ g.obj.left) (w : h.hom ≫ g.arro
w = f.arrow
参数：h : f.obj.left ≅ g.obj.left。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convenience constructor for an isomorphism in monomorphisms over `X`.
-/
def isoMk {f g : MonoOver X} (h : f.obj.left ≅ g.obj.left)
    (w : h.hom ≫ g.arrow = f.arrow := by cat_disch) : f ≅ g where
  hom := homMk h.hom w
  inv := homMk h.inv (by rw [h.inv_comp_eq, w])

/-- If `f : MonoOver X`, then `mk' f.arrow` is of course just `f`, but not definitionally, so we
package it as an isomorphism. -/
@[simps!]
/-
**CategoryTheory.MonoOver.mkArrowIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.M
onoOver`。
形式化陈述：mkArrowIso {X : C} (f : MonoOver X) : mk f.arrow ≅ f
参数：f : MonoOver X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f : MonoOver X`, then `mk' f.arrow` is of course just `f`, but not definitio
nally, so we
package it as an isomorphism.
-/
def mkArrowIso {X : C} (f : MonoOver X) : mk f.arrow ≅ f :=
  isoMk (Iso.refl _)
/-
**CategoryTheory.MonoOver.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.MonoOver`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {A B : MonoOver X} (f : A ⟶ B) [IsIso f] : IsIso f.hom.left :=
  inferInstanceAs (IsIso ((MonoOver.forget _ ⋙ Over.forget _).map f))
/-
**CategoryTheory.MonoOver.isIso_iff_isIso_hom_left** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.MonoOver`。
形式化陈述：isIso_iff_isIso_hom_left {A B : MonoOver X} (f : A ⟶ B) : IsIso f ↔ IsIso 
f.hom.left
参数：f : A ⟶ B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `CategoryTheory.isIso_iff_of_reflects_iso`：isIso_iff_of_reflects_iso {A B
 : C} (f : A ⟶ B) (F : C ⥤ D) [F.ReflectsIsomorphisms] : IsIso (F.map f) ↔ IsIso
 f
· 使用定理 `CategoryTheory.reflectsIsomorphisms_of_full_and_faithful`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Cate
goryTheory.Category.{v_2, u_2} D] (F : Categor…
-/
lemma isIso_iff_isIso_hom_left {A B : MonoOver X} (f : A ⟶ B) :
    IsIso f ↔ IsIso f.hom.left :=
  (isIso_iff_of_reflects_iso _ (MonoOver.forget X ⋙ Over.forget _)).symm

/-- Lift a functor between over categories to a functor between `MonoOver` categories,
given suitable evidence that morphisms are taken to monomorphisms.
-/
@[simps!]
/-
**CategoryTheory.MonoOver.lift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.MonoOve
r`。
形式化陈述：lift {Y : D} (F : Over Y ⥤ Over X) (h : forall f : MonoOver Y, Mono (F.obj
 ((MonoOver.forget Y).obj f)).hom) : MonoOver Y ⥤ MonoOver X
参数：F : Over Y ⥤ Over X；h : forall f : MonoOver Y, Mono (F.obj ((MonoOver.forget 
Y).obj f)).hom。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift a functor between over categories to a functor between `MonoOver` categorie
s,
given suitable evidence that morphisms are taken to monomorphisms.
-/
def lift {Y : D} (F : Over Y ⥤ Over X)
    (h : ∀ f : MonoOver Y, Mono (F.obj ((MonoOver.forget Y).obj f)).hom) :
    MonoOver Y ⥤ MonoOver X :=
  ObjectProperty.lift _ (forget _ ⋙ F) h

/-- Isomorphic functors `Over Y ⥤ Over X` lift to isomorphic functors `MonoOver Y ⥤ MonoOver X`.
-/
/-
**CategoryTheory.MonoOver.liftIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Mono
Over`。
形式化陈述：liftIso {Y : D} {F₁ F₂ : Over Y ⥤ Over X} (h₁ h₂) (i : F₁ ≅ F₂) : lift F₁ 
h₁ ≅ lift F₂ h₂
参数：h₁ h₂；i : F₁ ≅ F₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Isomorphic functors `Over Y ⥤ Over X` lift to isomorphic functors `MonoOver Y ⥤ 
MonoOver X`.
-/
def liftIso {Y : D} {F₁ F₂ : Over Y ⥤ Over X} (h₁ h₂) (i : F₁ ≅ F₂) : lift F₁ h₁ ≅ lift F₂ h₂ :=
  Functor.fullyFaithfulCancelRight (MonoOver.forget X) (isoWhiskerLeft (MonoOver.forget Y) i)

/-- `MonoOver.lift` commutes with composition of functors. -/
/-
**CategoryTheory.MonoOver.liftComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Mon
oOver`。
形式化陈述：liftComp {X Z : C} {Y : D} (F : Over X ⥤ Over Y) (G : Over Y ⥤ Over Z) (h₁
 h₂) : lift F h₁ ⋙ lift G h₂ ≅ lift (F ⋙ G) fun f => h₂ ⟨_, h₁ f⟩
参数：F : Over X ⥤ Over Y；G : Over Y ⥤ Over Z；h₁ h₂。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`MonoOver.lift` commutes with composition of functors.
-/
def liftComp {X Z : C} {Y : D} (F : Over X ⥤ Over Y) (G : Over Y ⥤ Over Z) (h₁ h₂) :
    lift F h₁ ⋙ lift G h₂ ≅ lift (F ⋙ G) fun f => h₂ ⟨_, h₁ f⟩ :=
  Functor.fullyFaithfulCancelRight (MonoOver.forget _) (Iso.refl _)

/-- `MonoOver.lift` preserves the identity functor. -/
/-
**CategoryTheory.MonoOver.liftId** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.MonoO
ver`。
形式化陈述：liftId : (lift (𝟭 (Over X)) fun f => f.2) ≅ 𝟭 _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`MonoOver.lift` preserves the identity functor.
-/
def liftId : (lift (𝟭 (Over X)) fun f => f.2) ≅ 𝟭 _ :=
  Functor.fullyFaithfulCancelRight (MonoOver.forget _) (Iso.refl _)

@[simp]
/-
**CategoryTheory.MonoOver.lift_comm** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Mo
noOver`。
形式化陈述：lift_comm (F : Over Y ⥤ Over X) (h : forall f : MonoOver Y, Mono (F.obj ((
MonoOver.forget Y).obj f)).hom) : lift F h ⋙ MonoOver.forget X = MonoOver.forget
 Y ⋙ F
参数：F : Over Y ⥤ Over X；h : forall f : MonoOver Y, Mono (F.obj ((MonoOver.forget 
Y).obj f)).hom。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_comm (F : Over Y ⥤ Over X)
    (h : ∀ f : MonoOver Y, Mono (F.obj ((MonoOver.forget Y).obj f)).hom) :
    lift F h ⋙ MonoOver.forget X = MonoOver.forget Y ⋙ F :=
  rfl

@[simp]
/-
**CategoryTheory.MonoOver.lift_obj_arrow** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.MonoOver`。
形式化陈述：lift_obj_arrow {Y : D} (F : Over Y ⥤ Over X) (h : forall f : MonoOver Y, M
ono (F.obj ((MonoOver.forget Y).obj f)).hom) (f : MonoOver Y) : ((lift F h).obj 
f).arrow = (F.obj ((forget Y).obj f)).hom
参数：F : Over Y ⥤ Over X；h : forall f : MonoOver Y, Mono (F.obj ((MonoOver.forget 
Y).obj f)).hom；f : MonoOver Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_obj_arrow {Y : D} (F : Over Y ⥤ Over X)
    (h : ∀ f : MonoOver Y, Mono (F.obj ((MonoOver.forget Y).obj f)).hom) (f : MonoOver Y) :
    ((lift F h).obj f).arrow = (F.obj ((forget Y).obj f)).hom :=
  rfl

/-- Monomorphisms over an object `f : Over A` in an over category
are equivalent to monomorphisms over the source of `f`.
-/
/-
**CategoryTheory.MonoOver.slice** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.MonoOv
er`。
形式化陈述：slice {A : C} {f : Over A} (h₁ : forall (g : MonoOver f), Mono ((Over.iter
atedSliceEquiv f).functor.obj ((forget f).obj g)).hom) (h₂ : forall (g : MonoOve
r f.left), Mono ((Over.iteratedSliceEquiv f).inverse.obj ((forget f.left).obj g)
).hom) : MonoOver f ≌ MonoOver f.left where functor
参数：h₁ : forall (g : MonoOver f), Mono ((Over.iteratedSliceEquiv f).functor.obj (
(forget f).obj g)).hom；h₂ : forall (g : MonoOver f.left), Mono ((Over.iteratedSl
iceEquiv f).inverse.obj ((forget f.left).obj g)).hom。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Monomorphisms over an object `f : Over A` in an over category
are equivalent to monomorphisms over the source of `f`.
-/
def slice {A : C} {f : Over A}
    (h₁ : ∀ (g : MonoOver f),
      Mono ((Over.iteratedSliceEquiv f).functor.obj ((forget f).obj g)).hom)
    (h₂ : ∀ (g : MonoOver f.left),
      Mono ((Over.iteratedSliceEquiv f).inverse.obj ((forget f.left).obj g)).hom) :
    MonoOver f ≌ MonoOver f.left where
  functor := MonoOver.lift f.iteratedSliceEquiv.functor h₁
  inverse := MonoOver.lift f.iteratedSliceEquiv.inverse h₂
  unitIso :=
    MonoOver.liftId.symm ≪≫
      MonoOver.liftIso _ _ f.iteratedSliceEquiv.unitIso ≪≫ (MonoOver.liftComp _ _ _ _).symm
  counitIso :=
    MonoOver.liftComp _ _ _ _ ≪≫
      MonoOver.liftIso _ _ f.iteratedSliceEquiv.counitIso ≪≫ MonoOver.liftId

section Limits

variable {J : Type u₃} [Category.{v₃} J] (X : C)

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.MonoOver.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.MonoOver`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (Over.isMono X).IsClosedUnderLimitsOfShape J where
  limitsOfShape_le := fun F ⟨p, hp⟩ ↦ ⟨fun g h e ↦ by
    refine (WithTerminal.isLimitEquiv.invFun p.isLimit).hom_ext (fun j ↦ ?_)
    cases j with
    | of j => have := hp j; rw [← cancel_mono ((p.diag.obj j).hom)]; simpa
    | star => exact e⟩
/-
**CategoryTheory.MonoOver.hasLimit** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mon
oOver`。
形式化陈述：hasLimit (F : J ⥤ MonoOver X) [HasLimit (F ⋙ (Over.isMono X).ι)] : HasLimi
t F
参数：F : J ⥤ MonoOver X；F ⋙ (Over.isMono X).ι。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasLimit_of_closedUnderLimits`：hasLimit_of_closedU
nderLimits [P.IsClosedUnderLimitsOfShape J] (F : J ⥤ P.FullSubcategory) [HasLimi
t (F ⋙ P.ι)] : HasLimit F
· 使用定理 `CategoryTheory.MonoOver.instIsClosedUnderLimitsOfShapeOverIsMono`：∀ {C :
 Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : Type u₃} [inst_1 : Ca
tegoryTheory.Category.{v₃, u₃} J]   (X : C), (Category…
-/
instance hasLimit (F : J ⥤ MonoOver X) [HasLimit (F ⋙ (Over.isMono X).ι)] :
    HasLimit F :=
  hasLimit_of_closedUnderLimits _ _ _
/-
**CategoryTheory.MonoOver.hasLimitsOfShape** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.MonoOver`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : Type u₃} 
[inst_1 : CategoryTheory.Category.{v₃, u₃} J]   (X : C) [CategoryTheory.Limits.H
asLimitsOfShape J (CategoryTheory.Over X)],   CategoryTheory.Limits.HasLimitsOfS
hape J (CategoryTheory.MonoOver X)
参数：X : C；CategoryTheory.Over X；CategoryTheory.MonoOver X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
instance hasLimitsOfShape [HasLimitsOfShape J (Over X)] :
    HasLimitsOfShape J (MonoOver X) where
/-
**CategoryTheory.MonoOver.hasFiniteLimits** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.MonoOver`。
形式化陈述：hasFiniteLimits [HasFiniteLimits (Over X)] : HasFiniteLimits (MonoOver X) 
where out _ _ _
参数：Over X。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MonoOver.hasLimitsOfShape`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {J : Type u₃} [inst_1 : CategoryTheory.Category.{v
₃, u₃} J]   (X : C) [CategoryT…
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_hasFiniteLimits`：∀ (C : Type u
) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLimi
ts C] (J : Type w)   [inst_2 : CategoryTheory.S…
-/
instance hasFiniteLimits [HasFiniteLimits (Over X)] : HasFiniteLimits (MonoOver X) where
  out _ _ _ := inferInstance
/-
**CategoryTheory.MonoOver.hasLimitsOfSize** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.MonoOver`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (X : C)   [Cat
egoryTheory.Limits.HasLimitsOfSize.{w, w', v₁, max u₁ v₁} (CategoryTheory.Over X
)],   CategoryTheory.Limits.HasLimitsOfSize.{w, w', v₁, max u₁ v₁} (CategoryTheo
ry.MonoOver X)
参数：X : C；CategoryTheory.Over X；CategoryTheory.MonoOver X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MonoOver.hasLimitsOfShape`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {J : Type u₃} [inst_1 : CategoryTheory.Category.{v
₃, u₃} J]   (X : C) [CategoryT…
· 使用定理 `CategoryTheory.Limits.instHasLimitsOfShapeOfHasLimitsOfSize`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTh
eory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
instance hasLimitsOfSize [HasLimitsOfSize.{w, w'} (Over X)] :
    HasLimitsOfSize.{w, w'} (MonoOver X) where

end Limits

section Colimits

variable [HasCoproducts C] [HasStrongEpiMonoFactorisations C] {J : Type u₂} [Category.{v₂} J]

/-- A helper function, providing the strong epi-mono factorization used construct to colimits. -/
/-
**CategoryTheory.MonoOver.strongEpiMonoFactorisationSigmaDesc** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.MonoOver`。
形式化陈述：strongEpiMonoFactorisationSigmaDesc (F : J ⥤ MonoOver Y) : StrongEpiMonoFa
ctorisation (Sigma.desc fun i => (F.obj i).arrow)
参数：F : J ⥤ MonoOver Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A helper function, providing the strong epi-mono factorization used construct to
 colimits.
-/
def strongEpiMonoFactorisationSigmaDesc (F : J ⥤ MonoOver Y) :
    StrongEpiMonoFactorisation (Sigma.desc fun i ↦ (F.obj i).arrow) :=
  Classical.choice <| HasStrongEpiMonoFactorisations.has_fac (Sigma.desc fun i ↦ (F.obj i).arrow)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If a category `C` has strong epi-mono factorization, for any `Y : C` and functor
`F : J ⥤ MonoOver Y`, there is a cocone under F. -/
/-
**CategoryTheory.MonoOver.coconeOfHasStrongEpiMonoFactorisation** 是 Mathlib 中的一个
定义，位于命名空间 `CategoryTheory.MonoOver`。
形式化陈述：coconeOfHasStrongEpiMonoFactorisation (F : J ⥤ MonoOver Y) : Cocone F wher
e pt
参数：F : J ⥤ MonoOver Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a category `C` has strong epi-mono factorization, for any `Y : C` and functor
`F : J ⥤ MonoOver Y`, there is a cocone under F.
-/
def coconeOfHasStrongEpiMonoFactorisation (F : J ⥤ MonoOver Y) :
    Cocone F where
  pt := MonoOver.mk ((strongEpiMonoFactorisationSigmaDesc F).m)
  ι.app j := homMk (Sigma.ι (fun i ↦ (F.obj i : C)) j ≫
    (strongEpiMonoFactorisationSigmaDesc F).e)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.MonoOver.commSqOfHasStrongEpiMonoFactorisation** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.MonoOver`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {Y : C} [inst_
1 : CategoryTheory.Limits.HasCoproducts C]   [inst_2 : CategoryTheory.Limits.Has
StrongEpiMonoFactorisations C] {J : Type u₂}   [inst_3 : CategoryTheory.Category
.{v₂, u₂} J] (F : CategoryTheory.Functor J (CategoryTheory.MonoOver Y))   (c : C
ategoryTheory.Limits.Cocone F),   CategoryTheory.CommSq (CategoryTheory.Limits.S
igma.desc fun i => CategoryTheory.Over.Hom.left (c.ι.app i).hom)     (CategoryTh
eory.MonoOver.strongEpiMonoFactorisationSigmaDesc F).e c.pt.arrow     (CategoryT
heory.MonoOver.strongEpiMonoFactorisationSigmaDesc F).m
参数：F : CategoryTheory.Functor J (CategoryTheory.MonoOver Y)；c : CategoryTheory.L
imits.Cocone F；CategoryTheory.Limits.Sigma.desc fun i => CategoryTheory.Over.Hom
.left (c.ι.app i).hom；CategoryTheory.MonoOver.strongEpiMonoFactorisationSigmaDes
c F；CategoryTheory.MonoOver.strongEpiMonoFactorisationSigmaDesc F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.MonoFactorisation.fac`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y}   (self : CategoryTheory.Lim
its.MonoFactorisation f), Categor…
· 使用定理 `CategoryTheory.Limits.Sigma.hom_ext`：∀ {β : Type w} {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] {f : β → C}   [inst_1 : CategoryTheory.Limits
.HasCoproduct f] {X : C} …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc_assoc`：∀ {J : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{
v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Over.w`：w : φ.left ≫ g.hom = f.hom
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma commSqOfHasStrongEpiMonoFactorisation (F : J ⥤ MonoOver Y) (c : Cocone F) :
    CommSq (Sigma.desc fun i ↦ (c.ι.app i).hom.left) (strongEpiMonoFactorisationSigmaDesc F).e
      c.pt.arrow (strongEpiMonoFactorisationSigmaDesc F).m where

/-- A helper function, providing the lift structure used to construct colimits. -/
/-
**CategoryTheory.MonoOver.liftStructOfHasStrongEpiMonoFactorisation** 是 Mathlib 
中的一个定义，位于命名空间 `CategoryTheory.MonoOver`。
形式化陈述：liftStructOfHasStrongEpiMonoFactorisation (F : J ⥤ MonoOver Y) (c : Cocone
 F) : (commSqOfHasStrongEpiMonoFactorisation F c).LiftStruct
参数：F : J ⥤ MonoOver Y；c : Cocone F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MonoOver.commSqOfHasStrongEpiMonoFactorisation`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {Y : C} [inst_1 : CategoryThe
ory.Limits.HasCoproducts C]   [inst_2 : CategoryThe…

--- 原说明 ---
A helper function, providing the lift structure used to construct colimits.
-/
def liftStructOfHasStrongEpiMonoFactorisation (F : J ⥤ MonoOver Y) (c : Cocone F) :
    (commSqOfHasStrongEpiMonoFactorisation F c).LiftStruct :=
  Classical.choice
    (((strongEpiMonoFactorisationSigmaDesc F).e_strong_epi.llp _).sq_hasLift
      (commSqOfHasStrongEpiMonoFactorisation F c)).exists_lift

/-- The cocone `coconeOfHasStrongEpiMonoFactorisation F` is a colimit -/
/-
**CategoryTheory.MonoOver.isColimitCoconeOfHasStrongEpiMonoFactorisation** 是 Mat
hlib 中的一个定义，位于命名空间 `CategoryTheory.MonoOver`。
形式化陈述：isColimitCoconeOfHasStrongEpiMonoFactorisation (F : J ⥤ MonoOver Y) : IsCo
limit (coconeOfHasStrongEpiMonoFactorisation F) where desc c
参数：F : J ⥤ MonoOver Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MonoOver.commSqOfHasStrongEpiMonoFactorisation`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {Y : C} [inst_1 : CategoryThe
ory.Limits.HasCoproducts C]   [inst_2 : CategoryThe…

--- 原说明 ---
The cocone `coconeOfHasStrongEpiMonoFactorisation F` is a colimit
-/
def isColimitCoconeOfHasStrongEpiMonoFactorisation (F : J ⥤ MonoOver Y) :
    IsColimit (coconeOfHasStrongEpiMonoFactorisation F) where
  desc c := homMk (liftStructOfHasStrongEpiMonoFactorisation F c).l
    (liftStructOfHasStrongEpiMonoFactorisation F c).fac_right
/-
**CategoryTheory.MonoOver.hasColimitsOfSize_of_hasStrongEpiMonoFactorisations** 
是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.MonoOver`。
形式化陈述：hasColimitsOfSize_of_hasStrongEpiMonoFactorisations : HasColimitsOfSize.{w
, w'} (MonoOver Y) where has_colimits_of_shape _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasColimitsOfSize_of_hasStrongEpiMonoFactorisations :
    HasColimitsOfSize.{w, w'} (MonoOver Y) where
  has_colimits_of_shape _ _ :=
    ⟨fun F ↦
      ⟨coconeOfHasStrongEpiMonoFactorisation F, isColimitCoconeOfHasStrongEpiMonoFactorisation F⟩⟩

end Colimits

section Pullback

variable [HasPullbacks C]

/-- When `C` has pullbacks, a morphism `f : X ⟶ Y` induces a functor `MonoOver Y ⥤ MonoOver X`,
by pulling back a monomorphism along `f`. -/
/-
**CategoryTheory.MonoOver.pullback** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Mon
oOver`。
形式化陈述：pullback (f : X ⟶ Y) : MonoOver Y ⥤ MonoOver X
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `C` has pullbacks, a morphism `f : X ⟶ Y` induces a functor `MonoOver Y ⥤ M
onoOver X`,
by pulling back a monomorphism along `f`.
-/
def pullback (f : X ⟶ Y) : MonoOver Y ⥤ MonoOver X :=
  MonoOver.lift (Over.pullback f) (fun g => by
    have : Mono ((forget Y).obj g).hom := (inferInstance : Mono g.arrow)
    apply pullback.snd_of_mono)

/-- pullback commutes with composition (up to a natural isomorphism) -/
/-
**CategoryTheory.MonoOver.pullbackComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.MonoOver`。
形式化陈述：pullbackComp (f : X ⟶ Y) (g : Y ⟶ Z) : pullback (f ≫ g) ≅ pullback g ⋙ pul
lback f
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
pullback commutes with composition (up to a natural isomorphism)
-/
def pullbackComp (f : X ⟶ Y) (g : Y ⟶ Z) : pullback (f ≫ g) ≅ pullback g ⋙ pullback f :=
  liftIso _ _ (Over.pullbackComp _ _) ≪≫ (liftComp _ _ _ _).symm

/-- pullback preserves the identity (up to a natural isomorphism) -/
/-
**CategoryTheory.MonoOver.pullbackId** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.M
onoOver`。
形式化陈述：pullbackId : pullback (𝟙 X) ≅ 𝟭 _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
pullback preserves the identity (up to a natural isomorphism)
-/
def pullbackId : pullback (𝟙 X) ≅ 𝟭 _ :=
  liftIso _ _ Over.pullbackId ≪≫ liftId

@[simp]
/-
**CategoryTheory.MonoOver.pullback_obj_left** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.MonoOver`。
形式化陈述：pullback_obj_left (f : X ⟶ Y) (g : MonoOver Y) : ((pullback f).obj g : C) 
= Limits.pullback g.arrow f
参数：f : X ⟶ Y；g : MonoOver Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pullback_obj_left (f : X ⟶ Y) (g : MonoOver Y) :
    ((pullback f).obj g : C) = Limits.pullback g.arrow f :=
  rfl

@[simp]
/-
**CategoryTheory.MonoOver.pullback_obj_arrow** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.MonoOver`。
形式化陈述：pullback_obj_arrow (f : X ⟶ Y) (g : MonoOver Y) : ((pullback f).obj g).arr
ow = pullback.snd _ _
参数：f : X ⟶ Y；g : MonoOver Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pullback_obj_arrow (f : X ⟶ Y) (g : MonoOver Y) :
    ((pullback f).obj g).arrow = pullback.snd _ _ :=
  rfl

end Pullback

section IsPullback

/--
Given two monomorphisms `S` and `T` over `X` and `Y` and two morphisms `f` and `f'` between them
forming the following pullback square:

```
(T : C) -f'-> (S : C)
   |             |
T.arrow       S.arrow
   |             |
   v             v
   Y -----f----> X
```

we get an isomorphism between `T` and the pullback of `S` along `f` through the `pullback` functor.
-/
/-
**CategoryTheory.MonoOver.pullbackObjIsoOfIsPullback** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.MonoOver`。
形式化陈述：pullbackObjIsoOfIsPullback [HasPullbacks C] {X Y : C} (f : Y ⟶ X) (S : Mon
oOver X) (T : MonoOver Y) (f' : (T : C) ⟶ (S : C)) (h : IsPullback f' T.arrow S.
arrow f) : (pullback f).obj S ≅ T
参数：f : Y ⟶ X；S : MonoOver X；T : MonoOver Y；f' : (T : C) ⟶ (S : C)；h : IsPullback
 f' T.arrow S.arrow f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two monomorphisms `S` and `T` over `X` and `Y` and two morphisms `f` and `
f'` between them
forming the following pullback square:

```
(T : C) -f'-> (S : C)
   |             |
T.arrow       S.arrow
   |             |
   v             v
   Y -----f----> X
```

we get an isomorphism between `T` and the pullback of `S` along `f` through the 
`pullback` functor.
-/
def pullbackObjIsoOfIsPullback [HasPullbacks C] {X Y : C} (f : Y ⟶ X) (S : MonoOver X)
    (T : MonoOver Y) (f' : (T : C) ⟶ (S : C))
    (h : IsPullback f' T.arrow S.arrow f) :
    (pullback f).obj S ≅ T :=
  isoMk ((IsPullback.isoPullback h).symm)

end IsPullback

section Map

/-- We can map monomorphisms over `X` to monomorphisms over `Y`
by post-composition with a monomorphism `f : X ⟶ Y`.
-/
/-
**CategoryTheory.MonoOver.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.MonoOver
`。
形式化陈述：map (f : X ⟶ Y) [Mono f] : MonoOver X ⥤ MonoOver Y
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We can map monomorphisms over `X` to monomorphisms over `Y`
by post-composition with a monomorphism `f : X ⟶ Y`.
-/
def map (f : X ⟶ Y) [Mono f] : MonoOver X ⥤ MonoOver Y :=
  lift (Over.map f) fun g => mono_comp g.arrow f

/-- `MonoOver.map` commutes with composition (up to a natural isomorphism). -/
/-
**CategoryTheory.MonoOver.mapComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Mono
Over`。
形式化陈述：mapComp (f : X ⟶ Y) (g : Y ⟶ Z) [Mono f] [Mono g] : map (f ≫ g) ≅ map f ⋙ 
map g
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.mono_comp`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] {X Y Z : C} (g : Z ⟶ Y) [CategoryTheory.Mono g] (f : Y ⟶ X)   [Catego
ryTheory.Mono …

--- 原说明 ---
`MonoOver.map` commutes with composition (up to a natural isomorphism).
-/
def mapComp (f : X ⟶ Y) (g : Y ⟶ Z) [Mono f] [Mono g] : map (f ≫ g) ≅ map f ⋙ map g :=
  liftIso _ _ (Over.mapComp _ _) ≪≫ (liftComp _ _ _ _).symm

variable (X) in
/-- `MonoOver.map` preserves the identity (up to a natural isomorphism). -/
/-
**CategoryTheory.MonoOver.mapId** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.MonoOv
er`。
形式化陈述：mapId : map (𝟙 X) ≅ 𝟭 _
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instMonoId`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] (X : C),   CategoryTheory.Mono (CategoryTheory.CategoryStruct.id X)

--- 原说明 ---
`MonoOver.map` preserves the identity (up to a natural isomorphism).
-/
def mapId : map (𝟙 X) ≅ 𝟭 _ :=
  liftIso _ _ (Over.mapId X) ≪≫ liftId

@[simp]
/-
**CategoryTheory.MonoOver.map_obj_left** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.MonoOver`。
形式化陈述：map_obj_left (f : X ⟶ Y) [Mono f] (g : MonoOver X) : ((map f).obj g : C) =
 g.obj.left
参数：f : X ⟶ Y；g : MonoOver X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_obj_left (f : X ⟶ Y) [Mono f] (g : MonoOver X) : ((map f).obj g : C) = g.obj.left :=
  rfl

@[simp]
/-
**CategoryTheory.MonoOver.map_obj_arrow** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.MonoOver`。
形式化陈述：map_obj_arrow (f : X ⟶ Y) [Mono f] (g : MonoOver X) : ((map f).obj g).arro
w = g.arrow ≫ f
参数：f : X ⟶ Y；g : MonoOver X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_obj_arrow (f : X ⟶ Y) [Mono f] (g : MonoOver X) : ((map f).obj g).arrow = g.arrow ≫ f :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.MonoOver.full_map** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mon
oOver`。
形式化陈述：full_map (f : X ⟶ Y) [Mono f] : Functor.Full (map f) where map_surjective 
{g h} e
参数：f : X ⟶ Y。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.MonoOver.w`：w {f g : MonoOver X} (k : f ⟶ g) : k.hom.left
 ≫ g.arrow = f.arrow
-/
instance full_map (f : X ⟶ Y) [Mono f] : Functor.Full (map f) where
  map_surjective {g h} e := by
    refine ⟨homMk e.hom.left ?_, rfl⟩
    · rw [← cancel_mono f, assoc]
      apply w e
/-
**CategoryTheory.MonoOver.faithful_map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.MonoOver`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f :
 X ⟶ Y) [inst_1 : CategoryTheory.Mono f],   (CategoryTheory.MonoOver.map f).Fait
hful
参数：f : X ⟶ Y；CategoryTheory.MonoOver.map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
instance faithful_map (f : X ⟶ Y) [Mono f] : Functor.Faithful (map f) where

/-- Isomorphic objects have equivalent `MonoOver` categories.
-/
@[simps]
/-
**CategoryTheory.MonoOver.mapIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.MonoO
ver`。
形式化陈述：mapIso {A B : C} (e : A ≅ B) : MonoOver A ≌ MonoOver B where functor
参数：e : A ≅ B。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instMonoId`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] (X : C),   CategoryTheory.Mono (CategoryTheory.CategoryStruct.id X)

--- 原说明 ---
Isomorphic objects have equivalent `MonoOver` categories.
-/
def mapIso {A B : C} (e : A ≅ B) : MonoOver A ≌ MonoOver B where
  functor := map e.hom
  inverse := map e.inv
  unitIso := ((mapComp _ _).symm ≪≫ eqToIso (by simp) ≪≫ (mapId _)).symm
  counitIso := (mapComp _ _).symm ≪≫ eqToIso (by simp) ≪≫ (mapId _)

section

variable (X)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- An equivalence of categories `e` between `C` and `D` induces an equivalence between
`MonoOver X` and `MonoOver (e.functor.obj X)` whenever `X` is an object of `C`. -/
@[simps]
/-
**CategoryTheory.MonoOver.congr** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.MonoOv
er`。
形式化陈述：congr (e : C ≌ D) : MonoOver X ≌ MonoOver (e.functor.obj X) where functor
参数：e : C ≌ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence of categories `e` between `C` and `D` induces an equivalence betw
een
`MonoOver X` and `MonoOver (e.functor.obj X)` whenever `X` is an object of `C`.
-/
def congr (e : C ≌ D) : MonoOver X ≌ MonoOver (e.functor.obj X) where
  functor :=
    lift (Over.post e.functor) fun f => by
      dsimp
      infer_instance
  inverse :=
    (lift (Over.post e.inverse) fun f => by
        dsimp
        infer_instance) ⋙
      (mapIso (e.unitIso.symm.app X)).functor
  unitIso := NatIso.ofComponents fun Y => isoMk (e.unitIso.app Y)
  counitIso := NatIso.ofComponents fun Y => isoMk (e.counitIso.app Y)

end

section

variable [HasPullbacks C]

/-- `map f` is left adjoint to `pullback f` when `f` is a monomorphism -/
/-
**CategoryTheory.MonoOver.mapPullbackAdj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.MonoOver`。
形式化陈述：mapPullbackAdj (f : X ⟶ Y) [Mono f] : map f ⊣ pullback f
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`map f` is left adjoint to `pullback f` when `f` is a monomorphism
-/
def mapPullbackAdj (f : X ⟶ Y) [Mono f] : map f ⊣ pullback f :=
  (Over.mapPullbackAdj f).restrictFullyFaithful (fullyFaithfulForget X) (fullyFaithfulForget Y)
    (Iso.refl _) (Iso.refl _)

/-- `MonoOver.map f` followed by `MonoOver.pullback f` is the identity. -/
/-
**CategoryTheory.MonoOver.pullbackMapSelf** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.MonoOver`。
形式化陈述：pullbackMapSelf (f : X ⟶ Y) [Mono f] : map f ⋙ pullback f ≅ 𝟭 _
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`MonoOver.map f` followed by `MonoOver.pullback f` is the identity.
-/
def pullbackMapSelf (f : X ⟶ Y) [Mono f] : map f ⋙ pullback f ≅ 𝟭 _ :=
  (asIso (MonoOver.mapPullbackAdj f).unit).symm

end

end Map

section Image

variable (f : X ⟶ Y) [HasImage f]

/-- The `MonoOver Y` for the image inclusion for a morphism `f : X ⟶ Y`.
-/
/-
**CategoryTheory.MonoOver.imageMonoOver** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.MonoOver`。
形式化陈述：imageMonoOver (f : X ⟶ Y) [HasImage f] : MonoOver Y
参数：f : X ⟶ Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instMonoι`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasIma
ge f], CategoryTheory…

--- 原说明 ---
The `MonoOver Y` for the image inclusion for a morphism `f : X ⟶ Y`.
-/
def imageMonoOver (f : X ⟶ Y) [HasImage f] : MonoOver Y :=
  MonoOver.mk (image.ι f)

@[simp]
/-
**CategoryTheory.MonoOver.imageMonoOver_arrow** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.MonoOver`。
形式化陈述：imageMonoOver_arrow (f : X ⟶ Y) [HasImage f] : (imageMonoOver f).arrow = i
mage.ι f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem imageMonoOver_arrow (f : X ⟶ Y) [HasImage f] : (imageMonoOver f).arrow = image.ι f :=
  rfl

end Image

section Image

variable [HasImages C]

/-- Taking the image of a morphism gives a functor `Over X ⥤ MonoOver X`.
-/
@[simps]
/-
**CategoryTheory.MonoOver.image** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.MonoOv
er`。
形式化陈述：image : Over X ⥤ MonoOver X where obj f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Taking the image of a morphism gives a functor `Over X ⥤ MonoOver X`.
-/
def image : Over X ⥤ MonoOver X where
  obj f := imageMonoOver f.hom
  map {f g} k := by
    apply (forget X).preimage _
    apply Over.homMk _ _
    · exact
        image.lift
          { I := Limits.image _
            m := image.ι g.hom
            e := k.left ≫ factorThruImage g.hom }
    · apply image.lift_fac

set_option backward.isDefEq.respectTransparency false in
/-- `MonoOver.image : Over X ⥤ MonoOver X` is left adjoint to
`MonoOver.forget : MonoOver X ⥤ Over X`
-/
/-
**CategoryTheory.MonoOver.imageForgetAdj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.MonoOver`。
形式化陈述：imageForgetAdj : image ⊣ forget X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`MonoOver.image : Over X ⥤ MonoOver X` is left adjoint to
`MonoOver.forget : MonoOver X ⥤ Over X`
-/
def imageForgetAdj : image ⊣ forget X :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun f g =>
        { toFun := fun k => by
            apply Over.homMk (factorThruImage f.hom ≫ k.hom.left) _
            rw [assoc, Over.w k.hom]
            apply image.fac
          invFun k :=
            homMk
              (image.lift
                { I := g.obj.left
                  m := g.arrow
                  e := k.left
                  fac := Over.w k }) (image.lift_fac _)
          left_inv _ := Subsingleton.elim _ _
          right_inv k := by ext; simp } }
/-
**CategoryTheory.MonoOver.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.MonoOver`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget X).IsRightAdjoint :=
  ⟨_, ⟨imageForgetAdj⟩⟩
/-
**CategoryTheory.MonoOver.reflective** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.M
onoOver`。
形式化陈述：reflective : Reflective (forget X) where L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance reflective : Reflective (forget X) where
  L := image
  adj := imageForgetAdj

/-- Forgetting that a monomorphism over `X` is a monomorphism, then taking its image,
is the identity functor.
-/
/-
**CategoryTheory.MonoOver.forgetImage** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
MonoOver`。
形式化陈述：forgetImage : forget X ⋙ image ≅ 𝟭 (MonoOver X)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Forgetting that a monomorphism over `X` is a monomorphism, then taking its image
,
is the identity functor.
-/
def forgetImage : forget X ⋙ image ≅ 𝟭 (MonoOver X) :=
  asIso (Adjunction.counit imageForgetAdj)

end Image

section Exists

variable [HasImages C]

/-- In the case where `f` is not a monomorphism but `C` has images,
we can still take the "forward map" under it, which agrees with `MonoOver.map f`.
-/
/-
**CategoryTheory.MonoOver.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.MonoOver`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In the case where `f` is not a monomorphism but `C` has images,
we can still take the "forward map" under it, which agrees with `MonoOver.map f`
.
-/
def «exists» (f : X ⟶ Y) : MonoOver X ⥤ MonoOver Y :=
  forget _ ⋙ Over.map f ⋙ image
/-
**CategoryTheory.MonoOver.faithful_exists** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.MonoOver`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y : C} [ins
t_1 : CategoryTheory.Limits.HasImages C]   (f : X ⟶ Y), (CategoryTheory.MonoOver
.exists f).Faithful
参数：f : X ⟶ Y；CategoryTheory.MonoOver.exists f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
instance faithful_exists (f : X ⟶ Y) : Functor.Faithful («exists» f) where

set_option backward.isDefEq.respectTransparency false in
/-- When `f : X ⟶ Y` is a monomorphism, `exists f` agrees with `map f`.
-/
/-
**CategoryTheory.MonoOver.existsIsoMap** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.MonoOver`。
形式化陈述：existsIsoMap (f : X ⟶ Y) [Mono f] : «exists» f ≅ map f
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `f : X ⟶ Y` is a monomorphism, `exists f` agrees with `map f`.
-/
def existsIsoMap (f : X ⟶ Y) [Mono f] : «exists» f ≅ map f :=
  NatIso.ofComponents (by
    intro Z
    suffices (forget _).obj ((«exists» f).obj Z) ≅ (forget _).obj ((map f).obj Z) by
      apply (forget _).preimageIso this
    apply Over.isoMk _ _
    · apply imageMonoIsoSource (Z.arrow ≫ f)
    · apply imageMonoIsoSource_hom_self)

/-- `exists` is adjoint to `pullback` when images exist -/
/-
**CategoryTheory.MonoOver.existsPullbackAdj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.MonoOver`。
形式化陈述：existsPullbackAdj (f : X ⟶ Y) [HasPullbacks C] : «exists» f ⊣ pullback f
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`exists` is adjoint to `pullback` when images exist
-/
def existsPullbackAdj (f : X ⟶ Y) [HasPullbacks C] : «exists» f ⊣ pullback f :=
  ((Over.mapPullbackAdj f).comp imageForgetAdj).restrictFullyFaithful
    (fullyFaithfulForget X) (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)

end Exists

end MonoOver

end CategoryTheory

