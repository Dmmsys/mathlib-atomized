/-
Copyright (c) 2025 Joseph Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Hua
-/
module

public import Mathlib.CategoryTheory.Groupoid.FreeGroupoid
public import Mathlib.CategoryTheory.Groupoid.Grpd.Basic
public import Mathlib.CategoryTheory.Adjunction.Reflective
public import Mathlib.CategoryTheory.Localization.Predicate

/-!
# Free groupoid on a category

This file defines the free groupoid on a category, the lifting of a functor to its unique
extension as a functor from the free groupoid, and proves uniqueness of this extension.

## Main results

Given a type `C` and a category instance on `C`:

- `CategoryTheory.FreeGroupoid C`: the underlying type of the free groupoid on `C`.
- `CategoryTheory.FreeGroupoid.instGroupoid`: the `Groupoid` instance on `FreeGroupoid C`.
- `CategoryTheory.FreeGroupoid.lift`: the lifting of a functor `C ⥤ G` where `G` is a
  groupoid, to a functor `CategoryTheory.FreeGroupoid C ⥤ G`.
- `CategoryTheory.FreeGroupoid.lift_spec` and
  `CategoryTheory.FreeGroupoid.lift_unique`:
  the proofs that, respectively, `CategoryTheory.FreeGroupoid.lift` indeed is a lifting
  and is the unique one.
- `CategoryTheory.Grpd.free`: the free functor from `Grpd` to `Cat`
- `CategoryTheory.Grpd.freeForgetAdjunction`: that `free` is left adjoint to
  `Grpd.forgetToCat`.

## Implementation notes

The free groupoid on a category `C` is first defined by taking the free groupoid `G`
on the underlying *quiver* of `C`. Then the free groupoid on the *category* `C` is defined as
the quotient of `G` by the relation that makes the inclusion prefunctor `C ⥤q G` a functor.

-/

@[expose] public section

noncomputable section

namespace CategoryTheory

universe v u v₁ u₁ v₂ u₂

variable (C : Type u) [Category.{v} C]

open Quiver in
/-- The relation on the free groupoid on the underlying *quiver* of C that
promotes the prefunctor `C ⥤q FreeGroupoid C` into a functor
`C ⥤ Quotient (FreeGroupoid.homRel C)`. -/
/-
**CategoryTheory.FreeGroupoid.homRel** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory
.FreeGroupoid`。
形式化陈述：(C : Type u) → [inst : CategoryTheory.Category.{v, u} C] → HomRel (Quiver.
FreeGroupoid C)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The relation on the free groupoid on the underlying *quiver* of C that
promotes the prefunctor `C ⥤q FreeGroupoid C` into a functor
`C ⥤ Quotient (FreeGroupoid.homRel C)`.
-/
inductive FreeGroupoid.homRel : HomRel (Quiver.FreeGroupoid C) where
| map_id (X : C) : homRel ((FreeGroupoid.of C).map (𝟙 X)) (𝟙 ((FreeGroupoid.of C).obj X))
| map_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : homRel ((FreeGroupoid.of C).map (f ≫ g))
  ((FreeGroupoid.of C).map f ≫ (FreeGroupoid.of C).map g)

/-- The underlying type of the free groupoid on a category,
defined by quotienting the free groupoid on the underlying quiver of `C`
by the relation that promotes the prefunctor `C ⥤q FreeGroupoid C` into a functor
`C ⥤ Quotient (FreeGroupoid.homRel C)`. -/
/-
**CategoryTheory.FreeGroupoid** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：FreeGroupoid
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying type of the free groupoid on a category,
defined by quotienting the free groupoid on the underlying quiver of `C`
by the relation that promotes the prefunctor `C ⥤q FreeGroupoid C` into a functo
r
`C ⥤ Quotient (FreeGroupoid.homRel C)`.
-/
def FreeGroupoid := Quotient (FreeGroupoid.homRel C)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nonempty C] : Nonempty (FreeGroupoid C) :=
  ⟨Quotient.mk (Quotient.mk ((Paths.of _).obj (Classical.arbitrary C)))⟩
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Groupoid (FreeGroupoid C) :=
  Quotient.groupoid (FreeGroupoid.homRel C)

namespace FreeGroupoid

/-- The localization functor from the category `C` to the groupoid `FreeGroupoid C` -/
/-
**CategoryTheory.FreeGroupoid.of** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.FreeG
roupoid`。
形式化陈述：of : C ⥤ FreeGroupoid C where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The localization functor from the category `C` to the groupoid `FreeGroupoid C`
-/
def of : C ⥤ FreeGroupoid C where
  __ := Quiver.FreeGroupoid.of C ⋙q (Quotient.functor (FreeGroupoid.homRel C)).toPrefunctor
  map_id X := Quotient.sound _ (FreeGroupoid.homRel.map_id X)
  map_comp f g := Quotient.sound _ (FreeGroupoid.homRel.map_comp f g)

variable {C}

/-- Construct an object in the free groupoid on `C` by providing an object in `C`. -/
/-
**CategoryTheory.FreeGroupoid.mk** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Fre
eGroupoid`。
形式化陈述：mk (X : C) : FreeGroupoid C
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an object in the free groupoid on `C` by providing an object in `C`.
-/
abbrev mk (X : C) : FreeGroupoid C := (of C).obj X

/-- Construct a morphism in the free groupoid on `C` by providing a morphism in `C`. -/
/-
**CategoryTheory.FreeGroupoid.homMk** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.
FreeGroupoid`。
形式化陈述：homMk {X Y : C} (f : X ⟶ Y) : mk X ⟶ mk Y
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a morphism in the free groupoid on `C` by providing a morphism in `C`.
-/
abbrev homMk {X Y : C} (f : X ⟶ Y) : mk X ⟶ mk Y := (of C).map f
/-
**CategoryTheory.FreeGroupoid.eq_mk** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Fr
eeGroupoid`。
形式化陈述：eq_mk (X : FreeGroupoid C) : X = .mk (X.as.as)
参数：X : FreeGroupoid C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma eq_mk (X : FreeGroupoid C) : X = .mk (X.as.as) := rfl
/-
**CategoryTheory.FreeGroupoid.of_obj_bijective** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.FreeGroupoid`。
形式化陈述：of_obj_bijective : Function.Bijective (of C).obj where left _ _ h
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma of_obj_bijective : Function.Bijective (of C).obj where
  left _ _ h := by cases h; rfl
  right X := ⟨X.as.as, rfl⟩

section UniversalProperty

variable {G : Type u₁} [Groupoid.{v₁} G]

set_option backward.isDefEq.respectTransparency false in
/-- The lift of a functor from `C` to a groupoid to a functor from
`FreeGroupoid C` to the groupoid -/
/-
**CategoryTheory.FreeGroupoid.lift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Fre
eGroupoid`。
形式化陈述：lift (φ : C ⥤ G) : FreeGroupoid C ⥤ G
参数：φ : C ⥤ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The lift of a functor from `C` to a groupoid to a functor from
`FreeGroupoid C` to the groupoid
-/
def lift (φ : C ⥤ G) : FreeGroupoid C ⥤ G :=
  Quotient.lift (FreeGroupoid.homRel C) (Quiver.FreeGroupoid.lift φ.toPrefunctor)
    (fun _ _ f g r ↦ by
      have {X Y : C} (f : X ⟶ Y) :=
        Prefunctor.congr_hom (Quiver.FreeGroupoid.lift_spec φ.toPrefunctor) f
      induction r <;> cat_disch)

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.FreeGroupoid.lift_spec** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.FreeGroupoid`。
形式化陈述：lift_spec (φ : C ⥤ G) : of C ⋙ lift φ = φ
参数：φ : C ⥤ G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.toPrefunctor_injective`：toPrefunctor_injective {F
 G : C ⥤ D} (h : F.toPrefunctor = G.toPrefunctor) : F = G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Quotient.lift_spec`：lift_spec : functor r ⋙ lift r F H = 
F
· 使用定理 `Quiver.FreeGroupoid.lift_spec`：lift_spec (φ : V ⥤q V') : of V ⋙q (lift φ
).toPrefunctor = φ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_spec (φ : C ⥤ G) : of C ⋙ lift φ = φ :=
  Functor.toPrefunctor_injective (by
    change Quiver.FreeGroupoid.of C ⋙q
      (Quotient.functor (FreeGroupoid.homRel C)).toPrefunctor ⋙q
        (lift φ).toPrefunctor = φ.toPrefunctor
    simp [lift, Quotient.lift_spec, Quiver.FreeGroupoid.lift_spec])

@[simp]
/-
**CategoryTheory.FreeGroupoid.lift_obj_mk** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.FreeGroupoid`。
形式化陈述：lift_obj_mk {E : Type u₂} [Groupoid.{v₂} E] (φ : C ⥤ E) (X : C) : (lift φ)
.obj (mk X) = φ.obj X
参数：φ : C ⥤ E；X : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma lift_obj_mk {E : Type u₂} [Groupoid.{v₂} E] (φ : C ⥤ E) (X : C) :
    (lift φ).obj (mk X) = φ.obj X := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.FreeGroupoid.lift_map_homMk** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.FreeGroupoid`。
形式化陈述：lift_map_homMk {E : Type u₂} [Groupoid.{v₂} E] (φ : C ⥤ E) {X Y : C} (f : 
X ⟶ Y) : (lift φ).map (homMk f) = φ.map f
参数：φ : C ⥤ E；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.congr_obj`：congr_obj {F G : C ⥤ D} (h : F = G) (X
) : F.obj X = G.obj X
· 使用定理 `CategoryTheory.FreeGroupoid.lift_spec`：lift_spec (φ : C ⥤ G) : of C ⋙ li
ft φ = φ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Functor.congr_hom`：congr_hom {F G : C ⥤ D} (h : F = G) {X
 Y} (f : X ⟶ Y) : F.map f = eqToHom (congr_obj h X) ≫ G.map f ≫ eqToHom (congr_o
bj h Y).symm
-/
lemma lift_map_homMk {E : Type u₂} [Groupoid.{v₂} E] (φ : C ⥤ E) {X Y : C} (f : X ⟶ Y) :
    (lift φ).map (homMk f) = φ.map f := by
  simpa using Functor.congr_hom (lift_spec φ) f
/-
**CategoryTheory.FreeGroupoid.lift_unique** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.FreeGroupoid`。
形式化陈述：lift_unique (φ : C ⥤ G) (Φ : FreeGroupoid C ⥤ G) (hΦ : of C ⋙ Φ = φ) : Φ =
 lift φ
参数：φ : C ⥤ G；Φ : FreeGroupoid C ⥤ G；hΦ : of C ⋙ Φ = φ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Quotient.lift_unique`：lift_unique (Φ : Quotient r ⥤ D) (h
Φ : functor r ⋙ Φ = F) : Φ = lift r F H
· 使用定理 `Quiver.FreeGroupoid.lift_unique`：lift_unique (φ : V ⥤q V') (Φ : Quiver.F
reeGroupoid V ⥤ V') (hΦ : of V ⋙q Φ.toPrefunctor = φ) : Φ = lift φ
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem lift_unique (φ : C ⥤ G) (Φ : FreeGroupoid C ⥤ G) (hΦ : of C ⋙ Φ = φ) :
    Φ = lift φ := by
  apply Quotient.lift_unique
  apply Quiver.FreeGroupoid.lift_unique
  exact congr_arg Functor.toPrefunctor hΦ
/-
**CategoryTheory.FreeGroupoid.lift_id_comp_of** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.FreeGroupoid`。
形式化陈述：lift_id_comp_of : lift (𝟭 G) ⋙ of G = 𝟭 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.FreeGroupoid.lift_unique`：lift_unique (φ : C ⥤ G) (Φ : Fr
eeGroupoid C ⥤ G) (hΦ : of C ⋙ Φ = φ) : Φ = lift φ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.assoc`：∀ {C : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   
{E : Type u₃} [ins…
· 使用定理 `CategoryTheory.FreeGroupoid.lift_spec`：lift_spec (φ : C ⥤ G) : of C ⋙ li
ft φ = φ
· 使用定理 `CategoryTheory.Functor.id_comp`：∀ {C : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D] 
  (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.comp_id`：∀ {C : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D] 
  (F : CategoryTheor…
-/
theorem lift_id_comp_of : lift (𝟭 G) ⋙ of G = 𝟭 _ := by
  rw [lift_unique (of G) (lift (𝟭 G) ⋙ of G) (by rw [← Functor.assoc, lift_spec, Functor.id_comp])]
  symm; apply lift_unique
  rw [Functor.comp_id]
/-
**CategoryTheory.FreeGroupoid.lift_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.FreeGroupoid`。
形式化陈述：lift_comp {H : Type u₂} [Groupoid.{v₂} H] (φ : C ⥤ G) (ψ : G ⥤ H) : lift (
φ ⋙ ψ) = lift φ ⋙ ψ
参数：φ : C ⥤ G；ψ : G ⥤ H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.FreeGroupoid.lift_unique`：lift_unique (φ : C ⥤ G) (Φ : Fr
eeGroupoid C ⥤ G) (hΦ : of C ⋙ Φ = φ) : Φ = lift φ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.assoc`：∀ {C : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   
{E : Type u₃} [ins…
· 使用定理 `CategoryTheory.FreeGroupoid.lift_spec`：lift_spec (φ : C ⥤ G) : of C ⋙ li
ft φ = φ
-/
theorem lift_comp {H : Type u₂} [Groupoid.{v₂} H] (φ : C ⥤ G) (ψ : G ⥤ H) :
    lift (φ ⋙ ψ) = lift φ ⋙ ψ := by
  symm
  apply lift_unique
  rw [← Functor.assoc, lift_spec]

/-- The universal property of the free groupoid. -/
/-
**CategoryTheory.FreeGroupoid.strictUniversalPropertyFixedTarget** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory.FreeGroupoid`。
形式化陈述：strictUniversalPropertyFixedTarget : Localization.StrictUniversalPropertyF
ixedTarget (of C) ⊤ G where inverts _
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.FreeGroupoid.lift_spec`：lift_spec (φ : C ⥤ G) : of C ⋙ li
ft φ = φ

--- 原说明 ---
The universal property of the free groupoid.
-/
def strictUniversalPropertyFixedTarget :
    Localization.StrictUniversalPropertyFixedTarget (of C) ⊤ G where
  inverts _ := inferInstance
  lift F _ := lift F
  fac _ _ := lift_spec ..
  uniq F G h := by rw [lift_unique (of C ⋙ G) F h, ← lift_unique (of C ⋙ G) G rfl]

attribute [local instance] Localization.groupoid
/-
**CategoryTheory.FreeGroupoid.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.FreeGro
upoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (of C).IsLocalization ⊤ :=
  .mk' _ _ strictUniversalPropertyFixedTarget strictUniversalPropertyFixedTarget

/-- In order to define a natural isomorphism `F ≅ G` with `F G : FreeGroupoid ⥤ D`,
it suffices to do so after precomposing with `FreeGroupoid.of C`. -/
/-
**CategoryTheory.FreeGroupoid.liftNatIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.FreeGroupoid`。
形式化陈述：liftNatIso (F₁ F₂ : FreeGroupoid C ⥤ G) (τ : of C ⋙ F₁ ≅ of C ⋙ F₂) : F₁ ≅
 F₂
参数：F₁ F₂ : FreeGroupoid C ⥤ G；τ : of C ⋙ F₁ ≅ of C ⋙ F₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.FreeGroupoid.instIsLocalizationOfTopMorphismProperty`：∀ {
C : Type u} [inst : CategoryTheory.Category.{v, u} C], (CategoryTheory.FreeGroup
oid.of C).IsLocalization ⊤

--- 原说明 ---
In order to define a natural isomorphism `F ≅ G` with `F G : FreeGroupoid ⥤ D`,
it suffices to do so after precomposing with `FreeGroupoid.of C`.
-/
def liftNatIso (F₁ F₂ : FreeGroupoid C ⥤ G) (τ : of C ⋙ F₁ ≅ of C ⋙ F₂) : F₁ ≅ F₂ :=
  Localization.liftNatIso (of C) ⊤ (of C ⋙ F₁) (of C ⋙ F₂) _ _ τ

@[simp]
/-
**CategoryTheory.FreeGroupoid.liftNatIso_hom_app** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.FreeGroupoid`。
形式化陈述：liftNatIso_hom_app (F₁ F₂ : FreeGroupoid C ⥤ G) (τ : of C ⋙ F₁ ≅ of C ⋙ F₂
) (X) : (liftNatIso F₁ F₂ τ).hom.app (mk X) = τ.hom.app X
参数：F₁ F₂ : FreeGroupoid C ⥤ G；τ : of C ⋙ F₁ ≅ of C ⋙ F₂；X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.FreeGroupoid.instIsLocalizationOfTopMorphismProperty`：∀ {
C : Type u} [inst : CategoryTheory.Category.{v, u} C], (CategoryTheory.FreeGroup
oid.of C).IsLocalization ⊤
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Localization.liftNatIso_hom`：∀ {C : Type u_1} {D : Type u
_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Cat
egory.{v_2, u_2} D] (L : Categor…
· 使用定理 `CategoryTheory.Localization.liftNatTrans_app`：liftNatTrans_app (F₁ F₂ : 
C ⥤ E) (F₁' F₂' : D ⥤ E) [Lifting L W F₁ F₁'] [Lifting L W F₂ F₂'] (τ : F₁ ⟶ F₂)
 (X : C) : (liftNatTrans L W F₁ F₂…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma liftNatIso_hom_app (F₁ F₂ : FreeGroupoid C ⥤ G) (τ : of C ⋙ F₁ ≅ of C ⋙ F₂) (X) :
    (liftNatIso F₁ F₂ τ).hom.app (mk X) = τ.hom.app X := by
  simp [liftNatIso]

@[simp]
/-
**CategoryTheory.FreeGroupoid.liftNatIso_inv_app** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.FreeGroupoid`。
形式化陈述：liftNatIso_inv_app (F₁ F₂ : FreeGroupoid C ⥤ G) (τ : of C ⋙ F₁ ≅ of C ⋙ F₂
) (X) : (liftNatIso F₁ F₂ τ).inv.app (mk X) = τ.inv.app X
参数：F₁ F₂ : FreeGroupoid C ⥤ G；τ : of C ⋙ F₁ ≅ of C ⋙ F₂；X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.FreeGroupoid.instIsLocalizationOfTopMorphismProperty`：∀ {
C : Type u} [inst : CategoryTheory.Category.{v, u} C], (CategoryTheory.FreeGroup
oid.of C).IsLocalization ⊤
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Localization.liftNatIso_inv`：∀ {C : Type u_1} {D : Type u
_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Cat
egory.{v_2, u_2} D] (L : Categor…
· 使用定理 `CategoryTheory.Localization.liftNatTrans_app`：liftNatTrans_app (F₁ F₂ : 
C ⥤ E) (F₁' F₂' : D ⥤ E) [Lifting L W F₁ F₁'] [Lifting L W F₂ F₂'] (τ : F₁ ⟶ F₂)
 (X : C) : (liftNatTrans L W F₁ F₂…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma liftNatIso_inv_app (F₁ F₂ : FreeGroupoid C ⥤ G) (τ : of C ⋙ F₁ ≅ of C ⋙ F₂) (X) :
    (liftNatIso F₁ F₂ τ).inv.app (mk X) = τ.inv.app X := by
  simp [liftNatIso]

end UniversalProperty

section Functoriality

variable {D : Type u₁} [Category.{v₁} D] {E : Type u₂} [Category.{v₂} E]

/-- The functor between free groupoids induced by a functor between categories. -/
/-
**CategoryTheory.FreeGroupoid.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Free
Groupoid`。
形式化陈述：map (φ : C ⥤ D) : FreeGroupoid C ⥤ FreeGroupoid D
参数：φ : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor between free groupoids induced by a functor between categories.
-/
def map (φ : C ⥤ D) : FreeGroupoid C ⥤ FreeGroupoid D :=
  lift (φ ⋙ of D)
/-
**CategoryTheory.FreeGroupoid.of_comp_map** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.FreeGroupoid`。
形式化陈述：of_comp_map (F : C ⥤ D) : of C ⋙ map F = F ⋙ of D
参数：F : C ⥤ D。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma of_comp_map (F : C ⥤ D) : of C ⋙ map F = F ⋙ of D := rfl

/-- The operation `of` is natural. -/
/-
**CategoryTheory.FreeGroupoid.ofCompMapIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.FreeGroupoid`。
形式化陈述：ofCompMapIso (F : C ⥤ D) : of C ⋙ map F ≅ F ⋙ of D
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The operation `of` is natural.
-/
def ofCompMapIso (F : C ⥤ D) : of C ⋙ map F ≅ F ⋙ of D := Iso.refl _

variable (C) in
/-- The functor induced by the identity is the identity. -/
/-
**CategoryTheory.FreeGroupoid.mapId** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Fr
eeGroupoid`。
形式化陈述：mapId : map (𝟭 C) ≅ 𝟭 (FreeGroupoid C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor induced by the identity is the identity.
-/
def mapId : map (𝟭 C) ≅ 𝟭 (FreeGroupoid C) :=
  liftNatIso _ _ (Iso.refl _)

@[simp]
/-
**CategoryTheory.FreeGroupoid.mapId_hom_app** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.FreeGroupoid`。
形式化陈述：mapId_hom_app (X) : (mapId C).hom.app X = 𝟙 X
参数：X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.FreeGroupoid.liftNatIso_hom_app`：liftNatIso_hom_app (F₁ F
₂ : FreeGroupoid C ⥤ G) (τ : of C ⋙ F₁ ≅ of C ⋙ F₂) (X) : (liftNatIso F₁ F₂ τ).h
om.app (mk X) = τ.hom.app X
-/
lemma mapId_hom_app (X) : (mapId C).hom.app X = 𝟙 X :=
  liftNatIso_hom_app ..

@[simp]
/-
**CategoryTheory.FreeGroupoid.mapId_inv_app** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.FreeGroupoid`。
形式化陈述：mapId_inv_app (X) : (mapId C).inv.app X = 𝟙 X
参数：X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.FreeGroupoid.liftNatIso_inv_app`：liftNatIso_inv_app (F₁ F
₂ : FreeGroupoid C ⥤ G) (τ : of C ⋙ F₁ ≅ of C ⋙ F₂) (X) : (liftNatIso F₁ F₂ τ).i
nv.app (mk X) = τ.inv.app X
-/
lemma mapId_inv_app (X) : (mapId C).inv.app X = 𝟙 X :=
  liftNatIso_inv_app ..

variable (C) in
/-
**CategoryTheory.FreeGroupoid.map_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.F
reeGroupoid`。
形式化陈述：map_id : map (𝟭 C) = 𝟭 (FreeGroupoid C)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.FreeGroupoid.lift_unique`：lift_unique (φ : C ⥤ G) (Φ : Fr
eeGroupoid C ⥤ G) (hΦ : of C ⋙ Φ = φ) : Φ = lift φ
-/
theorem map_id : map (𝟭 C) = 𝟭 (FreeGroupoid C) := by
  symm; apply lift_unique; rfl

/-- The functor induced by a composition is the composition of the functors they induce. -/
/-
**CategoryTheory.FreeGroupoid.mapComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
FreeGroupoid`。
形式化陈述：mapComp (φ : C ⥤ D) (φ' : D ⥤ E) : map (φ ⋙ φ') ≅ map φ ⋙ map φ'
参数：φ : C ⥤ D；φ' : D ⥤ E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor induced by a composition is the composition of the functors they ind
uce.
-/
def mapComp (φ : C ⥤ D) (φ' : D ⥤ E) : map (φ ⋙ φ') ≅ map φ ⋙ map φ' :=
  liftNatIso _ _ (Iso.refl _)

@[simp]
/-
**CategoryTheory.FreeGroupoid.mapComp_hom_app** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.FreeGroupoid`。
形式化陈述：mapComp_hom_app (φ : C ⥤ D) (φ' : D ⥤ E) (X) : (mapComp φ φ').hom.app X = 
𝟙 _
参数：φ : C ⥤ D；φ' : D ⥤ E；X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.FreeGroupoid.liftNatIso_hom_app`：liftNatIso_hom_app (F₁ F
₂ : FreeGroupoid C ⥤ G) (τ : of C ⋙ F₁ ≅ of C ⋙ F₂) (X) : (liftNatIso F₁ F₂ τ).h
om.app (mk X) = τ.hom.app X
-/
lemma mapComp_hom_app (φ : C ⥤ D) (φ' : D ⥤ E) (X) : (mapComp φ φ').hom.app X = 𝟙 _ :=
  liftNatIso_hom_app ..

@[simp]
/-
**CategoryTheory.FreeGroupoid.mapComp_inv_app** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.FreeGroupoid`。
形式化陈述：mapComp_inv_app (φ : C ⥤ D) (φ' : D ⥤ E) (X) : (mapComp φ φ').inv.app X = 
𝟙 _
参数：φ : C ⥤ D；φ' : D ⥤ E；X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.FreeGroupoid.liftNatIso_inv_app`：liftNatIso_inv_app (F₁ F
₂ : FreeGroupoid C ⥤ G) (τ : of C ⋙ F₁ ≅ of C ⋙ F₂) (X) : (liftNatIso F₁ F₂ τ).i
nv.app (mk X) = τ.inv.app X
-/
lemma mapComp_inv_app (φ : C ⥤ D) (φ' : D ⥤ E) (X) : (mapComp φ φ').inv.app X = 𝟙 _ :=
  liftNatIso_inv_app ..
/-
**CategoryTheory.FreeGroupoid.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.FreeGroupoid`。
形式化陈述：map_comp (φ : C ⥤ D) (φ' : D ⥤ E) : map (φ ⋙ φ') = map φ ⋙ map φ'
参数：φ : C ⥤ D；φ' : D ⥤ E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.FreeGroupoid.lift_unique`：lift_unique (φ : C ⥤ G) (Φ : Fr
eeGroupoid C ⥤ G) (hΦ : of C ⋙ Φ = φ) : Φ = lift φ
-/
theorem map_comp (φ : C ⥤ D) (φ' : D ⥤ E) : map (φ ⋙ φ') = map φ ⋙ map φ' := by
  symm; apply lift_unique; rfl

@[simp]
/-
**CategoryTheory.FreeGroupoid.map_obj_mk** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.FreeGroupoid`。
形式化陈述：map_obj_mk (φ : C ⥤ D) (X : C) : (map φ).obj (mk X) = mk (φ.obj X)
参数：φ : C ⥤ D；X : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_obj_mk (φ : C ⥤ D) (X : C) : (map φ).obj (mk X) = mk (φ.obj X) := rfl

@[simp]
/-
**CategoryTheory.FreeGroupoid.map_map_homMk** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.FreeGroupoid`。
形式化陈述：map_map_homMk (φ : C ⥤ D) {X Y : C} (f : X ⟶ Y) : (map φ).map (homMk f) = 
homMk (φ.map f)
参数：φ : C ⥤ D；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_map_homMk (φ : C ⥤ D) {X Y : C} (f : X ⟶ Y) :
    (map φ).map (homMk f) = homMk (φ.map f) := rfl

variable {E : Type u₂} [Groupoid.{v₂} E]
/-
**CategoryTheory.FreeGroupoid.map_comp_lift** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.FreeGroupoid`。
形式化陈述：map_comp_lift (F : C ⥤ D) (G : D ⥤ E) : map F ⋙ lift G = lift (F ⋙ G)
参数：F : C ⥤ D；G : D ⥤ E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.FreeGroupoid.lift_unique`：lift_unique (φ : C ⥤ G) (Φ : Fr
eeGroupoid C ⥤ G) (hΦ : of C ⋙ Φ = φ) : Φ = lift φ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.assoc`：∀ {C : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   
{E : Type u₃} [ins…
· 使用引理 `CategoryTheory.FreeGroupoid.of_comp_map`：of_comp_map (F : C ⥤ D) : of C 
⋙ map F = F ⋙ of D
· 使用定理 `CategoryTheory.FreeGroupoid.lift_spec`：lift_spec (φ : C ⥤ G) : of C ⋙ li
ft φ = φ
-/
lemma map_comp_lift (F : C ⥤ D) (G : D ⥤ E) : map F ⋙ lift G = lift (F ⋙ G) := by
  apply lift_unique
  rw [← Functor.assoc, of_comp_map, Functor.assoc, lift_spec G]

/-- The operation `lift` is natural. -/
/-
**CategoryTheory.FreeGroupoid.mapCompLift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.FreeGroupoid`。
形式化陈述：mapCompLift (F : C ⥤ D) (G : D ⥤ E) : map F ⋙ lift G ≅ lift (F ⋙ G)
参数：F : C ⥤ D；G : D ⥤ E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The operation `lift` is natural.
-/
def mapCompLift (F : C ⥤ D) (G : D ⥤ E) : map F ⋙ lift G ≅ lift (F ⋙ G) :=
  liftNatIso _ _ (Iso.refl _)

@[simp]
/-
**CategoryTheory.FreeGroupoid.mapCompLift_hom_app** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.FreeGroupoid`。
形式化陈述：mapCompLift_hom_app (F : C ⥤ D) (G : D ⥤ E) (X) : (mapCompLift F G).hom.ap
p X = 𝟙 _
参数：F : C ⥤ D；G : D ⥤ E；X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.FreeGroupoid.liftNatIso_hom_app`：liftNatIso_hom_app (F₁ F
₂ : FreeGroupoid C ⥤ G) (τ : of C ⋙ F₁ ≅ of C ⋙ F₂) (X) : (liftNatIso F₁ F₂ τ).h
om.app (mk X) = τ.hom.app X
-/
lemma mapCompLift_hom_app (F : C ⥤ D) (G : D ⥤ E) (X) : (mapCompLift F G).hom.app X = 𝟙 _ :=
  liftNatIso_hom_app ..

@[simp]
/-
**CategoryTheory.FreeGroupoid.mapCompLift_inv_app** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.FreeGroupoid`。
形式化陈述：mapCompLift_inv_app (F : C ⥤ D) (G : D ⥤ E) (X) : (mapCompLift F G).inv.ap
p X = 𝟙 _
参数：F : C ⥤ D；G : D ⥤ E；X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.FreeGroupoid.liftNatIso_inv_app`：liftNatIso_inv_app (F₁ F
₂ : FreeGroupoid C ⥤ G) (τ : of C ⋙ F₁ ≅ of C ⋙ F₂) (X) : (liftNatIso F₁ F₂ τ).i
nv.app (mk X) = τ.inv.app X
-/
lemma mapCompLift_inv_app (F : C ⥤ D) (G : D ⥤ E) (X) : (mapCompLift F G).inv.app X = 𝟙 _ :=
  liftNatIso_inv_app ..

end Functoriality

/-- Functors out of the free groupoid biject with functors out of the original category. -/
@[simps]
/-
**CategoryTheory.FreeGroupoid.functorEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.FreeGroupoid`。
形式化陈述：functorEquiv {D : Type*} [Groupoid D] : (FreeGroupoid C ⥤ D) ≃ (C ⥤ D) whe
re toFun G
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.FreeGroupoid.lift_spec`：lift_spec (φ : C ⥤ G) : of C ⋙ li
ft φ = φ

--- 原说明 ---
Functors out of the free groupoid biject with functors out of the original categ
ory.
-/
def functorEquiv {D : Type*} [Groupoid D] : (FreeGroupoid C ⥤ D) ≃ (C ⥤ D) where
  toFun G := of C ⋙ G
  invFun F := lift F
  right_inv := lift_spec
  left_inv _ := (lift_unique _ _ rfl).symm

end FreeGroupoid

namespace Grpd

open FreeGroupoid

set_option backward.isDefEq.respectTransparency false in
/-- The free groupoid construction on a category as a functor. -/
/-
**CategoryTheory.Grpd.free** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Grpd`。
形式化陈述：free : Cat.{u, u} ⥤ Grpd.{u, u} where obj C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The free groupoid construction on a category as a functor.
-/
def free : Cat.{u, u} ⥤ Grpd.{u, u} where
  obj C := Grpd.of <| FreeGroupoid C
  map {C D} F := map F.toFunctor
  map_id C := by simp [map_id, id_eq_id]
  map_comp F G := by simp [Grpd.comp_eq_comp, map_comp]

@[simp]
/-
**CategoryTheory.Grpd.free_obj** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Grpd`。
形式化陈述：free_obj (C : Cat.{u, u}) : free.obj C = FreeGroupoid C
参数：C : Cat.{u, u}。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma free_obj (C : Cat.{u, u}) : free.obj C = FreeGroupoid C :=
  rfl

@[simp]
/-
**CategoryTheory.Grpd.free_map** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Grpd`。
形式化陈述：free_map {C D : Cat.{u, u}} (F : C ⟶ D) : free.map F = map F.toFunctor
参数：F : C ⟶ D。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma free_map {C D : Cat.{u, u}} (F : C ⟶ D) : free.map F = map F.toFunctor :=
  rfl

/-- The free-forgetful adjunction between `Grpd` and `Cat`. -/
/-
**CategoryTheory.Grpd.freeForgetAdjunction** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Grpd`。
形式化陈述：freeForgetAdjunction : free ⊣ Grpd.forgetToCat
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
The free-forgetful adjunction between `Grpd` and `Cat`.
-/
def freeForgetAdjunction : free ⊣ Grpd.forgetToCat :=
  Adjunction.mkOfHomEquiv
    { homEquiv _ _ := FreeGroupoid.functorEquiv.trans (Functor.equivCatHom _ _)
      homEquiv_naturality_left_symm _ _ := (FreeGroupoid.map_comp_lift _ _).symm
      homEquiv_naturality_right _ _ := rfl }

variable {C : Type u} [Category.{u} C] {D : Type u} [Groupoid.{u} D]

@[simp]
/-
**CategoryTheory.Grpd.freeForgetAdjunction_homEquiv_apply** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Grpd`。
形式化陈述：freeForgetAdjunction_homEquiv_apply (F : FreeGroupoid C ⥤ D) : (freeForget
Adjunction.homEquiv (Cat.of C) (Grpd.of D) F).toFunctor = FreeGroupoid.of C ⋙ F
参数：F : FreeGroupoid C ⥤ D。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma freeForgetAdjunction_homEquiv_apply (F : FreeGroupoid C ⥤ D) :
    (freeForgetAdjunction.homEquiv (Cat.of C) (Grpd.of D) F).toFunctor = FreeGroupoid.of C ⋙ F :=
  rfl

@[simp]
/-
**CategoryTheory.Grpd.freeForgetAdjunction_homEquiv_symm_apply** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Grpd`。
形式化陈述：freeForgetAdjunction_homEquiv_symm_apply (F : C ⥤ D) : (freeForgetAdjuncti
on.homEquiv (Cat.of C) (Grpd.of D)).symm F.toCatHom = map F ⋙ lift (𝟭 D)
参数：F : C ⥤ D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma freeForgetAdjunction_homEquiv_symm_apply (F : C ⥤ D) :
    (freeForgetAdjunction.homEquiv (Cat.of C) (Grpd.of D)).symm F.toCatHom = map F ⋙ lift (𝟭 D) :=
  rfl

@[simp]
/-
**CategoryTheory.Grpd.freeForgetAdjunction_unit_app** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Grpd`。
形式化陈述：freeForgetAdjunction_unit_app : (freeForgetAdjunction.unit.app (Cat.of C))
.toFunctor = FreeGroupoid.of C
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma freeForgetAdjunction_unit_app :
    (freeForgetAdjunction.unit.app (Cat.of C)).toFunctor = FreeGroupoid.of C :=
  rfl

@[simp]
/-
**CategoryTheory.Grpd.freeForgetAdjunction_counit_app** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Grpd`。
形式化陈述：freeForgetAdjunction_counit_app : freeForgetAdjunction.counit.app (Grpd.of
 D) = lift (𝟭 D)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma freeForgetAdjunction_counit_app :
    freeForgetAdjunction.counit.app (Grpd.of D) = lift (𝟭 D) :=
  rfl
/-
**CategoryTheory.Grpd.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Grpd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Reflective Grpd.forgetToCat where
  L := free
  adj := freeForgetAdjunction

end Grpd
end CategoryTheory
end

