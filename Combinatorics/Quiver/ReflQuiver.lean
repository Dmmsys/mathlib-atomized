/-
Copyright (c) 2024 Mario Carneiro and Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Emily Riehl
-/
module

public import Mathlib.Data.Set.Function
public import Mathlib.CategoryTheory.Category.Cat

/-!
# Reflexive Quivers

This module defines reflexive quivers. A reflexive quiver, or "refl quiver" for short, extends
a quiver with a specified endoarrow on each term in its type of objects.

We also introduce morphisms between reflexive quivers, called reflexive prefunctors or "refl
prefunctors" for short.

Note: Currently Category does not extend ReflQuiver, although it could. (TODO: do this)
-/

@[expose] public section

namespace CategoryTheory
universe v v₁ v₂ u u₁ u₂

/-- A reflexive quiver extends a quiver with a specified arrow `id X : X ⟶ X` for each `X` in its
type of objects. We denote these arrows by `id` since categories can be understood as an extension
of refl quivers.
-/
/-
**CategoryTheory.ReflQuiver** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：Type u → Type (max u (v + 1))
参数：max u (v + 1)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A reflexive quiver extends a quiver with a specified arrow `id X : X ⟶ X` for ea
ch `X` in its
type of objects. We denote these arrows by `id` since categories can be understo
od as an extension
of refl quivers.
-/
class ReflQuiver (obj : Type u) : Type max u (v + 1) extends Quiver.{v} obj where
  /-- The identity morphism on an object. -/
  id : ∀ X : obj, Hom X X

/-- Notation for the identity morphism in a category. -/
scoped notation "𝟙rq" => ReflQuiver.id  -- type as \b1

@[simp]
/-
**CategoryTheory.ReflQuiver.homOfEq_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.ReflQuiver`。
形式化陈述：∀ {V : Type u_1} [inst : CategoryTheory.ReflQuiver V] {X X' : V} (hX : X =
 X'),   Quiver.homOfEq (CategoryTheory.ReflQuiver.id X) hX hX = CategoryTheory.R
eflQuiver.id X'
参数：hX : X = X'；CategoryTheory.ReflQuiver.id X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ReflQuiver.homOfEq_id {V : Type*} [ReflQuiver V] {X X' : V} (hX : X = X') :
    Quiver.homOfEq (𝟙rq X) hX hX = 𝟙rq X' := by subst hX; rfl
/-
**CategoryTheory.catToReflQuiver** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：catToReflQuiver {C : Type u} [inst : Category.{v} C] : ReflQuiver.{v, u} C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance catToReflQuiver {C : Type u} [inst : Category.{v} C] : ReflQuiver.{v, u} C :=
  { inst with }
/-
**CategoryTheory.ReflQuiver.id_eq_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.R
eflQuiver`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (X : C),   
CategoryTheory.ReflQuiver.id X = CategoryTheory.CategoryStruct.id X
参数：X : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem ReflQuiver.id_eq_id {C : Type*} [Category* C] (X : C) : 𝟙rq X = 𝟙 X := rfl

/-- A morphism of reflexive quivers called a `ReflPrefunctor`. -/
/-
**CategoryTheory.ReflPrefunctor** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory`。
形式化陈述：ReflPrefunctor (V : Type u₁) [ReflQuiver.{v₁} V] (W : Type u₂) [ReflQuiver
.{v₂} W] extends Prefunctor V W where /-- A functor preserves identity morphisms
. -/ map_id : forall X : V, map (𝟙rq X) = 𝟙rq (obj X)
参数：V : Type u₁；W : Type u₂。
继承自：Prefunctor V W。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of reflexive quivers called a `ReflPrefunctor`.
-/
structure ReflPrefunctor (V : Type u₁) [ReflQuiver.{v₁} V] (W : Type u₂) [ReflQuiver.{v₂} W]
    extends Prefunctor V W where
  /-- A functor preserves identity morphisms. -/
  map_id : ∀ X : V, map (𝟙rq X) = 𝟙rq (obj X) := by cat_disch

namespace ReflPrefunctor

attribute [simp] map_id

-- These lemmas cannot be `@[simp]` because after `whnfR` they have a variable on the LHS.
-- Nevertheless they are sometimes useful when building functors.
/-
**CategoryTheory.ReflPrefunctor.mk_obj** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.ReflPrefunctor`。
形式化陈述：mk_obj {V W : Type*} [ReflQuiver V] [ReflQuiver W] {obj : V -> W} {map} {X
 : V} : (Prefunctor.mk obj map).obj X = obj X
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk_obj {V W : Type*} [ReflQuiver V] [ReflQuiver W] {obj : V → W} {map} {X : V} :
    (Prefunctor.mk obj map).obj X = obj X := rfl
/-
**CategoryTheory.ReflPrefunctor.mk_map** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.ReflPrefunctor`。
形式化陈述：mk_map {V W : Type*} [ReflQuiver V] [ReflQuiver W] {obj : V -> W} {map} {X
 Y : V} {f : X ⟶ Y} : (Prefunctor.mk obj map).map f = map f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk_map {V W : Type*} [ReflQuiver V] [ReflQuiver W] {obj : V → W} {map} {X Y : V} {f : X ⟶ Y} :
    (Prefunctor.mk obj map).map f = map f := rfl

/-- Proving equality between reflexive prefunctors. This isn't an extensionality lemma,
  because usually you don't really want to do this. -/
/-
**CategoryTheory.ReflPrefunctor.ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Re
flPrefunctor`。
形式化陈述：ext {V : Type u} [ReflQuiver.{v₁} V] {W : Type u₂} [ReflQuiver.{v₂} W] {F 
G : ReflPrefunctor V W} (h_obj : forall X, F.obj X = G.obj X) (h_map : forall (X
 Y : V) (f : X ⟶ Y), F.map f = Eq.recOn (h_obj Y).symm (Eq.recOn (h_obj X).symm 
(G.map f))) : F = G
参数：h_obj : forall X, F.obj X = G.obj X；h_map : forall (X Y : V) (f : X ⟶ Y), F.m
ap f = Eq.recOn (h_obj Y).symm (Eq.recOn (h_obj X).symm (G.map f))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.eqOn_univ`：eqOn_univ (f₁ f₂ : α -> β) : EqOn f₁ f₂ univ ↔ f₁ = f₂

--- 原说明 ---
Proving equality between reflexive prefunctors. This isn't an extensionality lem
ma,
  because usually you don't really want to do this.
-/
theorem ext {V : Type u} [ReflQuiver.{v₁} V] {W : Type u₂} [ReflQuiver.{v₂} W]
    {F G : ReflPrefunctor V W}
    (h_obj : ∀ X, F.obj X = G.obj X)
    (h_map : ∀ (X Y : V) (f : X ⟶ Y),
      F.map f = Eq.recOn (h_obj Y).symm (Eq.recOn (h_obj X).symm (G.map f))) : F = G := by
  obtain ⟨⟨F_obj⟩⟩ := F
  obtain ⟨⟨G_obj⟩⟩ := G
  obtain rfl : F_obj = G_obj := (Set.eqOn_univ F_obj G_obj).mp fun _ _ ↦ h_obj _
  congr
  funext X Y f
  simpa using h_map X Y f

/-- This may be a more useful form of `ReflPrefunctor.ext`. -/
/-
**CategoryTheory.ReflPrefunctor.ext'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.R
eflPrefunctor`。
形式化陈述：ext' {V W : Type u} [ReflQuiver.{v} V] [ReflQuiver.{v} W] {F G : ReflPrefu
nctor V W} (h_obj : forall X, F.obj X = G.obj X) (h_map : forall (X Y : V) (f : 
X ⟶ Y), F.map f = Quiver.homOfEq (G.map f) (h_obj _).symm (h_obj _).symm) : F = 
G
参数：h_obj : forall X, F.obj X = G.obj X；h_map : forall (X Y : V) (f : X ⟶ Y), F.m
ap f = Quiver.homOfEq (G.map f) (h_obj _).symm (h_obj _).symm。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Prefunctor.ext'`：ext' {V W : Type u} [Quiver V] [Quiver W] {F G : Prefun
ctor V W} (h_obj : forall X, F.obj X = G.obj X) (h_map : forall (X Y : V) (f : X
 ⟶ Y)…

--- 原说明 ---
This may be a more useful form of `ReflPrefunctor.ext`.
-/
theorem ext' {V W : Type u} [ReflQuiver.{v} V] [ReflQuiver.{v} W]
    {F G : ReflPrefunctor V W}
    (h_obj : ∀ X, F.obj X = G.obj X)
    (h_map : ∀ (X Y : V) (f : X ⟶ Y),
      F.map f = Quiver.homOfEq (G.map f) (h_obj _).symm (h_obj _).symm) : F = G := by
  obtain ⟨Fpre, Fid⟩ := F
  obtain ⟨Gpre, Gid⟩ := G
  obtain rfl : Fpre = Gpre := Prefunctor.ext' (V := V) (W := W) h_obj h_map
  rfl

/-- The identity morphism between reflexive quivers. -/
@[simps!]
/-
**CategoryTheory.ReflPrefunctor.id** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Ref
lPrefunctor`。
形式化陈述：id (V : Type*) [ReflQuiver V] : ReflPrefunctor V V where __
参数：V : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity morphism between reflexive quivers.
-/
def id (V : Type*) [ReflQuiver V] : ReflPrefunctor V V where
  __ := Prefunctor.id _
  map_id _ := rfl
/-
**CategoryTheory.ReflPrefunctor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ReflP
refunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (V : Type*) [ReflQuiver V] : Inhabited (ReflPrefunctor V V) :=
  ⟨id V⟩

set_option backward.defeqAttrib.useBackward true in
/-- Composition of morphisms between reflexive quivers. -/
@[simps!]
/-
**CategoryTheory.ReflPrefunctor.comp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.R
eflPrefunctor`。
形式化陈述：comp {U : Type*} [ReflQuiver U] {V : Type*} [ReflQuiver V] {W : Type*} [Re
flQuiver W] (F : ReflPrefunctor U V) (G : ReflPrefunctor V W) : ReflPrefunctor U
 W where __
参数：F : ReflPrefunctor U V；G : ReflPrefunctor V W。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of morphisms between reflexive quivers.
-/
def comp {U : Type*} [ReflQuiver U] {V : Type*} [ReflQuiver V] {W : Type*} [ReflQuiver W]
    (F : ReflPrefunctor U V) (G : ReflPrefunctor V W) : ReflPrefunctor U W where
  __ := F.toPrefunctor.comp G.toPrefunctor
  map_id _ := by simp [F.map_id, G.map_id]

@[simp]
/-
**CategoryTheory.ReflPrefunctor.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.ReflPrefunctor`。
形式化陈述：comp_id {U V : Type*} [ReflQuiver U] [ReflQuiver V] (F : ReflPrefunctor U 
V) : F.comp (id _) = F
参数：F : ReflPrefunctor U V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_id {U V : Type*} [ReflQuiver U] [ReflQuiver V] (F : ReflPrefunctor U V) :
    F.comp (id _) = F := rfl

@[simp]
/-
**CategoryTheory.ReflPrefunctor.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.ReflPrefunctor`。
形式化陈述：id_comp {U V : Type*} [ReflQuiver U] [ReflQuiver V] (F : ReflPrefunctor U 
V) : (id _).comp F = F
参数：F : ReflPrefunctor U V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_comp {U V : Type*} [ReflQuiver U] [ReflQuiver V] (F : ReflPrefunctor U V) :
    (id _).comp F = F := rfl

@[simp]
/-
**CategoryTheory.ReflPrefunctor.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.ReflPrefunctor`。
形式化陈述：comp_assoc {U V W Z : Type*} [ReflQuiver U] [ReflQuiver V] [ReflQuiver W] 
[ReflQuiver Z] (F : ReflPrefunctor U V) (G : ReflPrefunctor V W) (H : ReflPrefun
ctor W Z) : (F.comp G).comp H = F.comp (G.comp H)
参数：F : ReflPrefunctor U V；G : ReflPrefunctor V W；H : ReflPrefunctor W Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_assoc {U V W Z : Type*} [ReflQuiver U] [ReflQuiver V] [ReflQuiver W] [ReflQuiver Z]
    (F : ReflPrefunctor U V) (G : ReflPrefunctor V W) (H : ReflPrefunctor W Z) :
    (F.comp G).comp H = F.comp (G.comp H) := rfl

/-- Notation for a prefunctor between reflexive quivers. -/
infixl:50 " ⥤rq " => ReflPrefunctor

/-- Notation for composition of reflexive prefunctors. -/
infixl:60 " ⋙rq " => ReflPrefunctor.comp

/-- Notation for the identity prefunctor on a reflexive quiver. -/
notation "𝟭rq" => id

/-
**CategoryTheory.ReflPrefunctor.congr_map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.ReflPrefunctor`。
形式化陈述：congr_map {U V : Type*} [ReflQuiver U] [ReflQuiver V] (F : U ⥤rq V) {X Y :
 U} {f g : X ⟶ Y} (h : f = g) : F.map f = F.map g
参数：F : U ⥤rq V；h : f = g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem congr_map {U V : Type*} [ReflQuiver U] [ReflQuiver V] (F : U ⥤rq V) {X Y : U}
    {f g : X ⟶ Y} (h : f = g) : F.map f = F.map g := congrArg F.map h

/-- An equality of refl prefunctors gives an equality on objects. -/
/-
**CategoryTheory.ReflPrefunctor.congr_obj** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.ReflPrefunctor`。
形式化陈述：congr_obj {U V : Type*} [ReflQuiver U] [ReflQuiver V] {F G : U ⥤rq V} (e :
 F = G) (X : U) : F.obj X = G.obj X
参数：e : F = G；X : U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
An equality of refl prefunctors gives an equality on objects.
-/
theorem congr_obj {U V : Type*} [ReflQuiver U] [ReflQuiver V] {F G : U ⥤rq V}
    (e : F = G) (X : U) : F.obj X = G.obj X := by cases e; rfl

/-- An equality of refl prefunctors gives an equality on homs. -/
/-
**CategoryTheory.ReflPrefunctor.congr_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.ReflPrefunctor`。
形式化陈述：congr_hom {U V : Type*} [ReflQuiver U] [ReflQuiver V] {F G : U ⥤rq V} (e :
 F = G) {X Y : U} (f : X ⟶ Y) : Quiver.homOfEq (F.map f) (congr_obj e X) (congr_
obj e Y) = G.map f
参数：e : F = G；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ReflPrefunctor.congr_obj`：congr_obj {U V : Type*} [ReflQu
iver U] [ReflQuiver V] {F G : U ⥤rq V} (e : F = G) (X : U) : F.obj X = G.obj X
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
An equality of refl prefunctors gives an equality on homs.
-/
theorem congr_hom {U V : Type*} [ReflQuiver U] [ReflQuiver V] {F G : U ⥤rq V}
    (e : F = G) {X Y : U} (f : X ⟶ Y) :
    Quiver.homOfEq (F.map f) (congr_obj e X) (congr_obj e Y) = G.map f := by
  subst e
  simp

end ReflPrefunctor

/-- A functor has an underlying refl prefunctor. -/
/-
**CategoryTheory.Functor.toReflPrefunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Functor`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] → CategoryTh
eory.Functor C D → C ⥤rq D
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…

--- 原说明 ---
A functor has an underlying refl prefunctor.
-/
def Functor.toReflPrefunctor {C D} [Category* C] [Category* D] (F : C ⥤ D) : C ⥤rq D := { F with }
/-
**CategoryTheory.Functor.toReflPrefunctor.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Functor.toReflPrefunctor`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} {E : Type u_3} [inst : CategoryTheory.Cate
gory.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : C
ategoryTheory.Category.{v_3, u_3} E]   (F : CategoryTheory.Functor C D) (G : Cat
egoryTheory.Functor D E),   (F.comp G).toReflPrefunctor = F.toReflPrefunctor ⋙rq
 G.toReflPrefunctor
参数：F : CategoryTheory.Functor C D；G : CategoryTheory.Functor D E；F.comp G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Functor.toReflPrefunctor.map_comp {C D E} [Category* C] [Category* D] [Category* E]
    (F : C ⥤ D) (G : D ⥤ E) :
    toReflPrefunctor (F ⋙ G) = toReflPrefunctor F ⋙rq toReflPrefunctor G := rfl

@[simp]
/-
**CategoryTheory.Functor.toReflPrefunctor_toPrefunctor** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Functor`。
形式化陈述：∀ {C : CategoryTheory.Cat} {D : CategoryTheory.Cat} (F : CategoryTheory.Fu
nctor ↑C ↑D),   F.toReflPrefunctor.toPrefunctor = F.toPrefunctor
参数：F : CategoryTheory.Functor ↑C ↑D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Functor.toReflPrefunctor_toPrefunctor {C D : Cat} (F : C ⥤ D) :
    (Functor.toReflPrefunctor F).toPrefunctor = F.toPrefunctor := rfl

namespace ReflQuiver
open Opposite

/-- `Vᵒᵖ` reverses the direction of all arrows of `V`. -/
/-
**CategoryTheory.ReflQuiver.opposite** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.R
eflQuiver`。
形式化陈述：opposite {V} [ReflQuiver V] : ReflQuiver Vᵒᵖ where id X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Vᵒᵖ` reverses the direction of all arrows of `V`.
-/
instance opposite {V} [ReflQuiver V] : ReflQuiver Vᵒᵖ where
  id X := op (𝟙rq X.unop)
/-
**CategoryTheory.ReflQuiver.discreteReflQuiver** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.ReflQuiver`。
形式化陈述：discreteReflQuiver (V : Type u) : ReflQuiver.{u} (Discrete V)
参数：V : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance discreteReflQuiver (V : Type u) : ReflQuiver.{u} (Discrete V) :=
  { discreteCategory V with }

end ReflQuiver

end CategoryTheory

