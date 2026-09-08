/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn, Kim Morrison
-/
module

public import Mathlib.Combinatorics.Quiver.Basic

/-!
# Morphisms of quivers
-/

@[expose] public section

universe v₁ v₂ u u₁ u₂

/-- A morphism of quivers. As we will later have categorical functors extend this structure,
we call it a `Prefunctor`. -/
/-
**Prefunctor** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(V : Type u₁) → [Quiver V] → (W : Type u₂) → [Quiver W] → Type (max (max (
max u₁ u₂) v₁) v₂)
参数：max (max u₁ u₂) v₁。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of quivers. As we will later have categorical functors extend this st
ructure,
we call it a `Prefunctor`.
-/
structure Prefunctor (V : Type u₁) [Quiver.{v₁} V] (W : Type u₂) [Quiver.{v₂} W] where
  /-- The action of a (pre)functor on vertices/objects. -/
  obj : V → W
  /-- The action of a (pre)functor on edges/arrows/morphisms. -/
  map : ∀ {X Y : V}, (X ⟶ Y) → (obj X ⟶ obj Y)

attribute [to_dual self] Prefunctor.map

namespace Prefunctor

-- These lemmas cannot be `@[simp]` because after `whnfR` they have a variable on the LHS.
-- Nevertheless they are sometimes useful when building functors.
/-
**Prefunctor.mk_obj** 是 Mathlib 中的一个引理，位于命名空间 `Prefunctor`。
形式化陈述：mk_obj {V W : Type*} [Quiver V] [Quiver W] {obj : V -> W} {map} {X : V} : 
(Prefunctor.mk obj map).obj X = obj X
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk_obj {V W : Type*} [Quiver V] [Quiver W] {obj : V → W} {map} {X : V} :
    (Prefunctor.mk obj map).obj X = obj X := rfl
/-
**Prefunctor.mk_map** 是 Mathlib 中的一个引理，位于命名空间 `Prefunctor`。
形式化陈述：mk_map {V W : Type*} [Quiver V] [Quiver W] {obj : V -> W} {map} {X Y : V} 
{f : X ⟶ Y} : (Prefunctor.mk obj map).map f = map f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk_map {V W : Type*} [Quiver V] [Quiver W] {obj : V → W} {map} {X Y : V} {f : X ⟶ Y} :
    (Prefunctor.mk obj map).map f = map f := rfl

@[ext (iff := false)]
/-
**Prefunctor.ext** 是 Mathlib 中的一个定理，位于命名空间 `Prefunctor`。
形式化陈述：ext {V : Type u} [Quiver.{v₁} V] {W : Type u₂} [Quiver.{v₂} W] {F G : Pref
unctor V W} (h_obj : forall X, F.obj X = G.obj X) (h_map : forall (X Y : V) (f :
 X ⟶ Y), F.map f = Eq.recOn (h_obj Y).symm (Eq.recOn (h_obj X).symm (G.map f))) 
: F = G
参数：h_obj : forall X, F.obj X = G.obj X；h_map : forall (X Y : V) (f : X ⟶ Y), F.m
ap f = Eq.recOn (h_obj Y).symm (Eq.recOn (h_obj X).symm (G.map f))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem ext {V : Type u} [Quiver.{v₁} V] {W : Type u₂} [Quiver.{v₂} W] {F G : Prefunctor V W}
    (h_obj : ∀ X, F.obj X = G.obj X)
    (h_map : ∀ (X Y : V) (f : X ⟶ Y),
      F.map f = Eq.recOn (h_obj Y).symm (Eq.recOn (h_obj X).symm (G.map f))) : F = G := by
  obtain ⟨F_obj, _⟩ := F
  obtain ⟨G_obj, _⟩ := G
  obtain rfl : F_obj = G_obj := by
    ext X
    apply h_obj
  congr
  funext X Y f
  simpa using h_map X Y f

/-- This may be a more useful form of `Prefunctor.ext`. -/
/-
**Prefunctor.ext'** 是 Mathlib 中的一个定理，位于命名空间 `Prefunctor`。
形式化陈述：ext' {V W : Type u} [Quiver V] [Quiver W] {F G : Prefunctor V W} (h_obj : 
forall X, F.obj X = G.obj X) (h_map : forall (X Y : V) (f : X ⟶ Y), F.map f = Qu
iver.homOfEq (G.map f) (h_obj _).symm (h_obj _).symm) : F = G
参数：h_obj : forall X, F.obj X = G.obj X；h_map : forall (X Y : V) (f : X ⟶ Y), F.m
ap f = Quiver.homOfEq (G.map f) (h_obj _).symm (h_obj _).symm。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Prefunctor.mk.injEq`：∀ {V : Type u₁} [inst : Quiver V] {W : Type u₂} [in
st_1 : Quiver W] (obj : V → W)   (map : {X Y : V} → (X ⟶ Y) → (obj X ⟶ obj Y)) (
obj_1 : V…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
This may be a more useful form of `Prefunctor.ext`.
-/
theorem ext' {V W : Type u} [Quiver V] [Quiver W] {F G : Prefunctor V W}
    (h_obj : ∀ X, F.obj X = G.obj X)
    (h_map : ∀ (X Y : V) (f : X ⟶ Y),
      F.map f = Quiver.homOfEq (G.map f) (h_obj _).symm (h_obj _).symm) : F = G := by
  obtain ⟨Fobj, Fmap⟩ := F
  obtain ⟨Gobj, Gmap⟩ := G
  obtain rfl : Fobj = Gobj := funext h_obj
  simp only [mk.injEq, heq_eq_eq, true_and]
  ext X Y f
  simpa only [Quiver.homOfEq_rfl] using h_map X Y f

/-- The identity morphism between quivers. -/
@[simps]
/-
**Prefunctor.id** 是 Mathlib 中的一个定义，位于命名空间 `Prefunctor`。
形式化陈述：id (V : Type*) [Quiver V] : Prefunctor V V where obj
参数：V : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity morphism between quivers.
-/
def id (V : Type*) [Quiver V] : Prefunctor V V where
  obj := fun X => X
  map f := f
/-
**Prefunctor.** 是 Mathlib 中的一个实例，位于命名空间 `Prefunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (V : Type*) [Quiver V] : Inhabited (Prefunctor V V) :=
  ⟨id V⟩

/-- Composition of morphisms between quivers. -/
@[simps]
/-
**Prefunctor.comp** 是 Mathlib 中的一个定义，位于命名空间 `Prefunctor`。
形式化陈述：comp {U : Type*} [Quiver U] {V : Type*} [Quiver V] {W : Type*} [Quiver W] 
(F : Prefunctor U V) (G : Prefunctor V W) : Prefunctor U W where obj X
参数：F : Prefunctor U V；G : Prefunctor V W。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of morphisms between quivers.
-/
def comp {U : Type*} [Quiver U] {V : Type*} [Quiver V] {W : Type*} [Quiver W]
    (F : Prefunctor U V) (G : Prefunctor V W) : Prefunctor U W where
  obj X := G.obj (F.obj X)
  map f := G.map (F.map f)

@[simp]
/-
**Prefunctor.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `Prefunctor`。
形式化陈述：comp_id {U V : Type*} [Quiver U] [Quiver V] (F : Prefunctor U V) : F.comp 
(id _) = F
参数：F : Prefunctor U V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_id {U V : Type*} [Quiver U] [Quiver V] (F : Prefunctor U V) :
    F.comp (id _) = F := rfl

@[simp]
/-
**Prefunctor.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `Prefunctor`。
形式化陈述：id_comp {U V : Type*} [Quiver U] [Quiver V] (F : Prefunctor U V) : (id _).
comp F = F
参数：F : Prefunctor U V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_comp {U V : Type*} [Quiver U] [Quiver V] (F : Prefunctor U V) :
    (id _).comp F = F := rfl

@[simp]
/-
**Prefunctor.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Prefunctor`。
形式化陈述：comp_assoc {U V W Z : Type*} [Quiver U] [Quiver V] [Quiver W] [Quiver Z] (
F : Prefunctor U V) (G : Prefunctor V W) (H : Prefunctor W Z) : (F.comp G).comp 
H = F.comp (G.comp H)
参数：F : Prefunctor U V；G : Prefunctor V W；H : Prefunctor W Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_assoc {U V W Z : Type*} [Quiver U] [Quiver V] [Quiver W] [Quiver Z]
    (F : Prefunctor U V) (G : Prefunctor V W) (H : Prefunctor W Z) :
    (F.comp G).comp H = F.comp (G.comp H) :=
  rfl

/-- Notation for a prefunctor between quivers. -/
infixl:50 " ⥤q " => Prefunctor

/-- Notation for composition of prefunctors. -/
infixl:60 " ⋙q " => Prefunctor.comp

/-- Notation for the identity prefunctor on a quiver. -/
notation "𝟭q" => id

@[to_dual self]
/-
**Prefunctor.congr_map** 是 Mathlib 中的一个定理，位于命名空间 `Prefunctor`。
形式化陈述：congr_map {U V : Type*} [Quiver U] [Quiver V] (F : U ⥤q V) {X Y : U} {f g 
: X ⟶ Y} (h : f = g) : F.map f = F.map g
参数：F : U ⥤q V；h : f = g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem congr_map {U V : Type*} [Quiver U] [Quiver V] (F : U ⥤q V) {X Y : U} {f g : X ⟶ Y}
    (h : f = g) : F.map f = F.map g := by
  rw [h]

/-- An equality of prefunctors gives an equality on objects. -/
/-
**Prefunctor.congr_obj** 是 Mathlib 中的一个定理，位于命名空间 `Prefunctor`。
形式化陈述：congr_obj {U V : Type*} [Quiver U] [Quiver V] {F G : U ⥤q V} (e : F = G) (
X : U) : F.obj X = G.obj X
参数：e : F = G；X : U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
An equality of prefunctors gives an equality on objects.
-/
theorem congr_obj {U V : Type*} [Quiver U] [Quiver V] {F G : U ⥤q V} (e : F = G) (X : U) :
    F.obj X = G.obj X := by cases e; rfl

/-- An equality of prefunctors gives an equality on homs. -/
@[to_dual self]
/-
**Prefunctor.congr_hom** 是 Mathlib 中的一个定理，位于命名空间 `Prefunctor`。
形式化陈述：congr_hom {U V : Type*} [Quiver U] [Quiver V] {F G : U ⥤q V} (e : F = G) {
X Y : U} (f : X ⟶ Y) : Quiver.homOfEq (F.map f) (congr_obj e X) (congr_obj e Y) 
= G.map f
参数：e : F = G；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prefunctor.congr_obj`：congr_obj {U V : Type*} [Quiver U] [Quiver V] {F G
 : U ⥤q V} (e : F = G) (X : U) : F.obj X = G.obj X
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
An equality of prefunctors gives an equality on homs.
-/
theorem congr_hom {U V : Type*} [Quiver U] [Quiver V] {F G : U ⥤q V} (e : F = G) {X Y : U}
    (f : X ⟶ Y) : Quiver.homOfEq (F.map f) (congr_obj e X) (congr_obj e Y) = G.map f := by
  subst e
  simp

/-- Prefunctors commute with `homOfEq`. -/
@[simp, to_dual self]
/-
**Prefunctor.homOfEq_map** 是 Mathlib 中的一个定理，位于命名空间 `Prefunctor`。
形式化陈述：homOfEq_map {U V : Type*} [Quiver U] [Quiver V] (F : U ⥤q V) {X Y : U} (f 
: X ⟶ Y) {X' Y' : U} (hX : X = X') (hY : Y = Y') : F.map (Quiver.homOfEq f hX hY
) = Quiver.homOfEq (F.map f) (congr_arg F.obj hX) (congr_arg F.obj hY)
参数：F : U ⥤q V；f : X ⟶ Y；hX : X = X'；hY : Y = Y'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Prefunctors commute with `homOfEq`.
-/
theorem homOfEq_map {U V : Type*} [Quiver U] [Quiver V] (F : U ⥤q V) {X Y : U} (f : X ⟶ Y)
    {X' Y' : U} (hX : X = X') (hY : Y = Y') :
    F.map (Quiver.homOfEq f hX hY) =
      Quiver.homOfEq (F.map f) (congr_arg F.obj hX) (congr_arg F.obj hY) := by subst hX hY; simp

end Prefunctor

