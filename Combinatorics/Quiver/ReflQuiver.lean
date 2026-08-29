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

/--
Definition of `ReflQuiver` / `ReflQuiver` 的定义

English:
class ReflQuiver
  parameters: (obj : Type u)
  extends: Quiver.{v} obj
  axioms and operations (1):
    - id : forall X : obj, Hom X X

中文:
类 ReflQuiver
  参数: (obj : 类型u)
  继承: 箭图.{v} obj
  公理与运算 (1 个):
    - id : 对任意 X : obj, 态射 X X
-/
class ReflQuiver (obj : Type u) : Type max u (v + 1) extends Quiver.{v} obj where
  /-- The identity morphism on an object. -/
  id : forall X : obj, Hom X X

/-- Notation for the identity morphism in a category. -/
scoped notation "𝟙rq" => ReflQuiver.id -- type as \b1

@[simp]
/--
theorem `ReflQuiver.homOfEq_id` / 定理 `ReflQuiver.homOfEq_id`

English:
theorem ReflQuiver.homOfEq_id
  given: {V : Type*} [ReflQuiver V] {X X' : V} (hX : X = X')
  proof: by subst hX; rfl

中文:
定理 ReflQuiver.homOfEq_id
  条件: {V : 类型} [ReflQuiver V] {X X' : V} (hX : X = X')
  证明: by subst hX; rfl
-/
theorem ReflQuiver.homOfEq_id {V : Type*} [ReflQuiver V] {X X' : V} (hX : X = X') :
    Quiver.homOfEq (𝟙rq X) hX hX = 𝟙rq X' := by subst hX; rfl

/--
Instance `catToReflQuiver` / 实例 `catToReflQuiver`

English:
instance catToReflQuiver
  signature: {C : Type u} [inst : Category.{v} C]
  body: { inst with }

中文:
实例 catToReflQuiver
  签名: {C : 类型u} [inst : 范畴.{v} C]
  定义体: { inst with }
-/
instance catToReflQuiver {C : Type u} [inst : Category.{v} C] : ReflQuiver.{v, u} C :=
  { inst with }

/--
theorem `ReflQuiver.id_eq_id` / 定理 `ReflQuiver.id_eq_id`

English:
theorem ReflQuiver.id_eq_id
  given: {C : Type*} [Category* C] (X : C)
  statement: 𝟙rq X = 𝟙 X
  proof: rfl

中文:
定理 ReflQuiver.id_eq_id
  条件: {C : 类型} [范畴* C] (X : C)
  结论: 𝟙rq X = 𝟙 X
  证明: rfl
-/
@[simp] theorem ReflQuiver.id_eq_id {C : Type*} [Category* C] (X : C) : 𝟙rq X = 𝟙 X := rfl

/--
Definition of `ReflPrefunctor` / `ReflPrefunctor` 的定义

English:
structure ReflPrefunctor
  parameters: (V : Type u₁) [ReflQuiver.{v₁} V] (W : Type u₂) [ReflQuiver.{v₂} W]
  extends: Prefunctor V W
  axioms and operations (1):
    - map_id : forall X : V, map (𝟙rq X) = 𝟙rq (obj X)  [default: by cat_disch]

中文:
结构 ReflPrefunctor
  参数: (V : 类型u₁) [ReflQuiver.{v₁} V] (W : 类型u₂) [ReflQuiver.{v₂} W]
  继承: 预函子 V W
  公理与运算 (1 个):
    - map_id : 对任意 X : V, map (𝟙rq X) = 𝟙rq (obj X)  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure ReflPrefunctor (V : Type u₁) [ReflQuiver.{v₁} V] (W : Type u₂) [ReflQuiver.{v₂} W]
    extends Prefunctor V W where
  /-- A functor preserves identity morphisms. -/
  map_id : forall X : V, map (𝟙rq X) = 𝟙rq (obj X) := by cat_disch

namespace ReflPrefunctor

attribute [simp] map_id

-- These lemmas cannot be `@[simp]` because after `whnfR` they have a variable on the LHS.
-- Nevertheless they are sometimes useful when building functors.
/--
lemma `mk_obj` / 引理 `mk_obj`

English:
lemma mk_obj
  given: {V W : Type*} [ReflQuiver V] [ReflQuiver W] {obj : V -> W} {map} {X : V}
  proof: rfl

中文:
引理 mk_obj
  条件: {V W : 类型} [ReflQuiver V] [ReflQuiver W] {obj : V -> W} {map} {X : V}
  证明: rfl
-/
lemma mk_obj {V W : Type*} [ReflQuiver V] [ReflQuiver W] {obj : V -> W} {map} {X : V} :
    (Prefunctor.mk obj map).obj X = obj X := rfl

/--
lemma `mk_map` / 引理 `mk_map`

English:
lemma mk_map
  given: {V W : Type*} [ReflQuiver V] [ReflQuiver W] {obj : V -> W} {map} {X Y : V} {f : X ⟶ Y}
  proof: rfl

中文:
引理 mk_map
  条件: {V W : 类型} [ReflQuiver V] [ReflQuiver W] {obj : V -> W} {map} {X Y : V} {f : X ⟶ Y}
  证明: rfl
-/
lemma mk_map {V W : Type*} [ReflQuiver V] [ReflQuiver W] {obj : V -> W} {map} {X Y : V} {f : X ⟶ Y} :
    (Prefunctor.mk obj map).map f = map f := rfl

/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  statement: {V : Type u} [ReflQuiver.{v₁} V] {W : Type u₂} [ReflQuiver.{v₂} W]
  proof: by
  obtain ⟨⟨F_obj⟩⟩ := F
  obtain ⟨⟨G_obj⟩⟩ := G
  obtain rfl : F_obj = G_obj := (Set.eqOn_univ F_obj G_obj).mp fun _ _ => h_obj _
  congr
  funext X Y f
  simpa using h_map X Y f

中文:
定理 ext
  结论: {V : 类型u} [ReflQuiver.{v₁} V] {W : 类型u₂} [ReflQuiver.{v₂} W]
  证明: by
  obtain ⟨⟨F_obj⟩⟩ := F
  obtain ⟨⟨G_obj⟩⟩ := G
  obtain rfl : F_obj = G_obj := (Set.eqOn_univ F_obj G_obj).mp fun _ _ => h_obj _
  congr
  funext X Y f
  simpa using h_map X Y f

Depends on / 依赖: F_obj, G_obj, Set.eqOn_univ, eqOn_univ, h_map, h_obj
-/
theorem ext {V : Type u} [ReflQuiver.{v₁} V] {W : Type u₂} [ReflQuiver.{v₂} W]
    {F G : ReflPrefunctor V W}
    (h_obj : forall X, F.obj X = G.obj X)
    (h_map : forall (X Y : V) (f : X ⟶ Y),
      F.map f = Eq.recOn (h_obj Y).symm (Eq.recOn (h_obj X).symm (G.map f))) : F = G := by
  obtain ⟨⟨F_obj⟩⟩ := F
  obtain ⟨⟨G_obj⟩⟩ := G
  obtain rfl : F_obj = G_obj := (Set.eqOn_univ F_obj G_obj).mp fun _ _ => h_obj _
  congr
  funext X Y f
  simpa using h_map X Y f

/--
theorem `ext'` / 定理 `ext'`

English:
theorem ext'
  statement: {V W : Type u} [ReflQuiver.{v} V] [ReflQuiver.{v} W]
  proof: by
  obtain ⟨Fpre, Fid⟩ := F
  obtain ⟨Gpre, Gid⟩ := G
  obtain rfl : Fpre = Gpre := Prefunctor.ext' (V := V) (W := W) h_obj h_map
  rfl

中文:
定理 ext'
  结论: {V W : 类型u} [ReflQuiver.{v} V] [ReflQuiver.{v} W]
  证明: by
  obtain ⟨Fpre, Fid⟩ := F
  obtain ⟨Gpre, Gid⟩ := G
  obtain rfl : Fpre = Gpre := Prefunctor.ext' (V := V) (W := W) h_obj h_map
  rfl

Depends on / 依赖: Prefunctor, Prefunctor.ext, h_map, h_obj
-/
theorem ext' {V W : Type u} [ReflQuiver.{v} V] [ReflQuiver.{v} W]
    {F G : ReflPrefunctor V W}
    (h_obj : forall X, F.obj X = G.obj X)
    (h_map : forall (X Y : V) (f : X ⟶ Y),
      F.map f = Quiver.homOfEq (G.map f) (h_obj _).symm (h_obj _).symm) : F = G := by
  obtain ⟨Fpre, Fid⟩ := F
  obtain ⟨Gpre, Gid⟩ := G
  obtain rfl : Fpre = Gpre := Prefunctor.ext' (V := V) (W := W) h_obj h_map
  rfl

/-- The identity morphism between reflexive quivers. -/
@[simps!]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: (V : Type*) [ReflQuiver V]
  body: Prefunctor.id _
  map_id _ := rfl

中文:
定义 id
  签名: (V : 类型) [ReflQuiver V]
  定义体: Prefunctor.id _
  map_id _ := rfl

Depends on / 依赖: Prefunctor, Prefunctor.id
-/
def id (V : Type*) [ReflQuiver V] : ReflPrefunctor V V where
  __ := Prefunctor.id _
  map_id _ := rfl

instance (V : Type*) [ReflQuiver V] : Inhabited (ReflPrefunctor V V) :=
  ⟨id V⟩

set_option backward.defeqAttrib.useBackward true in
/-- Composition of morphisms between reflexive quivers. -/
@[simps!]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: {U : Type*} [ReflQuiver U] {V : Type*} [ReflQuiver V] {W : Type*} [ReflQuiver W]
  body: F.toPrefunctor.comp G.toPrefunctor
  map_id _ := by simp [F.map_id, G.map_id]

@[simp]

中文:
定义 comp
  签名: {U : 类型} [ReflQuiver U] {V : 类型} [ReflQuiver V] {W : 类型} [ReflQuiver W]
  定义体: F.toPrefunctor.comp G.toPrefunctor
  map_id _ := by simp [F.map_id, G.map_id]

@[simp]

Depends on / 依赖: F.toPrefunctor.comp, G.toPrefunctor, toPrefunctor
-/
def comp {U : Type*} [ReflQuiver U] {V : Type*} [ReflQuiver V] {W : Type*} [ReflQuiver W]
    (F : ReflPrefunctor U V) (G : ReflPrefunctor V W) : ReflPrefunctor U W where
  __ := F.toPrefunctor.comp G.toPrefunctor
  map_id _ := by simp [F.map_id, G.map_id]

@[simp]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: {U V : Type*} [ReflQuiver U] [ReflQuiver V] (F : ReflPrefunctor U V)
  proof: rfl

@[simp]

中文:
定理 comp_id
  条件: {U V : 类型} [ReflQuiver U] [ReflQuiver V] (F : ReflPrefunctor U V)
  证明: rfl

@[simp]
-/
theorem comp_id {U V : Type*} [ReflQuiver U] [ReflQuiver V] (F : ReflPrefunctor U V) :
    F.comp (id _) = F := rfl

@[simp]
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  given: {U V : Type*} [ReflQuiver U] [ReflQuiver V] (F : ReflPrefunctor U V)
  proof: rfl

@[simp]

中文:
定理 id_comp
  条件: {U V : 类型} [ReflQuiver U] [ReflQuiver V] (F : ReflPrefunctor U V)
  证明: rfl

@[simp]
-/
theorem id_comp {U V : Type*} [ReflQuiver U] [ReflQuiver V] (F : ReflPrefunctor U V) :
    (id _).comp F = F := rfl

@[simp]
/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  statement: {U V W Z : Type*} [ReflQuiver U] [ReflQuiver V] [ReflQuiver W] [ReflQuiver Z]
  proof: rfl

中文:
定理 comp_assoc
  结论: {U V W Z : 类型} [ReflQuiver U] [ReflQuiver V] [ReflQuiver W] [ReflQuiver Z]
  证明: rfl
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

/--
theorem `congr_map` / 定理 `congr_map`

English:
theorem congr_map
  statement: {U V : Type*} [ReflQuiver U] [ReflQuiver V] (F : U ⥤rq V) {X Y : U}
  proof: congrArg F.map h

中文:
定理 congr_map
  结论: {U V : 类型} [ReflQuiver U] [ReflQuiver V] (F : U ⥤rq V) {X Y : U}
  证明: congrArg F.map h

Depends on / 依赖: F.map
-/
theorem congr_map {U V : Type*} [ReflQuiver U] [ReflQuiver V] (F : U ⥤rq V) {X Y : U}
    {f g : X ⟶ Y} (h : f = g) : F.map f = F.map g := congrArg F.map h

/--
theorem `congr_obj` / 定理 `congr_obj`

English:
theorem congr_obj
  statement: {U V : Type*} [ReflQuiver U] [ReflQuiver V] {F G : U ⥤rq V}
  proof: by cases e; rfl

中文:
定理 congr_obj
  结论: {U V : 类型} [ReflQuiver U] [ReflQuiver V] {F G : U ⥤rq V}
  证明: by cases e; rfl
-/
theorem congr_obj {U V : Type*} [ReflQuiver U] [ReflQuiver V] {F G : U ⥤rq V}
    (e : F = G) (X : U) : F.obj X = G.obj X := by cases e; rfl

/--
theorem `congr_hom` / 定理 `congr_hom`

English:
theorem congr_hom
  statement: {U V : Type*} [ReflQuiver U] [ReflQuiver V] {F G : U ⥤rq V}
  proof: by
  subst e
  simp

中文:
定理 congr_hom
  结论: {U V : 类型} [ReflQuiver U] [ReflQuiver V] {F G : U ⥤rq V}
  证明: by
  subst e
  simp
-/
theorem congr_hom {U V : Type*} [ReflQuiver U] [ReflQuiver V] {F G : U ⥤rq V}
    (e : F = G) {X Y : U} (f : X ⟶ Y) :
    Quiver.homOfEq (F.map f) (congr_obj e X) (congr_obj e Y) = G.map f := by
  subst e
  simp

end ReflPrefunctor

/--
Definition of `Functor.toReflPrefunctor` / `Functor.toReflPrefunctor` 的定义

English:
definition Functor.toReflPrefunctor
  signature: {C D} [Category* C] [Category* D] (F : C ⥤ D)
  body: { F with }

中文:
定义 函子.toReflPrefunctor
  签名: {C D} [范畴* C] [范畴* D] (F : C ⥤ D)
  定义体: { F with }
-/
def Functor.toReflPrefunctor {C D} [Category* C] [Category* D] (F : C ⥤ D) : C ⥤rq D := { F with }

/--
theorem `Functor.toReflPrefunctor.map_comp` / 定理 `Functor.toReflPrefunctor.map_comp`

English:
theorem Functor.toReflPrefunctor.map_comp
  statement: {C D E} [Category* C] [Category* D] [Category* E]
  proof: rfl

@[simp]

中文:
定理 函子.toReflPrefunctor.map_comp
  结论: {C D E} [范畴* C] [范畴* D] [范畴* E]
  证明: rfl

@[simp]
-/
theorem Functor.toReflPrefunctor.map_comp {C D E} [Category* C] [Category* D] [Category* E]
    (F : C ⥤ D) (G : D ⥤ E) :
    toReflPrefunctor (F ⋙ G) = toReflPrefunctor F ⋙rq toReflPrefunctor G := rfl

@[simp]
/--
theorem `Functor.toReflPrefunctor_toPrefunctor` / 定理 `Functor.toReflPrefunctor_toPrefunctor`

English:
theorem Functor.toReflPrefunctor_toPrefunctor
  given: {C D : Cat} (F : C ⥤ D)
  proof: rfl

中文:
定理 函子.toReflPrefunctor_toPrefunctor
  条件: {C D : Cat} (F : C ⥤ D)
  证明: rfl
-/
theorem Functor.toReflPrefunctor_toPrefunctor {C D : Cat} (F : C ⥤ D) :
    (Functor.toReflPrefunctor F).toPrefunctor = F.toPrefunctor := rfl

namespace ReflQuiver
open Opposite

/--
Instance `opposite` / 实例 `opposite`

English:
instance opposite
  signature: {V} [ReflQuiver V]
  body: op (𝟙rq X.unop)

中文:
实例 opposite
  签名: {V} [ReflQuiver V]
  定义体: op (𝟙rq X.unop)

Depends on / 依赖: X.unop
-/
instance opposite {V} [ReflQuiver V] : ReflQuiver Vᵒᵖ where
  id X := op (𝟙rq X.unop)

/--
Instance `discreteReflQuiver` / 实例 `discreteReflQuiver`

English:
instance discreteReflQuiver
  signature: (V : Type u)
  body: { discreteCategory V with }

中文:
实例 discreteReflQuiver
  签名: (V : 类型u)
  定义体: { discreteCategory V with }

Depends on / 依赖: discreteCategory
-/
instance discreteReflQuiver (V : Type u) : ReflQuiver.{u} (Discrete V) :=
  { discreteCategory V with }

end ReflQuiver

end CategoryTheory
