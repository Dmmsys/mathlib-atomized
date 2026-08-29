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

/--
Definition of `Prefunctor` / `Prefunctor` 的定义

English:
structure Prefunctor
  parameters: (V : Type u₁) [Quiver.{v₁} V] (W : Type u₂) [Quiver.{v₂} W]
  axioms and operations (2):
    - obj : V -> W
    - map : forall {X Y : V}, (X ⟶ Y) -> (obj X ⟶ obj Y)

中文:
结构 Prefunctor
  参数: (V : 类型u₁) [Quiver.{v₁} V] (W : 类型u₂) [Quiver.{v₂} W]
  公理与运算 (2 个):
    - obj : V -> W
    - map : 对任意 {X Y : V}, (X ⟶ Y) -> (obj X ⟶ obj Y)

Depends on / 依赖: AddEquiv, AddEquiv.ext, mapRange_id
-/
structure Prefunctor (V : Type u₁) [Quiver.{v₁} V] (W : Type u₂) [Quiver.{v₂} W] where
  /-- The action of a (pre)functor on vertices/objects. -/
  obj : V -> W
  /-- The action of a (pre)functor on edges/arrows/morphisms. -/
  map : forall {X Y : V}, (X ⟶ Y) -> (obj X ⟶ obj Y)

attribute [to_dual self] Prefunctor.map

namespace Prefunctor

-- These lemmas cannot be `@[simp]` because after `whnfR` they have a variable on the LHS.
-- Nevertheless they are sometimes useful when building functors.
/--
lemma `mk_obj` / 引理 `mk_obj`

English:
lemma mk_obj
  given: {V W : Type*} [Quiver V] [Quiver W] {obj : V -> W} {map} {X : V}
  proof: rfl

中文:
引理 mk_obj
  条件: {V W : 类型} [Quiver V] [Quiver W] {obj : V -> W} {map} {X : V}
  证明: rfl
-/
lemma mk_obj {V W : Type*} [Quiver V] [Quiver W] {obj : V -> W} {map} {X : V} :
    (Prefunctor.mk obj map).obj X = obj X := rfl

/--
lemma `mk_map` / 引理 `mk_map`

English:
lemma mk_map
  given: {V W : Type*} [Quiver V] [Quiver W] {obj : V -> W} {map} {X Y : V} {f : X ⟶ Y}
  proof: rfl

@[ext (iff := false)]

中文:
引理 mk_map
  条件: {V W : 类型} [Quiver V] [Quiver W] {obj : V -> W} {map} {X Y : V} {f : X ⟶ Y}
  证明: rfl

@[ext (iff := false)]
-/
lemma mk_map {V W : Type*} [Quiver V] [Quiver W] {obj : V -> W} {map} {X Y : V} {f : X ⟶ Y} :
    (Prefunctor.mk obj map).map f = map f := rfl

@[ext (iff := false)]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  statement: {V : Type u} [Quiver.{v₁} V] {W : Type u₂} [Quiver.{v₂} W] {F G : Prefunctor V W}
  proof: by
  obtain ⟨F_obj, _⟩ := F
  obtain ⟨G_obj, _⟩ := G
  obtain rfl : F_obj = G_obj := by
    ext X
    apply h_obj
  congr
  funext X Y f
  simpa using h_map X Y f

中文:
定理 ext
  结论: {V : 类型u} [Quiver.{v₁} V] {W : 类型u₂} [Quiver.{v₂} W] {F G : Prefunctor V W}
  证明: by
  obtain ⟨F_obj, _⟩ := F
  obtain ⟨G_obj, _⟩ := G
  obtain rfl : F_obj = G_obj := by
    ext X
    apply h_obj
  congr
  funext X Y f
  simpa using h_map X Y f

Depends on / 依赖: F_obj, G_obj, h_map, h_obj
-/
theorem ext {V : Type u} [Quiver.{v₁} V] {W : Type u₂} [Quiver.{v₂} W] {F G : Prefunctor V W}
    (h_obj : forall X, F.obj X = G.obj X)
    (h_map : forall (X Y : V) (f : X ⟶ Y),
      F.map f = Eq.recOn (h_obj Y).symm (Eq.recOn (h_obj X).symm (G.map f))) : F = G := by
  obtain ⟨F_obj, _⟩ := F
  obtain ⟨G_obj, _⟩ := G
  obtain rfl : F_obj = G_obj := by
    ext X
    apply h_obj
  congr
  funext X Y f
  simpa using h_map X Y f

/--
theorem `ext'` / 定理 `ext'`

English:
theorem ext'
  statement: {V W : Type u} [Quiver V] [Quiver W] {F G : Prefunctor V W}
  proof: by
  obtain ⟨Fobj, Fmap⟩ := F
  obtain ⟨Gobj, Gmap⟩ := G
  obtain rfl : Fobj = Gobj := funext h_obj
  simp only [mk.injEq, heq_eq_eq, true_and]
  ext X Y f
  simpa only [Quiver.homOfEq_rfl] using h_map X Y f

中文:
定理 ext'
  结论: {V W : 类型u} [Quiver V] [Quiver W] {F G : Prefunctor V W}
  证明: by
  obtain ⟨Fobj, Fmap⟩ := F
  obtain ⟨Gobj, Gmap⟩ := G
  obtain rfl : Fobj = Gobj := funext h_obj
  simp only [mk.injEq, heq_eq_eq, true_and]
  ext X Y f
  simpa only [Quiver.homOfEq_rfl] using h_map X Y f

Depends on / 依赖: Quiver, Quiver.homOfEq_rfl, h_map, h_obj, heq_eq_eq, homOfEq_rfl, mk.injEq, true_and
-/
theorem ext' {V W : Type u} [Quiver V] [Quiver W] {F G : Prefunctor V W}
    (h_obj : forall X, F.obj X = G.obj X)
    (h_map : forall (X Y : V) (f : X ⟶ Y),
      F.map f = Quiver.homOfEq (G.map f) (h_obj _).symm (h_obj _).symm) : F = G := by
  obtain ⟨Fobj, Fmap⟩ := F
  obtain ⟨Gobj, Gmap⟩ := G
  obtain rfl : Fobj = Gobj := funext h_obj
  simp only [mk.injEq, heq_eq_eq, true_and]
  ext X Y f
  simpa only [Quiver.homOfEq_rfl] using h_map X Y f

/-- The identity morphism between quivers. -/
@[simps]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: (V : Type*) [Quiver V]
  body: fun X => X
  map f := f

中文:
定义 id
  签名: (V : 类型) [Quiver V]
  定义体: fun X => X
  map f := f
-/
def id (V : Type*) [Quiver V] : Prefunctor V V where
  obj := fun X => X
  map f := f

instance (V : Type*) [Quiver V] : Inhabited (Prefunctor V V) :=
  ⟨id V⟩

/-- Composition of morphisms between quivers. -/
@[simps]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: {U : Type*} [Quiver U] {V : Type*} [Quiver V] {W : Type*} [Quiver W]
  body: G.obj (F.obj X)
  map f := G.map (F.map f)

@[simp]

中文:
定义 comp
  签名: {U : 类型} [Quiver U] {V : 类型} [Quiver V] {W : 类型} [Quiver W]
  定义体: G.obj (F.obj X)
  map f := G.map (F.map f)

@[simp]

Depends on / 依赖: F.obj, G.obj
-/
def comp {U : Type*} [Quiver U] {V : Type*} [Quiver V] {W : Type*} [Quiver W]
    (F : Prefunctor U V) (G : Prefunctor V W) : Prefunctor U W where
  obj X := G.obj (F.obj X)
  map f := G.map (F.map f)

@[simp]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: {U V : Type*} [Quiver U] [Quiver V] (F : Prefunctor U V)
  proof: rfl

@[simp]

中文:
定理 comp_id
  条件: {U V : 类型} [Quiver U] [Quiver V] (F : Prefunctor U V)
  证明: rfl

@[simp]
-/
theorem comp_id {U V : Type*} [Quiver U] [Quiver V] (F : Prefunctor U V) :
    F.comp (id _) = F := rfl

@[simp]
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  given: {U V : Type*} [Quiver U] [Quiver V] (F : Prefunctor U V)
  proof: rfl

@[simp]

中文:
定理 id_comp
  条件: {U V : 类型} [Quiver U] [Quiver V] (F : Prefunctor U V)
  证明: rfl

@[simp]
-/
theorem id_comp {U V : Type*} [Quiver U] [Quiver V] (F : Prefunctor U V) :
    (id _).comp F = F := rfl

@[simp]
/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  statement: {U V W Z : Type*} [Quiver U] [Quiver V] [Quiver W] [Quiver Z]
  proof: rfl

中文:
定理 comp_assoc
  结论: {U V W Z : 类型} [Quiver U] [Quiver V] [Quiver W] [Quiver Z]
  证明: rfl
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
/--
theorem `congr_map` / 定理 `congr_map`

English:
theorem congr_map
  statement: {U V : Type*} [Quiver U] [Quiver V] (F : U ⥤q V) {X Y : U} {f g : X ⟶ Y}
  proof: by
  rw [h]

中文:
定理 congr_map
  结论: {U V : 类型} [Quiver U] [Quiver V] (F : U ⥤q V) {X Y : U} {f g : X ⟶ Y}
  证明: by
  rw [h]
-/
theorem congr_map {U V : Type*} [Quiver U] [Quiver V] (F : U ⥤q V) {X Y : U} {f g : X ⟶ Y}
    (h : f = g) : F.map f = F.map g := by
  rw [h]

/--
theorem `congr_obj` / 定理 `congr_obj`

English:
theorem congr_obj
  given: {U V : Type*} [Quiver U] [Quiver V] {F G : U ⥤q V} (e : F = G) (X : U)
  proof: by cases e; rfl

中文:
定理 congr_obj
  条件: {U V : 类型} [Quiver U] [Quiver V] {F G : U ⥤q V} (e : F = G) (X : U)
  证明: by cases e; rfl
-/
theorem congr_obj {U V : Type*} [Quiver U] [Quiver V] {F G : U ⥤q V} (e : F = G) (X : U) :
    F.obj X = G.obj X := by cases e; rfl

/-- An equality of prefunctors gives an equality on homs. -/
@[to_dual self]
/--
theorem `congr_hom` / 定理 `congr_hom`

English:
theorem congr_hom
  statement: {U V : Type*} [Quiver U] [Quiver V] {F G : U ⥤q V} (e : F = G) {X Y : U}
  proof: by
  subst e
  simp

中文:
定理 congr_hom
  结论: {U V : 类型} [Quiver U] [Quiver V] {F G : U ⥤q V} (e : F = G) {X Y : U}
  证明: by
  subst e
  simp
-/
theorem congr_hom {U V : Type*} [Quiver U] [Quiver V] {F G : U ⥤q V} (e : F = G) {X Y : U}
    (f : X ⟶ Y) : Quiver.homOfEq (F.map f) (congr_obj e X) (congr_obj e Y) = G.map f := by
  subst e
  simp

/-- Prefunctors commute with `homOfEq`. -/
@[simp, to_dual self]
/--
theorem `homOfEq_map` / 定理 `homOfEq_map`

English:
theorem homOfEq_map
  statement: {U V : Type*} [Quiver U] [Quiver V] (F : U ⥤q V) {X Y : U} (f : X ⟶ Y)
  proof: by subst hX hY; simp

中文:
定理 homOfEq_map
  结论: {U V : 类型} [Quiver U] [Quiver V] (F : U ⥤q V) {X Y : U} (f : X ⟶ Y)
  证明: by subst hX hY; simp
-/
theorem homOfEq_map {U V : Type*} [Quiver U] [Quiver V] (F : U ⥤q V) {X Y : U} (f : X ⟶ Y)
    {X' Y' : U} (hX : X = X') (hY : Y = Y') :
    F.map (Quiver.homOfEq f hX hY) =
      Quiver.homOfEq (F.map f) (congr_arg F.obj hX) (congr_arg F.obj hY) := by subst hX hY; simp

end Prefunctor
