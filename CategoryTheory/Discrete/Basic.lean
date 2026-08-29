/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Kim Morrison, Floris van Doorn
-/
module

public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.Data.Set.Image

/-!
# Discrete categories

We define `Discrete α` as a structure containing a term `a : α` for any type `α`,
and use this type alias to provide a `SmallCategory` instance
whose only morphisms are the identities.

There is an annoying technical difficulty that it has turned out to be inconvenient
to allow categories with morphisms living in `Prop`,
so instead of defining `X ⟶ Y` in `Discrete α` as `X = Y`,
one might define it as `PLift (X = Y)`.
In fact, to allow `Discrete α` to be a `SmallCategory`
(i.e. with morphisms in the same universe as the objects),
we actually define the hom type `X ⟶ Y` as `ULift (PLift (X = Y))`.

`Discrete.functor` promotes a function `f : I → C` (for any category `C`) to a functor
`Discrete.functor f : Discrete I ⥤ C`.

Similarly, `Discrete.natTrans` and `Discrete.natIso` promote `I`-indexed families of morphisms,
or `I`-indexed families of isomorphisms to natural transformations or natural isomorphism.

We show equivalences of types are the same as (categorical) equivalences of the corresponding
discrete categories.
-/

@[expose] public section

namespace CategoryTheory

-- morphism levels before object levels. See note [category theory universes].
universe v₁ v₂ v₃ u₁ u₁' u₂ u₃

-- This is intentionally a structure rather than a type synonym
-- to enforce using `DiscreteEquiv` (or `Discrete.mk` and `Discrete.as`) to move between
-- `Discrete α` and `α`. Otherwise there is too much API leakage.
/-- A wrapper for promoting any type to a category,
with the only morphisms being equalities.
-/
@[ext, aesop safe cases (rule_sets := [CategoryTheory])]
/--
Definition of `Discrete` / `Discrete` 的定义

English:
structure Discrete
  parameters: (α : Type u₁)
  axioms and operations (1):
    - as : α

中文:
结构 离散
  参数: (α : 类型u₁)
  公理与运算 (1 个):
    - as : α
-/
structure Discrete (α : Type u₁) where
  /-- A wrapper for promoting any type to a category,
  with the only morphisms being equalities. -/
  as : α

@[simp]
/--
theorem `Discrete.mk_as` / 定理 `Discrete.mk_as`

English:
theorem Discrete.mk_as
  given: {α : Type u₁} (X : Discrete α)
  statement: Discrete.mk X.as = X
  proof: rfl

中文:
定理 离散.mk_as
  条件: {α : 类型u₁} (X : 离散 α)
  结论: 离散.mk X.as = X
  证明: rfl
-/
theorem Discrete.mk_as {α : Type u₁} (X : Discrete α) : Discrete.mk X.as = X :=
  rfl

/-- `Discrete α` is equivalent to the original type `α`. -/
@[simps]
/--
Definition of `discreteEquiv` / `discreteEquiv` 的定义

English:
definition discreteEquiv
  signature: {α : Type u₁}
  body: Discrete.as
  invFun := Discrete.mk
  left_inv := by cat_disch
  right_inv := by cat_disch

中文:
定义 discreteEquiv
  签名: {α : 类型u₁}
  定义体: Discrete.as
  invFun := Discrete.mk
  left_inv := by cat_disch
  right_inv := by cat_disch

Depends on / 依赖: Discrete, Discrete.as
-/
def discreteEquiv {α : Type u₁} : Discrete α ≃ α where
  toFun := Discrete.as
  invFun := Discrete.mk
  left_inv := by cat_disch
  right_inv := by cat_disch

/--
lemma `Discrete.as_bijective` / 引理 `Discrete.as_bijective`

English:
lemma Discrete.as_bijective
  given: {α : Type*}
  statement: (Discrete.as (α := α)).Bijective
  proof: discreteEquiv.bijective

中文:
引理 离散.as_bijective
  条件: {α : 类型}
  结论: (离散.as (α := α)).双射
  证明: discreteEquiv.bijective

Depends on / 依赖: Bijective
-/
lemma Discrete.as_bijective {α : Type*} : (Discrete.as (α := α)).Bijective :=
  discreteEquiv.bijective

instance {α : Type u₁} [DecidableEq α] : DecidableEq (Discrete α) :=
  discreteEquiv.decidableEq

/-- The "Discrete" category on a type, whose morphisms are equalities.

Because we do not allow morphisms in `Prop` (only in `Type`),
somewhat annoyingly we have to define `X ⟶ Y` as `ULift (PLift (X = Y))`. -/
@[stacks 001A]
/--
Instance `discreteCategory` / 实例 `discreteCategory`

English:
instance discreteCategory
  signature: (α : Type u₁)
  body: ULift (PLift (X.as = Y.as))
  id _ := ULift.up (PLift.up rfl)
  comp {X Y Z} g f := by
    cases X
    cases Y
    cases Z
    rcases f with ⟨⟨⟨⟩⟩⟩
    exact g

中文:
实例 discreteCategory
  签名: (α : 类型u₁)
  定义体: ULift (PLift (X.as = Y.as))
  id _ := ULift.up (PLift.up rfl)
  comp {X Y Z} g f := by
    cases X
    cases Y
    cases Z
    rcases f with ⟨⟨⟨⟩⟩⟩
    exact g

Depends on / 依赖: X.as, Y.as
-/
instance discreteCategory (α : Type u₁) : SmallCategory (Discrete α) where
  Hom X Y := ULift (PLift (X.as = Y.as))
  id _ := ULift.up (PLift.up rfl)
  comp {X Y Z} g f := by
    cases X
    cases Y
    cases Z
    rcases f with ⟨⟨⟨⟩⟩⟩
    exact g

namespace Discrete

variable {α : Type u₁}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: α] : Inhabited (Discrete α)
  body: ⟨⟨default⟩⟩

中文:
实例 [可居
  签名: α] : 可居 (离散 α)
  定义体: ⟨⟨default⟩⟩
-/
instance [Inhabited α] : Inhabited (Discrete α) :=
  ⟨⟨default⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Subsingleton
  signature: α] : Subsingleton (Discrete α)
  body: ⟨by cat_disch⟩

中文:
实例 [子单例
  签名: α] : 子单例 (离散 α)
  定义体: ⟨by cat_disch⟩

Depends on / 依赖: cat_disch
-/
instance [Subsingleton α] : Subsingleton (Discrete α) :=
  ⟨by cat_disch⟩

/--
Instance `instSubsingletonDiscreteHom` / 实例 `instSubsingletonDiscreteHom`

English:
instance instSubsingletonDiscreteHom
  signature: (X Y : Discrete α)
  body: show Subsingleton (ULift (PLift _)) from inferInstance

中文:
实例 instSubsingletonDiscreteHom
  签名: (X Y : 离散 α)
  定义体: show Subsingleton (ULift (PLift _)) from inferInstance

Depends on / 依赖: Subsingleton
-/
instance instSubsingletonDiscreteHom (X Y : Discrete α) : Subsingleton (X ⟶ Y) :=
  show Subsingleton (ULift (PLift _)) from inferInstance

/-- A simple tactic to run `cases` on any `Discrete α` hypotheses. -/
macro "discrete_cases" : tactic =>
  `(tactic| fail_if_no_progress casesm* Discrete _, (_ : Discrete _) ⟶ (_ : Discrete _), PLift _)

open Lean Elab Tactic in
/--
Use:
```
attribute [local aesop safe tactic (rule_sets := [CategoryTheory])]
  CategoryTheory.Discrete.discreteCases
```
to locally give `cat_disch` the ability to call `cases` on
`Discrete` and `(_ : Discrete _) ⟶ (_ : Discrete _)` hypotheses.
-/
meta def discreteCases : TacticM Unit := do
  evalTactic (← `(tactic| discrete_cases))

-- TODO: investigate turning on either
-- `attribute [aesop safe cases (rule_sets := [CategoryTheory])] Discrete`
-- or
-- `attribute [aesop safe tactic (rule_sets := [CategoryTheory])] discreteCases`
-- globally.

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Unique
  signature: α] : Unique (Discrete α)
  body: Unique.mk' (Discrete α)

中文:
实例 [唯一
  签名: α] : 唯一 (离散 α)
  定义体: Unique.mk' (Discrete α)

Depends on / 依赖: Discrete, Unique, Unique.mk
-/
instance [Unique α] : Unique (Discrete α) :=
  Unique.mk' (Discrete α)

/--
theorem `eq_of_hom` / 定理 `eq_of_hom`

English:
theorem eq_of_hom
  given: {X Y : Discrete α} (i : X ⟶ Y)
  statement: X.as = Y.as
  proof: i.down.down

中文:
定理 eq_of_hom
  条件: {X Y : 离散 α} (i : X ⟶ Y)
  结论: X.as = Y.as
  证明: i.down.down

Depends on / 依赖: i.down.down
-/
theorem eq_of_hom {X Y : Discrete α} (i : X ⟶ Y) : X.as = Y.as :=
  i.down.down

/--
Definition of `eqToHom` / `eqToHom` 的定义

English:
abbreviation eqToHom
  signature: {X Y : Discrete α} (h : X.as = Y.as)
  body: eqToHom (by cat_disch)

中文:
缩写 eqToHom
  签名: {X Y : 离散 α} (h : X.as = Y.as)
  定义体: eqToHom (by cat_disch)
-/
protected abbrev eqToHom {X Y : Discrete α} (h : X.as = Y.as) : X ⟶ Y :=
  eqToHom (by cat_disch)

/--
Definition of `eqToIso` / `eqToIso` 的定义

English:
abbreviation eqToIso
  signature: {X Y : Discrete α} (h : X.as = Y.as)
  body: eqToIso (by cat_disch)

中文:
缩写 eqToIso
  签名: {X Y : 离散 α} (h : X.as = Y.as)
  定义体: eqToIso (by cat_disch)
-/
protected abbrev eqToIso {X Y : Discrete α} (h : X.as = Y.as) : X ≅ Y :=
  eqToIso (by cat_disch)

/--
Definition of `eqToHom'` / `eqToHom'` 的定义

English:
abbreviation eqToHom'
  signature: {a b : α} (h : a = b)
  body: Discrete.eqToHom h

中文:
缩写 eqToHom'
  签名: {a b : α} (h : a = b)
  定义体: Discrete.eqToHom h

Depends on / 依赖: Discrete, Discrete.eqToHom, eqToHom
-/
abbrev eqToHom' {a b : α} (h : a = b) : Discrete.mk a ⟶ Discrete.mk b :=
  Discrete.eqToHom h

/--
Definition of `eqToIso'` / `eqToIso'` 的定义

English:
abbreviation eqToIso'
  signature: {a b : α} (h : a = b)
  body: Discrete.eqToIso h

@[simp]

中文:
缩写 eqToIso'
  签名: {a b : α} (h : a = b)
  定义体: Discrete.eqToIso h

@[simp]

Depends on / 依赖: Discrete, Discrete.eqToIso, eqToIso
-/
abbrev eqToIso' {a b : α} (h : a = b) : Discrete.mk a ≅ Discrete.mk b :=
  Discrete.eqToIso h

@[simp]
/--
theorem `id_def` / 定理 `id_def`

English:
theorem id_def
  given: (X : Discrete α)
  statement: ULift.up (PLift.up (Eq.refl X.as)) = 𝟙 X
  proof: rfl

@[simp]

中文:
定理 id_def
  条件: (X : 离散 α)
  结论: 类型层提升.up (命题层提升.up (相等.refl X.as)) = 𝟙 X
  证明: rfl

@[simp]
-/
theorem id_def (X : Discrete α) : ULift.up (PLift.up (Eq.refl X.as)) = 𝟙 X :=
  rfl

@[simp]
/--
theorem `id_def'` / 定理 `id_def'`

English:
theorem id_def'
  given: (X : α)
  statement: ULift.up (PLift.up (Eq.refl X)) = 𝟙 (⟨X⟩ : Discrete α)
  proof: rfl

中文:
定理 id_def'
  条件: (X : α)
  结论: 类型层提升.up (命题层提升.up (相等.refl X)) = 𝟙 (⟨X⟩ : 离散 α)
  证明: rfl
-/
theorem id_def' (X : α) : ULift.up (PLift.up (Eq.refl X)) = 𝟙 (⟨X⟩ : Discrete α) :=
  rfl

variable {C : Type u₂} [Category.{v₂} C]

instance {I : Type u₁} {i j : Discrete I} (f : i ⟶ j) : IsIso f :=
  ⟨⟨Discrete.eqToHom (eq_of_hom f).symm, by cat_disch⟩⟩

attribute [local aesop safe tactic (rule_sets := [CategoryTheory])]
  CategoryTheory.Discrete.discreteCases

/-- Any function `I → C` gives a functor `Discrete I ⥤ C`. -/
@[implicit_reducible]
/--
Definition of `functor` / `functor` 的定义

English:
definition functor
  signature: {I : Type u₁} (F : I -> C)
  body: F ∘ Discrete.as
  map {X Y} f := by
    dsimp
    rcases f with ⟨⟨h⟩⟩
    exact eqToHom (congrArg _ h)

@[simp]

中文:
定义 functor
  签名: {I : 类型u₁} (F : I -> C)
  定义体: F ∘ Discrete.as
  map {X Y} f := by
    dsimp
    rcases f with ⟨⟨h⟩⟩
    exact eqToHom (congrArg _ h)

@[simp]

Depends on / 依赖: Discrete, Discrete.as
-/
def functor {I : Type u₁} (F : I -> C) : Discrete I ⥤ C where
  obj := F ∘ Discrete.as
  map {X Y} f := by
    dsimp
    rcases f with ⟨⟨h⟩⟩
    exact eqToHom (congrArg _ h)

@[simp]
/--
theorem `functor_obj` / 定理 `functor_obj`

English:
theorem functor_obj
  given: {I : Type u₁} (F : I -> C) (i : I)
  proof: rfl

中文:
定理 functor_obj
  条件: {I : 类型u₁} (F : I -> C) (i : I)
  证明: rfl
-/
theorem functor_obj {I : Type u₁} (F : I -> C) (i : I) :
    (Discrete.functor F).obj (Discrete.mk i) = F i :=
  rfl

/--
theorem `functor_map` / 定理 `functor_map`

English:
theorem functor_map
  given: {I : Type u₁} (F : I -> C) {i : Discrete I} (f : i ⟶ i)
  proof: by cat_disch

@[simp]

中文:
定理 functor_map
  条件: {I : 类型u₁} (F : I -> C) {i : 离散 I} (f : i ⟶ i)
  证明: by cat_disch

@[simp]

Depends on / 依赖: cat_disch
-/
theorem functor_map {I : Type u₁} (F : I -> C) {i : Discrete I} (f : i ⟶ i) :
    (Discrete.functor F).map f = 𝟙 (F i.as) := by cat_disch

@[simp]
/--
theorem `functor_obj_eq_as` / 定理 `functor_obj_eq_as`

English:
theorem functor_obj_eq_as
  given: {I : Type u₁} (F : I -> C) (X : Discrete I)
  proof: rfl

@[simp]

中文:
定理 functor_obj_eq_as
  条件: {I : 类型u₁} (F : I -> C) (X : 离散 I)
  证明: rfl

@[simp]
-/
theorem functor_obj_eq_as {I : Type u₁} (F : I -> C) (X : Discrete I) :
    (Discrete.functor F).obj X = F X.as :=
  rfl

@[simp]
/--
lemma `range_functor` / 引理 `range_functor`

English:
lemma range_functor
  given: {I : Type*} (X : I -> C)
  statement: Set.range (Discrete.functor X).obj = Set.range X
  proof: by
  simp [Discrete.functor, Set.range_comp, Discrete.as_bijective.surjective.range_eq]

@[ext]

中文:
引理 range_functor
  条件: {I : 类型} (X : I -> C)
  结论: 集合.range (离散.functor X).obj = 集合.range X
  证明: by
  simp [Discrete.functor, Set.range_comp, Discrete.as_bijective.surjective.range_eq]

@[ext]

Depends on / 依赖: Discrete, Discrete.as_bijective.surjective.range_eq, Discrete.functor, Set.range_comp, as_bijective, functor, range_comp, range_eq, surjective
-/
lemma range_functor {I : Type*} (X : I -> C) : Set.range (Discrete.functor X).obj = Set.range X := by
  simp [Discrete.functor, Set.range_comp, Discrete.as_bijective.surjective.range_eq]

@[ext]
/--
lemma `functor_ext` / 引理 `functor_ext`

English:
lemma functor_ext
  given: {I : Type u₁} {G F : Discrete I ⥤ C} (h : (i : I) -> G.obj ⟨i⟩ = F.obj ⟨i⟩)
  proof: by
  fapply Functor.ext
  · intro I; rw [h]
  · intro ⟨X⟩ ⟨Y⟩ ⟨⟨p⟩⟩; simp only at p; induction p; simp

中文:
引理 functor_ext
  条件: {I : 类型u₁} {G F : 离散 I ⥤ C} (h : (i : I) -> G.obj ⟨i⟩ = F.obj ⟨i⟩)
  证明: by
  fapply Functor.ext
  · intro I; rw [h]
  · intro ⟨X⟩ ⟨Y⟩ ⟨⟨p⟩⟩; simp only at p; induction p; simp

Depends on / 依赖: Functor, Functor.ext, fapply
-/
lemma functor_ext {I : Type u₁} {G F : Discrete I ⥤ C} (h : (i : I) -> G.obj ⟨i⟩ = F.obj ⟨i⟩) :
    G = F := by
  fapply Functor.ext
  · intro I; rw [h]
  · intro ⟨X⟩ ⟨Y⟩ ⟨⟨p⟩⟩; simp only at p; induction p; simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The discrete functor induced by a composition of maps can be written as a
composition of two discrete functors.
-/
@[simps!]
/--
Definition of `functorComp` / `functorComp` 的定义

English:
definition functorComp
  signature: {I : Type u₁} {J : Type u₁'} (f : J -> C) (g : I -> J)
  body: NatIso.ofComponents fun _ => Iso.refl _

中文:
定义 functorComp
  签名: {I : 类型u₁} {J : 类型u₁'} (f : J -> C) (g : I -> J)
  定义体: NatIso.ofComponents fun _ => Iso.refl _

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def functorComp {I : Type u₁} {J : Type u₁'} (f : J -> C) (g : I -> J) :
    Discrete.functor (f ∘ g) ≅ Discrete.functor (Discrete.mk ∘ g) ⋙ Discrete.functor f :=
  NatIso.ofComponents fun _ => Iso.refl _

/-- For functors out of a discrete category,
a natural transformation is just a collection of maps,
as the naturality squares are trivial.
-/
@[simps, implicit_reducible]
/--
Definition of `natTrans` / `natTrans` 的定义

English:
definition natTrans
  signature: {I : Type u₁} {F G : Discrete I ⥤ C} (f : forall i : Discrete I, F.obj i ⟶ G.obj i)
  body: f
  naturality := fun {X Y} ⟨⟨g⟩⟩ => by
    discrete_cases
    rcases g
    change F.map (𝟙 _) ≫ _ = _ ≫ G.map (𝟙 _)
    simp

中文:
定义 natTrans
  签名: {I : 类型u₁} {F G : 离散 I ⥤ C} (f : 对任意 i : 离散 I, F.obj i ⟶ G.obj i)
  定义体: f
  naturality := fun {X Y} ⟨⟨g⟩⟩ => by
    discrete_cases
    rcases g
    change F.map (𝟙 _) ≫ _ = _ ≫ G.map (𝟙 _)
    simp
-/
def natTrans {I : Type u₁} {F G : Discrete I ⥤ C} (f : forall i : Discrete I, F.obj i ⟶ G.obj i) :
    F ⟶ G where
  app := f
  naturality := fun {X Y} ⟨⟨g⟩⟩ => by
    discrete_cases
    rcases g
    change F.map (𝟙 _) ≫ _ = _ ≫ G.map (𝟙 _)
    simp

/-- For functors out of a discrete category,
a natural isomorphism is just a collection of isomorphisms,
as the naturality squares are trivial.
-/
@[simps!]
/--
Definition of `natIso` / `natIso` 的定义

English:
definition natIso
  signature: {I : Type u₁} {F G : Discrete I ⥤ C} (f : forall i : Discrete I, F.obj i ≅ G.obj i)
  body: NatIso.ofComponents f fun ⟨⟨g⟩⟩ => by
    discrete_cases
    rcases g
    change F.map (𝟙 _) ≫ _ = _ ≫ G.map (𝟙 _)
    simp

中文:
定义 natIso
  签名: {I : 类型u₁} {F G : 离散 I ⥤ C} (f : 对任意 i : 离散 I, F.obj i ≅ G.obj i)
  定义体: NatIso.ofComponents f fun ⟨⟨g⟩⟩ => by
    discrete_cases
    rcases g
    change F.map (𝟙 _) ≫ _ = _ ≫ G.map (𝟙 _)
    simp

Depends on / 依赖: F.map, G.map, NatIso, NatIso.ofComponents, discrete_cases, ofComponents
-/
def natIso {I : Type u₁} {F G : Discrete I ⥤ C} (f : forall i : Discrete I, F.obj i ≅ G.obj i) :
    F ≅ G :=
  NatIso.ofComponents f fun ⟨⟨g⟩⟩ => by
    discrete_cases
    rcases g
    change F.map (𝟙 _) ≫ _ = _ ≫ G.map (𝟙 _)
    simp

instance {I : Type*} {F G : Discrete I ⥤ C} (f : forall i, F.obj i ⟶ G.obj i) [forall i, IsIso (f i)] :
    IsIso (Discrete.natTrans f) := by
  change IsIso (Discrete.natIso (fun i => asIso (f i))).hom
  infer_instance

@[simp]
/--
theorem `natIso_app` / 定理 `natIso_app`

English:
theorem natIso_app
  statement: {I : Type u₁} {F G : Discrete I ⥤ C} (f : forall i : Discrete I, F.obj i ≅ G.obj i)
  proof: by cat_disch

中文:
定理 natIso_app
  结论: {I : 类型u₁} {F G : 离散 I ⥤ C} (f : 对任意 i : 离散 I, F.obj i ≅ G.obj i)
  证明: by cat_disch

Depends on / 依赖: cat_disch
-/
theorem natIso_app {I : Type u₁} {F G : Discrete I ⥤ C} (f : forall i : Discrete I, F.obj i ≅ G.obj i)
    (i : Discrete I) : (Discrete.natIso f).app i = f i := by cat_disch

/-- Every functor `F` from a discrete category is naturally isomorphic (actually, equal) to
  `Discrete.functor (F.obj)`. -/
@[simps!]
/--
Definition of `natIsoFunctor` / `natIsoFunctor` 的定义

English:
definition natIsoFunctor
  signature: {I : Type u₁} {F : Discrete I ⥤ C}
  body: natIso fun _ => Iso.refl _

中文:
定义 natIsoFunctor
  签名: {I : 类型u₁} {F : 离散 I ⥤ C}
  定义体: natIso fun _ => Iso.refl _

Depends on / 依赖: Iso.refl, natIso
-/
def natIsoFunctor {I : Type u₁} {F : Discrete I ⥤ C} : F ≅ Discrete.functor (F.obj ∘ Discrete.mk) :=
  natIso fun _ => Iso.refl _

/-- Composing `Discrete.functor F` with another functor `G` amounts to composing `F` with `G.obj` -/
@[simps!]
/--
Definition of `compNatIsoDiscrete` / `compNatIsoDiscrete` 的定义

English:
definition compNatIsoDiscrete
  signature: {I : Type u₁} {D : Type u₃} [Category.{v₃} D] (F : I -> C) (G : C ⥤ D)
  body: natIso fun _ => Iso.refl _

中文:
定义 comp自然数IsoDiscrete
  签名: {I : 类型u₁} {D : 类型u₃} [范畴.{v₃} D] (F : I -> C) (G : C ⥤ D)
  定义体: natIso fun _ => Iso.refl _

Depends on / 依赖: Iso.refl, natIso
-/
def compNatIsoDiscrete {I : Type u₁} {D : Type u₃} [Category.{v₃} D] (F : I -> C) (G : C ⥤ D) :
    Discrete.functor F ⋙ G ≅ Discrete.functor (G.obj ∘ F) :=
  natIso fun _ => Iso.refl _

/-- We can promote a type-level `Equiv` to
an equivalence between the corresponding `discrete` categories.
-/
@[simps]
/--
Definition of `equivalence` / `equivalence` 的定义

English:
definition equivalence
  signature: {I : Type u₁} {J : Type u₂} (e : I ≃ J)
  body: Discrete.functor (Discrete.mk ∘ (e : I -> J))
  inverse := Discrete.functor (Discrete.mk ∘ (e.symm : J -> I))
  unitIso :=
    Discrete.natIso fun i => eqToIso (by simp)
  counitIso :=
    Discrete.natIso fun j => eqToIso (by simp)

中文:
定义 equivalence
  签名: {I : 类型u₁} {J : 类型u₂} (e : I ≃ J)
  定义体: Discrete.functor (Discrete.mk ∘ (e : I -> J))
  inverse := Discrete.functor (Discrete.mk ∘ (e.symm : J -> I))
  unitIso :=
    Discrete.natIso fun i => eqToIso (by simp)
  counitIso :=
    Discrete.natIso fun j => eqToIso (by simp)

Depends on / 依赖: Discrete, Discrete.functor, Discrete.mk, functor
-/
def equivalence {I : Type u₁} {J : Type u₂} (e : I ≃ J) : Discrete I ≌ Discrete J where
  functor := Discrete.functor (Discrete.mk ∘ (e : I -> J))
  inverse := Discrete.functor (Discrete.mk ∘ (e.symm : J -> I))
  unitIso :=
    Discrete.natIso fun i => eqToIso (by simp)
  counitIso :=
    Discrete.natIso fun j => eqToIso (by simp)

/-- We can convert an equivalence of `discrete` categories to a type-level `Equiv`. -/
@[simps]
/--
Definition of `equivOfEquivalence` / `equivOfEquivalence` 的定义

English:
definition equivOfEquivalence
  signature: {α : Type u₁} {β : Type u₂} (h : Discrete α ≌ Discrete β)
  body: Discrete.as ∘ h.functor.obj ∘ Discrete.mk
  invFun := Discrete.as ∘ h.inverse.obj ∘ Discrete.mk
  left_inv a := by simpa using eq_of_hom (h.unitIso.app (Discrete.mk a)).2
  right_inv a := by simpa using eq_of_hom (h.counitIso.app (Discrete.mk a)).1

中文:
定义 equivOfEquivalence
  签名: {α : 类型u₁} {β : 类型u₂} (h : 离散 α ≌ 离散 β)
  定义体: Discrete.as ∘ h.functor.obj ∘ Discrete.mk
  invFun := Discrete.as ∘ h.inverse.obj ∘ Discrete.mk
  left_inv a := by simpa using eq_of_hom (h.unitIso.app (Discrete.mk a)).2
  right_inv a := by simpa using eq_of_hom (h.counitIso.app (Discrete.mk a)).1

Depends on / 依赖: Discrete, Discrete.as, Discrete.mk, functor, h.functor.obj
-/
def equivOfEquivalence {α : Type u₁} {β : Type u₂} (h : Discrete α ≌ Discrete β) : α ≃ β where
  toFun := Discrete.as ∘ h.functor.obj ∘ Discrete.mk
  invFun := Discrete.as ∘ h.inverse.obj ∘ Discrete.mk
  left_inv a := by simpa using eq_of_hom (h.unitIso.app (Discrete.mk a)).2
  right_inv a := by simpa using eq_of_hom (h.counitIso.app (Discrete.mk a)).1

end Discrete

namespace Discrete

variable {J : Type v₁}

open Opposite

/-- A discrete category is equivalent to its opposite category. -/
@[simps! functor_obj_as inverse_obj]
/--
Definition of `opposite` / `opposite` 的定义

English:
definition opposite
  signature: (α : Type u₁)
  body: let F : Discrete α ⥤ (Discrete α)ᵒᵖ := Discrete.functor fun x => op (Discrete.mk x)
  { functor := F.leftOp
    inverse := F
    unitIso := NatIso.ofComponents fun ⟨_⟩ => Iso.refl _
    counitIso := Discrete.natIso fun ⟨_⟩ => Iso.refl _ }

中文:
定义 opposite
  签名: (α : 类型u₁)
  定义体: let F : Discrete α ⥤ (Discrete α)ᵒᵖ := Discrete.functor fun x => op (Discrete.mk x)
  { functor := F.leftOp
    inverse := F
    unitIso := NatIso.ofComponents fun ⟨_⟩ => Iso.refl _
    counitIso := Discrete.natIso fun ⟨_⟩ => Iso.refl _ }
-/
protected def opposite (α : Type u₁) : (Discrete α)ᵒᵖ ≌ Discrete α :=
  let F : Discrete α ⥤ (Discrete α)ᵒᵖ := Discrete.functor fun x => op (Discrete.mk x)
  { functor := F.leftOp
    inverse := F
    unitIso := NatIso.ofComponents fun ⟨_⟩ => Iso.refl _
    counitIso := Discrete.natIso fun ⟨_⟩ => Iso.refl _ }

variable {C : Type u₂} [Category.{v₂} C]

@[simp]
/--
theorem `functor_map_id` / 定理 `functor_map_id`

English:
theorem functor_map_id
  given: (F : Discrete J ⥤ C) {j : Discrete J} (f : j ⟶ j)
  proof: by
  have h : f = 𝟙 j := by cat_disch
  rw [h]
  simp

中文:
定理 functor_map_id
  条件: (F : 离散 J ⥤ C) {j : 离散 J} (f : j ⟶ j)
  证明: by
  have h : f = 𝟙 j := by cat_disch
  rw [h]
  simp

Depends on / 依赖: cat_disch
-/
theorem functor_map_id (F : Discrete J ⥤ C) {j : Discrete J} (f : j ⟶ j) :
    F.map f = 𝟙 (F.obj j) := by
  have h : f = 𝟙 j := by cat_disch
  rw [h]
  simp

end Discrete

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `Discrete.forall` / 引理 `Discrete.forall`

English:
lemma Discrete.forall
  given: {α : Type*} {p : Discrete α -> Prop}
  proof: by
  rw [iff_iff_eq]; rw [discreteEquiv.forall_congr_left]
  simp only [discreteEquiv, Equiv.symm_mk, Equiv.coe_fn_mk]

中文:
引理 离散.对任意
  条件: {α : 类型} {p : 离散 α -> 命题}
  证明: by
  rw [iff_iff_eq]; rw [discreteEquiv.forall_congr_left]
  simp only [discreteEquiv, Equiv.symm_mk, Equiv.coe_fn_mk]

Depends on / 依赖: Equiv.coe_fn_mk, Equiv.symm_mk, coe_fn_mk, discreteEquiv, discreteEquiv.forall_congr_left, forall_congr_left, iff_iff_eq, symm_mk
-/
lemma Discrete.forall {α : Type*} {p : Discrete α -> Prop} :
    (forall (a : Discrete α), p a) ↔ forall (a' : α), p ⟨a'⟩ := by
  rw [iff_iff_eq]; rw [discreteEquiv.forall_congr_left]
  simp only [discreteEquiv, Equiv.symm_mk, Equiv.coe_fn_mk]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `Discrete.exists` / 引理 `Discrete.exists`

English:
lemma Discrete.exists
  given: {α : Type*} {p : Discrete α -> Prop}
  proof: by
  rw [iff_iff_eq]; rw [discreteEquiv.exists_congr_left]
  simp [discreteEquiv]

中文:
引理 离散.存在
  条件: {α : 类型} {p : 离散 α -> 命题}
  证明: by
  rw [iff_iff_eq]; rw [discreteEquiv.exists_congr_left]
  simp [discreteEquiv]

Depends on / 依赖: discreteEquiv, discreteEquiv.exists_congr_left, exists_congr_left, iff_iff_eq
-/
lemma Discrete.exists {α : Type*} {p : Discrete α -> Prop} :
    (exists (a : Discrete α), p a) ↔ exists (a' : α), p ⟨a'⟩ := by
  rw [iff_iff_eq]; rw [discreteEquiv.exists_congr_left]
  simp [discreteEquiv]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The equivalence of categories `(J → C) ≌ (Discrete J ⥤ C)`. -/
@[simps]
/--
Definition of `piEquivalenceFunctorDiscrete` / `piEquivalenceFunctorDiscrete` 的定义

English:
definition piEquivalenceFunctorDiscrete
  signature: (J : Type u₂) (C : Type u₁) [Category.{v₁} C]
  body: { obj := fun F => Discrete.functor F
      map := fun f => Discrete.natTrans (fun j => f j.as) }
  inverse :=
    { obj := fun F j => F.obj ⟨j⟩
      map := fun f j => f.app ⟨j⟩ }
  unitIso := Iso.refl _
  counitIso := NatIso.ofComponents (fun F => (NatIso.ofComponents (fun _ => Iso.refl _)
    (by


中文:
定义 piEquivalenceFunctorDiscrete
  签名: (J : 类型u₂) (C : 类型u₁) [范畴.{v₁} C]
  定义体: { obj := fun F => Discrete.functor F
      map := fun f => Discrete.natTrans (fun j => f j.as) }
  inverse :=
    { obj := fun F j => F.obj ⟨j⟩
      map := fun f j => f.app ⟨j⟩ }
  unitIso := Iso.refl _
  counitIso := NatIso.ofComponents (fun F => (NatIso.ofComponents (fun _ => Iso.refl _)
    (by


Depends on / 依赖: Discrete, Discrete.eq_of_hom, Discrete.functor, Discrete.natTrans, F.obj, Iso.refl, NatIso, NatIso.ofComponents, cat_disch, counitIso, eq_of_hom, f.app, functor, inverse, j.as, natTrans, ofComponents, unitIso
-/
def piEquivalenceFunctorDiscrete (J : Type u₂) (C : Type u₁) [Category.{v₁} C] :
    (J -> C) ≌ (Discrete J ⥤ C) where
  functor :=
    { obj := fun F => Discrete.functor F
      map := fun f => Discrete.natTrans (fun j => f j.as) }
  inverse :=
    { obj := fun F j => F.obj ⟨j⟩
      map := fun f j => f.app ⟨j⟩ }
  unitIso := Iso.refl _
  counitIso := NatIso.ofComponents (fun F => (NatIso.ofComponents (fun _ => Iso.refl _)
    (by
      rintro ⟨x⟩ ⟨y⟩ f
      obtain rfl : x = y := Discrete.eq_of_hom f
      obtain rfl : f = 𝟙 _ := rfl
      simp))) (by cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- `piEquivalenceFunctorDiscrete` is compatible with `evaluation`. -/
@[simps!]
/--
Definition of `piEquivalenceFunctorDiscreteCompEvaluationIso` / `piEquivalenceFunctorDiscreteCompEvaluationIso` 的定义

English:
definition piEquivalenceFunctorDiscreteCompEvaluationIso
  signature: (C : Type*) [Category* C] {J : Type*} (j : J)
  body: NatIso.ofComponents fun _ => Iso.refl _

中文:
定义 piEquivalenceFunctorDiscreteCompEvaluationIso
  签名: (C : 类型) [范畴* C] {J : 类型} (j : J)
  定义体: NatIso.ofComponents fun _ => Iso.refl _

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def piEquivalenceFunctorDiscreteCompEvaluationIso (C : Type*) [Category* C] {J : Type*} (j : J) :
    (piEquivalenceFunctorDiscrete J C).functor ⋙ (evaluation _ _).obj ⟨j⟩ ≅ Pi.eval _ j :=
  NatIso.ofComponents fun _ => Iso.refl _

/--
Definition of `IsDiscrete` / `IsDiscrete` 的定义

English:
class IsDiscrete
  parameters: (C : Type*) [Category* C]
  axioms and operations (2):
    - subsingleton((X Y : C)) : Subsingleton (X ⟶ Y)  [default: by infer_instance]
    - eq_of_hom({X Y : C} (f : X ⟶ Y)) : X = Y

中文:
类 是离散
  参数: (C : 类型) [范畴* C]
  公理与运算 (2 个):
    - subsingleton((X Y : C)) : 子单例 (X ⟶ Y)  [默认: by infer_instance]
    - eq_of_hom({X Y : C} (f : X ⟶ Y)) : X = Y

Depends on / 依赖: eq_of_hom, infer_instance
-/
class IsDiscrete (C : Type*) [Category* C] : Prop where
  subsingleton (X Y : C) : Subsingleton (X ⟶ Y) := by infer_instance
  eq_of_hom {X Y : C} (f : X ⟶ Y) : X = Y

attribute [instance] IsDiscrete.subsingleton

/--
Instance `Discrete.isDiscrete` / 实例 `Discrete.isDiscrete`

English:
instance Discrete.isDiscrete
  signature: (C : Type*)
  body: by rintro ⟨_⟩ ⟨_⟩ ⟨⟨rfl⟩⟩; rfl

中文:
实例 离散.isDiscrete
  签名: (C : 类型)
  定义体: by rintro ⟨_⟩ ⟨_⟩ ⟨⟨rfl⟩⟩; rfl
-/
instance Discrete.isDiscrete (C : Type*) : IsDiscrete (Discrete C) where
  eq_of_hom := by rintro ⟨_⟩ ⟨_⟩ ⟨⟨rfl⟩⟩; rfl

section

variable {C : Type*} [Category* C] [IsDiscrete C]

/--
lemma `obj_ext_of_isDiscrete` / 引理 `obj_ext_of_isDiscrete`

English:
lemma obj_ext_of_isDiscrete
  given: {X Y : C} (f : X ⟶ Y)
  statement: X = Y
  proof: IsDiscrete.eq_of_hom f

中文:
引理 obj_ext_of_isDiscrete
  条件: {X Y : C} (f : X ⟶ Y)
  结论: X = Y
  证明: IsDiscrete.eq_of_hom f

Depends on / 依赖: IsDiscrete, IsDiscrete.eq_of_hom, eq_of_hom
-/
lemma obj_ext_of_isDiscrete {X Y : C} (f : X ⟶ Y) : X = Y := IsDiscrete.eq_of_hom f

/--
Instance `isIso_of_isDiscrete` / 实例 `isIso_of_isDiscrete`

English:
instance isIso_of_isDiscrete
  signature: {X Y : C} (f : X ⟶ Y)
  body: ⟨eqToHom (IsDiscrete.eq_of_hom f).symm, by cat_disch⟩

中文:
实例 isIso_of_isDiscrete
  签名: {X Y : C} (f : X ⟶ Y)
  定义体: ⟨eqToHom (IsDiscrete.eq_of_hom f).symm, by cat_disch⟩

Depends on / 依赖: F.obj, Functor, Functor.const_obj_obj, IsCofilteredOrEmpty, IsCofilteredOrEmpty.cone_objs, IsDiscrete, IsDiscrete.eq_of_hom, Nonempty, Nonempty.some, Over.homMk, Over.mk, Over.mk_hom, Over.mk_left, cat_disch, cone_objs, const_obj_obj, eqToHom, eq_of_hom, hc.fac, hc.lift
-/
instance isIso_of_isDiscrete {X Y : C} (f : X ⟶ Y) : IsIso f :=
  ⟨eqToHom (IsDiscrete.eq_of_hom f).symm, by cat_disch⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsDiscrete Cᵒᵖ
  body: by
    rintro ⟨_⟩ ⟨_⟩ ⟨f⟩
    obtain rfl := obj_ext_of_isDiscrete f
    rfl

中文:
实例 :
  签名: 是离散 Cᵒᵖ
  定义体: by
    rintro ⟨_⟩ ⟨_⟩ ⟨f⟩
    obtain rfl := obj_ext_of_isDiscrete f
    rfl

Depends on / 依赖: Cocone, F.obj, Functor, Functor.const_obj_obj, IsFilteredOrEmpty, IsFilteredOrEmpty.cocone_objs, Nonempty, Nonempty.some, Under.homMk, Under.mk, Under.mk_hom, Under.mk_right, cocone_objs, const_obj_obj, hc.desc, hc.fac, mk_hom, mk_right, obj_ext_of_isDiscrete, ofExistsUnique
-/
instance : IsDiscrete Cᵒᵖ where
  eq_of_hom := by
    rintro ⟨_⟩ ⟨_⟩ ⟨f⟩
    obtain rfl := obj_ext_of_isDiscrete f
    rfl

end

end CategoryTheory
