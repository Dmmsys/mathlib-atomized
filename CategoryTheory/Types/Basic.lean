/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Kim Morrison, Johannes Hölzl, Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Elementwise
public import Mathlib.CategoryTheory.EpiMono
public import Mathlib.Tactic.PPWithUniv
public import Mathlib.Tactic.ToAdditive

/-!
# The category `Type`.

In this section we define a `LargeCategory` structure on `Type u`, in such a way that it becomes a
`ConcreteCategory`.

## Implementation

We define the one-field structure `TypeCat.Fun` to wrap a function between types, and a `FunLike`
instance on it. Then we define a one-field structure `TypeCat.Hom` which wraps a `Fun`. The
morphisms in the category `Type u` are defined to be `TypeCat.Hom`, and the `FC` parameter of
the `ConcreteCategory` instance is `TypeCat.Fun`. `TypeCat.Fun` serves as a layer of separation
between the `FC` parameter of the `ConcreteCategory` instance and bare functions, to avoid defining
a `FunLike` instance on the latter (which would give two non-reducibly defeq coercions from
morphisms in `Type` to functions), and the outer nesting `TypeCat.Hom` gives a layer of separation
between morphisms and `FC`, as is done for all concrete categories in mathlib.

To promote a function to a morphism in this category, we provide the abbreviation `↾f`,
as well as a corresponding notation `↾f`. (Entered as `\upr `.)

## Main definitions

We define `uliftFunctor`, from `Type u` to `Type (max u v)`, and show that it is fully faithful
(but not, of course, essentially surjective).

We prove some basic facts about the category `Type`:
* epimorphisms are surjections and monomorphisms are injections,
* `Iso` is both `Iso` and `Equiv` to `Equiv` (at least within a fixed universe),
* every type level `IsLawfulFunctor` gives a categorical functor `Type ⥤ Type`
  (the corresponding fact about monads is in `Mathlib/CategoryTheory/Monad/Types.lean`).
-/

@[expose] public section

-- morphism levels before object levels. See note [category theory universes].
universe v w u u'

namespace TypeCat

/-- A one-field structure wrapping a function between types. -/
@[ext]
/--
Definition of `Fun` / `Fun` 的定义

English:
structure Fun
  parameters: (X Y : Type*)
  axioms and operations (1):
    - toFun : X -> Y

中文:
结构 Fun
  参数: (X Y : 类型)
  公理与运算 (1 个):
    - toFun : X -> Y
-/
structure Fun (X Y : Type*) where
  /-- The underlying function. -/
  toFun : X -> Y

/--
Instance `instFunLikeFun` / 实例 `instFunLikeFun`

English:
instance instFunLikeFun
  signature: {X Y : Type*}
  body: f.toFun x
  coe_injective _ := by aesop

initialize_simps_projections Fun (toFun -> apply)

中文:
实例 instFunLikeFun
  签名: {X Y : 类型}
  定义体: f.toFun x
  coe_injective _ := by aesop

initialize_simps_projections Fun (toFun -> apply)

Depends on / 依赖: f.toFun
-/
instance instFunLikeFun {X Y : Type*} : FunLike (Fun X Y) X Y where
  coe f x := f.toFun x
  coe_injective _ := by aesop

initialize_simps_projections Fun (toFun -> apply)

/--
lemma `Fun.mk_apply` / 引理 `Fun.mk_apply`

English:
lemma Fun.mk_apply
  given: {X Y : Type*} (f : X -> Y) (x : X)
  statement: (Fun.mk f) x = f x
  proof: rfl

@[simp]

中文:
引理 Fun.mk_apply
  条件: {X Y : 类型} (f : X -> Y) (x : X)
  结论: (Fun.mk f) x = f x
  证明: rfl

@[simp]
-/
lemma Fun.mk_apply {X Y : Type*} (f : X -> Y) (x : X) : (Fun.mk f) x = f x :=
  rfl

@[simp]
/--
lemma `Fun.coe_mk` / 引理 `Fun.coe_mk`

English:
lemma Fun.coe_mk
  given: {X Y : Type*} (f : X -> Y)
  statement: (Fun.mk f : X -> Y) = f
  proof: rfl

中文:
引理 Fun.coe_mk
  条件: {X Y : 类型} (f : X -> Y)
  结论: (Fun.mk f : X -> Y) = f
  证明: rfl
-/
lemma Fun.coe_mk {X Y : Type*} (f : X -> Y) : (Fun.mk f : X -> Y) = f :=
  rfl

/-- The identity function as a `Fun`. -/
@[simps! +dsimpLhs]
/--
Definition of `Fun.id` / `Fun.id` 的定义

English:
definition Fun.id
  signature: (X : Type*)
  body: Fun.mk _root_.id

中文:
定义 Fun.id
  签名: (X : 类型)
  定义体: Fun.mk _root_.id

Depends on / 依赖: Fun.mk, _root_, _root_.id
-/
def Fun.id (X : Type*) : Fun X X := Fun.mk _root_.id

/-- Composition of `Fun`s. -/
@[simps! +dsimpLhs]
/--
Definition of `Fun.comp` / `Fun.comp` 的定义

English:
definition Fun.comp
  signature: {X Y Z : Type*} (f : Fun Y Z) (g : Fun X Y)
  body: mk (f.toFun ∘ g.toFun)

中文:
定义 Fun.comp
  签名: {X Y Z : 类型} (f : Fun Y Z) (g : Fun X Y)
  定义体: mk (f.toFun ∘ g.toFun)

Depends on / 依赖: f.toFun, g.toFun
-/
def Fun.comp {X Y Z : Type*} (f : Fun Y Z) (g : Fun X Y) : Fun X Z := mk (f.toFun ∘ g.toFun)

/--
Definition of `Fun.homEquiv` / `Fun.homEquiv` 的定义

English:
definition Fun.homEquiv
  signature: (X Y : Type u)
  body: f
  invFun f := ⟨f⟩
  left_inv := by intro; rfl
  right_inv := by intro; rfl

中文:
定义 Fun.homEquiv
  签名: (X Y : 类型u)
  定义体: f
  invFun f := ⟨f⟩
  left_inv := by intro; rfl
  right_inv := by intro; rfl
-/
def Fun.homEquiv (X Y : Type u) : (Fun X Y) ≃ (X -> Y) where
  toFun f := f
  invFun f := ⟨f⟩
  left_inv := by intro; rfl
  right_inv := by intro; rfl

/-- The type of morphisms in `Type`. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (X Y : Type u)
  axioms and operations (2):
    - private(mk) : :
    - hom' : Fun X Y

中文:
结构 态射
  参数: (X Y : 类型u)
  公理与运算 (2 个):
    - private(mk) : :
    - hom' : Fun X Y
-/
structure Hom (X Y : Type u) where
  private mk ::
  /-- The underlying function -/
  hom' : Fun X Y

end TypeCat

open TypeCat CategoryTheory

set_option backward.privateInPublic true in
@[to_additive_do_translate] -- Expressions involving this instance can still be additivized.
/--
Instance `CategoryTheory.types` / 实例 `CategoryTheory.types`

English:
instance CategoryTheory.types
  signature: : Category.{u} (Type u) where
  body: Hom
id X := .mk .id X
comp f g := .mk g.hom'.comp f.hom'

中文:
实例 范畴论.types
  签名: : 范畴.{u} (类型u) where
  定义体: Hom
id X := .mk .id X
comp f g := .mk g.hom'.comp f.hom'
-/
instance CategoryTheory.types : Category.{u} (Type u) where
  Hom := Hom
id X := .mk .id X
comp f g := .mk g.hom'.comp f.hom'

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ConcreteCategory.{u} (Type u) Fun
  body: Hom.hom'
  ofHom := Hom.mk

example (X Y : Type u) (f : X ⟶ Y) : (f : X -> Y) = (ConcreteCategory.hom f : X -> Y) := by
  with_reducible rfl

example (X Y : Type u) (f : X ⟶ Y) (x : X) : f x = (f : X -> Y) x := by
  with_reducible rfl

example (X Y : Type*) (f : Fun X Y) : (f : X -> Y) = f := by
  with_reducible rfl

example (X Y : Type*) (f : Fun X Y) (x : X) : f x = (f : X -> Y) x := by
  with_reducible rfl

中文:
实例 :
  签名: 余ncrete范畴.{u} (类型u) Fun
  定义体: Hom.hom'
  ofHom := Hom.mk

example (X Y : Type u) (f : X ⟶ Y) : (f : X -> Y) = (ConcreteCategory.hom f : X -> Y) := by
  with_reducible rfl

example (X Y : Type u) (f : X ⟶ Y) (x : X) : f x = (f : X -> Y) x := by
  with_reducible rfl

example (X Y : Type*) (f : Fun X Y) : (f : X -> Y) = f := by
  with_reducible rfl

example (X Y : Type*) (f : Fun X Y) (x : X) : f x = (f : X -> Y) x := by
  with_reducible rfl

Depends on / 依赖: Hom.hom
-/
instance : ConcreteCategory.{u} (Type u) Fun where
  hom := Hom.hom'
  ofHom := Hom.mk

example (X Y : Type u) (f : X ⟶ Y) : (f : X -> Y) = (ConcreteCategory.hom f : X -> Y) := by
  with_reducible rfl

example (X Y : Type u) (f : X ⟶ Y) (x : X) : f x = (f : X -> Y) x := by
  with_reducible rfl

example (X Y : Type*) (f : Fun X Y) : (f : X -> Y) = f := by
  with_reducible rfl

example (X Y : Type*) (f : Fun X Y) (x : X) : f x = (f : X -> Y) x := by
  with_reducible rfl

namespace TypeCat

/--
Definition of `Hom.hom` / `Hom.hom` 的定义

English:
abbreviation Hom.hom
  signature: {X Y : Type u} (f : Hom X Y)
  body: ConcreteCategory.hom (C := Type u) f

中文:
缩写 态射.hom
  签名: {X Y : 类型u} (f : 态射 X Y)
  定义体: ConcreteCategory.hom (C := Type u) f
-/
abbrev Hom.hom {X Y : Type u} (f : Hom X Y) : Fun X Y :=
  ConcreteCategory.hom (C := Type u) f

/--
Definition of `ofHom` / `ofHom` 的定义

English:
abbreviation ofHom
  signature: {X Y : Type u} (f : X -> Y)
  body: ConcreteCategory.ofHom (Fun.mk f)

中文:
缩写 ofHom
  签名: {X Y : 类型u} (f : X -> Y)
  定义体: ConcreteCategory.ofHom (Fun.mk f)

Depends on / 依赖: ConcreteCategory, ConcreteCategory.ofHom, Fun.mk
-/
abbrev ofHom {X Y : Type u} (f : X -> Y) : X ⟶ Y :=
  ConcreteCategory.ofHom (Fun.mk f)

end TypeCat

namespace CategoryTheory

@[inherit_doc]
scoped notation "↾" f:200 => TypeCat.ofHom f

end CategoryTheory

namespace TypeCat

/--
Definition of `Hom.Simps.hom` / `Hom.Simps.hom` 的定义

English:
definition Hom.Simps.hom
  signature: (X Y : Type u) (f : X ⟶ Y)
  body: ConcreteCategory.hom f

initialize_simps_projections Hom (hom' -> hom)

@[simp]

中文:
定义 态射.Simps.hom
  签名: (X Y : 类型u) (f : X ⟶ Y)
  定义体: ConcreteCategory.hom f

initialize_simps_projections Hom (hom' -> hom)

@[simp]
-/
def Hom.Simps.hom (X Y : Type u) (f : X ⟶ Y) :=
  ConcreteCategory.hom f

initialize_simps_projections Hom (hom' -> hom)

@[simp]
/--
lemma `Fun.toFun_apply` / 引理 `Fun.toFun_apply`

English:
lemma Fun.toFun_apply
  given: {X Y : Type u} (f : Fun X Y) (x : X)
  statement: f.toFun x = f x
  proof: rfl

example (X : Type u) : CategoryTheory.ToType X = X := by with_reducible rfl

@[simp]

中文:
引理 Fun.toFun_apply
  条件: {X Y : 类型u} (f : Fun X Y) (x : X)
  结论: f.toFun x = f x
  证明: rfl

example (X : Type u) : CategoryTheory.ToType X = X := by with_reducible rfl

@[simp]
-/
lemma Fun.toFun_apply {X Y : Type u} (f : Fun X Y) (x : X) : f.toFun x = f x :=
  rfl

example (X : Type u) : CategoryTheory.ToType X = X := by with_reducible rfl

@[simp]
/--
lemma `ofHom_eq` / 引理 `ofHom_eq`

English:
lemma ofHom_eq
  given: {X Y : Type u} (f : X ⟶ Y)
  statement: ofHom f = f
  proof: rfl

@[simp high]

中文:
引理 ofHom_eq
  条件: {X Y : 类型u} (f : X ⟶ Y)
  结论: ofHom f = f
  证明: rfl

@[simp high]
-/
lemma ofHom_eq {X Y : Type u} (f : X ⟶ Y) : ofHom f = f :=
  rfl

@[simp high]
/--
lemma `hom_ofHom` / 引理 `hom_ofHom`

English:
lemma hom_ofHom
  given: {X Y : Type u} (f : X -> Y)
  statement: Hom.hom (ofHom f) = Fun.mk f
  proof: rfl

@[simp]

中文:
引理 hom_ofHom
  条件: {X Y : 类型u} (f : X -> Y)
  结论: 态射.hom (ofHom f) = Fun.mk f
  证明: rfl

@[simp]
-/
lemma hom_ofHom {X Y : Type u} (f : X -> Y) : Hom.hom (ofHom f) = Fun.mk f := rfl

@[simp]
/--
lemma `ofHom_hom` / 引理 `ofHom_hom`

English:
lemma ofHom_hom
  given: {X Y : Type u} (f : X ⟶ Y)
  statement: ofHom (Hom.hom f) = f
  proof: rfl

@[simp]

中文:
引理 ofHom_hom
  条件: {X Y : 类型u} (f : X ⟶ Y)
  结论: ofHom (态射.hom f) = f
  证明: rfl

@[simp]
-/
lemma ofHom_hom {X Y : Type u} (f : X ⟶ Y) : ofHom (Hom.hom f) = f := rfl

@[simp]
/--
lemma `ofHom_apply` / 引理 `ofHom_apply`

English:
lemma ofHom_apply
  given: {X Y : Type u} (f : X -> Y) (x : X)
  proof: rfl

中文:
引理 ofHom_apply
  条件: {X Y : 类型u} (f : X -> Y) (x : X)
  证明: rfl
-/
lemma ofHom_apply {X Y : Type u} (f : X -> Y) (x : X) :
    (↾f) x = f x :=
  rfl

/--
Definition of `homEquiv` / `homEquiv` 的定义

English:
definition homEquiv
  signature: {X Y : Type u}
  body: (ConcreteCategory.homEquiv (C := Type u)).trans (Fun.homEquiv _ _)

@[simp]

中文:
定义 homEquiv
  签名: {X Y : 类型u}
  定义体: (ConcreteCategory.homEquiv (C := Type u)).trans (Fun.homEquiv _ _)

@[simp]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.homEquiv, Fun.homEquiv, homEquiv
-/
def homEquiv {X Y : Type u} : (X ⟶ Y) ≃ (X -> Y) :=
  (ConcreteCategory.homEquiv (C := Type u)).trans (Fun.homEquiv _ _)

@[simp]
/--
lemma `homEquiv_apply` / 引理 `homEquiv_apply`

English:
lemma homEquiv_apply
  given: {X Y : Type u} (f : X ⟶ Y)
  proof: rfl

@[simp]

中文:
引理 homEquiv_apply
  条件: {X Y : 类型u} (f : X ⟶ Y)
  证明: rfl

@[simp]
-/
lemma homEquiv_apply {X Y : Type u} (f : X ⟶ Y) :
    homEquiv f = f :=
  rfl

@[simp]
/--
lemma `homEquiv_symm_apply` / 引理 `homEquiv_symm_apply`

English:
lemma homEquiv_symm_apply
  given: {X Y : Type u} (f : X -> Y)
  proof: rfl

中文:
引理 homEquiv_symm_apply
  条件: {X Y : 类型u} (f : X -> Y)
  证明: rfl
-/
lemma homEquiv_symm_apply {X Y : Type u} (f : X -> Y) :
    homEquiv.symm f = ofHom f :=
  rfl

/--
lemma `congr_arg` / 引理 `congr_arg`

English:
lemma congr_arg
  given: {X Y : Type u} (f : X ⟶ Y) {x x' : X} (h : x = x')
  statement: f x = f x'
  proof: by
  rw [h]

中文:
引理 congr_arg
  条件: {X Y : 类型u} (f : X ⟶ Y) {x x' : X} (h : x = x')
  结论: f x = f x'
  证明: by
  rw [h]
-/
lemma congr_arg {X Y : Type u} (f : X ⟶ Y) {x x' : X} (h : x = x') : f x = f x' := by
  rw [h]

end TypeCat

namespace CategoryTheory

/--
theorem `types_id` / 定理 `types_id`

English:
theorem types_id
  given: (X : Type u)
  statement: (𝟙 X : _ -> _) = id
  proof: rfl

中文:
定理 types_id
  条件: (X : 类型u)
  结论: (𝟙 X : _ -> _) = id
  证明: rfl
-/
theorem types_id (X : Type u) : (𝟙 X : _ -> _) = id :=
  rfl

/--
theorem `types_comp` / 定理 `types_comp`

English:
theorem types_comp
  given: {X Y Z : Type u} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: rfl

@[simp]

中文:
定理 types_comp
  条件: {X Y Z : 类型u} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: rfl

@[simp]
-/
theorem types_comp {X Y Z : Type u} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ConcreteCategory.hom (f ≫ g) = g ∘ f :=
  rfl

@[simp]
/--
lemma `types_id_apply` / 引理 `types_id_apply`

English:
lemma types_id_apply
  given: (X : Type u) (x : X)
  statement: 𝟙 X x = x
  proof: rfl

@[simp]

中文:
引理 types_id_apply
  条件: (X : 类型u) (x : X)
  结论: 𝟙 X x = x
  证明: rfl

@[simp]
-/
lemma types_id_apply (X : Type u) (x : X) : 𝟙 X x = x :=
  rfl

@[simp]
/--
lemma `types_comp_apply` / 引理 `types_comp_apply`

English:
lemma types_comp_apply
  given: {X Y Z : Type u} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
  proof: rfl

@[congr]

中文:
引理 types_comp_apply
  条件: {X Y Z : 类型u} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
  证明: rfl

@[congr]
-/
lemma types_comp_apply {X Y Z : Type u} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g) x = g (f x) :=
  rfl

@[congr]
/--
lemma `types_congr_hom` / 引理 `types_congr_hom`

English:
lemma types_congr_hom
  given: {X Y : Type u} {f g : X ⟶ Y} (h : f = g) (x : X)
  statement: f x = g x
  proof: ConcreteCategory.congr_hom h x

@[deprecated (since := "2026-02-09")] alias hom_inv_id_apply := Iso.hom_inv_id_apply
@[deprecated (since := "2026-02-09")] alias inv_hom_id_apply := Iso.inv_hom_id_apply
@[deprecated (since := "2026-02-09")] alias asHom := ofHom

中文:
引理 types_congr_hom
  条件: {X Y : 类型u} {f g : X ⟶ Y} (h : f = g) (x : X)
  结论: f x = g x
  证明: ConcreteCategory.congr_hom h x

@[deprecated (since := "2026-02-09")] alias hom_inv_id_apply := Iso.hom_inv_id_apply
@[deprecated (since := "2026-02-09")] alias inv_hom_id_apply := Iso.inv_hom_id_apply
@[deprecated (since := "2026-02-09")] alias asHom := ofHom

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, congr_hom
-/
lemma types_congr_hom {X Y : Type u} {f g : X ⟶ Y} (h : f = g) (x : X) : f x = g x :=
  ConcreteCategory.congr_hom h x

@[deprecated (since := "2026-02-09")] alias hom_inv_id_apply := Iso.hom_inv_id_apply
@[deprecated (since := "2026-02-09")] alias inv_hom_id_apply := Iso.inv_hom_id_apply
@[deprecated (since := "2026-02-09")] alias asHom := ofHom

namespace Functor

variable {J : Type u} [Category.{v} J]

/--
Definition of `sections` / `sections` 的定义

English:
definition sections
  signature: (F : J ⥤ Type w)
  body: { u | forall {j j'} (f : j ⟶ j'), F.map f (u j) = u j' }

@[simp]

中文:
定义 sections
  签名: (F : J ⥤ 类型 w)
  定义体: { u | forall {j j'} (f : j ⟶ j'), F.map f (u j) = u j' }

@[simp]

Depends on / 依赖: F.map
-/
def sections (F : J ⥤ Type w) : Set (forall j, F.obj j) :=
  { u | forall {j j'} (f : j ⟶ j'), F.map f (u j) = u j' }

@[simp]
/--
lemma `sections_property` / 引理 `sections_property`

English:
lemma sections_property
  statement: {F : J ⥤ Type w} (s : F.sections)
  proof: s.property f

中文:
引理 sections_property
  结论: {F : J ⥤ 类型 w} (s : F.sections)
  证明: s.property f

Depends on / 依赖: property, s.property
-/
lemma sections_property {F : J ⥤ Type w} (s : F.sections)
    {j j' : J} (f : j ⟶ j') : F.map f (s.val j) = s.val j' :=
  s.property f

/--
lemma `sections_ext_iff` / 引理 `sections_ext_iff`

English:
lemma sections_ext_iff
  given: {F : J ⥤ Type w} {x y : F.sections}
  statement: x = y ↔ forall j, x.val j = y.val j
  proof: Subtype.ext_iff.trans funext_iff

中文:
引理 sections_ext_iff
  条件: {F : J ⥤ 类型 w} {x y : F.sections}
  结论: x = y ↔ 对任意 j, x.val j = y.val j
  证明: Subtype.ext_iff.trans funext_iff

Depends on / 依赖: Subtype, Subtype.ext_iff.trans, ext_iff, funext_iff
-/
lemma sections_ext_iff {F : J ⥤ Type w} {x y : F.sections} : x = y ↔ forall j, x.val j = y.val j :=
  Subtype.ext_iff.trans funext_iff

variable (J)

/-- The functor which sends a functor to types to its sections. -/
@[simps]
/--
Definition of `sectionsFunctor` / `sectionsFunctor` 的定义

English:
definition sectionsFunctor
  signature: : (J ⥤ Type w) ⥤ Type max u w where
  body: F.sections
  map {F G} φ := ↾fun x => ⟨fun j => φ.app j (x.1 j), fun {j j'} f =>
    by simp [← NatTrans.naturality_apply, x.2 f]⟩

中文:
定义 sectionsFunctor
  签名: : (J ⥤ 类型 w) ⥤ 类型 最大值 u w where
  定义体: F.sections
  map {F G} φ := ↾fun x => ⟨fun j => φ.app j (x.1 j), fun {j j'} f =>
    by simp [← NatTrans.naturality_apply, x.2 f]⟩

Depends on / 依赖: F.sections, sections
-/
def sectionsFunctor : (J ⥤ Type w) ⥤ Type max u w where
  obj F := F.sections
  map {F G} φ := ↾fun x => ⟨fun j => φ.app j (x.1 j), fun {j j'} f =>
    by simp [← NatTrans.naturality_apply, x.2 f]⟩

end Functor

namespace FunctorToTypes

variable {C : Type u} [Category.{v} C] (F G H : C ⥤ Type w) {X Y Z : C}
variable (σ : F ⟶ G) (τ : G ⟶ H)

attribute [elementwise nosimp] Functor.map_comp Functor.map_id NatTrans.comp_app

@[deprecated Functor.map_comp_apply (since := "2026-03-09")]
/--
theorem `map_comp_apply` / 定理 `map_comp_apply`

English:
theorem map_comp_apply
  given: (f : X ⟶ Y) (g : Y ⟶ Z) (a : F.obj X)
  proof: F.map_comp_apply f g a

@[deprecated Functor.map_id_apply (since := "2026-03-09")]

中文:
定理 map_comp_apply
  条件: (f : X ⟶ Y) (g : Y ⟶ Z) (a : F.obj X)
  证明: F.map_comp_apply f g a

@[deprecated Functor.map_id_apply (since := "2026-03-09")]

Depends on / 依赖: F.map_comp_apply, map_comp_apply
-/
theorem map_comp_apply (f : X ⟶ Y) (g : Y ⟶ Z) (a : F.obj X) :
    (F.map (f ≫ g)) a = (F.map g) ((F.map f) a) :=
  F.map_comp_apply f g a

@[deprecated Functor.map_id_apply (since := "2026-03-09")]
/--
theorem `map_id_apply` / 定理 `map_id_apply`

English:
theorem map_id_apply
  given: (a : F.obj X)
  statement: (F.map (𝟙 X)) a = a
  proof: F.map_id_apply X a

@[deprecated (since := "2026-02-09")] alias naturality := NatTrans.naturality_apply

@[deprecated NatTrans.comp_app_apply (since := "2026-03-09")]

中文:
定理 map_id_apply
  条件: (a : F.obj X)
  结论: (F.map (𝟙 X)) a = a
  证明: F.map_id_apply X a

@[deprecated (since := "2026-02-09")] alias naturality := NatTrans.naturality_apply

@[deprecated NatTrans.comp_app_apply (since := "2026-03-09")]

Depends on / 依赖: F.map_id_apply, map_id_apply
-/
theorem map_id_apply (a : F.obj X) : (F.map (𝟙 X)) a = a :=
  F.map_id_apply X a

@[deprecated (since := "2026-02-09")] alias naturality := NatTrans.naturality_apply

@[deprecated NatTrans.comp_app_apply (since := "2026-03-09")]
/--
theorem `comp` / 定理 `comp`

English:
theorem comp
  given: (x : F.obj X)
  statement: (σ ≫ τ).app X x = τ.app X (σ.app X x)
  proof: σ.comp_app_apply τ X x

中文:
定理 comp
  条件: (x : F.obj X)
  结论: (σ ≫ τ).app X x = τ.app X (σ.app X x)
  证明: σ.comp_app_apply τ X x

Depends on / 依赖: comp_app_apply
-/
theorem comp (x : F.obj X) : (σ ≫ τ).app X x = τ.app X (σ.app X x) :=
  σ.comp_app_apply τ X x

attribute [elementwise (attr := simp)] eqToHom_map_comp

@[deprecated "Use `elementwise_of% eqToHom_map_comp` instead" (since := "2026-02-09")]
/--
theorem `eqToHom_map_comp_apply` / 定理 `eqToHom_map_comp_apply`

English:
theorem eqToHom_map_comp_apply
  given: (p : X = Y) (q : Y = Z) (x : F.obj X)
  proof: by
  cat_disch

中文:
定理 eqToHom_map_comp_apply
  条件: (p : X = Y) (q : Y = Z) (x : F.obj X)
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
theorem eqToHom_map_comp_apply (p : X = Y) (q : Y = Z) (x : F.obj X) :
    F.map (eqToHom q) (F.map (eqToHom p) x) = F.map (eqToHom <| p.trans q) x := by
  cat_disch

variable {D : Type u'} [𝒟 : Category.{u'} D] (I J : D ⥤ C) (ρ : I ⟶ J) {W : D}

@[deprecated "No replacement" (since := "2026-02-09")]
/--
theorem `hcomp` / 定理 `hcomp`

English:
theorem hcomp
  given: (x : (I ⋙ F).obj W)
  statement: (ρ ◫ σ).app W x = (G.map (ρ.app W)) (σ.app (I.obj W) x)
  proof: rfl

中文:
定理 hcomp
  条件: (x : (I ⋙ F).obj W)
  结论: (ρ ◫ σ).app W x = (G.map (ρ.app W)) (σ.app (I.obj W) x)
  证明: rfl
-/
theorem hcomp (x : (I ⋙ F).obj W) : (ρ ◫ σ).app W x = (G.map (ρ.app W)) (σ.app (I.obj W) x) :=
  rfl

attribute [elementwise nosimp] Functor.map_hom_inv Functor.map_inv_hom
  Functor.map_hom_inv' Functor.map_inv_hom'

@[deprecated (since := "2026-02-09")] alias map_inv_map_hom_apply := Functor.map_hom_inv_apply
@[deprecated (since := "2026-02-09")] alias map_hom_map_inv_apply := Functor.map_inv_hom_apply

attribute [elementwise (attr := simp)] Iso.hom_inv_id_app Iso.inv_hom_id_app


@[deprecated (since := "2026-02-09")] alias hom_inv_id_app_apply := Iso.hom_inv_id_app_apply
@[deprecated (since := "2026-02-09")] alias inv_hom_id_app_apply := Iso.inv_hom_id_app_apply

/--
lemma `naturality_symm` / 引理 `naturality_symm`

English:
lemma naturality_symm
  statement: {F G : C ⥤ Type*} (e : forall j, F.obj j ≃ G.obj j)
  proof: by
  ext x
  obtain ⟨y, rfl⟩ := (e j).surjective x
  apply (e j').injective
  dsimp
  simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply]
  exact (congr_fun (naturality f) y).symm

中文:
引理 naturality_symm
  结论: {F G : C ⥤ 类型} (e : 对任意 j, F.obj j ≃ G.obj j)
  证明: by
  ext x
  obtain ⟨y, rfl⟩ := (e j).surjective x
  apply (e j').injective
  dsimp
  simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply]
  exact (congr_fun (naturality f) y).symm

Depends on / 依赖: Equiv.apply_symm_apply, Equiv.symm_apply_apply, apply_symm_apply, congr_fun, injective, naturality, surjective, symm_apply_apply
-/
lemma naturality_symm {F G : C ⥤ Type*} (e : forall j, F.obj j ≃ G.obj j)
    (naturality : forall {j j'} (f : j ⟶ j'), e j' ∘ F.map f = G.map f ∘ e j) {j j' : C}
    (f : j ⟶ j') :
    (e j').symm ∘ G.map f = F.map f ∘ (e j).symm := by
  ext x
  obtain ⟨y, rfl⟩ := (e j).surjective x
  apply (e j').injective
  dsimp
  simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply]
  exact (congr_fun (naturality f) y).symm

end FunctorToTypes

/--
Definition of `uliftTrivial` / `uliftTrivial` 的定义

English:
definition uliftTrivial
  signature: (V : Type u)
  body: ofHom fun a => a.1
  inv := ofHom fun a => .up a

中文:
定义 uliftTrivial
  签名: (V : 类型u)
  定义体: ofHom fun a => a.1
  inv := ofHom fun a => .up a
-/
def uliftTrivial (V : Type u) : ULift.{u} V ≅ V where
  hom := ofHom fun a => a.1
  inv := ofHom fun a => .up a

/-- The functor embedding `Type u` into `Type (max u v)`.
Write this as `uliftFunctor.{5, 2}` to get `Type 2 ⥤ Type 5`.
-/
@[pp_with_univ, simps obj map]
/--
Definition of `uliftFunctor` / `uliftFunctor` 的定义

English:
definition uliftFunctor
  signature: : Type u ⥤ Type max u v where
  body: ULift.{v} X
  map {X} {_} f := ofHom fun x : ULift.{v} X => ULift.up (f x.down)

中文:
定义 uliftFunctor
  签名: : 类型u ⥤ 类型 最大值 u v where
  定义体: ULift.{v} X
  map {X} {_} f := ofHom fun x : ULift.{v} X => ULift.up (f x.down)
-/
def uliftFunctor : Type u ⥤ Type max u v where
  obj X := ULift.{v} X
  map {X} {_} f := ofHom fun x : ULift.{v} X => ULift.up (f x.down)

/--
Definition of `fullyFaithfulULiftFunctor` / `fullyFaithfulULiftFunctor` 的定义

English:
definition fullyFaithfulULiftFunctor
  signature: : (uliftFunctor.{v, u}).FullyFaithful where
  body: ofHom fun x => (f (ULift.up x)).down

中文:
定义 fullyFaithfulULiftFunctor
  签名: : (uliftFunctor.{v, u}).满忠实 where
  定义体: ofHom fun x => (f (ULift.up x)).down

Depends on / 依赖: ULift.up
-/
def fullyFaithfulULiftFunctor : (uliftFunctor.{v, u}).FullyFaithful where
  preimage f := ofHom fun x => (f (ULift.up x)).down

/--
Instance `uliftFunctor_full` / 实例 `uliftFunctor_full`

English:
instance uliftFunctor_full
  signature: : (uliftFunctor.{v, u}).Full
  body: fullyFaithfulULiftFunctor.full

中文:
实例 uliftFunctor_full
  签名: : (uliftFunctor.{v, u}).满
  定义体: fullyFaithfulULiftFunctor.full

Depends on / 依赖: fullyFaithfulULiftFunctor, fullyFaithfulULiftFunctor.full
-/
instance uliftFunctor_full : (uliftFunctor.{v, u}).Full :=
  fullyFaithfulULiftFunctor.full

/--
Instance `uliftFunctor_faithful` / 实例 `uliftFunctor_faithful`

English:
instance uliftFunctor_faithful
  signature: : uliftFunctor.{v, u}.Faithful
  body: fullyFaithfulULiftFunctor.faithful

中文:
实例 uliftFunctor_faithful
  签名: : uliftFunctor.{v, u}.忠实
  定义体: fullyFaithfulULiftFunctor.faithful

Depends on / 依赖: faithful, fullyFaithfulULiftFunctor, fullyFaithfulULiftFunctor.faithful
-/
instance uliftFunctor_faithful : uliftFunctor.{v, u}.Faithful :=
  fullyFaithfulULiftFunctor.faithful

/--
Definition of `uliftFunctorTrivial` / `uliftFunctorTrivial` 的定义

English:
definition uliftFunctorTrivial
  signature: : uliftFunctor.{u, u} ≅ 𝟭 _
  body: NatIso.ofComponents uliftTrivial

中文:
定义 uliftFunctorTrivial
  签名: : uliftFunctor.{u, u} ≅ 𝟭 _
  定义体: NatIso.ofComponents uliftTrivial

Depends on / 依赖: NatIso, NatIso.ofComponents, ofComponents, uliftTrivial
-/
def uliftFunctorTrivial : uliftFunctor.{u, u} ≅ 𝟭 _ :=
  NatIso.ofComponents uliftTrivial

-- TODO We should connect this to a general story about concrete categories
-- whose forgetful functor is representable.
/--
Definition of `homOfElement` / `homOfElement` 的定义

English:
definition homOfElement
  signature: {X : Type u} (x : X)
  body: ofHom fun _ => x

中文:
定义 homOfElement
  签名: {X : 类型u} (x : X)
  定义体: ofHom fun _ => x
-/
def homOfElement {X : Type u} (x : X) : PUnit ⟶ X := ofHom fun _ => x

/--
theorem `homOfElement_eq_iff` / 定理 `homOfElement_eq_iff`

English:
theorem homOfElement_eq_iff
  given: {X : Type u} (x y : X)
  statement: homOfElement x = homOfElement y ↔ x = y
  proof: ⟨fun H => ConcreteCategory.congr_hom H PUnit.unit, by simp_all⟩

中文:
定理 homOfElement_eq_iff
  条件: {X : 类型u} (x y : X)
  结论: homOfElement x = homOfElement y ↔ x = y
  证明: ⟨fun H => ConcreteCategory.congr_hom H PUnit.unit, by simp_all⟩

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, PUnit.unit, congr_hom
-/
theorem homOfElement_eq_iff {X : Type u} (x y : X) : homOfElement x = homOfElement y ↔ x = y :=
  ⟨fun H => ConcreteCategory.congr_hom H PUnit.unit, by simp_all⟩

/-- A morphism in `Type` is a monomorphism if and only if it is injective. -/
@[stacks 003C]
/--
theorem `ofHom_mono_iff_injective` / 定理 `ofHom_mono_iff_injective`

English:
theorem ofHom_mono_iff_injective
  given: {X Y : Type u} (f : X -> Y)
  proof: by
  constructor
  · intro H x x' h
    rw [← homOfElement_eq_iff] at h ⊢
    exact (cancel_mono (ofHom f)).mp h
  · refine fun H => ⟨fun g g' h => ConcreteCategory.hom_ext _ _ fun x =>
      congrFun (H.comp_left ?_) x⟩
    ext y
    exact ConcreteCategory.congr_hom h y

中文:
定理 ofHom_mono_iff_injective
  条件: {X Y : 类型u} (f : X -> Y)
  证明: by
  constructor
  · intro H x x' h
    rw [← homOfElement_eq_iff] at h ⊢
    exact (cancel_mono (ofHom f)).mp h
  · refine fun H => ⟨fun g g' h => ConcreteCategory.hom_ext _ _ fun x =>
      congrFun (H.comp_left ?_) x⟩
    ext y
    exact ConcreteCategory.congr_hom h y

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, ConcreteCategory.hom_ext, H.comp_left, cancel_mono, comp_left, congr_hom, homOfElement_eq_iff, hom_ext
-/
theorem ofHom_mono_iff_injective {X Y : Type u} (f : X -> Y) :
    Mono (ofHom f) ↔ Function.Injective f := by
  constructor
  · intro H x x' h
    rw [← homOfElement_eq_iff] at h ⊢
    exact (cancel_mono (ofHom f)).mp h
  · refine fun H => ⟨fun g g' h => ConcreteCategory.hom_ext _ _ fun x =>
      congrFun (H.comp_left ?_) x⟩
    ext y
    exact ConcreteCategory.congr_hom h y

/-- A morphism in `Type` is a monomorphism if and only if it is injective. -/
@[stacks 003C]
/--
theorem `mono_iff_injective` / 定理 `mono_iff_injective`

English:
theorem mono_iff_injective
  given: {X Y : Type u} (f : X ⟶ Y)
  statement: Mono f ↔ Function.Injective f
  proof: by
  simp [← ofHom_mono_iff_injective]

中文:
定理 mono_iff_injective
  条件: {X Y : 类型u} (f : X ⟶ Y)
  结论: 单态射 f ↔ 函数.单射 f
  证明: by
  simp [← ofHom_mono_iff_injective]

Depends on / 依赖: ofHom_mono_iff_injective
-/
theorem mono_iff_injective {X Y : Type u} (f : X ⟶ Y) : Mono f ↔ Function.Injective f := by
  simp [← ofHom_mono_iff_injective]

/--
theorem `injective_of_mono` / 定理 `injective_of_mono`

English:
theorem injective_of_mono
  given: {X Y : Type u} (f : X ⟶ Y) [hf : Mono f]
  statement: Function.Injective f
  proof: (mono_iff_injective f).1 hf

中文:
定理 injective_of_mono
  条件: {X Y : 类型u} (f : X ⟶ Y) [hf : 单态射 f]
  结论: 函数.单射 f
  证明: (mono_iff_injective f).1 hf

Depends on / 依赖: mono_iff_injective
-/
theorem injective_of_mono {X Y : Type u} (f : X ⟶ Y) [hf : Mono f] : Function.Injective f :=
  (mono_iff_injective f).1 hf

/-- A morphism in `Type _` is an epimorphism if and only if it is surjective. -/
@[stacks 003C]
/--
theorem `ofHom_epi_iff_surjective` / 定理 `ofHom_epi_iff_surjective`

English:
theorem ofHom_epi_iff_surjective
  given: {X Y : Type u} (f : X -> Y)
  proof: by
  constructor
  · rintro ⟨H⟩
    refine Function.surjective_of_right_cancellable_Prop fun g₁ g₂ hg => ?_
    rw [← Equiv.ulift.{u}.symm.injective.comp_left.eq_iff]
    apply TypeCat.homEquiv.symm.injective
    apply H
    apply ConcreteCategory.hom_ext
    intro x
    simp [dsimp% congrFun hg x]
  · refine fun H => ⟨fun g g' h => ConcreteCategory.hom_ext _ _ fun x =>
      congrFun (H.injective_comp_right ?_) x⟩
    ext y
    exact ConcreteCategory.congr_hom h y

中文:
定理 ofHom_epi_iff_surjective
  条件: {X Y : 类型u} (f : X -> Y)
  证明: by
  constructor
  · rintro ⟨H⟩
    refine Function.surjective_of_right_cancellable_Prop fun g₁ g₂ hg => ?_
    rw [← Equiv.ulift.{u}.symm.injective.comp_left.eq_iff]
    apply TypeCat.homEquiv.symm.injective
    apply H
    apply ConcreteCategory.hom_ext
    intro x
    simp [dsimp% congrFun hg x]
  · refine fun H => ⟨fun g g' h => ConcreteCategory.hom_ext _ _ fun x =>
      congrFun (H.injective_comp_right ?_) x⟩
    ext y
    exact ConcreteCategory.congr_hom h y

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, ConcreteCategory.hom_ext, Equiv.ulift, Function, Function.surjective_of_right_cancellable_Prop, H.injective_comp_right, TypeCat, TypeCat.homEquiv.symm.injective, comp_left, congr_hom, eq_iff, homEquiv, hom_ext, injective, injective_comp_right, surjective_of_right_cancellable_Prop, symm.injective.comp_left.eq_iff
-/
theorem ofHom_epi_iff_surjective {X Y : Type u} (f : X -> Y) :
    Epi (ofHom f) ↔ Function.Surjective f := by
  constructor
  · rintro ⟨H⟩
    refine Function.surjective_of_right_cancellable_Prop fun g₁ g₂ hg => ?_
    rw [← Equiv.ulift.{u}.symm.injective.comp_left.eq_iff]
    apply TypeCat.homEquiv.symm.injective
    apply H
    apply ConcreteCategory.hom_ext
    intro x
    simp [dsimp% congrFun hg x]
  · refine fun H => ⟨fun g g' h => ConcreteCategory.hom_ext _ _ fun x =>
      congrFun (H.injective_comp_right ?_) x⟩
    ext y
    exact ConcreteCategory.congr_hom h y

/-- A morphism in `Type` is an epimorphism if and only if it is surjective. -/
@[stacks 003C]
/--
theorem `epi_iff_surjective` / 定理 `epi_iff_surjective`

English:
theorem epi_iff_surjective
  given: {X Y : Type u} (f : X ⟶ Y)
  statement: Epi f ↔ Function.Surjective f
  proof: by
  simp [← ofHom_epi_iff_surjective]

中文:
定理 epi_iff_surjective
  条件: {X Y : 类型u} (f : X ⟶ Y)
  结论: 满态射 f ↔ 函数.满射 f
  证明: by
  simp [← ofHom_epi_iff_surjective]

Depends on / 依赖: ofHom_epi_iff_surjective
-/
theorem epi_iff_surjective {X Y : Type u} (f : X ⟶ Y) : Epi f ↔ Function.Surjective f := by
  simp [← ofHom_epi_iff_surjective]

/--
theorem `surjective_of_epi` / 定理 `surjective_of_epi`

English:
theorem surjective_of_epi
  given: {X Y : Type u} (f : X ⟶ Y) [hf : Epi f]
  statement: Function.Surjective f
  proof: (epi_iff_surjective f).1 hf

中文:
定理 surjective_of_epi
  条件: {X Y : 类型u} (f : X ⟶ Y) [hf : 满态射 f]
  结论: 函数.满射 f
  证明: (epi_iff_surjective f).1 hf

Depends on / 依赖: epi_iff_surjective
-/
theorem surjective_of_epi {X Y : Type u} (f : X ⟶ Y) [hf : Epi f] : Function.Surjective f :=
  (epi_iff_surjective f).1 hf

section

/-- `ofTypeFunctor m` converts from Lean's `Type`-based `Category` to `CategoryTheory`. This
allows us to use these functors in category theory. -/
@[simps obj map]
/--
Definition of `ofTypeFunctor` / `ofTypeFunctor` 的定义

English:
definition ofTypeFunctor
  signature: (m : Type u -> Type v) [_root_.Functor m] [LawfulFunctor m]
  body: m x
  map f := ofHom (_root_.Functor.map f.hom)
  map_id := fun α => by ext X; apply id_map
  map_comp f g := by
    ext x
    exact comp_map (f := m) f.hom g.hom x

中文:
定义 ofTypeFunctor
  签名: (m : 类型u -> 类型v) [_root_.函子 m] [Lawful函子 m]
  定义体: m x
  map f := ofHom (_root_.Functor.map f.hom)
  map_id := fun α => by ext X; apply id_map
  map_comp f g := by
    ext x
    exact comp_map (f := m) f.hom g.hom x
-/
def ofTypeFunctor (m : Type u -> Type v) [_root_.Functor m] [LawfulFunctor m] :
    Type u ⥤ Type v where
  obj x := m x
  map f := ofHom (_root_.Functor.map f.hom)
  map_id := fun α => by ext X; apply id_map
  map_comp f g := by
    ext x
    exact comp_map (f := m) f.hom g.hom x

end

end CategoryTheory

-- Isomorphisms in Type and equivalences.
namespace Equiv

variable {X Y : Type u}

/-- Any equivalence between types in the same universe gives
a categorical isomorphism between those types.
-/
@[simps!]
/--
Definition of `toIso` / `toIso` 的定义

English:
definition toIso
  signature: (e : X ≃ Y)
  body: ofHom fun x => e x
  inv := ofHom fun x => e.symm x

@[deprecated (since := "2026-03-20")] alias toIso_hom := toIso_hom_hom_apply
@[deprecated (since := "2026-03-20")] alias toIso_inv := toIso_inv_hom_apply

中文:
定义 toIso
  签名: (e : X ≃ Y)
  定义体: ofHom fun x => e x
  inv := ofHom fun x => e.symm x

@[deprecated (since := "2026-03-20")] alias toIso_hom := toIso_hom_hom_apply
@[deprecated (since := "2026-03-20")] alias toIso_inv := toIso_inv_hom_apply
-/
def toIso (e : X ≃ Y) : X ≅ Y where
  hom := ofHom fun x => e x
  inv := ofHom fun x => e.symm x

@[deprecated (since := "2026-03-20")] alias toIso_hom := toIso_hom_hom_apply
@[deprecated (since := "2026-03-20")] alias toIso_inv := toIso_inv_hom_apply

end Equiv

namespace CategoryTheory.Iso

open CategoryTheory

variable {X Y : Type u}

/-- Any isomorphism between types gives an equivalence. -/
@[simps]
/--
Definition of `toEquiv` / `toEquiv` 的定义

English:
definition toEquiv
  signature: (i : X ≅ Y)
  body: i.hom
  invFun := i.inv
  left_inv x := by simp
  right_inv y := by simp

中文:
定义 toEquiv
  签名: (i : X ≅ Y)
  定义体: i.hom
  invFun := i.inv
  left_inv x := by simp
  right_inv y := by simp

Depends on / 依赖: i.hom
-/
def toEquiv (i : X ≅ Y) : X ≃ Y where
  toFun := i.hom
  invFun := i.inv
  left_inv x := by simp
  right_inv y := by simp

/--
theorem `toEquiv_fun` / 定理 `toEquiv_fun`

English:
theorem toEquiv_fun
  given: (i : X ≅ Y)
  statement: (i.toEquiv : X -> Y) = i.hom
  proof: rfl

中文:
定理 toEquiv_fun
  条件: (i : X ≅ Y)
  结论: (i.toEquiv : X -> Y) = i.hom
  证明: rfl
-/
theorem toEquiv_fun (i : X ≅ Y) : (i.toEquiv : X -> Y) = i.hom :=
  rfl

/--
theorem `toEquiv_symm_fun` / 定理 `toEquiv_symm_fun`

English:
theorem toEquiv_symm_fun
  given: (i : X ≅ Y)
  statement: (i.toEquiv.symm :) = (ConcreteCategory.hom i.inv).toFun
  proof: rfl

@[simp]

中文:
定理 toEquiv_symm_fun
  条件: (i : X ≅ Y)
  结论: (i.toEquiv.symm :) = (余ncrete范畴.hom i.inv).toFun
  证明: rfl

@[simp]
-/
theorem toEquiv_symm_fun (i : X ≅ Y) : (i.toEquiv.symm :) = (ConcreteCategory.hom i.inv).toFun :=
  rfl

@[simp]
/--
theorem `toEquiv_id` / 定理 `toEquiv_id`

English:
theorem toEquiv_id
  given: (X : Type u)
  statement: (Iso.refl X).toEquiv = Equiv.refl X
  proof: rfl

@[simp]

中文:
定理 toEquiv_id
  条件: (X : 类型u)
  结论: (同构.refl X).toEquiv = 等价.refl X
  证明: rfl

@[simp]
-/
theorem toEquiv_id (X : Type u) : (Iso.refl X).toEquiv = Equiv.refl X :=
  rfl

@[simp]
/--
theorem `toEquiv_comp` / 定理 `toEquiv_comp`

English:
theorem toEquiv_comp
  given: {X Y Z : Type u} (f : X ≅ Y) (g : Y ≅ Z)
  proof: rfl

中文:
定理 toEquiv_comp
  条件: {X Y Z : 类型u} (f : X ≅ Y) (g : Y ≅ Z)
  证明: rfl
-/
theorem toEquiv_comp {X Y Z : Type u} (f : X ≅ Y) (g : Y ≅ Z) :
    (f ≪≫ g).toEquiv = f.toEquiv.trans g.toEquiv :=
  rfl

end CategoryTheory.Iso

namespace CategoryTheory

/--
theorem `isIso_iff_bijective` / 定理 `isIso_iff_bijective`

English:
theorem isIso_iff_bijective
  given: {X Y : Type u} (f : X ⟶ Y)
  statement: IsIso f ↔ Function.Bijective f
  proof: Iff.intro (fun _ => (asIso f : X ≅ Y).toEquiv.bijective) fun b =>
    (Equiv.ofBijective f b).toIso.isIso_hom

中文:
定理 isIso_iff_bijective
  条件: {X Y : 类型u} (f : X ⟶ Y)
  结论: 是同构 f ↔ 函数.双射 f
  证明: Iff.intro (fun _ => (asIso f : X ≅ Y).toEquiv.bijective) fun b =>
    (Equiv.ofBijective f b).toIso.isIso_hom

Depends on / 依赖: Equiv.ofBijective, Iff.intro, bijective, isIso_hom, ofBijective, toEquiv, toEquiv.bijective, toIso.isIso_hom
-/
theorem isIso_iff_bijective {X Y : Type u} (f : X ⟶ Y) : IsIso f ↔ Function.Bijective f :=
  Iff.intro (fun _ => (asIso f : X ≅ Y).toEquiv.bijective) fun b =>
    (Equiv.ofBijective f b).toIso.isIso_hom

/--
theorem `bijective_iff_isIso_ofHom` / 定理 `bijective_iff_isIso_ofHom`

English:
theorem bijective_iff_isIso_ofHom
  given: {X Y : Type u} (f : X -> Y)
  proof: Iff.intro (fun b => (Equiv.ofBijective f b).toIso.isIso_hom)
    fun _ => (asIso (ofHom f) : X ≅ Y).toEquiv.bijective

中文:
定理 bijective_iff_isIso_ofHom
  条件: {X Y : 类型u} (f : X -> Y)
  证明: Iff.intro (fun b => (Equiv.ofBijective f b).toIso.isIso_hom)
    fun _ => (asIso (ofHom f) : X ≅ Y).toEquiv.bijective

Depends on / 依赖: Equiv.ofBijective, Iff.intro, bijective, isIso_hom, ofBijective, toEquiv, toEquiv.bijective, toIso.isIso_hom
-/
theorem bijective_iff_isIso_ofHom {X Y : Type u} (f : X -> Y) :
    Function.Bijective f ↔ IsIso (ofHom f) :=
  Iff.intro (fun b => (Equiv.ofBijective f b).toIso.isIso_hom)
    fun _ => (asIso (ofHom f) : X ≅ Y).toEquiv.bijective

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SplitEpiCategory (Type u)
  body: IsSplitEpi.mk'
      { section_ := ofHom <| Function.surjInv <| (epi_iff_surjective f).1 hf
        id := by
          ext x
          exact (Function.rightInverse_surjInv <| (epi_iff_surjective f).1 hf) x }

中文:
实例 :
  签名: 分裂满态射范畴 (类型u)
  定义体: IsSplitEpi.mk'
      { section_ := ofHom <| Function.surjInv <| (epi_iff_surjective f).1 hf
        id := by
          ext x
          exact (Function.rightInverse_surjInv <| (epi_iff_surjective f).1 hf) x }

Depends on / 依赖: Function, Function.rightInverse_surjInv, Function.surjInv, IsSplitEpi, IsSplitEpi.mk, epi_iff_surjective, rightInverse_surjInv, section_, surjInv
-/
instance : SplitEpiCategory (Type u) where
  isSplitEpi_of_epi f hf :=
IsSplitEpi.mk'
      { section_ := ofHom <| Function.surjInv <| (epi_iff_surjective f).1 hf
        id := by
          ext x
          exact (Function.rightInverse_surjInv <| (epi_iff_surjective f).1 hf) x }

/--
theorem `isSplitEpi_iff_surjective` / 定理 `isSplitEpi_iff_surjective`

English:
theorem isSplitEpi_iff_surjective
  given: {X Y : Type u} (f : X ⟶ Y)
  proof: Iff.intro (fun _ => surjective_of_epi _)
    fun hf => (by simp only [(epi_iff_surjective f).mpr hf, isSplitEpi_of_epi])

中文:
定理 isSplitEpi_iff_surjective
  条件: {X Y : 类型u} (f : X ⟶ Y)
  证明: Iff.intro (fun _ => surjective_of_epi _)
    fun hf => (by simp only [(epi_iff_surjective f).mpr hf, isSplitEpi_of_epi])

Depends on / 依赖: Iff.intro, epi_iff_surjective, isSplitEpi_of_epi, surjective_of_epi
-/
theorem isSplitEpi_iff_surjective {X Y : Type u} (f : X ⟶ Y) :
    IsSplitEpi f ↔ Function.Surjective f :=
  Iff.intro (fun _ => surjective_of_epi _)
    fun hf => (by simp only [(epi_iff_surjective f).mpr hf, isSplitEpi_of_epi])

end CategoryTheory

-- We prove `equivIsoIso` and then use that to sneakily construct `equivEquivIso`.
-- (In this order the proofs are handled by `cat_disch`.)
/-- Equivalences (between types in the same universe) are the same as (isomorphic to) isomorphisms
of types. -/
@[simps]
/--
Definition of `equivIsoIso` / `equivIsoIso` 的定义

English:
definition equivIsoIso
  signature: {X Y : Type u}
  body: ofHom fun e => e.toIso
  inv := ofHom fun i => i.toEquiv

中文:
定义 equivIsoIso
  签名: {X Y : 类型u}
  定义体: ofHom fun e => e.toIso
  inv := ofHom fun i => i.toEquiv

Depends on / 依赖: e.toIso
-/
def equivIsoIso {X Y : Type u} : (X ≃ Y) ≅ (X ≅ Y) where
  hom := ofHom fun e => e.toIso
  inv := ofHom fun i => i.toEquiv

/--
Definition of `equivEquivIso` / `equivEquivIso` 的定义

English:
definition equivEquivIso
  signature: {X Y : Type u}
  body: equivIsoIso.toEquiv

@[simp]

中文:
定义 equivEquivIso
  签名: {X Y : 类型u}
  定义体: equivIsoIso.toEquiv

@[simp]

Depends on / 依赖: equivIsoIso, equivIsoIso.toEquiv, toEquiv
-/
def equivEquivIso {X Y : Type u} : X ≃ Y ≃ (X ≅ Y) :=
  equivIsoIso.toEquiv

@[simp]
/--
theorem `equivEquivIso_hom` / 定理 `equivEquivIso_hom`

English:
theorem equivEquivIso_hom
  given: {X Y : Type u} (e : X ≃ Y)
  statement: equivEquivIso e = e.toIso
  proof: rfl

@[simp]

中文:
定理 equivEquivIso_hom
  条件: {X Y : 类型u} (e : X ≃ Y)
  结论: equivEquivIso e = e.toIso
  证明: rfl

@[simp]
-/
theorem equivEquivIso_hom {X Y : Type u} (e : X ≃ Y) : equivEquivIso e = e.toIso :=
  rfl

@[simp]
/--
theorem `equivEquivIso_inv` / 定理 `equivEquivIso_inv`

English:
theorem equivEquivIso_inv
  given: {X Y : Type u} (e : X ≅ Y)
  statement: equivEquivIso.symm e = e.toEquiv
  proof: rfl

中文:
定理 equivEquivIso_inv
  条件: {X Y : 类型u} (e : X ≅ Y)
  结论: equivEquivIso.symm e = e.toEquiv
  证明: rfl
-/
theorem equivEquivIso_inv {X Y : Type u} (e : X ≅ Y) : equivEquivIso.symm e = e.toEquiv :=
  rfl
