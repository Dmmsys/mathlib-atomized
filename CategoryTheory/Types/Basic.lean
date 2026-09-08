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
*  epimorphisms are surjections and monomorphisms are injections,
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
/-
**TypeCat.Fun** 是 Mathlib 中的一个归纳类型，位于命名空间 `TypeCat`。
形式化陈述：Type u_1 → Type u_2 → Type (max u_1 u_2)
参数：max u_1 u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A one-field structure wrapping a function between types.
-/
structure Fun (X Y : Type*) where
  /-- The underlying function. -/
  toFun : X → Y
/-
**TypeCat.instFunLikeFun** 是 Mathlib 中的一个实例，位于命名空间 `TypeCat`。
形式化陈述：instFunLikeFun {X Y : Type*} : FunLike (Fun X Y) X Y where coe f x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFunLikeFun {X Y : Type*} : FunLike (Fun X Y) X Y where
  coe f x := f.toFun x
  coe_injective _ := by aesop

initialize_simps_projections Fun (toFun → apply)
/-
**TypeCat.Fun.mk_apply** 是 Mathlib 中的一个定理，位于命名空间 `TypeCat.Fun`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} (f : X → Y) (x : X), { toFun := f } x = f 
x
参数：f : X → Y；x : X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Fun.mk_apply {X Y : Type*} (f : X → Y) (x : X) : (Fun.mk f) x = f x :=
  rfl

@[simp]
/-
**TypeCat.Fun.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `TypeCat.Fun`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} (f : X → Y), ⇑{ toFun := f } = f
参数：f : X → Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Fun.coe_mk {X Y : Type*} (f : X → Y) : (Fun.mk f : X → Y) = f :=
  rfl

/-- The identity function as a `Fun`. -/
@[simps! +dsimpLhs]
/-
**TypeCat.Fun.id** 是 Mathlib 中的一个定义，位于命名空间 `TypeCat.Fun`。
形式化陈述：(X : Type u_1) → TypeCat.Fun X X
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity function as a `Fun`.
-/
def Fun.id (X : Type*) : Fun X X := Fun.mk _root_.id

/-- Composition of `Fun`s. -/
@[simps! +dsimpLhs]
/-
**TypeCat.Fun.comp** 是 Mathlib 中的一个定义，位于命名空间 `TypeCat.Fun`。
形式化陈述：{X : Type u_1} → {Y : Type u_2} → {Z : Type u_3} → TypeCat.Fun Y Z → TypeC
at.Fun X Y → TypeCat.Fun X Z
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of `Fun`s.
-/
def Fun.comp {X Y Z : Type*} (f : Fun Y Z) (g : Fun X Y) : Fun X Z := mk (f.toFun ∘ g.toFun)

/-- The equivalence between `Fun`s and functions between types. -/
/-
**TypeCat.Fun.homEquiv** 是 Mathlib 中的一个定义，位于命名空间 `TypeCat.Fun`。
形式化陈述：(X Y : Type u) → TypeCat.Fun X Y ≃ (X → Y)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between `Fun`s and functions between types.
-/
def Fun.homEquiv (X Y : Type u) : (Fun X Y) ≃ (X → Y) where
  toFun f := f
  invFun f := ⟨f⟩
  left_inv := by intro; rfl
  right_inv := by intro; rfl

/-- The type of morphisms in `Type`. -/
@[ext]
/-
**TypeCat.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `TypeCat`。
形式化陈述：Type u → Type u → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of morphisms in `Type`.
-/
structure Hom (X Y : Type u) where
  private mk ::
  /-- The underlying function -/
  hom' : Fun X Y

end TypeCat

open TypeCat CategoryTheory

set_option backward.privateInPublic true in
@[to_additive_do_translate] -- Expressions involving this instance can still be additivized.
/-
**CategoryTheory.types** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：CategoryTheory.types : Category.{u} (Type u) where Hom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance CategoryTheory.types : Category.{u} (Type u) where
  Hom := Hom
  id X := .mk <| .id X
  comp f g := .mk <| g.hom'.comp f.hom'

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
The concrete category instance on `Type u`.

Note: sometimes one needs to specify explicitly `(CC := fun X ↦ X)` to help typeclass inference.
-/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The concrete category instance on `Type u`.

Note: sometimes one needs to specify explicitly `(CC := fun X ↦ X)` to help type
class inference.
-/
instance : ConcreteCategory.{u} (Type u) Fun where
  hom := Hom.hom'
  ofHom := Hom.mk
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (X Y : Type u) (f : X ⟶ Y) : (f : X → Y) = (ConcreteCategory.hom f : X → Y) := by
  with_reducible rfl
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (X Y : Type u) (f : X ⟶ Y) (x : X) : f x = (f : X → Y) x := by
  with_reducible rfl
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (X Y : Type*) (f : Fun X Y) : (f : X → Y) = f := by
  with_reducible rfl
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (X Y : Type*) (f : Fun X Y) (x : X) : f x = (f : X → Y) x := by
  with_reducible rfl

namespace TypeCat

/-- Turn a morphism in `Type` back into a function. -/
/-
**TypeCat.Hom.hom** 是 Mathlib 中的一个定义，位于命名空间 `TypeCat.Hom`。
形式化陈述：{X Y : Type u} → TypeCat.Hom X Y → TypeCat.Fun X Y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a morphism in `Type` back into a function.
-/
abbrev Hom.hom {X Y : Type u} (f : Hom X Y) : Fun X Y :=
  ConcreteCategory.hom (C := Type u) f

/-- Typecheck a function as a morphism in `Type`. -/
/-
**TypeCat.ofHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `TypeCat`。
形式化陈述：ofHom {X Y : Type u} (f : X -> Y) : X ⟶ Y
参数：f : X -> Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typecheck a function as a morphism in `Type`.
-/
abbrev ofHom {X Y : Type u} (f : X → Y) : X ⟶ Y :=
  ConcreteCategory.ofHom (Fun.mk f)

end TypeCat

namespace CategoryTheory

@[inherit_doc]
scoped notation "↾" f:200 => TypeCat.ofHom f

end CategoryTheory

namespace TypeCat

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
/-
**TypeCat.Hom.Simps.hom** 是 Mathlib 中的一个定义，位于命名空间 `TypeCat.Hom.Simps`。
形式化陈述：(X Y : Type u) → (X ⟶ Y) → TypeCat.Fun X Y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas.
-/
def Hom.Simps.hom (X Y : Type u) (f : X ⟶ Y) :=
  ConcreteCategory.hom f

initialize_simps_projections Hom (hom' → hom)

@[simp]
/-
**TypeCat.Fun.toFun_apply** 是 Mathlib 中的一个定理，位于命名空间 `TypeCat.Fun`。
形式化陈述：∀ {X Y : Type u} (f : TypeCat.Fun X Y) (x : X), f.toFun x = f x
参数：f : TypeCat.Fun X Y；x : X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Fun.toFun_apply {X Y : Type u} (f : Fun X Y) (x : X) : f.toFun x = f x :=
  rfl
/-
**TypeCat.** 是 Mathlib 中的一个示例，位于命名空间 `TypeCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (X : Type u) : CategoryTheory.ToType X = X := by with_reducible rfl

@[simp]
/-
**TypeCat.ofHom_eq** 是 Mathlib 中的一个引理，位于命名空间 `TypeCat`。
形式化陈述：ofHom_eq {X Y : Type u} (f : X ⟶ Y) : ofHom f = f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_eq {X Y : Type u} (f : X ⟶ Y) : ofHom f = f :=
  rfl

@[simp high]
/-
**TypeCat.hom_ofHom** 是 Mathlib 中的一个引理，位于命名空间 `TypeCat`。
形式化陈述：hom_ofHom {X Y : Type u} (f : X -> Y) : Hom.hom (ofHom f) = Fun.mk f
参数：f : X -> Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_ofHom {X Y : Type u} (f : X → Y) : Hom.hom (ofHom f) = Fun.mk f := rfl

@[simp]
/-
**TypeCat.ofHom_hom** 是 Mathlib 中的一个引理，位于命名空间 `TypeCat`。
形式化陈述：ofHom_hom {X Y : Type u} (f : X ⟶ Y) : ofHom (Hom.hom f) = f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_hom {X Y : Type u} (f : X ⟶ Y) : ofHom (Hom.hom f) = f := rfl

@[simp]
/-
**TypeCat.ofHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `TypeCat`。
形式化陈述：ofHom_apply {X Y : Type u} (f : X -> Y) (x : X) : (↾f) x = f x
参数：f : X -> Y；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_apply {X Y : Type u} (f : X → Y) (x : X) :
    (↾f) x = f x :=
  rfl

/-- `TypeCat.Hom.hom` bundled as an `Equiv`. -/
/-
**TypeCat.homEquiv** 是 Mathlib 中的一个定义，位于命名空间 `TypeCat`。
形式化陈述：homEquiv {X Y : Type u} : (X ⟶ Y) ≃ (X -> Y)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
`TypeCat.Hom.hom` bundled as an `Equiv`.
-/
def homEquiv {X Y : Type u} : (X ⟶ Y) ≃ (X → Y) :=
  (ConcreteCategory.homEquiv (C := Type u)).trans (Fun.homEquiv _ _)

@[simp]
/-
**TypeCat.homEquiv_apply** 是 Mathlib 中的一个引理，位于命名空间 `TypeCat`。
形式化陈述：homEquiv_apply {X Y : Type u} (f : X ⟶ Y) : homEquiv f = f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homEquiv_apply {X Y : Type u} (f : X ⟶ Y) :
    homEquiv f = f :=
  rfl

@[simp]
/-
**TypeCat.homEquiv_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `TypeCat`。
形式化陈述：homEquiv_symm_apply {X Y : Type u} (f : X -> Y) : homEquiv.symm f = ofHom 
f
参数：f : X -> Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma homEquiv_symm_apply {X Y : Type u} (f : X → Y) :
    homEquiv.symm f = ofHom f :=
  rfl
/-
**TypeCat.congr_arg** 是 Mathlib 中的一个引理，位于命名空间 `TypeCat`。
形式化陈述：congr_arg {X Y : Type u} (f : X ⟶ Y) {x x' : X} (h : x = x') : f x = f x'
参数：f : X ⟶ Y；h : x = x'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma congr_arg {X Y : Type u} (f : X ⟶ Y) {x x' : X} (h : x = x') : f x = f x' := by
  rw [h]

end TypeCat

namespace CategoryTheory

/-
**CategoryTheory.types_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：types_id (X : Type u) : (𝟙 X : _ -> _) = id
参数：X : Type u。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem types_id (X : Type u) : (𝟙 X : _ → _) = id :=
  rfl
/-
**CategoryTheory.types_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：types_comp {X Y Z : Type u} (f : X ⟶ Y) (g : Y ⟶ Z) : ConcreteCategory.hom
 (f ≫ g) = g ∘ f
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem types_comp {X Y Z : Type u} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ConcreteCategory.hom (f ≫ g) = g ∘ f :=
  rfl

@[simp]
/-
**CategoryTheory.types_id_apply** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：types_id_apply (X : Type u) (x : X) : 𝟙 X x = x
参数：X : Type u；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma types_id_apply (X : Type u) (x : X) : 𝟙 X x = x :=
  rfl

@[simp]
/-
**CategoryTheory.types_comp_apply** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：types_comp_apply {X Y Z : Type u} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g
) x = g (f x)
参数：f : X ⟶ Y；g : Y ⟶ Z；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma types_comp_apply {X Y Z : Type u} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g) x = g (f x) :=
  rfl

@[congr]
/-
**CategoryTheory.types_congr_hom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：types_congr_hom {X Y : Type u} {f g : X ⟶ Y} (h : f = g) (x : X) : f x = g
 x
参数：h : f = g；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
-/
lemma types_congr_hom {X Y : Type u} {f g : X ⟶ Y} (h : f = g) (x : X) : f x = g x :=
  ConcreteCategory.congr_hom h x

@[deprecated (since := "2026-02-09")] alias hom_inv_id_apply := Iso.hom_inv_id_apply
@[deprecated (since := "2026-02-09")] alias inv_hom_id_apply := Iso.inv_hom_id_apply
@[deprecated (since := "2026-02-09")] alias asHom := ofHom

namespace Functor

variable {J : Type u} [Category.{v} J]

/-- The sections of a functor `F : J ⥤ Type` are
the choices of a point `u j : F.obj j` for each `j`,
such that `F.map f (u j) = u j'` for every morphism `f : j ⟶ j'`.

We later use these to define limits in `Type` and in many concrete categories.
-/
/-
**CategoryTheory.Functor.sections** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Func
tor`。
形式化陈述：sections (F : J ⥤ Type w) : Set (forall j, F.obj j)
参数：F : J ⥤ Type w。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sections of a functor `F : J ⥤ Type` are
the choices of a point `u j : F.obj j` for each `j`,
such that `F.map f (u j) = u j'` for every morphism `f : j ⟶ j'`.

We later use these to define limits in `Type` and in many concrete categories.
-/
def sections (F : J ⥤ Type w) : Set (∀ j, F.obj j) :=
  { u | ∀ {j j'} (f : j ⟶ j'), F.map f (u j) = u j' }

@[simp]
/-
**CategoryTheory.Functor.sections_property** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.Functor`。
形式化陈述：sections_property {F : J ⥤ Type w} (s : F.sections) {j j' : J} (f : j ⟶ j'
) : F.map f (s.val j) = s.val j'
参数：s : F.sections；f : j ⟶ j'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma sections_property {F : J ⥤ Type w} (s : F.sections)
    {j j' : J} (f : j ⟶ j') : F.map f (s.val j) = s.val j' :=
  s.property f
/-
**CategoryTheory.Functor.sections_ext_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Functor`。
形式化陈述：sections_ext_iff {F : J ⥤ Type w} {x y : F.sections} : x = y ↔ forall j, x
.val j = y.val j
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x
-/
lemma sections_ext_iff {F : J ⥤ Type w} {x y : F.sections} : x = y ↔ ∀ j, x.val j = y.val j :=
  Subtype.ext_iff.trans funext_iff

variable (J)

/-- The functor which sends a functor to types to its sections. -/
@[simps]
/-
**CategoryTheory.Functor.sectionsFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Functor`。
形式化陈述：sectionsFunctor : (J ⥤ Type w) ⥤ Type max u w where obj F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor which sends a functor to types to its sections.
-/
def sectionsFunctor : (J ⥤ Type w) ⥤ Type max u w where
  obj F := F.sections
  map {F G} φ := ↾fun x ↦ ⟨fun j => φ.app j (x.1 j), fun {j j'} f =>
    by simp [← NatTrans.naturality_apply, x.2 f]⟩

end Functor

namespace FunctorToTypes

variable {C : Type u} [Category.{v} C] (F G H : C ⥤ Type w) {X Y Z : C}
variable (σ : F ⟶ G) (τ : G ⟶ H)

attribute [elementwise nosimp] Functor.map_comp Functor.map_id NatTrans.comp_app

@[deprecated Functor.map_comp_apply (since := "2026-03-09")]
/-
**CategoryTheory.FunctorToTypes.map_comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.FunctorToTypes`。
形式化陈述：map_comp_apply (f : X ⟶ Y) (g : Y ⟶ Z) (a : F.obj X) : (F.map (f ≫ g)) a =
 (F.map g) ((F.map f) a)
参数：f : X ⟶ Y；g : Y ⟶ Z；a : F.obj X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_comp_apply`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, 
u₂} D]   (self : CategoryTh…
-/
theorem map_comp_apply (f : X ⟶ Y) (g : Y ⟶ Z) (a : F.obj X) :
    (F.map (f ≫ g)) a = (F.map g) ((F.map f) a) :=
  F.map_comp_apply f g a

@[deprecated Functor.map_id_apply (since := "2026-03-09")]
/-
**CategoryTheory.FunctorToTypes.map_id_apply** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.FunctorToTypes`。
形式化陈述：map_id_apply (a : F.obj X) : (F.map (𝟙 X)) a = a
参数：a : F.obj X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_id_apply`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   (self : CategoryTh…
-/
theorem map_id_apply (a : F.obj X) : (F.map (𝟙 X)) a = a :=
  F.map_id_apply X a

@[deprecated (since := "2026-02-09")] alias naturality := NatTrans.naturality_apply

@[deprecated NatTrans.comp_app_apply (since := "2026-03-09")]
/-
**CategoryTheory.FunctorToTypes.comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.F
unctorToTypes`。
形式化陈述：comp (x : F.obj X) : (σ ≫ τ).app X x = τ.app X (σ.app X x)
参数：x : F.obj X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.comp_app_apply`：∀ {C : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂,
 u₂} D]   {F G H : CategoryT…
-/
theorem comp (x : F.obj X) : (σ ≫ τ).app X x = τ.app X (σ.app X x) :=
  σ.comp_app_apply τ X x

attribute [elementwise (attr := simp)] eqToHom_map_comp

@[deprecated "Use `elementwise_of% eqToHom_map_comp` instead" (since := "2026-02-09")]
/-
**CategoryTheory.FunctorToTypes.eqToHom_map_comp_apply** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.FunctorToTypes`。
形式化陈述：eqToHom_map_comp_apply (p : X = Y) (q : Y = Z) (x : F.obj X) : F.map (eqTo
Hom q) (F.map (eqToHom p) x) = F.map (eqToHom <| p.trans q) x
参数：p : X = Y；q : Y = Z；x : F.obj X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eqToHom_map_comp_apply (p : X = Y) (q : Y = Z) (x : F.obj X) :
    F.map (eqToHom q) (F.map (eqToHom p) x) = F.map (eqToHom <| p.trans q) x := by
  cat_disch

variable {D : Type u'} [𝒟 : Category.{u'} D] (I J : D ⥤ C) (ρ : I ⟶ J) {W : D}

@[deprecated "No replacement" (since := "2026-02-09")]
/-
**CategoryTheory.FunctorToTypes.hcomp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
FunctorToTypes`。
形式化陈述：hcomp (x : (I ⋙ F).obj W) : (ρ ◫ σ).app W x = (G.map (ρ.app W)) (σ.app (I.
obj W) x)
参数：x : (I ⋙ F).obj W。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**CategoryTheory.FunctorToTypes.naturality_symm** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.FunctorToTypes`。
形式化陈述：naturality_symm {F G : C ⥤ Type*} (e : forall j, F.obj j ≃ G.obj j) (natur
ality : forall {j j'} (f : j ⟶ j'), e j' ∘ F.map f = G.map f ∘ e j) {j j' : C} (
f : j ⟶ j') : (e j').symm ∘ G.map f = F.map f ∘ (e j).symm
参数：e : forall j, F.obj j ≃ G.obj j；naturality : forall {j j'} (f : j ⟶ j'), e j'
 ∘ F.map f = G.map f ∘ e j；f : j ⟶ j'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
-/
lemma naturality_symm {F G : C ⥤ Type*} (e : ∀ j, F.obj j ≃ G.obj j)
    (naturality : ∀ {j j'} (f : j ⟶ j'), e j' ∘ F.map f = G.map f ∘ e j) {j j' : C}
    (f : j ⟶ j') :
    (e j').symm ∘ G.map f = F.map f ∘ (e j).symm := by
  ext x
  obtain ⟨y, rfl⟩ := (e j).surjective x
  apply (e j').injective
  dsimp
  simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply]
  exact (congr_fun (naturality f) y).symm

end FunctorToTypes

/-- The isomorphism between a `Type` which has been `ULift`ed to the same universe,
and the original type.
-/
/-
**CategoryTheory.uliftTrivial** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：uliftTrivial (V : Type u) : ULift.{u} V ≅ V where hom
参数：V : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism between a `Type` which has been `ULift`ed to the same universe,
and the original type.
-/
def uliftTrivial (V : Type u) : ULift.{u} V ≅ V where
  hom := ofHom fun a ↦ a.1
  inv := ofHom fun a ↦ .up a

/-- The functor embedding `Type u` into `Type (max u v)`.
Write this as `uliftFunctor.{5, 2}` to get `Type 2 ⥤ Type 5`.
-/
@[pp_with_univ, simps obj map]
/-
**CategoryTheory.uliftFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：uliftFunctor : Type u ⥤ Type max u v where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor embedding `Type u` into `Type (max u v)`.
Write this as `uliftFunctor.{5, 2}` to get `Type 2 ⥤ Type 5`.
-/
def uliftFunctor : Type u ⥤ Type max u v where
  obj X := ULift.{v} X
  map {X} {_} f := ofHom fun x : ULift.{v} X => ULift.up (f x.down)

/-- `uliftFunctor : Type u ⥤ Type max u v` is fully faithful. -/
/-
**CategoryTheory.fullyFaithfulULiftFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory`。
形式化陈述：fullyFaithfulULiftFunctor : (uliftFunctor.{v, u}).FullyFaithful where prei
mage f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`uliftFunctor : Type u ⥤ Type max u v` is fully faithful.
-/
def fullyFaithfulULiftFunctor : (uliftFunctor.{v, u}).FullyFaithful where
  preimage f := ofHom fun x ↦ (f (ULift.up x)).down
/-
**CategoryTheory.uliftFunctor_full** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：uliftFunctor_full : (uliftFunctor.{v, u}).Full
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.FullyFaithful.full`：full : F.Full where map_surje
ctive
-/
instance uliftFunctor_full : (uliftFunctor.{v, u}).Full :=
  fullyFaithfulULiftFunctor.full
/-
**CategoryTheory.uliftFunctor_faithful** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
`。
形式化陈述：uliftFunctor_faithful : uliftFunctor.{v, u}.Faithful
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.FullyFaithful.faithful`：faithful : F.Faithful whe
re map_injective
-/
instance uliftFunctor_faithful : uliftFunctor.{v, u}.Faithful :=
  fullyFaithfulULiftFunctor.faithful

/-- The functor embedding `Type u` into `Type u` via `ULift` is isomorphic to the identity functor.
-/
/-
**CategoryTheory.uliftFunctorTrivial** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：uliftFunctorTrivial : uliftFunctor.{u, u} ≅ 𝟭 _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor embedding `Type u` into `Type u` via `ULift` is isomorphic to the id
entity functor.
-/
def uliftFunctorTrivial : uliftFunctor.{u, u} ≅ 𝟭 _ :=
  NatIso.ofComponents uliftTrivial

-- TODO We should connect this to a general story about concrete categories
-- whose forgetful functor is representable.
/-- Any term `x` of a type `X` corresponds to a morphism `PUnit ⟶ X`. -/
/-
**CategoryTheory.homOfElement** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：homOfElement {X : Type u} (x : X) : PUnit ⟶ X
参数：x : X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any term `x` of a type `X` corresponds to a morphism `PUnit ⟶ X`.
-/
def homOfElement {X : Type u} (x : X) : PUnit ⟶ X := ofHom fun _ => x
/-
**CategoryTheory.homOfElement_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：homOfElement_eq_iff {X : Type u} (x y : X) : homOfElement x = homOfElement
 y ↔ x = y
参数：x y : X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem homOfElement_eq_iff {X : Type u} (x y : X) : homOfElement x = homOfElement y ↔ x = y :=
  ⟨fun H => ConcreteCategory.congr_hom H PUnit.unit, by simp_all⟩

/-- A morphism in `Type` is a monomorphism if and only if it is injective. -/
@[stacks 003C]
/-
**CategoryTheory.ofHom_mono_iff_injective** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory`。
形式化陈述：ofHom_mono_iff_injective {X Y : Type u} (f : X -> Y) : Mono (ofHom f) ↔ Fu
nction.Injective f
参数：f : X -> Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.homOfElement_eq_iff`：homOfElement_eq_iff {X : Type u} (x 
y : X) : homOfElement x = homOfElement y ↔ x = y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ext`：hom_ext {X Y : C} (f g : X ⟶ Y)
 (w : forall x, f x = g x) : f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Function.Injective.comp_left`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort 
u_3} {g : β → γ}, Function.Injective g → Function.Injective fun x => g ∘ x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x

--- 原说明 ---
A morphism in `Type` is a monomorphism if and only if it is injective.
-/
theorem ofHom_mono_iff_injective {X Y : Type u} (f : X → Y) :
    Mono (ofHom f) ↔ Function.Injective f := by
  constructor
  · intro H x x' h
    rw [← homOfElement_eq_iff] at h ⊢
    exact (cancel_mono (ofHom f)).mp h
  · refine fun H => ⟨fun g g' h => ConcreteCategory.hom_ext _ _ fun x ↦
      congrFun (H.comp_left ?_) x⟩
    ext y
    exact ConcreteCategory.congr_hom h y

/-- A morphism in `Type` is a monomorphism if and only if it is injective. -/
@[stacks 003C]
/-
**CategoryTheory.mono_iff_injective** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：mono_iff_injective {X Y : Type u} (f : X ⟶ Y) : Mono f ↔ Function.Injectiv
e f
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A morphism in `Type` is a monomorphism if and only if it is injective.
-/
theorem mono_iff_injective {X Y : Type u} (f : X ⟶ Y) : Mono f ↔ Function.Injective f := by
  simp [← ofHom_mono_iff_injective]
/-
**CategoryTheory.injective_of_mono** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：injective_of_mono {X Y : Type u} (f : X ⟶ Y) [hf : Mono f] : Function.Inje
ctive f
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.mono_iff_injective`：mono_iff_injective {X Y : Type u} (f 
: X ⟶ Y) : Mono f ↔ Function.Injective f
-/
theorem injective_of_mono {X Y : Type u} (f : X ⟶ Y) [hf : Mono f] : Function.Injective f :=
  (mono_iff_injective f).1 hf

/-- A morphism in `Type _` is an epimorphism if and only if it is surjective. -/
@[stacks 003C]
/-
**CategoryTheory.ofHom_epi_iff_surjective** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory`。
形式化陈述：ofHom_epi_iff_surjective {X Y : Type u} (f : X -> Y) : Epi (ofHom f) ↔ Fun
ction.Surjective f
参数：f : X -> Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.surjective_of_right_cancellable_Prop`：surjective_of_right_cance
llable_Prop (h : forall g₁ g₂ : β -> Prop, g₁ ∘ f = g₂ ∘ f -> g₁ = g₂) : Surject
ive f
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Function.Injective.comp_left`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort 
u_3} {g : β → γ}, Function.Injective g → Function.Injective fun x => g ∘ x
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ext`：hom_ext {X Y : C} (f g : X ⟶ Y)
 (w : forall x, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.ulift_symm_apply`：∀ {α : Type v}, ⇑Equiv.ulift.symm = ULift.up
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.Surjective.injective_comp_right`：∀ {α : Sort u_1} {β : Sort u_2
} {γ : Sort u_3} {f : α → β}, Function.Surjective f → Function.Injective fun g =
> g ∘ f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x

--- 原说明 ---
A morphism in `Type _` is an epimorphism if and only if it is surjective.
-/
theorem ofHom_epi_iff_surjective {X Y : Type u} (f : X → Y) :
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
  · refine fun H => ⟨fun g g' h =>  ConcreteCategory.hom_ext _ _ fun x ↦
      congrFun (H.injective_comp_right ?_) x⟩
    ext y
    exact ConcreteCategory.congr_hom h y

/-- A morphism in `Type` is an epimorphism if and only if it is surjective. -/
@[stacks 003C]
/-
**CategoryTheory.epi_iff_surjective** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：epi_iff_surjective {X Y : Type u} (f : X ⟶ Y) : Epi f ↔ Function.Surjectiv
e f
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A morphism in `Type` is an epimorphism if and only if it is surjective.
-/
theorem epi_iff_surjective {X Y : Type u} (f : X ⟶ Y) : Epi f ↔ Function.Surjective f := by
  simp [← ofHom_epi_iff_surjective]
/-
**CategoryTheory.surjective_of_epi** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：surjective_of_epi {X Y : Type u} (f : X ⟶ Y) [hf : Epi f] : Function.Surje
ctive f
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.epi_iff_surjective`：epi_iff_surjective {X Y : Type u} (f 
: X ⟶ Y) : Epi f ↔ Function.Surjective f
-/
theorem surjective_of_epi {X Y : Type u} (f : X ⟶ Y) [hf : Epi f] : Function.Surjective f :=
  (epi_iff_surjective f).1 hf

section

/-- `ofTypeFunctor m` converts from Lean's `Type`-based `Category` to `CategoryTheory`. This
allows us to use these functors in category theory. -/
@[simps obj map]
/-
**CategoryTheory.ofTypeFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：ofTypeFunctor (m : Type u -> Type v) [_root_.Functor m] [LawfulFunctor m] 
: Type u ⥤ Type v where obj x
参数：m : Type u -> Type v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ofTypeFunctor m` converts from Lean's `Type`-based `Category` to `CategoryTheor
y`. This
allows us to use these functors in category theory.
-/
def ofTypeFunctor (m : Type u → Type v) [_root_.Functor m] [LawfulFunctor m] :
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
/-
**Equiv.toIso** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：toIso (e : X ≃ Y) : X ≅ Y where hom
参数：e : X ≃ Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Any equivalence between types in the same universe gives
a categorical isomorphism between those types.
-/
def toIso (e : X ≃ Y) : X ≅ Y where
  hom := ofHom fun x ↦ e x
  inv := ofHom fun x ↦ e.symm x

@[deprecated (since := "2026-03-20")] alias toIso_hom := toIso_hom_hom_apply
@[deprecated (since := "2026-03-20")] alias toIso_inv := toIso_inv_hom_apply

end Equiv

namespace CategoryTheory.Iso

open CategoryTheory

variable {X Y : Type u}

/-- Any isomorphism between types gives an equivalence. -/
@[simps]
/-
**CategoryTheory.Iso.toEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：toEquiv (i : X ≅ Y) : X ≃ Y where toFun
参数：i : X ≅ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any isomorphism between types gives an equivalence.
-/
def toEquiv (i : X ≅ Y) : X ≃ Y where
  toFun := i.hom
  invFun := i.inv
  left_inv x := by simp
  right_inv y := by simp
/-
**CategoryTheory.Iso.toEquiv_fun** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：toEquiv_fun (i : X ≅ Y) : (i.toEquiv : X -> Y) = i.hom
参数：i : X ≅ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toEquiv_fun (i : X ≅ Y) : (i.toEquiv : X → Y) = i.hom :=
  rfl
/-
**CategoryTheory.Iso.toEquiv_symm_fun** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Iso`。
形式化陈述：toEquiv_symm_fun (i : X ≅ Y) : (i.toEquiv.symm :) = (ConcreteCategory.hom 
i.inv).toFun
参数：i : X ≅ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem toEquiv_symm_fun (i : X ≅ Y) : (i.toEquiv.symm :) = (ConcreteCategory.hom i.inv).toFun :=
  rfl

@[simp]
/-
**CategoryTheory.Iso.toEquiv_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：toEquiv_id (X : Type u) : (Iso.refl X).toEquiv = Equiv.refl X
参数：X : Type u。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toEquiv_id (X : Type u) : (Iso.refl X).toEquiv = Equiv.refl X :=
  rfl

@[simp]
/-
**CategoryTheory.Iso.toEquiv_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Iso`
。
形式化陈述：toEquiv_comp {X Y Z : Type u} (f : X ≅ Y) (g : Y ≅ Z) : (f ≪≫ g).toEquiv =
 f.toEquiv.trans g.toEquiv
参数：f : X ≅ Y；g : Y ≅ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toEquiv_comp {X Y Z : Type u} (f : X ≅ Y) (g : Y ≅ Z) :
    (f ≪≫ g).toEquiv = f.toEquiv.trans g.toEquiv :=
  rfl

end CategoryTheory.Iso

namespace CategoryTheory

/-- A morphism in `Type u` is an isomorphism if and only if it is bijective. -/
/-
**CategoryTheory.isIso_iff_bijective** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：isIso_iff_bijective {X Y : Type u} (f : X ⟶ Y) : IsIso f ↔ Function.Biject
ive f
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom

--- 原说明 ---
A morphism in `Type u` is an isomorphism if and only if it is bijective.
-/
theorem isIso_iff_bijective {X Y : Type u} (f : X ⟶ Y) : IsIso f ↔ Function.Bijective f :=
  Iff.intro (fun _ => (asIso f : X ≅ Y).toEquiv.bijective) fun b =>
    (Equiv.ofBijective f b).toIso.isIso_hom
/-
**CategoryTheory.bijective_iff_isIso_ofHom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory`。
形式化陈述：bijective_iff_isIso_ofHom {X Y : Type u} (f : X -> Y) : Function.Bijective
 f ↔ IsIso (ofHom f)
参数：f : X -> Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
-/
theorem bijective_iff_isIso_ofHom {X Y : Type u} (f : X → Y) :
    Function.Bijective f ↔ IsIso (ofHom f) :=
  Iff.intro (fun b => (Equiv.ofBijective f b).toIso.isIso_hom)
    fun _ => (asIso (ofHom f) : X ≅ Y).toEquiv.bijective
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SplitEpiCategory (Type u) where
  isSplitEpi_of_epi f hf :=
    IsSplitEpi.mk' <|
      { section_ := ofHom <| Function.surjInv <| (epi_iff_surjective f).1 hf
        id := by
          ext x
          exact (Function.rightInverse_surjInv <| (epi_iff_surjective f).1 hf) x }
/-
**CategoryTheory.isSplitEpi_iff_surjective** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory`。
形式化陈述：isSplitEpi_iff_surjective {X Y : Type u} (f : X ⟶ Y) : IsSplitEpi f ↔ Func
tion.Surjective f
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.surjective_of_epi`：surjective_of_epi {X Y : Type u} (f : 
X ⟶ Y) [hf : Epi f] : Function.Surjective f
· 使用定理 `CategoryTheory.IsSplitEpi.epi`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [hf : CategoryTheory.IsSplitEpi f],   C
ategoryTheory.Epi f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.instSplitEpiCategoryType`：CategoryTheory.SplitEpiCategory
 (Type u)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.epi_iff_surjective`：epi_iff_surjective {X Y : Type u} (f 
: X ⟶ Y) : Epi f ↔ Function.Surjective f
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
/-
**equivIsoIso** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：equivIsoIso {X Y : Type u} : (X ≃ Y) ≅ (X ≅ Y) where hom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalences (between types in the same universe) are the same as (isomorphic to
) isomorphisms
of types.
-/
def equivIsoIso {X Y : Type u} : (X ≃ Y) ≅ (X ≅ Y) where
  hom := ofHom fun e ↦ e.toIso
  inv := ofHom fun i ↦ i.toEquiv

/-- Equivalences (between types in the same universe) are the same as (equivalent to) isomorphisms
of types. -/
/-
**equivEquivIso** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：equivEquivIso {X Y : Type u} : X ≃ Y ≃ (X ≅ Y)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalences (between types in the same universe) are the same as (equivalent to
) isomorphisms
of types.
-/
def equivEquivIso {X Y : Type u} : X ≃ Y ≃ (X ≅ Y) :=
  equivIsoIso.toEquiv

@[simp]
/-
**equivEquivIso_hom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：equivEquivIso_hom {X Y : Type u} (e : X ≃ Y) : equivEquivIso e = e.toIso
参数：e : X ≃ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equivEquivIso_hom {X Y : Type u} (e : X ≃ Y) : equivEquivIso e = e.toIso :=
  rfl

@[simp]
/-
**equivEquivIso_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：equivEquivIso_inv {X Y : Type u} (e : X ≅ Y) : equivEquivIso.symm e = e.to
Equiv
参数：e : X ≅ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem equivEquivIso_inv {X Y : Type u} (e : X ≅ Y) : equivEquivIso.symm e = e.toEquiv :=
  rfl
