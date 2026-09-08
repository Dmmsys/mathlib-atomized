/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.FinCategory.Basic
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.Algebra.Category.MonCat.Basic
public import Mathlib.Combinatorics.Quiver.SingleObj
public import Mathlib.Algebra.Group.Units.Equiv

/-!
# Single-object category

Single object category with a given monoid of endomorphisms.
It is defined to facilitate transferring some definitions and lemmas (e.g., conjugacy etc.)
from category theory to monoids and groups.

## Main definitions

Given a type `M` with a monoid structure, `SingleObj M` is `Unit` type with `Category` structure
such that `End (SingleObj M).star` is the monoid `M`.  This can be extended to a functor
`MonCat ⥤ Cat`.

If `M` is a group, then `SingleObj M` is a groupoid.

An element `x : M` can be reinterpreted as an element of `End (SingleObj.star M)` using
`SingleObj.toEnd`.

## Implementation notes

- `categoryStruct.comp` on `End (SingleObj.star M)` is `flip (*)`, not `(*)`. This way
  multiplication on `End` agrees with the multiplication on `M`.

- By default, Lean puts instances into `CategoryTheory` namespace instead of
  `CategoryTheory.SingleObj`, so we give all names explicitly.
-/

@[expose] public section

assert_not_exists MonoidWithZero

universe u v w

namespace CategoryTheory

/-- Abbreviation that allows writing `CategoryTheory.SingleObj` rather than `Quiver.SingleObj`.
-/
/-
**CategoryTheory.SingleObj** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：SingleObj
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Abbreviation that allows writing `CategoryTheory.SingleObj` rather than `Quiver.
SingleObj`.
-/
abbrev SingleObj :=
  Quiver.SingleObj

namespace SingleObj

variable (M G : Type u)

/-- One and `flip (*)` become `id` and `comp` for morphisms of the single object category. -/
/-
**CategoryTheory.SingleObj.categoryStruct** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.SingleObj`。
形式化陈述：categoryStruct [One M] [Mul M] : CategoryStruct (SingleObj M) where Hom _ 
_
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
One and `flip (*)` become `id` and `comp` for morphisms of the single object cat
egory.
-/
instance categoryStruct [One M] [Mul M] : CategoryStruct (SingleObj M) where
  Hom _ _ := M
  comp x y := y * x
  id _ := 1

variable [Monoid M] [Group G]

/-- Monoid laws become category laws for the single object category. -/
/-
**CategoryTheory.SingleObj.category** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Si
ngleObj`。
形式化陈述：category : Category (SingleObj M) where comp_id
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Monoid laws become category laws for the single object category.
-/
instance category : Category (SingleObj M) where
  comp_id := one_mul
  id_comp := mul_one
  assoc x y z := (mul_assoc z y x).symm
/-
**CategoryTheory.SingleObj.id_as_one** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.S
ingleObj`。
形式化陈述：id_as_one (x : SingleObj M) : 𝟙 x = 1
参数：x : SingleObj M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_as_one (x : SingleObj M) : 𝟙 x = 1 :=
  rfl
/-
**CategoryTheory.SingleObj.comp_as_mul** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.SingleObj`。
形式化陈述：comp_as_mul {x y z : SingleObj M} (f : x ⟶ y) (g : y ⟶ z) : f ≫ g = g * f
参数：f : x ⟶ y；g : y ⟶ z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_as_mul {x y z : SingleObj M} (f : x ⟶ y) (g : y ⟶ z) : f ≫ g = g * f :=
  rfl

/-- If `M` is finite and in universe zero, then `SingleObj M` is a `FinCategory`. -/
/-
**CategoryTheory.SingleObj.finCategoryOfFintype** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.SingleObj`。
形式化陈述：(M : Type) → [Fintype M] → [inst : Monoid M] → CategoryTheory.FinCategory 
(CategoryTheory.SingleObj M)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `M` is finite and in universe zero, then `SingleObj M` is a `FinCategory`.
-/
instance finCategoryOfFintype (M : Type) [Fintype M] [Monoid M] : FinCategory (SingleObj M) where

/-- Groupoid structure on `SingleObj M`. -/
@[stacks 0019]
/-
**CategoryTheory.SingleObj.groupoid** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Si
ngleObj`。
形式化陈述：groupoid : Groupoid (SingleObj G) where inv x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Groupoid structure on `SingleObj M`.
-/
instance groupoid : Groupoid (SingleObj G) where
  inv x := x⁻¹
  inv_comp := mul_inv_cancel
  comp_inv := inv_mul_cancel
/-
**CategoryTheory.SingleObj.inv_as_inv** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
SingleObj`。
形式化陈述：inv_as_inv {x y : SingleObj G} (f : x ⟶ y) : inv f = f⁻¹
参数：f : x ⟶ y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsIso.inv_eq_of_hom_inv_id`：inv_eq_of_hom_inv_id {f : X ⟶
 Y} [IsIso f] {g : Y ⟶ X} (hom_inv_id : f ≫ g = 𝟙 X) : inv f = g
· 使用定理 `CategoryTheory.IsGroupoid.all_isIso`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.IsGroupoid C] {X Y : C} (f : X ⟶ Y)
,   CategoryTheory.IsIso …
· 使用定理 `CategoryTheory.instIsGroupoid`：∀ {C : Type u} [inst : CategoryTheory.Gro
upoid C], CategoryTheory.IsGroupoid C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.SingleObj.comp_as_mul`：comp_as_mul {x y z : SingleObj M} 
(f : x ⟶ y) (g : y ⟶ z) : f ≫ g = g * f
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `CategoryTheory.SingleObj.id_as_one`：id_as_one (x : SingleObj M) : 𝟙 x = 
1
-/
theorem inv_as_inv {x y : SingleObj G} (f : x ⟶ y) : inv f = f⁻¹ := by
  apply IsIso.inv_eq_of_hom_inv_id
  rw [comp_as_mul, inv_mul_cancel, id_as_one]

/-- Abbreviation that allows writing `CategoryTheory.SingleObj.star` rather than
`Quiver.SingleObj.star`.
-/
/-
**CategoryTheory.SingleObj.star** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Sing
leObj`。
形式化陈述：star : SingleObj M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Abbreviation that allows writing `CategoryTheory.SingleObj.star` rather than
`Quiver.SingleObj.star`.
-/
abbrev star : SingleObj M :=
  Quiver.SingleObj.star M

/-- The endomorphisms monoid of the only object in `SingleObj M` is equivalent to the original
monoid `M`. -/
/-
**CategoryTheory.SingleObj.toEnd** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Singl
eObj`。
形式化陈述：toEnd : M ≃* End (SingleObj.star M)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
The endomorphisms monoid of the only object in `SingleObj M` is equivalent to th
e original
monoid `M`.
-/
def toEnd : M ≃* End (SingleObj.star M) :=
  { Equiv.refl M with map_mul' := fun _ _ => rfl }
/-
**CategoryTheory.SingleObj.toEnd_def** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.S
ingleObj`。
形式化陈述：toEnd_def (x : M) : toEnd M x = x
参数：x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toEnd_def (x : M) : toEnd M x = x :=
  rfl

variable (N : Type v) [Monoid N]

/-- There is a 1-1 correspondence between monoid homomorphisms `M → N` and functors between the
corresponding single-object categories. It means that `SingleObj` is a fully faithful functor. -/
@[stacks 001F "We do not characterize when the functor is full or faithful."]
/-
**CategoryTheory.SingleObj.mapHom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sing
leObj`。
形式化陈述：mapHom : (M ->* N) ≃ SingleObj M ⥤ SingleObj N where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
There is a 1-1 correspondence between monoid homomorphisms `M → N` and functors 
between the
corresponding single-object categories. It means that `SingleObj` is a fully fai
thful functor.
-/
def mapHom : (M →* N) ≃ SingleObj M ⥤ SingleObj N where
  toFun f :=
    { obj := id
      map := ⇑f
      map_id := fun _ => f.map_one
      map_comp := fun x y => f.map_mul y x }
  invFun f :=
    { toFun := fun x => f.map ((toEnd M) x)
      map_one' := f.map_id _
      map_mul' := fun x y => f.map_comp y x }
  left_inv := by cat_disch
  right_inv := by cat_disch
/-
**CategoryTheory.SingleObj.mapHom_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.S
ingleObj`。
形式化陈述：mapHom_id : mapHom M M (MonoidHom.id M) = 𝟭 _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapHom_id : mapHom M M (MonoidHom.id M) = 𝟭 _ :=
  rfl

variable {M N G}
/-
**CategoryTheory.SingleObj.mapHom_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.SingleObj`。
形式化陈述：mapHom_comp (f : M ->* N) {P : Type w} [Monoid P] (g : N ->* P) : mapHom M
 P (g.comp f) = mapHom M N f ⋙ mapHom N P g
参数：f : M ->* N；g : N ->* P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapHom_comp (f : M →* N) {P : Type w} [Monoid P] (g : N →* P) :
    mapHom M P (g.comp f) = mapHom M N f ⋙ mapHom N P g :=
  rfl

variable {C : Type v} [Category.{w} C]

set_option backward.isDefEq.respectTransparency.types false in
/-- Given a function `f : C → G` from a category to a group, we get a functor
`C ⥤ G` sending any morphism `x ⟶ y` to `f y * (f x)⁻¹`. -/
@[simps]
/-
**CategoryTheory.SingleObj.differenceFunctor** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.SingleObj`。
形式化陈述：differenceFunctor (f : C -> G) : C ⥤ SingleObj G where obj _
参数：f : C -> G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a function `f : C → G` from a category to a group, we get a functor
`C ⥤ G` sending any morphism `x ⟶ y` to `f y * (f x)⁻¹`.
-/
def differenceFunctor (f : C → G) : C ⥤ SingleObj G where
  obj _ := ()
  map {x y} _ := f y * (f x)⁻¹
  map_id := by
    intro
    simp only [SingleObj.id_as_one, mul_inv_cancel]
  map_comp := by
    intros
    rw [SingleObj.comp_as_mul, ← mul_assoc, mul_left_inj, mul_assoc, inv_mul_cancel, mul_one]

/-- A monoid homomorphism `f: M → End X` into the endomorphisms of an object `X` of a category `C`
induces a functor `SingleObj M ⥤ C`. -/
@[simps]
/-
**CategoryTheory.SingleObj.functor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sin
gleObj`。
形式化陈述：functor {X : C} (f : M ->* End X) : SingleObj M ⥤ C where obj _
参数：f : M ->* End X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A monoid homomorphism `f: M → End X` into the endomorphisms of an object `X` of 
a category `C`
induces a functor `SingleObj M ⥤ C`.
-/
def functor {X : C} (f : M →* End X) : SingleObj M ⥤ C where
  obj _ := X
  map a := f a
  map_id _ := map_one f
  map_comp a b := map_mul f b a

/-- Construct a natural transformation between functors `SingleObj M ⥤ C` by
giving a compatible morphism `SingleObj.star M`. -/
@[simps]
/-
**CategoryTheory.SingleObj.natTrans** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Si
ngleObj`。
形式化陈述：natTrans {F G : SingleObj M ⥤ C} (u : F.obj (SingleObj.star M) ⟶ G.obj (Si
ngleObj.star M)) (h : forall a : M, F.map a ≫ u = u ≫ G.map a) : F ⟶ G where app
 _
参数：u : F.obj (SingleObj.star M) ⟶ G.obj (SingleObj.star M)；h : forall a : M, F.m
ap a ≫ u = u ≫ G.map a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a natural transformation between functors `SingleObj M ⥤ C` by
giving a compatible morphism `SingleObj.star M`.
-/
def natTrans {F G : SingleObj M ⥤ C} (u : F.obj (SingleObj.star M) ⟶ G.obj (SingleObj.star M))
    (h : ∀ a : M, F.map a ≫ u = u ≫ G.map a) : F ⟶ G where
  app _ := u
  naturality _ _ a := h a

end SingleObj

end CategoryTheory

open CategoryTheory

namespace MonoidHom

variable {M : Type u} {N : Type v} [Monoid M] [Monoid N]

/-- Reinterpret a monoid homomorphism `f : M → N` as a functor `(single_obj M) ⥤ (single_obj N)`.
See also `CategoryTheory.SingleObj.mapHom` for an equivalence between these types. -/
/-
**MonoidHom.toFunctor** 是 Mathlib 中的一个缩写定义，位于命名空间 `MonoidHom`。
形式化陈述：toFunctor (f : M ->* N) : SingleObj M ⥤ SingleObj N
参数：f : M ->* N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret a monoid homomorphism `f : M → N` as a functor `(single_obj M) ⥤ (si
ngle_obj N)`.
See also `CategoryTheory.SingleObj.mapHom` for an equivalence between these type
s.
-/
abbrev toFunctor (f : M →* N) : SingleObj M ⥤ SingleObj N :=
  SingleObj.mapHom M N f

@[simp]
/-
**MonoidHom.comp_toFunctor** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：comp_toFunctor (f : M ->* N) {P : Type w} [Monoid P] (g : N ->* P) : (g.co
mp f).toFunctor = f.toFunctor ⋙ g.toFunctor
参数：f : M ->* N；g : N ->* P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_toFunctor (f : M →* N) {P : Type w} [Monoid P] (g : N →* P) :
    (g.comp f).toFunctor = f.toFunctor ⋙ g.toFunctor :=
  rfl

variable (M)

@[simp]
/-
**MonoidHom.id_toFunctor** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：id_toFunctor : (id M).toFunctor = 𝟭 _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_toFunctor : (id M).toFunctor = 𝟭 _ :=
  rfl

end MonoidHom

namespace MulEquiv

variable {M : Type u} {N : Type v} [Monoid M] [Monoid N]

set_option backward.isDefEq.respectTransparency false in
/-- Reinterpret a monoid isomorphism `f : M ≃* N` as an equivalence `SingleObj M ≌ SingleObj N`. -/
@[simps!]
/-
**MulEquiv.toSingleObjEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MulEquiv`。
形式化陈述：toSingleObjEquiv (e : M ≃* N) : SingleObj M ≌ SingleObj N where functor
参数：e : M ≃* N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret a monoid isomorphism `f : M ≃* N` as an equivalence `SingleObj M ≌ S
ingleObj N`.
-/
def toSingleObjEquiv (e : M ≃* N) : SingleObj M ≌ SingleObj N where
  functor := e.toMonoidHom.toFunctor
  inverse := e.symm.toMonoidHom.toFunctor
  unitIso := eqToIso (by
    rw [← MonoidHom.comp_toFunctor, ← MonoidHom.id_toFunctor]
    congr 1
    simp)
  counitIso := eqToIso (by
    rw [← MonoidHom.comp_toFunctor, ← MonoidHom.id_toFunctor]
    congr 1
    simp)

end MulEquiv

namespace Units

variable (M : Type u) [Monoid M]

/-- The units in a monoid are (multiplicatively) equivalent to
the automorphisms of `star` when we think of the monoid as a single-object category. -/
/-
**Units.toAut** 是 Mathlib 中的一个定义，位于命名空间 `Units`。
形式化陈述：toAut : Mˣ ≃* Aut (SingleObj.star M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The units in a monoid are (multiplicatively) equivalent to
the automorphisms of `star` when we think of the monoid as a single-object categ
ory.
-/
def toAut : Mˣ ≃* Aut (SingleObj.star M) :=
  MulEquiv.trans (Units.mapEquiv (SingleObj.toEnd M))
    (Aut.unitsEndEquivAut (SingleObj.star M))

@[simp]
/-
**Units.toAut_hom** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：toAut_hom (x : Mˣ) : (toAut M x).hom = SingleObj.toEnd M x
参数：x : Mˣ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAut_hom (x : Mˣ) : (toAut M x).hom = SingleObj.toEnd M x :=
  rfl

@[simp]
/-
**Units.toAut_inv** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：toAut_inv (x : Mˣ) : (toAut M x).inv = SingleObj.toEnd M (x⁻¹ : Mˣ)
参数：x : Mˣ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAut_inv (x : Mˣ) : (toAut M x).inv = SingleObj.toEnd M (x⁻¹ : Mˣ) :=
  rfl

end Units

namespace MonCat

open CategoryTheory

/-- The fully faithful functor from `MonCat` to `Cat`. -/
/-
**MonCat.toCat** 是 Mathlib 中的一个定义，位于命名空间 `MonCat`。
形式化陈述：toCat : MonCat ⥤ Cat where obj x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fully faithful functor from `MonCat` to `Cat`.
-/
def toCat : MonCat ⥤ Cat where
  obj x := Cat.of (SingleObj x)
  map {x y} f := (SingleObj.mapHom x y f.hom).toCatHom
/-
**MonCat.toCat_full** 是 Mathlib 中的一个实例，位于命名空间 `MonCat`。
形式化陈述：toCat_full : toCat.Full where map_surjective y
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `CategoryTheory.Cat.Hom.ext`：∀ {C D : CategoryTheory.Cat} {x y : C.Hom D}
, x.toFunctor = y.toFunctor → x = y
-/
instance toCat_full : toCat.Full where
  map_surjective y :=
    let ⟨x, h⟩ := (SingleObj.mapHom _ _).surjective y.toFunctor
    ⟨ofHom x, Cat.Hom.ext h⟩

set_option backward.isDefEq.respectTransparency false in
/-
**MonCat.toCat_faithful** 是 Mathlib 中的一个实例，位于命名空间 `MonCat`。
形式化陈述：toCat_faithful : toCat.Faithful where map_injective h
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `MonCat.hom_ext`：hom_ext {M N : MonCat} {f g : M ⟶ N} (hf : f.hom = g.hom
) : f = g
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
instance toCat_faithful : toCat.Faithful where
  map_injective h := MonCat.hom_ext <| by simpa [toCat] using congr(($h).toFunctor)

end MonCat

