/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Category of groupoids

This file contains the definition of the category `Grpd` of all groupoids.
In this category objects are groupoids and morphisms are functors
between these groupoids.

We also provide two “forgetting” functors: `objects : Grpd ⥤ Type`
and `forgetToCat : Grpd ⥤ Cat`.

## Implementation notes

Though `Grpd` is not a concrete category, we use `Bundled` to define
its carrier type.
-/

@[expose] public section

assert_not_exists MonoidWithZero

universe v u

namespace CategoryTheory

-- intended to be used with explicit universe parameters
set_option linter.checkUnivs false in
/-- Category of groupoids -/
/-
**CategoryTheory.Grpd** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：Grpd
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Category of groupoids
-/
def Grpd :=
  Bundled Groupoid.{v, u}

namespace Grpd

/-
**CategoryTheory.Grpd.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Grpd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited Grpd :=
  ⟨Bundled.of (SingleObj PUnit)⟩
/-
**CategoryTheory.Grpd.str'** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Grpd`。
形式化陈述：str' (C : Grpd.{v, u}) : Groupoid.{v, u} C.α
参数：C : Grpd.{v, u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance str' (C : Grpd.{v, u}) : Groupoid.{v, u} C.α :=
  C.str
/-
**CategoryTheory.Grpd.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Grpd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort Grpd Type* :=
  Bundled.coeSort

/-- Construct a bundled `Grpd` from the underlying type and the typeclass `Groupoid`. -/
/-
**CategoryTheory.Grpd.of** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Grpd`。
形式化陈述：of (C : Type u) [Groupoid.{v} C] : Grpd.{v, u}
参数：C : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a bundled `Grpd` from the underlying type and the typeclass `Groupoid`
.
-/
def of (C : Type u) [Groupoid.{v} C] : Grpd.{v, u} :=
  Bundled.of C

@[simp]
/-
**CategoryTheory.Grpd.coe_of** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Grpd`。
形式化陈述：coe_of (C : Type u) [Groupoid C] : (of C : Type u) = C
参数：C : Type u。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_of (C : Type u) [Groupoid C] : (of C : Type u) = C :=
  rfl

/-- Category structure on `Grpd` -/
/-
**CategoryTheory.Grpd.category** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Grpd`。
形式化陈述：category : LargeCategory.{max v u} Grpd.{v, u} where Hom C D
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Category structure on `Grpd`
-/
instance category : LargeCategory.{max v u} Grpd.{v, u} where
  Hom C D := C ⥤ D
  id C := 𝟭 C
  comp F G := F ⋙ G
  id_comp _ := rfl
  comp_id _ := rfl
  assoc := by intros; rfl

/-- Functor that gets the set of objects of a groupoid. It is not
called `forget`, because it is not a faithful functor. -/
/-
**CategoryTheory.Grpd.objects** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Grpd`。
形式化陈述：objects : Grpd.{v, u} ⥤ Type u where obj C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Functor that gets the set of objects of a groupoid. It is not
called `forget`, because it is not a faithful functor.
-/
def objects : Grpd.{v, u} ⥤ Type u where
  obj C := Bundled.α C
  map F := ↾F.obj

/-- Forgetting functor to `Cat` -/
/-
**CategoryTheory.Grpd.forgetToCat** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Grpd
`。
形式化陈述：forgetToCat : Grpd.{v, u} ⥤ Cat.{v, u} where obj C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Forgetting functor to `Cat`
-/
def forgetToCat : Grpd.{v, u} ⥤ Cat.{v, u} where
  obj C := Cat.of C
  map := Functor.toCatHom
/-
**CategoryTheory.Grpd.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Grpd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : Grpd) : Groupoid (Grpd.forgetToCat.obj X) := inferInstanceAs (Groupoid X)
/-
**CategoryTheory.Grpd.forgetToCat_full** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.Grpd`。
形式化陈述：forgetToCat_full : forgetToCat.Full where map_surjective f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance forgetToCat_full : forgetToCat.Full where map_surjective f := ⟨f.toFunctor, rfl⟩
/-
**CategoryTheory.Grpd.forgetToCat_faithful** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTh
eory.Grpd`。
形式化陈述：forgetToCat_faithful : forgetToCat.Faithful where map_injective
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
instance forgetToCat_faithful : forgetToCat.Faithful where
  map_injective := congrArg (Cat.Hom.toFunctor)

/-- Convert arrows in the category of groupoids to functors,
which sometimes helps in applying simp lemmas -/
/-
**CategoryTheory.Grpd.comp_eq_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Grp
d`。
形式化陈述：comp_eq_comp {C D E : Grpd.{v, u}} (f : C ⟶ D) (g : D ⟶ E) : f ≫ g = f ⋙ g
参数：f : C ⟶ D；g : D ⟶ E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convert arrows in the category of groupoids to functors,
which sometimes helps in applying simp lemmas
-/
theorem comp_eq_comp {C D E : Grpd.{v, u}} (f : C ⟶ D) (g : D ⟶ E) : f ≫ g = f ⋙ g :=
  rfl

/-- Converts identity in the category of groupoids to the functor identity -/
/-
**CategoryTheory.Grpd.id_eq_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Grpd`。
形式化陈述：id_eq_id {C : Grpd.{v, u}} : 𝟙 C = 𝟭 C
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Converts identity in the category of groupoids to the functor identity
-/
theorem id_eq_id {C : Grpd.{v, u}} : 𝟙 C = 𝟭 C :=
  rfl

section Products

/-- Construct the product over an indexed family of groupoids, as a fan. -/
/-
**CategoryTheory.Grpd.piLimitFan** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Grpd`
。
形式化陈述：piLimitFan ⦃J : Type u⦄ (F : J -> Grpd.{u, u}) : Limits.Fan F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct the product over an indexed family of groupoids, as a fan.
-/
def piLimitFan ⦃J : Type u⦄ (F : J → Grpd.{u, u}) : Limits.Fan F :=
  Limits.Fan.mk (@of (∀ j : J, F j) _) fun j => CategoryTheory.Pi.eval _ j

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The product fan over an indexed family of groupoids, is a limit cone. -/
/-
**CategoryTheory.Grpd.piLimitFanIsLimit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Grpd`。
形式化陈述：piLimitFanIsLimit ⦃J : Type u⦄ (F : J -> Grpd.{u, u}) : Limits.IsLimit (pi
LimitFan F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product fan over an indexed family of groupoids, is a limit cone.
-/
def piLimitFanIsLimit ⦃J : Type u⦄ (F : J → Grpd.{u, u}) : Limits.IsLimit (piLimitFan F) :=
  Limits.Fan.IsLimit.mk (piLimitFan F) (fun s => Functor.pi' fun j => s.proj j)
    (by
      intros
      dsimp only [piLimitFan]
      simp [comp_eq_comp])
    (by
      intro s m w
      apply Functor.pi_ext
      intro j; specialize w j
      simpa)
/-
**CategoryTheory.Grpd.has_pi** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Grpd`。
形式化陈述：has_pi : Limits.HasProducts.{u} Grpd.{u, u}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasProducts_of_limit_fans`：hasProducts_of_limit_fa
ns (lf : forall {J : Type w} (f : J -> C), Fan f) (lf_isLimit : forall {J : Type
 w} (f : J -> C), IsLimit (lf f)) : H…
-/
instance has_pi : Limits.HasProducts.{u} Grpd.{u, u} :=
  Limits.hasProducts_of_limit_fans (by apply piLimitFan) (by apply piLimitFanIsLimit)

/-- The product of a family of groupoids is isomorphic
to the product object in the category of Groupoids -/
/-
**CategoryTheory.Grpd.piIsoPi** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Grpd`。
形式化陈述：piIsoPi (J : Type u) (f : J -> Grpd.{u, u}) : @of (forall j, f j) _ ≅ ∏ᶜ f
参数：J : Type u；f : J -> Grpd.{u, u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of a family of groupoids is isomorphic
to the product object in the category of Groupoids
-/
noncomputable def piIsoPi (J : Type u) (f : J → Grpd.{u, u}) : @of (∀ j, f j) _ ≅ ∏ᶜ f :=
  Limits.IsLimit.conePointUniqueUpToIso (piLimitFanIsLimit f)
    (Limits.limit.isLimit (Discrete.functor f))

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Grpd.piIsoPi_hom_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Grp
d`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem piIsoPi_hom_π (J : Type u) (f : J → Grpd.{u, u}) (j : J) :
    (piIsoPi J f).hom ≫ Limits.Pi.π f j = CategoryTheory.Pi.eval _ j := by
  simp [piIsoPi]
  rfl

end Products

end Grpd

end CategoryTheory

