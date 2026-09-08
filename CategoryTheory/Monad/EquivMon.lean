/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
module

public import Mathlib.CategoryTheory.Monad.Basic
public import Mathlib.CategoryTheory.Monoidal.End
public import Mathlib.CategoryTheory.Monoidal.Mon

/-!

# The equivalence between `Monad C` and `Mon (C ⥤ C)`.

A monad "is just" a monoid in the category of endofunctors.

## Definitions/Theorems

1. `toMon` associates a monoid object in `C ⥤ C` to any monad on `C`.
2. `monadToMon` is the functorial version of `toMon`.
3. `ofMon` associates a monad on `C` to any monoid object in `C ⥤ C`.
4. `monadMonEquiv` is the equivalence between `Monad C` and `Mon (C ⥤ C)`.

-/

@[expose] public section


namespace CategoryTheory

open Category MonObj

universe v u -- morphism levels before object levels. See note [category_theory universes].

variable {C : Type u} [Category.{v} C]

namespace Monad

attribute [local instance] endofunctorMonoidalCategory

@[simps]
/-
**CategoryTheory.Monad.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Monad`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (M : Monad C) : MonObj (M : C ⥤ C) where
  one := M.η
  mul := M.μ
  mul_assoc := by ext; simp [M.assoc]

/-- To every `Monad C` we associated a monoid object in `C ⥤ C`. -/
@[simps]
/-
**CategoryTheory.Monad.toMon** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Monad`。
形式化陈述：toMon (M : Monad C) : Mon (C ⥤ C) where X
参数：M : Monad C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To every `Monad C` we associated a monoid object in `C ⥤ C`.
-/
def toMon (M : Monad C) : Mon (C ⥤ C) where
  X := (M : C ⥤ C)

set_option backward.isDefEq.respectTransparency false in
variable (C) in
/-- Passing from `Monad C` to `Mon (C ⥤ C)` is functorial. -/
@[simps]
/-
**CategoryTheory.Monad.monadToMon** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Mona
d`。
形式化陈述：monadToMon : Monad C ⥤ Mon (C ⥤ C) where obj
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Passing from `Monad C` to `Mon (C ⥤ C)` is functorial.
-/
def monadToMon : Monad C ⥤ Mon (C ⥤ C) where
  obj := toMon
  map f := .mk' f.toNatTrans

/-- To every monoid object in `C ⥤ C` we associate a `Monad C`. -/
@[simps «η» «μ»]
/-
**CategoryTheory.Monad.ofMon** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Monad`。
形式化陈述：ofMon (M : Mon (C ⥤ C)) : Monad C where toFunctor
参数：M : Mon (C ⥤ C)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To every monoid object in `C ⥤ C` we associate a `Monad C`.
-/
def ofMon (M : Mon (C ⥤ C)) : Monad C where
  toFunctor := M.X
  «η» := η[M.X]
  «μ» := μ[M.X]
  left_unit := fun X => by
    simpa [-MonObj.mul_one] using! congrArg (fun t ↦ t.app X) (mul_one M.X)
  right_unit := fun X => by
    simpa [-MonObj.one_mul] using! congrArg (fun t ↦ t.app X) (one_mul M.X)
  assoc := fun X => by
    simpa [-MonObj.mul_assoc] using! congrArg (fun t ↦ t.app X) (mul_assoc M.X)

-- Porting note: `@[simps]` fails to generate `ofMon_obj`:
/-
**CategoryTheory.Monad.ofMon_obj** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Monad
`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (M : CategoryTheo
ry.Mon (CategoryTheory.Functor C C)) (X : C),   (CategoryTheory.Monad.ofMon M).o
bj X = M.X.obj X
参数：M : CategoryTheory.Mon (CategoryTheory.Functor C C)；X : C；CategoryTheory.Mona
d.ofMon M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofMon_obj (M : Mon (C ⥤ C)) (X : C) : (ofMon M).obj X = M.X.obj X := rfl

variable (C)

set_option backward.isDefEq.respectTransparency false in
/-- Passing from `Mon (C ⥤ C)` to `Monad C` is functorial. -/
@[simps]
/-
**CategoryTheory.Monad.monToMonad** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Mona
d`。
形式化陈述：monToMonad : Mon (C ⥤ C) ⥤ Monad C where obj
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Passing from `Mon (C ⥤ C)` to `Monad C` is functorial.
-/
def monToMonad : Mon (C ⥤ C) ⥤ Monad C where
  obj := ofMon
  map {X Y} f :=
    { f.hom with
      app_η X := by
        simpa [-IsMonHom.one_hom] using congrArg (fun t ↦ t.app X) (IsMonHom.one_hom f.hom)
      app_μ Z := by
        simpa [-IsMonHom.mul_hom] using congrArg (fun t ↦ t.app Z) (IsMonHom.mul_hom f.hom) }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Oh, monads are just monoids in the category of endofunctors (equivalence of categories). -/
@[simps]
/-
**CategoryTheory.Monad.monadMonEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.M
onad`。
形式化陈述：monadMonEquiv : Monad C ≌ Mon (C ⥤ C) where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Oh, monads are just monoids in the category of endofunctors (equivalence of cate
gories).
-/
def monadMonEquiv : Monad C ≌ Mon (C ⥤ C) where
  functor := monadToMon _
  inverse := monToMonad _
  unitIso :=
  { hom := { app := fun _ => { app := fun _ => 𝟙 _ } }
    inv := { app := fun _ => { app := fun _ => 𝟙 _ } } }
  counitIso :=
  { hom := { app := fun _ => { hom := 𝟙 _ } }
    inv := { app := fun _ => { hom := 𝟙 _ } } }

-- Sanity check
/-
**CategoryTheory.Monad.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Monad`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (A : Monad C) {X : C} : ((monadMonEquiv C).unitIso.app A).hom.app X = 𝟙 _ :=
  rfl

end Monad

end CategoryTheory

