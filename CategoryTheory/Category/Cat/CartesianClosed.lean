/-
Copyright (c) 2025 Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emily Riehl
-/
module

public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Cat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Cartesian closed structure on `Cat`

The category of small categories is Cartesian closed, with the exponential at a category `C`
defined by the functor category mapping out of `C`.

Adjoint transposition is defined by currying and uncurrying.

TODO: It would be useful to investigate and formalize further compatibilities along the
lines of `Cat.ihom_obj` and `Cat.ihom_map`, relating currying of functors with currying in
monoidal closed categories and precomposition with left whiskering. These may not be
definitional equalities but may have to be phrased using `eqToIso`.

-/

@[expose] public section

universe v u v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

open CategoryTheory.Functor Cat

namespace Cat

variable (C : Type u) [Category.{v} C]

/-- A category `C` induces a functor from `Cat` to itself defined
by forming the category of functors out of `C`. -/
@[simps]
/-
**CategoryTheory.Cat.exp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Cat`。
形式化陈述：exp : Cat ⥤ Cat where obj D
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category `C` induces a functor from `Cat` to itself defined
by forming the category of functors out of `C`.
-/
def exp : Cat ⥤ Cat where
  obj D := Cat.of (C ⥤ D)
  map F := ((whiskeringRight _ _ _).obj F.toFunctor).toCatHom

end Cat

section

variable {B : Type u₁} [Category.{v₁} B] {C : Type u₂} [Category.{v₂} C] {D : Type u₃}
  [Category.{v₃} D] {E : Type u₄} [Category.{v₄} E]

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism of categories of bifunctors given by currying. -/
@[simps!]
/-
**CategoryTheory.curryingIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：curryingIso : Cat.of (C ⥤ D ⥤ E) ≅ Cat.of (C × D ⥤ E)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.curry_obj_uncurry_obj`：curry_obj_uncurry_obj (F :
 B ⥤ C ⥤ D) : curry.obj (uncurry.obj F) = F
· 使用引理 `CategoryTheory.Functor.uncurry_obj_curry_obj`：uncurry_obj_curry_obj (F :
 B × C ⥤ D) : uncurry.obj (curry.obj F) = F

--- 原说明 ---
The isomorphism of categories of bifunctors given by currying.
-/
def curryingIso : Cat.of (C ⥤ D ⥤ E) ≅ Cat.of (C × D ⥤ E) :=
  isoOfEquiv currying Functor.curry_obj_uncurry_obj Functor.uncurry_obj_curry_obj

/-- The isomorphism of categories of bifunctors given by flipping the arguments. -/
@[simps!]
/-
**CategoryTheory.flippingIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：flippingIso : Cat.of (C ⥤ D ⥤ E) ≅ Cat.of (D ⥤ C ⥤ E)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.flip_flip`：flip_flip (F : B ⥤ C ⥤ D) : F.flip.fli
p = F

--- 原说明 ---
The isomorphism of categories of bifunctors given by flipping the arguments.
-/
def flippingIso : Cat.of (C ⥤ D ⥤ E) ≅ Cat.of (D ⥤ C ⥤ E) :=
  isoOfEquiv flipping Functor.flip_flip Functor.flip_flip

end

namespace Cat

section
variable (C : Type u) [Category.{u} C]

/-
**CategoryTheory.Cat.closed** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Cat`。
形式化陈述：closed : Closed (Cat.of C) where rightAdj
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
instance closed : Closed (Cat.of C) where
  rightAdj := exp C
  adj := Adjunction.mkOfHomEquiv
    { homEquiv _ _ := Equiv.trans (Cat.Hom.equivFunctor _ _) (curryingFlipEquiv.symm.trans
        (Functor.equivCatHom _ _))
      homEquiv_naturality_left_symm _ _ := rfl
      homEquiv_naturality_right _ _ := rfl }
/-
**CategoryTheory.Cat.cartesianClosed** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.C
at`。
形式化陈述：cartesianClosed : MonoidalClosed Cat.{u, u} where closed C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance cartesianClosed : MonoidalClosed Cat.{u, u} where
  closed C := closed C

@[simp]
/-
**CategoryTheory.Cat.ihom_obj** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Cat`。
形式化陈述：ihom_obj (D : Type u) [Category.{u} D] : (ihom (Cat.of C)).obj (Cat.of D) 
= Cat.of (C ⥤ D)
参数：D : Type u。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ihom_obj (D : Type u) [Category.{u} D] :
    (ihom (Cat.of C)).obj (Cat.of D) = Cat.of (C ⥤ D) := rfl

@[simp]
/-
**CategoryTheory.Cat.ihom_map** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Cat`。
形式化陈述：ihom_map {D E : Type u} [Category.{u} D] [Category.{u} E] (F : D ⥤ E) : (i
hom (Cat.of C)).map F.toCatHom = ((whiskeringRight _ _ _).obj F).toCatHom
参数：F : D ⥤ E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ihom_map {D E : Type u} [Category.{u} D] [Category.{u} E] (F : D ⥤ E) :
    (ihom (Cat.of C)).map F.toCatHom = ((whiskeringRight _ _ _).obj F).toCatHom := rfl

end

end Cat

end CategoryTheory

