/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
public import Mathlib.CategoryTheory.PUnit
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

/-!
# A Cartesian closed category with zero object is trivial

A Cartesian closed category with zero object is trivial: it is equivalent to the category with one
object and one morphism.

## References

* https://mathoverflow.net/a/136480

-/

@[expose] public section


universe w v u

noncomputable section

namespace CategoryTheory

open Category Limits MonoidalCategory

variable {C : Type u} [Category.{v} C]
variable [CartesianMonoidalCategory C] [MonoidalClosed C]

open scoped CartesianClosed

/-- If a Cartesian closed category has an initial object which is isomorphic to the terminal object,
then each homset has exactly one element.
-/
@[instance_reducible]
/-
**CategoryTheory.uniqueHomsetOfInitialIsoUnit** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory`。
形式化陈述：uniqueHomsetOfInitialIsoUnit [HasInitial C] (i : ⊥_ C ≅ 𝟙_ C) (X Y : C) : 
Unique (X ⟶ Y)
参数：i : ⊥_ C ≅ 𝟙_ C；X Y : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a Cartesian closed category has an initial object which is isomorphic to the 
terminal object,
then each homset has exactly one element.
-/
def uniqueHomsetOfInitialIsoUnit [HasInitial C] (i : ⊥_ C ≅ 𝟙_ C) (X Y : C) : Unique (X ⟶ Y) :=
  Equiv.unique <|
    calc
      (X ⟶ Y) ≃ (X ⊗ 𝟙_ C ⟶ Y) := Iso.homCongr (rightUnitor _).symm (Iso.refl _)
      _ ≃ (X ⊗ ⊥_ C ⟶ Y) := (Iso.homCongr ((Iso.refl _) ⊗ᵢ i.symm) (Iso.refl _))
      _ ≃ (⊥_ C ⟶ Y ^^ X) := (ihom.adjunction _).homEquiv _ _

open scoped ZeroObject

/-- If a Cartesian closed category has a zero object, each homset has exactly one element. -/
@[instance_reducible]
/-
**CategoryTheory.uniqueHomsetOfZero** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：uniqueHomsetOfZero [HasZeroObject C] (X Y : C) : Unique (X ⟶ Y)
参数：X Y : C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasZeroObject.hasInitial`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C],   Cate
goryTheory.Limits.HasInitial C

--- 原说明 ---
If a Cartesian closed category has a zero object, each homset has exactly one el
ement.
-/
def uniqueHomsetOfZero [HasZeroObject C] (X Y : C) : Unique (X ⟶ Y) := by
  haveI : HasInitial C := HasZeroObject.hasInitial
  apply uniqueHomsetOfInitialIsoUnit _ X Y
  refine ⟨default, (default : 𝟙_ C ⟶ 0) ≫ default, ?_, ?_⟩ <;> simp [eq_iff_true_of_subsingleton]

attribute [local instance] uniqueHomsetOfZero

/-- A Cartesian closed category with a zero object is equivalent to the category with one object and
one morphism.
-/
/-
**CategoryTheory.equivPUnit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：equivPUnit [HasZeroObject C] : C ≌ Discrete PUnit.{w + 1} where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Cartesian closed category with a zero object is equivalent to the category wit
h one object and
one morphism.
-/
def equivPUnit [HasZeroObject C] : C ≌ Discrete PUnit.{w + 1} where
  functor := Functor.star C
  inverse := Functor.fromPUnit 0
  unitIso := NatIso.ofComponents
      (fun X =>
        { hom := default
          inv := default })
      fun _ => Subsingleton.elim _ _
  counitIso := Functor.punitExt _ _

end CategoryTheory

