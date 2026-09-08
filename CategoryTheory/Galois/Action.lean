/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Galois.Examples
public import Mathlib.CategoryTheory.Galois.Prorepresentability

/-!

# Induced functor to finite `Aut F`-sets

Any (fiber) functor `F : C ⥤ FintypeCat` factors via the forgetful functor
from finite `Aut F`-sets to finite sets. In this file we collect basic properties
of the induced functor `H : C ⥤ Action FintypeCat (Aut F)`.

See `Mathlib/CategoryTheory/Galois/Full.lean` for the proof that `H` is (faithfully) full.

-/

@[expose] public section

universe u

namespace CategoryTheory

namespace PreGaloisCategory

open Limits CategoryTheory.Functor

variable {C : Type*} [Category* C] (F : C ⥤ FintypeCat.{u})

/-- Any (fiber) functor `F : C ⥤ FintypeCat` naturally factors via
the forgetful functor from `Action FintypeCat (Aut F)` to `FintypeCat`. -/
/-
**CategoryTheory.PreGaloisCategory.functorToAction** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.PreGaloisCategory`。
形式化陈述：functorToAction : C ⥤ Action FintypeCat.{u} (Aut F) where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any (fiber) functor `F : C ⥤ FintypeCat` naturally factors via
the forgetful functor from `Action FintypeCat (Aut F)` to `FintypeCat`.
-/
def functorToAction : C ⥤ Action FintypeCat.{u} (Aut F) where
  obj X := Action.FintypeCat.ofMulAction (Aut F) (F.obj X)
  map f := {
    hom := F.map f
    comm := fun g ↦ symm <| g.hom.naturality f
  }
/-
**CategoryTheory.PreGaloisCategory.functorToAction_comp_forget** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.PreGaloisCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma functorToAction_comp_forget₂_eq : functorToAction F ⋙ forget₂ _ FintypeCat = F := rfl

@[simp]
/-
**CategoryTheory.PreGaloisCategory.functorToAction_map** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.PreGaloisCategory`。
形式化陈述：functorToAction_map {X Y : C} (f : X ⟶ Y) : ((functorToAction F).map f).ho
m = F.map f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma functorToAction_map {X Y : C} (f : X ⟶ Y) : ((functorToAction F).map f).hom = F.map f :=
  rfl
/-
**CategoryTheory.PreGaloisCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pr
eGaloisCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) : MulAction (Aut X) ((functorToAction F).obj X).V :=
  inferInstanceAs <| MulAction (Aut X) (F.obj X)

variable [GaloisCategory C] [FiberFunctor F]
/-
**CategoryTheory.PreGaloisCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pr
eGaloisCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) [IsGalois X] : MulAction.IsPretransitive (Aut X) ((functorToAction F).obj X).V :=
  isPretransitive_of_isGalois F X
/-
**CategoryTheory.PreGaloisCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pr
eGaloisCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Functor.Faithful (functorToAction F) :=
  have : Functor.Faithful (functorToAction F ⋙ forget₂ _ FintypeCat) :=
    inferInstanceAs <| Functor.Faithful F
  Functor.Faithful.of_comp (functorToAction F) (forget₂ _ FintypeCat)
/-
**CategoryTheory.PreGaloisCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pr
eGaloisCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PreservesMonomorphisms (functorToAction F) :=
  have : PreservesMonomorphisms (functorToAction F ⋙ forget₂ _ FintypeCat) :=
    inferInstanceAs <| PreservesMonomorphisms F
  preservesMonomorphisms_of_preserves_of_reflects (functorToAction F) (forget₂ _ FintypeCat)
/-
**CategoryTheory.PreGaloisCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pr
eGaloisCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ReflectsMonomorphisms (functorToAction F) := reflectsMonomorphisms_of_faithful _
/-
**CategoryTheory.PreGaloisCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pr
eGaloisCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Functor.ReflectsIsomorphisms (functorToAction F) where
  reflects f _ :=
    have : IsIso (F.map f) := (forget₂ _ FintypeCat).map_isIso ((functorToAction F).map f)
    isIso_of_reflects_iso f F
/-
**CategoryTheory.PreGaloisCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pr
eGaloisCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : PreservesFiniteCoproducts (functorToAction F) :=
  ⟨fun _ ↦ Action.preservesColimitsOfShape_of_preserves (functorToAction F)
    (inferInstanceAs <| PreservesColimitsOfShape (Discrete _) F)⟩
/-
**CategoryTheory.PreGaloisCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pr
eGaloisCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : PreservesFiniteProducts (functorToAction F) :=
  ⟨fun _ ↦ Action.preservesLimitsOfShape_of_preserves (functorToAction F)
    (inferInstanceAs <| PreservesLimitsOfShape (Discrete _) F)⟩
/-
**CategoryTheory.PreGaloisCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pr
eGaloisCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance (G : Type*) [Group G] [Finite G] :
    PreservesColimitsOfShape (SingleObj G) (functorToAction F) :=
  Action.preservesColimitsOfShape_of_preserves _ <|
    inferInstanceAs <| PreservesColimitsOfShape (SingleObj G) F
/-
**CategoryTheory.PreGaloisCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pr
eGaloisCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PreservesIsConnected (functorToAction F) :=
  ⟨fun {X} _ ↦ FintypeCat.Action.isConnected_of_transitive (Aut F) (F.obj X)⟩

end PreGaloisCategory

end CategoryTheory

