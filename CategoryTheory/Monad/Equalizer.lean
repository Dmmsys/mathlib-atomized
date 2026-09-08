/-
Copyright (c) 2024 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Reflexive
public import Mathlib.CategoryTheory.Limits.Shapes.SplitEqualizer
public import Mathlib.CategoryTheory.Monad.Algebra

/-!
# Special equalizers associated to a comonad

Associated to a comonad `T : C ⥤ C` we have important equalizer constructions:
Any coalgebra is an equalizer (in the category of coalgebras) of cofree coalgebras. Furthermore,
this equalizer is coreflexive.
In `C`, this fork diagram is a split equalizer (in particular, it is still an equalizer).
This split equalizer is known as the Beck equalizer (as it features heavily in Beck's
comonadicity theorem).

This file is adapted from `Mathlib/CategoryTheory/Monad/Coequalizer.lean`.
Please try to keep them in sync.

-/

@[expose] public section


universe v₁ u₁

namespace CategoryTheory

namespace Comonad

open Limits

variable {C : Type u₁}
variable [Category.{v₁} C]
variable {T : Comonad C} (X : Coalgebra T)

/-!
Show that any coalgebra is an equalizer of cofree coalgebras.
-/


/-- The top map in the equalizer diagram we will construct. -/
@[simps!]
/-
**CategoryTheory.Comonad.CofreeEqualizer.topMap** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Comonad.CofreeEqualizer`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {T : C
ategoryTheory.Comonad C} → (X : T.Coalgebra) → T.cofree.obj X.A ⟶ T.cofree.obj (
T.obj X.A)
参数：X : T.Coalgebra；T.obj X.A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The top map in the equalizer diagram we will construct.
-/
def CofreeEqualizer.topMap : (Comonad.cofree T).obj X.A ⟶ (Comonad.cofree T).obj (T.obj X.A) :=
  (Comonad.cofree T).map X.a

/-- The bottom map in the equalizer diagram we will construct. -/
@[simps]
/-
**CategoryTheory.Comonad.CofreeEqualizer.bottomMap** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Comonad.CofreeEqualizer`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {T : C
ategoryTheory.Comonad C} → (X : T.Coalgebra) → T.cofree.obj X.A ⟶ T.cofree.obj (
T.obj X.A)
参数：X : T.Coalgebra；T.obj X.A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bottom map in the equalizer diagram we will construct.
-/
def CofreeEqualizer.bottomMap :
    (Comonad.cofree T).obj X.A ⟶ (Comonad.cofree T).obj (T.obj X.A) where
  f := T.δ.app X.A
  h := T.coassoc X.A

/-- The fork map in the equalizer diagram we will construct. -/
@[simps]
/-
**CategoryTheory.Comonad.CofreeEqualizer.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Comonad`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fork map in the equalizer diagram we will construct.
-/
def CofreeEqualizer.ι : X ⟶ (Comonad.cofree T).obj X.A where
  f := X.a
  h := X.coassoc.symm
/-
**CategoryTheory.Comonad.CofreeEqualizer.condition** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Comonad.CofreeEqualizer`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {T : CategoryT
heory.Comonad C} (X : T.Coalgebra),   CategoryTheory.CategoryStruct.comp (Catego
ryTheory.Comonad.CofreeEqualizer.ι X)       (CategoryTheory.Comonad.CofreeEquali
zer.topMap X) =     CategoryTheory.CategoryStruct.comp (CategoryTheory.Comonad.C
ofreeEqualizer.ι X)       (CategoryTheory.Comonad.CofreeEqualizer.bottomMap X)
参数：X : T.Coalgebra；CategoryTheory.Comonad.CofreeEqualizer.ι X；CategoryTheory.Com
onad.CofreeEqualizer.topMap X；CategoryTheory.Comonad.CofreeEqualizer.ι X；Categor
yTheory.Comonad.CofreeEqualizer.bottomMap X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Comonad.Coalgebra.Hom.ext`：∀ {C : Type u₁} {inst : Catego
ryTheory.Category.{v₁, u₁} C} {G : CategoryTheory.Comonad C} {A B : G.Coalgebra}
   {x y : A.Hom B}, x.f = y.f …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Comonad.Coalgebra.coassoc`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {G : CategoryTheory.Comonad C} (self : G.Coalgebra
),   CategoryTheory.CategorySt…
-/
theorem CofreeEqualizer.condition :
    CofreeEqualizer.ι X ≫ CofreeEqualizer.topMap X =
      CofreeEqualizer.ι X ≫ CofreeEqualizer.bottomMap X :=
  Coalgebra.Hom.ext X.coassoc.symm

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Comonad.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Comonad`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsCoreflexivePair (CofreeEqualizer.topMap X) (CofreeEqualizer.bottomMap X) := by
  apply IsCoreflexivePair.mk' _ _ _
  · apply (cofree T).map (T.ε.app X.A)
  · ext
    dsimp
    rw [← Functor.map_comp, X.counit, Functor.map_id]
  · ext
    apply Comonad.right_counit

/-- Construct the Beck fork in the category of coalgebras. This fork is coreflexive as well as an
equalizer.
-/
@[simps!]
/-
**CategoryTheory.Comonad.beckCoalgebraFork** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Comonad`。
形式化陈述：beckCoalgebraFork : Fork (CofreeEqualizer.topMap X) (CofreeEqualizer.botto
mMap X)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Comonad.CofreeEqualizer.condition`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {T : CategoryTheory.Comonad C} (X : T.Coal
gebra),   CategoryTheory.CategoryStruc…

--- 原说明 ---
Construct the Beck fork in the category of coalgebras. This fork is coreflexive 
as well as an
equalizer.
-/
def beckCoalgebraFork : Fork (CofreeEqualizer.topMap X) (CofreeEqualizer.bottomMap X) :=
  Fork.ofι _ (CofreeEqualizer.condition X)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The fork constructed is a limit. This shows that any coalgebra is a (coreflexive) equalizer of
cofree coalgebras.
-/
/-
**CategoryTheory.Comonad.beckCoalgebraEqualizer** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Comonad`。
形式化陈述：beckCoalgebraEqualizer : IsLimit (beckCoalgebraFork X)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fork constructed is a limit. This shows that any coalgebra is a (coreflexive
) equalizer of
cofree coalgebras.
-/
def beckCoalgebraEqualizer : IsLimit (beckCoalgebraFork X) :=
  Fork.IsLimit.mk' _ fun s => by
    have h₁ : s.ι.f ≫ (T : C ⥤ C).map X.a = s.ι.f ≫ T.δ.app X.A :=
      congr_arg Comonad.Coalgebra.Hom.f s.condition
    have h₂ : s.pt.a ≫ (T : C ⥤ C).map s.ι.f = s.ι.f ≫ T.δ.app X.A := s.ι.h
    refine ⟨⟨s.ι.f ≫ T.ε.app _, ?_⟩, ?_, ?_⟩
    · dsimp
      rw [Functor.map_comp, reassoc_of% h₂, Comonad.right_counit]
      dsimp
      rw [Category.comp_id, Category.assoc, ← T.counit_naturality,
        reassoc_of% h₁, Comonad.left_counit]
      simp
    · ext
      simpa [← T.ε.naturality_assoc, T.left_counit_assoc] using! h₁ =≫ T.ε.app ((T : C ⥤ C).obj X.A)
    · intro m hm
      ext
      dsimp only
      rw [← hm]
      simp [beckCoalgebraFork, X.counit]

/-- The Beck fork is a split equalizer. -/
/-
**CategoryTheory.Comonad.beckSplitEqualizer** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Comonad`。
形式化陈述：beckSplitEqualizer : IsSplitEqualizer (T.map X.a) (T.δ.app _) X.a
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Comonad.Coalgebra.counit`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {G : CategoryTheory.Comonad C} (self : G.Coalgebra)
,   CategoryTheory.CategorySt…

--- 原说明 ---
The Beck fork is a split equalizer.
-/
def beckSplitEqualizer : IsSplitEqualizer (T.map X.a) (T.δ.app _) X.a :=
  ⟨T.ε.app _, T.ε.app _, X.coassoc.symm, X.counit, T.left_counit _, (T.ε.naturality _)⟩

/-- This is the Beck fork. It is a split equalizer, in particular an equalizer. -/
@[simps! pt]
/-
**CategoryTheory.Comonad.beckFork** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Como
nad`。
形式化陈述：beckFork : Fork (T.map X.a) (T.δ.app _)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the Beck fork. It is a split equalizer, in particular an equalizer.
-/
def beckFork : Fork (T.map X.a) (T.δ.app _) :=
  (beckSplitEqualizer X).asFork

@[simp]
/-
**CategoryTheory.Comonad.beckFork_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Com
onad`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem beckFork_ι : (beckFork X).ι = X.a :=
  rfl

/-- The Beck fork is an equalizer. -/
/-
**CategoryTheory.Comonad.beckEqualizer** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Comonad`。
形式化陈述：beckEqualizer : IsLimit (beckFork X)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Beck fork is an equalizer.
-/
def beckEqualizer : IsLimit (beckFork X) :=
  (beckSplitEqualizer X).isEqualizer

@[simp]
/-
**CategoryTheory.Comonad.beckEqualizer_lift** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Comonad`。
形式化陈述：beckEqualizer_lift (s : Fork (T.toFunctor.map X.a) (T.δ.app X.A)) : (beckE
qualizer X).lift s = s.ι ≫ T.ε.app _
参数：s : Fork (T.toFunctor.map X.a) (T.δ.app X.A)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem beckEqualizer_lift (s : Fork (T.toFunctor.map X.a) (T.δ.app X.A)) :
    (beckEqualizer X).lift s = s.ι ≫ T.ε.app _ :=
  rfl

end Comonad

end CategoryTheory

