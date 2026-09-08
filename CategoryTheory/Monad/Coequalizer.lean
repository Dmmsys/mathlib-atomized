/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Reflexive
public import Mathlib.CategoryTheory.Limits.Shapes.SplitCoequalizer
public import Mathlib.CategoryTheory.Monad.Algebra

/-!
# Special coequalizers associated to a monad

Associated to a monad `T : C ⥤ C` we have important coequalizer constructions:
Any algebra is a coequalizer (in the category of algebras) of free algebras. Furthermore, this
coequalizer is reflexive.
In `C`, this cofork diagram is a split coequalizer (in particular, it is still a coequalizer).
This split coequalizer is known as the Beck coequalizer (as it features heavily in Beck's
monadicity theorem).

This file has been adapted to `Mathlib/CategoryTheory/Monad/Equalizer.lean`.
Please try to keep them in sync.

-/

@[expose] public section


universe v₁ u₁

namespace CategoryTheory

namespace Monad

open Limits

variable {C : Type u₁}
variable [Category.{v₁} C]
variable {T : Monad C} (X : Algebra T)

/-!
Show that any algebra is a coequalizer of free algebras.
-/


/-- The top map in the coequalizer diagram we will construct. -/
@[simps!]
/-
**CategoryTheory.Monad.FreeCoequalizer.topMap** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Monad.FreeCoequalizer`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {T : C
ategoryTheory.Monad C} → (X : T.Algebra) → T.free.obj (T.obj X.A) ⟶ T.free.obj X
.A
参数：X : T.Algebra；T.obj X.A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The top map in the coequalizer diagram we will construct.
-/
def FreeCoequalizer.topMap : (Monad.free T).obj (T.obj X.A) ⟶ (Monad.free T).obj X.A :=
  (Monad.free T).map X.a

/-- The bottom map in the coequalizer diagram we will construct. -/
@[simps]
/-
**CategoryTheory.Monad.FreeCoequalizer.bottomMap** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Monad.FreeCoequalizer`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {T : C
ategoryTheory.Monad C} → (X : T.Algebra) → T.free.obj (T.obj X.A) ⟶ T.free.obj X
.A
参数：X : T.Algebra；T.obj X.A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bottom map in the coequalizer diagram we will construct.
-/
def FreeCoequalizer.bottomMap : (Monad.free T).obj (T.obj X.A) ⟶ (Monad.free T).obj X.A where
  f := T.μ.app X.A
  h := T.assoc X.A

/-- The cofork map in the coequalizer diagram we will construct. -/
@[simps]
/-
**CategoryTheory.Monad.FreeCoequalizer.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Monad`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cofork map in the coequalizer diagram we will construct.
-/
def FreeCoequalizer.π : (Monad.free T).obj X.A ⟶ X where
  f := X.a
  h := X.assoc.symm
/-
**CategoryTheory.Monad.FreeCoequalizer.condition** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Monad.FreeCoequalizer`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {T : CategoryT
heory.Monad C} (X : T.Algebra),   CategoryTheory.CategoryStruct.comp (CategoryTh
eory.Monad.FreeCoequalizer.topMap X)       (CategoryTheory.Monad.FreeCoequalizer
.π X) =     CategoryTheory.CategoryStruct.comp (CategoryTheory.Monad.FreeCoequal
izer.bottomMap X)       (CategoryTheory.Monad.FreeCoequalizer.π X)
参数：X : T.Algebra；CategoryTheory.Monad.FreeCoequalizer.topMap X；CategoryTheory.Mo
nad.FreeCoequalizer.π X；CategoryTheory.Monad.FreeCoequalizer.bottomMap X；Categor
yTheory.Monad.FreeCoequalizer.π X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Monad.Algebra.Hom.ext`：∀ {C : Type u₁} {inst : CategoryTh
eory.Category.{v₁, u₁} C} {T : CategoryTheory.Monad C} {A B : T.Algebra}   {x y 
: A.Hom B}, x.f = y.f → x …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Monad.Algebra.assoc`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {T : CategoryTheory.Monad C} (self : T.Algebra),   Categ
oryTheory.CategoryStruct…
-/
theorem FreeCoequalizer.condition :
    FreeCoequalizer.topMap X ≫ FreeCoequalizer.π X =
      FreeCoequalizer.bottomMap X ≫ FreeCoequalizer.π X :=
  Algebra.Hom.ext X.assoc.symm

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Monad.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Monad`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsReflexivePair (FreeCoequalizer.topMap X) (FreeCoequalizer.bottomMap X) := by
  apply IsReflexivePair.mk' _ _ _
  · apply (free T).map (T.η.app X.A)
  · ext
    dsimp
    rw [← Functor.map_comp, X.unit, Functor.map_id]
  · ext
    apply Monad.right_unit

/-- Construct the Beck cofork in the category of algebras. This cofork is reflexive as well as a
coequalizer.
-/
@[simps!]
/-
**CategoryTheory.Monad.beckAlgebraCofork** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Monad`。
形式化陈述：beckAlgebraCofork : Cofork (FreeCoequalizer.topMap X) (FreeCoequalizer.bot
tomMap X)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Monad.FreeCoequalizer.condition`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {T : CategoryTheory.Monad C} (X : T.Algebra)
,   CategoryTheory.CategoryStruct.co…

--- 原说明 ---
Construct the Beck cofork in the category of algebras. This cofork is reflexive 
as well as a
coequalizer.
-/
def beckAlgebraCofork : Cofork (FreeCoequalizer.topMap X) (FreeCoequalizer.bottomMap X) :=
  Cofork.ofπ _ (FreeCoequalizer.condition X)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The cofork constructed is a colimit. This shows that any algebra is a (reflexive) coequalizer of
free algebras.
-/
/-
**CategoryTheory.Monad.beckAlgebraCoequalizer** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Monad`。
形式化陈述：beckAlgebraCoequalizer : IsColimit (beckAlgebraCofork X)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cofork constructed is a colimit. This shows that any algebra is a (reflexive
) coequalizer of
free algebras.
-/
def beckAlgebraCoequalizer : IsColimit (beckAlgebraCofork X) :=
  Cofork.IsColimit.mk' _ fun s => by
    have h₁ : (T : C ⥤ C).map X.a ≫ s.π.f = T.μ.app X.A ≫ s.π.f :=
      congr_arg Monad.Algebra.Hom.f s.condition
    have h₂ : (T : C ⥤ C).map s.π.f ≫ s.pt.a = T.μ.app X.A ≫ s.π.f := s.π.h
    refine ⟨⟨T.η.app _ ≫ s.π.f, ?_⟩, ?_, ?_⟩
    · dsimp
      rw [Functor.map_comp, Category.assoc, h₂, Monad.right_unit_assoc,
        show X.a ≫ _ ≫ _ = _ from T.η.naturality_assoc _ _, h₁, Monad.left_unit_assoc]
    · ext
      simpa [← T.η.naturality_assoc, T.left_unit_assoc] using! T.η.app ((T : C ⥤ C).obj X.A) ≫= h₁
    · intro m hm
      ext
      dsimp only
      rw [← hm]
      apply (X.unit_assoc _).symm

/-- The Beck cofork is a split coequalizer. -/
/-
**CategoryTheory.Monad.beckSplitCoequalizer** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Monad`。
形式化陈述：beckSplitCoequalizer : IsSplitCoequalizer (T.map X.a) (T.μ.app _) X.a
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Monad.Algebra.unit`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {T : CategoryTheory.Monad C} (self : T.Algebra),   Catego
ryTheory.CategoryStruct…

--- 原说明 ---
The Beck cofork is a split coequalizer.
-/
def beckSplitCoequalizer : IsSplitCoequalizer (T.map X.a) (T.μ.app _) X.a :=
  ⟨T.η.app _, T.η.app _, X.assoc.symm, X.unit, T.left_unit _, (T.η.naturality _).symm⟩

/-- This is the Beck cofork. It is a split coequalizer, in particular a coequalizer. -/
@[simps! pt]
/-
**CategoryTheory.Monad.beckCofork** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Mona
d`。
形式化陈述：beckCofork : Cofork (T.map X.a) (T.μ.app _)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the Beck cofork. It is a split coequalizer, in particular a coequalizer.
-/
def beckCofork : Cofork (T.map X.a) (T.μ.app _) :=
  (beckSplitCoequalizer X).asCofork

@[simp]
/-
**CategoryTheory.Monad.beckCofork_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Mon
ad`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem beckCofork_π : (beckCofork X).π = X.a :=
  rfl

/-- The Beck cofork is a coequalizer. -/
/-
**CategoryTheory.Monad.beckCoequalizer** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Monad`。
形式化陈述：beckCoequalizer : IsColimit (beckCofork X)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Beck cofork is a coequalizer.
-/
def beckCoequalizer : IsColimit (beckCofork X) :=
  (beckSplitCoequalizer X).isCoequalizer

@[simp]
/-
**CategoryTheory.Monad.beckCoequalizer_desc** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Monad`。
形式化陈述：beckCoequalizer_desc (s : Cofork (T.toFunctor.map X.a) (T.μ.app X.A)) : (b
eckCoequalizer X).desc s = T.η.app _ ≫ s.π
参数：s : Cofork (T.toFunctor.map X.a) (T.μ.app X.A)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem beckCoequalizer_desc (s : Cofork (T.toFunctor.map X.a) (T.μ.app X.A)) :
    (beckCoequalizer X).desc s = T.η.app _ ≫ s.π :=
  rfl

end Monad

end CategoryTheory

