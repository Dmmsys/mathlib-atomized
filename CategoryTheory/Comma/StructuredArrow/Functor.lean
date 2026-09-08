/-
Copyright (c) 2024 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.Grothendieck

/-!
# Structured Arrow Categories as strict functor to Cat

Forming a structured arrow category `StructuredArrow d T` with `d : D` and `T : C ⥤ D` is strictly
functorial in `S`, inducing a functor `Dᵒᵖ ⥤ Cat`. This file constructs said functor and proves
that, in the dual case, we can precompose it with another functor `L : E ⥤ D` to obtain a category
equivalent to `Comma L T`.
-/

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace StructuredArrow

set_option backward.isDefEq.respectTransparency false in
/-- The structured arrow category `StructuredArrow d T` depends on the chosen domain `d : D` in a
functorial way, inducing a functor `Dᵒᵖ ⥤ Cat`. -/
@[simps]
/-
**CategoryTheory.StructuredArrow.functor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.StructuredArrow`。
形式化陈述：functor (T : C ⥤ D) : Dᵒᵖ ⥤ Cat where obj d
参数：T : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The structured arrow category `StructuredArrow d T` depends on the chosen domain
 `d : D` in a
functorial way, inducing a functor `Dᵒᵖ ⥤ Cat`.
-/
def functor (T : C ⥤ D) : Dᵒᵖ ⥤ Cat where
  obj d := .of <| StructuredArrow d.unop T
  map f := (map f.unop).toCatHom
  map_id d := by
    ext
    exact Functor.ext (fun ⟨_, _, _⟩ => by simp)
  map_comp f g := by
    ext
    exact Functor.ext (fun _ => by simp)

end StructuredArrow

namespace CostructuredArrow

set_option backward.isDefEq.respectTransparency false in
/-- The costructured arrow category `CostructuredArrow T d` depends on the chosen codomain `d : D`
in a functorial way, inducing a functor `D ⥤ Cat`. -/
@[simps]
/-
**CategoryTheory.CostructuredArrow.functor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.CostructuredArrow`。
形式化陈述：functor (T : C ⥤ D) : D ⥤ Cat where obj d
参数：T : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The costructured arrow category `CostructuredArrow T d` depends on the chosen co
domain `d : D`
in a functorial way, inducing a functor `D ⥤ Cat`.
-/
def functor (T : C ⥤ D) : D ⥤ Cat where
  obj d := .of <| CostructuredArrow T d
  map f := (CostructuredArrow.map f).toCatHom
  map_id d := by
    ext
    exact Functor.ext (fun ⟨_, _, _⟩ => by simp [CostructuredArrow.map, Comma.mapRight])
  map_comp f g := by
    ext
    exact Functor.ext (fun _ => by simp [CostructuredArrow.map, Comma.mapRight])

variable {E : Type u₃} [Category.{v₃} E]
variable (L : C ⥤ D) (R : E ⥤ D)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The functor used to establish the equivalence `grothendieckPrecompFunctorEquivalence` between
the Grothendieck construction on `CostructuredArrow.functor` and the comma category. -/
@[simps]
/-
**CategoryTheory.CostructuredArrow.grothendieckPrecompFunctorToComma** 是 Mathlib
 中的一个定义，位于命名空间 `CategoryTheory.CostructuredArrow`。
形式化陈述：grothendieckPrecompFunctorToComma : Grothendieck (R ⋙ functor L) ⥤ Comma L
 R where obj P
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor used to establish the equivalence `grothendieckPrecompFunctorEquival
ence` between
the Grothendieck construction on `CostructuredArrow.functor` and the comma categ
ory.
-/
def grothendieckPrecompFunctorToComma : Grothendieck (R ⋙ functor L) ⥤ Comma L R where
  obj P := ⟨P.fiber.left, P.base, P.fiber.hom⟩
  map f := ⟨f.fiber.left, f.base, by simp⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Fibers of `grothendieckPrecompFunctorToComma L R`, composed with `Comma.fst L R`, are isomorphic
to the projection `proj L (R.obj X)`. -/
@[simps!]
/-
**CategoryTheory.CostructuredArrow.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Co
structuredArrow`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Fibers of `grothendieckPrecompFunctorToComma L R`, composed with `Comma.fst L R`
, are isomorphic
to the projection `proj L (R.obj X)`.
-/
def ιCompGrothendieckPrecompFunctorToCommaCompFst (X : E) :
    Grothendieck.ι (R ⋙ functor L) X ⋙ grothendieckPrecompFunctorToComma L R ⋙ Comma.fst _ _ ≅
    proj L (R.obj X) :=
  NatIso.ofComponents (fun X => Iso.refl _) (fun _ => by simp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The inverse functor used to establish the equivalence `grothendieckPrecompFunctorEquivalence`
between the Grothendieck construction on `CostructuredArrow.functor` and the comma category. -/
@[simps]
/-
**CategoryTheory.CostructuredArrow.commaToGrothendieckPrecompFunctor** 是 Mathlib
 中的一个定义，位于命名空间 `CategoryTheory.CostructuredArrow`。
形式化陈述：commaToGrothendieckPrecompFunctor : Comma L R ⥤ Grothendieck (R ⋙ functor 
L) where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse functor used to establish the equivalence `grothendieckPrecompFuncto
rEquivalence`
between the Grothendieck construction on `CostructuredArrow.functor` and the com
ma category.
-/
def commaToGrothendieckPrecompFunctor : Comma L R ⥤ Grothendieck (R ⋙ functor L) where
  obj X := ⟨X.right, mk X.hom⟩
  map f := ⟨f.right, homMk f.left⟩
  map_id X := Grothendieck.ext _ _ rfl (by simp)
  map_comp f g := Grothendieck.ext _ _ rfl (by simp)

set_option backward.isDefEq.respectTransparency false in
/-- For `L : C ⥤ D`, taking the Grothendieck construction of `CostructuredArrow.functor L`
precomposed with another functor `R : E ⥤ D` results in a category which is equivalent to
the comma category `Comma L R`. -/
@[simps]
/-
**CategoryTheory.CostructuredArrow.grothendieckPrecompFunctorEquivalence** 是 Mat
hlib 中的一个定义，位于命名空间 `CategoryTheory.CostructuredArrow`。
形式化陈述：grothendieckPrecompFunctorEquivalence : Grothendieck (R ⋙ functor L) ≌ Com
ma L R where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `L : C ⥤ D`, taking the Grothendieck construction of `CostructuredArrow.func
tor L`
precomposed with another functor `R : E ⥤ D` results in a category which is equi
valent to
the comma category `Comma L R`.
-/
def grothendieckPrecompFunctorEquivalence : Grothendieck (R ⋙ functor L) ≌ Comma L R where
  functor := grothendieckPrecompFunctorToComma _ _
  inverse := commaToGrothendieckPrecompFunctor _ _
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _)

/-- The functor projecting out the domain of arrows from the Grothendieck construction on
costructured arrows. -/
@[simps!]
/-
**CategoryTheory.CostructuredArrow.grothendieckProj** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.CostructuredArrow`。
形式化陈述：grothendieckProj : Grothendieck (functor L) ⥤ C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor projecting out the domain of arrows from the Grothendieck constructi
on on
costructured arrows.
-/
def grothendieckProj : Grothendieck (functor L) ⥤ C :=
  grothendieckPrecompFunctorToComma L (𝟭 _) ⋙ Comma.fst _ _

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Fibers of `grothendieckProj L` are isomorphic to the projection `proj L X`. -/
@[simps!]
/-
**CategoryTheory.CostructuredArrow.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Co
structuredArrow`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Fibers of `grothendieckProj L` are isomorphic to the projection `proj L X`.
-/
def ιCompGrothendieckProj (X : D) :
    Grothendieck.ι (functor L) X ⋙ grothendieckProj L ≅ proj L X :=
  ιCompGrothendieckPrecompFunctorToCommaCompFst L (𝟭 _) X

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Functors between costructured arrow categories induced by morphisms in the base category
composed with fibers of `grothendieckProj L` are isomorphic to the projection `proj L X`. -/
@[simps!]
/-
**CategoryTheory.CostructuredArrow.mapComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.CostructuredArrow`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Functors between costructured arrow categories induced by morphisms in the base 
category
composed with fibers of `grothendieckProj L` are isomorphic to the projection `p
roj L X`.
-/
def mapCompιCompGrothendieckProj {X Y : D} (f : X ⟶ Y) :
    CostructuredArrow.map f ⋙ Grothendieck.ι (functor L) Y ⋙ grothendieckProj L ≅ proj L X :=
  Functor.isoWhiskerLeft (CostructuredArrow.map f)
    (ιCompGrothendieckPrecompFunctorToCommaCompFst L (𝟭 _) Y)

/-- The functor `CostructuredArrow.pre` induces a natural transformation
`CostructuredArrow.functor (S ⋙ T) ⟶ CostructuredArrow.functor T` for `S : C ⥤ D` and
`T : D ⥤ E`. -/
@[simps]
/-
**CategoryTheory.CostructuredArrow.preFunctor** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.CostructuredArrow`。
形式化陈述：preFunctor {D : Type u₁} [Category.{v₁} D] (S : C ⥤ D) (T : D ⥤ E) : funct
or (S ⋙ T) ⟶ functor T where app e
参数：S : C ⥤ D；T : D ⥤ E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `CostructuredArrow.pre` induces a natural transformation
`CostructuredArrow.functor (S ⋙ T) ⟶ CostructuredArrow.functor T` for `S : C ⥤ D
` and
`T : D ⥤ E`.
-/
def preFunctor {D : Type u₁} [Category.{v₁} D] (S : C ⥤ D) (T : D ⥤ E) :
    functor (S ⋙ T) ⟶ functor T where
  app e := (pre S T e).toCatHom

end CostructuredArrow

end CategoryTheory

