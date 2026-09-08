/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Subfunctor.Basic

/-!
# Type-valued flat functors

A functor `F : C ⥤ Type w` is a flat Type-valued functor if the category
`F.Elements` is cofiltered. (This is not equivalent to saying that `F`
is representably flat in the sense of the typeclass `RepresentablyFlat`
defined in the file `Mathlib/CategoryTheory/Functor/Flat.lean`, see also
https://golem.ph.utexas.edu/category/2011/06/flat_functors_and_morphisms_of.html
for a clarification about the differences between these notions.)

In this file, we show that if finite limits exist in `C` and are preserved by `F`,
then `F.Elements` is cofiltered.

-/

public section

universe w v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

/-
**CategoryTheory.Functor.isCofiltered_elements** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Functor`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (F : CategoryTheo
ry.Functor C (Type w))   [CategoryTheory.Limits.HasFiniteLimits C] [CategoryTheo
ry.Limits.PreservesFiniteLimits F],   CategoryTheory.IsCofiltered F.Elements
参数：F : CategoryTheory.Functor C (Type w)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_hom_comp`：conePoint
UniqueUpToIso_hom_comp {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (j : J) : 
(conePointUniqueUpToIso P Q).hom ≫ t.π.app j = s.π.…
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_hasFiniteLimits`：∀ (C : Type u
) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLimi
ts C] (J : Type w)   [inst_2 : CategoryTheory.S…
· 使用定理 `CategoryTheory.Limits.equalizer.condition`：∀ {C : Type u} {X Y : C} [ins
t : CategoryTheory.Category.{v, u} C] (f g : X ⟶ Y)   [inst_1 : CategoryTheory.L
imits.HasEqualizer f g],   Cate…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.CategoryOfElements.ext`：ext (F : C ⥤ Type w) {x y : F.Ele
ments} (f g : x ⟶ y) (w : f.val = g.val) : f = g
-/
lemma Functor.isCofiltered_elements
    (F : C ⥤ Type w) [HasFiniteLimits C] [PreservesFiniteLimits F] :
    IsCofiltered F.Elements where
  nonempty := ⟨⊤_ C, (terminalIsTerminal.isTerminalObj F).from PUnit .unit⟩
  cone_objs := by
    rintro ⟨X, x⟩ ⟨Y, y⟩
    let h := mapIsLimitOfPreservesOfIsLimit F _ _ (prodIsProd X Y)
    let h' := Types.binaryProductLimit (F.obj X) (F.obj Y)
    exact ⟨⟨X ⨯ Y, (h'.conePointUniqueUpToIso h).hom ⟨x, y⟩⟩,
      ⟨prod.fst, ConcreteCategory.congr_hom (h'.conePointUniqueUpToIso_hom_comp h (.mk .left)) _⟩,
      ⟨prod.snd, ConcreteCategory.congr_hom (h'.conePointUniqueUpToIso_hom_comp h (.mk .right)) _⟩,
      by tauto⟩
  cone_maps := by
    rintro ⟨X, x⟩ ⟨Y, y⟩ ⟨f, hf⟩ ⟨g, hg⟩
    dsimp at f g hf hg
    rw [← hg] at hf
    let h := isLimitForkMapOfIsLimit F _ (equalizerIsEqualizer f g)
    let h' := (Types.equalizerLimit (g := F.map f) (h := F.map g)).isLimit
    exact ⟨⟨equalizer f g, (h'.conePointUniqueUpToIso h).hom ⟨x, hf⟩⟩,
      ⟨equalizer.ι f g, ConcreteCategory.congr_hom
        (h'.conePointUniqueUpToIso_hom_comp h .zero) ⟨x, hf⟩⟩,
      by ext; exact equalizer.condition f g⟩

namespace FunctorToTypes

variable (F : C ⥤ Type w) {X : C} (x : F.obj X)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given a functor `F : C ⥤ Type w`, an object `X : C` and `x : F.obj X`,
this is the subfunctor of the functor `Over.forget X ⋙ F : Over X ⥤ Type w`
which sends an object of `Over X` corresponding to a morphism `f : Y ⟶ X`
to the subset of `F.obj Y` consisting of those elements `y : F.obj Y`
such that `F.map f y = x`. -/
/-
**CategoryTheory.FunctorToTypes.fromOverSubfunctor** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.FunctorToTypes`。
形式化陈述：fromOverSubfunctor : Subfunctor (Over.forget X ⋙ F) where obj U
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a functor `F : C ⥤ Type w`, an object `X : C` and `x : F.obj X`,
this is the subfunctor of the functor `Over.forget X ⋙ F : Over X ⥤ Type w`
which sends an object of `Over X` corresponding to a morphism `f : Y ⟶ X`
to the subset of `F.obj Y` consisting of those elements `y : F.obj Y`
such that `F.map f y = x`.
-/
def fromOverSubfunctor : Subfunctor (Over.forget X ⋙ F) where
  obj U := F.map U.hom ⁻¹' {x}
  map _ _ _ := by simpa [← comp_apply, ← Functor.map_comp]

@[simp]
/-
**CategoryTheory.FunctorToTypes.mem_fromOverSubfunctor_iff** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.FunctorToTypes`。
形式化陈述：mem_fromOverSubfunctor_iff {U : Over X} (u : F.obj U.left) : u in (fromOve
rSubfunctor F x).obj U ↔ F.map U.hom u = x
参数：u : F.obj U.left。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_fromOverSubfunctor_iff {U : Over X} (u : F.obj U.left) :
    u ∈ (fromOverSubfunctor F x).obj U ↔ F.map U.hom u = x := Iff.rfl

/-- Given a functor `F : C ⥤ Type w`, an object `X : C` and `x : F.obj X`,
this is the functor `Over X ⥤ Type w` which sends an object of `Over X`
corresponding to a morphism `f : Y ⟶ X` to the subtype of `F.obj Y`
consisting of those elements `y : F.obj Y` such that `F.map f y = x`. -/
/-
**CategoryTheory.FunctorToTypes.fromOverFunctor** 是 Mathlib 中的一个缩写定义，位于命名空间 `Cat
egoryTheory.FunctorToTypes`。
形式化陈述：fromOverFunctor : Over X ⥤ Type w
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a functor `F : C ⥤ Type w`, an object `X : C` and `x : F.obj X`,
this is the functor `Over X ⥤ Type w` which sends an object of `Over X`
corresponding to a morphism `f : Y ⟶ X` to the subtype of `F.obj Y`
consisting of those elements `y : F.obj Y` such that `F.map f y = x`.
-/
abbrev fromOverFunctor : Over X ⥤ Type w := (fromOverSubfunctor F x).toFunctor

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open CategoryOfElements in
/-- Given a functor `F : C ⥤ Type w`, an object `X : C` and `x : F.obj X`,
this is the equivalence between the category of elements of `fromOverFunctor F x`
with the `Over` category of `x` considered as an object of `F.Elements`. -/
/-
**CategoryTheory.FunctorToTypes.fromOverFunctorElementsEquivalence** 是 Mathlib 中
的一个定义，位于命名空间 `CategoryTheory.FunctorToTypes`。
形式化陈述：fromOverFunctorElementsEquivalence : (fromOverFunctor F x).Elements ≌ Over
 (F.elementsMk X x) where functor.obj u
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a functor `F : C ⥤ Type w`, an object `X : C` and `x : F.obj X`,
this is the equivalence between the category of elements of `fromOverFunctor F x
`
with the `Over` category of `x` considered as an object of `F.Elements`.
-/
def fromOverFunctorElementsEquivalence :
    (fromOverFunctor F x).Elements ≌ Over (F.elementsMk X x) where
  functor.obj u :=
    Over.mk (homMk (F.elementsMk u.fst.left u.snd.1) _ u.fst.hom u.snd.2)
  functor.map f :=
    Over.homMk (homMk _ _ f.val.left (Subtype.ext_iff.1 f.prop))
  inverse.obj u :=
    Functor.elementsMk _ (Over.mk u.hom.1) ⟨u.left.snd, u.hom.2⟩
  inverse.map f := homMk _ _ (Over.homMk f.left.val (Subtype.ext_iff.1 (Over.w f)))
    (by cat_disch)
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  -- `cat_disch` can fill in this proof, but is unfortunately quite slow.
  functor_unitIso_comp X := by simp_all; rfl
/-
**CategoryTheory.FunctorToTypes.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Funct
orToTypes`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsCofiltered F.Elements] : IsCofiltered (fromOverFunctor F x).Elements :=
  .of_equivalence (fromOverFunctorElementsEquivalence F x).symm

end FunctorToTypes

end CategoryTheory

