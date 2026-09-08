/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Patrick Massot, Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Adjunction.Reflective
public import Mathlib.CategoryTheory.Monad.Limits  -- shake: keep (used in `example` only)
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.UniformSpace.Completion

/-!
# The category of uniform spaces

We construct the category of uniform spaces, show that the complete separated uniform spaces
form a reflective subcategory, and hence possess all limits that uniform spaces do.

TODO: show that uniform spaces actually have all limits!
-/

@[expose] public section


universe u

open CategoryTheory


/-- An object in the category of uniform spaces. -/
/-
**UniformSpaceCat** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type (u + 1)
参数：u + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An object in the category of uniform spaces.
-/
structure UniformSpaceCat : Type (u + 1) where
  /-- Construct a bundled `UniformSpace` from the underlying type and the typeclass. -/
  of ::
  /-- The underlying uniform space. -/
  carrier : Type u
  [str : UniformSpace carrier]

attribute [instance] UniformSpaceCat.str

namespace UniformSpaceCat

/-
**UniformSpaceCat.** 是 Mathlib 中的一个实例，位于命名空间 `UniformSpaceCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort UniformSpaceCat Type* :=
  ⟨carrier⟩

/-- A bundled uniform continuous map. -/
@[ext]
/-
**UniformSpaceCat.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `UniformSpaceCat`。
形式化陈述：UniformSpaceCat → UniformSpaceCat → Type (max u_1 u_2)
参数：max u_1 u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bundled uniform continuous map.
-/
structure Hom (X Y : UniformSpaceCat) where
  /-- The underlying `UniformContinuous` function. -/
  hom' : { f : X → Y // UniformContinuous f }
/-
**UniformSpaceCat.** 是 Mathlib 中的一个实例，位于命名空间 `UniformSpaceCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LargeCategory.{u} UniformSpaceCat.{u} where
  Hom := Hom
  id X := ⟨id, uniformContinuous_id⟩
  comp f g := ⟨⟨g.hom'.val ∘ f.hom'.val, g.hom'.property.comp f.hom'.property⟩⟩
  id_comp := by intros; apply Hom.ext; simp
  comp_id := by intros; apply Hom.ext; simp
  assoc := by intros; apply Hom.ext; ext; simp
/-
**UniformSpaceCat.instFunLike** 是 Mathlib 中的一个实例，位于命名空间 `UniformSpaceCat`。
形式化陈述：instFunLike (X Y : UniformSpaceCat) : FunLike { f : X -> Y // UniformConti
nuous f } X Y where coe
参数：X Y : UniformSpaceCat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFunLike (X Y : UniformSpaceCat) :
    FunLike { f : X → Y // UniformContinuous f } X Y where
  coe := Subtype.val
  coe_injective _ _ h := Subtype.ext h
/-
**UniformSpaceCat.** 是 Mathlib 中的一个实例，位于命名空间 `UniformSpaceCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ConcreteCategory UniformSpaceCat ({ f : · → · // UniformContinuous f }) where
  hom f := f.hom'
  ofHom f := ⟨f⟩

/-- Turn a morphism in `UniformSpaceCat` back into a function which is `UniformContinuous`. -/
/-
**UniformSpaceCat.Hom.hom** 是 Mathlib 中的一个定义，位于命名空间 `UniformSpaceCat.Hom`。
形式化陈述：{X Y : UniformSpaceCat} → X.Hom Y → { f // UniformContinuous f }
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a morphism in `UniformSpaceCat` back into a function which is `UniformConti
nuous`.
-/
abbrev Hom.hom {X Y : UniformSpaceCat} (f : Hom X Y) :=
  ConcreteCategory.hom (C := UniformSpaceCat) f

/-- Typecheck a function which is `UniformContinuous` as a morphism in `UniformSpaceCat`. -/
/-
**UniformSpaceCat.ofHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `UniformSpaceCat`。
形式化陈述：ofHom {X Y : Type u} [UniformSpace X] [UniformSpace Y] (f : { f : X -> Y /
/ UniformContinuous f }) : of X ⟶ of Y
参数：f : { f : X -> Y // UniformContinuous f }。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typecheck a function which is `UniformContinuous` as a morphism in `UniformSpace
Cat`.
-/
abbrev ofHom {X Y : Type u} [UniformSpace X] [UniformSpace Y]
    (f : { f : X → Y // UniformContinuous f }) : of X ⟶ of Y :=
  ConcreteCategory.ofHom f
/-
**UniformSpaceCat.** 是 Mathlib 中的一个实例，位于命名空间 `UniformSpaceCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited UniformSpaceCat :=
  ⟨UniformSpaceCat.of Empty⟩
/-
**UniformSpaceCat.coe_of** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpaceCat`。
形式化陈述：coe_of (X : Type u) [UniformSpace X] : (of X : Type u) = X
参数：X : Type u。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_of (X : Type u) [UniformSpace X] : (of X : Type u) = X :=
  rfl

@[simp]
/-
**UniformSpaceCat.hom_comp** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpaceCat`。
形式化陈述：hom_comp {X Y Z : UniformSpaceCat} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).hom =
 ⟨g ∘ f, g.hom.prop.comp f.hom.prop⟩
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hom_comp {X Y Z : UniformSpaceCat} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = ⟨g ∘ f, g.hom.prop.comp f.hom.prop⟩ :=
  rfl

@[simp]
/-
**UniformSpaceCat.hom_id** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpaceCat`。
形式化陈述：hom_id (X : UniformSpaceCat) : (𝟙 X : X ⟶ X).hom = ⟨id, uniformContinuous_
id⟩
参数：X : UniformSpaceCat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hom_id (X : UniformSpaceCat) : (𝟙 X : X ⟶ X).hom = ⟨id, uniformContinuous_id⟩ :=
  rfl

@[simp]
/-
**UniformSpaceCat.hom_ofHom** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpaceCat`。
形式化陈述：hom_ofHom {X Y : Type u} [UniformSpace X] [UniformSpace Y] (f : { f : X ->
 Y // UniformContinuous f }) : (ofHom f).hom = f
参数：f : { f : X -> Y // UniformContinuous f }。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hom_ofHom {X Y : Type u} [UniformSpace X] [UniformSpace Y]
    (f : { f : X → Y // UniformContinuous f }) : (ofHom f).hom = f :=
  rfl
/-
**UniformSpaceCat.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpaceCat`。
形式化陈述：coe_comp {X Y Z : UniformSpaceCat} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g : X ->
 Z) = g ∘ f
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp {X Y Z : UniformSpaceCat} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g : X → Z) = g ∘ f :=
  rfl
/-
**UniformSpaceCat.coe_id** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpaceCat`。
形式化陈述：coe_id (X : UniformSpaceCat) : (𝟙 X : X -> X) = id
参数：X : UniformSpaceCat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_id (X : UniformSpaceCat) : (𝟙 X : X → X) = id :=
  rfl
/-
**UniformSpaceCat.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpaceCat`。
形式化陈述：coe_mk {X Y : UniformSpaceCat} (f : X -> Y) (hf : UniformContinuous f) : (
⟨f, hf⟩ : X ⟶ Y).hom = f
参数：f : X -> Y；hf : UniformContinuous f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk {X Y : UniformSpaceCat} (f : X → Y) (hf : UniformContinuous f) :
    (⟨f, hf⟩ : X ⟶ Y).hom = f :=
  rfl

@[ext]
/-
**UniformSpaceCat.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpaceCat`。
形式化陈述：hom_ext {X Y : UniformSpaceCat} {f g : X ⟶ Y} (h : (f : X -> Y) = g) : f =
 g
参数：h : (f : X -> Y) = g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpaceCat.Hom.ext`：∀ {X : UniformSpaceCat} {Y : UniformSpaceCat} {
x y : X.Hom Y}, x.hom' = y.hom' → x = y
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
theorem hom_ext {X Y : UniformSpaceCat} {f g : X ⟶ Y} (h : (f : X → Y) = g) : f = g :=
  Hom.ext (Subtype.ext h)

/-- The forgetful functor from uniform spaces to topological spaces. -/
/-
**UniformSpaceCat.hasForgetToTop** 是 Mathlib 中的一个实例，位于命名空间 `UniformSpaceCat`。
形式化陈述：hasForgetToTop : HasForget₂ UniformSpaceCat.{u} TopCat.{u} where forget₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from uniform spaces to topological spaces.
-/
instance hasForgetToTop : HasForget₂ UniformSpaceCat.{u} TopCat.{u} where
  forget₂ :=
    { obj := fun X => TopCat.of X
      map := fun f => TopCat.ofHom
        { toFun := f
          continuous_toFun := f.hom.property.continuous } }

end UniformSpaceCat

/-- A (bundled) complete separated uniform space. -/
/-
**CpltSepUniformSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type (u + 1)
参数：u + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A (bundled) complete separated uniform space.
-/
structure CpltSepUniformSpace where
  /-- The underlying space -/
  α : Type u
  [isUniformSpace : UniformSpace α]
  [isCompleteSpace : CompleteSpace α]
  [isT0 : T0Space α]

namespace CpltSepUniformSpace

/-
**CpltSepUniformSpace.** 是 Mathlib 中的一个实例，位于命名空间 `CpltSepUniformSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort CpltSepUniformSpace (Type u) :=
  ⟨CpltSepUniformSpace.α⟩

attribute [instance] isUniformSpace isCompleteSpace isT0

/-- The function forgetting that a complete separated uniform spaces is complete and separated. -/
/-
**CpltSepUniformSpace.toUniformSpace** 是 Mathlib 中的一个定义，位于命名空间 `CpltSepUniformSp
ace`。
形式化陈述：toUniformSpace (X : CpltSepUniformSpace) : UniformSpaceCat
参数：X : CpltSepUniformSpace。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The function forgetting that a complete separated uniform spaces is complete and
 separated.
-/
def toUniformSpace (X : CpltSepUniformSpace) : UniformSpaceCat :=
  UniformSpaceCat.of X
/-
**CpltSepUniformSpace.completeSpace** 是 Mathlib 中的一个实例，位于命名空间 `CpltSepUniformSpa
ce`。
形式化陈述：completeSpace (X : CpltSepUniformSpace) : CompleteSpace (toUniformSpace X)
.carrier
参数：X : CpltSepUniformSpace。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CpltSepUniformSpace.isCompleteSpace`：∀ (self : CpltSepUniformSpace), Com
pleteSpace self.α
-/
instance completeSpace (X : CpltSepUniformSpace) : CompleteSpace (toUniformSpace X).carrier :=
  CpltSepUniformSpace.isCompleteSpace X
/-
**CpltSepUniformSpace.t0Space** 是 Mathlib 中的一个实例，位于命名空间 `CpltSepUniformSpace`。
形式化陈述：t0Space (X : CpltSepUniformSpace) : T0Space (toUniformSpace X).carrier
参数：X : CpltSepUniformSpace。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CpltSepUniformSpace.isT0`：∀ (self : CpltSepUniformSpace), T0Space self.α
-/
instance t0Space (X : CpltSepUniformSpace) : T0Space (toUniformSpace X).carrier :=
  CpltSepUniformSpace.isT0 X

/-- Construct a bundled `UniformSpace` from the underlying type and the appropriate typeclasses. -/
/-
**CpltSepUniformSpace.of** 是 Mathlib 中的一个定义，位于命名空间 `CpltSepUniformSpace`。
形式化陈述：of (X : Type u) [UniformSpace X] [CompleteSpace X] [T0Space X] : CpltSepUn
iformSpace
参数：X : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a bundled `UniformSpace` from the underlying type and the appropriate 
typeclasses.
-/
def of (X : Type u) [UniformSpace X] [CompleteSpace X] [T0Space X] : CpltSepUniformSpace :=
  ⟨X⟩

@[simp]
/-
**CpltSepUniformSpace.coe_of** 是 Mathlib 中的一个定理，位于命名空间 `CpltSepUniformSpace`。
形式化陈述：coe_of (X : Type u) [UniformSpace X] [CompleteSpace X] [T0Space X] : (of X
 : Type u) = X
参数：X : Type u。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_of (X : Type u) [UniformSpace X] [CompleteSpace X] [T0Space X] :
    (of X : Type u) = X :=
  rfl
/-
**CpltSepUniformSpace.** 是 Mathlib 中的一个实例，位于命名空间 `CpltSepUniformSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited CpltSepUniformSpace :=
  ⟨CpltSepUniformSpace.of Empty⟩

/-- The category instance on `CpltSepUniformSpace`. -/
/-
**CpltSepUniformSpace.category** 是 Mathlib 中的一个实例，位于命名空间 `CpltSepUniformSpace`。
形式化陈述：category : LargeCategory CpltSepUniformSpace
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category instance on `CpltSepUniformSpace`.
-/
instance category : LargeCategory CpltSepUniformSpace :=
  inferInstanceAs <| Category (InducedCategory _ toUniformSpace)
/-
**CpltSepUniformSpace.instFunLike** 是 Mathlib 中的一个实例，位于命名空间 `CpltSepUniformSpace
`。
形式化陈述：instFunLike (X Y : CpltSepUniformSpace) : FunLike { f : X -> Y // UniformC
ontinuous f } X Y where coe
参数：X Y : CpltSepUniformSpace。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFunLike (X Y : CpltSepUniformSpace) :
    FunLike { f : X → Y // UniformContinuous f } X Y where
  coe := Subtype.val
  coe_injective _ _ h := Subtype.ext h

set_option backward.isDefEq.respectTransparency.types false in
/-- The concrete category instance on `CpltSepUniformSpace`. -/
/-
**CpltSepUniformSpace.concreteCategory** 是 Mathlib 中的一个实例，位于命名空间 `CpltSepUniform
Space`。
形式化陈述：concreteCategory : ConcreteCategory CpltSepUniformSpace ({ f : · -> · // U
niformContinuous f })
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The concrete category instance on `CpltSepUniformSpace`.
-/
instance concreteCategory : ConcreteCategory CpltSepUniformSpace
    ({ f : · → · // UniformContinuous f }) :=
  inferInstanceAs <| ConcreteCategory (InducedCategory _ toUniformSpace) _

set_option backward.isDefEq.respectTransparency.types false in
/-
**CpltSepUniformSpace.hasForgetToUniformSpace** 是 Mathlib 中的一个实例，位于命名空间 `CpltSep
UniformSpace`。
形式化陈述：hasForgetToUniformSpace : HasForget₂ CpltSepUniformSpace UniformSpaceCat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToUniformSpace : HasForget₂ CpltSepUniformSpace UniformSpaceCat :=
  inferInstanceAs <| HasForget₂ (InducedCategory _ toUniformSpace) _

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CpltSepUniformSpace.hom_comp** 是 Mathlib 中的一个定理，位于命名空间 `CpltSepUniformSpace`。
形式化陈述：hom_comp {X Y Z : CpltSepUniformSpace} (f : X ⟶ Y) (g : Y ⟶ Z) : ConcreteC
ategory.hom (f ≫ g) = ⟨g ∘ f, g.hom.hom.prop.comp f.hom.hom.prop⟩
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hom_comp {X Y Z : CpltSepUniformSpace} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ConcreteCategory.hom (f ≫ g) = ⟨g ∘ f, g.hom.hom.prop.comp f.hom.hom.prop⟩ :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CpltSepUniformSpace.hom_id** 是 Mathlib 中的一个定理，位于命名空间 `CpltSepUniformSpace`。
形式化陈述：hom_id (X : CpltSepUniformSpace) : ConcreteCategory.hom (𝟙 X : X ⟶ X) = ⟨i
d, uniformContinuous_id⟩
参数：X : CpltSepUniformSpace。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hom_id (X : CpltSepUniformSpace) :
    ConcreteCategory.hom (𝟙 X : X ⟶ X) = ⟨id, uniformContinuous_id⟩ :=
  rfl

@[simp]
/-
**CpltSepUniformSpace.hom_ofHom** 是 Mathlib 中的一个定理，位于命名空间 `CpltSepUniformSpace`。
形式化陈述：hom_ofHom {X Y : Type u} [UniformSpace X] [UniformSpace Y] (f : { f : X ->
 Y // UniformContinuous f }) : (UniformSpaceCat.ofHom f).hom = f
参数：f : { f : X -> Y // UniformContinuous f }。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hom_ofHom {X Y : Type u} [UniformSpace X] [UniformSpace Y]
    (f : { f : X → Y // UniformContinuous f }) : (UniformSpaceCat.ofHom f).hom = f :=
  rfl

end CpltSepUniformSpace

namespace UniformSpaceCat

open UniformSpace

open CpltSepUniformSpace

set_option backward.isDefEq.respectTransparency.types false in
/-- The functor turning uniform spaces into complete separated uniform spaces. -/
@[simps map]
/-
**UniformSpaceCat.completionFunctor** 是 Mathlib 中的一个定义，位于命名空间 `UniformSpaceCat`。
形式化陈述：completionFunctor : UniformSpaceCat ⥤ CpltSepUniformSpace where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor turning uniform spaces into complete separated uniform spaces.
-/
noncomputable def completionFunctor : UniformSpaceCat ⥤ CpltSepUniformSpace where
  obj X := CpltSepUniformSpace.of (Completion X)
  map f := ConcreteCategory.ofHom ⟨Completion.map f.1, Completion.uniformContinuous_map⟩
  map_id _ := InducedCategory.hom_ext (hom_ext (by apply Completion.map_id))
  map_comp f g := InducedCategory.hom_ext (hom_ext (by
    exact (Completion.map_comp g.hom.property f.hom.property).symm))

/-- The inclusion of a uniform space into its completion. -/
/-
**UniformSpaceCat.completionHom** 是 Mathlib 中的一个定义，位于命名空间 `UniformSpaceCat`。
形式化陈述：completionHom (X : UniformSpaceCat) : X ⟶ (forget₂ CpltSepUniformSpace Uni
formSpaceCat).obj (completionFunctor.obj X) where hom'.val
参数：X : UniformSpaceCat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of a uniform space into its completion.
-/
noncomputable def completionHom (X : UniformSpaceCat) :
    X ⟶ (forget₂ CpltSepUniformSpace UniformSpaceCat).obj (completionFunctor.obj X) where
  hom'.val := ((↑) : X → Completion X)
  hom'.property := Completion.uniformContinuous_coe X

@[simp]
/-
**UniformSpaceCat.completionHom_val** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpaceCat`。
形式化陈述：completionHom_val (X : UniformSpaceCat) (x) : (completionHom X) x = (x : C
ompletion X)
参数：X : UniformSpaceCat；x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem completionHom_val (X : UniformSpaceCat) (x) : (completionHom X) x = (x : Completion X) :=
  rfl

/-- The mate of a morphism from a `UniformSpace` to a `CpltSepUniformSpace`. -/
/-
**UniformSpaceCat.extensionHom** 是 Mathlib 中的一个定义，位于命名空间 `UniformSpaceCat`。
形式化陈述：extensionHom {X : UniformSpaceCat} {Y : CpltSepUniformSpace} (f : X ⟶ (for
get₂ CpltSepUniformSpace UniformSpaceCat).obj Y) : completionFunctor.obj X ⟶ Y
参数：f : X ⟶ (forget₂ CpltSepUniformSpace UniformSpaceCat).obj Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The mate of a morphism from a `UniformSpace` to a `CpltSepUniformSpace`.
-/
noncomputable def extensionHom {X : UniformSpaceCat} {Y : CpltSepUniformSpace}
    (f : X ⟶ (forget₂ CpltSepUniformSpace UniformSpaceCat).obj Y) :
    completionFunctor.obj X ⟶ Y :=
  ConcreteCategory.ofHom ⟨Completion.extension f, Completion.uniformContinuous_extension⟩

@[simp]
/-
**UniformSpaceCat.extensionHom_val** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpaceCat`。
形式化陈述：extensionHom_val {X : UniformSpaceCat} {Y : CpltSepUniformSpace} (f : X ⟶ 
(forget₂ _ _).obj Y) (x) : (extensionHom f) x = Completion.extension f x
参数：f : X ⟶ (forget₂ _ _).obj Y；x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem extensionHom_val {X : UniformSpaceCat} {Y : CpltSepUniformSpace}
    (f : X ⟶ (forget₂ _ _).obj Y) (x) : (extensionHom f) x = Completion.extension f x :=
  rfl

@[simp]
/-
**UniformSpaceCat.extension_comp_hom** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpaceCat`
。
形式化陈述：extension_comp_hom {X : UniformSpaceCat} {Y : CpltSepUniformSpace} (f : to
UniformSpace (CpltSepUniformSpace.of (Completion X)) ⟶ toUniformSpace Y) : (exte
nsionHom (completionHom X ≫ f)).hom = f
参数：f : toUniformSpace (CpltSepUniformSpace.of (Completion X)) ⟶ toUniformSpace Y
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpaceCat.hom_ext`：hom_ext {X Y : UniformSpaceCat} {f g : X ⟶ Y} (
h : (f : X -> Y) = g) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `UniformSpace.Completion.extension_comp_coe`：extension_comp_coe {f : Comp
letion α -> β} (hf : UniformContinuous f) : Completion.extension (f ∘ (↑)) = f
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem extension_comp_hom {X : UniformSpaceCat} {Y : CpltSepUniformSpace}
    (f : toUniformSpace (CpltSepUniformSpace.of (Completion X)) ⟶ toUniformSpace Y) :
    (extensionHom (completionHom X ≫ f)).hom = f := by
  ext x
  exact congr_fun (Completion.extension_comp_coe f.hom.property) x

set_option backward.isDefEq.respectTransparency false in
/-- The completion functor is left adjoint to the forgetful functor. -/
/-
**UniformSpaceCat.adj** 是 Mathlib 中的一个定义，位于命名空间 `UniformSpaceCat`。
形式化陈述：adj : completionFunctor ⊣ forget₂ CpltSepUniformSpace UniformSpaceCat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The completion functor is left adjoint to the forgetful functor.
-/
noncomputable def adj : completionFunctor ⊣ forget₂ CpltSepUniformSpace UniformSpaceCat :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => completionHom X ≫ f.hom
          invFun := fun f => extensionHom f
          left_inv := fun f => InducedCategory.hom_ext (by simp)
          right_inv := fun f => by
            ext x
            rcases f with ⟨⟨_, _⟩⟩
            exact @Completion.extension_coe _ _ _ _ _ (CpltSepUniformSpace.t0Space _)
              ‹_› _ }
      homEquiv_naturality_left_symm := fun {X' X Y} f g => by
        ext x
        dsimp [-Function.comp_apply]
        erw [Completion.extension_map (γ := Y) g.hom.2 f.hom.2]
        rfl }
/-
**UniformSpaceCat.** 是 Mathlib 中的一个实例，位于命名空间 `UniformSpaceCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Reflective (forget₂ CpltSepUniformSpace UniformSpaceCat) where
  L := completionFunctor
  adj := adj
  map_surjective f := ⟨ConcreteCategory.ofHom f.hom, rfl⟩

open CategoryTheory.Limits

-- TODO Once someone defines `HasLimits UniformSpace`, turn this into an instance.
/-
**UniformSpaceCat.** 是 Mathlib 中的一个示例，位于命名空间 `UniformSpaceCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example [HasLimits.{u} UniformSpaceCat.{u}] : HasLimits.{u} CpltSepUniformSpace.{u} :=
  hasLimits_of_reflective <| forget₂ CpltSepUniformSpace UniformSpaceCat.{u}

end UniformSpaceCat

