/-
Copyright (c) 2025 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.StrictPseudofunctor

/-!

# Induced bicategories

In this file we develop API for constructing a full sub-bicategory of a bicategory `C`, given a
map `F : B → C`. The objects of the induced bicategory are the objects of `B`, while the
1-morphisms and 2-morphisms are taken as all corresponding morphisms in `C`.

## TODO

One might also want to develop "locally induced" bicategories, which should allow for a sub-class
of 1-morphisms as well. However, this needs more thought. If one tries the naive approach of simply
replacing the map `F` below with a "functor" (between `CategoryStruct`s), one runs into the issue
that `map_comp` and `map_id` might not be definitional equalities (which they should be in
practice). Hence one needs to carefully carry these around, or specify `F` in a way that ensures
they are def-eqs, perhaps constructing it from specified `MorphismProperty`s.
-/

@[expose] public section

namespace CategoryTheory.Bicategory

variable {B : Type*} (C : Type*) [Bicategory C] (F : B → C)

/-- `InducedBicategory B C`, where `F : B → C`, is a typeclass synonym for `B`. This is given
a bicategory structure where the 1-morphisms `X ⟶ Y` are the 1-morphisms in `C` from `F X` to
`F Y`, and the 2-morphisms `f ⟶ g` are also the 2-morphisms in `C` from `f` to `g`.
-/
@[nolint unusedArguments]
/-
**CategoryTheory.Bicategory.InducedBicategory** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Bicategory`。
形式化陈述：InducedBicategory (_F : B -> C)
参数：_F : B -> C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`InducedBicategory B C`, where `F : B → C`, is a typeclass synonym for `B`. This
 is given
a bicategory structure where the 1-morphisms `X ⟶ Y` are the 1-morphisms in `C` 
from `F X` to
`F Y`, and the 2-morphisms `f ⟶ g` are also the 2-morphisms in `C` from `f` to `
g`.
-/
def InducedBicategory (_F : B → C) :=
  B

namespace InducedBicategory

variable {C F}

/-
**CategoryTheory.Bicategory.InducedBicategory.hasCoeToSort** 是 Mathlib 中的一个实例，位于
命名空间 `CategoryTheory.Bicategory.InducedBicategory`。
形式化陈述：hasCoeToSort {α : Sort*} [CoeSort C α] : CoeSort (InducedBicategory C F) α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasCoeToSort {α : Sort*} [CoeSort C α] : CoeSort (InducedBicategory C F) α :=
  ⟨fun c => F c⟩

/-- `InducedBicategory.Hom X Y` is a type-alias for morphisms between `X Y : B` viewed as objects
of `B` with the induced bicategory structure. This is given a `CategoryStruct` instance below,
where the identity and composition is induced from `C`. -/
@[ext]
/-
**CategoryTheory.Bicategory.InducedBicategory.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `C
ategoryTheory.Bicategory.InducedBicategory`。
形式化陈述：{B : Type u_1} →   {C : Type u_2} →     [CategoryTheory.Bicategory C] →   
    {F : B → C} →         CategoryTheory.Bicategory.InducedBicategory C F → Cate
goryTheory.Bicategory.InducedBicategory C F → Type u_4
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`InducedBicategory.Hom X Y` is a type-alias for morphisms between `X Y : B` view
ed as objects
of `B` with the induced bicategory structure. This is given a `CategoryStruct` i
nstance below,
where the identity and composition is induced from `C`.
-/
structure Hom (X Y : InducedBicategory C F) where
  private mk ::
  /-- The morphism in `C` underlying the morphism in `InducedBicategory C F`. -/
  hom : F X ⟶ F Y

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[simps id_hom comp_hom]
/-
**CategoryTheory.Bicategory.InducedBicategory.categoryStruct** 是 Mathlib 中的一个实例，
位于命名空间 `CategoryTheory.Bicategory.InducedBicategory`。
形式化陈述：categoryStruct : CategoryStruct (InducedBicategory C F) where Hom X Y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance categoryStruct : CategoryStruct (InducedBicategory C F) where
  Hom X Y := Hom X Y
  id X := ⟨𝟙 (F X)⟩
  comp u v := ⟨u.hom ≫ v.hom⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Synonym for `Hom.mk` which makes unification easier. -/
/-
**CategoryTheory.Bicategory.InducedBicategory.mkHom** 是 Mathlib 中的一个缩写定义，位于命名空间 
`CategoryTheory.Bicategory.InducedBicategory`。
形式化陈述：mkHom {X Y : InducedBicategory C F} (f : F X ⟶ F Y) : X ⟶ Y
参数：f : F X ⟶ F Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Synonym for `Hom.mk` which makes unification easier.
-/
abbrev mkHom {X Y : InducedBicategory C F} (f : F X ⟶ F Y) : X ⟶ Y :=
  ⟨f⟩

@[ext]
/-
**CategoryTheory.Bicategory.InducedBicategory.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Bicategory.InducedBicategory`。
形式化陈述：hom_ext {X Y : InducedBicategory C F} {f g : X ⟶ Y} (h : f.hom = g.hom) : 
f = g
参数：h : f.hom = g.hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Bicategory.InducedBicategory.Hom.ext`：∀ {B : Type u_1} {C
 : Type u_2} {inst : CategoryTheory.Bicategory C} {F : B → C}   {X Y : CategoryT
heory.Bicategory.InducedBicategory C F} {…
-/
lemma hom_ext {X Y : InducedBicategory C F} {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g :=
  Hom.ext h

/-- `InducedBicategory.Hom₂ f g` is a type-alias for 2-morphisms between `f g : X ⟶ Y`, where
`f` and `g` are 1-morphisms for the induced bicategory structure on `B`.

This is given a `Category` instance below, induced from the corresponding one in `C`. -/
@[ext]
/-
**CategoryTheory.Bicategory.InducedBicategory.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `C
ategoryTheory.Bicategory.InducedBicategory`。
形式化陈述：{B : Type u_1} →   {C : Type u_2} →     [CategoryTheory.Bicategory C] →   
    {F : B → C} →         CategoryTheory.Bicategory.InducedBicategory C F → Cate
goryTheory.Bicategory.InducedBicategory C F → Type u_4
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`InducedBicategory.Hom₂ f g` is a type-alias for 2-morphisms between `f g : X ⟶ 
Y`, where
`f` and `g` are 1-morphisms for the induced bicategory structure on `B`.

This is given a `Category` instance below, induced from the corresponding one in
 `C`.
-/
structure Hom₂ {X Y : InducedBicategory C F} (f g : X ⟶ Y) where
  /-- The 2-morphism in `C` underlying the 2-morphism in `InducedBicategory C F`. -/
  hom : f.hom ⟶ g.hom

@[simps!]
/-
**CategoryTheory.Bicategory.InducedBicategory.Hom.category** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.Bicategory.InducedBicategory.Hom`。
形式化陈述：{B : Type u_1} →   {C : Type u_2} →     [inst : CategoryTheory.Bicategory 
C] →       {F : B → C} → (X Y : CategoryTheory.Bicategory.InducedBicategory C F)
 → CategoryTheory.Category.{u_3, u_4} (X ⟶ Y)
参数：X Y : CategoryTheory.Bicategory.InducedBicategory C F；X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Hom.category (X Y : InducedBicategory C F) : Category (X ⟶ Y) where
  Hom f g := Hom₂ f g
  id f := ⟨𝟙 f.hom⟩
  comp u v := ⟨u.hom ≫ v.hom⟩

@[ext]
/-
**CategoryTheory.Bicategory.InducedBicategory.hom** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Bicategory.InducedBicategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom₂_ext {X Y : InducedBicategory C F} {f g : X ⟶ Y} {η θ : f ⟶ g} (h : η.hom = θ.hom) :
    η = θ :=
  Hom₂.ext h

/-- Synonym for the constructor of `Hom₂` where the 1-morphisms `f` and `g` lie in `C`, and not
given in the form `f'.hom`, `g'.hom` for some `f' g' : InducedBicategory.Hom _ _`. -/
/-
**CategoryTheory.Bicategory.InducedBicategory.mkHom** 是 Mathlib 中的一个缩写定义，位于命名空间 
`CategoryTheory.Bicategory.InducedBicategory`。
形式化陈述：mkHom {X Y : InducedBicategory C F} (f : F X ⟶ F Y) : X ⟶ Y
参数：f : F X ⟶ F Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Synonym for the constructor of `Hom₂` where the 1-morphisms `f` and `g` lie in `
C`, and not
given in the form `f'.hom`, `g'.hom` for some `f' g' : InducedBicategory.Hom _ _
`.
-/
abbrev mkHom₂ {a b : InducedBicategory C F} {f g : F a ⟶ F b} (η : f ⟶ g) : mkHom f ⟶ mkHom g :=
  Hom₂.mk η

/-- Constructor for 2-isomorphisms in the induced bicategory. -/
@[simps!]
/-
**CategoryTheory.Bicategory.InducedBicategory.isoMk** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Bicategory.InducedBicategory`。
形式化陈述：isoMk {X Y : InducedBicategory C F} {f g : X ⟶ Y} (φ : f.hom ≅ g.hom) : f 
≅ g where hom
参数：φ : f.hom ≅ g.hom。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for 2-isomorphisms in the induced bicategory.
-/
def isoMk {X Y : InducedBicategory C F} {f g : X ⟶ Y} (φ : f.hom ≅ g.hom) : f ≅ g where
  hom := ⟨φ.hom⟩
  inv := ⟨φ.inv⟩

@[simps!]
/-
**CategoryTheory.Bicategory.InducedBicategory.bicategory** 是 Mathlib 中的一个实例，位于命名
空间 `CategoryTheory.Bicategory.InducedBicategory`。
形式化陈述：bicategory : Bicategory (InducedBicategory C F) where whiskerLeft {_ _ _} 
h {_ _} η
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance bicategory : Bicategory (InducedBicategory C F) where
  whiskerLeft {_ _ _} h {_ _} η := mkHom₂ <| h.hom ◁ Hom₂.hom η
  whiskerRight {_ _ _} {_ _} η h := mkHom₂ <| (Hom₂.hom η) ▷ h.hom
  associator x y z := isoMk (α_ x.hom y.hom z.hom)
  leftUnitor x := isoMk (λ_ x.hom)
  rightUnitor x := isoMk (ρ_ x.hom)
  whisker_exchange {_ _ _ _ _ _ _} η θ := by ext; simpa using whisker_exchange _ _

attribute [-simp] bicategory_comp_hom bicategory_Hom

section

/-- The forgetful (strict) pseudofunctor from an induced bicategory to the original bicategory,
forgetting the extra data.
-/
@[simps!]
/-
**CategoryTheory.Bicategory.InducedBicategory.forget** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Bicategory.InducedBicategory`。
形式化陈述：forget : StrictPseudofunctor (InducedBicategory C F) C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful (strict) pseudofunctor from an induced bicategory to the original 
bicategory,
forgetting the extra data.
-/
def forget : StrictPseudofunctor (InducedBicategory C F) C :=
  StrictPseudofunctor.mk' {
    obj X := F X
    map f := f.hom
    map₂ η := η.hom }

end

section

@[simp]
/-
**CategoryTheory.Bicategory.InducedBicategory.eqToHom_hom** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Bicategory.InducedBicategory`。
形式化陈述：eqToHom_hom {X Y : InducedBicategory C F} {f g : X ⟶ Y} (h : f = g) : (eqT
oHom h).hom = eqToHom (h ▸ rfl)
参数：h : f = g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma eqToHom_hom {X Y : InducedBicategory C F} {f g : X ⟶ Y} (h : f = g) :
    (eqToHom h).hom = eqToHom (h ▸ rfl) := by
  subst h; simp only [eqToHom_refl, Hom.category_id_hom]

@[simp]
/-
**CategoryTheory.Bicategory.InducedBicategory.mkHom_eqToHom** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.Bicategory.InducedBicategory`。
形式化陈述：mkHom_eqToHom {X Y : InducedBicategory C F} {f g : F X ⟶ F Y} (h : f = g) 
: mkHom₂ (eqToHom h) = eqToHom (h ▸ rfl)
参数：h : f = g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Bicategory.InducedBicategory.hom₂_ext`：hom₂_ext {X Y : In
ducedBicategory C F} {f g : X ⟶ Y} {η θ : f ⟶ g} (h : η.hom = θ.hom) : η = θ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mkHom_eqToHom {X Y : InducedBicategory C F} {f g : F X ⟶ F Y} (h : f = g) :
    mkHom₂ (eqToHom h) = eqToHom (h ▸ rfl) := by
  ext; subst h; simp only [eqToHom_refl, Hom.category_id_hom]

variable [Strict C]

attribute [local simp] Strict.leftUnitor_eqToIso Strict.rightUnitor_eqToIso
  Strict.associator_eqToIso
/-
**CategoryTheory.Bicategory.InducedBicategory.** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.Bicategory.InducedBicategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Strict (InducedBicategory C F) where

end

end InducedBicategory

end CategoryTheory.Bicategory

