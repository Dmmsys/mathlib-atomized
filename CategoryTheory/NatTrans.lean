/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Baumann, Stephen Morgan, Kim Morrison, Floris van Doorn
-/
module

public import Mathlib.Tactic.CategoryTheory.Reassoc

/-!
# Natural transformations

Defines natural transformations between functors.

A natural transformation `α : NatTrans F G` consists of morphisms `α.app X : F.obj X ⟶ G.obj X`,
and the naturality squares `α.naturality f : F.map f ≫ α.app Y = α.app X ≫ G.map f`,
where `f : X ⟶ Y`.

Note that we make `NatTrans.naturality` a simp lemma, with the preferred simp normal form
pushing components of natural transformations to the left.

See also `CategoryTheory.FunctorCat`, where we provide the category structure on
functors and natural transformations.

Introduces notations
* `τ.app X` for the components of natural transformations,
* `F ⟶ G` for the type of natural transformations between functors `F` and `G`
  (this and the next require `CategoryTheory.FunctorCat`),
* `σ ≫ τ` for vertical compositions, and
* `σ ◫ τ` for horizontal compositions.

-/

@[expose] public section

set_option mathlib.tactic.category.grind true

namespace CategoryTheory

-- declare the `v`'s first; see note [category theory universes].
universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

set_option linter.translate.warnInvalid false in
/-- `NatTrans F G` represents a natural transformation between functors `F` and `G`.

The field `app` provides the components of the natural transformation.

Naturality is expressed by `α.naturality`.
-/
@[ext, to_dual self (reorder := F G), wikidata Q1442189]
/-
**CategoryTheory.NatTrans** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory`。
形式化陈述：NatTrans (F G : C ⥤ D) : Type max u₁ v₂ where /-- The component of a natur
al transformation. -/ app (X : C) : F.obj X ⟶ G.obj X /-- The naturality square 
for a given morphism. -/ naturality ⦃X Y : C⦄ (f : X ⟶ Y) : F.map f ≫ app Y = ap
p X ≫ G.map f
参数：F G : C ⥤ D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`NatTrans F G` represents a natural transformation between functors `F` and `G`.

The field `app` provides the components of the natural transformation.

Naturality is expressed by `α.naturality`.
-/
structure NatTrans (F G : C ⥤ D) : Type max u₁ v₂ where
  /-- The component of a natural transformation. -/
  app (X : C) : F.obj X ⟶ G.obj X
  /-- The naturality square for a given morphism. -/
  naturality ⦃X Y : C⦄ (f : X ⟶ Y) : F.map f ≫ app Y = app X ≫ G.map f := by cat_disch

@[to_dual existing naturality]
/-
**CategoryTheory.NatTrans.naturality'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
NatTrans`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F G : CategoryTheory.Functor C 
D} (self : CategoryTheory.NatTrans G F) ⦃X Y : C⦄ (f : Y ⟶ X),   CategoryTheory.
CategoryStruct.comp (self.app Y) (F.map f) = CategoryTheory.CategoryStruct.comp 
(G.map f) (self.app X)
参数：self : CategoryTheory.NatTrans G F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
lemma NatTrans.naturality' {F G : C ⥤ D} (self : NatTrans G F) ⦃X Y : C⦄ (f : Y ⟶ X) :
    self.app Y ≫ F.map f = G.map f ≫ self.app X := (self.naturality f).symm

/-- `NatTrans.mk'` is the dual of `NatTrans.mk`, which we need for `to_dual`.
Please avoid using this directly. -/
@[to_dual existing mk]
/-
**CategoryTheory.NatTrans.mk'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.NatTrans
`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         {F G : C
ategoryTheory.Functor C D} →           (app : (X : C) → G.obj X ⟶ F.obj X) →    
         (∀ ⦃X Y : C⦄ (f : Y ⟶ X),                 CategoryTheory.CategoryStruct
.comp (app Y) (F.map f) =                   CategoryTheory.CategoryStruct.comp (
G.map f) (app X)) →               CategoryTheory.NatTrans G F
参数：app : (X : C) → G.obj X ⟶ F.obj X；∀ ⦃X Y : C⦄ (f : Y ⟶ X),                 Ca
tegoryTheory.CategoryStruct.comp (app Y) (F.map f) =                   CategoryT
heory.CategoryStruct.comp (G.map f) (app X)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`NatTrans.mk'` is the dual of `NatTrans.mk`, which we need for `to_dual`.
Please avoid using this directly.
-/
abbrev NatTrans.mk' {F G : C ⥤ D} (app : (X : C) → G.obj X ⟶ F.obj X)
    (naturality : ∀ ⦃X Y : C⦄ (f : Y ⟶ X), app Y ≫ F.map f = G.map f ≫ app X) : NatTrans G F where
  app

-- Rather arbitrarily, we say that the 'simpler' form is
-- components of natural transformations moving earlier.
attribute [reassoc (attr := simp)] NatTrans.naturality

attribute [grind _=_] NatTrans.naturality

@[to_dual self]
/-
**CategoryTheory.congr_app** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：congr_app {F G : C ⥤ D} {α β : NatTrans F G} (h : α = β) (X : C) : α.app X
 = β.app X
参数：h : α = β；X : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem congr_app {F G : C ⥤ D} {α β : NatTrans F G} (h : α = β) (X : C) : α.app X = β.app X := by
  cat_disch

namespace NatTrans

/-- `NatTrans.id F` is the identity natural transformation on a functor `F`. -/
@[implicit_reducible]
/-
**CategoryTheory.NatTrans.id** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.NatTrans`
。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] → (F : CategoryThe
ory.Functor C D) → CategoryTheory.NatTrans F F
参数：F : CategoryTheory.Functor C D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`NatTrans.id F` is the identity natural transformation on a functor `F`.
-/
protected def id (F : C ⥤ D) : NatTrans F F where app X := 𝟙 (F.obj X)

@[simp]
/-
**CategoryTheory.NatTrans.id_app'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.NatT
rans`。
形式化陈述：id_app' (F : C ⥤ D) (X : C) : (NatTrans.id F).app X = 𝟙 (F.obj X)
参数：F : C ⥤ D；X : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_app' (F : C ⥤ D) (X : C) : (NatTrans.id F).app X = 𝟙 (F.obj X) := rfl
/-
**CategoryTheory.NatTrans.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.NatTrans`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ D) : Inhabited (NatTrans F F) := ⟨NatTrans.id F⟩

open Category

open CategoryTheory.Functor

section

variable {F G H : C ⥤ D}

/-- `vcomp α β` is the vertical compositions of natural transformations. -/
@[to_dual self (reorder := F H, α β)]
/-
**CategoryTheory.NatTrans.vcomp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.NatTra
ns`。
形式化陈述：vcomp (α : NatTrans F G) (β : NatTrans G H) : NatTrans F H where app X
参数：α : NatTrans F G；β : NatTrans G H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`vcomp α β` is the vertical compositions of natural transformations.
-/
def vcomp (α : NatTrans F G) (β : NatTrans G H) : NatTrans F H where
  app X := α.app X ≫ β.app X

-- functor_category will rewrite (vcomp α β) to (α ≫ β), so this is not a
-- suitable simp lemma.  We will declare the variant vcomp_app' there.
@[to_dual self]
/-
**CategoryTheory.NatTrans.vcomp_app** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Na
tTrans`。
形式化陈述：vcomp_app (α : NatTrans F G) (β : NatTrans G H) (X : C) : (vcomp α β).app 
X = α.app X ≫ β.app X
参数：α : NatTrans F G；β : NatTrans G H；X : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem vcomp_app (α : NatTrans F G) (β : NatTrans G H) (X : C) :
    (vcomp α β).app X = α.app X ≫ β.app X := rfl

attribute [grind =] vcomp_app

end

/-- The diagram
```
    F(f)      F(g)      F(h)
F X ----> F Y ----> F U ----> F V
 |         |         |         |
 | α(X)    | α(Y)    | α(U)    | α(V)
 v         v         v         v
G X ----> G Y ----> G U ----> G V
    G(f)      G(g)      G(h)
```
commutes.
-/
/-
**CategoryTheory.NatTrans.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.NatTrans`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The diagram
```
    F(f)      F(g)      F(h)
F X ----> F Y ----> F U ----> F V
 |         |         |         |
 | α(X)    | α(Y)    | α(U)    | α(V)
 v         v         v         v
G X ----> G Y ----> G U ----> G V
    G(f)      G(g)      G(h)
```
commutes.
-/
example {F G : C ⥤ D} (α : NatTrans F G) {X Y U V : C} (f : X ⟶ Y) (g : Y ⟶ U) (h : U ⟶ V) :
    α.app X ≫ G.map f ≫ G.map g ≫ G.map h = F.map f ≫ F.map g ≫ F.map h ≫ α.app V := by
  grind

end NatTrans

end CategoryTheory

