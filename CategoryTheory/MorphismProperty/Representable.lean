/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne, Joël Riou, Ravi Vakil
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!

# Relatively representable morphisms

In this file we define and develop basic results about relatively representable morphisms.

Classically, a morphism `f : F ⟶ G` of presheaves is said to be representable if for any morphism
`g : yoneda.obj X ⟶ G`, there exists a pullback square of the following form
```
  yoneda.obj Y --yoneda.map snd--> yoneda.obj X
      |                                |
     fst                               g
      |                                |
      v                                v
      F ------------ f --------------> G
```

In this file, we define a notion of relative representability which works with respect to any
functor, and not just `yoneda`. The fact that a morphism `f : F ⟶ G` between presheaves is
representable in the classical case will then be given by `yoneda.relativelyRepresentable f`.

## Main definitions

Throughout this file, `F : C ⥤ D` is a functor between categories `C` and `D`.

* `Functor.relativelyRepresentable`: A morphism `f : X ⟶ Y` in `D` is said to be relatively
  representable with respect to `F`, if for any `g : F.obj a ⟶ Y`, there exists a pullback square
  of the following form
  ```
  F.obj b --F.map snd--> F.obj a
      |                     |
     fst                    g
      |                     |
      v                     v
      X ------- f --------> Y
  ```

* `MorphismProperty.relative`: Given a morphism property `P` in `C`, a morphism `f : X ⟶ Y` in `D`
  satisfies `P.relative F` if it is relatively representable and for any `g : F.obj a ⟶ Y`, the
  property `P` holds for any represented pullback of `f` by `g`.

## API

Given `hf : relativelyRepresentable f`, with `f : X ⟶ Y` and `g : F.obj a ⟶ Y`, we provide:
* `hf.pullback g` which is the object in `C` such that `F.obj (hf.pullback g)` is a
  pullback of `f` and `g`.
* `hf.snd g` is the morphism `hf.pullback g ⟶ F.obj a`
* `hf.fst g` is the morphism `F.obj (hf.pullback g) ⟶ X`
* If `F` is full, and `f` is of type `F.obj c ⟶ G`, we also have `hf.fst' g : hf.pullback g ⟶ X`
  which is the preimage under `F` of `hf.fst g`.
* `hom_ext`, `hom_ext'`, `lift`, `lift'` are variants of the universal property of
  `F.obj (hf.pullback g)`, where as much as possible has been formulated internally to `C`.
  For these theorems we also need that `F` is full and/or faithful.
* `symmetry` and `symmetryIso` are variants of the fact that pullbacks are symmetric for
  representable morphisms, formulated internally to `C`. We assume that `F` is fully faithful here.

We also provide some basic API for dealing with triple pullbacks, i.e. given
`hf₁ : relativelyRepresentable f₁`, `f₂ : F.obj A₂ ⟶ X` and `f₃ : F.obj A₃ ⟶ X`, we define
`hf₁.pullback₃ f₂ f₃` to be the pullback of `(A₁ ×_X A₂) ×_{A₁} (A₁ ×_X A₃)`. We then develop
some API for working with this object, mirroring the usual API for pullbacks, but where as much
as possible is phrased internally to `C`.

## Main results

* `relativelyRepresentable.isMultiplicative`: The class of relatively representable morphisms is
  multiplicative.
* `relativelyRepresentable.isStableUnderBaseChange`: Being relatively representable is stable under
  base change.
* `relativelyRepresentable.of_isIso`: Isomorphisms are relatively representable.

-/

@[expose] public section

namespace CategoryTheory

open Category Limits MorphismProperty

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)

/-- A morphism `f : X ⟶ Y` in `D` is said to be relatively representable if for any
`g : F.obj a ⟶ Y`, there exists a pullback square of the following form
```
F.obj b --F.map snd--> F.obj a
    |                     |
   fst                    g
    |                     |
    v                     v
    X ------- f --------> Y
```
-/
/-
**CategoryTheory.Functor.relativelyRepresentable** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Functor`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] → CategoryTheory.F
unctor C D → CategoryTheory.MorphismProperty D
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism `f : X ⟶ Y` in `D` is said to be relatively representable if for any
`g : F.obj a ⟶ Y`, there exists a pullback square of the following form
```
F.obj b --F.map snd--> F.obj a
    |                     |
   fst                    g
    |                     |
    v                     v
    X ------- f --------> Y
```
-/
def Functor.relativelyRepresentable : MorphismProperty D :=
  fun X Y f ↦ ∀ ⦃a : C⦄ (g : F.obj a ⟶ Y), ∃ (b : C) (snd : b ⟶ a)
    (fst : F.obj b ⟶ X), IsPullback fst (F.map snd) f g

namespace Functor.relativelyRepresentable

section

variable {F}
variable {X Y : D} {f : X ⟶ Y} (hf : F.relativelyRepresentable f)
  {b : C} {f' : F.obj b ⟶ Y} (hf' : F.relativelyRepresentable f')
  {a : C} (g : F.obj a ⟶ Y) (hg : F.relativelyRepresentable g)

/-- Let `f : X ⟶ Y` be a relatively representable morphism in `D`. Then, for any
`g : F.obj a ⟶ Y`, `hf.pullback g` denotes the (choice of) a corresponding object in `C` such that
there is a pullback square of the following form
```
hf.pullback g --F.map snd--> F.obj a
    |                          |
   fst                         g
    |                          |
    v                          v
    X ---------- f ----------> Y
``` -/
/-
**CategoryTheory.Functor.relativelyRepresentable.pullback** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Functor.relativelyRepresentable`。
形式化陈述：pullback : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `f : X ⟶ Y` be a relatively representable morphism in `D`. Then, for any
`g : F.obj a ⟶ Y`, `hf.pullback g` denotes the (choice of) a corresponding objec
t in `C` such that
there is a pullback square of the following form
```
hf.pullback g --F.map snd--> F.obj a
    |                          |
   fst                         g
    |                          |
    v                          v
    X ---------- f ----------> Y
```
-/
noncomputable def pullback : C :=
  (hf g).choose

/-- Given a representable morphism `f : X ⟶ Y`, then for any `g : F.obj a ⟶ Y`, `hf.snd g`
denotes the morphism in `C` giving rise to the following diagram
```
hf.pullback g --F.map (hf.snd g)--> F.obj a
    |                                 |
   fst                                g
    |                                 |
    v                                 v
    X -------------- f -------------> Y
``` -/
/-
**CategoryTheory.Functor.relativelyRepresentable.snd** 是 Mathlib 中的一个缩写定义，位于命名空间
 `CategoryTheory.Functor.relativelyRepresentable`。
形式化陈述：snd : hf.pullback g ⟶ a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a representable morphism `f : X ⟶ Y`, then for any `g : F.obj a ⟶ Y`, `hf.
snd g`
denotes the morphism in `C` giving rise to the following diagram
```
hf.pullback g --F.map (hf.snd g)--> F.obj a
    |                                 |
   fst                                g
    |                                 |
    v                                 v
    X -------------- f -------------> Y
```
-/
noncomputable abbrev snd : hf.pullback g ⟶ a :=
  (hf g).choose_spec.choose

/-- Given a relatively representable morphism `f : X ⟶ Y`, then for any `g : F.obj a ⟶ Y`,
`hf.fst g` denotes the first projection in the following diagram, given by the defining property
of `f` being relatively representable
```
hf.pullback g --F.map (hf.snd g)--> F.obj a
    |                                 |
hf.fst g                              g
    |                                 |
    v                                 v
    X -------------- f -------------> Y
``` -/
/-
**CategoryTheory.Functor.relativelyRepresentable.fst** 是 Mathlib 中的一个缩写定义，位于命名空间
 `CategoryTheory.Functor.relativelyRepresentable`。
形式化陈述：fst : F.obj (hf.pullback g) ⟶ X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a relatively representable morphism `f : X ⟶ Y`, then for any `g : F.obj a
 ⟶ Y`,
`hf.fst g` denotes the first projection in the following diagram, given by the d
efining property
of `f` being relatively representable
```
hf.pullback g --F.map (hf.snd g)--> F.obj a
    |                                 |
hf.fst g                              g
    |                                 |
    v                                 v
    X -------------- f -------------> Y
```
-/
noncomputable abbrev fst : F.obj (hf.pullback g) ⟶ X :=
  (hf g).choose_spec.choose_spec.choose

/-- When `F` is full, given a representable morphism `f' : F.obj b ⟶ Y`, then `hf'.fst' g` denotes
the preimage of `hf'.fst g` under `F`. -/
/-
**CategoryTheory.Functor.relativelyRepresentable.fst'** 是 Mathlib 中的一个缩写定义，位于命名空
间 `CategoryTheory.Functor.relativelyRepresentable`。
形式化陈述：fst' [Full F] : hf'.pullback g ⟶ b
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `F` is full, given a representable morphism `f' : F.obj b ⟶ Y`, then `hf'.f
st' g` denotes
the preimage of `hf'.fst g` under `F`.
-/
noncomputable abbrev fst' [Full F] : hf'.pullback g ⟶ b :=
  F.preimage (hf'.fst g)
/-
**CategoryTheory.Functor.relativelyRepresentable.map_fst'** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Functor.relativelyRepresentable`。
形式化陈述：map_fst' [Full F] : F.map (hf'.fst' g) = hf'.fst g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_preimage`：map_preimage (F : C ⥤ D) [Full F] {
X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage F f) = f
-/
lemma map_fst' [Full F] : F.map (hf'.fst' g) = hf'.fst g :=
  F.map_preimage _
/-
**CategoryTheory.Functor.relativelyRepresentable.isPullback** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.Functor.relativelyRepresentable`。
形式化陈述：isPullback : IsPullback (hf.fst g) (F.map (hf.snd g)) f g
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma isPullback : IsPullback (hf.fst g) (F.map (hf.snd g)) f g :=
  (hf g).choose_spec.choose_spec.choose_spec

@[reassoc]
/-
**CategoryTheory.Functor.relativelyRepresentable.w** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Functor.relativelyRepresentable`。
形式化陈述：w : hf.fst g ≫ f = F.map (hf.snd g) ≫ g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `CategoryTheory.IsPullback.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}   
{g : Y ⟶ Z}, CategoryThe…
· 使用引理 `CategoryTheory.Functor.relativelyRepresentable.isPullback`：isPullback : 
IsPullback (hf.fst g) (F.map (hf.snd g)) f g
-/
lemma w : hf.fst g ≫ f = F.map (hf.snd g) ≫ g := (hf.isPullback g).w

/-- Variant of the pullback square when `F` is full, and given `f' : F.obj b ⟶ Y`. -/
/-
**CategoryTheory.Functor.relativelyRepresentable.isPullback'** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Functor.relativelyRepresentable`。
形式化陈述：isPullback' [Full F] : IsPullback (F.map (hf'.fst' g)) (F.map (hf'.snd g))
 f' g
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.relativelyRepresentable.isPullback`：isPullback : 
IsPullback (hf.fst g) (F.map (hf.snd g)) f g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Functor.relativelyRepresentable.map_fst'`：map_fst' [Full 
F] : F.map (hf'.fst' g) = hf'.fst g

--- 原说明 ---
Variant of the pullback square when `F` is full, and given `f' : F.obj b ⟶ Y`.
-/
lemma isPullback' [Full F] : IsPullback (F.map (hf'.fst' g)) (F.map (hf'.snd g)) f' g :=
  (hf'.map_fst' _) ▸ hf'.isPullback g

@[reassoc]
/-
**CategoryTheory.Functor.relativelyRepresentable.w'** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Functor.relativelyRepresentable`。
形式化陈述：w' {X Y Z : C} {f : X ⟶ Z} (hf : F.relativelyRepresentable (F.map f)) (g :
 Y ⟶ Z) [Full F] [Faithful F] : hf.fst' (F.map g) ≫ f = hf.snd (F.map g) ≫ g
参数：hf : F.relativelyRepresentable (F.map f)；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_preimage`：map_preimage (F : C ⥤ D) [Full F] {
X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage F f) = f
· 使用引理 `CategoryTheory.Functor.relativelyRepresentable.w`：w : hf.fst g ≫ f = F.m
ap (hf.snd g) ≫ g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma w' {X Y Z : C} {f : X ⟶ Z} (hf : F.relativelyRepresentable (F.map f)) (g : Y ⟶ Z)
    [Full F] [Faithful F] : hf.fst' (F.map g) ≫ f = hf.snd (F.map g) ≫ g :=
  F.map_injective <| by simp [(hf.w (F.map g))]
/-
**CategoryTheory.Functor.relativelyRepresentable.isPullback_of_map** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.Functor.relativelyRepresentable`。
形式化陈述：isPullback_of_map {X Y Z : C} {f : X ⟶ Z} (hf : F.relativelyRepresentable 
(F.map f)) (g : Y ⟶ Z) [Full F] [Faithful F] : IsPullback (hf.fst' (F.map g)) (h
f.snd (F.map g)) f g
参数：hf : F.relativelyRepresentable (F.map f)；g : Y ⟶ Z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.of_map`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D
]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.reflectsLimit_of_reflectsLimitsOfShape`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Catego
ryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.reflectsLimitsOfShape_of_reflectsLimits`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categ
oryTheory.Category.{v₂, u₂} D]   (J : Type w) [inst…
· 使用引理 `CategoryTheory.Functor.relativelyRepresentable.w'`：w' {X Y Z : C} {f : X
 ⟶ Z} (hf : F.relativelyRepresentable (F.map f)) (g : Y ⟶ Z) [Full F] [Faithful 
F] : hf.fst' (F.map g) ≫ f = hf.snd (F.…
· 使用引理 `CategoryTheory.Functor.relativelyRepresentable.isPullback'`：isPullback' 
[Full F] : IsPullback (F.map (hf'.fst' g)) (F.map (hf'.snd g)) f' g
-/
lemma isPullback_of_map {X Y Z : C} {f : X ⟶ Z} (hf : F.relativelyRepresentable (F.map f))
    (g : Y ⟶ Z) [Full F] [Faithful F] :
    IsPullback (hf.fst' (F.map g)) (hf.snd (F.map g)) f g :=
  IsPullback.of_map F (hf.w' g) (hf.isPullback' (F.map g))

variable {g}

/-- Two morphisms `a b : c ⟶ hf.pullback g` are equal if
* Their compositions (in `C`) with `hf.snd g : hf.pullback  ⟶ X` are equal.
* The compositions of `F.map a` and `F.map b` with `hf.fst g` are equal. -/
@[ext 100]
/-
**CategoryTheory.Functor.relativelyRepresentable.hom_ext** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Functor.relativelyRepresentable`。
形式化陈述：hom_ext [Faithful F] {c : C} {a b : c ⟶ hf.pullback g} (h₁ : F.map a ≫ hf.
fst g = F.map b ≫ hf.fst g) (h₂ : a ≫ hf.snd g = b ≫ hf.snd g) : a = b
参数：h₁ : F.map a ≫ hf.fst g = F.map b ≫ hf.fst g；h₂ : a ≫ hf.snd g = b ≫ hf.snd g
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `CategoryTheory.Limits.PullbackCone.IsLimit.hom_ext`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   {t : 
CategoryTheory.Limits.PullbackCone f g} …
· 使用引理 `CategoryTheory.Functor.relativelyRepresentable.isPullback`：isPullback : 
IsPullback (hf.fst g) (F.map (hf.snd g)) f g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Functor.congr_map`：congr_map (F : C ⥤ D) {X Y : C} {f g :
 X ⟶ Y} (h : f = g) : F.map f = F.map g

--- 原说明 ---
Two morphisms `a b : c ⟶ hf.pullback g` are equal if
* Their compositions (in `C`) with `hf.snd g : hf.pullback  ⟶ X` are equal.
* The compositions of `F.map a` and `F.map b` with `hf.fst g` are equal.
-/
lemma hom_ext [Faithful F] {c : C} {a b : c ⟶ hf.pullback g}
    (h₁ : F.map a ≫ hf.fst g = F.map b ≫ hf.fst g)
    (h₂ : a ≫ hf.snd g = b ≫ hf.snd g) : a = b :=
  F.map_injective <|
    PullbackCone.IsLimit.hom_ext (hf.isPullback g).isLimit h₁ (by simpa using! F.congr_map h₂)

/-- In the case of a representable morphism `f' : F.obj Y ⟶ G`, whose codomain lies
in the image of `F`, we get that two morphism `a b : Z ⟶ hf.pullback g` are equal if
* Their compositions (in `C`) with `hf'.snd g : hf.pullback  ⟶ X` are equal.
* Their compositions (in `C`) with `hf'.fst' g : hf.pullback  ⟶ Y` are equal. -/
@[ext]
/-
**CategoryTheory.Functor.relativelyRepresentable.hom_ext'** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Functor.relativelyRepresentable`。
形式化陈述：hom_ext' [Full F] [Faithful F] {c : C} {a b : c ⟶ hf'.pullback g} (h₁ : a 
≫ hf'.fst' g = b ≫ hf'.fst' g) (h₂ : a ≫ hf'.snd g = b ≫ hf'.snd g) : a = b
参数：h₁ : a ≫ hf'.fst' g = b ≫ hf'.fst' g；h₂ : a ≫ hf'.snd g = b ≫ hf'.snd g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.relativelyRepresentable.hom_ext`：hom_ext [Faithfu
l F] {c : C} {a b : c ⟶ hf.pullback g} (h₁ : F.map a ≫ hf.fst g = F.map b ≫ hf.f
st g) (h₂ : a ≫ hf.snd g = b ≫ hf.snd g) : a…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Functor.map_preimage`：map_preimage (F : C ⥤ D) [Full F] {
X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage F f) = f
· 使用定理 `CategoryTheory.Functor.congr_map`：congr_map (F : C ⥤ D) {X Y : C} {f g :
 X ⟶ Y} (h : f = g) : F.map f = F.map g

--- 原说明 ---
In the case of a representable morphism `f' : F.obj Y ⟶ G`, whose codomain lies
in the image of `F`, we get that two morphism `a b : Z ⟶ hf.pullback g` are equa
l if
* Their compositions (in `C`) with `hf'.snd g : hf.pullback  ⟶ X` are equal.
* Their compositions (in `C`) with `hf'.fst' g : hf.pullback  ⟶ Y` are equal.
-/
lemma hom_ext' [Full F] [Faithful F] {c : C} {a b : c ⟶ hf'.pullback g}
    (h₁ : a ≫ hf'.fst' g = b ≫ hf'.fst' g)
    (h₂ : a ≫ hf'.snd g = b ≫ hf'.snd g) : a = b :=
  hf'.hom_ext (by simpa [map_fst'] using F.congr_map h₁) h₂

section

variable {c : C} (i : F.obj c ⟶ X) (h : c ⟶ a) (hi : i ≫ f = F.map h ≫ g)

/-- The lift (in `C`) obtained from the universal property of `F.obj (hf.pullback g)`, in the
case when the cone point is in the image of `F.obj`. -/
/-
**CategoryTheory.Functor.relativelyRepresentable.lift** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Functor.relativelyRepresentable`。
形式化陈述：lift [Full F] : c ⟶ hf.pullback g
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.relativelyRepresentable.isPullback`：isPullback : 
IsPullback (hf.fst g) (F.map (hf.snd g)) f g

--- 原说明 ---
The lift (in `C`) obtained from the universal property of `F.obj (hf.pullback g)
`, in the
case when the cone point is in the image of `F.obj`.
-/
noncomputable def lift [Full F] : c ⟶ hf.pullback g :=
  F.preimage <| PullbackCone.IsLimit.lift (hf.isPullback g).isLimit _ _ hi

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.relativelyRepresentable.lift_fst** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Functor.relativelyRepresentable`。
形式化陈述：lift_fst [Full F] : F.map (hf.lift i h hi) ≫ hf.fst g = i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.relativelyRepresentable.isPullback`：isPullback : 
IsPullback (hf.fst g) (F.map (hf.snd g)) f g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_preimage`：map_preimage (F : C ⥤ D) [Full F] {
X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage F f) = f
· 使用定理 `CategoryTheory.Limits.PullbackCone.IsLimit.lift_fst`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   {t :
 CategoryTheory.Limits.PullbackCone f g} …
-/
lemma lift_fst [Full F] : F.map (hf.lift i h hi) ≫ hf.fst g = i := by
  simpa [lift] using! PullbackCone.IsLimit.lift_fst _ _ _ _

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.relativelyRepresentable.lift_snd** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Functor.relativelyRepresentable`。
形式化陈述：lift_snd [Full F] [Faithful F] : hf.lift i h hi ≫ hf.snd g = h
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用引理 `CategoryTheory.Functor.relativelyRepresentable.isPullback`：isPullback : 
IsPullback (hf.fst g) (F.map (hf.snd g)) f g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Functor.map_preimage`：map_preimage (F : C ⥤ D) [Full F] {
X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage F f) = f
· 使用定理 `CategoryTheory.Limits.PullbackCone.IsLimit.lift_snd`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   {t :
 CategoryTheory.Limits.PullbackCone f g} …
-/
lemma lift_snd [Full F] [Faithful F] : hf.lift i h hi ≫ hf.snd g = h :=
  F.map_injective <| by simpa [lift] using! PullbackCone.IsLimit.lift_snd _ _ _ _

end

section

variable {c : C} (i : c ⟶ b) (h : c ⟶ a) (hi : F.map i ≫ f' = F.map h ≫ g)

/-- Variant of `lift` in the case when the domain of `f` lies in the image of `F.obj`. Thus,
in this case, one can obtain the lift directly by giving two morphisms in `C`. -/
/-
**CategoryTheory.Functor.relativelyRepresentable.lift'** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Functor.relativelyRepresentable`。
形式化陈述：lift' [Full F] : c ⟶ hf'.pullback g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Variant of `lift` in the case when the domain of `f` lies in the image of `F.obj
`. Thus,
in this case, one can obtain the lift directly by giving two morphisms in `C`.
-/
noncomputable def lift' [Full F] : c ⟶ hf'.pullback g := hf'.lift _ _ hi

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.relativelyRepresentable.lift'_fst** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Functor.relativelyRepresentable`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F : CategoryTheory.Functor C D}
 {Y : D} {b : C} {f' : F.obj b ⟶ Y} (hf' : F.relativelyRepresentable f') {a : C}
   {g : F.obj a ⟶ Y} {c : C} (i : c ⟶ b) (h : c ⟶ a)   (hi : CategoryTheory.Cate
goryStruct.comp (F.map i) f' = CategoryTheory.CategoryStruct.comp (F.map h) g)  
 [inst_2 : F.Full] [F.Faithful], CategoryTheory.CategoryStruct.comp (hf'.lift' i
 h hi) (hf'.fst' g) = i
参数：hf' : F.relativelyRepresentable f'；i : c ⟶ b；h : c ⟶ a；hi : CategoryTheory.Ca
tegoryStruct.comp (F.map i) f' = CategoryTheory.CategoryStruct.comp (F.map h) g；
hf'.lift' i h hi；hf'.fst' g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Functor.map_preimage`：map_preimage (F : C ⥤ D) [Full F] {
X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage F f) = f
· 使用引理 `CategoryTheory.Functor.relativelyRepresentable.lift_fst`：lift_fst [Full 
F] : F.map (hf.lift i h hi) ≫ hf.fst g = i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lift'_fst [Full F] [Faithful F] : hf'.lift' i h hi ≫ hf'.fst' g = i :=
  F.map_injective (by simp [lift'])

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.relativelyRepresentable.lift'_snd** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Functor.relativelyRepresentable`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F : CategoryTheory.Functor C D}
 {Y : D} {b : C} {f' : F.obj b ⟶ Y} (hf' : F.relativelyRepresentable f') {a : C}
   {g : F.obj a ⟶ Y} {c : C} (i : c ⟶ b) (h : c ⟶ a)   (hi : CategoryTheory.Cate
goryStruct.comp (F.map i) f' = CategoryTheory.CategoryStruct.comp (F.map h) g)  
 [inst_2 : F.Full] [F.Faithful], CategoryTheory.CategoryStruct.comp (hf'.lift' i
 h hi) (hf'.snd g) = h
参数：hf' : F.relativelyRepresentable f'；i : c ⟶ b；h : c ⟶ a；hi : CategoryTheory.Ca
tegoryStruct.comp (F.map i) f' = CategoryTheory.CategoryStruct.comp (F.map h) g；
hf'.lift' i h hi；hf'.snd g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.relativelyRepresentable.lift_snd`：lift_snd [Full 
F] [Faithful F] : hf.lift i h hi ≫ hf.snd g = h
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lift'_snd [Full F] [Faithful F] : hf'.lift' i h hi ≫ hf'.snd g = h := by
  simp [lift']

end

/-- Given two representable morphisms `f' : F.obj b ⟶ Y` and `g : F.obj a ⟶ Y`, we
obtain an isomorphism `hf'.pullback g ⟶ hg.pullback f'`. -/
/-
**CategoryTheory.Functor.relativelyRepresentable.symmetry** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Functor.relativelyRepresentable`。
形式化陈述：symmetry [Full F] : hf'.pullback g ⟶ hg.pullback f'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two representable morphisms `f' : F.obj b ⟶ Y` and `g : F.obj a ⟶ Y`, we
obtain an isomorphism `hf'.pullback g ⟶ hg.pullback f'`.
-/
noncomputable def symmetry [Full F] : hf'.pullback g ⟶ hg.pullback f' :=
  hg.lift' (hf'.snd g) (hf'.fst' g) (hf'.isPullback' _).w.symm

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.relativelyRepresentable.symmetry_fst** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.Functor.relativelyRepresentable`。
形式化陈述：symmetry_fst [Full F] [Faithful F] : hf'.symmetry hg ≫ hg.fst' f' = hf'.sn
d g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.relativelyRepresentable.lift'_fst`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma symmetry_fst [Full F] [Faithful F] : hf'.symmetry hg ≫ hg.fst' f' = hf'.snd g := by
  simp [symmetry]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.relativelyRepresentable.symmetry_snd** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.Functor.relativelyRepresentable`。
形式化陈述：symmetry_snd [Full F] [Faithful F] : hf'.symmetry hg ≫ hg.snd f' = hf'.fst
' g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.relativelyRepresentable.lift'_snd`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma symmetry_snd [Full F] [Faithful F] : hf'.symmetry hg ≫ hg.snd f' = hf'.fst' g := by
  simp [symmetry]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.relativelyRepresentable.symmetry_symmetry** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.Functor.relativelyRepresentable`。
形式化陈述：symmetry_symmetry [Full F] [Faithful F] : hf'.symmetry hg ≫ hg.symmetry hf
' = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.relativelyRepresentable.hom_ext'`：hom_ext' [Full 
F] [Faithful F] {c : C} {a b : c ⟶ hf'.pullback g} (h₁ : a ≫ hf'.fst' g = b ≫ hf
'.fst' g) (h₂ : a ≫ hf'.snd g = b ≫ hf'.snd g…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.Functor.relativelyRepresentable.symmetry_fst`：symmetry_fs
t [Full F] [Faithful F] : hf'.symmetry hg ≫ hg.fst' f' = hf'.snd g
· 使用引理 `CategoryTheory.Functor.relativelyRepresentable.symmetry_snd`：symmetry_sn
d [Full F] [Faithful F] : hf'.symmetry hg ≫ hg.snd f' = hf'.fst' g
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma symmetry_symmetry [Full F] [Faithful F] : hf'.symmetry hg ≫ hg.symmetry hf' = 𝟙 _ :=
  hom_ext' hf' (by simp) (by simp)

/-- The isomorphism given by `Presheaf.representable.symmetry`. -/
@[simps]
/-
**CategoryTheory.Functor.relativelyRepresentable.symmetryIso** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.Functor.relativelyRepresentable`。
形式化陈述：symmetryIso [Full F] [Faithful F] : hf'.pullback g ≅ hg.pullback f' where 
hom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism given by `Presheaf.representable.symmetry`.
-/
noncomputable def symmetryIso [Full F] [Faithful F] : hf'.pullback g ≅ hg.pullback f' where
  hom := hf'.symmetry hg
  inv := hg.symmetry hf'
/-
**CategoryTheory.Functor.relativelyRepresentable.** 是 Mathlib 中的一个实例，位于命名空间 `Cat
egoryTheory.Functor.relativelyRepresentable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Full F] [Faithful F] : IsIso (hf'.symmetry hg) :=
  (hf'.symmetryIso hg).isIso_hom

end

/-- When `C` has pullbacks, then `F.map f` is representable with respect to `F` for any
`f : a ⟶ b` in `C`. -/
/-
**CategoryTheory.Functor.relativelyRepresentable.map** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Functor.relativelyRepresentable`。
形式化陈述：map [Full F] [HasPullbacks C] {a b : C} (f : a ⟶ b) [forall c (g : c ⟶ b),
 PreservesLimit (cospan f g) F] : F.relativelyRepresentable (F.map f)
参数：f : a ⟶ b；g : c ⟶ b；cospan f g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_surjective`：map_surjective (F : C ⥤ D) [Full 
F] : Function.Surjective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Functor.map_isPullback`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, 
u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.IsPullback.of_hasPullback`：of_hasPullback (f : X ⟶ Z) (g 
: Y ⟶ Z) [HasPullback f g] : IsPullback (pullback.fst f g) (pullback.snd f g) f 
g

--- 原说明 ---
When `C` has pullbacks, then `F.map f` is representable with respect to `F` for 
any
`f : a ⟶ b` in `C`.
-/
lemma map [Full F] [HasPullbacks C] {a b : C} (f : a ⟶ b)
    [∀ c (g : c ⟶ b), PreservesLimit (cospan f g) F] :
    F.relativelyRepresentable (F.map f) := fun c g ↦ by
  obtain ⟨g, rfl⟩ := F.map_surjective g
  refine ⟨Limits.pullback f g, Limits.pullback.snd f g, F.map (Limits.pullback.fst f g), ?_⟩
  apply F.map_isPullback <| IsPullback.of_hasPullback f g
/-
**CategoryTheory.Functor.relativelyRepresentable.of_isIso** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Functor.relativelyRepresentable`。
形式化陈述：of_isIso {X Y : D} (f : X ⟶ Y) [IsIso f] : F.relativelyRepresentable f
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.of_vert_isIso`：of_vert_isIso [IsIso snd] [IsIs
o f] (sq : CommSq fst snd f g) : IsPullback fst snd f g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma of_isIso {X Y : D} (f : X ⟶ Y) [IsIso f] : F.relativelyRepresentable f :=
  fun a g ↦ ⟨a, 𝟙 a, g ≫ CategoryTheory.inv f, IsPullback.of_vert_isIso ⟨by simp⟩⟩
/-
**CategoryTheory.Functor.relativelyRepresentable.isomorphisms_le** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.Functor.relativelyRepresentable`。
形式化陈述：isomorphisms_le : MorphismProperty.isomorphisms D <= F.relativelyRepresent
able
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.relativelyRepresentable.of_isIso`：of_isIso {X Y :
 D} (f : X ⟶ Y) [IsIso f] : F.relativelyRepresentable f
-/
lemma isomorphisms_le : MorphismProperty.isomorphisms D ≤ F.relativelyRepresentable :=
  fun _ _ f hf ↦ letI : IsIso f := hf; of_isIso F f
/-
**CategoryTheory.Functor.relativelyRepresentable.isMultiplicative** 是 Mathlib 中的
一个实例，位于命名空间 `CategoryTheory.Functor.relativelyRepresentable`。
形式化陈述：isMultiplicative : IsMultiplicative F.relativelyRepresentable where id_mem
 _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.relativelyRepresentable.of_isIso`：of_isIso {X Y :
 D} (f : X ⟶ Y) [IsIso f] : F.relativelyRepresentable f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.IsPullback.paste_vert`：paste_vert {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃
₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {
v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂…
· 使用引理 `CategoryTheory.Functor.relativelyRepresentable.isPullback`：isPullback : 
IsPullback (hf.fst g) (F.map (hf.snd g)) f g
-/
instance isMultiplicative : IsMultiplicative F.relativelyRepresentable where
  id_mem _ := of_isIso F _
  comp_mem {F G H} f g hf hg := fun X h ↦
    ⟨hf.pullback (hg.fst h), hf.snd (hg.fst h) ≫ hg.snd h, hf.fst (hg.fst h),
      by simpa using IsPullback.paste_vert (hf.isPullback (hg.fst h)) (hg.isPullback h)⟩
/-
**CategoryTheory.Functor.relativelyRepresentable.isStableUnderBaseChange** 是 Mat
hlib 中的一个实例，位于命名空间 `CategoryTheory.Functor.relativelyRepresentable`。
形式化陈述：isStableUnderBaseChange : IsStableUnderBaseChange F.relativelyRepresentabl
e where of_isPullback {X Y Y' X' f g f' g'} P₁ hg a h
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.Functor.relativelyRepresentable.w`：w : hf.fst g ≫ f = F.m
ap (hf.snd g) ≫ g
· 使用定理 `CategoryTheory.IsPullback.of_right'`：of_right' {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ 
: C} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃} {h₁₃ : X₁₁ ⟶ X₁₃} {v₁
₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂…
· 使用引理 `CategoryTheory.Functor.relativelyRepresentable.isPullback`：isPullback : 
IsPullback (hf.fst g) (F.map (hf.snd g)) f g
-/
instance isStableUnderBaseChange : IsStableUnderBaseChange F.relativelyRepresentable where
  of_isPullback {X Y Y' X' f g f' g'} P₁ hg a h := by
    refine ⟨hg.pullback (h ≫ f), hg.snd (h ≫ f), ?_, ?_⟩
    · apply P₁.lift (hg.fst (h ≫ f)) (F.map (hg.snd (h ≫ f)) ≫ h) (by simpa using hg.w (h ≫ f))
    · apply IsPullback.of_right' (hg.isPullback (h ≫ f)) P₁
/-
**CategoryTheory.Functor.relativelyRepresentable.respectsIso** 是 Mathlib 中的一个实例，
位于命名空间 `CategoryTheory.Functor.relativelyRepresentable`。
形式化陈述：respectsIso : RespectsIso F.relativelyRepresentable
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderBaseChange.respectsIso`：∀ {
C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.Morphi
smProperty C}   [P.IsStableUnderBaseChange], P.RespectsIs…
-/
instance respectsIso : RespectsIso F.relativelyRepresentable :=
  (isStableUnderBaseChange F).respectsIso

end Functor.relativelyRepresentable

namespace MorphismProperty

open Functor.relativelyRepresentable

variable {X Y : D} (P : MorphismProperty C)

/-- Given a morphism property `P` in a category `C`, a functor `F : C ⥤ D` and a morphism
`f : X ⟶ Y` in `D`. Then `f` satisfies the morphism property `P.relative` with respect to `F` iff:
* The morphism is representable with respect to `F`
* For any morphism `g : F.obj a ⟶ Y`, the property `P` holds for any represented pullback of
  `f` by `g`. -/
/-
**CategoryTheory.MorphismProperty.relative** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.MorphismProperty`。
形式化陈述：relative : MorphismProperty D
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a morphism property `P` in a category `C`, a functor `F : C ⥤ D` and a mor
phism
`f : X ⟶ Y` in `D`. Then `f` satisfies the morphism property `P.relative` with r
espect to `F` iff:
* The morphism is representable with respect to `F`
* For any morphism `g : F.obj a ⟶ Y`, the property `P` holds for any represented
 pullback of
  `f` by `g`.
-/
def relative : MorphismProperty D :=
  fun X Y f ↦ F.relativelyRepresentable f ∧
    ∀ ⦃a b : C⦄ (g : F.obj a ⟶ Y) (fst : F.obj b ⟶ X) (snd : b ⟶ a)
      (_ : IsPullback fst (F.map snd) f g), P snd

/-- Given a morphism property `P` in a category `C`, a morphism `f : F ⟶ G` of presheaves in the
category `Cᵒᵖ ⥤ Type v` satisfies the morphism property `P.presheaf` iff:
* The morphism is representable.
* For any morphism `g : F.obj a ⟶ G`, the property `P` holds for any represented pullback of
  `f` by `g`.

This is implemented as a special case of the more general notion of `P.relative`, to the case when
the functor `F` is `yoneda`. -/
/-
**CategoryTheory.MorphismProperty.presheaf** 是 Mathlib 中的一个缩写定义，位于命名空间 `Category
Theory.MorphismProperty`。
形式化陈述：presheaf : MorphismProperty (Cᵒᵖ ⥤ Type v₁)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a morphism property `P` in a category `C`, a morphism `f : F ⟶ G` of presh
eaves in the
category `Cᵒᵖ ⥤ Type v` satisfies the morphism property `P.presheaf` iff:
* The morphism is representable.
* For any morphism `g : F.obj a ⟶ G`, the property `P` holds for any represented
 pullback of
  `f` by `g`.

This is implemented as a special case of the more general notion of `P.relative`
, to the case when
the functor `F` is `yoneda`.
-/
abbrev presheaf : MorphismProperty (Cᵒᵖ ⥤ Type v₁) := P.relative yoneda

variable {P} {F}

/-- A morphism satisfying `P.relative` is representable. -/
/-
**CategoryTheory.MorphismProperty.relative.rep** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.MorphismProperty.relative`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F : CategoryTheory.Functor C D}
 {X Y : D} {P : CategoryTheory.MorphismProperty C} {f : X ⟶ Y},   CategoryTheory
.MorphismProperty.relative F P f → F.relativelyRepresentable f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
A morphism satisfying `P.relative` is representable.
-/
lemma relative.rep {f : X ⟶ Y} (hf : P.relative F f) : F.relativelyRepresentable f :=
  hf.1
/-
**CategoryTheory.MorphismProperty.relative.property** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.MorphismProperty.relative`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F : CategoryTheory.Functor C D}
 {X Y : D} {P : CategoryTheory.MorphismProperty C} {f : X ⟶ Y},   CategoryTheory
.MorphismProperty.relative F P f →     ∀ ⦃a b : C⦄ (g : F.obj a ⟶ Y) (fst : F.ob
j b ⟶ X) (snd : b ⟶ a),       CategoryTheory.IsPullback fst (F.map snd) f g → P 
snd
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma relative.property {f : X ⟶ Y} (hf : P.relative F f) :
    ∀ ⦃a b : C⦄ (g : F.obj a ⟶ Y) (fst : F.obj b ⟶ X) (snd : b ⟶ a)
    (_ : IsPullback fst (F.map snd) f g), P snd :=
  hf.2
/-
**CategoryTheory.MorphismProperty.relative.property_snd** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.MorphismProperty.relative`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F : CategoryTheory.Functor C D}
 {X Y : D} {P : CategoryTheory.MorphismProperty C} {f : X ⟶ Y}   (hf : CategoryT
heory.MorphismProperty.relative F P f) {a : C} (g : F.obj a ⟶ Y), P (⋯.snd g)
参数：hf : CategoryTheory.MorphismProperty.relative F P f；g : F.obj a ⟶ Y；⋯.snd g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.relative.property`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.MorphismProperty.relative.rep`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D]   {F : CategoryTheor…
· 使用引理 `CategoryTheory.Functor.relativelyRepresentable.isPullback`：isPullback : 
IsPullback (hf.fst g) (F.map (hf.snd g)) f g
-/
lemma relative.property_snd {f : X ⟶ Y} (hf : P.relative F f) {a : C} (g : F.obj a ⟶ Y) :
    P (hf.rep.snd g) :=
  hf.property g _ _ (hf.rep.isPullback g)

set_option backward.defeqAttrib.useBackward true in
/-- Given a morphism property `P` which respects isomorphisms, then to show that a morphism
`f : X ⟶ Y` satisfies `P.relative` it suffices to show that:
* The morphism is representable.
* For any morphism `g : F.obj a ⟶ G`, the property `P` holds for *some* represented pullback
  of `f` by `g`. -/
/-
**CategoryTheory.MorphismProperty.relative.of_exists** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.MorphismProperty.relative`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F : CategoryTheory.Functor C D}
 {X Y : D} {P : CategoryTheory.MorphismProperty C} [F.Faithful] [F.Full]   [P.Re
spectsIso] {f : X ⟶ Y},   (∀ ⦃a : C⦄ (g : F.obj a ⟶ Y), ∃ b fst snd, ∃ (_ : Cate
goryTheory.IsPullback fst (F.map snd) f g), P snd) →     CategoryTheory.Morphism
Property.relative F P f
参数：∀ ⦃a : C⦄ (g : F.obj a ⟶ Y), ∃ b fst snd, ∃ (_ : CategoryTheory.IsPullback fs
t (F.map snd) f g), P snd。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_preimage`：map_preimage (F : C ⥤ D) [Full F] {
X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage F f) = f
· 使用定理 `CategoryTheory.IsPullback.isoIsPullback_hom_snd`：isoIsPullback_hom_snd (
h : IsPullback fst snd f g) (h' : IsPullback fst' snd' f g) : (h.isoIsPullback _
 _ h').hom ≫ snd' = snd
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Given a morphism property `P` which respects isomorphisms, then to show that a m
orphism
`f : X ⟶ Y` satisfies `P.relative` it suffices to show that:
* The morphism is representable.
* For any morphism `g : F.obj a ⟶ G`, the property `P` holds for *some* represen
ted pullback
  of `f` by `g`.
-/
lemma relative.of_exists [F.Faithful] [F.Full] [P.RespectsIso] {f : X ⟶ Y}
    (h₀ : ∀ ⦃a : C⦄ (g : F.obj a ⟶ Y), ∃ (b : C) (fst : F.obj b ⟶ X) (snd : b ⟶ a)
      (_ : IsPullback fst (F.map snd) f g), P snd) : P.relative F f := by
  refine ⟨fun a g ↦ ?_, fun a b g fst snd h ↦ ?_⟩
  all_goals obtain ⟨c, g_fst, g_snd, BC, H⟩ := h₀ g
  · refine ⟨c, g_snd, g_fst, BC⟩
  · refine (P.arrow_mk_iso_iff ?_).2 H
    exact Arrow.isoMk (F.preimageIso (h.isoIsPullback X (F.obj a) BC)) (Iso.refl _)
      (F.map_injective (by simp))
/-
**CategoryTheory.MorphismProperty.relative_of_snd** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.MorphismProperty`。
形式化陈述：relative_of_snd [F.Faithful] [F.Full] [P.RespectsIso] {f : X ⟶ Y} (hf : F.
relativelyRepresentable f) (h : forall ⦃a : C⦄ (g : F.obj a ⟶ Y), P (hf.snd g)) 
: P.relative F f
参数：hf : F.relativelyRepresentable f；h : forall ⦃a : C⦄ (g : F.obj a ⟶ Y), P (hf.
snd g)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.relative.of_exists`：∀ {C : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.C
ategory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用引理 `CategoryTheory.Functor.relativelyRepresentable.isPullback`：isPullback : 
IsPullback (hf.fst g) (F.map (hf.snd g)) f g
-/
lemma relative_of_snd [F.Faithful] [F.Full] [P.RespectsIso] {f : X ⟶ Y}
    (hf : F.relativelyRepresentable f) (h : ∀ ⦃a : C⦄ (g : F.obj a ⟶ Y), P (hf.snd g)) :
    P.relative F f :=
  relative.of_exists (fun _ g ↦ ⟨hf.pullback g, hf.fst g, hf.snd g, hf.isPullback g, h g⟩)

/-- If `P : MorphismProperty C` is stable under base change, `F` is fully faithful and preserves
pullbacks, and `C` has all pullbacks, then for any `f : a ⟶ b` in `C`, `F.map f` satisfies
`P.relative` if `f` satisfies `P`. -/
/-
**CategoryTheory.MorphismProperty.relative_map** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.MorphismProperty`。
形式化陈述：relative_map [F.Faithful] [F.Full] [HasPullbacks C] [IsStableUnderBaseChan
ge P] {a b : C} {f : a ⟶ b} [forall c (g : c ⟶ b), PreservesLimit (cospan f g) F
] (hf : P f) : P.relative F (F.map f)
参数：g : c ⟶ b；cospan f g；hf : P f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.relative.of_exists`：∀ {C : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.C
ategory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderBaseChange.respectsIso`：∀ {
C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.Morphi
smProperty C}   [P.IsStableUnderBaseChange], P.RespectsIs…
· 使用定理 `CategoryTheory.Functor.map_surjective`：map_surjective (F : C ⥤ D) [Full 
F] : Function.Surjective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.IsPullback.map`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (F : CategoryTheor…
· 使用定理 `CategoryTheory.IsPullback.of_hasPullback`：of_hasPullback (f : X ⟶ Z) (g 
: Y ⟶ Z) [HasPullback f g] : IsPullback (pullback.fst f g) (pullback.snd f g) f 
g
· 使用定理 `CategoryTheory.MorphismProperty.pullback_snd`：pullback_snd {X Y S : C} (
f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g] [P.IsStableUnderBaseChangeAlong g] (H :
 P f) : P (pullback.snd f g)
· 使用定理 `CategoryTheory.MorphismProperty.instIsStableUnderBaseChangeAlongOfIsStab
leUnderBaseChange`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P :
 CategoryTheory.MorphismProperty C)   [P.IsStableUnderBaseChange] {X Y : C} (f …

--- 原说明 ---
If `P : MorphismProperty C` is stable under base change, `F` is fully faithful a
nd preserves
pullbacks, and `C` has all pullbacks, then for any `f : a ⟶ b` in `C`, `F.map f`
 satisfies
`P.relative` if `f` satisfies `P`.
-/
lemma relative_map [F.Faithful] [F.Full] [HasPullbacks C] [IsStableUnderBaseChange P]
    {a b : C} {f : a ⟶ b} [∀ c (g : c ⟶ b), PreservesLimit (cospan f g) F]
    (hf : P f) : P.relative F (F.map f) := by
  apply relative.of_exists
  intro Y' g
  obtain ⟨g, rfl⟩ := F.map_surjective g
  exact ⟨_, _, _, (IsPullback.of_hasPullback f g).map F, P.pullback_snd _ _ hf⟩
/-
**CategoryTheory.MorphismProperty.of_relative_map** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.MorphismProperty`。
形式化陈述：of_relative_map {a b : C} {f : a ⟶ b} (hf : P.relative F (F.map f)) : P f
参数：hf : P.relative F (F.map f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.relative.property`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用引理 `CategoryTheory.IsPullback.id_horiz`：id_horiz (f : X ⟶ Z) : IsPullback (𝟙
 X) f f (𝟙 Z)
-/
lemma of_relative_map {a b : C} {f : a ⟶ b} (hf : P.relative F (F.map f)) : P f :=
  hf.property (𝟙 _) (𝟙 _) f (IsPullback.id_horiz (F.map f))
/-
**CategoryTheory.MorphismProperty.relative_map_iff** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.MorphismProperty`。
形式化陈述：relative_map_iff [F.Faithful] [F.Full] [PreservesLimitsOfShape WalkingCosp
an F] [HasPullbacks C] [IsStableUnderBaseChange P] {X Y : C} {f : X ⟶ Y} : P.rel
ative F (F.map f) ↔ P f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.of_relative_map`：of_relative_map {a b : 
C} {f : a ⟶ b} (hf : P.relative F (F.map f)) : P f
· 使用引理 `CategoryTheory.MorphismProperty.relative_map`：relative_map [F.Faithful] 
[F.Full] [HasPullbacks C] [IsStableUnderBaseChange P] {a b : C} {f : a ⟶ b} [for
all c (g : c ⟶ b), PreservesLimit …
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
-/
lemma relative_map_iff [F.Faithful] [F.Full] [PreservesLimitsOfShape WalkingCospan F]
    [HasPullbacks C] [IsStableUnderBaseChange P] {X Y : C} {f : X ⟶ Y} :
    P.relative F (F.map f) ↔ P f :=
  ⟨fun hf ↦ of_relative_map hf, fun hf ↦ relative_map hf⟩

/-- If `P' : MorphismProperty C` is satisfied whenever `P` is, then also `P'.relative` is
satisfied whenever `P.relative` is. -/
/-
**CategoryTheory.MorphismProperty.relative_monotone** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.MorphismProperty`。
形式化陈述：relative_monotone {P' : MorphismProperty C} (h : P <= P') : P.relative F <
= P'.relative F
参数：h : P <= P'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.relative.rep`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.MorphismProperty.relative.property`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {F : CategoryTheor…

--- 原说明 ---
If `P' : MorphismProperty C` is satisfied whenever `P` is, then also `P'.relativ
e` is
satisfied whenever `P.relative` is.
-/
lemma relative_monotone {P' : MorphismProperty C} (h : P ≤ P') :
    P.relative F ≤ P'.relative F := fun _ _ _ hf ↦
  ⟨hf.rep, fun _ _ g fst snd BC ↦ h _ (hf.property g fst snd BC)⟩

section

variable (P)

/-
**CategoryTheory.MorphismProperty.relative_isStableUnderBaseChange** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：relative_isStableUnderBaseChange : IsStableUnderBaseChange (P.relative F) 
where of_isPullback hfBC hg
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.of_isPullback`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismProperty C}   [self 
: P.IsStableUnderBaseChange] {X Y Y…
· 使用定理 `CategoryTheory.MorphismProperty.relative.rep`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.MorphismProperty.relative.property`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.IsPullback.paste_horiz`：paste_horiz {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ 
X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃}
 {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X…
-/
lemma relative_isStableUnderBaseChange : IsStableUnderBaseChange (P.relative F) where
  of_isPullback hfBC hg :=
    ⟨of_isPullback hfBC hg.rep,
      fun _ _ _ _ _ BC ↦ hg.property _ _ _ (IsPullback.paste_horiz BC hfBC)⟩
/-
**CategoryTheory.MorphismProperty.relative_isStableUnderComposition** 是 Mathlib 
中的一个实例，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：relative_isStableUnderComposition [F.Faithful] [F.Full] [P.IsStableUnderCo
mposition] : IsStableUnderComposition (P.relative F) where comp_mem {F G H} f g 
hf hg
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.comp_mem`：comp_mem (W : MorphismProperty
 C) [W.IsStableUnderComposition] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) 
(hg : W g) : W (f ≫ g)
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `CategoryTheory.IsPullback.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}   
{g : Y ⟶ Z}, CategoryThe…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Functor.relativelyRepresentable.lift_snd`：lift_snd [Full 
F] [Faithful F] : hf.lift i h hi ≫ hf.snd g = h
· 使用定理 `CategoryTheory.MorphismProperty.relative.property`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.IsPullback.of_bot`：of_bot {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {
h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁
₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ …
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用引理 `CategoryTheory.Functor.relativelyRepresentable.lift_fst`：lift_fst [Full 
F] : F.map (hf.lift i h hi) ≫ hf.fst g = i
· 使用引理 `CategoryTheory.Functor.relativelyRepresentable.isPullback`：isPullback : 
IsPullback (hf.fst g) (F.map (hf.snd g)) f g
· 使用定理 `CategoryTheory.MorphismProperty.relative.property_snd`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheor
y.Category.{v₂, u₂} D]   {F : CategoryTheor…
-/
instance relative_isStableUnderComposition [F.Faithful] [F.Full] [P.IsStableUnderComposition] :
    IsStableUnderComposition (P.relative F) where
  comp_mem {F G H} f g hf hg := by
    refine ⟨comp_mem _ _ _ hf.1 hg.1, fun Z X p fst snd h ↦ ?_⟩
    rw [← hg.1.lift_snd (fst ≫ f) snd (by simpa using h.w)]
    refine comp_mem _ _ _ (hf.property (hg.1.fst p) fst _
      (IsPullback.of_bot ?_ ?_ (hg.1.isPullback p))) (hg.property_snd p)
    · rw [← Functor.map_comp, lift_snd]
      exact h
    · symm
      apply hg.1.lift_fst
/-
**CategoryTheory.MorphismProperty.relative_respectsIso** 是 Mathlib 中的一个实例，位于命名空间
 `CategoryTheory.MorphismProperty`。
形式化陈述：relative_respectsIso : RespectsIso (P.relative F)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderBaseChange.respectsIso`：∀ {
C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.Morphi
smProperty C}   [P.IsStableUnderBaseChange], P.RespectsIs…
· 使用引理 `CategoryTheory.MorphismProperty.relative_isStableUnderBaseChange`：relati
ve_isStableUnderBaseChange : IsStableUnderBaseChange (P.relative F) where of_isP
ullback hfBC hg
-/
instance relative_respectsIso : RespectsIso (P.relative F) :=
  (relative_isStableUnderBaseChange P).respectsIso
/-
**CategoryTheory.MorphismProperty.relative_isMultiplicative** 是 Mathlib 中的一个实例，位
于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：relative_isMultiplicative [F.Faithful] [F.Full] [P.IsMultiplicative] [P.Re
spectsIso] : IsMultiplicative (P.relative F) where id_mem X
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.relative.of_exists`：∀ {C : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.C
ategory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用引理 `CategoryTheory.IsPullback.of_id_snd`：of_id_snd : IsPullback f (𝟙 _) (𝟙 _
) f
· 使用引理 `CategoryTheory.MorphismProperty.id_mem`：id_mem (W : MorphismProperty C) 
[W.ContainsIdentities] (X : C) : W (𝟙 X)
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toContainsIdentities`：∀
 {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheory.Morp
hismProperty C}   [self : W.IsMultiplicative], W.ContainsId…
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
-/
instance relative_isMultiplicative [F.Faithful] [F.Full] [P.IsMultiplicative] [P.RespectsIso] :
    IsMultiplicative (P.relative F) where
  id_mem X := relative.of_exists
    (fun Y g ↦ ⟨Y, g, 𝟙 Y, by simpa using IsPullback.of_id_snd, id_mem _ _⟩)

end

section

-- TODO(Calle): This could be generalized to functors whose image forms a separating family.
/-- Morphisms satisfying `(monomorphism C).presheaf` are in particular monomorphisms. -/
/-
**CategoryTheory.MorphismProperty.presheaf_monomorphisms_le_monomorphisms** 是 Ma
thlib 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：presheaf_monomorphisms_le_monomorphisms : (monomorphisms C).presheaf <= mo
nomorphisms _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.relative.rep`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MorphismProperty.relative.property_snd`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheor
y.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用引理 `CategoryTheory.Functor.relativelyRepresentable.lift_snd`：lift_snd [Full 
F] [Faithful F] : hf.lift i h hi ≫ hf.snd g = h
· 使用引理 `CategoryTheory.Functor.relativelyRepresentable.lift_fst`：lift_fst [Full 
F] : F.map (hf.lift i h hi) ≫ hf.fst g = i
· 使用定理 `CategoryTheory.eq_whisker`：eq_whisker {f g : X ⟶ Y} (w : f = g) (h : Y ⟶
 Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.Functor.congr_map`：congr_map (F : C ⥤ D) {X Y : C} {f g :
 X ⟶ Y} (h : f = g) : F.map f = F.map g
· 使用引理 `CategoryTheory.hom_ext_yoneda`：hom_ext_yoneda {P Q : Cᵒᵖ ⥤ Type v₁} {f g
 : P ⟶ Q} (h : forall (X : C) (p : yoneda.obj X ⟶ P), p ≫ f = p ≫ g) : f = g
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…

--- 原说明 ---
Morphisms satisfying `(monomorphism C).presheaf` are in particular monomorphisms
.
-/
lemma presheaf_monomorphisms_le_monomorphisms :
    (monomorphisms C).presheaf ≤ monomorphisms _ := fun F G f hf ↦ by
  suffices ∀ {X : C} {a b : yoneda.obj X ⟶ F}, a ≫ f = b ≫ f → a = b from
    ⟨fun _ _ h ↦ hom_ext_yoneda (fun _ _ ↦ this (by simp only [assoc, h]))⟩
  intro X a b h
  /- It suffices to show that the lifts of `a` and `b` to morphisms
  `X ⟶ hf.rep.pullback g` are equal, where `g = a ≫ f = a ≫ f`. -/
  suffices hf.rep.lift (g := a ≫ f) a (𝟙 X) (by simp) =
      hf.rep.lift b (𝟙 X) (by simp [← h]) by
    simpa using yoneda.congr_map this =≫ (hf.rep.fst (a ≫ f))
  -- This follows from the fact that the induced maps `hf.rep.pullback g ⟶ X` are mono.
  have : Mono (hf.rep.snd (a ≫ f)) := hf.property_snd (a ≫ f)
  simp only [← cancel_mono (hf.rep.snd (a ≫ f)), lift_snd]

variable {G : Cᵒᵖ ⥤ Type v₁}
/-
**CategoryTheory.MorphismProperty.presheaf_mono_of_le** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.MorphismProperty`。
形式化陈述：presheaf_mono_of_le (hP : P <= MorphismProperty.monomorphisms C) {X : C} {
f : yoneda.obj X ⟶ G} (hf : P.presheaf f) : Mono f
参数：hP : P <= MorphismProperty.monomorphisms C；hf : P.presheaf f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.presheaf_monomorphisms_le_monomorphisms`
：presheaf_monomorphisms_le_monomorphisms : (monomorphisms C).presheaf <= monomor
phisms _
· 使用引理 `CategoryTheory.MorphismProperty.relative_monotone`：relative_monotone {P'
 : MorphismProperty C} (h : P <= P') : P.relative F <= P'.relative F
-/
lemma presheaf_mono_of_le (hP : P ≤ MorphismProperty.monomorphisms C)
    {X : C} {f : yoneda.obj X ⟶ G} (hf : P.presheaf f) : Mono f :=
  MorphismProperty.presheaf_monomorphisms_le_monomorphisms _
    (MorphismProperty.relative_monotone hP _ hf)
/-
**CategoryTheory.MorphismProperty.fst'_self_eq_snd** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.MorphismProperty`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryT
heory.MorphismProperty C}   {G : CategoryTheory.Functor Cᵒᵖ (Type v₁)},   P ≤ Ca
tegoryTheory.MorphismProperty.monomorphisms C →     ∀ {X : C} {f : CategoryTheor
y.yoneda.obj X ⟶ G} (hf : P.presheaf f), ⋯.fst' f = ⋯.snd f
参数：Type v₁；hf : P.presheaf f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.presheaf_mono_of_le`：presheaf_mono_of_le
 (hP : P <= MorphismProperty.monomorphisms C) {X : C} {f : yoneda.obj X ⟶ G} (hf
 : P.presheaf f) : Mono f
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `CategoryTheory.MorphismProperty.relative.rep`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `CategoryTheory.IsPullback.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}   
{g : Y ⟶ Z}, CategoryThe…
· 使用引理 `CategoryTheory.Functor.relativelyRepresentable.isPullback'`：isPullback' 
[Full F] : IsPullback (F.map (hf'.fst' g)) (F.map (hf'.snd g)) f' g
-/
lemma fst'_self_eq_snd (hP : P ≤ MorphismProperty.monomorphisms C)
    {X : C} {f : yoneda.obj X ⟶ G} (hf : P.presheaf f) : hf.rep.fst' f = hf.rep.snd f := by
  have := P.presheaf_mono_of_le hP hf
  apply yoneda.map_injective
  rw [← cancel_mono f, (hf.rep.isPullback' f).w]
/-
**CategoryTheory.MorphismProperty.isIso_fst'_self** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.MorphismProperty`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryT
heory.MorphismProperty C}   {G : CategoryTheory.Functor Cᵒᵖ (Type v₁)},   P ≤ Ca
tegoryTheory.MorphismProperty.monomorphisms C →     ∀ {X : C} {f : CategoryTheor
y.yoneda.obj X ⟶ G} (hf : P.presheaf f), CategoryTheory.IsIso (⋯.fst' f)
参数：Type v₁；hf : P.presheaf f；⋯.fst' f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.presheaf_mono_of_le`：presheaf_mono_of_le
 (hP : P <= MorphismProperty.monomorphisms C) {X : C} {f : yoneda.obj X ⟶ G} (hf
 : P.presheaf f) : Mono f
· 使用定理 `CategoryTheory.MorphismProperty.relative.rep`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D]   {F : CategoryTheor…
· 使用引理 `CategoryTheory.IsPullback.isIso_fst_of_mono`：isIso_fst_of_mono (h : IsPu
llback fst snd f f) (inst : Mono f
· 使用引理 `CategoryTheory.Functor.relativelyRepresentable.isPullback'`：isPullback' 
[Full F] : IsPullback (F.map (hf'.fst' g)) (F.map (hf'.snd g)) f' g
· 使用引理 `CategoryTheory.Functor.FullyFaithful.isIso_of_isIso_map`：isIso_of_isIso_
map {X Y : C} (f : X ⟶ Y) [IsIso (F.map f)] : IsIso f
-/
lemma isIso_fst'_self (hP : P ≤ MorphismProperty.monomorphisms C)
    {X : C} {f : yoneda.obj X ⟶ G} (hf : P.presheaf f) : IsIso (hf.rep.fst' f) :=
  have := P.presheaf_mono_of_le hP hf
  have := (hf.rep.isPullback' f).isIso_fst_of_mono
  Yoneda.fullyFaithful.isIso_of_isIso_map _

end

end MorphismProperty

namespace Functor.relativelyRepresentable

section Pullbacks₃
/-
In this section we develop some basic API that help deal with certain triple pullbacks obtained
from morphism `f₁ : F.obj A₁ ⟶ X` which is relatively representable with respect to some functor
`F : C ⥤ D`.

More precisely, given two objects `A₂` and `A₃` in `C`, and two morphisms `f₂ : A₂ ⟶ X` and
`f₃ : A₃ ⟶ X`, we can consider the pullbacks (in `D`) `(A₁ ×_X A₂)` and `(A₁ ×_X A₃)`
(which makes sense as objects in `C` due to `F` being relatively representable).

We can then consider the pullback, in `C`, of these two pullbacks. This is the object
`(A₁ ×_X A₂) ×_{A₁} (A₁ ×_X A₃)`. In this section we develop some basic API for dealing with this
pullback. This is used in `Mathlib/AlgebraicGeometry/Sites/Representability.lean` to show that
representability is Zariski-local.
-/
variable {F : C ⥤ D} [Full F] {A₁ A₂ A₃ : C} {X : D}
  {f₁ : F.obj A₁ ⟶ X} (hf₁ : F.relativelyRepresentable f₁)
  (f₂ : F.obj A₂ ⟶ X) (f₃ : F.obj A₃ ⟶ X)
  [HasPullback (hf₁.fst' f₂) (hf₁.fst' f₃)]

/-- The pullback `(A₁ ×_X A₂) ×_{A₁} (A₁ ×_X A₃)`. -/
/-
**CategoryTheory.Functor.relativelyRepresentable.pullback** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Functor.relativelyRepresentable`。
形式化陈述：pullback : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback `(A₁ ×_X A₂) ×_{A₁} (A₁ ×_X A₃)`.
-/
noncomputable def pullback₃ := Limits.pullback (hf₁.fst' f₂) (hf₁.fst' f₃)
/-- The morphism `(A₁ ×_X A₂) ×_{A₁} (A₁ ×_X A₃) ⟶ A₁`. -/
/-
**CategoryTheory.Functor.relativelyRepresentable.pullback** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Functor.relativelyRepresentable`。
形式化陈述：pullback : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `(A₁ ×_X A₂) ×_{A₁} (A₁ ×_X A₃) ⟶ A₁`.
-/
noncomputable def pullback₃.p₁ : hf₁.pullback₃ f₂ f₃ ⟶ A₁ := pullback.fst _ _ ≫ hf₁.fst' f₂
/-- The morphism `(A₁ ×_X A₂) ×_{A₁} (A₁ ×_X A₃) ⟶ A₂`. -/
/-
**CategoryTheory.Functor.relativelyRepresentable.pullback** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Functor.relativelyRepresentable`。
形式化陈述：pullback : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `(A₁ ×_X A₂) ×_{A₁} (A₁ ×_X A₃) ⟶ A₂`.
-/
noncomputable def pullback₃.p₂ : hf₁.pullback₃ f₂ f₃ ⟶ A₂ := pullback.fst _ _ ≫ hf₁.snd f₂
/-- The morphism `(A₁ ×_X A₂) ×_{A₁} (A₁ ×_X A₃) ⟶ A₃`. -/
/-
**CategoryTheory.Functor.relativelyRepresentable.pullback** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Functor.relativelyRepresentable`。
形式化陈述：pullback : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `(A₁ ×_X A₂) ×_{A₁} (A₁ ×_X A₃) ⟶ A₃`.
-/
noncomputable def pullback₃.p₃ : hf₁.pullback₃ f₂ f₃ ⟶ A₃ := pullback.snd _ _ ≫ hf₁.snd f₃

/-- The morphism `F.obj (A₁ ×_X A₂) ×_{A₁} (A₁ ×_X A₃) ⟶ X`. -/
/-
**CategoryTheory.Functor.relativelyRepresentable.pullback** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Functor.relativelyRepresentable`。
形式化陈述：pullback : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `F.obj (A₁ ×_X A₂) ×_{A₁} (A₁ ×_X A₃) ⟶ X`.
-/
noncomputable def pullback₃.π : F.obj (pullback₃ hf₁ f₂ f₃) ⟶ X :=
  F.map (p₁ hf₁ f₂ f₃) ≫ f₁

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.relativelyRepresentable.pullback** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Functor.relativelyRepresentable`。
形式化陈述：pullback : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pullback₃.map_p₁_comp : F.map (p₁ hf₁ f₂ f₃) ≫ f₁ = π _ _ _ :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.relativelyRepresentable.pullback** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Functor.relativelyRepresentable`。
形式化陈述：pullback : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pullback₃.map_p₂_comp : F.map (p₂ hf₁ f₂ f₃) ≫ f₂ = π _ _ _ := by
  simp [π, p₁, p₂, ← hf₁.w f₂]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.relativelyRepresentable.pullback** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Functor.relativelyRepresentable`。
形式化陈述：pullback : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pullback₃.map_p₃_comp : F.map (p₃ hf₁ f₂ f₃) ≫ f₃ = π _ _ _ := by
  simp [π, p₁, p₃, ← hf₁.w f₃, pullback.condition]

section

variable [Faithful F] {Z : C} (x₁ : Z ⟶ A₁) (x₂ : Z ⟶ A₂) (x₃ : Z ⟶ A₃)
  (h₁₂ : F.map x₁ ≫ f₁ = F.map x₂ ≫ f₂)
  (h₁₃ : F.map x₁ ≫ f₁ = F.map x₃ ≫ f₃)

/-- The lift obtained from the universal property of `(A₁ ×_X A₂) ×_{A₁} (A₁ ×_X A₃)`. -/
/-
**CategoryTheory.Functor.relativelyRepresentable.lift** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Functor.relativelyRepresentable`。
形式化陈述：lift [Full F] : c ⟶ hf.pullback g
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.relativelyRepresentable.isPullback`：isPullback : 
IsPullback (hf.fst g) (F.map (hf.snd g)) f g

--- 原说明 ---
The lift obtained from the universal property of `(A₁ ×_X A₂) ×_{A₁} (A₁ ×_X A₃)
`.
-/
noncomputable def lift₃ : Z ⟶ pullback₃ hf₁ f₂ f₃ :=
  pullback.lift (hf₁.lift' x₁ x₂ h₁₂)
    (hf₁.lift' x₁ x₃ h₁₃) (by simp)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.relativelyRepresentable.lift** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Functor.relativelyRepresentable`。
形式化陈述：lift [Full F] : c ⟶ hf.pullback g
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.relativelyRepresentable.isPullback`：isPullback : 
IsPullback (hf.fst g) (F.map (hf.snd g)) f g
-/
lemma lift₃_p₁ : hf₁.lift₃ f₂ f₃ x₁ x₂ x₃ h₁₂ h₁₃ ≫ pullback₃.p₁ hf₁ f₂ f₃ = x₁ := by
  simp [lift₃, pullback₃.p₁]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.relativelyRepresentable.lift** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Functor.relativelyRepresentable`。
形式化陈述：lift [Full F] : c ⟶ hf.pullback g
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.relativelyRepresentable.isPullback`：isPullback : 
IsPullback (hf.fst g) (F.map (hf.snd g)) f g
-/
lemma lift₃_p₂ : hf₁.lift₃ f₂ f₃ x₁ x₂ x₃ h₁₂ h₁₃ ≫ pullback₃.p₂ hf₁ f₂ f₃ = x₂ := by
  simp [lift₃, pullback₃.p₂]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.relativelyRepresentable.lift** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Functor.relativelyRepresentable`。
形式化陈述：lift [Full F] : c ⟶ hf.pullback g
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.relativelyRepresentable.isPullback`：isPullback : 
IsPullback (hf.fst g) (F.map (hf.snd g)) f g
-/
lemma lift₃_p₃ : hf₁.lift₃ f₂ f₃ x₁ x₂ x₃ h₁₂ h₁₃ ≫ pullback₃.p₃ hf₁ f₂ f₃ = x₃ := by
  simp [lift₃, pullback₃.p₃]

end

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.relativelyRepresentable.pullback** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Functor.relativelyRepresentable`。
形式化陈述：pullback : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pullback₃.fst_fst'_eq_p₁ : pullback.fst _ _ ≫ hf₁.fst' f₂ = pullback₃.p₁ hf₁ f₂ f₃ := rfl

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.relativelyRepresentable.pullback** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Functor.relativelyRepresentable`。
形式化陈述：pullback : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pullback₃.fst_snd_eq_p₂ : pullback.fst _ _ ≫ hf₁.snd f₂ = pullback₃.p₂ hf₁ f₂ f₃ := rfl

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.relativelyRepresentable.pullback** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Functor.relativelyRepresentable`。
形式化陈述：pullback : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pullback₃.snd_snd_eq_p₃ : pullback.snd _ _ ≫ hf₁.snd f₃ = pullback₃.p₃ hf₁ f₂ f₃ := rfl

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.relativelyRepresentable.pullback** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Functor.relativelyRepresentable`。
形式化陈述：pullback : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pullback₃.snd_fst'_eq_p₁ :
    pullback.snd (hf₁.fst' f₂) (hf₁.fst' f₃) ≫ hf₁.fst' f₃ = pullback₃.p₁ hf₁ f₂ f₃ :=
  pullback.condition.symm

set_option backward.isDefEq.respectTransparency.types false in
variable {hf₁ f₂ f₃} in
@[ext]
/-
**CategoryTheory.Functor.relativelyRepresentable.pullback** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Functor.relativelyRepresentable`。
形式化陈述：pullback : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pullback₃.hom_ext [Faithful F] {Z : C} {φ φ' : Z ⟶ pullback₃ hf₁ f₂ f₃}
    (h₁ : φ ≫ pullback₃.p₁ hf₁ f₂ f₃ = φ' ≫ pullback₃.p₁ hf₁ f₂ f₃)
    (h₂ : φ ≫ pullback₃.p₂ hf₁ f₂ f₃ = φ' ≫ pullback₃.p₂ hf₁ f₂ f₃)
    (h₃ : φ ≫ pullback₃.p₃ hf₁ f₂ f₃ = φ' ≫ pullback₃.p₃ hf₁ f₂ f₃) : φ = φ' := by
  apply pullback.hom_ext <;> ext <;> simpa

end Pullbacks₃

section Diagonal
/-
In this section, we prove a criterion for the diagonal morphisms to be relatively representable.
-/

variable {F : C ⥤ D}
variable [HasBinaryProducts C]
variable [HasPullbacks D] [HasBinaryProducts D] [HasTerminal D]
variable [Full F]
variable [PreservesLimitsOfShape (Discrete WalkingPair) F]

set_option backward.isDefEq.respectTransparency false in
/-- Assume that
1. `C` has binary products,
2. `D` has pullbacks, binary products and a terminal object, and
3. `F : C ⥤ D` is full and preserves binary products.

For an object `X` in a category `D`, if the diagonal morphism `X ⟶ X × X` is relatively
representable, then every morphism of the form `F.obj a ⟶ X` is relatively representable with
respect to `F`.
-/
/-
**CategoryTheory.Functor.relativelyRepresentable.of_diag** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Functor.relativelyRepresentable`。
形式化陈述：of_diag {X : D} (h : F.relativelyRepresentable (Limits.diag X)) ⦃a : C⦄ (g
 : F.obj a ⟶ X) : F.relativelyRepresentable g
参数：h : F.relativelyRepresentable (Limits.diag X)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.IsPullback.instHasPullbackFst`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {P X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_
1 : CategoryTheory.Limits.HasPullb…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.pullback_map_diagonal_isPullback`：pullback_map_dia
gonal_isPullback : IsPullback (pullback.fst _ _ ≫ f) (pullback.map f g (f ≫ i) (
g ≫ i) _ _ i (Category.id_comp _).symm (Cate…
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `CategoryTheory.Limits.instHasLimitCompOfPreservesLimit`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.prod.hom_ext`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryProd
uct X Y] {f g : W ⟶ X ⨯ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `prodIsoPullback_inv_fst`：prodIsoPullback_inv_fst [HasTerminal C] [HasPul
lbacks C] (X Y : C) [HasBinaryProduct X Y] : (prodIsoPullback X Y).inv ≫ prod.fs
t = pullback.…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `prodIsoPullback_inv_snd`：prodIsoPullback_inv_snd [HasTerminal C] [HasPul
lbacks C] (X Y : C) [HasBinaryProduct X Y] : (prodIsoPullback X Y).inv ≫ prod.sn
d = pullback.…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `CategoryTheory.IsPullback.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}   
{g : Y ⟶ Z}, CategoryThe…
· 使用定理 `CategoryTheory.Limits.terminal.comp_from`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasTerminal C] {P 
Q : C}   (f : P ⟶ Q),   Catego…
· 使用定理 `CategoryTheory.IsPullback.of_vert_isIso_mono`：of_vert_isIso_mono [IsIso 
snd] [Mono f] (sq : CommSq fst snd f g) : IsPullback fst snd f g
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
（共 42 条，此处仅展示前 30 条）

--- 原说明 ---
Assume that
1. `C` has binary products,
2. `D` has pullbacks, binary products and a terminal object, and
3. `F : C ⥤ D` is full and preserves binary products.

For an object `X` in a category `D`, if the diagonal morphism `X ⟶ X × X` is rel
atively
representable, then every morphism of the form `F.obj a ⟶ X` is relatively repre
sentable with
respect to `F`.
-/
lemma of_diag {X : D} (h : F.relativelyRepresentable (Limits.diag X))
    ⦃a : C⦄ (g : F.obj a ⟶ X) : F.relativelyRepresentable g := by
  rw [(by cat_disch : Limits.diag X = pullback.lift (𝟙 X) (𝟙 X) ≫ (prodIsoPullback X X).inv)] at h
  intro a' g'
  obtain ⟨_, ⟨left⟩⟩ := pullback_map_diagonal_isPullback g g' (terminal.from X)
  let prodMap : F.obj (a ⨯ a') ⟶ X ⨯ X :=
    (preservesLimitIso _ (pair _ _) ≪≫ HasLimit.isoOfNatIso (pairComp _ _ _)).hom ≫ prod.map g g'
  let pbRepr :=
    (h prodMap).choose_spec.choose_spec.choose_spec.isLimit'.some.conePointUniqueUpToIso <|
    pasteHorizIsPullback rfl (IsPullback.of_vert_isIso_mono (snd := pullback.congrHom
      (terminal.comp_from g) (terminal.comp_from g') ≪≫ (prodIsoPullback _ _).symm ≪≫
      (HasLimit.isoOfNatIso (pairComp _ _ _)).symm ≪≫ (preservesLimitIso _ (pair _ _)).symm |>.hom)
    ⟨by cat_disch⟩).isLimit'.some left
  exact ⟨_, ⟨_, ⟨_, IsPullback.of_iso_pullback (fst := pbRepr.hom ≫ pullback.fst g g')
    (snd := F.map (Functor.preimage F (pbRepr.hom ≫ pullback.snd g g')))
    ⟨by simp [pullback.condition]⟩ pbRepr (by cat_disch) (by cat_disch)⟩⟩⟩

/-- Assume that
1. `C` has binary products and pullbacks,
2. `D` has pullbacks, binary products and a terminal object, and
3. `F : C ⥤ D` is full and preserves binary products and pullbacks.

For a morphism `g : F.obj a ⟶ pullback (terminal.from X) (terminal.from X)`,
the canonical morphism from `F.obj a` to
`pullback ((g ≫ pullback.fst _ _) ≫ terminal.from X) ((g ≫ pullback.snd _ _) ≫ terminal.from X)`
is relatively representable with respect to `F`.
-/
/-
**CategoryTheory.Functor.relativelyRepresentable.toPullbackTerminal** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.Functor.relativelyRepresentable`。
形式化陈述：toPullbackTerminal {X : D} {a : C} [HasPullbacks C] [PreservesLimitsOfShap
e WalkingCospan F] (g : F.obj a ⟶ Limits.pullback (terminal.from X) (terminal.fr
om X)) : F.relativelyRepresentable (pullback.lift (f
参数：g : F.obj a ⟶ Limits.pullback (terminal.from X) (terminal.from X)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.IsPullback.instHasPullbackFst`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {P X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_
1 : CategoryTheory.Limits.HasPullb…
· 使用定理 `CategoryTheory.Limits.terminal.comp_from`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasTerminal C] {P 
Q : C}   (f : P ⟶ Q),   Catego…
· 使用定理 `CategoryTheory.Limits.instHasLimitCompOfPreservesLimit`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.MorphismProperty.RespectsRight.postcomp`：∀ {C : Type u} {
inst : CategoryTheory.CategoryStruct.{v, u} C} {P Q : CategoryTheory.MorphismPro
perty C}   [self : P.RespectsRight Q] {X Y Z…
· 使用定理 `CategoryTheory.MorphismProperty.Respects.toRespectsRight`：∀ {C : Type u}
 {inst : CategoryTheory.CategoryStruct.{v, u} C} {P Q : CategoryTheory.MorphismP
roperty C}   [self : P.Respects Q], P.Respects…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用引理 `CategoryTheory.Functor.relativelyRepresentable.map`：map [Full F] [HasPul
lbacks C] {a b : C} (f : a ⟶ b) [forall c (g : c ⟶ b), PreservesLimit (cospan f 
g) F] : F.relativelyRepresentable (F.map…
· 使用定理 `CategoryTheory.Functor.map_preimage`：map_preimage (F : C ⥤ D) [Full F] {
X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage F f) = f

--- 原说明 ---
Assume that
1. `C` has binary products and pullbacks,
2. `D` has pullbacks, binary products and a terminal object, and
3. `F : C ⥤ D` is full and preserves binary products and pullbacks.

For a morphism `g : F.obj a ⟶ pullback (terminal.from X) (terminal.from X)`,
the canonical morphism from `F.obj a` to
`pullback ((g ≫ pullback.fst _ _) ≫ terminal.from X) ((g ≫ pullback.snd _ _) ≫ t
erminal.from X)`
is relatively representable with respect to `F`.
-/
lemma toPullbackTerminal {X : D} {a : C}
    [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan F]
    (g : F.obj a ⟶ Limits.pullback (terminal.from X) (terminal.from X)) :
    F.relativelyRepresentable (pullback.lift (f := (g ≫ pullback.fst _ _) ≫ terminal.from X)
        (g := (g ≫ pullback.snd _ _) ≫ terminal.from X) (𝟙 _) (𝟙 _) (by cat_disch)) := by
  let pbIso := pullback.congrHom
    (terminal.comp_from _ : (g ≫ pullback.fst _ _) ≫ terminal.from X = terminal.from _)
    (terminal.comp_from _ : (g ≫ pullback.snd _ _) ≫ terminal.from X = terminal.from _) ≪≫
    (prodIsoPullback _ _).symm ≪≫ (HasLimit.isoOfNatIso (pairComp _ _ _)).symm ≪≫
    (preservesLimitIso _ (pair _ _)).symm
  rw [← comp_id (pullback.lift _ _), ← pbIso.hom_inv_id, ← Category.assoc]
  apply (respectsIso F).toRespectsRight.postcomp _ (inferInstance : IsIso _) _
  exact map_preimage F (_ ≫ pbIso.hom) ▸ map F (F.preimage _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Assume that
1. `C` has binary products and pullbacks,
2. `D` has pullbacks, binary products and a terminal object, and
3. `F : C ⥤ D` is full and preserves binary products and pullbacks.

For an object `X` in a category `D`, if every morphism of the form `F.obj a ⟶ X` is relatively
representable with respect to `F`, so is the diagonal morphism `X ⟶ X × X`.
-/
/-
**CategoryTheory.Functor.relativelyRepresentable.diag_of_map_from_obj** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.Functor.relativelyRepresentable`。
形式化陈述：diag_of_map_from_obj [HasPullbacks C] [PreservesLimitsOfShape WalkingCospa
n F] {X : D} (h : forall ⦃a : C⦄ (g : F.obj a ⟶ X), F.relativelyRepresentable g)
 : F.relativelyRepresentable (Limits.diag X)
参数：h : forall ⦃a : C⦄ (g : F.obj a ⟶ X), F.relativelyRepresentable g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.prod.hom_ext`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryProd
uct X Y] {f g : W ⟶ X ⨯ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `prodIsoPullback_inv_fst`：prodIsoPullback_inv_fst [HasTerminal C] [HasPul
lbacks C] (X Y : C) [HasBinaryProduct X Y] : (prodIsoPullback X Y).inv ≫ prod.fs
t = pullback.…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `prodIsoPullback_inv_snd`：prodIsoPullback_inv_snd [HasTerminal C] [HasPul
lbacks C] (X Y : C) [HasBinaryProduct X Y] : (prodIsoPullback X Y).inv ≫ prod.sn
d = pullback.…
· 使用定理 `CategoryTheory.IsPullback.instHasPullbackFst`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {P X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_
1 : CategoryTheory.Limits.HasPullb…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.IsPullback.of_iso_pullback`：of_iso_pullback (h : CommSq f
st snd f g) [HasPullback f g] (i : P ≅ pullback f g) (w₁ : i.hom ≫ pullback.fst 
_ _ = fst) (w₂ : i.hom ≫ pullba…
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `CategoryTheory.Limits.terminal.comp_from`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasTerminal C] {P 
Q : C}   (f : P ⟶ Q),   Catego…
· 使用引理 `CategoryTheory.Functor.relativelyRepresentable.toPullbackTerminal`：toPul
lbackTerminal {X : D} {a : C} [HasPullbacks C] [PreservesLimitsOfShape WalkingCo
span F] (g : F.obj a ⟶ Limits.pullback (terminal.from X…
· 使用定理 `CategoryTheory.Limits.pullback.hom_ext`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categor
yTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.IsPullback.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}   
{g : Y ⟶ Z}, CategoryThe…
· 使用定理 `CategoryTheory.IsPullback.flip`：flip (h : IsPullback fst snd f g) : IsPu
llback snd fst g f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_preimage`：map_preimage (F : C ⥤ D) [Full F] {
X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage F f) = f
· 使用定理 `CategoryTheory.IsPullback.of_isLimit`：of_isLimit {c : PullbackCone f g} 
(h : Limits.IsLimit c) : IsPullback c.fst c.snd f g
· 使用定理 `CategoryTheory.IsPullback.isLimit'`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}   
{g : Y ⟶ Z} (self : Cate…
· 使用定理 `CategoryTheory.MorphismProperty.RespectsRight.postcomp`：∀ {C : Type u} {
inst : CategoryTheory.CategoryStruct.{v, u} C} {P Q : CategoryTheory.MorphismPro
perty C}   [self : P.RespectsRight Q] {X Y Z…
· 使用定理 `CategoryTheory.MorphismProperty.Respects.toRespectsRight`：∀ {C : Type u}
 {inst : CategoryTheory.CategoryStruct.{v, u} C} {P Q : CategoryTheory.MorphismP
roperty C}   [self : P.Respects Q], P.Respects…
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
Assume that
1. `C` has binary products and pullbacks,
2. `D` has pullbacks, binary products and a terminal object, and
3. `F : C ⥤ D` is full and preserves binary products and pullbacks.

For an object `X` in a category `D`, if every morphism of the form `F.obj a ⟶ X`
 is relatively
representable with respect to `F`, so is the diagonal morphism `X ⟶ X × X`.
-/
lemma diag_of_map_from_obj [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan F]
    {X : D} (h : ∀ ⦃a : C⦄ (g : F.obj a ⟶ X), F.relativelyRepresentable g) :
    F.relativelyRepresentable (Limits.diag X) := by
  rw [(by cat_disch : Limits.diag X = pullback.lift (𝟙 X) (𝟙 X) ≫ (prodIsoPullback X X).inv)]
  suffices F.relativelyRepresentable (pullback.lift (𝟙 _) (𝟙 _)) from
    (respectsIso F).toRespectsRight.postcomp _ (inferInstance : IsIso _) _ this
  intro a g
  obtain ⟨_, ⟨_, ⟨_, pbRepr⟩⟩⟩ := h (g ≫ pullback.fst _ _) (g ≫ pullback.snd _ _)
  obtain ⟨_, ⟨bot⟩⟩ := IsPullback.of_iso_pullback ⟨by rw [assoc]; simp [pullback.condition]⟩
    (pbRepr.isoPullback ≪≫ (pullbackDiagonalMapIdIso (g ≫ pullback.fst _ _) (g ≫ pullback.snd _ _)
      (terminal.from X)).symm) rfl rfl
  obtain ⟨_, ⟨_, ⟨topMap, top⟩⟩⟩ := (toPullbackTerminal g) <|
    (pbRepr.isoPullback ≪≫ (pullbackDiagonalMapIdIso (g ≫ pullback.fst _ _) (g ≫ pullback.snd _ _)
      (terminal.from X)).symm).hom ≫ pullback.snd
        (pullback.diagonal (terminal.from X))
        (pullback.map _ _ _ _ _ _ (𝟙 _) (by cat_disch) (by cat_disch))
  have hg : g = pullback.lift (𝟙 _) (𝟙 _) (by cat_disch) ≫ pullback.map
    ((g ≫ pullback.fst _ _) ≫ terminal.from X) ((g ≫ pullback.snd _ _) ≫ terminal.from X) _ _
      (g ≫ pullback.fst _ _) (g ≫ pullback.snd _ _) (𝟙 _) (by cat_disch) (by cat_disch) := by
    apply Limits.pullback.hom_ext <;> simp
  exact hg ▸ ⟨_, ⟨_, ⟨_, IsPullback.of_isLimit <| pasteVertIsPullback rfl bot
    (map_preimage F topMap ▸ top).flip.isLimit'.some⟩⟩⟩

/-- Assume that
1. `C` has binary products and pullbacks,
2. `D` has pullbacks, binary products and a terminal object, and
3. `F : C ⥤ D` is full and preserves binary products and pullbacks.

For an object `X` in a category `D`, the diagonal morphism `X ⟶ X × X` is relatively representable
with respect to `F` if and only if so is every morphism of the form `F.obj a ⟶ X`.
-/
/-
**CategoryTheory.Functor.relativelyRepresentable.diag_iff** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Functor.relativelyRepresentable`。
形式化陈述：diag_iff {X : D} [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan F]
 : F.relativelyRepresentable (Limits.diag X) ↔ forall ⦃a : C⦄ (g : F.obj a ⟶ X),
 F.relativelyRepresentable g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用引理 `CategoryTheory.Functor.relativelyRepresentable.of_diag`：of_diag {X : D} 
(h : F.relativelyRepresentable (Limits.diag X)) ⦃a : C⦄ (g : F.obj a ⟶ X) : F.re
lativelyRepresentable g
· 使用引理 `CategoryTheory.Functor.relativelyRepresentable.diag_of_map_from_obj`：dia
g_of_map_from_obj [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan F] {X :
 D} (h : forall ⦃a : C⦄ (g : F.obj a ⟶ X), F.relativelyRe…

--- 原说明 ---
Assume that
1. `C` has binary products and pullbacks,
2. `D` has pullbacks, binary products and a terminal object, and
3. `F : C ⥤ D` is full and preserves binary products and pullbacks.

For an object `X` in a category `D`, the diagonal morphism `X ⟶ X × X` is relati
vely representable
with respect to `F` if and only if so is every morphism of the form `F.obj a ⟶ X
`.
-/
lemma diag_iff {X : D} [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan F] :
    F.relativelyRepresentable (Limits.diag X) ↔
      ∀ ⦃a : C⦄ (g : F.obj a ⟶ X), F.relativelyRepresentable g :=
  ⟨fun h _ g => of_diag h g, fun h => diag_of_map_from_obj h⟩

end Diagonal

end Functor.relativelyRepresentable

end CategoryTheory

