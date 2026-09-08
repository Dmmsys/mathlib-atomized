/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Kim Morrison, Floris van Doorn
-/
module

public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.Data.Set.Image

/-!
# Discrete categories

We define `Discrete α` as a structure containing a term `a : α` for any type `α`,
and use this type alias to provide a `SmallCategory` instance
whose only morphisms are the identities.

There is an annoying technical difficulty that it has turned out to be inconvenient
to allow categories with morphisms living in `Prop`,
so instead of defining `X ⟶ Y` in `Discrete α` as `X = Y`,
one might define it as `PLift (X = Y)`.
In fact, to allow `Discrete α` to be a `SmallCategory`
(i.e. with morphisms in the same universe as the objects),
we actually define the hom type `X ⟶ Y` as `ULift (PLift (X = Y))`.

`Discrete.functor` promotes a function `f : I → C` (for any category `C`) to a functor
`Discrete.functor f : Discrete I ⥤ C`.

Similarly, `Discrete.natTrans` and `Discrete.natIso` promote `I`-indexed families of morphisms,
or `I`-indexed families of isomorphisms to natural transformations or natural isomorphism.

We show equivalences of types are the same as (categorical) equivalences of the corresponding
discrete categories.
-/

@[expose] public section

namespace CategoryTheory

-- morphism levels before object levels. See note [category theory universes].
universe v₁ v₂ v₃ u₁ u₁' u₂ u₃

-- This is intentionally a structure rather than a type synonym
-- to enforce using `DiscreteEquiv` (or `Discrete.mk` and `Discrete.as`) to move between
-- `Discrete α` and `α`. Otherwise there is too much API leakage.
/-- A wrapper for promoting any type to a category,
with the only morphisms being equalities.
-/
@[ext, aesop safe cases (rule_sets := [CategoryTheory])]
/-
**CategoryTheory.Discrete** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：Type u₁ → Type u₁
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A wrapper for promoting any type to a category,
with the only morphisms being equalities.
-/
structure Discrete (α : Type u₁) where
  /-- A wrapper for promoting any type to a category,
  with the only morphisms being equalities. -/
  as : α

@[simp]
/-
**CategoryTheory.Discrete.mk_as** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Discre
te`。
形式化陈述：∀ {α : Type u₁} (X : CategoryTheory.Discrete α), { as := X.as } = X
参数：X : CategoryTheory.Discrete α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Discrete.mk_as {α : Type u₁} (X : Discrete α) : Discrete.mk X.as = X :=
  rfl

/-- `Discrete α` is equivalent to the original type `α`. -/
@[simps]
/-
**CategoryTheory.discreteEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：discreteEquiv {α : Type u₁} : Discrete α ≃ α where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Discrete α` is equivalent to the original type `α`.
-/
def discreteEquiv {α : Type u₁} : Discrete α ≃ α where
  toFun := Discrete.as
  invFun := Discrete.mk
  left_inv := by cat_disch
  right_inv := by cat_disch
/-
**CategoryTheory.Discrete.as_bijective** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Discrete`。
形式化陈述：∀ {α : Type u_1}, Function.Bijective CategoryTheory.Discrete.as
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
-/
lemma Discrete.as_bijective {α : Type*} : (Discrete.as (α := α)).Bijective :=
  discreteEquiv.bijective
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Type u₁} [DecidableEq α] : DecidableEq (Discrete α) :=
  discreteEquiv.decidableEq

/-- The "Discrete" category on a type, whose morphisms are equalities.

Because we do not allow morphisms in `Prop` (only in `Type`),
somewhat annoyingly we have to define `X ⟶ Y` as `ULift (PLift (X = Y))`. -/
@[stacks 001A]
/-
**CategoryTheory.discreteCategory** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：discreteCategory (α : Type u₁) : SmallCategory (Discrete α) where Hom X Y
参数：α : Type u₁。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The "Discrete" category on a type, whose morphisms are equalities.

Because we do not allow morphisms in `Prop` (only in `Type`),
somewhat annoyingly we have to define `X ⟶ Y` as `ULift (PLift (X = Y))`.
-/
instance discreteCategory (α : Type u₁) : SmallCategory (Discrete α) where
  Hom X Y := ULift (PLift (X.as = Y.as))
  id _ := ULift.up (PLift.up rfl)
  comp {X Y Z} g f := by
    cases X
    cases Y
    cases Z
    rcases f with ⟨⟨⟨⟩⟩⟩
    exact g

namespace Discrete

variable {α : Type u₁}

/-
**CategoryTheory.Discrete.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Discrete`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited α] : Inhabited (Discrete α) :=
  ⟨⟨default⟩⟩
/-
**CategoryTheory.Discrete.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Discrete`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Subsingleton α] : Subsingleton (Discrete α) :=
  ⟨by cat_disch⟩
/-
**CategoryTheory.Discrete.instSubsingletonDiscreteHom** 是 Mathlib 中的一个实例，位于命名空间 
`CategoryTheory.Discrete`。
形式化陈述：instSubsingletonDiscreteHom (X Y : Discrete α) : Subsingleton (X ⟶ Y)
参数：X Y : Discrete α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `instSubsingletonULift`：∀ {α : Type u_1} [Subsingleton α], Subsingleton (
ULift.{u_2, u_1} α)
· 使用定理 `instSubsingletonPLift`：∀ {α : Sort u_1} [Subsingleton α], Subsingleton (
PLift α)
· 使用定理 `instSubsingleton`：∀ (p : Prop), Subsingleton p
-/
instance instSubsingletonDiscreteHom (X Y : Discrete α) : Subsingleton (X ⟶ Y) :=
  show Subsingleton (ULift (PLift _)) from inferInstance

/-- A simple tactic to run `cases` on any `Discrete α` hypotheses. -/
macro "discrete_cases" : tactic =>
  `(tactic| fail_if_no_progress casesm* Discrete _, (_ : Discrete _) ⟶ (_ : Discrete _), PLift _)

open Lean Elab Tactic in
/--
Use:
```
attribute [local aesop safe tactic (rule_sets := [CategoryTheory])]
  CategoryTheory.Discrete.discreteCases
```
to locally give `cat_disch` the ability to call `cases` on
`Discrete` and `(_ : Discrete _) ⟶ (_ : Discrete _)` hypotheses.
-/
meta def discreteCases : TacticM Unit := do
  evalTactic (← `(tactic| discrete_cases))

-- TODO: investigate turning on either
-- `attribute [aesop safe cases (rule_sets := [CategoryTheory])] Discrete`
-- or
-- `attribute [aesop safe tactic (rule_sets := [CategoryTheory])] discreteCases`
-- globally.

/-
**CategoryTheory.Discrete.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Discrete`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Unique α] : Unique (Discrete α) :=
  Unique.mk' (Discrete α)

/-- Extract the equation from a morphism in a discrete category. -/
/-
**CategoryTheory.Discrete.eq_of_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Di
screte`。
形式化陈述：eq_of_hom {X Y : Discrete α} (i : X ⟶ Y) : X.as = Y.as
参数：i : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extract the equation from a morphism in a discrete category.
-/
theorem eq_of_hom {X Y : Discrete α} (i : X ⟶ Y) : X.as = Y.as :=
  i.down.down

/-- Promote an equation between the wrapped terms in `X Y : Discrete α` to a morphism `X ⟶ Y`
in the discrete category. -/
/-
**CategoryTheory.Discrete.eqToHom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Disc
rete`。
形式化陈述：{α : Type u₁} → {X Y : CategoryTheory.Discrete α} → X.as = Y.as → (X ⟶ Y)
参数：X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Promote an equation between the wrapped terms in `X Y : Discrete α` to a morphis
m `X ⟶ Y`
in the discrete category.
-/
protected abbrev eqToHom {X Y : Discrete α} (h : X.as = Y.as) : X ⟶ Y :=
  eqToHom (by cat_disch)

/-- Promote an equation between the wrapped terms in `X Y : Discrete α` to an isomorphism `X ≅ Y`
in the discrete category. -/
/-
**CategoryTheory.Discrete.eqToIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Disc
rete`。
形式化陈述：{α : Type u₁} → {X Y : CategoryTheory.Discrete α} → X.as = Y.as → (X ≅ Y)
参数：X ≅ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Promote an equation between the wrapped terms in `X Y : Discrete α` to an isomor
phism `X ≅ Y`
in the discrete category.
-/
protected abbrev eqToIso {X Y : Discrete α} (h : X.as = Y.as) : X ≅ Y :=
  eqToIso (by cat_disch)

/-- A variant of `eqToHom` that lifts terms to the discrete category. -/
/-
**CategoryTheory.Discrete.eqToHom'** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.D
iscrete`。
形式化陈述：eqToHom' {a b : α} (h : a = b) : Discrete.mk a ⟶ Discrete.mk b
参数：h : a = b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A variant of `eqToHom` that lifts terms to the discrete category.
-/
abbrev eqToHom' {a b : α} (h : a = b) : Discrete.mk a ⟶ Discrete.mk b :=
  Discrete.eqToHom h

/-- A variant of `eqToIso` that lifts terms to the discrete category. -/
/-
**CategoryTheory.Discrete.eqToIso'** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.D
iscrete`。
形式化陈述：eqToIso' {a b : α} (h : a = b) : Discrete.mk a ≅ Discrete.mk b
参数：h : a = b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A variant of `eqToIso` that lifts terms to the discrete category.
-/
abbrev eqToIso' {a b : α} (h : a = b) : Discrete.mk a ≅ Discrete.mk b :=
  Discrete.eqToIso h

@[simp]
/-
**CategoryTheory.Discrete.id_def** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Discr
ete`。
形式化陈述：id_def (X : Discrete α) : ULift.up (PLift.up (Eq.refl X.as)) = 𝟙 X
参数：X : Discrete α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_def (X : Discrete α) : ULift.up (PLift.up (Eq.refl X.as)) = 𝟙 X :=
  rfl

@[simp]
/-
**CategoryTheory.Discrete.id_def'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Disc
rete`。
形式化陈述：id_def' (X : α) : ULift.up (PLift.up (Eq.refl X)) = 𝟙 (⟨X⟩ : Discrete α)
参数：X : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_def' (X : α) : ULift.up (PLift.up (Eq.refl X)) = 𝟙 (⟨X⟩ : Discrete α) :=
  rfl

variable {C : Type u₂} [Category.{v₂} C]
/-
**CategoryTheory.Discrete.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Discrete`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {I : Type u₁} {i j : Discrete I} (f : i ⟶ j) : IsIso f :=
  ⟨⟨Discrete.eqToHom (eq_of_hom f).symm, by cat_disch⟩⟩

attribute [local aesop safe tactic (rule_sets := [CategoryTheory])]
  CategoryTheory.Discrete.discreteCases

/-- Any function `I → C` gives a functor `Discrete I ⥤ C`. -/
@[implicit_reducible]
/-
**CategoryTheory.Discrete.functor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Disc
rete`。
形式化陈述：functor {I : Type u₁} (F : I -> C) : Discrete I ⥤ C where obj
参数：F : I -> C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any function `I → C` gives a functor `Discrete I ⥤ C`.
-/
def functor {I : Type u₁} (F : I → C) : Discrete I ⥤ C where
  obj := F ∘ Discrete.as
  map {X Y} f := by
    dsimp
    rcases f with ⟨⟨h⟩⟩
    exact eqToHom (congrArg _ h)

@[simp]
/-
**CategoryTheory.Discrete.functor_obj** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Discrete`。
形式化陈述：functor_obj {I : Type u₁} (F : I -> C) (i : I) : (Discrete.functor F).obj 
(Discrete.mk i) = F i
参数：F : I -> C；i : I。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem functor_obj {I : Type u₁} (F : I → C) (i : I) :
    (Discrete.functor F).obj (Discrete.mk i) = F i :=
  rfl
/-
**CategoryTheory.Discrete.functor_map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Discrete`。
形式化陈述：functor_map {I : Type u₁} (F : I -> C) {i : Discrete I} (f : i ⟶ i) : (Dis
crete.functor F).map f = 𝟙 (F i.as)
参数：F : I -> C；f : i ⟶ i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem functor_map {I : Type u₁} (F : I → C) {i : Discrete I} (f : i ⟶ i) :
    (Discrete.functor F).map f = 𝟙 (F i.as) := by cat_disch

@[simp]
/-
**CategoryTheory.Discrete.functor_obj_eq_as** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Discrete`。
形式化陈述：functor_obj_eq_as {I : Type u₁} (F : I -> C) (X : Discrete I) : (Discrete.
functor F).obj X = F X.as
参数：F : I -> C；X : Discrete I。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem functor_obj_eq_as {I : Type u₁} (F : I → C) (X : Discrete I) :
    (Discrete.functor F).obj X = F X.as :=
  rfl

@[simp]
/-
**CategoryTheory.Discrete.range_functor** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Discrete`。
形式化陈述：range_functor {I : Type*} (X : I -> C) : Set.range (Discrete.functor X).ob
j = Set.range X
参数：X : I -> C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `CategoryTheory.Discrete.as_bijective`：∀ {α : Type u_1}, Function.Bijecti
ve CategoryTheory.Discrete.as
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma range_functor {I : Type*} (X : I → C) : Set.range (Discrete.functor X).obj = Set.range X := by
  simp [Discrete.functor, Set.range_comp, Discrete.as_bijective.surjective.range_eq]

@[ext]
/-
**CategoryTheory.Discrete.functor_ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
Discrete`。
形式化陈述：functor_ext {I : Type u₁} {G F : Discrete I ⥤ C} (h : (i : I) -> G.obj ⟨i⟩
 = F.obj ⟨i⟩) : G = F
参数：h : (i : I) -> G.obj ⟨i⟩ = F.obj ⟨i⟩。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.ext`：ext {F G : C ⥤ D} (h_obj : forall X, F.obj X
 = G.obj X) (h_map : forall X Y f, F.map f = eqToHom (h_obj X) ≫ G.map f ≫ eqToH
om (h_obj Y).sym…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.eqToHom_trans`：eqToHom_trans {X Y Z : C} (p : X = Y) (q :
 Y = Z) : eqToHom p ≫ eqToHom q = eqToHom (p.trans q)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma functor_ext {I : Type u₁} {G F : Discrete I ⥤ C} (h : (i : I) → G.obj ⟨i⟩ = F.obj ⟨i⟩) :
    G = F := by
  fapply Functor.ext
  · intro I; rw [h]
  · intro ⟨X⟩ ⟨Y⟩ ⟨⟨p⟩⟩; simp only at p; induction p; simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The discrete functor induced by a composition of maps can be written as a
composition of two discrete functors.
-/
@[simps!]
/-
**CategoryTheory.Discrete.functorComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Discrete`。
形式化陈述：functorComp {I : Type u₁} {J : Type u₁'} (f : J -> C) (g : I -> J) : Discr
ete.functor (f ∘ g) ≅ Discrete.functor (Discrete.mk ∘ g) ⋙ Discrete.functor f
参数：f : J -> C；g : I -> J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The discrete functor induced by a composition of maps can be written as a
composition of two discrete functors.
-/
def functorComp {I : Type u₁} {J : Type u₁'} (f : J → C) (g : I → J) :
    Discrete.functor (f ∘ g) ≅ Discrete.functor (Discrete.mk ∘ g) ⋙ Discrete.functor f :=
  NatIso.ofComponents fun _ => Iso.refl _

/-- For functors out of a discrete category,
a natural transformation is just a collection of maps,
as the naturality squares are trivial.
-/
@[simps, implicit_reducible]
/-
**CategoryTheory.Discrete.natTrans** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Dis
crete`。
形式化陈述：natTrans {I : Type u₁} {F G : Discrete I ⥤ C} (f : forall i : Discrete I, 
F.obj i ⟶ G.obj i) : F ⟶ G where app
参数：f : forall i : Discrete I, F.obj i ⟶ G.obj i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For functors out of a discrete category,
a natural transformation is just a collection of maps,
as the naturality squares are trivial.
-/
def natTrans {I : Type u₁} {F G : Discrete I ⥤ C} (f : ∀ i : Discrete I, F.obj i ⟶ G.obj i) :
    F ⟶ G where
  app := f
  naturality := fun {X Y} ⟨⟨g⟩⟩ => by
    discrete_cases
    rcases g
    change F.map (𝟙 _) ≫ _ = _ ≫ G.map (𝟙 _)
    simp

/-- For functors out of a discrete category,
a natural isomorphism is just a collection of isomorphisms,
as the naturality squares are trivial.
-/
@[simps!]
/-
**CategoryTheory.Discrete.natIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Discr
ete`。
形式化陈述：natIso {I : Type u₁} {F G : Discrete I ⥤ C} (f : forall i : Discrete I, F.
obj i ≅ G.obj i) : F ≅ G
参数：f : forall i : Discrete I, F.obj i ≅ G.obj i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For functors out of a discrete category,
a natural isomorphism is just a collection of isomorphisms,
as the naturality squares are trivial.
-/
def natIso {I : Type u₁} {F G : Discrete I ⥤ C} (f : ∀ i : Discrete I, F.obj i ≅ G.obj i) :
    F ≅ G :=
  NatIso.ofComponents f fun ⟨⟨g⟩⟩ => by
    discrete_cases
    rcases g
    change F.map (𝟙 _) ≫ _ = _ ≫ G.map (𝟙 _)
    simp
/-
**CategoryTheory.Discrete.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Discrete`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {I : Type*} {F G : Discrete I ⥤ C} (f : ∀ i, F.obj i ⟶ G.obj i) [∀ i, IsIso (f i)] :
    IsIso (Discrete.natTrans f) := by
  change IsIso (Discrete.natIso (fun i => asIso (f i))).hom
  infer_instance

@[simp]
/-
**CategoryTheory.Discrete.natIso_app** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.D
iscrete`。
形式化陈述：natIso_app {I : Type u₁} {F G : Discrete I ⥤ C} (f : forall i : Discrete I
, F.obj i ≅ G.obj i) (i : Discrete I) : (Discrete.natIso f).app i = f i
参数：f : forall i : Discrete I, F.obj i ≅ G.obj i；i : Discrete I。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem natIso_app {I : Type u₁} {F G : Discrete I ⥤ C} (f : ∀ i : Discrete I, F.obj i ≅ G.obj i)
    (i : Discrete I) : (Discrete.natIso f).app i = f i := by cat_disch

/-- Every functor `F` from a discrete category is naturally isomorphic (actually, equal) to
  `Discrete.functor (F.obj)`. -/
@[simps!]
/-
**CategoryTheory.Discrete.natIsoFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Discrete`。
形式化陈述：natIsoFunctor {I : Type u₁} {F : Discrete I ⥤ C} : F ≅ Discrete.functor (F
.obj ∘ Discrete.mk)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every functor `F` from a discrete category is naturally isomorphic (actually, eq
ual) to
  `Discrete.functor (F.obj)`.
-/
def natIsoFunctor {I : Type u₁} {F : Discrete I ⥤ C} : F ≅ Discrete.functor (F.obj ∘ Discrete.mk) :=
  natIso fun _ => Iso.refl _

/-- Composing `Discrete.functor F` with another functor `G` amounts to composing `F` with `G.obj` -/
@[simps!]
/-
**CategoryTheory.Discrete.compNatIsoDiscrete** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Discrete`。
形式化陈述：compNatIsoDiscrete {I : Type u₁} {D : Type u₃} [Category.{v₃} D] (F : I ->
 C) (G : C ⥤ D) : Discrete.functor F ⋙ G ≅ Discrete.functor (G.obj ∘ F)
参数：F : I -> C；G : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composing `Discrete.functor F` with another functor `G` amounts to composing `F`
 with `G.obj`
-/
def compNatIsoDiscrete {I : Type u₁} {D : Type u₃} [Category.{v₃} D] (F : I → C) (G : C ⥤ D) :
    Discrete.functor F ⋙ G ≅ Discrete.functor (G.obj ∘ F) :=
  natIso fun _ => Iso.refl _

/-- We can promote a type-level `Equiv` to
an equivalence between the corresponding `discrete` categories.
-/
@[simps]
/-
**CategoryTheory.Discrete.equivalence** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Discrete`。
形式化陈述：equivalence {I : Type u₁} {J : Type u₂} (e : I ≃ J) : Discrete I ≌ Discret
e J where functor
参数：e : I ≃ J。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
We can promote a type-level `Equiv` to
an equivalence between the corresponding `discrete` categories.
-/
def equivalence {I : Type u₁} {J : Type u₂} (e : I ≃ J) : Discrete I ≌ Discrete J where
  functor := Discrete.functor (Discrete.mk ∘ (e : I → J))
  inverse := Discrete.functor (Discrete.mk ∘ (e.symm : J → I))
  unitIso :=
    Discrete.natIso fun i => eqToIso (by simp)
  counitIso :=
    Discrete.natIso fun j => eqToIso (by simp)

/-- We can convert an equivalence of `discrete` categories to a type-level `Equiv`. -/
@[simps]
/-
**CategoryTheory.Discrete.equivOfEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Discrete`。
形式化陈述：equivOfEquivalence {α : Type u₁} {β : Type u₂} (h : Discrete α ≌ Discrete 
β) : α ≃ β where toFun
参数：h : Discrete α ≌ Discrete β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We can convert an equivalence of `discrete` categories to a type-level `Equiv`.
-/
def equivOfEquivalence {α : Type u₁} {β : Type u₂} (h : Discrete α ≌ Discrete β) : α ≃ β where
  toFun := Discrete.as ∘ h.functor.obj ∘ Discrete.mk
  invFun := Discrete.as ∘ h.inverse.obj ∘ Discrete.mk
  left_inv a := by simpa using eq_of_hom (h.unitIso.app (Discrete.mk a)).2
  right_inv a := by simpa using eq_of_hom (h.counitIso.app (Discrete.mk a)).1

end Discrete

namespace Discrete

variable {J : Type v₁}

open Opposite

/-- A discrete category is equivalent to its opposite category. -/
@[simps! functor_obj_as inverse_obj]
/-
**CategoryTheory.Discrete.opposite** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Dis
crete`。
形式化陈述：(α : Type u₁) → (CategoryTheory.Discrete α)ᵒᵖ ≌ CategoryTheory.Discrete α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A discrete category is equivalent to its opposite category.
-/
protected def opposite (α : Type u₁) : (Discrete α)ᵒᵖ ≌ Discrete α :=
  let F : Discrete α ⥤ (Discrete α)ᵒᵖ := Discrete.functor fun x => op (Discrete.mk x)
  { functor := F.leftOp
    inverse := F
    unitIso := NatIso.ofComponents fun ⟨_⟩ => Iso.refl _
    counitIso := Discrete.natIso fun ⟨_⟩ => Iso.refl _ }

variable {C : Type u₂} [Category.{v₂} C]

@[simp]
/-
**CategoryTheory.Discrete.functor_map_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Discrete`。
形式化陈述：functor_map_id (F : Discrete J ⥤ C) {j : Discrete J} (f : j ⟶ j) : F.map f
 = 𝟙 (F.obj j)
参数：F : Discrete J ⥤ C；f : j ⟶ j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem functor_map_id (F : Discrete J ⥤ C) {j : Discrete J} (f : j ⟶ j) :
    F.map f = 𝟙 (F.obj j) := by
  have h : f = 𝟙 j := by cat_disch
  rw [h]
  simp

end Discrete

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.Discrete.forall** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Discr
ete`。
形式化陈述：∀ {α : Type u_1} {p : CategoryTheory.Discrete α → Prop},   (∀ (a : Categor
yTheory.Discrete α), p a) ↔ ∀ (a' : α), p { as := a' }
参数：∀ (a : CategoryTheory.Discrete α), p a；a' : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_iff_eq`：∀ {a b : Prop}, (a ↔ b) ↔ a = b
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.forall_congr_left`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} (e :
 α ≃ β), (∀ (a : α), p a) ↔ ∀ (b : β), p (e.symm b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Discrete.forall {α : Type*} {p : Discrete α → Prop} :
    (∀ (a : Discrete α), p a) ↔ ∀ (a' : α), p ⟨a'⟩ := by
  rw [iff_iff_eq, discreteEquiv.forall_congr_left]
  simp only [discreteEquiv, Equiv.symm_mk, Equiv.coe_fn_mk]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.Discrete.exists** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Discr
ete`。
形式化陈述：∀ {α : Type u_1} {p : CategoryTheory.Discrete α → Prop}, (∃ a, p a) ↔ ∃ a'
, p { as := a' }
参数：∃ a, p a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_iff_eq`：∀ {a b : Prop}, (a ↔ b) ↔ a = b
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.exists_congr_left`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} (e :
 α ≃ β), (∃ a, p a) ↔ ∃ b, p (e.symm b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Discrete.exists {α : Type*} {p : Discrete α → Prop} :
    (∃ (a : Discrete α), p a) ↔ ∃ (a' : α), p ⟨a'⟩ := by
  rw [iff_iff_eq, discreteEquiv.exists_congr_left]
  simp [discreteEquiv]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The equivalence of categories `(J → C) ≌ (Discrete J ⥤ C)`. -/
@[simps]
/-
**CategoryTheory.piEquivalenceFunctorDiscrete** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory`。
形式化陈述：piEquivalenceFunctorDiscrete (J : Type u₂) (C : Type u₁) [Category.{v₁} C]
 : (J -> C) ≌ (Discrete J ⥤ C) where functor
参数：J : Type u₂；C : Type u₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence of categories `(J → C) ≌ (Discrete J ⥤ C)`.
-/
def piEquivalenceFunctorDiscrete (J : Type u₂) (C : Type u₁) [Category.{v₁} C] :
    (J → C) ≌ (Discrete J ⥤ C) where
  functor :=
    { obj := fun F => Discrete.functor F
      map := fun f => Discrete.natTrans (fun j => f j.as) }
  inverse :=
    { obj := fun F j => F.obj ⟨j⟩
      map := fun f j => f.app ⟨j⟩ }
  unitIso := Iso.refl _
  counitIso := NatIso.ofComponents (fun F => (NatIso.ofComponents (fun _ => Iso.refl _)
    (by
      rintro ⟨x⟩ ⟨y⟩ f
      obtain rfl : x = y := Discrete.eq_of_hom f
      obtain rfl : f = 𝟙 _ := rfl
      simp))) (by cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- `piEquivalenceFunctorDiscrete` is compatible with `evaluation`. -/
@[simps!]
/-
**CategoryTheory.piEquivalenceFunctorDiscreteCompEvaluationIso** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory`。
形式化陈述：piEquivalenceFunctorDiscreteCompEvaluationIso (C : Type*) [Category* C] {J
 : Type*} (j : J) : (piEquivalenceFunctorDiscrete J C).functor ⋙ (evaluation _ _
).obj ⟨j⟩ ≅ Pi.eval _ j
参数：C : Type*；j : J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`piEquivalenceFunctorDiscrete` is compatible with `evaluation`.
-/
def piEquivalenceFunctorDiscreteCompEvaluationIso (C : Type*) [Category* C] {J : Type*} (j : J) :
    (piEquivalenceFunctorDiscrete J C).functor ⋙ (evaluation _ _).obj ⟨j⟩ ≅ Pi.eval _ j :=
  NatIso.ofComponents fun _ ↦ Iso.refl _

/-- A category is discrete when there is at most one morphism between two objects,
in which case they are equal. -/
/-
**CategoryTheory.IsDiscrete** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory`。
形式化陈述：IsDiscrete (C : Type*) [Category* C] : Prop where subsingleton (X Y : C) :
 Subsingleton (X ⟶ Y)
参数：C : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category is discrete when there is at most one morphism between two objects,
in which case they are equal.
-/
class IsDiscrete (C : Type*) [Category* C] : Prop where
  subsingleton (X Y : C) : Subsingleton (X ⟶ Y) := by infer_instance
  eq_of_hom {X Y : C} (f : X ⟶ Y) : X = Y

attribute [instance] IsDiscrete.subsingleton
/-
**CategoryTheory.Discrete.isDiscrete** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.D
iscrete`。
形式化陈述：∀ (C : Type u_1), CategoryTheory.IsDiscrete (CategoryTheory.Discrete C)
参数：C : Type u_1；CategoryTheory.Discrete C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Discrete.isDiscrete (C : Type*) : IsDiscrete (Discrete C) where
  eq_of_hom := by rintro ⟨_⟩ ⟨_⟩ ⟨⟨rfl⟩⟩; rfl

section

variable {C : Type*} [Category* C] [IsDiscrete C]

/-
**CategoryTheory.obj_ext_of_isDiscrete** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
`。
形式化陈述：obj_ext_of_isDiscrete {X Y : C} (f : X ⟶ Y) : X = Y
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsDiscrete.eq_of_hom`：∀ {C : Type u_1} {inst : CategoryTh
eory.Category.{v_1, u_1} C} [self : CategoryTheory.IsDiscrete C] {X Y : C}   (f 
: X ⟶ Y), X = Y
-/
lemma obj_ext_of_isDiscrete {X Y : C} (f : X ⟶ Y) : X = Y := IsDiscrete.eq_of_hom f
/-
**CategoryTheory.isIso_of_isDiscrete** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：isIso_of_isDiscrete {X Y : C} (f : X ⟶ Y) : IsIso f
参数：f : X ⟶ Y。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.IsDiscrete.eq_of_hom`：∀ {C : Type u_1} {inst : CategoryTh
eory.Category.{v_1, u_1} C} [self : CategoryTheory.IsDiscrete C] {X Y : C}   (f 
: X ⟶ Y), X = Y
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `CategoryTheory.IsDiscrete.subsingleton`：∀ {C : Type u_1} {inst : Categor
yTheory.Category.{v_1, u_1} C} [self : CategoryTheory.IsDiscrete C] (X Y : C),  
 Subsingleton (X ⟶ Y)
-/
instance isIso_of_isDiscrete {X Y : C} (f : X ⟶ Y) : IsIso f :=
  ⟨eqToHom (IsDiscrete.eq_of_hom f).symm, by cat_disch⟩
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsDiscrete Cᵒᵖ where
  eq_of_hom := by
    rintro ⟨_⟩ ⟨_⟩ ⟨f⟩
    obtain rfl := obj_ext_of_isDiscrete f
    rfl

end

end CategoryTheory

