/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Functor.Hom

/-!
# The Yoneda embedding

Let `C : Type u₁` be a category (with `Category.{v₁} C`). We define
the Yoneda embedding as a fully faithful functor `yoneda : C ⥤ Cᵒᵖ ⥤ Type v₁`,
In addition to `yoneda`, we also define `uliftYoneda : C ⥤ Cᵒᵖ ⥤ Type (max w v₁)`
with the additional universe parameter `w`. When `C` is locally `w`-small,
one may also use `shrinkYoneda.{w} : C ⥤ Cᵒᵖ ⥤ Type w` from the file
`Mathlib/CategoryTheory/ShrinkYoneda.lean`.

The naturality of the bijection `yonedaEquiv` involved in the
Yoneda lemma is also expressed as a natural isomorphism
`yonedaLemma : yonedaPairing C ≅ yonedaEvaluation C`.

## References
* [Stacks: Opposite Categories and the Yoneda Lemma](https://stacks.math.columbia.edu/tag/001L)
-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

namespace CategoryTheory

open Opposite CategoryTheory.Functor

universe w v v₁ v₂ u₁ u₂

-- morphism levels before object levels. See note [category theory universes].
variable {C : Type u₁} [Category.{v₁} C]

/-- The Yoneda embedding, as a functor from `C` into presheaves on `C`. -/
@[implicit_reducible, simps obj_obj obj_map map_app, stacks 001O]
/-
**CategoryTheory.yoneda** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：yoneda : C ⥤ Cᵒᵖ ⥤ Type v₁ where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Yoneda embedding, as a functor from `C` into presheaves on `C`.
-/
def yoneda : C ⥤ Cᵒᵖ ⥤ Type v₁ where
  obj X :=
    { obj Y := (unop Y) ⟶ X
      map f := ↾fun g ↦ f.unop ≫ g }
  map f :=
    { app _ := ↾fun g ↦ g ≫ f }

/-- Unification hint for `(yoneda.obj X).obj (op Y) = Y ⟶ X`. -/
unif_hint yoneda_obj_obj_eq_hom (X X' Y Y' : C) where
  X ≟ X'
  Y ≟ Y' ⊢
  (yoneda.obj X).obj (op Y) ≟ Y' ⟶ X'

/-- Unification hint for `(yoneda.obj X).obj Y = unop Y ⟶ X`. -/
unif_hint yoneda_obj_obj_eq_hom' (X X' : C) (Y Y' : Cᵒᵖ) where
  X ≟ X'
  Y ≟ Y' ⊢
  (yoneda.obj X).obj Y ≟ unop Y' ⟶ X'

/-- Variant of the Yoneda embedding which allows a raise in the universe level
for the category of types. -/
@[pp_with_univ, simps! obj_obj obj_map map_app]
/-
**CategoryTheory.uliftYoneda** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：uliftYoneda : C ⥤ Cᵒᵖ ⥤ Type (max w v₁)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Variant of the Yoneda embedding which allows a raise in the universe level
for the category of types.
-/
def uliftYoneda : C ⥤ Cᵒᵖ ⥤ Type (max w v₁) :=
  yoneda ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{w}

/-- Unification hint for `(uliftYoneda.obj X).obj (op Y) ≃ ULift (Y ⟶ X)`. -/
unif_hint uliftYoneda_obj_obj_eq_hom (X X' Y Y' : C) where
  X ≟ X'
  Y ≟ Y' ⊢
  (uliftYoneda.{w}.obj X).obj (op Y) ≟ ULift (Y' ⟶ X')

/-- Unification hint for `(uliftYoneda.obj X).obj Y = ULift (unop Y ⟶ X)`. -/
unif_hint uliftYoneda_obj_obj_eq_hom' (X X' : C) (Y Y' : Cᵒᵖ) where
  X ≟ X'
  Y ≟ Y' ⊢
  (uliftYoneda.{w}.obj X).obj Y ≟ ULift (unop Y' ⟶ X')

/-- If `C` is a category with `[Category.{max w v₁} C]`, this is the isomorphism
`uliftYoneda.{w} (C := C) ≅ yoneda`. -/
@[simps! inv_app_app hom_app_app]
/-
**CategoryTheory.uliftYonedaIsoYoneda** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`
。
形式化陈述：uliftYonedaIsoYoneda {C : Type u₁} [Category.{max w v₁} C] : uliftYoneda.{
w} (C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `C` is a category with `[Category.{max w v₁} C]`, this is the isomorphism
`uliftYoneda.{w} (C := C) ≅ yoneda`.
-/
def uliftYonedaIsoYoneda {C : Type u₁} [Category.{max w v₁} C] :
    uliftYoneda.{w} (C := C) ≅ yoneda :=
  NatIso.ofComponents (fun _ ↦ NatIso.ofComponents (fun _ ↦ Equiv.ulift.toIso))

/-- The co-Yoneda embedding, as a functor from `Cᵒᵖ` into co-presheaves on `C`.
-/
/-
**CategoryTheory.coyoneda** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：coyoneda : Cᵒᵖ ⥤ C ⥤ Type v₁
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The co-Yoneda embedding, as a functor from `Cᵒᵖ` into co-presheaves on `C`.
-/
abbrev coyoneda : Cᵒᵖ ⥤ C ⥤ Type v₁ := yoneda.flip

/-- Unification hint for `(coyoneda.obj (op X)).obj Y = X ⟶ Y`. -/
unif_hint coyoneda_obj_obj_eq_hom (X X' Y Y' : C) where
  X ≟ X'
  Y ≟ Y' ⊢
  (coyoneda.obj (op X)).obj Y ≟ X' ⟶ Y'

/-- Unification hint for `(coyoneda.obj Y).obj X = unop Y ⟶ X`. -/
unif_hint coyoneda_obj_obj_eq_hom' (X X' : C) (Y Y' : Cᵒᵖ) where
  X ≟ X'
  Y ≟ Y' ⊢
  (coyoneda.obj Y).obj X ≟ unop Y' ⟶ X'

/-- Variant of the Coyoneda embedding which allows a raise in the universe level
for the category of types. -/
@[pp_with_univ]
/-
**CategoryTheory.uliftCoyoneda** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：uliftCoyoneda : Cᵒᵖ ⥤ C ⥤ Type (max w v₁)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Variant of the Coyoneda embedding which allows a raise in the universe level
for the category of types.
-/
abbrev uliftCoyoneda : Cᵒᵖ ⥤ C ⥤ Type (max w v₁) := uliftYoneda.{w}.flip

/-- Unification hint for `(uliftCoyoneda.{w}.obj (op X)).obj Y = ULift (Y ⟶ X)`. -/
unif_hint uliftCoyoneda_obj_obj_eq_hom (X X' Y Y' : C) where
  X ≟ X'
  Y ≟ Y' ⊢
  (uliftCoyoneda.{w}.obj (op X)).obj Y ≟ ULift (Y' ⟶ X')

/-- Unification hint for `(uliftCoyoneda.{w}.obj X).obj Y = ULift (unop Y ⟶ X)`. -/
unif_hint uliftCoyoneda_obj_obj_eq_hom' (X X' : Cᵒᵖ) (Y Y' : C) where
  X ≟ X'
  Y ≟ Y' ⊢
  (uliftCoyoneda.{w}.obj X).obj Y ≟ ULift (Y' ⟶ unop X')

/-- If `C` is a category with `[Category.{max w v₁} C]`, this is the isomorphism
`uliftCoyoneda.{w} (C := C) ≅ coyoneda`. -/
@[simps! inv_app_app hom_app_app]
/-
**CategoryTheory.uliftCoyonedaIsoCoyoneda** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory`。
形式化陈述：uliftCoyonedaIsoCoyoneda {C : Type u₁} [Category.{max w v₁} C] : uliftCoyo
neda.{w} (C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `C` is a category with `[Category.{max w v₁} C]`, this is the isomorphism
`uliftCoyoneda.{w} (C := C) ≅ coyoneda`.
-/
def uliftCoyonedaIsoCoyoneda {C : Type u₁} [Category.{max w v₁} C] :
    uliftCoyoneda.{w} (C := C) ≅ coyoneda :=
  NatIso.ofComponents (fun _ ↦ NatIso.ofComponents (fun _ ↦ Equiv.ulift.toIso))

namespace Yoneda

/-
**CategoryTheory.Yoneda.obj_map_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Yon
eda`。
形式化陈述：obj_map_id {X Y : C} (f : op X ⟶ op Y) : (yoneda.obj X).map f (𝟙 X) = (yon
eda.map f.unop).app (op Y) (𝟙 Y)
参数：f : op X ⟶ op Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem obj_map_id {X Y : C} (f : op X ⟶ op Y) :
    (yoneda.obj X).map f (𝟙 X) = (yoneda.map f.unop).app (op Y) (𝟙 Y) := by
  simp

/-- The Yoneda embedding is fully faithful. -/
/-
**CategoryTheory.Yoneda.fullyFaithful** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Yoneda`。
形式化陈述：fullyFaithful : (yoneda (C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Yoneda embedding is fully faithful.
-/
def fullyFaithful : (yoneda (C := C)).FullyFaithful where
  preimage f := f.app _ (𝟙 _)
  map_preimage := by -- this was automatic
    intro Z W f
    ext X x
    have := f.naturality_apply x.op (𝟙 Z)
    cat_disch
/-
**CategoryTheory.Yoneda.fullyFaithful_preimage** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Yoneda`。
形式化陈述：fullyFaithful_preimage {X Y : C} (f : yoneda.obj X ⟶ yoneda.obj Y) : fully
Faithful.preimage f = f.app (op X) (𝟙 X)
参数：f : yoneda.obj X ⟶ yoneda.obj Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma fullyFaithful_preimage {X Y : C} (f : yoneda.obj X ⟶ yoneda.obj Y) :
    fullyFaithful.preimage f = f.app (op X) (𝟙 X) := rfl

/-- The Yoneda embedding is full. -/
@[stacks 001P]
/-
**CategoryTheory.Yoneda.yoneda_full** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Yo
neda`。
形式化陈述：yoneda_full : (yoneda : C ⥤ Cᵒᵖ ⥤ Type v₁).Full
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.FullyFaithful.full`：full : F.Full where map_surje
ctive

--- 原说明 ---
The Yoneda embedding is full.
-/
instance yoneda_full : (yoneda : C ⥤ Cᵒᵖ ⥤ Type v₁).Full :=
  fullyFaithful.full

/-- The Yoneda embedding is faithful. -/
@[stacks 001P]
/-
**CategoryTheory.Yoneda.yoneda_faithful** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.Yoneda`。
形式化陈述：yoneda_faithful : (yoneda : C ⥤ Cᵒᵖ ⥤ Type v₁).Faithful
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.FullyFaithful.faithful`：faithful : F.Faithful whe
re map_injective

--- 原说明 ---
The Yoneda embedding is faithful.
-/
instance yoneda_faithful : (yoneda : C ⥤ Cᵒᵖ ⥤ Type v₁).Faithful :=
  fullyFaithful.faithful

/-- Extensionality via Yoneda. The typical usage would be
```
-- Goal is `X ≅ Y`
apply Yoneda.ext
-- Goals are now functions `(Z ⟶ X) → (Z ⟶ Y)`, `(Z ⟶ Y) → (Z ⟶ X)`, and the fact that these
-- functions are inverses and natural in `Z`.
```
-/
/-
**CategoryTheory.Yoneda.ext** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Yoneda`。
形式化陈述：ext (X Y : C) (p : forall {Z : C}, (Z ⟶ X) -> (Z ⟶ Y)) (q : forall {Z : C}
, (Z ⟶ Y) -> (Z ⟶ X)) (h₁ : forall {Z : C} (f : Z ⟶ X), q (p f) = f) (h₂ : foral
l {Z : C} (f : Z ⟶ Y), p (q f) = f) (n : forall {Z Z' : C} (f : Z' ⟶ Z) (g : Z ⟶
 X), p (f ≫ g) = f ≫ p g) : X ≅ Y
参数：X Y : C；p : forall {Z : C}, (Z ⟶ X) -> (Z ⟶ Y)；q : forall {Z : C}, (Z ⟶ Y) ->
 (Z ⟶ X)；h₁ : forall {Z : C} (f : Z ⟶ X), q (p f) = f；h₂ : forall {Z : C} (f : Z
 ⟶ Y), p (q f) = f；n : forall {Z Z' : C} (f : Z' ⟶ Z) (g : Z ⟶ X), p (f ≫ g) = f
 ≫ p g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extensionality via Yoneda. The typical usage would be
```
-- Goal is `X ≅ Y`
apply Yoneda.ext
-- Goals are now functions `(Z ⟶ X) → (Z ⟶ Y)`, `(Z ⟶ Y) → (Z ⟶ X)`, and the fac
t that these
-- functions are inverses and natural in `Z`.
```
-/
def ext (X Y : C) (p : ∀ {Z : C}, (Z ⟶ X) → (Z ⟶ Y))
    (q : ∀ {Z : C}, (Z ⟶ Y) → (Z ⟶ X))
    (h₁ : ∀ {Z : C} (f : Z ⟶ X), q (p f) = f) (h₂ : ∀ {Z : C} (f : Z ⟶ Y), p (q f) = f)
    (n : ∀ {Z Z' : C} (f : Z' ⟶ Z) (g : Z ⟶ X), p (f ≫ g) = f ≫ p g) : X ≅ Y :=
  fullyFaithful.preimageIso
    (NatIso.ofComponents fun Z =>
      { hom := ↾p
        inv := ↾q })

/-- If `yoneda.map f` is an isomorphism, so was `f`.
-/
/-
**CategoryTheory.Yoneda.isIso** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Yoneda`。
形式化陈述：isIso {X Y : C} (f : X ⟶ Y) [IsIso (yoneda.map f)] : IsIso f
参数：f : X ⟶ Y；yoneda.map f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.isIso_of_fully_faithful`：isIso_of_fully_faithful (f : X ⟶
 Y) [IsIso (F.map f)] : IsIso f

--- 原说明 ---
If `yoneda.map f` is an isomorphism, so was `f`.
-/
theorem isIso {X Y : C} (f : X ⟶ Y) [IsIso (yoneda.map f)] : IsIso f :=
  isIso_of_fully_faithful yoneda f

end Yoneda

namespace ULiftYoneda

variable (C)

/-- When `C` is a category such that `Category.{v₁} C`, then
the functor `uliftYoneda.{w} : C ⥤ Cᵒᵖ ⥤ Type (max w v₁)` is fully faithful. -/
/-
**CategoryTheory.ULiftYoneda.fullyFaithful** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.ULiftYoneda`。
形式化陈述：fullyFaithful : (uliftYoneda.{w} (C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `C` is a category such that `Category.{v₁} C`, then
the functor `uliftYoneda.{w} : C ⥤ Cᵒᵖ ⥤ Type (max w v₁)` is fully faithful.
-/
def fullyFaithful : (uliftYoneda.{w} (C := C)).FullyFaithful :=
  Yoneda.fullyFaithful.comp (fullyFaithfulULiftFunctor.whiskeringRight _)
/-
**CategoryTheory.ULiftYoneda.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ULiftYon
eda`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (uliftYoneda.{w} (C := C)).Full :=
  (fullyFaithful C).full
/-
**CategoryTheory.ULiftYoneda.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ULiftYon
eda`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (uliftYoneda.{w} (C := C)).Faithful :=
  (fullyFaithful C).faithful

end ULiftYoneda

namespace Coyoneda

/-- The co-Yoneda embedding is fully faithful. -/
/-
**CategoryTheory.Coyoneda.fullyFaithful** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Coyoneda`。
形式化陈述：fullyFaithful : (coyoneda (C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The co-Yoneda embedding is fully faithful.
-/
def fullyFaithful : (coyoneda (C := C)).FullyFaithful where
  preimage f := (f.app _ (𝟙 _)).op
  map_preimage := by
    intro Z W f
    ext X x
    have := f.naturality_apply x (𝟙 (unop Z))
    cat_disch
/-
**CategoryTheory.Coyoneda.fullyFaithful_preimage** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Coyoneda`。
形式化陈述：fullyFaithful_preimage {X Y : Cᵒᵖ} (f : coyoneda.obj X ⟶ coyoneda.obj Y) :
 fullyFaithful.preimage f = (f.app X.unop (𝟙 X.unop)).op
参数：f : coyoneda.obj X ⟶ coyoneda.obj Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma fullyFaithful_preimage {X Y : Cᵒᵖ} (f : coyoneda.obj X ⟶ coyoneda.obj Y) :
    fullyFaithful.preimage f = (f.app X.unop (𝟙 X.unop)).op := rfl

/-- The morphism `X ⟶ Y` corresponding to a natural transformation
`coyoneda.obj X ⟶ coyoneda.obj Y`. -/
/-
**CategoryTheory.Coyoneda.preimage** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Coy
oneda`。
形式化陈述：preimage {X Y : Cᵒᵖ} (f : coyoneda.obj X ⟶ coyoneda.obj Y) : X ⟶ Y
参数：f : coyoneda.obj X ⟶ coyoneda.obj Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `X ⟶ Y` corresponding to a natural transformation
`coyoneda.obj X ⟶ coyoneda.obj Y`.
-/
def preimage {X Y : Cᵒᵖ} (f : coyoneda.obj X ⟶ coyoneda.obj Y) : X ⟶ Y :=
  (f.app _ (𝟙 X.unop)).op
/-
**CategoryTheory.Coyoneda.coyoneda_full** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.Coyoneda`。
形式化陈述：coyoneda_full : (coyoneda : Cᵒᵖ ⥤ C ⥤ Type v₁).Full
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.FullyFaithful.full`：full : F.Full where map_surje
ctive
-/
instance coyoneda_full : (coyoneda : Cᵒᵖ ⥤ C ⥤ Type v₁).Full :=
  fullyFaithful.full
/-
**CategoryTheory.Coyoneda.coyoneda_faithful** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.Coyoneda`。
形式化陈述：coyoneda_faithful : (coyoneda : Cᵒᵖ ⥤ C ⥤ Type v₁).Faithful
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.FullyFaithful.faithful`：faithful : F.Faithful whe
re map_injective
-/
instance coyoneda_faithful : (coyoneda : Cᵒᵖ ⥤ C ⥤ Type v₁).Faithful :=
  fullyFaithful.faithful

/-- Extensionality via Coyoneda. The typical usage would be
```
-- Goal is `X ≅ Y`
apply Coyoneda.ext
-- Goals are now functions `(X ⟶ Z) → (Y ⟶ Z)`, `(Y ⟶ Z) → (X ⟶ Z)`, and the fact that these
-- functions are inverses and natural in `Z`.
```
-/
/-
**CategoryTheory.Coyoneda.ext** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Coyoneda
`。
形式化陈述：ext (X Y : C) (p : forall {Z : C}, (X ⟶ Z) -> (Y ⟶ Z)) (q : forall {Z : C}
, (Y ⟶ Z) -> (X ⟶ Z)) (h₁ : forall {Z : C} (f : X ⟶ Z), q (p f) = f) (h₂ : foral
l {Z : C} (f : Y ⟶ Z), p (q f) = f) (n : forall {Z Z' : C} (f : Y ⟶ Z) (g : Z ⟶ 
Z'), q (f ≫ g) = q f ≫ g) : X ≅ Y
参数：X Y : C；p : forall {Z : C}, (X ⟶ Z) -> (Y ⟶ Z)；q : forall {Z : C}, (Y ⟶ Z) ->
 (X ⟶ Z)；h₁ : forall {Z : C} (f : X ⟶ Z), q (p f) = f；h₂ : forall {Z : C} (f : Y
 ⟶ Z), p (q f) = f；n : forall {Z Z' : C} (f : Y ⟶ Z) (g : Z ⟶ Z'), q (f ≫ g) = q
 f ≫ g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extensionality via Coyoneda. The typical usage would be
```
-- Goal is `X ≅ Y`
apply Coyoneda.ext
-- Goals are now functions `(X ⟶ Z) → (Y ⟶ Z)`, `(Y ⟶ Z) → (X ⟶ Z)`, and the fac
t that these
-- functions are inverses and natural in `Z`.
```
-/
def ext (X Y : C) (p : ∀ {Z : C}, (X ⟶ Z) → (Y ⟶ Z))
    (q : ∀ {Z : C}, (Y ⟶ Z) → (X ⟶ Z))
    (h₁ : ∀ {Z : C} (f : X ⟶ Z), q (p f) = f) (h₂ : ∀ {Z : C} (f : Y ⟶ Z), p (q f) = f)
    (n : ∀ {Z Z' : C} (f : Y ⟶ Z) (g : Z ⟶ Z'), q (f ≫ g) = q f ≫ g) : X ≅ Y :=
  fullyFaithful.preimageIso
    (NatIso.ofComponents (fun Z =>
      { hom := ↾q
        inv := ↾p })) |>.unop

/-- If `coyoneda.map f` is an isomorphism, so was `f`.
-/
/-
**CategoryTheory.Coyoneda.isIso** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Coyone
da`。
形式化陈述：isIso {X Y : Cᵒᵖ} (f : X ⟶ Y) [IsIso (coyoneda.map f)] : IsIso f
参数：f : X ⟶ Y；coyoneda.map f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.isIso_of_fully_faithful`：isIso_of_fully_faithful (f : X ⟶
 Y) [IsIso (F.map f)] : IsIso f

--- 原说明 ---
If `coyoneda.map f` is an isomorphism, so was `f`.
-/
theorem isIso {X Y : Cᵒᵖ} (f : X ⟶ Y) [IsIso (coyoneda.map f)] : IsIso f :=
  isIso_of_fully_faithful coyoneda f

/-- The identity functor on `Type` is isomorphic to the coyoneda functor coming from `PUnit`. -/
/-
**CategoryTheory.Coyoneda.punitIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Coy
oneda`。
形式化陈述：punitIso : coyoneda.obj (Opposite.op PUnit) ≅ 𝟭 (Type v₁)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity functor on `Type` is isomorphic to the coyoneda functor coming from
 `PUnit`.
-/
def punitIso : coyoneda.obj (Opposite.op PUnit) ≅ 𝟭 (Type v₁) :=
  NatIso.ofComponents fun X =>
    { hom := ↾fun f => f.hom ⟨⟩
      inv := ↾fun x => ↾fun _ => x }

/-- Taking the `unop` of morphisms is a natural isomorphism. -/
@[simps! inv_app hom_app]
/-
**CategoryTheory.Coyoneda.objOpOp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Coyo
neda`。
形式化陈述：objOpOp (X : C) : coyoneda.obj (op (op X)) ≅ yoneda.obj X
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Taking the `unop` of morphisms is a natural isomorphism.
-/
def objOpOp (X : C) : coyoneda.obj (op (op X)) ≅ yoneda.obj X :=
  NatIso.ofComponents fun _ => (opEquiv _ _).toIso

/-- Taking the `unop` of morphisms is a natural isomorphism. -/
/-
**CategoryTheory.Coyoneda.opIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Coyone
da`。
形式化陈述：opIso : yoneda ⋙ (whiskeringLeft _ _ _).obj (opOp C) ≅ coyoneda
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Taking the `unop` of morphisms is a natural isomorphism.
-/
def opIso : yoneda ⋙ (whiskeringLeft _ _ _).obj (opOp C) ≅ coyoneda :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents (fun Y ↦ (opEquiv (op Y) X).toIso)
    (fun _ ↦ rfl)) (fun _ ↦ rfl)

namespace ULiftCoyoneda

variable (C)

/-- When `C` is a category such that `Category.{v₁} C`, then
the functor `uliftCoyoneda.{w} : C ⥤ Cᵒᵖ ⥤ Type (max w v₁)` is fully faithful. -/
/-
**CategoryTheory.Coyoneda.ULiftCoyoneda.fullyFaithful** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Coyoneda.ULiftCoyoneda`。
形式化陈述：fullyFaithful : (uliftCoyoneda.{w} (C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `C` is a category such that `Category.{v₁} C`, then
the functor `uliftCoyoneda.{w} : C ⥤ Cᵒᵖ ⥤ Type (max w v₁)` is fully faithful.
-/
def fullyFaithful : (uliftCoyoneda.{w} (C := C)).FullyFaithful :=
  Coyoneda.fullyFaithful.comp (fullyFaithfulULiftFunctor.whiskeringRight _)
/-
**CategoryTheory.Coyoneda.ULiftCoyoneda.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Coyoneda.ULiftCoyoneda`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (uliftCoyoneda.{w} (C := C)).Full :=
  (fullyFaithful C).full
/-
**CategoryTheory.Coyoneda.ULiftCoyoneda.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Coyoneda.ULiftCoyoneda`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (uliftCoyoneda.{w} (C := C)).Faithful :=
  (fullyFaithful C).faithful

end ULiftCoyoneda

end Coyoneda

namespace Functor

/-- The data which expresses that a functor `F : Cᵒᵖ ⥤ Type v` is representable by `Y : C`.

In the situation where `F` factors through a concrete category, it may be more convenient to use
the API in the file `Mathlib/CategoryTheory/ConcreteCategory/Representable.lean`. -/
/-
**CategoryTheory.Functor.RepresentableBy** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheo
ry.Functor`。
形式化陈述：RepresentableBy (F : Cᵒᵖ ⥤ Type v) (Y : C) where /-- the natural bijection
 `(X ⟶ Y) ≃ F.obj (op X)`. -/ homEquiv {X : C} : (X ⟶ Y) ≃ F.obj (op X) homEquiv
_comp {X X' : C} (f : X ⟶ X') (g : X' ⟶ Y) : homEquiv (f ≫ g) = F.map f.op (homE
quiv g)
参数：F : Cᵒᵖ ⥤ Type v；Y : C；X ⟶ Y；op X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The data which expresses that a functor `F : Cᵒᵖ ⥤ Type v` is representable by `
Y : C`.

In the situation where `F` factors through a concrete category, it may be more c
onvenient to use
the API in the file `Mathlib/CategoryTheory/ConcreteCategory/Representable.lean`
.
-/
structure RepresentableBy (F : Cᵒᵖ ⥤ Type v) (Y : C) where
  /-- the natural bijection `(X ⟶ Y) ≃ F.obj (op X)`. -/
  homEquiv {X : C} : (X ⟶ Y) ≃ F.obj (op X)
  homEquiv_comp {X X' : C} (f : X ⟶ X') (g : X' ⟶ Y) :
    homEquiv (f ≫ g) = F.map f.op (homEquiv g) := by cat_disch
/-
**CategoryTheory.Functor.RepresentableBy.comp_homEquiv_symm** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Functor.RepresentableBy`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {F : CategoryT
heory.Functor Cᵒᵖ (Type v)} {Y : C}   (e : F.RepresentableBy Y) {X X' : C} (x : 
F.obj (Opposite.op X')) (f : X ⟶ X'),   CategoryTheory.CategoryStruct.comp f (e.
homEquiv.symm x) =     e.homEquiv.symm ((CategoryTheory.ConcreteCategory.hom (F.
map f.op)) x)
参数：Type v；e : F.RepresentableBy Y；x : F.obj (Opposite.op X')；f : X ⟶ X'；e.homEqu
iv.symm x；(CategoryTheory.ConcreteCategory.hom (F.map f.op)) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.RepresentableBy.homEquiv_comp`：∀ {C : Type u₁} [i
nst : CategoryTheory.Category.{v₁, u₁} C] {F : CategoryTheory.Functor Cᵒᵖ (Type 
v)} {Y : C}   (self : F.RepresentableBy Y)…
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma RepresentableBy.comp_homEquiv_symm {F : Cᵒᵖ ⥤ Type v} {Y : C}
    (e : F.RepresentableBy Y) {X X' : C} (x : F.obj (op X')) (f : X ⟶ X') :
    f ≫ e.homEquiv.symm x = e.homEquiv.symm (F.map f.op x) :=
  e.homEquiv.injective (by simp [homEquiv_comp])
/-
**CategoryTheory.Functor.RepresentableBy.homEquiv_unop_comp** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Functor.RepresentableBy`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {F : CategoryT
heory.Functor Cᵒᵖ (Type u_1)} {Y : C}   (h : F.RepresentableBy Y) {X : Cᵒᵖ} {X' 
: C} (f : Opposite.op X' ⟶ X) (g : X' ⟶ Y),   h.homEquiv (CategoryTheory.Categor
yStruct.comp f.unop g) =     (CategoryTheory.ConcreteCategory.hom (F.map f)) (h.
homEquiv g)
参数：Type u_1；h : F.RepresentableBy Y；f : Opposite.op X' ⟶ X；g : X' ⟶ Y；CategoryTh
eory.CategoryStruct.comp f.unop g；CategoryTheory.ConcreteCategory.hom (F.map f)；
h.homEquiv g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.RepresentableBy.homEquiv_comp`：∀ {C : Type u₁} [i
nst : CategoryTheory.Category.{v₁, u₁} C] {F : CategoryTheory.Functor Cᵒᵖ (Type 
v)} {Y : C}   (self : F.RepresentableBy Y)…
-/
lemma RepresentableBy.homEquiv_unop_comp {F : Cᵒᵖ ⥤ Type*} {Y : C}
    (h : F.RepresentableBy Y) {X : Cᵒᵖ} {X' : C} (f : Opposite.op X' ⟶ X) (g : X' ⟶ Y) :
    h.homEquiv (f.unop ≫ g) = F.map f (h.homEquiv g) :=
  h.homEquiv_comp _ _

/-- If `F ≅ F'`, and `F` is representable, then `F'` is representable. -/
/-
**CategoryTheory.Functor.RepresentableBy.ofIso** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Functor.RepresentableBy`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {F F' 
: CategoryTheory.Functor Cᵒᵖ (Type v)} → {Y : C} → F.RepresentableBy Y → (F ≅ F'
) → F'.RepresentableBy Y
参数：Type v；F ≅ F'。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
If `F ≅ F'`, and `F` is representable, then `F'` is representable.
-/
def RepresentableBy.ofIso {F F' : Cᵒᵖ ⥤ Type v} {Y : C} (e : F.RepresentableBy Y)
    (e' : F ≅ F') : F'.RepresentableBy Y where
  homEquiv {X} := e.homEquiv.trans (e'.app _).toEquiv
  homEquiv_comp {X X'} f g := by
    dsimp
    rw [e.homEquiv_comp]
    apply e'.hom.naturality_apply

/-- The data which expresses that a functor `F : C ⥤ Type v` is corepresentable by `X : C`. -/
/-
**CategoryTheory.Functor.CorepresentableBy** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTh
eory.Functor`。
形式化陈述：CorepresentableBy (F : C ⥤ Type v) (X : C) where /-- the natural bijection
 `(X ⟶ Y) ≃ F.obj Y`. -/ homEquiv {Y : C} : (X ⟶ Y) ≃ F.obj Y homEquiv_comp {Y Y
' : C} (g : Y ⟶ Y') (f : X ⟶ Y) : homEquiv (f ≫ g) = F.map g (homEquiv f)
参数：F : C ⥤ Type v；X : C；X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The data which expresses that a functor `F : C ⥤ Type v` is corepresentable by `
X : C`.
-/
structure CorepresentableBy (F : C ⥤ Type v) (X : C) where
  /-- the natural bijection `(X ⟶ Y) ≃ F.obj Y`. -/
  homEquiv {Y : C} : (X ⟶ Y) ≃ F.obj Y
  homEquiv_comp {Y Y' : C} (g : Y ⟶ Y') (f : X ⟶ Y) :
    homEquiv (f ≫ g) = F.map g (homEquiv f) := by cat_disch
/-
**CategoryTheory.Functor.CorepresentableBy.homEquiv_symm_comp** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Functor.CorepresentableBy`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {F : CategoryT
heory.Functor C (Type v)} {X : C}   (e : F.CorepresentableBy X) {Y Y' : C} (y : 
F.obj Y) (g : Y ⟶ Y'),   CategoryTheory.CategoryStruct.comp (e.homEquiv.symm y) 
g =     e.homEquiv.symm ((CategoryTheory.ConcreteCategory.hom (F.map g)) y)
参数：Type v；e : F.CorepresentableBy X；y : F.obj Y；g : Y ⟶ Y'；e.homEquiv.symm y；(Ca
tegoryTheory.ConcreteCategory.hom (F.map g)) y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.CorepresentableBy.homEquiv_comp`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {F : CategoryTheory.Functor C (Type 
v)} {X : C}   (self : F.CorepresentableBy X)…
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma CorepresentableBy.homEquiv_symm_comp {F : C ⥤ Type v} {X : C}
    (e : F.CorepresentableBy X) {Y Y' : C} (y : F.obj Y) (g : Y ⟶ Y') :
    e.homEquiv.symm y ≫ g = e.homEquiv.symm (F.map g y) :=
  e.homEquiv.injective (by simp [homEquiv_comp])

/-- If `F ≅ F'`, and `F` is corepresentable, then `F'` is corepresentable. -/
/-
**CategoryTheory.Functor.CorepresentableBy.ofIso** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Functor.CorepresentableBy`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {F F' 
: CategoryTheory.Functor C (Type v)} → {X : C} → F.CorepresentableBy X → (F ≅ F'
) → F'.CorepresentableBy X
参数：Type v；F ≅ F'。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
If `F ≅ F'`, and `F` is corepresentable, then `F'` is corepresentable.
-/
def CorepresentableBy.ofIso {F F' : C ⥤ Type v} {X : C} (e : F.CorepresentableBy X)
    (e' : F ≅ F') :
    F'.CorepresentableBy X where
  homEquiv {X} := e.homEquiv.trans (e'.app _).toEquiv
  homEquiv_comp {Y Y'} g f := by
    dsimp
    rw [e.homEquiv_comp]
    apply e'.hom.naturality_apply
/-
**CategoryTheory.Functor.RepresentableBy.homEquiv_eq** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Functor.RepresentableBy`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {F : CategoryT
heory.Functor Cᵒᵖ (Type v)} {Y : C}   (e : F.RepresentableBy Y) {X : C} (f : X ⟶
 Y),   e.homEquiv f = (CategoryTheory.ConcreteCategory.hom (F.map f.op)) (e.homE
quiv (CategoryTheory.CategoryStruct.id Y))
参数：Type v；e : F.RepresentableBy Y；f : X ⟶ Y；CategoryTheory.ConcreteCategory.hom 
(F.map f.op)；e.homEquiv (CategoryTheory.CategoryStruct.id Y)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Functor.RepresentableBy.homEquiv_comp`：∀ {C : Type u₁} [i
nst : CategoryTheory.Category.{v₁, u₁} C] {F : CategoryTheory.Functor Cᵒᵖ (Type 
v)} {Y : C}   (self : F.RepresentableBy Y)…
-/
lemma RepresentableBy.homEquiv_eq {F : Cᵒᵖ ⥤ Type v} {Y : C} (e : F.RepresentableBy Y)
    {X : C} (f : X ⟶ Y) :
    e.homEquiv f = F.map f.op (e.homEquiv (𝟙 Y)) := by
  conv_lhs => rw [← Category.comp_id f, e.homEquiv_comp]
/-
**CategoryTheory.Functor.CorepresentableBy.homEquiv_eq** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Functor.CorepresentableBy`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {F : CategoryT
heory.Functor C (Type v)} {X : C}   (e : F.CorepresentableBy X) {Y : C} (f : X ⟶
 Y),   e.homEquiv f = (CategoryTheory.ConcreteCategory.hom (F.map f)) (e.homEqui
v (CategoryTheory.CategoryStruct.id X))
参数：Type v；e : F.CorepresentableBy X；f : X ⟶ Y；CategoryTheory.ConcreteCategory.ho
m (F.map f)；e.homEquiv (CategoryTheory.CategoryStruct.id X)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Functor.CorepresentableBy.homEquiv_comp`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {F : CategoryTheory.Functor C (Type 
v)} {X : C}   (self : F.CorepresentableBy X)…
-/
lemma CorepresentableBy.homEquiv_eq {F : C ⥤ Type v} {X : C} (e : F.CorepresentableBy X)
    {Y : C} (f : X ⟶ Y) :
    e.homEquiv f = F.map f (e.homEquiv (𝟙 X)) := by
  conv_lhs => rw [← Category.id_comp f, e.homEquiv_comp]

/-- Representing objects are unique up to isomorphism. -/
@[simps!]
/-
**CategoryTheory.Functor.RepresentableBy.uniqueUpToIso** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Functor.RepresentableBy`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {F : C
ategoryTheory.Functor Cᵒᵖ (Type v)} → {Y Y' : C} → F.RepresentableBy Y → F.Repre
sentableBy Y' → (Y ≅ Y')
参数：Type v；Y ≅ Y'。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Representing objects are unique up to isomorphism.
-/
def RepresentableBy.uniqueUpToIso {F : Cᵒᵖ ⥤ Type v} {Y Y' : C} (e : F.RepresentableBy Y)
    (e' : F.RepresentableBy Y') : Y ≅ Y' :=
  let ε {X} := (@e.homEquiv X).trans e'.homEquiv.symm
  Yoneda.ext _ _ ε ε.symm (by simp) (by simp)
    (by simp [ε, comp_homEquiv_symm, homEquiv_comp])

/-- Corepresenting objects are unique up to isomorphism. -/
@[simps!]
/-
**CategoryTheory.Functor.CorepresentableBy.uniqueUpToIso** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Functor.CorepresentableBy`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {F : C
ategoryTheory.Functor C (Type v)} → {X X' : C} → F.CorepresentableBy X → F.Corep
resentableBy X' → (X ≅ X')
参数：Type v；X ≅ X'。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Corepresenting objects are unique up to isomorphism.
-/
def CorepresentableBy.uniqueUpToIso {F : C ⥤ Type v} {X X' : C} (e : F.CorepresentableBy X)
    (e' : F.CorepresentableBy X') : X ≅ X' :=
  let ε {Y} := (@e.homEquiv Y).trans e'.homEquiv.symm
  Coyoneda.ext _ _ ε ε.symm (by simp) (by simp)
    (by simp [ε, homEquiv_symm_comp, homEquiv_comp])

@[ext]
/-
**CategoryTheory.Functor.RepresentableBy.ext** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Functor.RepresentableBy`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {F : CategoryT
heory.Functor Cᵒᵖ (Type v)} {Y : C}   {e e' : F.RepresentableBy Y},   e.homEquiv
 (CategoryTheory.CategoryStruct.id Y) = e'.homEquiv (CategoryTheory.CategoryStru
ct.id Y) → e = e'
参数：Type v；CategoryTheory.CategoryStruct.id Y；CategoryTheory.CategoryStruct.id Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.RepresentableBy.homEquiv_eq`：∀ {C : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} C] {F : CategoryTheory.Functor Cᵒᵖ (Type v)
} {Y : C}   (e : F.RepresentableBy Y) {X…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
-/
lemma RepresentableBy.ext {F : Cᵒᵖ ⥤ Type v} {Y : C} {e e' : F.RepresentableBy Y}
    (h : e.homEquiv (𝟙 Y) = e'.homEquiv (𝟙 Y)) : e = e' := by
  have : ∀ {X : C} (f : X ⟶ Y), e.homEquiv f = e'.homEquiv f := fun {X} f ↦ by
    rw [e.homEquiv_eq, e'.homEquiv_eq, h]
  obtain ⟨e, he⟩ := e
  obtain ⟨e', he'⟩ := e'
  obtain rfl : @e = @e' := by ext; apply this
  rfl

@[ext]
/-
**CategoryTheory.Functor.CorepresentableBy.ext** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Functor.CorepresentableBy`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {F : CategoryT
heory.Functor C (Type v)} {X : C}   {e e' : F.CorepresentableBy X},   e.homEquiv
 (CategoryTheory.CategoryStruct.id X) = e'.homEquiv (CategoryTheory.CategoryStru
ct.id X) → e = e'
参数：Type v；CategoryTheory.CategoryStruct.id X；CategoryTheory.CategoryStruct.id X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.CorepresentableBy.homEquiv_eq`：∀ {C : Type u₁} [i
nst : CategoryTheory.Category.{v₁, u₁} C] {F : CategoryTheory.Functor C (Type v)
} {X : C}   (e : F.CorepresentableBy X) {Y…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
-/
lemma CorepresentableBy.ext {F : C ⥤ Type v} {X : C} {e e' : F.CorepresentableBy X}
    (h : e.homEquiv (𝟙 X) = e'.homEquiv (𝟙 X)) : e = e' := by
  have : ∀ {Y : C} (f : X ⟶ Y), e.homEquiv f = e'.homEquiv f := fun {X} f ↦ by
    rw [e.homEquiv_eq, e'.homEquiv_eq, h]
  obtain ⟨e, he⟩ := e
  obtain ⟨e', he'⟩ := e'
  obtain rfl : @e = @e' := by ext; apply this
  rfl

/-- The obvious bijection `F.RepresentableBy Y ≃ (yoneda.obj Y ≅ F)`
when `F : Cᵒᵖ ⥤ Type v₁` and `[Category.{v₁} C]`. -/
/-
**CategoryTheory.Functor.representableByEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Functor`。
形式化陈述：representableByEquiv {F : Cᵒᵖ ⥤ Type v₁} {Y : C} : F.RepresentableBy Y ≃ (
yoneda.obj Y ≅ F) where toFun r
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The obvious bijection `F.RepresentableBy Y ≃ (yoneda.obj Y ≅ F)`
when `F : Cᵒᵖ ⥤ Type v₁` and `[Category.{v₁} C]`.
-/
def representableByEquiv {F : Cᵒᵖ ⥤ Type v₁} {Y : C} :
    F.RepresentableBy Y ≃ (yoneda.obj Y ≅ F) where
  toFun r := NatIso.ofComponents (fun _ ↦ r.homEquiv.toIso) (fun {X X'} f ↦ by
    ext g
    dsimp
    apply r.homEquiv_comp)
  invFun e :=
    { homEquiv := (e.app _).toEquiv
      homEquiv_comp := fun {X X'} f g ↦ by apply e.hom.naturality_apply }

/-- `yoneda.obj X` is represented by `X`. -/
/-
**CategoryTheory.Functor.RepresentableBy.yoneda** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Functor.RepresentableBy`。
形式化陈述：{C : Type u₁} → [inst : CategoryTheory.Category.{v₁, u₁} C] → (X : C) → (C
ategoryTheory.yoneda.obj X).RepresentableBy X
参数：X : C；CategoryTheory.yoneda.obj X。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`yoneda.obj X` is represented by `X`.
-/
protected def RepresentableBy.yoneda (X : C) : (yoneda.obj X).RepresentableBy X :=
  Functor.representableByEquiv.symm (Iso.refl _)

@[simp]
/-
**CategoryTheory.Functor.RepresentableBy.coyoneda_homEquiv** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Functor.RepresentableBy`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (X Y : C),   (
CategoryTheory.Functor.RepresentableBy.yoneda X).homEquiv = Equiv.refl (Y ⟶ X)
参数：X Y : C；CategoryTheory.Functor.RepresentableBy.yoneda X；Y ⟶ X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma RepresentableBy.coyoneda_homEquiv (X Y : C) :
    (RepresentableBy.yoneda X).homEquiv = Equiv.refl (Y ⟶ X) :=
  rfl

/-- The isomorphism `yoneda.obj Y ≅ F` induced by `e : F.RepresentableBy Y`. -/
/-
**CategoryTheory.Functor.RepresentableBy.toIso** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Functor.RepresentableBy`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {F : C
ategoryTheory.Functor Cᵒᵖ (Type v₁)} → {Y : C} → F.RepresentableBy Y → (Category
Theory.yoneda.obj Y ≅ F)
参数：Type v₁；CategoryTheory.yoneda.obj Y ≅ F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism `yoneda.obj Y ≅ F` induced by `e : F.RepresentableBy Y`.
-/
def RepresentableBy.toIso {F : Cᵒᵖ ⥤ Type v₁} {Y : C} (e : F.RepresentableBy Y) :
    yoneda.obj Y ≅ F :=
  representableByEquiv e

/-- The obvious bijection `F.CorepresentableBy X ≃ (yoneda.obj Y ≅ F)`
when `F : C ⥤ Type v₁` and `[Category.{v₁} C]`. -/
/-
**CategoryTheory.Functor.corepresentableByEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Functor`。
形式化陈述：corepresentableByEquiv {F : C ⥤ Type v₁} {X : C} : F.CorepresentableBy X ≃
 (coyoneda.obj (op X) ≅ F) where toFun r
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The obvious bijection `F.CorepresentableBy X ≃ (yoneda.obj Y ≅ F)`
when `F : C ⥤ Type v₁` and `[Category.{v₁} C]`.
-/
def corepresentableByEquiv {F : C ⥤ Type v₁} {X : C} :
    F.CorepresentableBy X ≃ (coyoneda.obj (op X) ≅ F) where
  toFun r := NatIso.ofComponents (fun _ ↦ r.homEquiv.toIso) (fun {X X'} f ↦ by
    ext g
    dsimp
    apply r.homEquiv_comp)
  invFun e :=
    { homEquiv := (e.app _).toEquiv
      homEquiv_comp := fun {X X'} f g ↦ by apply e.hom.naturality_apply }

/-- `coyoneda.obj X` is represented by `X`. -/
/-
**CategoryTheory.Functor.CorepresentableBy.coyoneda** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Functor.CorepresentableBy`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     (X : C
ᵒᵖ) → (CategoryTheory.coyoneda.obj X).CorepresentableBy (Opposite.unop X)
参数：X : Cᵒᵖ；CategoryTheory.coyoneda.obj X；Opposite.unop X。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`coyoneda.obj X` is represented by `X`.
-/
protected def CorepresentableBy.coyoneda (X : Cᵒᵖ) :
    (coyoneda.obj X).CorepresentableBy X.unop :=
  Functor.corepresentableByEquiv.symm (Iso.refl _)

@[simp]
/-
**CategoryTheory.Functor.CorepresentableBy.coyoneda_homEquiv** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.Functor.CorepresentableBy`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (X : Cᵒᵖ) (Y :
 C),   (CategoryTheory.Functor.CorepresentableBy.coyoneda X).homEquiv = Equiv.re
fl (Opposite.unop X ⟶ Y)
参数：X : Cᵒᵖ；Y : C；CategoryTheory.Functor.CorepresentableBy.coyoneda X；Opposite.un
op X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma CorepresentableBy.coyoneda_homEquiv (X : Cᵒᵖ) (Y : C) :
    (CorepresentableBy.coyoneda X).homEquiv = Equiv.refl (X.unop ⟶ Y) :=
  rfl

/-- The isomorphism `coyoneda.obj (op X) ≅ F` induced by `e : F.CorepresentableBy X`. -/
/-
**CategoryTheory.Functor.CorepresentableBy.toIso** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Functor.CorepresentableBy`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {F : C
ategoryTheory.Functor C (Type v₁)} →       {X : C} → F.CorepresentableBy X → (Ca
tegoryTheory.coyoneda.obj (Opposite.op X) ≅ F)
参数：Type v₁；CategoryTheory.coyoneda.obj (Opposite.op X) ≅ F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism `coyoneda.obj (op X) ≅ F` induced by `e : F.CorepresentableBy X`
.
-/
def CorepresentableBy.toIso {F : C ⥤ Type v₁} {X : C} (e : F.CorepresentableBy X) :
    coyoneda.obj (op X) ≅ F :=
  corepresentableByEquiv e

/-- Transport `RepresentableBy` along an isomorphism of the object. -/
@[simps]
/-
**CategoryTheory.Functor.RepresentableBy.ofIsoObj** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Functor.RepresentableBy`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {F : C
ategoryTheory.Functor Cᵒᵖ (Type w)} → {X Y : C} → F.RepresentableBy X → (Y ≅ X) 
→ F.RepresentableBy Y
参数：Type w；Y ≅ X。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
Transport `RepresentableBy` along an isomorphism of the object.
-/
def RepresentableBy.ofIsoObj {F : Cᵒᵖ ⥤ Type w} {X Y : C} (R : F.RepresentableBy X)
    (e : Y ≅ X) :
    F.RepresentableBy Y where
  homEquiv {Z} := e.homToEquiv.trans R.homEquiv
  homEquiv_comp := by simp [R.homEquiv_comp]

/-- Transport `RepresentableBy` along an isomorphism of the object. -/
@[simps]
/-
**CategoryTheory.Functor.CorepresentableBy.ofIsoObj** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Functor.CorepresentableBy`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {F : C
ategoryTheory.Functor C (Type w)} → {X Y : C} → F.CorepresentableBy X → (Y ≅ X) 
→ F.CorepresentableBy Y
参数：Type w；Y ≅ X。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
Transport `RepresentableBy` along an isomorphism of the object.
-/
def CorepresentableBy.ofIsoObj {F : C ⥤ Type w} {X Y : C} (R : F.CorepresentableBy X)
    (e : Y ≅ X) :
    F.CorepresentableBy Y where
  homEquiv {Z} := e.homFromEquiv.trans R.homEquiv
  homEquiv_comp := by simp [R.homEquiv_comp]

/-- If `Y` is isomorphic to `X`, representations of `F` by `X` are equivalent
to representations of `F` by `Y`. -/
@[simps]
/-
**CategoryTheory.Functor.RepresentableBy.equivOfIsoObj** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Functor.RepresentableBy`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {F : C
ategoryTheory.Functor Cᵒᵖ (Type w)} → {X Y : C} → (Y ≅ X) → F.RepresentableBy X 
≃ F.RepresentableBy Y
参数：Type w；Y ≅ X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `Y` is isomorphic to `X`, representations of `F` by `X` are equivalent
to representations of `F` by `Y`.
-/
def RepresentableBy.equivOfIsoObj {F : Cᵒᵖ ⥤ Type w} {X Y : C} (e : Y ≅ X) :
    F.RepresentableBy X ≃ F.RepresentableBy Y where
  toFun R := R.ofIsoObj e
  invFun R := R.ofIsoObj e.symm
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

/-- If `Y` is isomorphic to `X`, corepresentations of `F` by `X` are equivalent
to corepresentations of `F` by `Y`. -/
@[simps]
/-
**CategoryTheory.Functor.CorepresentableBy.equivOfIsoObj** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Functor.CorepresentableBy`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {F : C
ategoryTheory.Functor C (Type w)} → {X Y : C} → (Y ≅ X) → F.CorepresentableBy X 
≃ F.CorepresentableBy Y
参数：Type w；Y ≅ X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `Y` is isomorphic to `X`, corepresentations of `F` by `X` are equivalent
to corepresentations of `F` by `Y`.
-/
def CorepresentableBy.equivOfIsoObj {F : C ⥤ Type w} {X Y : C} (e : Y ≅ X) :
    F.CorepresentableBy X ≃ F.CorepresentableBy Y where
  toFun R := R.ofIsoObj e
  invFun R := R.ofIsoObj e.symm
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Representing `F` composed with universe lifting is the same as representing `F`. -/
@[simps]
/-
**CategoryTheory.Functor.representableByUliftFunctorEquiv** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Functor`。
形式化陈述：representableByUliftFunctorEquiv {F : Cᵒᵖ ⥤ Type v} {X : C} : (F ⋙ uliftFu
nctor.{w}).RepresentableBy X ≃ F.RepresentableBy X where toFun R
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Representing `F` composed with universe lifting is the same as representing `F`.
-/
def representableByUliftFunctorEquiv {F : Cᵒᵖ ⥤ Type v} {X : C} :
    (F ⋙ uliftFunctor.{w}).RepresentableBy X ≃ F.RepresentableBy X where
  toFun R :=
    { homEquiv {Y} := R.homEquiv.trans Equiv.ulift
      homEquiv_comp f g := congr($(R.homEquiv_comp _ _).down) }
  invFun R :=
    { homEquiv {Y} := R.homEquiv.trans Equiv.ulift.symm
      homEquiv_comp f g := by simp [R.homEquiv_comp] }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Corepresenting `F` composed with universe lifting is the same as corepresenting `F`. -/
@[simps]
/-
**CategoryTheory.Functor.corepresentableByUliftFunctorEquiv** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.Functor`。
形式化陈述：corepresentableByUliftFunctorEquiv {F : C ⥤ Type v} {X : C} : (F ⋙ uliftFu
nctor.{w}).CorepresentableBy X ≃ F.CorepresentableBy X where toFun R
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Corepresenting `F` composed with universe lifting is the same as corepresenting 
`F`.
-/
def corepresentableByUliftFunctorEquiv {F : C ⥤ Type v} {X : C} :
    (F ⋙ uliftFunctor.{w}).CorepresentableBy X ≃ F.CorepresentableBy X where
  toFun R :=
    { homEquiv {Y} := R.homEquiv.trans Equiv.ulift
      homEquiv_comp f g := congr($(R.homEquiv_comp _ _).down) }
  invFun R :=
    { homEquiv {Y} := R.homEquiv.trans Equiv.ulift.symm
      homEquiv_comp f g := by simp [R.homEquiv_comp] }

/-- Version of `representableByEquiv` with more general universe assumptions. -/
@[simps]
/-
**CategoryTheory.Functor.RepresentableBy.equivUliftYonedaIso** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.Functor.RepresentableBy`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     (F : C
ategoryTheory.Functor Cᵒᵖ (Type (max w v₁))) →       (X : C) → F.RepresentableBy
 X ≃ (CategoryTheory.uliftYoneda.{w, v₁, u₁}.obj X ≅ F)
参数：F : CategoryTheory.Functor Cᵒᵖ (Type (max w v₁))；X : C；CategoryTheory.uliftYo
neda.{w, v₁, u₁}.obj X ≅ F。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Version of `representableByEquiv` with more general universe assumptions.
-/
def RepresentableBy.equivUliftYonedaIso (F : Cᵒᵖ ⥤ Type (max w v₁)) (X : C) :
    F.RepresentableBy X ≃ (uliftYoneda.obj X ≅ F) where
  toFun R := NatIso.ofComponents (fun X ↦ equivEquivIso (Equiv.ulift.trans R.homEquiv)) <| by
    intro X Y f
    ext x
    exact R.homEquiv_comp f.unop _
  invFun e :=
    { homEquiv {X} := Equiv.ulift.symm.trans (equivEquivIso.symm (e.app _))
      homEquiv_comp {X Y} f g := congr($(e.hom.naturality f.op) ⟨g⟩) }

/-- Version of `corepresentableByEquiv` with more general universe assumptions. -/
@[simps]
/-
**CategoryTheory.Functor.CorepresentableBy.equivUliftCoyonedaIso** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory.Functor.CorepresentableBy`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     (F : C
ategoryTheory.Functor C (Type (max w v₁))) →       (X : C) → F.CorepresentableBy
 X ≃ (CategoryTheory.uliftCoyoneda.{w, v₁, u₁}.obj (Opposite.op X) ≅ F)
参数：F : CategoryTheory.Functor C (Type (max w v₁))；X : C；CategoryTheory.uliftCoyo
neda.{w, v₁, u₁}.obj (Opposite.op X) ≅ F。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Version of `corepresentableByEquiv` with more general universe assumptions.
-/
def CorepresentableBy.equivUliftCoyonedaIso (F : C ⥤ Type (max w v₁)) (X : C) :
    F.CorepresentableBy X ≃ (uliftCoyoneda.obj (op X) ≅ F) where
  toFun R := NatIso.ofComponents (fun X ↦ equivEquivIso (Equiv.ulift.trans R.homEquiv)) <| by
    intro X Y f
    ext x
    exact R.homEquiv_comp f _
  invFun e :=
    { homEquiv {X} := Equiv.ulift.symm.trans (equivEquivIso.symm (e.app _))
      homEquiv_comp {X Y} f g := congr($(e.hom.naturality f) ⟨g⟩) }

/-- A functor `F : Cᵒᵖ ⥤ Type v` is representable if there is an object `Y` with a structure
`F.RepresentableBy Y`, i.e. there is a natural bijection `(X ⟶ Y) ≃ F.obj (op X)`,
which may also be rephrased as a natural isomorphism `yoneda.obj X ≅ F` when `Category.{v} C`. -/
@[stacks 001Q]
/-
**CategoryTheory.Functor.IsRepresentable** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTh
eory.Functor`。
形式化陈述：{C : Type u₁} → [inst : CategoryTheory.Category.{v₁, u₁} C] → CategoryTheo
ry.Functor Cᵒᵖ (Type v) → Prop
参数：Type v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `F : Cᵒᵖ ⥤ Type v` is representable if there is an object `Y` with a s
tructure
`F.RepresentableBy Y`, i.e. there is a natural bijection `(X ⟶ Y) ≃ F.obj (op X)
`,
which may also be rephrased as a natural isomorphism `yoneda.obj X ≅ F` when `Ca
tegory.{v} C`.
-/
class IsRepresentable (F : Cᵒᵖ ⥤ Type v) : Prop where
  has_representation : ∃ (Y : C), Nonempty (F.RepresentableBy Y)
/-
**CategoryTheory.Functor.RepresentableBy.isRepresentable** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Functor.RepresentableBy`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {F : CategoryT
heory.Functor Cᵒᵖ (Type v)} {Y : C}   (e : F.RepresentableBy Y), F.IsRepresentab
le
参数：Type v；e : F.RepresentableBy Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma RepresentableBy.isRepresentable {F : Cᵒᵖ ⥤ Type v} {Y : C} (e : F.RepresentableBy Y) :
    F.IsRepresentable where
  has_representation := ⟨Y, ⟨e⟩⟩

/-- Alternative constructor for `F.IsRepresentable`, which takes as an input an
isomorphism `yoneda.obj X ≅ F`. -/
/-
**CategoryTheory.Functor.IsRepresentable.mk'** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Functor.IsRepresentable`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {F : CategoryT
heory.Functor Cᵒᵖ (Type v₁)} {X : C}   (e : CategoryTheory.yoneda.obj X ≅ F), F.
IsRepresentable
参数：Type v₁；e : CategoryTheory.yoneda.obj X ≅ F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.RepresentableBy.isRepresentable`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {F : CategoryTheory.Functor Cᵒᵖ (Typ
e v)} {Y : C}   (e : F.RepresentableBy Y), F…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Alternative constructor for `F.IsRepresentable`, which takes as an input an
isomorphism `yoneda.obj X ≅ F`.
-/
lemma IsRepresentable.mk' {F : Cᵒᵖ ⥤ Type v₁} {X : C} (e : yoneda.obj X ≅ F) :
    F.IsRepresentable :=
  (representableByEquiv.symm e).isRepresentable
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : C} : IsRepresentable (yoneda.obj X) :=
  IsRepresentable.mk' (Iso.refl _)
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : C} : IsRepresentable (uliftYoneda.{w}.obj X) :=
  RepresentableBy.isRepresentable (representableByUliftFunctorEquiv.symm (RepresentableBy.yoneda X))

/--
A functor `F : C ⥤ Type v₁` is corepresentable if there is object `X` so `F ≅ coyoneda.obj X`.
-/
@[stacks 001Q]
/-
**CategoryTheory.Functor.IsCorepresentable** 是 Mathlib 中的一个归纳类型，位于命名空间 `Category
Theory.Functor`。
形式化陈述：{C : Type u₁} → [inst : CategoryTheory.Category.{v₁, u₁} C] → CategoryTheo
ry.Functor C (Type v) → Prop
参数：Type v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `F : C ⥤ Type v₁` is corepresentable if there is object `X` so `F ≅ co
yoneda.obj X`.
-/
class IsCorepresentable (F : C ⥤ Type v) : Prop where
  has_corepresentation : ∃ (X : C), Nonempty (F.CorepresentableBy X)
/-
**CategoryTheory.Functor.CorepresentableBy.isCorepresentable** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.Functor.CorepresentableBy`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {F : CategoryT
heory.Functor C (Type v)} {X : C}   (e : F.CorepresentableBy X), F.IsCorepresent
able
参数：Type v；e : F.CorepresentableBy X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma CorepresentableBy.isCorepresentable {F : C ⥤ Type v} {X : C}
    (e : F.CorepresentableBy X) : F.IsCorepresentable where
  has_corepresentation := ⟨X, ⟨e⟩⟩

/-- Alternative constructor for `F.IsCorepresentable`, which takes as an input an
isomorphism `coyoneda.obj (op X) ≅ F`. -/
/-
**CategoryTheory.Functor.IsCorepresentable.mk'** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Functor.IsCorepresentable`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {F : CategoryT
heory.Functor C (Type v₁)} {X : C}   (e : CategoryTheory.coyoneda.obj (Opposite.
op X) ≅ F), F.IsCorepresentable
参数：Type v₁；e : CategoryTheory.coyoneda.obj (Opposite.op X) ≅ F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.CorepresentableBy.isCorepresentable`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {F : CategoryTheory.Functor C (T
ype v)} {X : C}   (e : F.CorepresentableBy X), F…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Alternative constructor for `F.IsCorepresentable`, which takes as an input an
isomorphism `coyoneda.obj (op X) ≅ F`.
-/
lemma IsCorepresentable.mk' {F : C ⥤ Type v₁} {X : C} (e : coyoneda.obj (op X) ≅ F) :
    F.IsCorepresentable :=
  (corepresentableByEquiv.symm e).isCorepresentable
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : Cᵒᵖ} : IsCorepresentable (coyoneda.obj X) :=
  IsCorepresentable.mk' (Iso.refl _)
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : Cᵒᵖ} : IsCorepresentable (uliftCoyoneda.{w}.obj X) :=
  CorepresentableBy.isCorepresentable
    (corepresentableByUliftFunctorEquiv.symm (CorepresentableBy.coyoneda X))

-- instance : corepresentable (𝟭 (Type v₁)) :=
-- corepresentable_of_nat_iso (op punit) coyoneda.punit_iso
section Representable

variable (F : Cᵒᵖ ⥤ Type v) [hF : F.IsRepresentable]

/-- The representing object for the representable functor `F`. -/
/-
**CategoryTheory.Functor.reprX** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor
`。
形式化陈述：reprX : C
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsRepresentable.has_representation`：∀ {C : Type u
₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {F : CategoryTheory.Functor Cᵒᵖ (
Type v)}   [self : F.IsRepresentable], ∃ Y, Non…

--- 原说明 ---
The representing object for the representable functor `F`.
-/
noncomputable def reprX : C :=
  hF.has_representation.choose

/-- A chosen term in `F.RepresentableBy (reprX F)` when `F.IsRepresentable` holds. -/
/-
**CategoryTheory.Functor.representableBy** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Functor`。
形式化陈述：representableBy : F.RepresentableBy F.reprX
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsRepresentable.has_representation`：∀ {C : Type u
₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {F : CategoryTheory.Functor Cᵒᵖ (
Type v)}   [self : F.IsRepresentable], ∃ Y, Non…

--- 原说明 ---
A chosen term in `F.RepresentableBy (reprX F)` when `F.IsRepresentable` holds.
-/
noncomputable def representableBy : F.RepresentableBy F.reprX :=
  hF.has_representation.choose_spec.some

/-- Any representing object for a representable functor `F` is isomorphic to `reprX F`. -/
/-
**CategoryTheory.Functor.RepresentableBy.isoReprX** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Functor.RepresentableBy`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     (F : C
ategoryTheory.Functor Cᵒᵖ (Type v)) → [hF : F.IsRepresentable] → {Y : C} → F.Rep
resentableBy Y → (Y ≅ F.reprX)
参数：F : CategoryTheory.Functor Cᵒᵖ (Type v)；Y ≅ F.reprX。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any representing object for a representable functor `F` is isomorphic to `reprX 
F`.
-/
noncomputable def RepresentableBy.isoReprX {Y : C} (e : F.RepresentableBy Y) :
    Y ≅ F.reprX :=
  RepresentableBy.uniqueUpToIso e (representableBy F)

/-- The representing element for the representable functor `F`, sometimes called the universal
element of the functor.
-/
/-
**CategoryTheory.Functor.reprx** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor
`。
形式化陈述：reprx : F.obj (op F.reprX)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The representing element for the representable functor `F`, sometimes called the
 universal
element of the functor.
-/
noncomputable def reprx : F.obj (op F.reprX) :=
  F.representableBy.homEquiv (𝟙 _)

/-- An isomorphism between a representable `F` and a functor of the
form `C(-, F.reprX)`.  Note the components `F.reprW.app X`
definitionally have type `(X.unop ⟶ F.reprX) ≅ F.obj X`.
-/
/-
**CategoryTheory.Functor.reprW** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor
`。
形式化陈述：reprW (F : Cᵒᵖ ⥤ Type v₁) [F.IsRepresentable] : yoneda.obj F.reprX ≅ F
参数：F : Cᵒᵖ ⥤ Type v₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isomorphism between a representable `F` and a functor of the
form `C(-, F.reprX)`.  Note the components `F.reprW.app X`
definitionally have type `(X.unop ⟶ F.reprX) ≅ F.obj X`.
-/
noncomputable def reprW (F : Cᵒᵖ ⥤ Type v₁) [F.IsRepresentable] :
    yoneda.obj F.reprX ≅ F := F.representableBy.toIso
/-
**CategoryTheory.Functor.reprW_hom_app** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Functor`。
形式化陈述：reprW_hom_app (F : Cᵒᵖ ⥤ Type v₁) [F.IsRepresentable] (X : Cᵒᵖ) (f : unop 
X ⟶ F.reprX) : F.reprW.hom.app X f = F.map f.op F.reprx
参数：F : Cᵒᵖ ⥤ Type v₁；X : Cᵒᵖ；f : unop X ⟶ F.reprX。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.RepresentableBy.homEquiv_eq`：∀ {C : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} C] {F : CategoryTheory.Functor Cᵒᵖ (Type v)
} {Y : C}   (e : F.RepresentableBy Y) {X…
-/
theorem reprW_hom_app (F : Cᵒᵖ ⥤ Type v₁) [F.IsRepresentable]
    (X : Cᵒᵖ) (f : unop X ⟶ F.reprX) :
    F.reprW.hom.app X f = F.map f.op F.reprx := by
  apply RepresentableBy.homEquiv_eq

/-- If `F` is representable, it is, modulo universe lifting, isomorphic to
`Hom(-, X)` for the representing object `X`. -/
/-
**CategoryTheory.Functor.uliftYonedaReprXIso** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Functor`。
形式化陈述：uliftYonedaReprXIso (F : Cᵒᵖ ⥤ Type (max v v₁)) [F.IsRepresentable] : ulif
tYoneda.{v}.obj F.reprX ≅ F
参数：F : Cᵒᵖ ⥤ Type (max v v₁)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F` is representable, it is, modulo universe lifting, isomorphic to
`Hom(-, X)` for the representing object `X`.
-/
noncomputable def uliftYonedaReprXIso (F : Cᵒᵖ ⥤ Type (max v v₁)) [F.IsRepresentable] :
    uliftYoneda.{v}.obj F.reprX ≅ F :=
  (RepresentableBy.equivUliftYonedaIso F _) F.representableBy
/-
**CategoryTheory.Functor.uliftYonedaReprXIso_hom_app** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Functor`。
形式化陈述：uliftYonedaReprXIso_hom_app (F : Cᵒᵖ ⥤ Type (max v v₁)) [F.IsRepresentable
] (X : Cᵒᵖ) (f : ULift (unop X ⟶ F.reprX)) : F.uliftYonedaReprXIso.hom.app X f =
 F.map f.down.op F.reprx
参数：F : Cᵒᵖ ⥤ Type (max v v₁)；X : Cᵒᵖ；f : ULift (unop X ⟶ F.reprX)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.RepresentableBy.homEquiv_eq`：∀ {C : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} C] {F : CategoryTheory.Functor Cᵒᵖ (Type v)
} {Y : C}   (e : F.RepresentableBy Y) {X…
-/
lemma uliftYonedaReprXIso_hom_app (F : Cᵒᵖ ⥤ Type (max v v₁)) [F.IsRepresentable]
    (X : Cᵒᵖ) (f : ULift (unop X ⟶ F.reprX)) :
    F.uliftYonedaReprXIso.hom.app X f = F.map f.down.op F.reprx :=
  RepresentableBy.homEquiv_eq _ _

end Representable

section Corepresentable

variable (F : C ⥤ Type v) [hF : F.IsCorepresentable]

/-- The representing object for the corepresentable functor `F`. -/
/-
**CategoryTheory.Functor.coreprX** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Funct
or`。
形式化陈述：coreprX : C
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsCorepresentable.has_corepresentation`：∀ {C : Ty
pe u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {F : CategoryTheory.Functor C
 (Type v)}   [self : F.IsCorepresentable], ∃ X, Non…

--- 原说明 ---
The representing object for the corepresentable functor `F`.
-/
noncomputable def coreprX : C :=
  hF.has_corepresentation.choose

/-- A chosen term in `F.CorepresentableBy (coreprX F)` when `F.IsCorepresentable` holds. -/
/-
**CategoryTheory.Functor.corepresentableBy** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Functor`。
形式化陈述：corepresentableBy : F.CorepresentableBy F.coreprX
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsCorepresentable.has_corepresentation`：∀ {C : Ty
pe u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {F : CategoryTheory.Functor C
 (Type v)}   [self : F.IsCorepresentable], ∃ X, Non…

--- 原说明 ---
A chosen term in `F.CorepresentableBy (coreprX F)` when `F.IsCorepresentable` ho
lds.
-/
noncomputable def corepresentableBy : F.CorepresentableBy F.coreprX :=
  hF.has_corepresentation.choose_spec.some

variable {F} in
/-- Any corepresenting object for a corepresentable functor `F` is isomorphic to `coreprX F`. -/
/-
**CategoryTheory.Functor.CorepresentableBy.isoCoreprX** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Functor.CorepresentableBy`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {F : C
ategoryTheory.Functor C (Type v)} →       [hF : F.IsCorepresentable] → {Y : C} →
 F.CorepresentableBy Y → (Y ≅ F.coreprX)
参数：Type v；Y ≅ F.coreprX。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any corepresenting object for a corepresentable functor `F` is isomorphic to `co
reprX F`.
-/
noncomputable def CorepresentableBy.isoCoreprX {Y : C} (e : F.CorepresentableBy Y) :
    Y ≅ F.coreprX :=
  CorepresentableBy.uniqueUpToIso e (corepresentableBy F)

/-- The representing element for the corepresentable functor `F`, sometimes called the universal
element of the functor.
-/
/-
**CategoryTheory.Functor.coreprx** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Funct
or`。
形式化陈述：coreprx : F.obj F.coreprX
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The representing element for the corepresentable functor `F`, sometimes called t
he universal
element of the functor.
-/
noncomputable def coreprx : F.obj F.coreprX :=
  F.corepresentableBy.homEquiv (𝟙 _)

/-- An isomorphism between a corepresentable `F` and a functor of the form
`C(F.corepr X, -)`. Note the components `F.coreprW.app X`
definitionally have type `F.corepr_X ⟶ X ≅ F.obj X`.
-/
/-
**CategoryTheory.Functor.coreprW** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Funct
or`。
形式化陈述：coreprW (F : C ⥤ Type v₁) [F.IsCorepresentable] : coyoneda.obj (op F.corep
rX) ≅ F
参数：F : C ⥤ Type v₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isomorphism between a corepresentable `F` and a functor of the form
`C(F.corepr X, -)`. Note the components `F.coreprW.app X`
definitionally have type `F.corepr_X ⟶ X ≅ F.obj X`.
-/
noncomputable def coreprW (F : C ⥤ Type v₁) [F.IsCorepresentable] :
    coyoneda.obj (op F.coreprX) ≅ F :=
  F.corepresentableBy.toIso
/-
**CategoryTheory.Functor.coreprW_hom_app** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Functor`。
形式化陈述：coreprW_hom_app (F : C ⥤ Type v₁) [F.IsCorepresentable] (X : C) (f : F.cor
eprX ⟶ X) : F.coreprW.hom.app X f = F.map f F.coreprx
参数：F : C ⥤ Type v₁；X : C；f : F.coreprX ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.CorepresentableBy.homEquiv_eq`：∀ {C : Type u₁} [i
nst : CategoryTheory.Category.{v₁, u₁} C] {F : CategoryTheory.Functor C (Type v)
} {X : C}   (e : F.CorepresentableBy X) {Y…
-/
theorem coreprW_hom_app (F : C ⥤ Type v₁) [F.IsCorepresentable] (X : C) (f : F.coreprX ⟶ X) :
    F.coreprW.hom.app X f = F.map f F.coreprx := by
  apply CorepresentableBy.homEquiv_eq

/-- If `F` is corepresentable, it is, modulo universe lifting, isomorphic to
`Hom(X, -)` for the corepresenting object `X`. -/
/-
**CategoryTheory.Functor.uliftCoyonedaCoreprXIso** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Functor`。
形式化陈述：uliftCoyonedaCoreprXIso (F : C ⥤ Type (max v v₁)) [F.IsCorepresentable] : 
uliftCoyoneda.{v}.obj (op F.coreprX) ≅ F
参数：F : C ⥤ Type (max v v₁)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F` is corepresentable, it is, modulo universe lifting, isomorphic to
`Hom(X, -)` for the corepresenting object `X`.
-/
noncomputable def uliftCoyonedaCoreprXIso (F : C ⥤ Type (max v v₁)) [F.IsCorepresentable] :
    uliftCoyoneda.{v}.obj (op F.coreprX) ≅ F :=
  (CorepresentableBy.equivUliftCoyonedaIso F _) F.corepresentableBy
/-
**CategoryTheory.Functor.uliftCoyonedaCoreprXIso_hom_app** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Functor`。
形式化陈述：uliftCoyonedaCoreprXIso_hom_app (F : C ⥤ Type (max v v₁)) [F.IsCorepresent
able] (X : C) (f : ULift (F.coreprX ⟶ X)) : F.uliftCoyonedaCoreprXIso.hom.app X 
f = F.map f.down F.coreprx
参数：F : C ⥤ Type (max v v₁)；X : C；f : ULift (F.coreprX ⟶ X)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.CorepresentableBy.homEquiv_eq`：∀ {C : Type u₁} [i
nst : CategoryTheory.Category.{v₁, u₁} C] {F : CategoryTheory.Functor C (Type v)
} {X : C}   (e : F.CorepresentableBy X) {Y…
-/
lemma uliftCoyonedaCoreprXIso_hom_app (F : C ⥤ Type (max v v₁)) [F.IsCorepresentable]
    (X : C) (f : ULift (F.coreprX ⟶ X)) :
    F.uliftCoyonedaCoreprXIso.hom.app X f = F.map f.down F.coreprx :=
  CorepresentableBy.homEquiv_eq _ _

end Corepresentable

/-
**CategoryTheory.Functor.isRepresentable_comp_uliftFunctor_iff** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {F : CategoryT
heory.Functor Cᵒᵖ (Type v)},   (F.comp CategoryTheory.uliftFunctor.{w, v}).IsRep
resentable ↔ F.IsRepresentable
参数：Type v；F.comp CategoryTheory.uliftFunctor.{w, v}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma isRepresentable_comp_uliftFunctor_iff {F : Cᵒᵖ ⥤ Type v} :
    (F ⋙ uliftFunctor.{w}).IsRepresentable ↔ F.IsRepresentable where
  mp | ⟨X, ⟨R⟩⟩ => ⟨X, ⟨representableByUliftFunctorEquiv R⟩⟩
  mpr | ⟨X, ⟨R⟩⟩ => ⟨X, ⟨representableByUliftFunctorEquiv.symm R⟩⟩
/-
**CategoryTheory.Functor.isCorepresentable_comp_uliftFunctor_iff** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {F : CategoryT
heory.Functor C (Type v)},   (F.comp CategoryTheory.uliftFunctor.{w, v}).IsCorep
resentable ↔ F.IsCorepresentable
参数：Type v；F.comp CategoryTheory.uliftFunctor.{w, v}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma isCorepresentable_comp_uliftFunctor_iff {F : C ⥤ Type v} :
    (F ⋙ uliftFunctor.{w}).IsCorepresentable ↔ F.IsCorepresentable where
  mp | ⟨X, ⟨R⟩⟩ => ⟨X, ⟨corepresentableByUliftFunctorEquiv R⟩⟩
  mpr | ⟨X, ⟨R⟩⟩ => ⟨X, ⟨corepresentableByUliftFunctorEquiv.symm R⟩⟩
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : Cᵒᵖ ⥤ Type v) [F.IsRepresentable] : (F ⋙ uliftFunctor.{w}).IsRepresentable :=
  isRepresentable_comp_uliftFunctor_iff.mpr ‹_›
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ Type v) [F.IsCorepresentable] : (F ⋙ uliftFunctor.{w}).IsCorepresentable :=
  isCorepresentable_comp_uliftFunctor_iff.mpr ‹_›

end Functor

/-
**CategoryTheory.isRepresentable_of_natIso** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory`。
形式化陈述：isRepresentable_of_natIso (F : Cᵒᵖ ⥤ Type v) {G} (i : F ≅ G) [F.IsRepresen
table] : G.IsRepresentable
参数：F : Cᵒᵖ ⥤ Type v；i : F ≅ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.RepresentableBy.isRepresentable`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {F : CategoryTheory.Functor Cᵒᵖ (Typ
e v)} {Y : C}   (e : F.RepresentableBy Y), F…
-/
theorem isRepresentable_of_natIso (F : Cᵒᵖ ⥤ Type v) {G} (i : F ≅ G) [F.IsRepresentable] :
    G.IsRepresentable :=
  (F.representableBy.ofIso i).isRepresentable
/-
**CategoryTheory.corepresentable_of_natIso** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory`。
形式化陈述：corepresentable_of_natIso (F : C ⥤ Type v) {G} (i : F ≅ G) [F.IsCorepresen
table] : G.IsCorepresentable
参数：F : C ⥤ Type v；i : F ≅ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.CorepresentableBy.isCorepresentable`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {F : CategoryTheory.Functor C (T
ype v)} {X : C}   (e : F.CorepresentableBy X), F…
-/
theorem corepresentable_of_natIso (F : C ⥤ Type v) {G} (i : F ≅ G) [F.IsCorepresentable] :
    G.IsCorepresentable :=
  (F.corepresentableBy.ofIso i).isCorepresentable

/-- The identity functor on `Type v` is corepresented by `PUnit`. -/
/-
**CategoryTheory.Functor.CorepresentableBy.id** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Functor.CorepresentableBy`。
形式化陈述：(CategoryTheory.Functor.id (Type v)).CorepresentableBy PUnit.{v + 1}
参数：Type v。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The identity functor on `Type v` is corepresented by `PUnit`.
-/
def Functor.CorepresentableBy.id : (𝟭 (Type v)).CorepresentableBy PUnit :=
  corepresentableByEquiv.symm Coyoneda.punitIso
/-
**CategoryTheory.Functor.CorepresentableBy.id_homEquiv_apply** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.Functor.CorepresentableBy`。
形式化陈述：∀ (X : Type v) (a : PUnit.{v + 1} ⟶ X),   CategoryTheory.Functor.Coreprese
ntableBy.id.homEquiv a = (CategoryTheory.ConcreteCategory.hom a) PUnit.unit
参数：X : Type v；a : PUnit.{v + 1} ⟶ X；CategoryTheory.ConcreteCategory.hom a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma Functor.CorepresentableBy.id_homEquiv_apply (X : Type v)
    (a : PUnit ⟶ X) : dsimp% id.homEquiv a = a ⟨⟩ :=
  rfl
/-
**CategoryTheory.Functor.CorepresentableBy.id_homEquiv_symm_apply** 是 Mathlib 中的
一个定理，位于命名空间 `CategoryTheory.Functor.CorepresentableBy`。
形式化陈述：∀ (X : Type v) (x : X) (a : PUnit.{v + 1}),   (CategoryTheory.ConcreteCate
gory.hom (CategoryTheory.Functor.CorepresentableBy.id.homEquiv.symm x)) a = x
参数：X : Type v；x : X；a : PUnit.{v + 1}；CategoryTheory.ConcreteCategory.hom (Categ
oryTheory.Functor.CorepresentableBy.id.homEquiv.symm x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
@[simp] lemma Functor.CorepresentableBy.id_homEquiv_symm_apply (X : Type v) (x : X)
    (a : PUnit) : dsimp% id.homEquiv.symm x a = x :=
  rfl
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Functor.IsCorepresentable (𝟭 (Type v)) :=
  Functor.CorepresentableBy.id.isCorepresentable

open Opposite

variable (C)

-- We need to help typeclass inference with some awkward universe levels here.
/-
**CategoryTheory.prodCategoryInstance1** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
`。
形式化陈述：prodCategoryInstance1 : Category ((Cᵒᵖ ⥤ Type v₁) × Cᵒᵖ)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance prodCategoryInstance1 : Category ((Cᵒᵖ ⥤ Type v₁) × Cᵒᵖ) :=
  CategoryTheory.prod'.{max u₁ v₁, v₁} (Cᵒᵖ ⥤ Type v₁) Cᵒᵖ
/-
**CategoryTheory.prodCategoryInstance2** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
`。
形式化陈述：prodCategoryInstance2 : Category (Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance prodCategoryInstance2 : Category (Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁)) :=
  CategoryTheory.prod'.{v₁, max u₁ v₁} Cᵒᵖ (Cᵒᵖ ⥤ Type v₁)

open Yoneda

section YonedaLemma

variable {C}

/-- We have a type-level equivalence between natural transformations from the yoneda embedding
and elements of `F.obj X`, without any universe switching.
-/
@[implicit_reducible]
/-
**CategoryTheory.yonedaEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：yonedaEquiv {X : C} {F : Cᵒᵖ ⥤ Type v₁} : (yoneda.obj X ⟶ F) ≃ F.obj (op X
) where toFun η
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We have a type-level equivalence between natural transformations from the yoneda
 embedding
and elements of `F.obj X`, without any universe switching.
-/
def yonedaEquiv {X : C} {F : Cᵒᵖ ⥤ Type v₁} : (yoneda.obj X ⟶ F) ≃ F.obj (op X) where
  toFun η := η.app (op X) (𝟙 X)
  invFun ξ := { app _ := ↾fun f ↦ F.map f.op ξ }
  left_inv := by
    intro η
    ext Y f
    simp [← NatTrans.naturality_apply]
  right_inv := by intro ξ; simp
/-
**CategoryTheory.yonedaEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：yonedaEquiv_apply {X : C} {F : Cᵒᵖ ⥤ Type v₁} (f : yoneda.obj X ⟶ F) : yon
edaEquiv f = f.app (op X) (𝟙 X)
参数：f : yoneda.obj X ⟶ F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem yonedaEquiv_apply {X : C} {F : Cᵒᵖ ⥤ Type v₁} (f : yoneda.obj X ⟶ F) :
    yonedaEquiv f = f.app (op X) (𝟙 X) :=
  rfl

@[simp]
/-
**CategoryTheory.yonedaEquiv_symm_app** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`
。
形式化陈述：yonedaEquiv_symm_app {X : C} {F : Cᵒᵖ ⥤ Type v₁} (x : F.obj (op X)) (Y : C
ᵒᵖ) : (yonedaEquiv.symm x).app Y = ↾fun f => F.map f.op x
参数：x : F.obj (op X)；Y : Cᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem yonedaEquiv_symm_app {X : C} {F : Cᵒᵖ ⥤ Type v₁} (x : F.obj (op X)) (Y : Cᵒᵖ) :
    (yonedaEquiv.symm x).app Y = ↾fun f ↦ F.map f.op x :=
  rfl
/-
**CategoryTheory.yonedaEquiv_symm_app_apply** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory`。
形式化陈述：yonedaEquiv_symm_app_apply {X : C} {F : Cᵒᵖ ⥤ Type v₁} (x : F.obj (op X)) 
(Y : Cᵒᵖ) (f : Y.unop ⟶ X) : dsimp% (yonedaEquiv.symm x).app Y f = F.map f.op x
参数：x : F.obj (op X)；Y : Cᵒᵖ；f : Y.unop ⟶ X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem yonedaEquiv_symm_app_apply {X : C} {F : Cᵒᵖ ⥤ Type v₁} (x : F.obj (op X)) (Y : Cᵒᵖ)
    (f : Y.unop ⟶ X) : dsimp% (yonedaEquiv.symm x).app Y f = F.map f.op x :=
  rfl

/-- See also `yonedaEquiv_naturality'` for a more general version. -/
/-
**CategoryTheory.yonedaEquiv_naturality** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y`。
形式化陈述：yonedaEquiv_naturality {X Y : C} {F : Cᵒᵖ ⥤ Type v₁} (f : yoneda.obj X ⟶ F
) (g : Y ⟶ X) : F.map g.op (yonedaEquiv f) = yonedaEquiv (yoneda.map g ≫ f)
参数：f : yoneda.obj X ⟶ F；g : Y ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatTrans.naturality_apply`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {D : Type u_1} [inst_1 : CategoryTheory.Category.{v_1
, u_1} D]   {FD : outParam (D …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
See also `yonedaEquiv_naturality'` for a more general version.
-/
lemma yonedaEquiv_naturality {X Y : C} {F : Cᵒᵖ ⥤ Type v₁} (f : yoneda.obj X ⟶ F)
    (g : Y ⟶ X) : F.map g.op (yonedaEquiv f) = yonedaEquiv (yoneda.map g ≫ f) := by
  simp [yonedaEquiv, ← f.naturality_apply]

/-- Variant of `yonedaEquiv_naturality` with general `g`. This is technically strictly more general
    than `yonedaEquiv_naturality`, but `yonedaEquiv_naturality` is sometimes preferable because it
    can avoid the "motive is not type correct" error. -/
/-
**CategoryTheory.yonedaEquiv_naturality'** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry`。
形式化陈述：yonedaEquiv_naturality' {X Y : Cᵒᵖ} {F : Cᵒᵖ ⥤ Type v₁} (f : yoneda.obj (u
nop X) ⟶ F) (g : X ⟶ Y) : F.map g (yonedaEquiv f) = yonedaEquiv (yoneda.map g.un
op ≫ f)
参数：f : yoneda.obj (unop X) ⟶ F；g : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.yonedaEquiv_naturality`：yonedaEquiv_naturality {X Y : C} 
{F : Cᵒᵖ ⥤ Type v₁} (f : yoneda.obj X ⟶ F) (g : Y ⟶ X) : F.map g.op (yonedaEquiv
 f) = yonedaEquiv (yoneda.m…

--- 原说明 ---
Variant of `yonedaEquiv_naturality` with general `g`. This is technically strict
ly more general
    than `yonedaEquiv_naturality`, but `yonedaEquiv_naturality` is sometimes pre
ferable because it
    can avoid the "motive is not type correct" error.
-/
lemma yonedaEquiv_naturality' {X Y : Cᵒᵖ} {F : Cᵒᵖ ⥤ Type v₁} (f : yoneda.obj (unop X) ⟶ F)
    (g : X ⟶ Y) : F.map g (yonedaEquiv f) = yonedaEquiv (yoneda.map g.unop ≫ f) :=
  yonedaEquiv_naturality _ _
/-
**CategoryTheory.yonedaEquiv_comp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：yonedaEquiv_comp {X : C} {F G : Cᵒᵖ ⥤ Type v₁} (α : yoneda.obj X ⟶ F) (β :
 F ⟶ G) : yonedaEquiv (α ≫ β) = β.app _ (yonedaEquiv α)
参数：α : yoneda.obj X ⟶ F；β : F ⟶ G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma yonedaEquiv_comp {X : C} {F G : Cᵒᵖ ⥤ Type v₁} (α : yoneda.obj X ⟶ F) (β : F ⟶ G) :
    yonedaEquiv (α ≫ β) = β.app _ (yonedaEquiv α) :=
  rfl
/-
**CategoryTheory.yonedaEquiv_yoneda_map** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y`。
形式化陈述：yonedaEquiv_yoneda_map {X Y : C} (f : X ⟶ Y) : yonedaEquiv (yoneda.map f) 
= f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.yonedaEquiv_apply`：yonedaEquiv_apply {X : C} {F : Cᵒᵖ ⥤ T
ype v₁} (f : yoneda.obj X ⟶ F) : yonedaEquiv f = f.app (op X) (𝟙 X)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma yonedaEquiv_yoneda_map {X Y : C} (f : X ⟶ Y) : yonedaEquiv (yoneda.map f) = f := by
  rw [yonedaEquiv_apply]
  simp

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.yonedaEquiv_symm_naturality_left** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory`。
形式化陈述：yonedaEquiv_symm_naturality_left {X X' : C} (f : X' ⟶ X) (F : Cᵒᵖ ⥤ Type v
₁) (x : F.obj ⟨X⟩) : yoneda.map f ≫ yonedaEquiv.symm x = yonedaEquiv.symm ((F.ma
p f.op) x)
参数：f : X' ⟶ X；F : Cᵒᵖ ⥤ Type v₁；x : F.obj ⟨X⟩。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma yonedaEquiv_symm_naturality_left {X X' : C} (f : X' ⟶ X) (F : Cᵒᵖ ⥤ Type v₁)
    (x : F.obj ⟨X⟩) : yoneda.map f ≫ yonedaEquiv.symm x = yonedaEquiv.symm ((F.map f.op) x) := by
  apply yonedaEquiv.injective
  simp [yonedaEquiv]
/-
**CategoryTheory.yonedaEquiv_symm_naturality_right** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory`。
形式化陈述：yonedaEquiv_symm_naturality_right (X : C) {F F' : Cᵒᵖ ⥤ Type v₁} (f : F ⟶ 
F') (x : F.obj ⟨X⟩) : yonedaEquiv.symm x ≫ f = yonedaEquiv.symm (f.app ⟨X⟩ x)
参数：X : C；f : F ⟶ F'；x : F.obj ⟨X⟩。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma yonedaEquiv_symm_naturality_right (X : C) {F F' : Cᵒᵖ ⥤ Type v₁} (f : F ⟶ F')
    (x : F.obj ⟨X⟩) : yonedaEquiv.symm x ≫ f = yonedaEquiv.symm (f.app ⟨X⟩ x) := by
  apply yonedaEquiv.injective
  simp [yonedaEquiv_comp]

/-- See also `map_yonedaEquiv'` for a more general version. -/
/-
**CategoryTheory.map_yonedaEquiv** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：map_yonedaEquiv {X Y : C} {F : Cᵒᵖ ⥤ Type v₁} (f : yoneda.obj X ⟶ F) (g : 
Y ⟶ X) : F.map g.op (yonedaEquiv f) = f.app (op Y) g
参数：f : yoneda.obj X ⟶ F；g : Y ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.yonedaEquiv_naturality`：yonedaEquiv_naturality {X Y : C} 
{F : Cᵒᵖ ⥤ Type v₁} (f : yoneda.obj X ⟶ F) (g : Y ⟶ X) : F.map g.op (yonedaEquiv
 f) = yonedaEquiv (yoneda.m…
· 使用引理 `CategoryTheory.yonedaEquiv_comp`：yonedaEquiv_comp {X : C} {F G : Cᵒᵖ ⥤ T
ype v₁} (α : yoneda.obj X ⟶ F) (β : F ⟶ G) : yonedaEquiv (α ≫ β) = β.app _ (yone
daEquiv α)
· 使用引理 `CategoryTheory.yonedaEquiv_yoneda_map`：yonedaEquiv_yoneda_map {X Y : C} 
(f : X ⟶ Y) : yonedaEquiv (yoneda.map f) = f

--- 原说明 ---
See also `map_yonedaEquiv'` for a more general version.
-/
lemma map_yonedaEquiv {X Y : C} {F : Cᵒᵖ ⥤ Type v₁} (f : yoneda.obj X ⟶ F)
    (g : Y ⟶ X) : F.map g.op (yonedaEquiv f) = f.app (op Y) g := by
  rw [yonedaEquiv_naturality, yonedaEquiv_comp, yonedaEquiv_yoneda_map]

/-- Variant of `map_yonedaEquiv` with general `g`. This is technically strictly more general
    than `map_yonedaEquiv`, but `map_yonedaEquiv` is sometimes preferable because it
    can avoid the "motive is not type correct" error. -/
/-
**CategoryTheory.map_yonedaEquiv'** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：map_yonedaEquiv' {X Y : Cᵒᵖ} {F : Cᵒᵖ ⥤ Type v₁} (f : yoneda.obj (unop X) 
⟶ F) (g : X ⟶ Y) : F.map g (yonedaEquiv f) = f.app Y g.unop
参数：f : yoneda.obj (unop X) ⟶ F；g : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.yonedaEquiv_naturality'`：yonedaEquiv_naturality' {X Y : C
ᵒᵖ} {F : Cᵒᵖ ⥤ Type v₁} (f : yoneda.obj (unop X) ⟶ F) (g : X ⟶ Y) : F.map g (yon
edaEquiv f) = yonedaEquiv (y…
· 使用引理 `CategoryTheory.yonedaEquiv_comp`：yonedaEquiv_comp {X : C} {F G : Cᵒᵖ ⥤ T
ype v₁} (α : yoneda.obj X ⟶ F) (β : F ⟶ G) : yonedaEquiv (α ≫ β) = β.app _ (yone
daEquiv α)
· 使用引理 `CategoryTheory.yonedaEquiv_yoneda_map`：yonedaEquiv_yoneda_map {X Y : C} 
(f : X ⟶ Y) : yonedaEquiv (yoneda.map f) = f

--- 原说明 ---
Variant of `map_yonedaEquiv` with general `g`. This is technically strictly more
 general
    than `map_yonedaEquiv`, but `map_yonedaEquiv` is sometimes preferable becaus
e it
    can avoid the "motive is not type correct" error.
-/
lemma map_yonedaEquiv' {X Y : Cᵒᵖ} {F : Cᵒᵖ ⥤ Type v₁} (f : yoneda.obj (unop X) ⟶ F)
    (g : X ⟶ Y) : F.map g (yonedaEquiv f) = f.app Y g.unop := by
  rw [yonedaEquiv_naturality', yonedaEquiv_comp, yonedaEquiv_yoneda_map]
/-
**CategoryTheory.yonedaEquiv_symm_map** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`
。
形式化陈述：yonedaEquiv_symm_map {X Y : Cᵒᵖ} (f : X ⟶ Y) {F : Cᵒᵖ ⥤ Type v₁} (t : F.ob
j X) : yonedaEquiv.symm (F.map f t) = yoneda.map f.unop ≫ yonedaEquiv.symm t
参数：f : X ⟶ Y；t : F.obj X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.yonedaEquiv_naturality'`：yonedaEquiv_naturality' {X Y : C
ᵒᵖ} {F : Cᵒᵖ ⥤ Type v₁} (f : yoneda.obj (unop X) ⟶ F) (g : X ⟶ Y) : F.map g (yon
edaEquiv f) = yonedaEquiv (y…
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
lemma yonedaEquiv_symm_map {X Y : Cᵒᵖ} (f : X ⟶ Y) {F : Cᵒᵖ ⥤ Type v₁} (t : F.obj X) :
    yonedaEquiv.symm (F.map f t) = yoneda.map f.unop ≫ yonedaEquiv.symm t := by
  obtain ⟨u, rfl⟩ := yonedaEquiv.surjective t
  rw [yonedaEquiv_naturality', Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- Two morphisms of presheaves of types `P ⟶ Q` coincide if the precompositions
with morphisms `yoneda.obj X ⟶ P` agree. -/
/-
**CategoryTheory.hom_ext_yoneda** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：hom_ext_yoneda {P Q : Cᵒᵖ ⥤ Type v₁} {f g : P ⟶ Q} (h : forall (X : C) (p 
: yoneda.obj X ⟶ P), p ≫ f = p ≫ g) : f = g
参数：h : forall (X : C) (p : yoneda.obj X ⟶ P), p ≫ f = p ≫ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `TypeCat.Fun.ext`：∀ {X : Type u_1} {Y : Type u_2} {x y : TypeCat.Fun X Y}
, x.toFun = y.toFun → x = y
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂

--- 原说明 ---
Two morphisms of presheaves of types `P ⟶ Q` coincide if the precompositions
with morphisms `yoneda.obj X ⟶ P` agree.
-/
lemma hom_ext_yoneda {P Q : Cᵒᵖ ⥤ Type v₁} {f g : P ⟶ Q}
    (h : ∀ (X : C) (p : yoneda.obj X ⟶ P), p ≫ f = p ≫ g) :
    f = g := by
  ext X x
  simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply]
    using! congr_arg (yonedaEquiv) (h _ (yonedaEquiv.symm x))

variable (C)

/-- The "Yoneda evaluation" functor, which sends `X : Cᵒᵖ` and `F : Cᵒᵖ ⥤ Type`
to `F.obj X`, functorially in both `X` and `F`.
-/
/-
**CategoryTheory.yonedaEvaluation** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：yonedaEvaluation : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁) ⥤ Type (max u₁ v₁)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The "Yoneda evaluation" functor, which sends `X : Cᵒᵖ` and `F : Cᵒᵖ ⥤ Type`
to `F.obj X`, functorially in both `X` and `F`.
-/
def yonedaEvaluation : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁) ⥤ Type (max u₁ v₁) :=
  evaluationUncurried Cᵒᵖ (Type v₁) ⋙ uliftFunctor

@[simp]
/-
**CategoryTheory.yonedaEvaluation_map_down** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory`。
形式化陈述：yonedaEvaluation_map_down (P Q : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁)) (α : P ⟶ Q) (x : (
yonedaEvaluation C).obj P) : ((yonedaEvaluation C).map α x).down = α.2.app Q.1 (
P.2.map α.1 x.down)
参数：P Q : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁)；α : P ⟶ Q；x : (yonedaEvaluation C).obj P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem yonedaEvaluation_map_down (P Q : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁)) (α : P ⟶ Q)
    (x : (yonedaEvaluation C).obj P) :
    ((yonedaEvaluation C).map α x).down = α.2.app Q.1 (P.2.map α.1 x.down) :=
  rfl

/-- The "Yoneda pairing" functor, which sends `X : Cᵒᵖ` and `F : Cᵒᵖ ⥤ Type`
to `yoneda.op.obj X ⟶ F`, functorially in both `X` and `F`.
-/
/-
**CategoryTheory.yonedaPairing** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：yonedaPairing : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁) ⥤ Type (max u₁ v₁)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The "Yoneda pairing" functor, which sends `X : Cᵒᵖ` and `F : Cᵒᵖ ⥤ Type`
to `yoneda.op.obj X ⟶ F`, functorially in both `X` and `F`.
-/
def yonedaPairing : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁) ⥤ Type (max u₁ v₁) :=
  Functor.prod yoneda.op (𝟭 (Cᵒᵖ ⥤ Type v₁)) ⋙ Functor.hom (Cᵒᵖ ⥤ Type v₁)

@[ext]
/-
**CategoryTheory.yonedaPairingExt** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：yonedaPairingExt {X : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁)} {x y : (yonedaPairing C).obj 
X} (w : forall Y, x.app Y = y.app Y) : x = y
参数：Cᵒᵖ ⥤ Type v₁；yonedaPairing C；w : forall Y, x.app Y = y.app Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext`：∀ {C : Type u₁} {inst : CategoryTheory.Cate
gory.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D}   {
F G : CategoryThe…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma yonedaPairingExt {X : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁)} {x y : (yonedaPairing C).obj X}
    (w : ∀ Y, x.app Y = y.app Y) : x = y :=
  NatTrans.ext (funext w)

@[simp]
/-
**CategoryTheory.yonedaPairing_map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：yonedaPairing_map (P Q : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁)) (α : P ⟶ Q) : (yonedaPairi
ng C).map α = ↾fun β => yoneda.map α.1.unop ≫ β ≫ α.2
参数：P Q : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁)；α : P ⟶ Q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem yonedaPairing_map (P Q : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁)) (α : P ⟶ Q) :
    (yonedaPairing C).map α = ↾fun β ↦ yoneda.map α.1.unop ≫ β ≫ α.2 :=
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The Yoneda lemma asserts that the Yoneda pairing
`(X : Cᵒᵖ, F : Cᵒᵖ ⥤ Type) ↦ (yoneda.obj (unop X) ⟶ F)`
is naturally isomorphic to the evaluation `(X, F) ↦ F.obj X`. -/
@[stacks 001P]
/-
**CategoryTheory.yonedaLemma** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：yonedaLemma : yonedaPairing C ≅ yonedaEvaluation C
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The Yoneda lemma asserts that the Yoneda pairing
`(X : Cᵒᵖ, F : Cᵒᵖ ⥤ Type) ↦ (yoneda.obj (unop X) ⟶ F)`
is naturally isomorphic to the evaluation `(X, F) ↦ F.obj X`.
-/
def yonedaLemma : yonedaPairing C ≅ yonedaEvaluation C :=
  NatIso.ofComponents
    (fun _ ↦ Equiv.toIso (yonedaEquiv.trans Equiv.ulift.symm))
    (by intro (X, F) (Y, G) f
        ext (a : yoneda.obj X.unop ⟶ F)
        apply ULift.ext
        dsimp [yonedaEvaluation, yonedaEquiv]
        simp [← NatTrans.naturality_apply])

variable {C}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/- Porting note: this used to be two calls to `tidy` -/
/-- The curried version of yoneda lemma when `C` is small. -/
/-
**CategoryTheory.curriedYonedaLemma** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：curriedYonedaLemma {C : Type u₁} [SmallCategory C] : (yoneda.op ⋙ coyoneda
 : Cᵒᵖ ⥤ (Cᵒᵖ ⥤ Type u₁) ⥤ Type u₁) ≅ evaluation Cᵒᵖ (Type u₁)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The curried version of yoneda lemma when `C` is small.
-/
def curriedYonedaLemma {C : Type u₁} [SmallCategory C] :
    (yoneda.op ⋙ coyoneda : Cᵒᵖ ⥤ (Cᵒᵖ ⥤ Type u₁) ⥤ Type u₁) ≅
      evaluation Cᵒᵖ (Type u₁) :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents (fun _ ↦ Equiv.toIso yonedaEquiv)) (by
    intro X Y f
    ext a b
    simp [yonedaEquiv, ← NatTrans.naturality_apply])

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The curried version of the Yoneda lemma. -/
/-
**CategoryTheory.largeCurriedYonedaLemma** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry`。
形式化陈述：largeCurriedYonedaLemma {C : Type u₁} [Category.{v₁} C] : yoneda.op ⋙ coyo
neda ≅ evaluation Cᵒᵖ (Type v₁) ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u₁}
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The curried version of the Yoneda lemma.
-/
def largeCurriedYonedaLemma {C : Type u₁} [Category.{v₁} C] :
    yoneda.op ⋙ coyoneda ≅
      evaluation Cᵒᵖ (Type v₁) ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u₁} :=
  NatIso.ofComponents
    (fun X => NatIso.ofComponents
      (fun _ => Equiv.toIso <| yonedaEquiv.trans Equiv.ulift.symm)
      (by
        intro Y Z f
        ext g
        simp [yonedaEquiv]))
    (by
      intro Y Z f
      ext F g
      simpa [← ULift.down_inj] using! (yonedaEquiv_naturality _ _).symm)

/-- Version of the Yoneda lemma where the presheaf is fixed but the argument varies. -/
/-
**CategoryTheory.yonedaOpCompYonedaObj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
`。
形式化陈述：yonedaOpCompYonedaObj {C : Type u₁} [Category.{v₁} C] (P : Cᵒᵖ ⥤ Type v₁) 
: yoneda.op ⋙ yoneda.obj P ≅ P ⋙ uliftFunctor.{u₁}
参数：P : Cᵒᵖ ⥤ Type v₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Version of the Yoneda lemma where the presheaf is fixed but the argument varies.
-/
def yonedaOpCompYonedaObj {C : Type u₁} [Category.{v₁} C] (P : Cᵒᵖ ⥤ Type v₁) :
    yoneda.op ⋙ yoneda.obj P ≅ P ⋙ uliftFunctor.{u₁} :=
  isoWhiskerRight largeCurriedYonedaLemma ((evaluation _ _).obj P)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The curried version of yoneda lemma when `C` is small. -/
/-
**CategoryTheory.curriedYonedaLemma'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：curriedYonedaLemma' {C : Type u₁} [SmallCategory C] : yoneda ⋙ (whiskering
Left Cᵒᵖ (Cᵒᵖ ⥤ Type u₁)ᵒᵖ (Type u₁)).obj yoneda.op ≅ 𝟭 (Cᵒᵖ ⥤ Type u₁)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The curried version of yoneda lemma when `C` is small.
-/
def curriedYonedaLemma' {C : Type u₁} [SmallCategory C] :
    yoneda ⋙ (whiskeringLeft Cᵒᵖ (Cᵒᵖ ⥤ Type u₁)ᵒᵖ (Type u₁)).obj yoneda.op
      ≅ 𝟭 (Cᵒᵖ ⥤ Type u₁) :=
  NatIso.ofComponents (fun F ↦ NatIso.ofComponents (fun _ ↦ Equiv.toIso yonedaEquiv) (by
    intro X Y f
    ext a
    dsimp [yonedaEquiv]
    simp [← NatTrans.naturality_apply]))
/-
**CategoryTheory.isIso_of_yoneda_map_bijective** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory`。
形式化陈述：isIso_of_yoneda_map_bijective {X Y : C} (f : X ⟶ Y) (hf : forall (T : C), 
Function.Bijective (fun (x : T ⟶ X) => x ≫ f)) : IsIso f
参数：f : X ⟶ Y；hf : forall (T : C), Function.Bijective (fun (x : T ⟶ X) => x ≫ f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isIso_of_yoneda_map_bijective {X Y : C} (f : X ⟶ Y)
    (hf : ∀ (T : C), Function.Bijective (fun (x : T ⟶ X) => x ≫ f)) :
    IsIso f := by
  obtain ⟨g, hg : g ≫ f = 𝟙 Y⟩ := (hf Y).2 (𝟙 Y)
  exact ⟨g, (hf _).1 (by cat_disch), hg⟩
/-
**CategoryTheory.isIso_iff_yoneda_map_bijective** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory`。
形式化陈述：isIso_iff_yoneda_map_bijective {X Y : C} (f : X ⟶ Y) : IsIso f ↔ (forall (
T : C), Function.Bijective (fun (x : T ⟶ X) => x ≫ f))
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.bijective_iff_isIso_ofHom`：bijective_iff_isIso_ofHom {X Y
 : Type u} (f : X -> Y) : Function.Bijective f ↔ IsIso (ofHom f)
· 使用引理 `CategoryTheory.isIso_of_yoneda_map_bijective`：isIso_of_yoneda_map_biject
ive {X Y : C} (f : X ⟶ Y) (hf : forall (T : C), Function.Bijective (fun (x : T ⟶
 X) => x ≫ f)) : IsIso f
-/
lemma isIso_iff_yoneda_map_bijective {X Y : C} (f : X ⟶ Y) :
    IsIso f ↔ (∀ (T : C), Function.Bijective (fun (x : T ⟶ X) => x ≫ f)) := by
  refine ⟨fun _ ↦ ?_, fun hf ↦ isIso_of_yoneda_map_bijective f hf⟩
  intro T
  rw [bijective_iff_isIso_ofHom]
  exact inferInstanceAs (IsIso ((yoneda.map f).app _))
/-
**CategoryTheory.isIso_iff_isIso_yoneda_map** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory`。
形式化陈述：isIso_iff_isIso_yoneda_map {X Y : C} (f : X ⟶ Y) : IsIso f ↔ forall c : C,
 IsIso ((yoneda.map f).app ⟨c⟩)
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.isIso_iff_yoneda_map_bijective`：isIso_iff_yoneda_map_bije
ctive {X Y : C} (f : X ⟶ Y) : IsIso f ↔ (forall (T : C), Function.Bijective (fun
 (x : T ⟶ X) => x ≫ f))
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `CategoryTheory.bijective_iff_isIso_ofHom`：bijective_iff_isIso_ofHom {X Y
 : Type u} (f : X -> Y) : Function.Bijective f ↔ IsIso (ofHom f)
-/
lemma isIso_iff_isIso_yoneda_map {X Y : C} (f : X ⟶ Y) :
    IsIso f ↔ ∀ c : C, IsIso ((yoneda.map f).app ⟨c⟩) := by
  rw [isIso_iff_yoneda_map_bijective]
  exact forall_congr' fun _ ↦ (bijective_iff_isIso_ofHom _)

set_option backward.defeqAttrib.useBackward true in
/-- Yoneda's lemma as a bijection `(uliftYoneda.{w}.obj X ⟶ F) ≃ F.obj (op X)`
for any presheaf of type `F : Cᵒᵖ ⥤ Type (max w v₁)` for some
auxiliary universe `w`. -/
@[simps! -isSimp apply symm_apply_app]
/-
**CategoryTheory.uliftYonedaEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：uliftYonedaEquiv {X : C} {F : Cᵒᵖ ⥤ Type (max w v₁)} : (uliftYoneda.{w}.ob
j X ⟶ F) ≃ F.obj (op X) where toFun τ
参数：max w v₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Yoneda's lemma as a bijection `(uliftYoneda.{w}.obj X ⟶ F) ≃ F.obj (op X)`
for any presheaf of type `F : Cᵒᵖ ⥤ Type (max w v₁)` for some
auxiliary universe `w`.
-/
def uliftYonedaEquiv {X : C} {F : Cᵒᵖ ⥤ Type (max w v₁)} :
    (uliftYoneda.{w}.obj X ⟶ F) ≃ F.obj (op X) where
  toFun τ := τ.app (op X) (ULift.up (𝟙 _))
  invFun x := { app Y := ↾fun y ↦ F.map y.down.op x }
  left_inv τ := by
    ext ⟨Y⟩ ⟨y⟩
    simp [← NatTrans.naturality_apply]
  right_inv x := by simp

attribute [simp] uliftYonedaEquiv_symm_apply_app

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.uliftYonedaEquiv_naturality** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory`。
形式化陈述：uliftYonedaEquiv_naturality {X Y : Cᵒᵖ} {F : Cᵒᵖ ⥤ Type (max w v₁)} (f : u
liftYoneda.{w}.obj (unop X) ⟶ F) (g : X ⟶ Y) : F.map g (uliftYonedaEquiv.{w} f) 
= uliftYonedaEquiv.{w} (uliftYoneda.map g.unop ≫ f)
参数：max w v₁；f : uliftYoneda.{w}.obj (unop X) ⟶ F；g : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatTrans.naturality_apply`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {D : Type u_1} [inst_1 : CategoryTheory.Category.{v_1
, u_1} D]   {FD : outParam (D …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma uliftYonedaEquiv_naturality {X Y : Cᵒᵖ} {F : Cᵒᵖ ⥤ Type (max w v₁)}
    (f : uliftYoneda.{w}.obj (unop X) ⟶ F) (g : X ⟶ Y) :
    F.map g (uliftYonedaEquiv.{w} f) = uliftYonedaEquiv.{w} (uliftYoneda.map g.unop ≫ f) := by
  simp [uliftYonedaEquiv, uliftYoneda, ← f.naturality_apply]
/-
**CategoryTheory.uliftYonedaEquiv_comp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
`。
形式化陈述：uliftYonedaEquiv_comp {X : C} {F G : Cᵒᵖ ⥤ Type (max w v₁)} (α : uliftYone
da.{w}.obj X ⟶ F) (β : F ⟶ G) : uliftYonedaEquiv.{w} (α ≫ β) = β.app _ (uliftYon
edaEquiv α)
参数：max w v₁；α : uliftYoneda.{w}.obj X ⟶ F；β : F ⟶ G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma uliftYonedaEquiv_comp {X : C} {F G : Cᵒᵖ ⥤ Type (max w v₁)}
    (α : uliftYoneda.{w}.obj X ⟶ F) (β : F ⟶ G) :
    uliftYonedaEquiv.{w} (α ≫ β) = β.app _ (uliftYonedaEquiv α) :=
  rfl

@[reassoc]
/-
**CategoryTheory.uliftYonedaEquiv_symm_map** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory`。
形式化陈述：uliftYonedaEquiv_symm_map {X Y : Cᵒᵖ} (f : X ⟶ Y) {F : Cᵒᵖ ⥤ Type (max w v
₁)} (t : F.obj X) : uliftYonedaEquiv.{w}.symm (F.map f t) = uliftYoneda.map f.un
op ≫ uliftYonedaEquiv.symm t
参数：f : X ⟶ Y；max w v₁；t : F.obj X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.uliftYonedaEquiv_naturality`：uliftYonedaEquiv_naturality 
{X Y : Cᵒᵖ} {F : Cᵒᵖ ⥤ Type (max w v₁)} (f : uliftYoneda.{w}.obj (unop X) ⟶ F) (
g : X ⟶ Y) : F.map g (uliftYoned…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma uliftYonedaEquiv_symm_map {X Y : Cᵒᵖ} (f : X ⟶ Y) {F : Cᵒᵖ ⥤ Type (max w v₁)}
    (t : F.obj X) :
    uliftYonedaEquiv.{w}.symm (F.map f t) =
      uliftYoneda.map f.unop ≫ uliftYonedaEquiv.symm t := by
  obtain ⟨u, rfl⟩ := uliftYonedaEquiv.surjective t
  rw [uliftYonedaEquiv_naturality]
  simp

@[reassoc]
/-
**CategoryTheory.uliftYonedaEquiv_symm_comp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory`。
形式化陈述：uliftYonedaEquiv_symm_comp {F G : Cᵒᵖ ⥤ Type max w v₁} {X : Cᵒᵖ} (x : F.ob
j X) (f : F ⟶ G) : uliftYonedaEquiv.symm x ≫ f = uliftYonedaEquiv.symm (f.app _ 
x)
参数：x : F.obj X；f : F ⟶ G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.uliftYonedaEquiv_comp`：uliftYonedaEquiv_comp {X : C} {F G
 : Cᵒᵖ ⥤ Type (max w v₁)} (α : uliftYoneda.{w}.obj X ⟶ F) (β : F ⟶ G) : uliftYon
edaEquiv.{w} (α ≫ β) = β.a…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma uliftYonedaEquiv_symm_comp
    {F G : Cᵒᵖ ⥤ Type max w v₁} {X : Cᵒᵖ} (x : F.obj X) (f : F ⟶ G) :
    uliftYonedaEquiv.symm x ≫ f = uliftYonedaEquiv.symm (f.app _ x) :=
  uliftYonedaEquiv.injective (by rw [uliftYonedaEquiv_comp]; simp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.uliftYonedaEquiv_uliftYoneda_map** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory`。
形式化陈述：uliftYonedaEquiv_uliftYoneda_map {X Y : C} (f : X ⟶ Y) : DFunLike.coe (β
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma uliftYonedaEquiv_uliftYoneda_map {X Y : C} (f : X ⟶ Y) :
    DFunLike.coe (β := fun _ ↦ ULift.{w} (X ⟶ Y))
        uliftYonedaEquiv.{w} (uliftYoneda.map f) = ULift.up f := by
  simp [uliftYonedaEquiv, uliftYoneda]

/-- Two morphisms of presheaves of types `P ⟶ Q` coincide if the precompositions
with morphisms `uliftYoneda.obj X ⟶ P` agree. -/
/-
**CategoryTheory.hom_ext_uliftYoneda** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：hom_ext_uliftYoneda {P Q : Cᵒᵖ ⥤ Type (max w v₁)} {f g : P ⟶ Q} (h : foral
l (X : C) (p : uliftYoneda.{w}.obj X ⟶ P), p ≫ f = p ≫ g) : f = g
参数：max w v₁；h : forall (X : C) (p : uliftYoneda.{w}.obj X ⟶ P), p ≫ f = p ≫ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `TypeCat.Fun.ext`：∀ {X : Type u_1} {Y : Type u_2} {x y : TypeCat.Fun X Y}
, x.toFun = y.toFun → x = y
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂

--- 原说明 ---
Two morphisms of presheaves of types `P ⟶ Q` coincide if the precompositions
with morphisms `uliftYoneda.obj X ⟶ P` agree.
-/
lemma hom_ext_uliftYoneda {P Q : Cᵒᵖ ⥤ Type (max w v₁)} {f g : P ⟶ Q}
    (h : ∀ (X : C) (p : uliftYoneda.{w}.obj X ⟶ P), p ≫ f = p ≫ g) :
    f = g := by
  ext X x
  simpa [-op_unop, uliftYonedaEquiv_comp] using
    congr_arg uliftYonedaEquiv.{w} (h _ (uliftYonedaEquiv.symm x))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A variant of the curried version of the Yoneda lemma with a raise in the universe level. -/
/-
**CategoryTheory.uliftYonedaOpCompCoyoneda** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory`。
形式化陈述：uliftYonedaOpCompCoyoneda {C : Type u₁} [Category.{v₁} C] : uliftYoneda.{w
}.op ⋙ coyoneda ≅ evaluation Cᵒᵖ (Type (max v₁ w)) ⋙ (whiskeringRight _ _ _).obj
 uliftFunctor.{u₁}
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
A variant of the curried version of the Yoneda lemma with a raise in the univers
e level.
-/
def uliftYonedaOpCompCoyoneda {C : Type u₁} [Category.{v₁} C] :
    uliftYoneda.{w}.op ⋙ coyoneda ≅
      evaluation Cᵒᵖ (Type (max v₁ w)) ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u₁} :=
  NatIso.ofComponents
    (fun X => NatIso.ofComponents
      (fun _ => Equiv.toIso <| uliftYonedaEquiv.trans Equiv.ulift.symm)
      (by
        intros Y Z f
        ext g
        rw [← ULift.down_inj]
        simpa using uliftYonedaEquiv_comp _ _))
    (by
      intros Y Z f
      ext F g
      rw [← ULift.down_inj]
      simpa using (uliftYonedaEquiv_naturality _ _).symm)

end YonedaLemma

section CoyonedaLemma

variable {C}

/-- We have a type-level equivalence between natural transformations from the coyoneda embedding
and elements of `F.obj X.unop`, without any universe switching.
-/
@[implicit_reducible]
/-
**CategoryTheory.coyonedaEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：coyonedaEquiv {X : C} {F : C ⥤ Type v₁} : (coyoneda.obj (op X) ⟶ F) ≃ F.ob
j X where toFun η
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We have a type-level equivalence between natural transformations from the coyone
da embedding
and elements of `F.obj X.unop`, without any universe switching.
-/
def coyonedaEquiv {X : C} {F : C ⥤ Type v₁} : (coyoneda.obj (op X) ⟶ F) ≃ F.obj X where
  toFun η := η.app X (𝟙 X)
  invFun ξ := { app _ := ↾fun x ↦ F.map x ξ }
  left_inv := fun η ↦ by
    ext Y (x : X ⟶ Y)
    simp [← NatTrans.naturality_apply]
  right_inv := by intro ξ; simp
/-
**CategoryTheory.coyonedaEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：coyonedaEquiv_apply {X : C} {F : C ⥤ Type v₁} (f : coyoneda.obj (op X) ⟶ F
) : coyonedaEquiv f = f.app X (𝟙 X)
参数：f : coyoneda.obj (op X) ⟶ F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coyonedaEquiv_apply {X : C} {F : C ⥤ Type v₁} (f : coyoneda.obj (op X) ⟶ F) :
    coyonedaEquiv f = f.app X (𝟙 X) :=
  rfl

@[simp]
/-
**CategoryTheory.coyonedaEquiv_symm_app_apply** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory`。
形式化陈述：coyonedaEquiv_symm_app_apply {X : C} {F : C ⥤ Type v₁} (x : F.obj X) (Y : 
C) (f : X ⟶ Y) : dsimp% (coyonedaEquiv.symm x).app Y f = F.map f x
参数：x : F.obj X；Y : C；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem coyonedaEquiv_symm_app_apply {X : C} {F : C ⥤ Type v₁} (x : F.obj X) (Y : C)
    (f : X ⟶ Y) : dsimp% (coyonedaEquiv.symm x).app Y f = F.map f x :=
  rfl
/-
**CategoryTheory.coyonedaEquiv_naturality** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory`。
形式化陈述：coyonedaEquiv_naturality {X Y : C} {F : C ⥤ Type v₁} (f : coyoneda.obj (op
 X) ⟶ F) (g : X ⟶ Y) : F.map g (coyonedaEquiv f) = coyonedaEquiv (coyoneda.map g
.op ≫ f)
参数：f : coyoneda.obj (op X) ⟶ F；g : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coyonedaEquiv_naturality {X Y : C} {F : C ⥤ Type v₁} (f : coyoneda.obj (op X) ⟶ F)
    (g : X ⟶ Y) : F.map g (coyonedaEquiv f) = coyonedaEquiv (coyoneda.map g.op ≫ f) := by
  change (f.app X ≫ F.map g) (𝟙 X) = f.app Y (g ≫ 𝟙 Y)
  rw [← f.naturality]
  simp
/-
**CategoryTheory.coyonedaEquiv_comp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：coyonedaEquiv_comp {X : C} {F G : C ⥤ Type v₁} (α : coyoneda.obj (op X) ⟶ 
F) (β : F ⟶ G) : coyonedaEquiv (α ≫ β) = β.app _ (coyonedaEquiv α)
参数：α : coyoneda.obj (op X) ⟶ F；β : F ⟶ G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coyonedaEquiv_comp {X : C} {F G : C ⥤ Type v₁} (α : coyoneda.obj (op X) ⟶ F) (β : F ⟶ G) :
    coyonedaEquiv (α ≫ β) = β.app _ (coyonedaEquiv α) := by
  rfl
/-
**CategoryTheory.coyonedaEquiv_coyoneda_map** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory`。
形式化陈述：coyonedaEquiv_coyoneda_map {X Y : C} (f : X ⟶ Y) : coyonedaEquiv (coyoneda
.map f.op) = f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.coyonedaEquiv_apply`：coyonedaEquiv_apply {X : C} {F : C ⥤
 Type v₁} (f : coyoneda.obj (op X) ⟶ F) : coyonedaEquiv f = f.app X (𝟙 X)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coyonedaEquiv_coyoneda_map {X Y : C} (f : X ⟶ Y) :
    coyonedaEquiv (coyoneda.map f.op) = f := by
  rw [coyonedaEquiv_apply]
  simp
/-
**CategoryTheory.map_coyonedaEquiv** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：map_coyonedaEquiv {X Y : C} {F : C ⥤ Type v₁} (f : coyoneda.obj (op X) ⟶ F
) (g : X ⟶ Y) : F.map g (coyonedaEquiv f) = f.app Y g
参数：f : coyoneda.obj (op X) ⟶ F；g : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.coyonedaEquiv_naturality`：coyonedaEquiv_naturality {X Y :
 C} {F : C ⥤ Type v₁} (f : coyoneda.obj (op X) ⟶ F) (g : X ⟶ Y) : F.map g (coyon
edaEquiv f) = coyonedaEquiv (…
· 使用引理 `CategoryTheory.coyonedaEquiv_comp`：coyonedaEquiv_comp {X : C} {F G : C ⥤
 Type v₁} (α : coyoneda.obj (op X) ⟶ F) (β : F ⟶ G) : coyonedaEquiv (α ≫ β) = β.
app _ (coyonedaEquiv α)
· 使用引理 `CategoryTheory.coyonedaEquiv_coyoneda_map`：coyonedaEquiv_coyoneda_map {X
 Y : C} (f : X ⟶ Y) : coyonedaEquiv (coyoneda.map f.op) = f
-/
lemma map_coyonedaEquiv {X Y : C} {F : C ⥤ Type v₁} (f : coyoneda.obj (op X) ⟶ F)
    (g : X ⟶ Y) : F.map g (coyonedaEquiv f) = f.app Y g := by
  rw [coyonedaEquiv_naturality, coyonedaEquiv_comp, coyonedaEquiv_coyoneda_map]
/-
**CategoryTheory.coyonedaEquiv_symm_map** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y`。
形式化陈述：coyonedaEquiv_symm_map {X Y : C} (f : X ⟶ Y) {F : C ⥤ Type v₁} (t : F.obj 
X) : coyonedaEquiv.symm (F.map f t) = coyoneda.map f.op ≫ coyonedaEquiv.symm t
参数：f : X ⟶ Y；t : F.obj X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.coyonedaEquiv_naturality`：coyonedaEquiv_naturality {X Y :
 C} {F : C ⥤ Type v₁} (f : coyoneda.obj (op X) ⟶ F) (g : X ⟶ Y) : F.map g (coyon
edaEquiv f) = coyonedaEquiv (…
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coyonedaEquiv_symm_map {X Y : C} (f : X ⟶ Y) {F : C ⥤ Type v₁} (t : F.obj X) :
    coyonedaEquiv.symm (F.map f t) = coyoneda.map f.op ≫ coyonedaEquiv.symm t := by
  obtain ⟨u, rfl⟩ := coyonedaEquiv.surjective t
  simp [coyonedaEquiv_naturality u f]

variable (C)

/-- The "Coyoneda evaluation" functor, which sends `X : C` and `F : C ⥤ Type`
to `F.obj X`, functorially in both `X` and `F`.
-/
/-
**CategoryTheory.coyonedaEvaluation** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：coyonedaEvaluation : C × (C ⥤ Type v₁) ⥤ Type (max u₁ v₁)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The "Coyoneda evaluation" functor, which sends `X : C` and `F : C ⥤ Type`
to `F.obj X`, functorially in both `X` and `F`.
-/
def coyonedaEvaluation : C × (C ⥤ Type v₁) ⥤ Type (max u₁ v₁) :=
  evaluationUncurried C (Type v₁) ⋙ uliftFunctor

@[simp]
/-
**CategoryTheory.coyonedaEvaluation_map_down** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory`。
形式化陈述：coyonedaEvaluation_map_down (P Q : C × (C ⥤ Type v₁)) (α : P ⟶ Q) (x : (co
yonedaEvaluation C).obj P) : ((coyonedaEvaluation C).map α x).down = α.2.app Q.1
 (P.2.map α.1 x.down)
参数：P Q : C × (C ⥤ Type v₁)；α : P ⟶ Q；x : (coyonedaEvaluation C).obj P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coyonedaEvaluation_map_down (P Q : C × (C ⥤ Type v₁)) (α : P ⟶ Q)
    (x : (coyonedaEvaluation C).obj P) :
    ((coyonedaEvaluation C).map α x).down = α.2.app Q.1 (P.2.map α.1 x.down) :=
  rfl

/-- The "Coyoneda pairing" functor, which sends `X : C` and `F : C ⥤ Type`
to `coyoneda.rightOp.obj X ⟶ F`, functorially in both `X` and `F`.
-/
/-
**CategoryTheory.coyonedaPairing** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：coyonedaPairing : C × (C ⥤ Type v₁) ⥤ Type (max u₁ v₁)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The "Coyoneda pairing" functor, which sends `X : C` and `F : C ⥤ Type`
to `coyoneda.rightOp.obj X ⟶ F`, functorially in both `X` and `F`.
-/
def coyonedaPairing : C × (C ⥤ Type v₁) ⥤ Type (max u₁ v₁) :=
  Functor.prod coyoneda.rightOp (𝟭 (C ⥤ Type v₁)) ⋙ Functor.hom (C ⥤ Type v₁)

@[ext]
/-
**CategoryTheory.coyonedaPairingExt** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：coyonedaPairingExt {X : C × (C ⥤ Type v₁)} {x y : (coyonedaPairing C).obj 
X} (w : forall Y, x.app Y = y.app Y) : x = y
参数：C ⥤ Type v₁；coyonedaPairing C；w : forall Y, x.app Y = y.app Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext`：∀ {C : Type u₁} {inst : CategoryTheory.Cate
gory.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D}   {
F G : CategoryThe…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma coyonedaPairingExt {X : C × (C ⥤ Type v₁)} {x y : (coyonedaPairing C).obj X}
    (w : ∀ Y, x.app Y = y.app Y) : x = y :=
  NatTrans.ext (funext w)

@[simp]
/-
**CategoryTheory.coyonedaPairing_map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：coyonedaPairing_map (P Q : C × (C ⥤ Type v₁)) (α : P ⟶ Q) (β : (coyonedaPa
iring C).obj P) : (coyonedaPairing C).map α β = coyoneda.map α.1.op ≫ β ≫ α.2
参数：P Q : C × (C ⥤ Type v₁)；α : P ⟶ Q；β : (coyonedaPairing C).obj P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coyonedaPairing_map (P Q : C × (C ⥤ Type v₁)) (α : P ⟶ Q) (β : (coyonedaPairing C).obj P) :
    (coyonedaPairing C).map α β = coyoneda.map α.1.op ≫ β ≫ α.2 :=
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The Coyoneda lemma asserts that the Coyoneda pairing
`(X : C, F : C ⥤ Type) ↦ (coyoneda.obj X ⟶ F)`
is naturally isomorphic to the evaluation `(X, F) ↦ F.obj X`. -/
@[stacks 001P]
/-
**CategoryTheory.coyonedaLemma** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：coyonedaLemma : coyonedaPairing C ≅ coyonedaEvaluation C
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The Coyoneda lemma asserts that the Coyoneda pairing
`(X : C, F : C ⥤ Type) ↦ (coyoneda.obj X ⟶ F)`
is naturally isomorphic to the evaluation `(X, F) ↦ F.obj X`.
-/
def coyonedaLemma : coyonedaPairing C ≅ coyonedaEvaluation C :=
  NatIso.ofComponents
    (fun _ ↦ Equiv.toIso (coyonedaEquiv.trans Equiv.ulift.symm))
    (by intro (X, F) (Y, G) f
        ext (a : coyoneda.obj (op X) ⟶ F)
        apply ULift.ext
        dsimp [coyonedaEquiv, coyonedaEvaluation]
        simp [← NatTrans.naturality_apply])

variable {C}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/- Porting note: this used to be two calls to `tidy` -/
/-- The curried version of coyoneda lemma when `C` is small. -/
/-
**CategoryTheory.curriedCoyonedaLemma** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`
。
形式化陈述：curriedCoyonedaLemma {C : Type u₁} [SmallCategory C] : coyoneda.rightOp ⋙ 
coyoneda ≅ evaluation C (Type u₁)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The curried version of coyoneda lemma when `C` is small.
-/
def curriedCoyonedaLemma {C : Type u₁} [SmallCategory C] :
    coyoneda.rightOp ⋙ coyoneda ≅ evaluation C (Type u₁) :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents (fun _ ↦ Equiv.toIso coyonedaEquiv)) (by
    intro X Y f
    ext a b
    simp [coyonedaEquiv, ← NatTrans.naturality_apply])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The curried version of the Coyoneda lemma. -/
/-
**CategoryTheory.largeCurriedCoyonedaLemma** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory`。
形式化陈述：largeCurriedCoyonedaLemma {C : Type u₁} [Category.{v₁} C] : coyoneda.right
Op ⋙ coyoneda ≅ evaluation C (Type v₁) ⋙ (whiskeringRight _ _ _).obj uliftFuncto
r.{u₁}
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The curried version of the Coyoneda lemma.
-/
def largeCurriedCoyonedaLemma {C : Type u₁} [Category.{v₁} C] :
    coyoneda.rightOp ⋙ coyoneda ≅
      evaluation C (Type v₁) ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u₁} :=
  NatIso.ofComponents
    (fun X => NatIso.ofComponents
      (fun _ => Equiv.toIso <| coyonedaEquiv.trans Equiv.ulift.symm)
      (by
        intro Y Z f
        ext g
        rw [← ULift.down_inj]
        simpa using coyonedaEquiv_comp _ _))
    (by
      intro Y Z f
      ext F g
      rw [← ULift.down_inj]
      simpa using (coyonedaEquiv_naturality _ _).symm)

/-- Version of the Coyoneda lemma where the presheaf is fixed but the argument varies. -/
/-
**CategoryTheory.coyonedaCompYonedaObj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
`。
形式化陈述：coyonedaCompYonedaObj {C : Type u₁} [Category.{v₁} C] (P : C ⥤ Type v₁) : 
coyoneda.rightOp ⋙ yoneda.obj P ≅ P ⋙ uliftFunctor.{u₁}
参数：P : C ⥤ Type v₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Version of the Coyoneda lemma where the presheaf is fixed but the argument varie
s.
-/
def coyonedaCompYonedaObj {C : Type u₁} [Category.{v₁} C] (P : C ⥤ Type v₁) :
    coyoneda.rightOp ⋙ yoneda.obj P ≅ P ⋙ uliftFunctor.{u₁} :=
  isoWhiskerRight largeCurriedCoyonedaLemma ((evaluation _ _).obj P)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The curried version of coyoneda lemma when `C` is small. -/
/-
**CategoryTheory.curriedCoyonedaLemma'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
`。
形式化陈述：curriedCoyonedaLemma' {C : Type u₁} [SmallCategory C] : yoneda ⋙ (whiskeri
ngLeft C (C ⥤ Type u₁)ᵒᵖ (Type u₁)).obj coyoneda.rightOp ≅ 𝟭 (C ⥤ Type u₁)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The curried version of coyoneda lemma when `C` is small.
-/
def curriedCoyonedaLemma' {C : Type u₁} [SmallCategory C] :
    yoneda ⋙ (whiskeringLeft C (C ⥤ Type u₁)ᵒᵖ (Type u₁)).obj coyoneda.rightOp
      ≅ 𝟭 (C ⥤ Type u₁) :=
  NatIso.ofComponents (fun F ↦ NatIso.ofComponents (fun _ ↦ Equiv.toIso coyonedaEquiv) (by
    intro X Y f
    ext a
    simp [coyonedaEquiv, ← NatTrans.naturality_apply]))
/-
**CategoryTheory.isIso_of_coyoneda_map_bijective** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory`。
形式化陈述：isIso_of_coyoneda_map_bijective {X Y : C} (f : X ⟶ Y) (hf : forall (T : C)
, Function.Bijective (fun (x : Y ⟶ T) => f ≫ x)) : IsIso f
参数：f : X ⟶ Y；hf : forall (T : C), Function.Bijective (fun (x : Y ⟶ T) => f ≫ x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isIso_of_coyoneda_map_bijective {X Y : C} (f : X ⟶ Y)
    (hf : ∀ (T : C), Function.Bijective (fun (x : Y ⟶ T) => f ≫ x)) :
    IsIso f := by
  obtain ⟨g, hg : f ≫ g = 𝟙 X⟩ := (hf X).2 (𝟙 X)
  refine ⟨g, hg, (hf _).1 ?_⟩
  simp only [Category.comp_id, ← Category.assoc, hg, Category.id_comp]
/-
**CategoryTheory.isIso_iff_coyoneda_map_bijective** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory`。
形式化陈述：isIso_iff_coyoneda_map_bijective {X Y : C} (f : X ⟶ Y) : IsIso f ↔ (forall
 (T : C), Function.Bijective (fun (x : Y ⟶ T) => f ≫ x))
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.bijective_iff_isIso_ofHom`：bijective_iff_isIso_ofHom {X Y
 : Type u} (f : X -> Y) : Function.Bijective f ↔ IsIso (ofHom f)
· 使用引理 `CategoryTheory.isIso_of_coyoneda_map_bijective`：isIso_of_coyoneda_map_bi
jective {X Y : C} (f : X ⟶ Y) (hf : forall (T : C), Function.Bijective (fun (x :
 Y ⟶ T) => f ≫ x)) : IsIso f
-/
lemma isIso_iff_coyoneda_map_bijective {X Y : C} (f : X ⟶ Y) :
    IsIso f ↔ (∀ (T : C), Function.Bijective (fun (x : Y ⟶ T) => f ≫ x)) := by
  refine ⟨fun _ ↦ ?_, fun hf ↦ isIso_of_coyoneda_map_bijective f hf⟩
  intro T
  rw [bijective_iff_isIso_ofHom]
  exact inferInstanceAs (IsIso ((coyoneda.map f.op).app _))
/-
**CategoryTheory.isIso_iff_isIso_coyoneda_map** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory`。
形式化陈述：isIso_iff_isIso_coyoneda_map {X Y : C} (f : X ⟶ Y) : IsIso f ↔ forall c : 
C, IsIso ((coyoneda.map f.op).app c)
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.isIso_iff_coyoneda_map_bijective`：isIso_iff_coyoneda_map_
bijective {X Y : C} (f : X ⟶ Y) : IsIso f ↔ (forall (T : C), Function.Bijective 
(fun (x : Y ⟶ T) => f ≫ x))
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `CategoryTheory.bijective_iff_isIso_ofHom`：bijective_iff_isIso_ofHom {X Y
 : Type u} (f : X -> Y) : Function.Bijective f ↔ IsIso (ofHom f)
-/
lemma isIso_iff_isIso_coyoneda_map {X Y : C} (f : X ⟶ Y) :
    IsIso f ↔ ∀ c : C, IsIso ((coyoneda.map f.op).app c) := by
  rw [isIso_iff_coyoneda_map_bijective]
  exact forall_congr' fun _ ↦ bijective_iff_isIso_ofHom _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Coyoneda's lemma as a bijection `(uliftCoyoneda.{w}.obj X ⟶ F) ≃ F.obj (op X)`
for any presheaf of type `F : Cᵒᵖ ⥤ Type (max w v₁)` for some
auxiliary universe `w`. -/
@[simps! -isSimp apply symm_apply_app]
/-
**CategoryTheory.uliftCoyonedaEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：uliftCoyonedaEquiv {X : Cᵒᵖ} {F : C ⥤ Type (max w v₁)} : (uliftCoyoneda.{w
}.obj X ⟶ F) ≃ F.obj X.unop where toFun τ
参数：max w v₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coyoneda's lemma as a bijection `(uliftCoyoneda.{w}.obj X ⟶ F) ≃ F.obj (op X)`
for any presheaf of type `F : Cᵒᵖ ⥤ Type (max w v₁)` for some
auxiliary universe `w`.
-/
def uliftCoyonedaEquiv {X : Cᵒᵖ} {F : C ⥤ Type (max w v₁)} :
    (uliftCoyoneda.{w}.obj X ⟶ F) ≃ F.obj X.unop where
  toFun τ := τ.app X.unop (ULift.up (𝟙 _))
  invFun x := { app Y := ↾fun y ↦ F.map y.down x }
  left_inv τ := by
    ext Y ⟨x⟩
    simp [← comp_apply, ← τ.naturality]
  right_inv x := by simp

attribute [simp] uliftCoyonedaEquiv_symm_apply_app

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.uliftCoyonedaEquiv_naturality** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory`。
形式化陈述：uliftCoyonedaEquiv_naturality {X Y : C} {F : C ⥤ Type max w v₁} (f : ulift
Coyoneda.{w}.obj (op X) ⟶ F) (g : X ⟶ Y) : F.map g (uliftCoyonedaEquiv.{w} f) = 
uliftCoyonedaEquiv.{w} (uliftCoyoneda.map g.op ≫ f)
参数：f : uliftCoyoneda.{w}.obj (op X) ⟶ F；g : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma uliftCoyonedaEquiv_naturality {X Y : C} {F : C ⥤ Type max w v₁}
    (f : uliftCoyoneda.{w}.obj (op X) ⟶ F) (g : X ⟶ Y) :
    F.map g (uliftCoyonedaEquiv.{w} f) = uliftCoyonedaEquiv.{w} (uliftCoyoneda.map g.op ≫ f) := by
  simp [uliftCoyonedaEquiv, ← comp_apply, ← f.naturality]
/-
**CategoryTheory.uliftCoyonedaEquiv_comp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry`。
形式化陈述：uliftCoyonedaEquiv_comp {X : Cᵒᵖ} {F G : C ⥤ Type (max w v₁)} (α : uliftCo
yoneda.{w}.obj X ⟶ F) (β : F ⟶ G) : uliftCoyonedaEquiv.{w} (α ≫ β) = β.app _ (ul
iftCoyonedaEquiv α)
参数：max w v₁；α : uliftCoyoneda.{w}.obj X ⟶ F；β : F ⟶ G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma uliftCoyonedaEquiv_comp {X : Cᵒᵖ} {F G : C ⥤ Type (max w v₁)}
    (α : uliftCoyoneda.{w}.obj X ⟶ F) (β : F ⟶ G) :
    uliftCoyonedaEquiv.{w} (α ≫ β) = β.app _ (uliftCoyonedaEquiv α) :=
  rfl

@[reassoc]
/-
**CategoryTheory.uliftCoyonedaEquiv_symm_map** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory`。
形式化陈述：uliftCoyonedaEquiv_symm_map {X Y : C} (f : X ⟶ Y) {F : C ⥤ Type (max w v₁)
} (t : F.obj X) : uliftCoyonedaEquiv.{w}.symm (F.map f t) = uliftCoyoneda.map f.
op ≫ uliftCoyonedaEquiv.symm t
参数：f : X ⟶ Y；max w v₁；t : F.obj X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.uliftCoyonedaEquiv_naturality`：uliftCoyonedaEquiv_natural
ity {X Y : C} {F : C ⥤ Type max w v₁} (f : uliftCoyoneda.{w}.obj (op X) ⟶ F) (g 
: X ⟶ Y) : F.map g (uliftCoyonedaE…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma uliftCoyonedaEquiv_symm_map {X Y : C} (f : X ⟶ Y) {F : C ⥤ Type (max w v₁)}
    (t : F.obj X) :
    uliftCoyonedaEquiv.{w}.symm (F.map f t) =
      uliftCoyoneda.map f.op ≫ uliftCoyonedaEquiv.symm t := by
  obtain ⟨u, rfl⟩ := uliftCoyonedaEquiv.surjective t
  rw [uliftCoyonedaEquiv_naturality]
  simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.uliftCoyonedaEquiv_uliftCoyoneda_map** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory`。
形式化陈述：uliftCoyonedaEquiv_uliftCoyoneda_map {X Y : Cᵒᵖ} (f : X ⟶ Y) : DFunLike.co
e (β
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma uliftCoyonedaEquiv_uliftCoyoneda_map {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    DFunLike.coe (β := fun _ ↦ ULift.{w} (Y.unop ⟶ X.unop))
        uliftCoyonedaEquiv.{w} (uliftCoyoneda.map f) = ULift.up f.unop := by
  simp [uliftCoyonedaEquiv, uliftYoneda]

set_option backward.isDefEq.respectTransparency.types false in
/-- Two morphisms of presheaves of types `P ⟶ Q` coincide if the precompositions
with morphisms `uliftCoyoneda.obj X ⟶ P` agree. -/
/-
**CategoryTheory.hom_ext_uliftCoyoneda** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
`。
形式化陈述：hom_ext_uliftCoyoneda {P Q : C ⥤ Type (max w v₁)} {f g : P ⟶ Q} (h : foral
l (X : Cᵒᵖ) (p : uliftCoyoneda.{w}.obj X ⟶ P), p ≫ f = p ≫ g) : f = g
参数：max w v₁；h : forall (X : Cᵒᵖ) (p : uliftCoyoneda.{w}.obj X ⟶ P), p ≫ f = p ≫ 
g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `TypeCat.Fun.ext`：∀ {X : Type u_1} {Y : Type u_2} {x y : TypeCat.Fun X Y}
, x.toFun = y.toFun → x = y
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂

--- 原说明 ---
Two morphisms of presheaves of types `P ⟶ Q` coincide if the precompositions
with morphisms `uliftCoyoneda.obj X ⟶ P` agree.
-/
lemma hom_ext_uliftCoyoneda {P Q : C ⥤ Type (max w v₁)} {f g : P ⟶ Q}
    (h : ∀ (X : Cᵒᵖ) (p : uliftCoyoneda.{w}.obj X ⟶ P), p ≫ f = p ≫ g) :
    f = g := by
  ext X x
  simpa [uliftCoyonedaEquiv]
    using congr_arg uliftCoyonedaEquiv.{w} (h _ (uliftCoyonedaEquiv.symm x))

set_option backward.isDefEq.respectTransparency false in
/-- A variant of the curried version of the Coyoneda lemma with a raise in the universe level. -/
/-
**CategoryTheory.uliftCoyonedaRightOpCompCoyoneda** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory`。
形式化陈述：uliftCoyonedaRightOpCompCoyoneda {C : Type u₁} [Category.{v₁} C] : uliftCo
yoneda.{w}.rightOp ⋙ coyoneda ≅ evaluation C (Type (max v₁ w)) ⋙ (whiskeringRigh
t _ _ _).obj uliftFunctor.{u₁}
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
A variant of the curried version of the Coyoneda lemma with a raise in the unive
rse level.
-/
def uliftCoyonedaRightOpCompCoyoneda {C : Type u₁} [Category.{v₁} C] :
    uliftCoyoneda.{w}.rightOp ⋙ coyoneda ≅
      evaluation C (Type (max v₁ w)) ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u₁} :=
  NatIso.ofComponents
    (fun X => NatIso.ofComponents
      (fun _ => Equiv.toIso <| uliftCoyonedaEquiv.trans Equiv.ulift.symm)
      (by
        intros Y Z f
        ext g
        rw [← ULift.down_inj]
        simpa using uliftCoyonedaEquiv_comp _ _))
    (by
      intros Y Z f
      ext F g
      rw [← ULift.down_inj]
      simpa using (uliftCoyonedaEquiv_naturality _ _).symm)

end CoyonedaLemma

section

variable {C}
variable {D : Type*} [Category.{v₁} D] (F : C ⥤ D)

/-- The natural transformation `yoneda.obj X ⟶ F.op ⋙ yoneda.obj (F.obj X)`
when `F : C ⥤ D` and `X : C`. -/
/-
**CategoryTheory.yonedaMap** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：yonedaMap (X : C) : yoneda.obj X ⟶ F.op ⋙ yoneda.obj (F.obj X) where app _
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural transformation `yoneda.obj X ⟶ F.op ⋙ yoneda.obj (F.obj X)`
when `F : C ⥤ D` and `X : C`.
-/
def yonedaMap (X : C) : yoneda.obj X ⟶ F.op ⋙ yoneda.obj (F.obj X) where
  app _ := ↾fun f ↦ F.map f

@[simp]
/-
**CategoryTheory.yonedaMap_app_apply** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：yonedaMap_app_apply {Y : C} {X : Cᵒᵖ} (f : X.unop ⟶ Y) : dsimp% (yonedaMap
 F Y).app X f = F.map f
参数：f : X.unop ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma yonedaMap_app_apply {Y : C} {X : Cᵒᵖ} (f : X.unop ⟶ Y) :
    dsimp% (yonedaMap F Y).app X f = F.map f := rfl

end

section

variable {C}
variable {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)

/-- The natural transformation `uliftYoneda.obj X ⟶ F.op ⋙ uliftYoneda.obj (F.obj X)`
when `F : C ⥤ D` and `X : C`. -/
/-
**CategoryTheory.uliftYonedaMap** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：uliftYonedaMap (X : C) : uliftYoneda.{max w v₂}.obj X ⟶ F.op ⋙ uliftYoneda
.{max w v₁}.obj (F.obj X) where app _
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural transformation `uliftYoneda.obj X ⟶ F.op ⋙ uliftYoneda.obj (F.obj X)
`
when `F : C ⥤ D` and `X : C`.
-/
def uliftYonedaMap (X : C) :
    uliftYoneda.{max w v₂}.obj X ⟶ F.op ⋙ uliftYoneda.{max w v₁}.obj (F.obj X) where
  app _ := ↾fun f ↦ ULift.up (F.map (ULift.down f))

@[simp]
/-
**CategoryTheory.uliftYonedaMap_app_apply** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory`。
形式化陈述：uliftYonedaMap_app_apply {Y : C} {X : Cᵒᵖ} (f : X.unop ⟶ Y) : dsimp% (ulif
tYonedaMap.{w} F Y).app X (ULift.up f) = ULift.up (F.map f)
参数：f : X.unop ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma uliftYonedaMap_app_apply {Y : C} {X : Cᵒᵖ} (f : X.unop ⟶ Y) :
    dsimp% (uliftYonedaMap.{w} F Y).app X (ULift.up f) = ULift.up (F.map f) := rfl

end

section

variable {C : Type u₁} [Category.{v₁} C]

set_option backward.isDefEq.respectTransparency.types false in
/-- A type-level equivalence between sections of a functor and morphisms from a terminal functor
to it. We use the constant functor on a given singleton type here as a specific choice of terminal
functor. -/
@[simps apply_app]
/-
**CategoryTheory.Functor.sectionsEquivHom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Functor`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     (F : C
ategoryTheory.Functor C (Type u₂)) →       (X : Type u₂) → [Unique X] → ↑F.secti
ons ≃ ((CategoryTheory.Functor.const C).obj X ⟶ F)
参数：F : CategoryTheory.Functor C (Type u₂)；X : Type u₂；(CategoryTheory.Functor.co
nst C).obj X ⟶ F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type-level equivalence between sections of a functor and morphisms from a term
inal functor
to it. We use the constant functor on a given singleton type here as a specific 
choice of terminal
functor.
-/
def Functor.sectionsEquivHom (F : C ⥤ Type u₂) (X : Type u₂) [Unique X] :
    F.sections ≃ ((const _).obj X ⟶ F) where
  toFun s :=
    { app j := ↾fun _ ↦ s.1 j
      naturality _ _ _ := by ext x; simp }
  invFun τ := by
    refine ⟨fun j ↦ τ.app _ (default : X), fun φ ↦ ?_⟩
    simp [-const_obj_obj, ← comp_apply, -types_comp_apply, ← NatTrans.naturality]
    rfl
  right_inv τ := by
    ext _ (x : X)
    rw [Unique.eq_default x]
    rfl
/-
**CategoryTheory.Functor.sectionsEquivHom_naturality** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Functor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {F G : Categor
yTheory.Functor C (Type u₂)} (f : F ⟶ G)   (X : Type u₂) [inst_1 : Unique X] (x 
: ↑F.sections),   (G.sectionsEquivHom X) ((CategoryTheory.ConcreteCategory.hom (
(CategoryTheory.Functor.sectionsFunctor C).map f)) x) =     CategoryTheory.Categ
oryStruct.comp ((F.sectionsEquivHom X) x) f
参数：Type u₂；f : F ⟶ G；X : Type u₂；x : ↑F.sections；G.sectionsEquivHom X；(CategoryT
heory.ConcreteCategory.hom ((CategoryTheory.Functor.sectionsFunctor C).map f)) x
；(F.sectionsEquivHom X) x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Functor.sectionsEquivHom_naturality {F G : C ⥤ Type u₂} (f : F ⟶ G) (X : Type u₂)
    [Unique X] (x : F.sections) :
    (G.sectionsEquivHom X) ((sectionsFunctor C).map f x) = (F.sectionsEquivHom X) x ≫ f := by
  rfl
/-
**CategoryTheory.Functor.sectionsEquivHom_naturality_symm** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Functor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {F G : Categor
yTheory.Functor C (Type u₂)} (f : F ⟶ G)   (X : Type u₂) [inst_1 : Unique X] (τ 
: (CategoryTheory.Functor.const C).obj X ⟶ F),   (G.sectionsEquivHom X).symm (Ca
tegoryTheory.CategoryStruct.comp τ f) =     (CategoryTheory.ConcreteCategory.hom
 ((CategoryTheory.Functor.sectionsFunctor C).map f))       ((F.sectionsEquivHom 
X).symm τ)
参数：Type u₂；f : F ⟶ G；X : Type u₂；τ : (CategoryTheory.Functor.const C).obj X ⟶ F；
G.sectionsEquivHom X；CategoryTheory.CategoryStruct.comp τ f；CategoryTheory.Concr
eteCategory.hom ((CategoryTheory.Functor.sectionsFunctor C).map f)；(F.sectionsEq
uivHom X).symm τ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma Functor.sectionsEquivHom_naturality_symm {F G : C ⥤ Type u₂} (f : F ⟶ G)
    (X : Type u₂) [Unique X] (τ : (const C).obj X ⟶ F) :
    (G.sectionsEquivHom X).symm (τ ≫ f) =
      (sectionsFunctor C).map f ((F.sectionsEquivHom X).symm τ) := by
  rfl

/-- A natural isomorphism between the sections functor `(C ⥤ Type) ⥤ Type` and the co-Yoneda
embedding of a terminal functor, specifically a constant functor on a given singleton type `X`. -/
@[simps! +dsimpLhs]
/-
**CategoryTheory.sectionsFunctorNatIsoCoyoneda** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory`。
形式化陈述：sectionsFunctorNatIsoCoyoneda (X : Type (max u₁ u₂)) [Unique X] : Functor.
sectionsFunctor.{v₁, max u₁ u₂} C ≅ coyoneda.obj (op ((Functor.const C).obj X))
参数：X : Type (max u₁ u₂)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A natural isomorphism between the sections functor `(C ⥤ Type) ⥤ Type` and the c
o-Yoneda
embedding of a terminal functor, specifically a constant functor on a given sing
leton type `X`.
-/
noncomputable def sectionsFunctorNatIsoCoyoneda (X : Type (max u₁ u₂)) [Unique X] :
    Functor.sectionsFunctor.{v₁, max u₁ u₂} C ≅ coyoneda.obj (op ((Functor.const C).obj X)) :=
  NatIso.ofComponents fun F ↦ (F.sectionsEquivHom X).toIso

end

namespace Functor.FullyFaithful

variable {C : Type u₁} [Category.{v₁} C]

set_option backward.isDefEq.respectTransparency.types false in
/-- `FullyFaithful.homEquiv` as a natural isomorphism. -/
@[simps! hom_app inv_app]
/-
**CategoryTheory.Functor.FullyFaithful.homNatIso** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Functor.FullyFaithful`。
形式化陈述：homNatIso {D : Type u₂} [Category.{v₂} D] {F : C ⥤ D} (hF : F.FullyFaithfu
l) (X : C) : F.op ⋙ uliftYoneda.{v₁}.obj (F.obj X) ≅ uliftYoneda.{v₂}.obj X
参数：hF : F.FullyFaithful；X : C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`FullyFaithful.homEquiv` as a natural isomorphism.
-/
def homNatIso {D : Type u₂} [Category.{v₂} D] {F : C ⥤ D} (hF : F.FullyFaithful) (X : C) :
    F.op ⋙ uliftYoneda.{v₁}.obj (F.obj X) ≅ uliftYoneda.{v₂}.obj X :=
  NatIso.ofComponents
    (fun Y => Equiv.toIso (Equiv.ulift.trans <| hF.homEquiv.symm.trans Equiv.ulift.symm))
    (fun f => by ext; exact Equiv.ulift.injective (hF.map_injective (by simp)))

set_option backward.isDefEq.respectTransparency.types false in
/-- `FullyFaithful.homEquiv` as a natural isomorphism. -/
@[simps! +dsimpLhs]
/-
**CategoryTheory.Functor.FullyFaithful.compUliftYonedaCompWhiskeringLeft** 是 Mat
hlib 中的一个定义，位于命名空间 `CategoryTheory.Functor.FullyFaithful`。
形式化陈述：compUliftYonedaCompWhiskeringLeft {D : Type u₂} [Category.{v₂} D] {F : C ⥤
 D} (hF : F.FullyFaithful) : F ⋙ uliftYoneda.{v₁} ⋙ (whiskeringLeft _ _ _).obj F
.op ≅ uliftYoneda.{v₂}
参数：hF : F.FullyFaithful。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`FullyFaithful.homEquiv` as a natural isomorphism.
-/
def compUliftYonedaCompWhiskeringLeft {D : Type u₂} [Category.{v₂} D] {F : C ⥤ D}
    (hF : F.FullyFaithful) :
    F ⋙ uliftYoneda.{v₁} ⋙ (whiskeringLeft _ _ _).obj F.op ≅ uliftYoneda.{v₂} :=
  NatIso.ofComponents (fun X => hF.homNatIso _) fun f => by
    ext; exact Equiv.ulift.injective (hF.map_injective (by simp))

set_option backward.isDefEq.respectTransparency.types false in
/-- `FullyFaithful.homEquiv` as a natural isomorphism, using coyoneda. -/
@[simps! hom_app inv_app]
/-
**CategoryTheory.Functor.FullyFaithful.homNatIso'** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Functor.FullyFaithful`。
形式化陈述：homNatIso' {D : Type u₂} [Category.{v₂} D] {F : C ⥤ D} (hF : F.FullyFaithf
ul) (X : C) : F ⋙ uliftCoyoneda.{v₁}.obj (op (F.obj X)) ≅ uliftCoyoneda.{v₂}.obj
 (op X)
参数：hF : F.FullyFaithful；X : C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`FullyFaithful.homEquiv` as a natural isomorphism, using coyoneda.
-/
def homNatIso' {D : Type u₂} [Category.{v₂} D] {F : C ⥤ D} (hF : F.FullyFaithful) (X : C) :
    F ⋙ uliftCoyoneda.{v₁}.obj (op (F.obj X)) ≅ uliftCoyoneda.{v₂}.obj (op X) :=
  NatIso.ofComponents
    (fun Y => Equiv.toIso (Equiv.ulift.trans <| hF.homEquiv.symm.trans Equiv.ulift.symm))
    (fun f => by ext; exact Equiv.ulift.injective (hF.map_injective (by simp)))

set_option backward.isDefEq.respectTransparency.types false in
/-- `FullyFaithful.homEquiv` as a natural isomorphism, using coyoneda. -/
@[simps! +dsimpLhs]
/-
**CategoryTheory.Functor.FullyFaithful.compUliftCoyonedaCompWhiskeringLeft** 是 M
athlib 中的一个定义，位于命名空间 `CategoryTheory.Functor.FullyFaithful`。
形式化陈述：compUliftCoyonedaCompWhiskeringLeft {D : Type u₂} [Category.{v₂} D] {F : C
 ⥤ D} (hF : F.FullyFaithful) : F.op ⋙ uliftCoyoneda.{v₁} ⋙ (whiskeringLeft _ _ _
).obj F ≅ uliftCoyoneda.{v₂}
参数：hF : F.FullyFaithful。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`FullyFaithful.homEquiv` as a natural isomorphism, using coyoneda.
-/
def compUliftCoyonedaCompWhiskeringLeft {D : Type u₂} [Category.{v₂} D] {F : C ⥤ D}
    (hF : F.FullyFaithful) :
    F.op ⋙ uliftCoyoneda.{v₁} ⋙ (whiskeringLeft _ _ _).obj F ≅ uliftCoyoneda.{v₂} :=
  NatIso.ofComponents (fun X => hF.homNatIso' _)
    (fun f => by ext; exact Equiv.ulift.injective (hF.map_injective (by simp)))

end Functor.FullyFaithful

end CategoryTheory

