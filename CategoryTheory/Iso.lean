/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Baumann, Stephen Morgan, Kim Morrison, Floris van Doorn
-/
module

public import Mathlib.Tactic.CategoryTheory.Reassoc

/-!
# Isomorphisms

This file defines isomorphisms between objects of a category.

## Main definitions

- `structure Iso` : a bundled isomorphism between two objects of a category;
- `class IsIso` : an unbundled version of `Iso`;
  note that `IsIso f` is a `Prop`, and only asserts the existence of an inverse.
  Of course, this inverse is unique, so it doesn't cost us much to use choice to retrieve it.
- `inv f`, for the inverse of a morphism with `[IsIso f]`
- `asIso` : convert from `IsIso` to `Iso` (noncomputable);
- `of_iso` : convert from `Iso` to `IsIso`;
- standard operations on isomorphisms (composition, inverse etc)

## Notation

- `X ≅ Y` : same as `Iso X Y`;
- `α ≪≫ β` : composition of two isomorphisms; it is called `Iso.trans`

## Tags

category, category theory, isomorphism
-/

@[expose] public section

set_option mathlib.tactic.category.grind true

universe v u

-- morphism levels before object levels. See note [category theory universes].
namespace CategoryTheory

open Category

/-- An isomorphism (a.k.a. an invertible morphism) between two objects of a category.
The inverse morphism is bundled.

See also `CategoryTheory.Core` for the category with the same objects and isomorphisms playing
the role of morphisms. -/
@[stacks 0017, wikidata Q189112]
/-
**CategoryTheory.Iso** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory`。
形式化陈述：Iso {C : Type u} [Category.{v} C] (X Y : C) where /-- The forward directio
n of an isomorphism. -/ hom : X ⟶ Y /-- The backwards direction of an isomorphis
m. -/ inv : Y ⟶ X /-- Composition of the two directions of an isomorphism is the
 identity on the source. -/ hom_inv_id : hom ≫ inv = 𝟙 X
参数：X Y : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isomorphism (a.k.a. an invertible morphism) between two objects of a category
.
The inverse morphism is bundled.

See also `CategoryTheory.Core` for the category with the same objects and isomor
phisms playing
the role of morphisms.
-/
structure Iso {C : Type u} [Category.{v} C] (X Y : C) where
  /-- The forward direction of an isomorphism. -/
  hom : X ⟶ Y
  /-- The backwards direction of an isomorphism. -/
  inv : Y ⟶ X
  /-- Composition of the two directions of an isomorphism is the identity on the source. -/
  hom_inv_id : hom ≫ inv = 𝟙 X := by cat_disch
  /-- Composition of the two directions of an isomorphism in reverse order
  is the identity on the target. -/
  inv_hom_id : inv ≫ hom = 𝟙 Y := by cat_disch

attribute [to_dual existing inv] Iso.hom
attribute [to_dual self] Iso.mk Iso.casesOn

attribute [reassoc +to_dual (attr := simp), grind =] Iso.hom_inv_id Iso.inv_hom_id

/-- Notation for an isomorphism in a category. -/
infixr:10 " ≅ " => Iso -- type as \cong or \iso

variable {C : Type u} [Category.{v} C] {X Y Z : C}

namespace Iso

set_option linter.style.whitespace false in -- manual alignment is not recognised
set_option linter.existingAttributeWarning false in
@[ext, grind ext, to_dual ext_inv]
/-
**CategoryTheory.Iso.ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β :=
  suffices α.inv = β.inv by grind [Iso]
  calc
    α.inv = α.inv ≫ β.hom ≫ β.inv := by grind
    _     = β.inv                 := by grind

/-- Inverse isomorphism. -/
@[symm, implicit_reducible]
/-
**CategoryTheory.Iso.symm** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：symm (I : X ≅ Y) : Y ≅ X where hom
参数：I : X ≅ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Inverse isomorphism.
-/
def symm (I : X ≅ Y) : Y ≅ X where
  hom := I.inv
  inv := I.hom

@[to_dual (attr := simp, grind =) symm_inv]
/-
**CategoryTheory.Iso.symm_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：symm_hom (α : X ≅ Y) : α.symm.hom = α.inv
参数：α : X ≅ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_hom (α : X ≅ Y) : α.symm.hom = α.inv :=
  rfl

@[simp, grind =, to_dual self]
/-
**CategoryTheory.Iso.symm_mk** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：symm_mk {X Y : C} (hom : X ⟶ Y) (inv : Y ⟶ X) (hom_inv_id) (inv_hom_id) : 
Iso.symm { hom, inv, hom_inv_id
参数：hom : X ⟶ Y；inv : Y ⟶ X；hom_inv_id；inv_hom_id。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_mk {X Y : C} (hom : X ⟶ Y) (inv : Y ⟶ X) (hom_inv_id) (inv_hom_id) :
    Iso.symm { hom, inv, hom_inv_id := hom_inv_id, inv_hom_id := inv_hom_id } =
      { hom := inv, inv := hom, hom_inv_id := inv_hom_id, inv_hom_id := hom_inv_id } :=
  rfl

@[simp, grind =]
/-
**CategoryTheory.Iso.symm_symm_eq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Iso`
。
形式化陈述：symm_symm_eq {X Y : C} (α : X ≅ Y) : α.symm.symm = α
参数：α : X ≅ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_symm_eq {X Y : C} (α : X ≅ Y) : α.symm.symm = α := rfl
/-
**CategoryTheory.Iso.symm_bijective** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Is
o`。
形式化陈述：symm_bijective {X Y : C} : Function.Bijective (symm : (X ≅ Y) -> _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.bijective_iff_has_inverse`：bijective_iff_has_inverse : Bijectiv
e f ↔ exists g, LeftInverse g f ∧ RightInverse g f
· 使用定理 `CategoryTheory.Iso.symm_symm_eq`：symm_symm_eq {X Y : C} (α : X ≅ Y) : α.
symm.symm = α
-/
theorem symm_bijective {X Y : C} : Function.Bijective (symm : (X ≅ Y) → _) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm_eq, symm_symm_eq⟩

@[simp]
/-
**CategoryTheory.Iso.symm_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：symm_eq_iff {X Y : C} {α β : X ≅ Y} : α.symm = β.symm ↔ α = β
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `CategoryTheory.Iso.symm_bijective`：symm_bijective {X Y : C} : Function.B
ijective (symm : (X ≅ Y) -> _)
-/
theorem symm_eq_iff {X Y : C} {α β : X ≅ Y} : α.symm = β.symm ↔ α = β :=
  symm_bijective.injective.eq_iff
/-
**CategoryTheory.Iso.nonempty_iso_symm** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Iso`。
形式化陈述：nonempty_iso_symm (X Y : C) : Nonempty (X ≅ Y) ↔ Nonempty (Y ≅ X)
参数：X Y : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nonempty_iso_symm (X Y : C) : Nonempty (X ≅ Y) ↔ Nonempty (Y ≅ X) :=
  ⟨fun h => ⟨h.some.symm⟩, fun h => ⟨h.some.symm⟩⟩

/-- Identity isomorphism. -/
@[refl, simps (attr := grind =), implicit_reducible]
/-
**CategoryTheory.Iso.refl** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：refl (X : C) : X ≅ X where hom
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Identity isomorphism.
-/
def refl (X : C) : X ≅ X where
  hom := 𝟙 X
  inv := 𝟙 X

attribute [to_dual existing refl_inv] refl_hom
/-
**CategoryTheory.Iso.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Iso`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (X ≅ X) := ⟨Iso.refl X⟩
/-
**CategoryTheory.Iso.nonempty_iso_refl** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Iso`。
形式化陈述：nonempty_iso_refl (X : C) : Nonempty (X ≅ X)
参数：X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nonempty_iso_refl (X : C) : Nonempty (X ≅ X) := ⟨default⟩

@[simp, grind =]
/-
**CategoryTheory.Iso.refl_symm** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：refl_symm (X : C) : (Iso.refl X).symm = Iso.refl X
参数：X : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl_symm (X : C) : (Iso.refl X).symm = Iso.refl X := rfl

/-- Composition of two isomorphisms -/
@[simps (attr := grind =), implicit_reducible]
/-
**CategoryTheory.Iso.trans** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：trans (α : X ≅ Y) (β : Y ≅ Z) : X ≅ Z where hom
参数：α : X ≅ Y；β : Y ≅ Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of two isomorphisms
-/
def trans (α : X ≅ Y) (β : Y ≅ Z) : X ≅ Z where
  hom := α.hom ≫ β.hom
  inv := β.inv ≫ α.inv

attribute [to_dual existing trans_inv] trans_hom

@[simps]
/-
**CategoryTheory.Iso.instTransIso** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Iso`
。
形式化陈述：instTransIso : Trans (α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instTransIso : Trans (α := C) (· ≅ ·) (· ≅ ·) (· ≅ ·) where
  trans := trans

/-- Notation for composition of isomorphisms. -/
infixr:80 " ≪≫ " => Iso.trans -- type as `\ll \gg`.

-- Annotating this with `@[grind =]` triggers a run-away chain of `Category.assoc` instantiations.
-- Hopefully this can be restored when `grind` has support for associative/commutative operations,
-- or direct support for category theory.
@[simp, to_dual self]
/-
**CategoryTheory.Iso.trans_mk** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：trans_mk {X Y Z : C} (hom : X ⟶ Y) (inv : Y ⟶ X) (hom_inv_id) (inv_hom_id)
 (hom' : Y ⟶ Z) (inv' : Z ⟶ Y) (hom_inv_id') (inv_hom_id') (hom_inv_id'') (inv_h
om_id'') : Iso.trans ⟨hom, inv, hom_inv_id, inv_hom_id⟩ ⟨hom', inv', hom_inv_id'
, inv_hom_id'⟩ = ⟨hom ≫ hom', inv' ≫ inv, hom_inv_id'', inv_hom_id''⟩
参数：hom : X ⟶ Y；inv : Y ⟶ X；hom_inv_id；inv_hom_id；hom' : Y ⟶ Z；inv' : Z ⟶ Y；hom_i
nv_id'；inv_hom_id'；hom_inv_id''；inv_hom_id''。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans_mk {X Y Z : C} (hom : X ⟶ Y) (inv : Y ⟶ X) (hom_inv_id) (inv_hom_id)
    (hom' : Y ⟶ Z) (inv' : Z ⟶ Y) (hom_inv_id') (inv_hom_id') (hom_inv_id'') (inv_hom_id'') :
    Iso.trans ⟨hom, inv, hom_inv_id, inv_hom_id⟩ ⟨hom', inv', hom_inv_id', inv_hom_id'⟩ =
     ⟨hom ≫ hom', inv' ≫ inv, hom_inv_id'', inv_hom_id''⟩ :=
  rfl

@[simp, grind _=_]
/-
**CategoryTheory.Iso.trans_symm** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：trans_symm (α : X ≅ Y) (β : Y ≅ Z) : (α ≪≫ β).symm = β.symm ≪≫ α.symm
参数：α : X ≅ Y；β : Y ≅ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans_symm (α : X ≅ Y) (β : Y ≅ Z) : (α ≪≫ β).symm = β.symm ≪≫ α.symm :=
  rfl

@[simp, grind _=_]
/-
**CategoryTheory.Iso.trans_assoc** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：trans_assoc {Z' : C} (α : X ≅ Y) (β : Y ≅ Z) (γ : Z ≅ Z') : (α ≪≫ β) ≪≫ γ 
= α ≪≫ β ≪≫ γ
参数：α : X ≅ Y；β : Y ≅ Z；γ : Z ≅ Z'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem trans_assoc {Z' : C} (α : X ≅ Y) (β : Y ≅ Z) (γ : Z ≅ Z') :
    (α ≪≫ β) ≪≫ γ = α ≪≫ β ≪≫ γ := by
  ext; simp only [trans_hom, Category.assoc]

@[simp]
/-
**CategoryTheory.Iso.refl_trans** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：refl_trans (α : X ≅ Y) : Iso.refl X ≪≫ α = α
参数：α : X ≅ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
theorem refl_trans (α : X ≅ Y) : Iso.refl X ≪≫ α = α := by ext; apply Category.id_comp

@[simp]
/-
**CategoryTheory.Iso.trans_refl** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：trans_refl (α : X ≅ Y) : α ≪≫ Iso.refl Y = α
参数：α : X ≅ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
theorem trans_refl (α : X ≅ Y) : α ≪≫ Iso.refl Y = α := by ext; apply Category.comp_id

@[simp]
/-
**CategoryTheory.Iso.symm_self_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Iso`
。
形式化陈述：symm_self_id (α : X ≅ Y) : α.symm ≪≫ α = Iso.refl Y
参数：α : X ≅ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
-/
theorem symm_self_id (α : X ≅ Y) : α.symm ≪≫ α = Iso.refl Y :=
  ext α.inv_hom_id

@[simp]
/-
**CategoryTheory.Iso.self_symm_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Iso`
。
形式化陈述：self_symm_id (α : X ≅ Y) : α ≪≫ α.symm = Iso.refl X
参数：α : X ≅ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
-/
theorem self_symm_id (α : X ≅ Y) : α ≪≫ α.symm = Iso.refl X :=
  ext α.hom_inv_id

@[simp]
/-
**CategoryTheory.Iso.symm_self_id_assoc** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Iso`。
形式化陈述：symm_self_id_assoc (α : X ≅ Y) (β : Y ≅ Z) : α.symm ≪≫ α ≪≫ β = β
参数：α : X ≅ Y；β : Y ≅ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Iso.trans_assoc`：trans_assoc {Z' : C} (α : X ≅ Y) (β : Y 
≅ Z) (γ : Z ≅ Z') : (α ≪≫ β) ≪≫ γ = α ≪≫ β ≪≫ γ
· 使用定理 `CategoryTheory.Iso.symm_self_id`：symm_self_id (α : X ≅ Y) : α.symm ≪≫ α 
= Iso.refl Y
· 使用定理 `CategoryTheory.Iso.refl_trans`：refl_trans (α : X ≅ Y) : Iso.refl X ≪≫ α 
= α
-/
theorem symm_self_id_assoc (α : X ≅ Y) (β : Y ≅ Z) : α.symm ≪≫ α ≪≫ β = β := by
  rw [← trans_assoc, symm_self_id, refl_trans]

@[simp]
/-
**CategoryTheory.Iso.self_symm_id_assoc** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Iso`。
形式化陈述：self_symm_id_assoc (α : X ≅ Y) (β : X ≅ Z) : α ≪≫ α.symm ≪≫ β = β
参数：α : X ≅ Y；β : X ≅ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Iso.trans_assoc`：trans_assoc {Z' : C} (α : X ≅ Y) (β : Y 
≅ Z) (γ : Z ≅ Z') : (α ≪≫ β) ≪≫ γ = α ≪≫ β ≪≫ γ
· 使用定理 `CategoryTheory.Iso.self_symm_id`：self_symm_id (α : X ≅ Y) : α ≪≫ α.symm 
= Iso.refl X
· 使用定理 `CategoryTheory.Iso.refl_trans`：refl_trans (α : X ≅ Y) : Iso.refl X ≪≫ α 
= α
-/
theorem self_symm_id_assoc (α : X ≅ Y) (β : X ≅ Z) : α ≪≫ α.symm ≪≫ β = β := by
  rw [← trans_assoc, self_symm_id, refl_trans]

@[to_dual none]
/-
**CategoryTheory.Iso.inv_comp_eq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：inv_comp_eq (α : X ≅ Y) {f : X ⟶ Z} {g : Y ⟶ Z} : α.inv ≫ f = g ↔ f = α.ho
m ≫ g
参数：α : X ≅ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
-/
theorem inv_comp_eq (α : X ≅ Y) {f : X ⟶ Z} {g : Y ⟶ Z} : α.inv ≫ f = g ↔ f = α.hom ≫ g :=
  ⟨fun H => by simp [H.symm], fun H => by simp [H]⟩

@[to_dual none]
/-
**CategoryTheory.Iso.eq_inv_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：eq_inv_comp (α : X ≅ Y) {f : X ⟶ Z} {g : Y ⟶ Z} : g = α.inv ≫ f ↔ α.hom ≫ 
g = f
参数：α : X ≅ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `CategoryTheory.Iso.inv_comp_eq`：inv_comp_eq (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : α.inv ≫ f = g ↔ f = α.hom ≫ g
-/
theorem eq_inv_comp (α : X ≅ Y) {f : X ⟶ Z} {g : Y ⟶ Z} : g = α.inv ≫ f ↔ α.hom ≫ g = f :=
  (inv_comp_eq α.symm).symm

@[to_dual none]
/-
**CategoryTheory.Iso.comp_inv_eq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：comp_inv_eq (α : X ≅ Y) {f : Z ⟶ Y} {g : Z ⟶ X} : f ≫ α.inv = g ↔ f = g ≫ 
α.hom
参数：α : X ≅ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
-/
theorem comp_inv_eq (α : X ≅ Y) {f : Z ⟶ Y} {g : Z ⟶ X} : f ≫ α.inv = g ↔ f = g ≫ α.hom :=
  ⟨fun H => by simp [H.symm], fun H => by simp [H]⟩

@[to_dual none]
/-
**CategoryTheory.Iso.eq_comp_inv** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：eq_comp_inv (α : X ≅ Y) {f : Z ⟶ Y} {g : Z ⟶ X} : g = f ≫ α.inv ↔ g ≫ α.ho
m = f
参数：α : X ≅ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `CategoryTheory.Iso.comp_inv_eq`：comp_inv_eq (α : X ≅ Y) {f : Z ⟶ Y} {g :
 Z ⟶ X} : f ≫ α.inv = g ↔ f = g ≫ α.hom
-/
theorem eq_comp_inv (α : X ≅ Y) {f : Z ⟶ Y} {g : Z ⟶ X} : g = f ≫ α.inv ↔ g ≫ α.hom = f :=
  (comp_inv_eq α.symm).symm

@[to_dual none]
/-
**CategoryTheory.Iso.inv_eq_inv** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：inv_eq_inv (f g : X ≅ Y) : f.inv = g.inv ↔ f.hom = g.hom
参数：f g : X ≅ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
-/
theorem inv_eq_inv (f g : X ≅ Y) : f.inv = g.inv ↔ f.hom = g.hom :=
  have : ∀ {X Y : C} (f g : X ≅ Y), f.hom = g.hom → f.inv = g.inv := fun f g h => by rw [ext h]
  ⟨this f.symm g.symm, this f g⟩

@[to_dual comp_inv_eq_id]
/-
**CategoryTheory.Iso.hom_comp_eq_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Is
o`。
形式化陈述：hom_comp_eq_id (α : X ≅ Y) {f : Y ⟶ X} : α.hom ≫ f = 𝟙 X ↔ f = α.inv
参数：α : X ≅ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Iso.eq_inv_comp`：eq_inv_comp (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : g = α.inv ≫ f ↔ α.hom ≫ g = f
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem hom_comp_eq_id (α : X ≅ Y) {f : Y ⟶ X} : α.hom ≫ f = 𝟙 X ↔ f = α.inv := by
  rw [← eq_inv_comp, comp_id]

@[to_dual inv_comp_eq_id]
/-
**CategoryTheory.Iso.comp_hom_eq_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Is
o`。
形式化陈述：comp_hom_eq_id (α : X ≅ Y) {f : Y ⟶ X} : f ≫ α.hom = 𝟙 Y ↔ f = α.inv
参数：α : X ≅ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Iso.eq_comp_inv`：eq_comp_inv (α : X ≅ Y) {f : Z ⟶ Y} {g :
 Z ⟶ X} : g = f ≫ α.inv ↔ g ≫ α.hom = f
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem comp_hom_eq_id (α : X ≅ Y) {f : Y ⟶ X} : f ≫ α.hom = 𝟙 Y ↔ f = α.inv := by
  rw [← eq_comp_inv, id_comp]

@[to_dual inv_eq_hom]
/-
**CategoryTheory.Iso.hom_eq_inv** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：hom_eq_inv (α : X ≅ Y) (β : Y ≅ X) : α.hom = β.inv ↔ β.hom = α.inv
参数：α : X ≅ Y；β : Y ≅ X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Iso.symm_inv`：∀ {C : Type u} [inst : CategoryTheory.Categ
ory.{v, u} C] {X Y : C} (α : X ≅ Y), α.symm.inv = α.hom
· 使用定理 `CategoryTheory.Iso.inv_eq_inv`：inv_eq_inv (f g : X ≅ Y) : f.inv = g.inv 
↔ f.hom = g.hom
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem hom_eq_inv (α : X ≅ Y) (β : Y ≅ X) : α.hom = β.inv ↔ β.hom = α.inv := by
  rw [← symm_inv, inv_eq_inv α.symm β, eq_comm]
  rfl

attribute [local grind] Function.LeftInverse Function.RightInverse

/-- The bijection `(Z ⟶ X) ≃ (Z ⟶ Y)` induced by `α : X ≅ Y`. -/
@[implicit_reducible, to_dual (attr := simps) homFromEquiv
/-- The bijection `(X ⟶ Z) ≃ (Y ⟶ Z)` induced by `α : X ≅ Y`. -/]
/-
**CategoryTheory.Iso.homToEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：homToEquiv (α : X ≅ Y) {Z : C} : (Z ⟶ X) ≃ (Z ⟶ Y) where toFun f
参数：α : X ≅ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def homToEquiv (α : X ≅ Y) {Z : C} : (Z ⟶ X) ≃ (Z ⟶ Y) where
  toFun f := f ≫ α.hom
  invFun g := g ≫ α.inv
  left_inv := by cat_disch
  right_inv := by cat_disch

end Iso

set_option linter.translate.warnInvalid false in
/-- The `IsIso` typeclass expresses that a morphism is invertible.

Given a morphism `f` with `IsIso f`, one can view `f` as an isomorphism via `asIso f` and get
the inverse using `inv f`. -/
@[to_dual self]
/-
**CategoryTheory.IsIso** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → {X Y : C} → (X 
⟶ Y) → Prop
参数：X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `IsIso` typeclass expresses that a morphism is invertible.

Given a morphism `f` with `IsIso f`, one can view `f` as an isomorphism via `asI
so f` and get
the inverse using `inv f`.
-/
class IsIso (f : X ⟶ Y) : Prop where
  /-- The existence of an inverse morphism. -/
  out : ∃ inv : Y ⟶ X, f ≫ inv = 𝟙 X ∧ inv ≫ f = 𝟙 Y

/-- `IsIso.mk'` is the dual of `IsIso.mk`, which we need for `to_dual`.
Please avoid using this directly. -/
@[to_dual existing mk]
/-
**CategoryTheory.IsIso.mk'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsIso`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} {f : Y 
⟶ X},   (∃ inv,       CategoryTheory.CategoryStruct.comp inv f = CategoryTheory.
CategoryStruct.id X ∧         CategoryTheory.CategoryStruct.comp f inv = Categor
yTheory.CategoryStruct.id Y) →     CategoryTheory.IsIso f
参数：∃ inv,       CategoryTheory.CategoryStruct.comp inv f = CategoryTheory.Catego
ryStruct.id X ∧         CategoryTheory.CategoryStruct.comp f inv = CategoryTheor
y.CategoryStruct.id Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True

--- 原说明 ---
`IsIso.mk'` is the dual of `IsIso.mk`, which we need for `to_dual`.
Please avoid using this directly.
-/
theorem IsIso.mk' {f : Y ⟶ X} (out : ∃ inv : X ⟶ Y, inv ≫ f = 𝟙 X ∧ f ≫ inv = 𝟙 Y) : IsIso f where
  out := by simp_all only [and_comm]

/-- The inverse of a morphism `f` when we have `[IsIso f]`. -/
@[to_dual self, no_expose]
/-
**CategoryTheory.inv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：inv (f : X ⟶ Y) [I : IsIso f] : Y ⟶ X
参数：f : X ⟶ Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsIso.out`：∀ {C : Type u} {inst : CategoryTheory.Category
.{v, u} C} {X Y : C} {f : X ⟶ Y} [self : CategoryTheory.IsIso f],   ∃ inv,     C
ategoryTheory.…

--- 原说明 ---
The inverse of a morphism `f` when we have `[IsIso f]`.
-/
noncomputable def inv (f : X ⟶ Y) [I : IsIso f] : Y ⟶ X :=
  Classical.choose I.1

namespace IsIso

/-
**CategoryTheory.IsIso.hom_inv_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsIs
o`。
形式化陈述：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : f ≫ inv f = 𝟙 X
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `CategoryTheory.IsIso.out`：∀ {C : Type u} {inst : CategoryTheory.Category
.{v, u} C} {X Y : C} {f : X ⟶ Y} [self : CategoryTheory.IsIso f],   ∃ inv,     C
ategoryTheory.…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem hom_inv_id (f : X ⟶ Y) [I : IsIso f] : f ≫ inv f = 𝟙 X :=
  (Classical.choose_spec I.1).left

@[to_dual existing (attr := reassoc (attr := simp), grind =) hom_inv_id]
/-
**CategoryTheory.IsIso.inv_hom_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsIs
o`。
形式化陈述：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : inv f ≫ f = 𝟙 Y
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `CategoryTheory.IsIso.out`：∀ {C : Type u} {inst : CategoryTheory.Category
.{v, u} C} {X Y : C} {f : X ⟶ Y} [self : CategoryTheory.IsIso f],   ∃ inv,     C
ategoryTheory.…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem inv_hom_id (f : X ⟶ Y) [I : IsIso f] : inv f ≫ f = 𝟙 Y :=
  (Classical.choose_spec I.1).right

end IsIso

/-
**CategoryTheory.Iso.isIso_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} (e : X 
≅ Y), CategoryTheory.IsIso e.hom
参数：e : X ≅ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
-/
instance Iso.isIso_hom (e : X ≅ Y) : IsIso e.hom :=
  ⟨e.inv, by simp only [hom_inv_id], by simp⟩

@[to_dual existing isIso_hom]
/-
**CategoryTheory.Iso.isIso_inv** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} (e : X 
≅ Y), CategoryTheory.IsIso e.inv
参数：e : X ≅ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
instance Iso.isIso_inv (e : X ≅ Y) : IsIso e.inv := e.symm.isIso_hom

open IsIso

/-- Reinterpret a morphism `f : X ⟶ Y` with an `IsIso f` instance as `X ≅ Y`. -/
@[to_dual asIso' /-- Reinterpret a morphism `f : X ⟶ Y` with an `IsIso f` instance as `Y ≅ X`. -/]
/-
**CategoryTheory.asIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：asIso (f : X ⟶ Y) [IsIso f] : X ≅ Y
参数：f : X ⟶ Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y

--- 原说明 ---
Reinterpret a morphism `f : X ⟶ Y` with an `IsIso f` instance as `X ≅ Y`.
-/
noncomputable def asIso (f : X ⟶ Y) [IsIso f] : X ≅ Y :=
  ⟨f, inv f, hom_inv_id f, inv_hom_id f⟩

@[to_dual (attr := simp) asIso'_hom]
/-
**CategoryTheory.asIso_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：asIso_hom (f : X ⟶ Y) [IsIso f] : (asIso f).hom = f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem asIso_hom (f : X ⟶ Y) [IsIso f] : (asIso f).hom = f :=
  rfl

@[to_dual (attr := simp) asIso'_inv]
/-
**CategoryTheory.asIso_inv** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：asIso_inv (f : X ⟶ Y) [IsIso f] : (asIso f).inv = inv f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem asIso_inv (f : X ⟶ Y) [IsIso f] : (asIso f).inv = inv f :=
  rfl

namespace IsIso

-- see Note [lower instance priority]
@[to_dual]
/-
**CategoryTheory.IsIso.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.IsIso`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) epi_of_iso (f : X ⟶ Y) [IsIso f] : Epi f where
  left_cancellation g h w := by
    rw [← IsIso.inv_hom_id_assoc f g, w, IsIso.inv_hom_id_assoc f h]

@[aesop apply safe (rule_sets := [CategoryTheory]), grind ←=, to_dual inv_eq_of_inv_hom_id]
/-
**CategoryTheory.IsIso.inv_eq_of_hom_inv_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.IsIso`。
形式化陈述：inv_eq_of_hom_inv_id {f : X ⟶ Y} [IsIso f] {g : Y ⟶ X} (hom_inv_id : f ≫ g
 = 𝟙 X) : inv f = g
参数：hom_inv_id : f ≫ g = 𝟙 X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem inv_eq_of_hom_inv_id {f : X ⟶ Y} [IsIso f] {g : Y ⟶ X} (hom_inv_id : f ≫ g = 𝟙 X) :
    inv f = g := by
  have := congrArg (inv f ≫ ·) hom_inv_id
  grind

@[aesop apply safe (rule_sets := [CategoryTheory]), to_dual eq_inv_of_inv_hom_id]
/-
**CategoryTheory.IsIso.eq_inv_of_hom_inv_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.IsIso`。
形式化陈述：eq_inv_of_hom_inv_id {f : X ⟶ Y} [IsIso f] {g : Y ⟶ X} (hom_inv_id : f ≫ g
 = 𝟙 X) : g = inv f
参数：hom_inv_id : f ≫ g = 𝟙 X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.IsIso.inv_eq_of_hom_inv_id`：inv_eq_of_hom_inv_id {f : X ⟶
 Y} [IsIso f] {g : Y ⟶ X} (hom_inv_id : f ≫ g = 𝟙 X) : inv f = g
-/
theorem eq_inv_of_hom_inv_id {f : X ⟶ Y} [IsIso f] {g : Y ⟶ X} (hom_inv_id : f ≫ g = 𝟙 X) :
    g = inv f :=
  (inv_eq_of_hom_inv_id hom_inv_id).symm
/-
**CategoryTheory.IsIso.id** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.IsIso`。
形式化陈述：id (X : C) : IsIso (𝟙 X)
参数：X : C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
instance id (X : C) : IsIso (𝟙 X) := ⟨⟨𝟙 X, by simp⟩⟩

variable {f : X ⟶ Y} {h : Y ⟶ Z}

@[to_dual self]
/-
**CategoryTheory.IsIso.inv_isIso** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.IsIso
`。
形式化陈述：inv_isIso [IsIso f] : IsIso (inv f)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
-/
instance inv_isIso [IsIso f] : IsIso (inv f) :=
  (asIso f).isIso_inv

@[to_dual self (reorder := X Z, f h, 8 9)]
/-
**CategoryTheory.IsIso.comp_isIso** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.IsIs
o`。
形式化陈述：comp_isIso [IsIso f] [IsIso h] : IsIso (f ≫ h)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
instance comp_isIso [IsIso f] [IsIso h] : IsIso (f ≫ h) :=
  (asIso f ≪≫ asIso h).isIso_hom

/--
The composition of isomorphisms is an isomorphism. Here the arguments of type `IsIso` are
explicit, to make this easier to use with the `refine` tactic, for instance.
-/
@[to_dual self (reorder := X Z, f h, 8 9)]
/-
**CategoryTheory.IsIso.comp_isIso'** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.IsI
so`。
形式化陈述：comp_isIso' (_ : IsIso f) (_ : IsIso h) : IsIso (f ≫ h)
参数：_ : IsIso f；_ : IsIso h。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of isomorphisms is an isomorphism. Here the arguments of type `I
sIso` are
explicit, to make this easier to use with the `refine` tactic, for instance.
-/
lemma comp_isIso' (_ : IsIso f) (_ : IsIso h) : IsIso (f ≫ h) := inferInstance

@[simp]
/-
**CategoryTheory.IsIso.inv_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsIso`。
形式化陈述：inv_id : inv (𝟙 X) = 𝟙 X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsIso.inv_eq_of_hom_inv_id`：inv_eq_of_hom_inv_id {f : X ⟶
 Y} [IsIso f] {g : Y ⟶ X} (hom_inv_id : f ≫ g = 𝟙 X) : inv f = g
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
theorem inv_id : inv (𝟙 X) = 𝟙 X := by
  apply inv_eq_of_hom_inv_id
  simp

@[simp, reassoc, push, to_dual self]
/-
**CategoryTheory.IsIso.inv_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsIso`
。
形式化陈述：inv_comp [IsIso f] [IsIso h] : inv (f ≫ h) = inv h ≫ inv f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsIso.inv_eq_of_hom_inv_id`：inv_eq_of_hom_inv_id {f : X ⟶
 Y} [IsIso f] {g : Y ⟶ X} (hom_inv_id : f ≫ g = 𝟙 X) : inv f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.IsIso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : X ⟶ Z), CategoryT…
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inv_comp [IsIso f] [IsIso h] : inv (f ≫ h) = inv h ≫ inv f := by
  apply inv_eq_of_hom_inv_id
  simp

@[simp, push, to_dual self]
/-
**CategoryTheory.IsIso.inv_inv** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsIso`。
形式化陈述：inv_inv [IsIso f] : inv (inv f) = f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsIso.inv_eq_of_hom_inv_id`：inv_eq_of_hom_inv_id {f : X ⟶
 Y} [IsIso f] {g : Y ⟶ X} (hom_inv_id : f ≫ g = 𝟙 X) : inv f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inv_inv [IsIso f] : inv (inv f) = f := by
  apply inv_eq_of_hom_inv_id
  simp

@[to_dual (attr := simp, push) inv_hom]
/-
**CategoryTheory.IsIso.Iso.inv_inv** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsI
so.Iso`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} (f : X 
≅ Y), CategoryTheory.inv f.inv = f.hom
参数：f : X ≅ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsIso.inv_eq_of_hom_inv_id`：inv_eq_of_hom_inv_id {f : X ⟶
 Y} [IsIso f] {g : Y ⟶ X} (hom_inv_id : f ≫ g = 𝟙 X) : inv f = g
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Iso.inv_inv (f : X ≅ Y) : inv f.inv = f.hom := by
  apply inv_eq_of_hom_inv_id
  simp

@[to_dual (attr := simp) comp_inv_eq]
/-
**CategoryTheory.IsIso.inv_comp_eq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsI
so`。
形式化陈述：inv_comp_eq (α : X ⟶ Y) [IsIso α] {f : X ⟶ Z} {g : Y ⟶ Z} : inv α ≫ f = g 
↔ f = α ≫ g
参数：α : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.inv_comp_eq`：inv_comp_eq (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : α.inv ≫ f = g ↔ f = α.hom ≫ g
-/
theorem inv_comp_eq (α : X ⟶ Y) [IsIso α] {f : X ⟶ Z} {g : Y ⟶ Z} : inv α ≫ f = g ↔ f = α ≫ g :=
  (asIso α).inv_comp_eq

@[to_dual (attr := simp) eq_comp_inv]
/-
**CategoryTheory.IsIso.eq_inv_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsI
so`。
形式化陈述：eq_inv_comp (α : X ⟶ Y) [IsIso α] {f : X ⟶ Z} {g : Y ⟶ Z} : g = inv α ≫ f 
↔ α ≫ g = f
参数：α : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.eq_inv_comp`：eq_inv_comp (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : g = α.inv ≫ f ↔ α.hom ≫ g = f
-/
theorem eq_inv_comp (α : X ⟶ Y) [IsIso α] {f : X ⟶ Z} {g : Y ⟶ Z} : g = inv α ≫ f ↔ α ≫ g = f :=
  (asIso α).eq_inv_comp

@[to_dual (reorder := f g) of_isIso_comp_right]
/-
**CategoryTheory.IsIso.of_isIso_comp_left** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.IsIso`。
形式化陈述：of_isIso_comp_left {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] [IsIso (f
 ≫ g)] : IsIso g
参数：f : X ⟶ Y；g : Y ⟶ Z；f ≫ g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
-/
theorem of_isIso_comp_left {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] [IsIso (f ≫ g)] :
    IsIso g := by
  rw [← id_comp g, ← inv_hom_id f, assoc]
  infer_instance

@[to_dual of_isIso_fac_right]
/-
**CategoryTheory.IsIso.of_isIso_fac_left** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.IsIso`。
形式化陈述：of_isIso_fac_left {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} [IsIso f
] [hh : IsIso h] (w : f ≫ g = h) : IsIso g
参数：w : f ≫ g = h。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsIso.of_isIso_comp_left`：of_isIso_comp_left {X Y Z : C} 
(f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] [IsIso (f ≫ g)] : IsIso g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem of_isIso_fac_left {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} [IsIso f]
    [hh : IsIso h] (w : f ≫ g = h) : IsIso g := by
  rw [← w] at hh
  exact of_isIso_comp_left f g

end IsIso

@[to_dual (attr := simp) (reorder := f g) isIso_comp_right_iff]
/-
**CategoryTheory.isIso_comp_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：isIso_comp_left_iff {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] : IsIso 
(f ≫ g) ↔ IsIso g
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsIso.of_isIso_comp_left`：of_isIso_comp_left {X Y Z : C} 
(f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] [IsIso (f ≫ g)] : IsIso g
-/
theorem isIso_comp_left_iff {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] :
    IsIso (f ≫ g) ↔ IsIso g :=
  ⟨fun _ ↦ IsIso.of_isIso_comp_left f g, fun _ ↦ inferInstance⟩

open IsIso

@[to_dual self]
/-
**CategoryTheory.eq_of_inv_eq_inv** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：eq_of_inv_eq_inv {f g : X ⟶ Y} [IsIso f] [IsIso g] (p : inv f = inv g) : f
 = g
参数：p : inv f = inv g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.IsIso.epi_of_iso`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],   CategoryTheo
ry.Epi f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
-/
theorem eq_of_inv_eq_inv {f g : X ⟶ Y} [IsIso f] [IsIso g] (p : inv f = inv g) : f = g := by
  apply (cancel_epi (inv f)).1
  rw [inv_hom_id, p, inv_hom_id]

@[to_dual self]
/-
**CategoryTheory.IsIso.inv_eq_inv** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsIs
o`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} {f g : 
X ⟶ Y} [inst_1 : CategoryTheory.IsIso f]   [inst_2 : CategoryTheory.IsIso g], Ca
tegoryTheory.inv f = CategoryTheory.inv g ↔ f = g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.inv_eq_inv`：inv_eq_inv (f g : X ≅ Y) : f.inv = g.inv 
↔ f.hom = g.hom
-/
theorem IsIso.inv_eq_inv {f g : X ⟶ Y} [IsIso f] [IsIso g] : inv f = inv g ↔ f = g :=
  Iso.inv_eq_inv (asIso f) (asIso g)

@[to_dual comp_hom_eq_id]
/-
**CategoryTheory.hom_comp_eq_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：hom_comp_eq_id (g : X ⟶ Y) [IsIso g] {f : Y ⟶ X} : g ≫ f = 𝟙 X ↔ f = inv g
参数：g : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.hom_comp_eq_id`：hom_comp_eq_id (α : X ≅ Y) {f : Y ⟶ X
} : α.hom ≫ f = 𝟙 X ↔ f = α.inv
-/
theorem hom_comp_eq_id (g : X ⟶ Y) [IsIso g] {f : Y ⟶ X} : g ≫ f = 𝟙 X ↔ f = inv g :=
  (asIso g).hom_comp_eq_id

@[to_dual comp_inv_eq_id]
/-
**CategoryTheory.inv_comp_eq_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：inv_comp_eq_id (g : X ⟶ Y) [IsIso g] {f : X ⟶ Y} : inv g ≫ f = 𝟙 Y ↔ f = g
参数：g : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.inv_comp_eq_id`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {X Y : C} (α : X ≅ Y) {f : X ⟶ Y},   CategoryTheory.Category
Struct.comp α.inv f = C…
-/
theorem inv_comp_eq_id (g : X ⟶ Y) [IsIso g] {f : X ⟶ Y} : inv g ≫ f = 𝟙 Y ↔ f = g :=
  (asIso g).inv_comp_eq_id

@[to_dual isIso_of_comp_hom_eq_id]
/-
**CategoryTheory.isIso_of_hom_comp_eq_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry`。
形式化陈述：isIso_of_hom_comp_eq_id (g : X ⟶ Y) [IsIso g] {f : Y ⟶ X} (h : g ≫ f = 𝟙 X
) : IsIso f
参数：g : X ⟶ Y；h : g ≫ f = 𝟙 X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.hom_comp_eq_id`：hom_comp_eq_id (g : X ⟶ Y) [IsIso g] {f :
 Y ⟶ X} : g ≫ f = 𝟙 X ↔ f = inv g
-/
theorem isIso_of_hom_comp_eq_id (g : X ⟶ Y) [IsIso g] {f : Y ⟶ X} (h : g ≫ f = 𝟙 X) : IsIso f := by
  rw [(hom_comp_eq_id _).mp h]
  infer_instance
/-
**CategoryTheory.isIso_iff_of_thin** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：isIso_iff_of_thin [Quiver.IsThin C] {X Y : C} (f : X ⟶ Y) : IsIso f ↔ None
mpty (Y ⟶ X)
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
lemma isIso_iff_of_thin [Quiver.IsThin C] {X Y : C} (f : X ⟶ Y) : IsIso f ↔ Nonempty (Y ⟶ X) :=
  ⟨fun _ ↦ ⟨inv f⟩, fun g ↦ ⟨g.some, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩

namespace Iso

@[aesop apply safe (rule_sets := [CategoryTheory]), to_dual none]
/-
**CategoryTheory.Iso.inv_ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：inv_ext {f : X ≅ Y} {g : Y ⟶ X} (hom_inv_id : f.hom ≫ g = 𝟙 X) : f.inv = g
参数：hom_inv_id : f.hom ≫ g = 𝟙 X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Iso.hom_comp_eq_id`：hom_comp_eq_id (α : X ≅ Y) {f : Y ⟶ X
} : α.hom ≫ f = 𝟙 X ↔ f = α.inv
-/
theorem inv_ext {f : X ≅ Y} {g : Y ⟶ X} (hom_inv_id : f.hom ≫ g = 𝟙 X) : f.inv = g :=
  ((hom_comp_eq_id f).1 hom_inv_id).symm

@[aesop apply safe (rule_sets := [CategoryTheory]), to_dual none]
/-
**CategoryTheory.Iso.inv_ext'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：inv_ext' {f : X ≅ Y} {g : Y ⟶ X} (hom_inv_id : f.hom ≫ g = 𝟙 X) : g = f.in
v
参数：hom_inv_id : f.hom ≫ g = 𝟙 X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Iso.hom_comp_eq_id`：hom_comp_eq_id (α : X ≅ Y) {f : Y ⟶ X
} : α.hom ≫ f = 𝟙 X ↔ f = α.inv
-/
theorem inv_ext' {f : X ≅ Y} {g : Y ⟶ X} (hom_inv_id : f.hom ≫ g = 𝟙 X) : g = f.inv :=
  (hom_comp_eq_id f).1 hom_inv_id

/-!
All these cancellation lemmas can be solved by `simp [cancel_mono]` (or `simp [cancel_epi]`),
but with the current design `cancel_mono` is not a good `simp` lemma,
because it generates a typeclass search.

When we can see syntactically that a morphism is a `mono` or an `epi`
because it came from an isomorphism, it's fine to do the cancellation via `simp`.

In the longer term, it might be worth exploring making `mono` and `epi` structures,
rather than typeclasses, with coercions back to `X ⟶ Y`.
Presumably we could write `X ↪ Y` and `X ↠ Y`.
-/


@[to_dual (attr := simp) (reorder := f g' g) cancel_iso_inv_right]
/-
**CategoryTheory.Iso.cancel_iso_hom_left** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Iso`。
形式化陈述：cancel_iso_hom_left {X Y Z : C} (f : X ≅ Y) (g g' : Y ⟶ Z) : f.hom ≫ g = f
.hom ≫ g' ↔ g = g'
参数：f : X ≅ Y；g g' : Y ⟶ Z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.epi_of_iso`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],   CategoryTheo
ry.Epi f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
All these cancellation lemmas can be solved by `simp [cancel_mono]` (or `simp [c
ancel_epi]`),
but with the current design `cancel_mono` is not a good `simp` lemma,
because it generates a typeclass search.

When we can see syntactically that a morphism is a `mono` or an `epi`
because it came from an isomorphism, it's fine to do the cancellation via `simp`
.

In the longer term, it might be worth exploring making `mono` and `epi` structur
es,
rather than typeclasses, with coercions back to `X ⟶ Y`.
Presumably we could write `X ↪ Y` and `X ↠ Y`.
-/
theorem cancel_iso_hom_left {X Y Z : C} (f : X ≅ Y) (g g' : Y ⟶ Z) :
    f.hom ≫ g = f.hom ≫ g' ↔ g = g' := by
  simp only [cancel_epi]

@[to_dual (attr := simp) (reorder := f f' g) cancel_iso_inv_left]
/-
**CategoryTheory.Iso.cancel_iso_hom_right** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Iso`。
形式化陈述：cancel_iso_hom_right {X Y Z : C} (f f' : X ⟶ Y) (g : Y ≅ Z) : f ≫ g.hom = 
f' ≫ g.hom ↔ f = f'
参数：f f' : X ⟶ Y；g : Y ≅ Z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.mono_of_iso`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   CategoryThe
ory.Mono f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem cancel_iso_hom_right {X Y Z : C} (f f' : X ⟶ Y) (g : Y ≅ Z) :
    f ≫ g.hom = f' ≫ g.hom ↔ f = f' := by
  simp only [cancel_mono]

/-
Unfortunately cancelling an isomorphism from the right of a chain of compositions is awkward.
We would need separate lemmas for each chain length (worse: for each pair of chain lengths).

We provide two more lemmas, for case of three morphisms, because this actually comes up in practice,
but then stop.
-/
@[simp, to_dual none]
/-
**CategoryTheory.Iso.cancel_iso_hom_right_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Iso`。
形式化陈述：cancel_iso_hom_right_assoc {W X X' Y Z : C} (f : W ⟶ X) (g : X ⟶ Y) (f' : 
W ⟶ X') (g' : X' ⟶ Y) (h : Y ≅ Z) : f ≫ g ≫ h.hom = f' ≫ g' ≫ h.hom ↔ f ≫ g = f'
 ≫ g'
参数：f : W ⟶ X；g : X ⟶ Y；f' : W ⟶ X'；g' : X' ⟶ Y；h : Y ≅ Z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.IsIso.mono_of_iso`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   CategoryThe
ory.Mono f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Unfortunately cancelling an isomorphism from the right of a chain of composition
s is awkward.
We would need separate lemmas for each chain length (worse: for each pair of cha
in lengths).

We provide two more lemmas, for case of three morphisms, because this actually c
omes up in practice,
but then stop.
-/
theorem cancel_iso_hom_right_assoc {W X X' Y Z : C} (f : W ⟶ X) (g : X ⟶ Y) (f' : W ⟶ X')
    (g' : X' ⟶ Y) (h : Y ≅ Z) : f ≫ g ≫ h.hom = f' ≫ g' ≫ h.hom ↔ f ≫ g = f' ≫ g' := by
  simp only [← Category.assoc, cancel_mono]

@[simp, to_dual none]
/-
**CategoryTheory.Iso.cancel_iso_inv_right_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Iso`。
形式化陈述：cancel_iso_inv_right_assoc {W X X' Y Z : C} (f : W ⟶ X) (g : X ⟶ Y) (f' : 
W ⟶ X') (g' : X' ⟶ Y) (h : Z ≅ Y) : f ≫ g ≫ h.inv = f' ≫ g' ≫ h.inv ↔ f ≫ g = f'
 ≫ g'
参数：f : W ⟶ X；g : X ⟶ Y；f' : W ⟶ X'；g' : X' ⟶ Y；h : Z ≅ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.IsIso.mono_of_iso`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   CategoryThe
ory.Mono f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem cancel_iso_inv_right_assoc {W X X' Y Z : C} (f : W ⟶ X) (g : X ⟶ Y) (f' : W ⟶ X')
    (g' : X' ⟶ Y) (h : Z ≅ Y) : f ≫ g ≫ h.inv = f' ≫ g' ≫ h.inv ↔ f ≫ g = f' ≫ g' := by
  simp only [← Category.assoc, cancel_mono]

section

variable {D : Type*} [Category* D] {X Y : C} (e : X ≅ Y)

@[reassoc +to_dual (attr := simp), grind =]
/-
**CategoryTheory.Iso.map_hom_inv_id** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Is
o`。
形式化陈述：map_hom_inv_id (F : C ⥤ D) : F.map e.hom ≫ F.map e.inv = 𝟙 _
参数：F : C ⥤ D。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_hom_inv_id (F : C ⥤ D) :
    F.map e.hom ≫ F.map e.inv = 𝟙 _ := by grind

@[reassoc +to_dual (attr := simp), grind =]
/-
**CategoryTheory.Iso.map_inv_hom_id** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Is
o`。
形式化陈述：map_inv_hom_id (F : C ⥤ D) : F.map e.inv ≫ F.map e.hom = 𝟙 _
参数：F : C ⥤ D。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_inv_hom_id (F : C ⥤ D) :
    F.map e.inv ≫ F.map e.hom = 𝟙 _ := by grind

end

end Iso

namespace Functor

universe u₁ v₁ u₂ v₂

variable {D : Type u₂}
variable [Category.{v₂} D]

/-- A functor `F : C ⥤ D` sends isomorphisms `i : X ≅ Y` to isomorphisms `F.obj X ≅ F.obj Y` -/
@[simps, implicit_reducible]
/-
**CategoryTheory.Functor.mapIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functo
r`。
形式化陈述：mapIso (F : C ⥤ D) {X Y : C} (i : X ≅ Y) : F.obj X ≅ F.obj Y where hom
参数：F : C ⥤ D；i : X ≅ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `F : C ⥤ D` sends isomorphisms `i : X ≅ Y` to isomorphisms `F.obj X ≅ 
F.obj Y`
-/
def mapIso (F : C ⥤ D) {X Y : C} (i : X ≅ Y) : F.obj X ≅ F.obj Y where
  hom := F.map i.hom
  inv := F.map i.inv

attribute [to_dual existing mapIso_inv] mapIso_hom

@[simp]
/-
**CategoryTheory.Functor.mapIso_symm** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.F
unctor`。
形式化陈述：mapIso_symm (F : C ⥤ D) {X Y : C} (i : X ≅ Y) : F.mapIso i.symm = (F.mapIs
o i).symm
参数：F : C ⥤ D；i : X ≅ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapIso_symm (F : C ⥤ D) {X Y : C} (i : X ≅ Y) : F.mapIso i.symm = (F.mapIso i).symm :=
  rfl

@[simp]
/-
**CategoryTheory.Functor.mapIso_trans** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Functor`。
形式化陈述：mapIso_trans (F : C ⥤ D) {X Y Z : C} (i : X ≅ Y) (j : Y ≅ Z) : F.mapIso (i
 ≪≫ j) = F.mapIso i ≪≫ F.mapIso j
参数：F : C ⥤ D；i : X ≅ Y；j : Y ≅ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
-/
theorem mapIso_trans (F : C ⥤ D) {X Y Z : C} (i : X ≅ Y) (j : Y ≅ Z) :
    F.mapIso (i ≪≫ j) = F.mapIso i ≪≫ F.mapIso j := by
  ext; apply Functor.map_comp

@[simp]
/-
**CategoryTheory.Functor.mapIso_refl** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.F
unctor`。
形式化陈述：mapIso_refl (F : C ⥤ D) (X : C) : F.mapIso (Iso.refl X) = Iso.refl (F.obj 
X)
参数：F : C ⥤ D；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
-/
theorem mapIso_refl (F : C ⥤ D) (X : C) : F.mapIso (Iso.refl X) = Iso.refl (F.obj X) :=
  Iso.ext <| F.map_id X

@[to_dual self]
/-
**CategoryTheory.Functor.map_isIso** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Fun
ctor`。
形式化陈述：map_isIso (F : C ⥤ D) (f : X ⟶ Y) [IsIso f] : IsIso (F.map f)
参数：F : C ⥤ D；f : X ⟶ Y。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
instance map_isIso (F : C ⥤ D) (f : X ⟶ Y) [IsIso f] : IsIso (F.map f) :=
  (F.mapIso (asIso f)).isIso_hom

@[simp, push ←, to_dual self]
/-
**CategoryTheory.Functor.map_inv** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Funct
or`。
形式化陈述：map_inv (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) [IsIso f] : F.map (inv f) = inv 
(F.map f)
参数：F : C ⥤ D；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsIso.eq_inv_of_hom_inv_id`：eq_inv_of_hom_inv_id {f : X ⟶
 Y} [IsIso f] {g : Y ⟶ X} (hom_inv_id : f ≫ g = 𝟙 X) : g = inv f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_inv (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) [IsIso f] : F.map (inv f) = inv (F.map f) := by
  apply eq_inv_of_hom_inv_id
  simp [← F.map_comp]

@[to_dual (attr := reassoc) map_inv_hom]
/-
**CategoryTheory.Functor.map_hom_inv** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.F
unctor`。
形式化陈述：map_hom_inv (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) [IsIso f] : F.map f ≫ F.map 
(inv f) = 𝟙 (F.obj X)
参数：F : C ⥤ D；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_inv`：map_inv (F : C ⥤ D) {X Y : C} (f : X ⟶ Y
) [IsIso f] : F.map (inv f) = inv (F.map f)
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_hom_inv (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) [IsIso f] :
    F.map f ≫ F.map (inv f) = 𝟙 (F.obj X) := by simp

-- The following two lemmas are needed to generate good elementwise lemmas
@[reassoc]
/-
**CategoryTheory.Functor.map_hom_inv'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Functor`。
形式化陈述：map_hom_inv' (F : C ⥤ D) {X Y : C} (f : X ≅ Y) : F.map f.hom ≫ F.map f.inv
 = 𝟙 (F.obj X)
参数：F : C ⥤ D；f : X ≅ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Iso.map_hom_inv_id`：map_hom_inv_id (F : C ⥤ D) : F.map e.
hom ≫ F.map e.inv = 𝟙 _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_hom_inv' (F : C ⥤ D) {X Y : C} (f : X ≅ Y) :
    F.map f.hom ≫ F.map f.inv = 𝟙 (F.obj X) := by simp

@[reassoc]
/-
**CategoryTheory.Functor.map_inv_hom'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Functor`。
形式化陈述：map_inv_hom' (F : C ⥤ D) {X Y : C} (f : X ≅ Y) : F.map f.inv ≫ F.map f.hom
 = 𝟙 (F.obj Y)
参数：F : C ⥤ D；f : X ≅ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Iso.map_inv_hom_id`：map_inv_hom_id (F : C ⥤ D) : F.map e.
inv ≫ F.map e.hom = 𝟙 _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_inv_hom' (F : C ⥤ D) {X Y : C} (f : X ≅ Y) :
    F.map f.inv ≫ F.map f.hom = 𝟙 (F.obj Y) := by simp

end Functor

end CategoryTheory

