/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Paul Lezeau, Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.CategoryTheory.Monoidal.Action.Basic

/-!
# The category of module objects over a monoid object.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory MonObj

namespace CategoryTheory
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalLeftAction C D]

section ModObj

open MonObj AddMonObj

open scoped MonoidalLeftAction

section

variable (M : C) [AddMonObj M]

/-- Given an action of a monoidal category `C` on a category `D`,
an action of an additive monoid object `M` in `C` on an object `X` in `D` is the data of a
map `vadd : M ⊙ₗ X ⟶ X` that satisfies zero-additivity and associativity with addition.

See `AddAction` for the non-categorical version. -/
/-
**CategoryTheory.AddModObj** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory`。
形式化陈述：AddModObj (X : D) where /-- The action map -/ vadd : M ⊙ₗ X ⟶ X /-- The ze
ro acts trivially. -/ zero_vadd (X) : ζ ⊵ₗ X ≫ vadd = (funₗ X).hom
参数：X : D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an action of a monoidal category `C` on a category `D`,
an action of an additive monoid object `M` in `C` on an object `X` in `D` is the
 data of a
map `vadd : M ⊙ₗ X ⟶ X` that satisfies zero-additivity and associativity with ad
dition.

See `AddAction` for the non-categorical version.
-/
class AddModObj (X : D) where
  /-- The action map -/
  vadd : M ⊙ₗ X ⟶ X
  /-- The zero acts trivially. -/
  zero_vadd (X) : ζ ⊵ₗ X ≫ vadd = (λₗ X).hom := by cat_disch
  /-- The action map is compatible with addition. -/
  add_vadd (X) : σ ⊵ₗ X ≫ vadd = (αₗ M M X).hom ≫ M ⊴ₗ vadd ≫ vadd := by cat_disch

end

variable (M : C) [MonObj M]

/-- Given an action of a monoidal category `C` on a category `D`,
an action of a monoid object `M` in `C` on an object `X` in `D` is the data of a
map `smul : M ⊙ₗ X ⟶ X` that satisfies unitality and associativity with
multiplication.

See `MulAction` for the non-categorical version. -/
@[to_additive]
/-
**CategoryTheory.ModObj** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory`。
形式化陈述：ModObj (X : D) where /-- The action map -/ smul : M ⊙ₗ X ⟶ X /-- The ident
ity acts trivially. -/ one_smul (X) : η ⊵ₗ X ≫ smul = (funₗ X).hom
参数：X : D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an action of a monoidal category `C` on a category `D`,
an action of a monoid object `M` in `C` on an object `X` in `D` is the data of a
map `smul : M ⊙ₗ X ⟶ X` that satisfies unitality and associativity with
multiplication.

See `MulAction` for the non-categorical version.
-/
class ModObj (X : D) where
  /-- The action map -/
  smul : M ⊙ₗ X ⟶ X
  /-- The identity acts trivially. -/
  one_smul (X) : η ⊵ₗ X ≫ smul = (λₗ X).hom := by cat_disch
  /-- The action map is compatible with multiplication. -/
  mul_smul (X) : μ ⊵ₗ X ≫ smul = (αₗ M M X).hom ≫ M ⊴ₗ smul ≫ smul := by cat_disch

set_option linter.translateOverwrite false in
attribute [to_additive existing (attr := reassoc (attr := simp))] ModObj.mul_smul ModObj.one_smul


namespace AddModObj

@[inherit_doc] scoped[CategoryTheory.AddMonObj] notation "δ" => AddModObj.vadd
@[inherit_doc] scoped[CategoryTheory.AddMonObj] notation "δ[" Y "]" => AddModObj.vadd (X := Y)
@[inherit_doc] scoped[CategoryTheory.AddMonObj] notation "δ[" N "," Y "]" =>
  AddModObj.vadd (M := N) (X := Y)

end AddModObj

namespace ModObj

@[inherit_doc] scoped[CategoryTheory.MonObj] notation "γ" => ModObj.smul
@[inherit_doc] scoped[CategoryTheory.MonObj] notation "γ[" Y "]" => ModObj.smul (X := Y)
@[inherit_doc] scoped[CategoryTheory.MonObj] notation "γ[" N "," Y "]" =>
  ModObj.smul (M := N) (X := Y)

end ModObj

variable {M}

namespace ModObj

@[to_additive]
/-
**CategoryTheory.ModObj.assoc_flip** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Mod
Obj`。
形式化陈述：assoc_flip (X : D) [ModObj M X] : M ⊴ₗ γ ≫ γ = (αₗ M M X).inv ≫ μ[M] ⊵ₗ X 
≫ γ
参数：X : D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ModObj.mul_smul`：∀ {C : Type u₁} {inst : CategoryTheory.C
ategory.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {D : Type u₂}  
 {inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem assoc_flip (X : D) [ModObj M X] : M ⊴ₗ γ ≫ γ =
    (αₗ M M X).inv ≫ μ[M] ⊵ₗ X ≫ γ := by
  simp

variable (M) in
/-- The action of a monoid object on itself. -/
-- See note [reducible non-instances]
@[to_additive /-- The action of an additive monoid object on itself. -/]
/-
**CategoryTheory.ModObj.regular** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.ModO
bj`。
形式化陈述：regular : ModObj M M where smul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev regular : ModObj M M where
  smul := μ

attribute [local instance] regular in
@[to_additive (attr := simp)]
/-
**CategoryTheory.ModObj.smul_eq_mul** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Mo
dObj`。
形式化陈述：smul_eq_mul (M : C) [MonObj M] : γ[M,M] = μ[M]
参数：M : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma smul_eq_mul (M : C) [MonObj M] : γ[M,M] = μ[M] := rfl

/-- If `C` acts monoidally on `D`, then every object of `D` is canonically a
module over the trivial monoid. -/
@[to_additive (attr := simps) /-- If `C` acts monoidally on `D`, then every object of `D` is
canonically an additive module over the trivial additive monoid. -/]
/-
**CategoryTheory.ModObj.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ModObj`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : D) : ModObj (𝟙_ C) X where
  smul := (λₗ _).hom

@[to_additive (attr := ext)]
/-
**CategoryTheory.ModObj.ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.ModObj`。
形式化陈述：ext {X : C} (h₁ h₂ : ModObj M X) (H : h₁.smul = h₂.smul) : h₁ = h₂
参数：h₁ h₂ : ModObj M X；H : h₁.smul = h₂.smul。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem ext {X : C} (h₁ h₂ : ModObj M X) (H : h₁.smul = h₂.smul) :
    h₁ = h₂ := by
  cases h₁
  cases h₂
  subst H
  rfl

open MonoidalLeftAction in
/-- Transfer a `MulActionObj` along isomorphisms. -/
@[to_additive (attr := simps! -isSimp, implicit_reducible)
/-- Transfer an `AddActionObj` along isomorphisms. -/]
/-
**CategoryTheory.ModObj.ofIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.ModObj`。
形式化陈述：ofIso {X : D} {N : C} [MonObj N] (e₁ : M ≅ N) [IsMonHom e₁.hom] {Y : D} (e
₂ : X ≅ Y) [ModObj M X] : ModObj N Y where smul
参数：e₁ : M ≅ N；e₂ : X ≅ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def ofIso {X : D} {N : C} [MonObj N] (e₁ : M ≅ N) [IsMonHom e₁.hom]
      {Y : D} (e₂ : X ≅ Y) [ModObj M X] :
    ModObj N Y where
  smul := (e₁.inv ⊙ₗₘ e₂.inv) ≫ γ ≫ e₂.hom
  one_smul := by
    have : η ⊵ₗ Y ≫ (e₁.inv ⊙ₗₘ e₂.inv) = _ ⊴ₗ e₂.inv ≫ (η ≫ e₁.inv) ⊵ₗ X := by
      rw [actionHom_def', comp_actionHomLeft, action_exchange_assoc]
    simp [reassoc_of% this]
  mul_smul := by
    have : μ[N] ⊵ₗ Y ≫ (e₁.inv ⊙ₗₘ e₂.inv) =
        ((e₁.inv ⊗ₘ e₁.inv) ⊙ₗₘ e₂.inv) ≫ μ[M] ⊵ₗ X := by
      rw [actionHom_def', action_exchange, ← comp_actionHomLeft_assoc, IsMonHom.mul_hom,
        comp_actionHomLeft, Category.assoc, ← action_exchange, actionHom_def']
      nth_rw 2 [action_exchange]
      rw [Category.assoc]
    rw [reassoc_of% this]
    have : (αₗ N M X).inv ≫ (e₁.inv ▷ M) ⊵ₗ X ≫ (αₗ M M X).hom ≫ M ⊴ₗ smul =
        N ⊴ₗ γ ≫ e₁.inv ⊵ₗ X := by
      rw [← actionHomLeft_action_assoc, action_exchange]
    simp [tensorHom_def', actionHom_def', mul_smul_assoc, reassoc_of% this]

section SelfAction

variable (X : C) [ModObj M X]

@[to_additive (attr := reassoc (attr := simp))]
/-
**CategoryTheory.ModObj.one_smul_self** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
ModObj`。
形式化陈述：one_smul_self (M : C) [MonObj M] (X : C) [ModObj M X] : η ▷ X ≫ γ[M, X] = 
(fun_ X).hom
参数：M : C；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ModObj.one_smul`：∀ {C : Type u₁} {inst : CategoryTheory.C
ategory.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {D : Type u₂}  
 {inst_2 : CategoryT…
-/
lemma one_smul_self (M : C) [MonObj M] (X : C) [ModObj M X] :
    η ▷ X ≫ γ[M, X] = (λ_ X).hom :=
  ModObj.one_smul (M := M) X

@[to_additive (attr := reassoc (attr := simp))]
/-
**CategoryTheory.ModObj.mul_smul_self** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
ModObj`。
形式化陈述：mul_smul_self (M : C) [MonObj M] (X : C) [ModObj M X] : (μ ▷ X) ≫ γ[M, X] 
= (α_ _ _ _).hom ≫ (M ◁ γ[M, X]) ≫ γ[M, X]
参数：M : C；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ModObj.mul_smul`：∀ {C : Type u₁} {inst : CategoryTheory.C
ategory.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {D : Type u₂}  
 {inst_2 : CategoryT…
-/
lemma mul_smul_self (M : C) [MonObj M] (X : C) [ModObj M X] :
    (μ ▷ X) ≫ γ[M, X] = (α_ _ _ _).hom ≫ (M ◁ γ[M, X]) ≫ γ[M, X] :=
  ModObj.mul_smul (M := M) X

@[to_additive (attr := reassoc)]
/-
**CategoryTheory.ModObj.mul_smul_self_flip** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.ModObj`。
形式化陈述：mul_smul_self_flip : M ◁ γ[M, X] ≫ γ[M, X] = (α_ M M X).inv ≫ (μ ▷ X) ≫ γ[
M, X]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ModObj.mul_smul_self`：mul_smul_self (M : C) [MonObj M] (X
 : C) [ModObj M X] : (μ ▷ X) ≫ γ[M, X] = (α_ _ _ _).hom ≫ (M ◁ γ[M, X]) ≫ γ[M, X
]
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_smul_self_flip : M ◁ γ[M, X] ≫ γ[M, X] = (α_ M M X).inv ≫ (μ ▷ X) ≫ γ[M, X] := by
  simp

end SelfAction

end ModObj

end ModObj

open scoped ModObj MonoidalLeftAction

variable {M' N' O' : D}

open AddMonObj in
/-- A morphism in `D` is a morphism of `A`-additive module objects if it commutes with
the action maps -/
/-
**CategoryTheory.IsAddModHom** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory`。
形式化陈述：IsAddModHom (A : C) [AddMonObj A] [AddModObj A M'] [AddModObj A N'] (f : M
' ⟶ N') where vadd_hom : δ[M'] ≫ f = A ⊴ₗ f ≫ δ[N']
参数：A : C；f : M' ⟶ N'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism in `D` is a morphism of `A`-additive module objects if it commutes wi
th
the action maps
-/
class IsAddModHom (A : C) [AddMonObj A] [AddModObj A M'] [AddModObj A N'] (f : M' ⟶ N') where
  vadd_hom : δ[M'] ≫ f = A ⊴ₗ f ≫ δ[N'] := by cat_disch

variable (A : C) [MonObj A]
/-- A morphism in `D` is a morphism of `A`-module objects if it commutes with
the action maps -/
@[to_additive]
/-
**CategoryTheory.IsModHom** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory`。
形式化陈述：IsModHom {M N : D} [ModObj A M] [ModObj A N] (f : M ⟶ N) where smul_hom : 
γ[M] ≫ f = A ⊴ₗ f ≫ γ[N]
参数：f : M ⟶ N。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism in `D` is a morphism of `A`-module objects if it commutes with
the action maps
-/
class IsModHom {M N : D} [ModObj A M] [ModObj A N] (f : M ⟶ N) where
  smul_hom : γ[M] ≫ f = A ⊴ₗ f ≫ γ[N] := by cat_disch

@[deprecated (since := "2026-04-21")]
alias IsMod_Hom := IsModHom

@[deprecated (since := "2026-04-21")]
alias IsMod_Hom.smul_hom := IsModHom.smul_hom

set_option linter.translateOverwrite false in
attribute [to_additive existing (attr := reassoc (attr := simp))] IsModHom.smul_hom

variable {M N O : D} [ModObj A M] [ModObj A N] [ModObj A O]

@[to_additive]
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsModHom A (𝟙 M) where

@[to_additive]
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : M ⟶ N) (g : N ⟶ O) [IsModHom A f] [IsModHom A g] :
    IsModHom A (f ≫ g) where

@[to_additive]
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : M ≅ N) [IsModHom A f.hom] :
    IsModHom A f.inv where
  smul_hom := by simp [Iso.comp_inv_eq]

variable (D) in
/-- An additive module object for an additive monoid object in a monoidal category acting on the
ambient category. -/
/-
**CategoryTheory.AddMod** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.MonoidalCategory C] →       (D : Type u₂) →         [inst_2 :
 CategoryTheory.Category.{v₂, u₂} D] →           [CategoryTheory.MonoidalCategor
y.MonoidalLeftAction C D] →             (A : C) → [CategoryTheory.AddMonObj A] →
 Type (max u₂ v₂)
参数：D : Type u₂；A : C；max u₂ v₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An additive module object for an additive monoid object in a monoidal category a
cting on the
ambient category.
-/
structure AddMod (A : C) [AddMonObj A] where
  /-- The underlying object in the ambient category -/
  X : D
  [addMod : AddModObj A X]

attribute [instance] AddMod.addMod

variable (D) in
/-- A module object for a monoid object in a monoidal category acting on the
ambient category. -/
@[to_additive AddMod]
/-
**CategoryTheory.Mod** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.MonoidalCategory C] →       (D : Type u₂) →         [inst_2 :
 CategoryTheory.Category.{v₂, u₂} D] →           [CategoryTheory.MonoidalCategor
y.MonoidalLeftAction C D] →             (A : C) → [CategoryTheory.MonObj A] → Ty
pe (max u₂ v₂)
参数：D : Type u₂；A : C；max u₂ v₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A module object for a monoid object in a monoidal category acting on the
ambient category.
-/
structure Mod (A : C) [MonObj A] where
  /-- The underlying object in the ambient category -/
  X : D
  [mod : ModObj A X]

@[deprecated (since := "2026-04-21")]
alias Mod_ := Mod

@[deprecated (since := "2026-04-21")]
alias Mod_.mod := Mod.mod

attribute [instance] Mod.mod

namespace AddMod

variable {A : C} [AddMonObj A] (M : AddMod D A)

/-- A morphism of additive module objects. -/
@[ext]
/-
**CategoryTheory.AddMod.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.AddMod`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.MonoidalCategory C] →       {D : Type u₂} →         [inst_2 :
 CategoryTheory.Category.{v₂, u₂} D] →           [inst_3 : CategoryTheory.Monoid
alCategory.MonoidalLeftAction C D] →             {A : C} →               [inst_4
 : CategoryTheory.AddMonObj A] → CategoryTheory.AddMod D A → CategoryTheory.AddM
od D A → Type v₂
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of additive module objects.
-/
structure Hom (M N : AddMod D A) where
  /-- The underlying morphism -/
  hom : M.X ⟶ N.X
  [isAddModHom : IsAddModHom A hom]

attribute [instance] Hom.isAddModHom

end AddMod

namespace Mod

variable {A : C} [MonObj A] (M : Mod D A)

@[to_additive]
/-
**CategoryTheory.Mod.assoc_flip** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Mod`。
形式化陈述：assoc_flip : A ⊴ₗ γ ≫ γ = (αₗ A A M.X).inv ≫ μ ⊵ₗ M.X ≫ γ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ModObj.mul_smul`：∀ {C : Type u₁} {inst : CategoryTheory.C
ategory.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {D : Type u₂}  
 {inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem assoc_flip : A ⊴ₗ γ ≫ γ = (αₗ A A M.X).inv ≫ μ ⊵ₗ M.X ≫ γ := by simp

/-- A morphism of module objects. -/
@[ext, to_additive existing]
/-
**CategoryTheory.Mod.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.Mod`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.MonoidalCategory C] →       {D : Type u₂} →         [inst_2 :
 CategoryTheory.Category.{v₂, u₂} D] →           [inst_3 : CategoryTheory.Monoid
alCategory.MonoidalLeftAction C D] →             {A : C} → [inst_4 : CategoryThe
ory.MonObj A] → CategoryTheory.Mod D A → CategoryTheory.Mod D A → Type v₂
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of module objects.
-/
structure Hom (M N : Mod D A) where
  /-- The underlying morphism -/
  hom : M.X ⟶ N.X
  [isModHom : IsModHom A hom]

attribute [instance] Hom.isModHom

/-- An alternative constructor for `Hom`,
taking a morphism without a `[IsModHom]` instance, as well as the relevant
equality to put such an instance. -/
@[to_additive (attr := simps!)
  /-- An alternative constructor for `Hom`,
  taking a morphism without a `[IsAddModHom]` instance, as well as the relevant
  equality to put such an instance. -/]
/-
**CategoryTheory.Mod.Hom.mk'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Mod.Hom`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.MonoidalCategory C] →       {D : Type u₂} →         [inst_2 :
 CategoryTheory.Category.{v₂, u₂} D] →           [inst_3 : CategoryTheory.Monoid
alCategory.MonoidalLeftAction C D] →             {A : C} →               [inst_4
 : CategoryTheory.MonObj A] →                 {M N : CategoryTheory.Mod D A} →  
                 (f : M.X ⟶ N.X) →                     autoParam                
         (CategoryTheory.CategoryStruct.comp CategoryTheory.ModObj.smul f =     
                      CategoryTheory.CategoryStruct.comp                        
     (CategoryTheory.MonoidalCategory.MonoidalLeftActionStruct.actionHomRight A 
f)                             CategoryTheory.ModObj.smul)                      
   CategoryTheory.Mod.Hom.mk'._auto_1 →                       M.Hom N
参数：f : M.X ⟶ N.X；CategoryTheory.CategoryStruct.comp CategoryTheory.ModObj.smul f
 =                           CategoryTheory.CategoryStruct.comp                 
            (CategoryTheory.MonoidalCategory.MonoidalLeftActionStruct.actionHomR
ight A f)                             CategoryTheory.ModObj.smul。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Hom.mk' {M N : Mod D A} (f : M.X ⟶ N.X)
    (smul_hom : γ[M.X] ≫ f = A ⊴ₗ f ≫ γ[N.X] := by cat_disch) : Hom M N :=
  letI : IsModHom A f := ⟨smul_hom⟩
  ⟨f⟩

/-- An alternative constructor for `Hom`,
taking a morphism without a `[IsModHom]` instance, between objects with
a `ModObj` instance (rather than bundled as `Mod`),
as well as the relevant equality to put such an instance. -/
@[to_additive (attr := simps!)
  /-- An alternative constructor for `Hom`,
  taking a morphism without a `[IsAddModHom]` instance, between objects with
  an `AddModObj` instance (rather than bundled as `AddMod`),
  as well as the relevant equality to put such an instance. -/]
/-
**CategoryTheory.Mod.Hom.mk''** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Mod.Hom`
。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.MonoidalCategory C] →       {D : Type u₂} →         [inst_2 :
 CategoryTheory.Category.{v₂, u₂} D] →           [inst_3 : CategoryTheory.Monoid
alCategory.MonoidalLeftAction C D] →             {A : C} →               [inst_4
 : CategoryTheory.MonObj A] →                 {M N : D} →                   [ins
t_5 : CategoryTheory.ModObj A M] →                     [inst_6 : CategoryTheory.
ModObj A N] →                       (f : M ⟶ N) →                         autoPa
ram                             (CategoryTheory.CategoryStruct.comp CategoryTheo
ry.ModObj.smul f =                               CategoryTheory.CategoryStruct.c
omp                                 (CategoryTheory.MonoidalCategory.MonoidalLef
tActionStruct.actionHomRight A f)                                 CategoryTheory
.ModObj.smul)                             CategoryTheory.Mod.Hom.mk''._auto_1 → 
                          { X := M, mod := inst_5 }.Hom { X := N, mod := inst_6 
}
参数：f : M ⟶ N；CategoryTheory.CategoryStruct.comp CategoryTheory.ModObj.smul f =  
                             CategoryTheory.CategoryStruct.comp                 
                (CategoryTheory.MonoidalCategory.MonoidalLeftActionStruct.action
HomRight A f)                                 CategoryTheory.ModObj.smul。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Hom.mk'' {M N : D} [ModObj A M] [ModObj A N] (f : M ⟶ N)
    (smul_hom : γ[M] ≫ f = A ⊴ₗ f ≫ γ[N] := by cat_disch) :
    Hom (.mk (A := A) M) (.mk (A := A) N) :=
  letI : IsModHom A f := ⟨smul_hom⟩
  ⟨f⟩

/-- The identity morphism on a module object. -/
@[to_additive (attr := simps) /-- The identity morphism on an additive module object. -/]
/-
**CategoryTheory.Mod.id** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Mod`。
形式化陈述：id (M : Mod D A) : Hom M M where hom
参数：M : Mod D A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity morphism on a module object.
-/
def id (M : Mod D A) : Hom M M where hom := 𝟙 M.X

@[to_additive]
/-
**CategoryTheory.Mod.homInhabited** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mod`
。
形式化陈述：homInhabited (M : Mod D A) : Inhabited (Hom M M)
参数：M : Mod D A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance homInhabited (M : Mod D A) : Inhabited (Hom M M) :=
  ⟨id M⟩

/-- Composition of module object morphisms. -/
@[to_additive (attr := simps) /-- Composition of additive module object morphisms. -/]
/-
**CategoryTheory.Mod.comp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Mod`。
形式化陈述：comp {M N O : Mod D A} (f : Hom M N) (g : Hom N O) : Hom M O where hom
参数：f : Hom M N；g : Hom N O。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of module object morphisms.
-/
def comp {M N O : Mod D A} (f : Hom M N) (g : Hom N O) :
    Hom M O where
  hom := f.hom ≫ g.hom

@[to_additive]
/-
**CategoryTheory.Mod.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (Mod D A) where
  Hom M N := Hom M N
  id := id
  comp f g := comp f g

@[to_additive (attr := ext)]
/-
**CategoryTheory.Mod.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Mod`。
形式化陈述：hom_ext {M N : Mod D A} (f₁ f₂ : M ⟶ N) (h : f₁.hom = f₂.hom) : f₁ = f₂
参数：f₁ f₂ : M ⟶ N；h : f₁.hom = f₂.hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Mod.Hom.ext`：∀ {C : Type u₁} {inst : CategoryTheory.Categ
ory.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {D : Type u₂}   {in
st_2 : CategoryT…
-/
lemma hom_ext {M N : Mod D A} (f₁ f₂ : M ⟶ N) (h : f₁.hom = f₂.hom) :
    f₁ = f₂ :=
  Hom.ext h

@[to_additive (attr := simp)]
/-
**CategoryTheory.Mod.id_hom'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Mod`。
形式化陈述：id_hom' (M : Mod D A) : (𝟙 M : M ⟶ M).hom = 𝟙 M.X
参数：M : Mod D A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_hom' (M : Mod D A) : (𝟙 M : M ⟶ M).hom = 𝟙 M.X := by
  rfl

@[to_additive (attr := simp)]
/-
**CategoryTheory.Mod.comp_hom'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Mod`。
形式化陈述：comp_hom' {M N K : Mod D A} (f : M ⟶ N) (g : N ⟶ K) : (f ≫ g).hom = f.hom 
≫ g.hom
参数：f : M ⟶ N；g : N ⟶ K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_hom' {M N K : Mod D A} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

variable (A)

/-- A monoid object as a module over itself. -/
@[to_additive (attr := simps) /-- An additive monoid object as an additive module over itself. -/]
/-
**CategoryTheory.Mod.regular** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Mod`。
形式化陈述：regular : Mod C A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A monoid object as a module over itself.
-/
def regular : Mod C A :=
  letI : ModObj A A := .regular A
  ⟨A⟩

@[to_additive]
/-
**CategoryTheory.Mod.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Mod C A) :=
  ⟨regular A⟩

/-- The forgetful functor from module objects to the ambient category. -/
@[to_additive (attr := simps)
  /-- The forgetful functor from additive module objects to the ambient category. -/]
/-
**CategoryTheory.Mod.forget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Mod`。
形式化陈述：forget : Mod D A ⥤ D where obj A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def forget : Mod D A ⥤ D where
  obj A := A.X
  map f := f.hom

section comap

variable {A B : C} [MonObj A] [MonObj B] (f : A ⟶ B) [IsMonHom f]

open MonoidalLeftAction in
/-- When `M` is a `B`-module in `D` and `f : A ⟶ B` is a morphism of internal
monoid objects, `M` inherits an `A`-module structure via
"restriction of scalars", i.e `γ[A, M] = f ⊵ₗ M ≫ γ[B, M]`. -/
@[to_additive (attr := simps!, instance_reducible)
  /-- When `M` is a `B`-additive module in `D` and `f : A ⟶ B` is a morphism of internal
  additive monoid objects, `M` inherits an `A`-additive module structure via
  "restriction of scalars", i.e `δ[A, M] = f ⊵ₗ M ≫ δ[B, M]`. -/]
/-
**CategoryTheory.Mod.scalarRestriction** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Mod`。
形式化陈述：scalarRestriction (M : D) [ModObj B M] : ModObj A M where smul
参数：M : D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def scalarRestriction (M : D) [ModObj B M] : ModObj A M where
  smul := f ⊵ₗ M ≫ γ[B,M]
  one_smul := by
    rw [← comp_actionHomLeft_assoc]
    rw [IsMonHom.one_hom, ModObj.one_smul]
  mul_smul := by
    -- oh, for homotopy.io in a widget!
    slice_rhs 2 3 => rw [action_exchange]
    simp only [actionHomLeft_action_assoc, Category.assoc, Iso.hom_inv_id_assoc,
      actionHomRight_comp]
    slice_rhs 4 6 => rw [ModObj.assoc_flip]
    slice_rhs 2 4 => rw [← whiskerLeft_actionHomLeft]
    slice_rhs 1 2 => rw [← comp_actionHomLeft]
    rw [← comp_actionHomLeft, Category.assoc, ← comp_actionHomLeft_assoc,
      IsMonHom.mul_hom, tensorHom_def, Category.assoc]

open MonoidalLeftAction in
/-- If `g : M ⟶ N` is a `B`-linear morphism of `B`-modules, then it induces an
`A`-linear morphism when `M` and `N` have an `A`-module structure obtained
by restricting scalars along a monoid morphism `A ⟶ B`. -/
@[to_additive
  /-- If `g : M ⟶ N` is a `B`-linear morphism of `B`-modules, then it induces an
  `A`-linear morphism when `M` and `N` have an `A`-module structure obtained
  by restricting scalars along an additive monoid morphism `A ⟶ B`. -/]
/-
**CategoryTheory.Mod.scalarRestriction_hom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.Mod`。
形式化陈述：scalarRestriction_hom (M N : D) [ModObj B M] [ModObj B N] (g : M ⟶ N) [IsM
odHom B g] : letI
参数：M N : D；g : M ⟶ N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Mod.scalarRestriction_smul`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCategory C] {D :
 Type u₂}   [inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.IsModHom.smul_hom`：∀ {C : Type u₁} {inst : CategoryTheory
.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {D : Type u₂}
   {inst_2 : CategoryT…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalLeftAction.action_exchange_assoc
`：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C] 
  [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
-/
lemma scalarRestriction_hom
    (M N : D) [ModObj B M] [ModObj B N] (g : M ⟶ N) [IsModHom B g] :
    letI := scalarRestriction f M
    letI := scalarRestriction f N
    IsModHom A g :=
  letI := scalarRestriction f M
  letI := scalarRestriction f N
  { smul_hom := by
      simpa using (action_exchange_assoc f g γ).symm }

/-- A morphism of monoid objects induces a "restriction" or "comap" functor
between the categories of module objects.
-/
@[to_additive (attr := simps)
  /-- A morphism of additive monoid objects induces a "restriction" or "comap" functor
  between the categories of additive module objects. -/]
/-
**CategoryTheory.Mod.comap** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Mod`。
形式化陈述：comap {A B : C} [MonObj A] [MonObj B] (f : A ⟶ B) [IsMonHom f] : Mod D B ⥤
 Mod D A where obj M
参数：f : A ⟶ B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def comap {A B : C} [MonObj A] [MonObj B] (f : A ⟶ B) [IsMonHom f] :
    Mod D B ⥤ Mod D A where
  obj M :=
    letI := scalarRestriction f M.X
    ⟨M.X⟩
  map {M N} g :=
    letI := scalarRestriction_hom f M.X N.X g.hom
    ⟨g.hom⟩

-- Lots more could be said about `comap`, e.g. how it interacts with
-- identities, compositions, and equalities of monoid object morphisms.

end comap

end Mod

namespace Mod_

@[deprecated (since := "2026-04-21")] alias assoc_flip := Mod.assoc_flip

@[deprecated (since := "2026-04-21")] alias Hom := Mod.Hom

@[deprecated (since := "2026-04-21")] alias Hom.mk' := Mod.Hom.mk'

@[deprecated (since := "2026-04-21")] alias Hom.mk'' := Mod.Hom.mk''

@[deprecated (since := "2026-04-21")] alias id := Mod.id

@[deprecated (since := "2026-04-21")] alias comp := Mod.comp

@[deprecated (since := "2026-04-21")] alias hom_ext := Mod.hom_ext

@[deprecated (since := "2026-04-21")] alias id_hom' := Mod.id_hom'

@[deprecated (since := "2026-04-21")] alias comp_hom' := Mod.comp_hom'

@[deprecated (since := "2026-04-21")] alias regular := Mod.regular

@[deprecated (since := "2026-04-21")] alias forget := Mod.forget

@[deprecated (since := "2026-04-21")] alias scalarRestriction := Mod.scalarRestriction

@[deprecated (since := "2026-04-21")] alias scalarRestriction_hom := Mod.scalarRestriction_hom

@[deprecated (since := "2026-04-21")] alias comap := Mod.comap

end Mod_

end CategoryTheory

