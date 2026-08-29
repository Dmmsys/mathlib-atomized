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

/--
Definition of `AddModObj` / `AddModObj` 的定义

English:
class AddModObj
  parameters: (X : D)
  axioms and operations (3):
    - vadd : M ⊙ₗ X ⟶ X
    - zero_vadd((X)) : ζ ⊵ₗ X ≫ vadd = (funₗ X).hom  [default: by cat_disch]
    - add_vadd((X)) : σ ⊵ₗ X ≫ vadd = (αₗ M M X).hom ≫ M ⊴ₗ vadd ≫ vadd  [default: by cat_disch]

中文:
类 加法ModObj
  参数: (X : D)
  公理与运算 (3 个):
    - vadd : M ⊙ₗ X ⟶ X
    - zero_vadd((X)) : ζ ⊵ₗ X ≫ vadd = (funₗ X).hom  [默认: by cat_disch]
    - add_vadd((X)) : σ ⊵ₗ X ≫ vadd = (αₗ M M X).hom ≫ M ⊴ₗ vadd ≫ vadd  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
class AddModObj (X : D) where
  /-- The action map -/
  vadd : M ⊙ₗ X ⟶ X
  /-- The zero acts trivially. -/
  zero_vadd (X) : ζ ⊵ₗ X ≫ vadd = (funₗ X).hom := by cat_disch
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
/--
Definition of `ModObj` / `ModObj` 的定义

English:
class ModObj
  parameters: (X : D)
  axioms and operations (3):
    - smul : M ⊙ₗ X ⟶ X
    - one_smul((X)) : η ⊵ₗ X ≫ smul = (funₗ X).hom  [default: by cat_disch]
    - mul_smul((X)) : μ ⊵ₗ X ≫ smul = (αₗ M M X).hom ≫ M ⊴ₗ smul ≫ smul  [default: by cat_disch]

中文:
类 ModObj
  参数: (X : D)
  公理与运算 (3 个):
    - smul : M ⊙ₗ X ⟶ X
    - one_smul((X)) : η ⊵ₗ X ≫ smul = (funₗ X).hom  [默认: by cat_disch]
    - mul_smul((X)) : μ ⊵ₗ X ≫ smul = (αₗ M M X).hom ≫ M ⊴ₗ smul ≫ smul  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
class ModObj (X : D) where
  /-- The action map -/
  smul : M ⊙ₗ X ⟶ X
  /-- The identity acts trivially. -/
  one_smul (X) : η ⊵ₗ X ≫ smul = (funₗ X).hom := by cat_disch
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
/--
theorem `assoc_flip` / 定理 `assoc_flip`

English:
theorem assoc_flip
  given: (X : D) [ModObj M X]
  statement: M ⊴ₗ γ ≫ γ =
  proof: by
  simp

中文:
定理 assoc_flip
  条件: (X : D) [ModObj M X]
  结论: M ⊴ₗ γ ≫ γ =
  证明: by
  simp
-/
theorem assoc_flip (X : D) [ModObj M X] : M ⊴ₗ γ ≫ γ =
    (αₗ M M X).inv ≫ μ[M] ⊵ₗ X ≫ γ := by
  simp

variable (M) in
/-- The action of a monoid object on itself. -/
-- See note [reducible non-instances]
@[to_additive /-- The action of an additive monoid object on itself. -/]
/--
Definition of `regular` / `regular` 的定义

English:
abbreviation regular
  signature: : ModObj M M where
  body: μ

中文:
缩写 regular
  签名: : ModObj M M where
  定义体: μ
-/
abbrev regular : ModObj M M where
  smul := μ

attribute [local instance] regular in
@[to_additive (attr := simp)]
/--
lemma `smul_eq_mul` / 引理 `smul_eq_mul`

English:
lemma smul_eq_mul
  given: (M : C) [MonObj M]
  statement: γ[M,M] = μ[M]
  proof: rfl

中文:
引理 smul_eq_mul
  条件: (M : C) [MonObj M]
  结论: γ[M,M] = μ[M]
  证明: rfl
-/
lemma smul_eq_mul (M : C) [MonObj M] : γ[M,M] = μ[M] := rfl

/-- If `C` acts monoidally on `D`, then every object of `D` is canonically a
module over the trivial monoid. -/
@[to_additive (attr := simps) /-- If `C` acts monoidally on `D`, then every object of `D` is
canonically an additive module over the trivial additive monoid. -/]
instance (X : D) : ModObj (𝟙_ C) X where
  smul := (funₗ _).hom

@[to_additive (attr := ext)]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {X : C} (h₁ h₂ : ModObj M X) (H : h₁.smul = h₂.smul)
  proof: by
  cases h₁
  cases h₂
  subst H
  rfl

中文:
定理 ext
  条件: {X : C} (h₁ h₂ : ModObj M X) (H : h₁.smul = h₂.smul)
  证明: by
  cases h₁
  cases h₂
  subst H
  rfl
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
/--
Definition of `ofIso` / `ofIso` 的定义

English:
definition ofIso
  signature: {X : D} {N : C} [MonObj N] (e₁ : M ≅ N) [IsMonHom e₁.hom]
  body: (e₁.inv ⊙ₗₘ e₂.inv) ≫ γ ≫ e₂.hom
  one_smul := by
    have : η ⊵ₗ Y ≫ (e₁.inv ⊙ₗₘ e₂.inv) = _ ⊴ₗ e₂.inv ≫ (η ≫ e₁.inv) ⊵ₗ X := by
      rw [actionHom_def']; rw [comp_actionHomLeft]; rw [action_exchange_assoc]
    simp [reassoc_of% this]
  mul_smul := by
    have : μ[N] ⊵ₗ Y ≫ (e₁.inv ⊙ₗₘ e₂.inv) =
        ((e₁.inv otimesₘ e₁.inv) ⊙ₗₘ e₂.inv) ≫ μ[M] ⊵ₗ X := by
      rw [actionHom_def']; rw [action_exchange]; rw [← comp_actionHomLeft_assoc]; rw [IsMonHom.mul_hom]; rw [comp_actionHomLeft]; rw [Category.assoc]; rw [← action_exchange]; rw [actionHom_def']
      nth_rw 2 [action_exchange]
      rw [Category.assoc]
    rw [reassoc_of% this]
    have : (αₗ N M X).inv ≫ (e₁.inv ▷ M) ⊵ₗ X ≫ (αₗ M M X).hom ≫ M ⊴ₗ smul =
        N ⊴ₗ γ ≫ e₁.inv ⊵ₗ X := by
      rw [← actionHomLeft_action_assoc]; rw [action_exchange]
    simp [tensorHom_def', actionHom_def', mul_smul_assoc, reassoc_of% this]

中文:
定义 ofIso
  签名: {X : D} {N : C} [MonObj N] (e₁ : M ≅ N) [是幺半群态射 e₁.hom]
  定义体: (e₁.inv ⊙ₗₘ e₂.inv) ≫ γ ≫ e₂.hom
  one_smul := by
    have : η ⊵ₗ Y ≫ (e₁.inv ⊙ₗₘ e₂.inv) = _ ⊴ₗ e₂.inv ≫ (η ≫ e₁.inv) ⊵ₗ X := by
      rw [actionHom_def']; rw [comp_actionHomLeft]; rw [action_exchange_assoc]
    simp [reassoc_of% this]
  mul_smul := by
    have : μ[N] ⊵ₗ Y ≫ (e₁.inv ⊙ₗₘ e₂.inv) =
        ((e₁.inv otimesₘ e₁.inv) ⊙ₗₘ e₂.inv) ≫ μ[M] ⊵ₗ X := by
      rw [actionHom_def']; rw [action_exchange]; rw [← comp_actionHomLeft_assoc]; rw [IsMonHom.mul_hom]; rw [comp_actionHomLeft]; rw [Category.assoc]; rw [← action_exchange]; rw [actionHom_def']
      nth_rw 2 [action_exchange]
      rw [Category.assoc]
    rw [reassoc_of% this]
    have : (αₗ N M X).inv ≫ (e₁.inv ▷ M) ⊵ₗ X ≫ (αₗ M M X).hom ≫ M ⊴ₗ smul =
        N ⊴ₗ γ ≫ e₁.inv ⊵ₗ X := by
      rw [← actionHomLeft_action_assoc]; rw [action_exchange]
    simp [tensorHom_def', actionHom_def', mul_smul_assoc, reassoc_of% this]
-/
def ofIso {X : D} {N : C} [MonObj N] (e₁ : M ≅ N) [IsMonHom e₁.hom]
      {Y : D} (e₂ : X ≅ Y) [ModObj M X] :
    ModObj N Y where
  smul := (e₁.inv ⊙ₗₘ e₂.inv) ≫ γ ≫ e₂.hom
  one_smul := by
    have : η ⊵ₗ Y ≫ (e₁.inv ⊙ₗₘ e₂.inv) = _ ⊴ₗ e₂.inv ≫ (η ≫ e₁.inv) ⊵ₗ X := by
      rw [actionHom_def']; rw [comp_actionHomLeft]; rw [action_exchange_assoc]
    simp [reassoc_of% this]
  mul_smul := by
    have : μ[N] ⊵ₗ Y ≫ (e₁.inv ⊙ₗₘ e₂.inv) =
        ((e₁.inv otimesₘ e₁.inv) ⊙ₗₘ e₂.inv) ≫ μ[M] ⊵ₗ X := by
      rw [actionHom_def']; rw [action_exchange]; rw [← comp_actionHomLeft_assoc]; rw [IsMonHom.mul_hom]; rw [comp_actionHomLeft]; rw [Category.assoc]; rw [← action_exchange]; rw [actionHom_def']
      nth_rw 2 [action_exchange]
      rw [Category.assoc]
    rw [reassoc_of% this]
    have : (αₗ N M X).inv ≫ (e₁.inv ▷ M) ⊵ₗ X ≫ (αₗ M M X).hom ≫ M ⊴ₗ smul =
        N ⊴ₗ γ ≫ e₁.inv ⊵ₗ X := by
      rw [← actionHomLeft_action_assoc]; rw [action_exchange]
    simp [tensorHom_def', actionHom_def', mul_smul_assoc, reassoc_of% this]

section SelfAction

variable (X : C) [ModObj M X]

@[to_additive (attr := reassoc (attr := simp))]
/--
lemma `one_smul_self` / 引理 `one_smul_self`

English:
lemma one_smul_self
  given: (M : C) [MonObj M] (X : C) [ModObj M X]
  proof: ModObj.one_smul (M := M) X

@[to_additive (attr := reassoc (attr := simp))]

中文:
引理 one_smul_self
  条件: (M : C) [MonObj M] (X : C) [ModObj M X]
  证明: ModObj.one_smul (M := M) X

@[to_additive (attr := reassoc (attr := simp))]

Depends on / 依赖: ModObj, ModObj.one_smul, one_smul
-/
lemma one_smul_self (M : C) [MonObj M] (X : C) [ModObj M X] :
    η ▷ X ≫ γ[M, X] = (fun_ X).hom :=
  ModObj.one_smul (M := M) X

@[to_additive (attr := reassoc (attr := simp))]
/--
lemma `mul_smul_self` / 引理 `mul_smul_self`

English:
lemma mul_smul_self
  given: (M : C) [MonObj M] (X : C) [ModObj M X]
  proof: ModObj.mul_smul (M := M) X

@[to_additive (attr := reassoc)]

中文:
引理 mul_smul_self
  条件: (M : C) [MonObj M] (X : C) [ModObj M X]
  证明: ModObj.mul_smul (M := M) X

@[to_additive (attr := reassoc)]

Depends on / 依赖: ModObj, ModObj.mul_smul, mul_smul
-/
lemma mul_smul_self (M : C) [MonObj M] (X : C) [ModObj M X] :
    (μ ▷ X) ≫ γ[M, X] = (α_ _ _ _).hom ≫ (M ◁ γ[M, X]) ≫ γ[M, X] :=
  ModObj.mul_smul (M := M) X

@[to_additive (attr := reassoc)]
/--
theorem `mul_smul_self_flip` / 定理 `mul_smul_self_flip`

English:
theorem mul_smul_self_flip
  statement: M ◁ γ[M, X] ≫ γ[M, X] = (α_ M M X).inv ≫ (μ ▷ X) ≫ γ[M, X]
  proof: by
  simp

中文:
定理 mul_smul_self_flip
  结论: M ◁ γ[M, X] ≫ γ[M, X] = (α_ M M X).inv ≫ (μ ▷ X) ≫ γ[M, X]
  证明: by
  simp
-/
theorem mul_smul_self_flip : M ◁ γ[M, X] ≫ γ[M, X] = (α_ M M X).inv ≫ (μ ▷ X) ≫ γ[M, X] := by
  simp

end SelfAction

end ModObj

end ModObj

open scoped ModObj MonoidalLeftAction

variable {M' N' O' : D}

open AddMonObj in
/--
Definition of `IsAddModHom` / `IsAddModHom` 的定义

English:
class IsAddModHom
  parameters: (A : C) [AddMonObj A] [AddModObj A M'] [AddModObj A N'] (f : M' ⟶ N')
  axioms and operations (1):
    - vadd_hom : δ[M'] ≫ f = A ⊴ₗ f ≫ δ[N']  [default: by cat_disch]

中文:
类 是加法取模态射
  参数: (A : C) [加法MonObj A] [加法ModObj A M'] [加法ModObj A N'] (f : M' ⟶ N')
  公理与运算 (1 个):
    - vadd_hom : δ[M'] ≫ f = A ⊴ₗ f ≫ δ[N']  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
class IsAddModHom (A : C) [AddMonObj A] [AddModObj A M'] [AddModObj A N'] (f : M' ⟶ N') where
  vadd_hom : δ[M'] ≫ f = A ⊴ₗ f ≫ δ[N'] := by cat_disch

variable (A : C) [MonObj A]
/-- A morphism in `D` is a morphism of `A`-module objects if it commutes with
the action maps -/
@[to_additive]
/--
Definition of `IsModHom` / `IsModHom` 的定义

English:
class IsModHom
  parameters: {M N : D} [ModObj A M] [ModObj A N] (f : M ⟶ N)
  axioms and operations (1):
    - smul_hom : γ[M] ≫ f = A ⊴ₗ f ≫ γ[N]  [default: by cat_disch]

中文:
类 是取模态射
  参数: {M N : D} [ModObj A M] [ModObj A N] (f : M ⟶ N)
  公理与运算 (1 个):
    - smul_hom : γ[M] ≫ f = A ⊴ₗ f ≫ γ[N]  [默认: by cat_disch]

Depends on / 依赖: cat_disch
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
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsModHom A (𝟙 M)

中文:
实例 :
  签名: 是取模态射 A (𝟙 M)
-/
instance : IsModHom A (𝟙 M) where

@[to_additive]
instance (f : M ⟶ N) (g : N ⟶ O) [IsModHom A f] [IsModHom A g] :
    IsModHom A (f ≫ g) where

@[to_additive]
instance (f : M ≅ N) [IsModHom A f.hom] :
    IsModHom A f.inv where
  smul_hom := by simp [Iso.comp_inv_eq]

variable (D) in
/--
Definition of `AddMod` / `AddMod` 的定义

English:
structure AddMod
  parameters: (A : C) [AddMonObj A]
  axioms and operations (2):
    - X : D
    - [addMod : AddModObj A X]

中文:
结构 加法取模
  参数: (A : C) [加法MonObj A]
  公理与运算 (2 个):
    - X : D
    - [addMod : 加法ModObj A X]
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
/--
Definition of `Mod` / `Mod` 的定义

English:
structure Mod
  parameters: (A : C) [MonObj A]
  axioms and operations (2):
    - X : D
    - [mod : ModObj A X]

中文:
结构 取模
  参数: (A : C) [MonObj A]
  公理与运算 (2 个):
    - X : D
    - [mod : ModObj A X]
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
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (M N : AddMod D A)
  axioms and operations (2):
    - hom : M.X ⟶ N.X
    - [isAddModHom : IsAddModHom A hom]

中文:
结构 态射
  参数: (M N : 加法取模 D A)
  公理与运算 (2 个):
    - hom : M.X ⟶ N.X
    - [isAddModHom : 是加法取模态射 A hom]
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
/--
theorem `assoc_flip` / 定理 `assoc_flip`

English:
theorem assoc_flip
  statement: A ⊴ₗ γ ≫ γ = (αₗ A A M.X).inv ≫ μ ⊵ₗ M.X ≫ γ
  proof: by simp

中文:
定理 assoc_flip
  结论: A ⊴ₗ γ ≫ γ = (αₗ A A M.X).inv ≫ μ ⊵ₗ M.X ≫ γ
  证明: by simp
-/
theorem assoc_flip : A ⊴ₗ γ ≫ γ = (αₗ A A M.X).inv ≫ μ ⊵ₗ M.X ≫ γ := by simp

/-- A morphism of module objects. -/
@[ext, to_additive existing]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (M N : Mod D A)
  axioms and operations (2):
    - hom : M.X ⟶ N.X
    - [isModHom : IsModHom A hom]

中文:
结构 态射
  参数: (M N : 取模 D A)
  公理与运算 (2 个):
    - hom : M.X ⟶ N.X
    - [isModHom : 是取模态射 A hom]
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
/--
Definition of `Hom.mk'` / `Hom.mk'` 的定义

English:
definition Hom.mk'
  signature: {M N : Mod D A} (f : M.X ⟶ N.X)
  body: letI : IsModHom A f := ⟨smul_hom⟩
  ⟨f⟩

中文:
定义 态射.mk'
  签名: {M N : 取模 D A} (f : M.X ⟶ N.X)
  定义体: letI : IsModHom A f := ⟨smul_hom⟩
  ⟨f⟩
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
/--
Definition of `Hom.mk''` / `Hom.mk''` 的定义

English:
definition Hom.mk''
  signature: {M N : D} [ModObj A M] [ModObj A N] (f : M ⟶ N)
  body: letI : IsModHom A f := ⟨smul_hom⟩
  ⟨f⟩

中文:
定义 态射.mk''
  签名: {M N : D} [ModObj A M] [ModObj A N] (f : M ⟶ N)
  定义体: letI : IsModHom A f := ⟨smul_hom⟩
  ⟨f⟩

Depends on / 依赖: IsModHom, cat_disch, smul_hom
-/
def Hom.mk'' {M N : D} [ModObj A M] [ModObj A N] (f : M ⟶ N)
    (smul_hom : γ[M] ≫ f = A ⊴ₗ f ≫ γ[N] := by cat_disch) :
    Hom (.mk (A := A) M) (.mk (A := A) N) :=
  letI : IsModHom A f := ⟨smul_hom⟩
  ⟨f⟩

/-- The identity morphism on a module object. -/
@[to_additive (attr := simps) /-- The identity morphism on an additive module object. -/]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: (M : Mod D A)
  body: 𝟙 M.X

@[to_additive]

中文:
定义 id
  签名: (M : 取模 D A)
  定义体: 𝟙 M.X

@[to_additive]
-/
def id (M : Mod D A) : Hom M M where hom := 𝟙 M.X

@[to_additive]
/--
Instance `homInhabited` / 实例 `homInhabited`

English:
instance homInhabited
  signature: (M : Mod D A)
  body: ⟨id M⟩

中文:
实例 homInhabited
  签名: (M : 取模 D A)
  定义体: ⟨id M⟩
-/
instance homInhabited (M : Mod D A) : Inhabited (Hom M M) :=
  ⟨id M⟩

/-- Composition of module object morphisms. -/
@[to_additive (attr := simps) /-- Composition of additive module object morphisms. -/]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: {M N O : Mod D A} (f : Hom M N) (g : Hom N O)
  body: f.hom ≫ g.hom

@[to_additive]

中文:
定义 comp
  签名: {M N O : 取模 D A} (f : 态射 M N) (g : 态射 N O)
  定义体: f.hom ≫ g.hom

@[to_additive]

Depends on / 依赖: f.hom, g.hom
-/
def comp {M N O : Mod D A} (f : Hom M N) (g : Hom N O) :
    Hom M O where
  hom := f.hom ≫ g.hom

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (Mod D A)
  body: Hom M N
  id := id
  comp f g := comp f g

@[to_additive (attr := ext)]

中文:
实例 :
  签名: 范畴 (取模 D A)
  定义体: Hom M N
  id := id
  comp f g := comp f g

@[to_additive (attr := ext)]
-/
instance : Category (Mod D A) where
  Hom M N := Hom M N
  id := id
  comp f g := comp f g

@[to_additive (attr := ext)]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {M N : Mod D A} (f₁ f₂ : M ⟶ N) (h : f₁.hom = f₂.hom)
  proof: Hom.ext h

@[to_additive (attr := simp)]

中文:
引理 hom_ext
  条件: {M N : 取模 D A} (f₁ f₂ : M ⟶ N) (h : f₁.hom = f₂.hom)
  证明: Hom.ext h

@[to_additive (attr := simp)]

Depends on / 依赖: Hom.ext
-/
lemma hom_ext {M N : Mod D A} (f₁ f₂ : M ⟶ N) (h : f₁.hom = f₂.hom) :
    f₁ = f₂ :=
  Hom.ext h

@[to_additive (attr := simp)]
/--
theorem `id_hom'` / 定理 `id_hom'`

English:
theorem id_hom'
  given: (M : Mod D A)
  statement: (𝟙 M : M ⟶ M).hom = 𝟙 M.X
  proof: by
  rfl

@[to_additive (attr := simp)]

中文:
定理 id_hom'
  条件: (M : 取模 D A)
  结论: (𝟙 M : M ⟶ M).hom = 𝟙 M.X
  证明: by
  rfl

@[to_additive (attr := simp)]
-/
theorem id_hom' (M : Mod D A) : (𝟙 M : M ⟶ M).hom = 𝟙 M.X := by
  rfl

@[to_additive (attr := simp)]
/--
theorem `comp_hom'` / 定理 `comp_hom'`

English:
theorem comp_hom'
  given: {M N K : Mod D A} (f : M ⟶ N) (g : N ⟶ K)
  proof: rfl

中文:
定理 comp_hom'
  条件: {M N K : 取模 D A} (f : M ⟶ N) (g : N ⟶ K)
  证明: rfl
-/
theorem comp_hom' {M N K : Mod D A} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

variable (A)

/-- A monoid object as a module over itself. -/
@[to_additive (attr := simps) /-- An additive monoid object as an additive module over itself. -/]
/--
Definition of `regular` / `regular` 的定义

English:
definition regular
  signature: : Mod C A
  body: letI : ModObj A A := .regular A
  ⟨A⟩

@[to_additive]

中文:
定义 regular
  签名: : 取模 C A
  定义体: letI : ModObj A A := .regular A
  ⟨A⟩

@[to_additive]

Depends on / 依赖: ModObj, regular
-/
def regular : Mod C A :=
  letI : ModObj A A := .regular A
  ⟨A⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Mod C A)
  body: ⟨regular A⟩

中文:
实例 :
  签名: 可居 (取模 C A)
  定义体: ⟨regular A⟩

Depends on / 依赖: regular
-/
instance : Inhabited (Mod C A) :=
  ⟨regular A⟩

/-- The forgetful functor from module objects to the ambient category. -/
@[to_additive (attr := simps)
  /-- The forgetful functor from additive module objects to the ambient category. -/]
/--
Definition of `forget` / `forget` 的定义

English:
definition forget
  signature: : Mod D A ⥤ D where
  body: A.X
  map f := f.hom

中文:
定义 forget
  签名: : 取模 D A ⥤ D where
  定义体: A.X
  map f := f.hom
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
/--
Definition of `scalarRestriction` / `scalarRestriction` 的定义

English:
definition scalarRestriction
  signature: (M : D) [ModObj B M]
  body: f ⊵ₗ M ≫ γ[B,M]
  one_smul := by
    rw [← comp_actionHomLeft_assoc]
    rw [IsMonHom.one_hom]; rw [ModObj.one_smul]
  mul_smul := by
    -- oh, for homotopy.io in a widget!
    slice_rhs 2 3 => rw [action_exchange]
    simp only [actionHomLeft_action_assoc, Category.assoc, Iso.hom_inv_id_assoc,
      actionHomRight_comp]
    slice_rhs 4 6 => rw [ModObj.assoc_flip]
    slice_rhs 2 4 => rw [← whiskerLeft_actionHomLeft]
    slice_rhs 1 2 => rw [← comp_actionHomLeft]
    rw [← comp_actionHomLeft]; rw [Category.assoc]; rw [← comp_actionHomLeft_assoc]; rw [IsMonHom.mul_hom]; rw [tensorHom_def]; rw [Category.assoc]

中文:
定义 scalarRestriction
  签名: (M : D) [ModObj B M]
  定义体: f ⊵ₗ M ≫ γ[B,M]
  one_smul := by
    rw [← comp_actionHomLeft_assoc]
    rw [IsMonHom.one_hom]; rw [ModObj.one_smul]
  mul_smul := by
    -- oh, for homotopy.io in a widget!
    slice_rhs 2 3 => rw [action_exchange]
    simp only [actionHomLeft_action_assoc, Category.assoc, Iso.hom_inv_id_assoc,
      actionHomRight_comp]
    slice_rhs 4 6 => rw [ModObj.assoc_flip]
    slice_rhs 2 4 => rw [← whiskerLeft_actionHomLeft]
    slice_rhs 1 2 => rw [← comp_actionHomLeft]
    rw [← comp_actionHomLeft]; rw [Category.assoc]; rw [← comp_actionHomLeft_assoc]; rw [IsMonHom.mul_hom]; rw [tensorHom_def]; rw [Category.assoc]
-/
def scalarRestriction (M : D) [ModObj B M] : ModObj A M where
  smul := f ⊵ₗ M ≫ γ[B,M]
  one_smul := by
    rw [← comp_actionHomLeft_assoc]
    rw [IsMonHom.one_hom]; rw [ModObj.one_smul]
  mul_smul := by
    -- oh, for homotopy.io in a widget!
    slice_rhs 2 3 => rw [action_exchange]
    simp only [actionHomLeft_action_assoc, Category.assoc, Iso.hom_inv_id_assoc,
      actionHomRight_comp]
    slice_rhs 4 6 => rw [ModObj.assoc_flip]
    slice_rhs 2 4 => rw [← whiskerLeft_actionHomLeft]
    slice_rhs 1 2 => rw [← comp_actionHomLeft]
    rw [← comp_actionHomLeft]; rw [Category.assoc]; rw [← comp_actionHomLeft_assoc]; rw [IsMonHom.mul_hom]; rw [tensorHom_def]; rw [Category.assoc]

open MonoidalLeftAction in
/-- If `g : M ⟶ N` is a `B`-linear morphism of `B`-modules, then it induces an
`A`-linear morphism when `M` and `N` have an `A`-module structure obtained
by restricting scalars along a monoid morphism `A ⟶ B`. -/
@[to_additive
  /-- If `g : M ⟶ N` is a `B`-linear morphism of `B`-modules, then it induces an
  `A`-linear morphism when `M` and `N` have an `A`-module structure obtained
  by restricting scalars along an additive monoid morphism `A ⟶ B`. -/]
/--
lemma `scalarRestriction_hom` / 引理 `scalarRestriction_hom`

English:
lemma scalarRestriction_hom
  proof: scalarRestriction f M
    letI := scalarRestriction f N
    IsModHom A g :=
  letI := scalarRestriction f M
  letI := scalarRestriction f N
  { smul_hom := by
      simpa using (action_exchange_assoc f g γ).symm }

中文:
引理 scalarRestriction_hom
  证明: scalarRestriction f M
    letI := scalarRestriction f N
    IsModHom A g :=
  letI := scalarRestriction f M
  letI := scalarRestriction f N
  { smul_hom := by
      simpa using (action_exchange_assoc f g γ).symm }

Depends on / 依赖: scalarRestriction
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
/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: {A B : C} [MonObj A] [MonObj B] (f : A ⟶ B) [IsMonHom f]
  body: letI := scalarRestriction f M.X
    ⟨M.X⟩
  map {M N} g :=
    letI := scalarRestriction_hom f M.X N.X g.hom
    ⟨g.hom⟩

中文:
定义 comap
  签名: {A B : C} [MonObj A] [MonObj B] (f : A ⟶ B) [是幺半群态射 f]
  定义体: letI := scalarRestriction f M.X
    ⟨M.X⟩
  map {M N} g :=
    letI := scalarRestriction_hom f M.X N.X g.hom
    ⟨g.hom⟩

Depends on / 依赖: g.hom, scalarRestriction, scalarRestriction_hom
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
