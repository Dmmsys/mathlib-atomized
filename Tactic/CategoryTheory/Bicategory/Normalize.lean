/-
Copyright (c) 2024 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public meta import Mathlib.Tactic.CategoryTheory.Bicategory.Datatypes
public import Mathlib.Tactic.CategoryTheory.Bicategory.Datatypes
public import Mathlib.Tactic.CategoryTheory.Coherence.Normalize

/-!
# Normalization of 2-morphisms in bicategories

This file provides the implementation of the normalization given in
`Mathlib/Tactic/CategoryTheory/Coherence/Normalize.lean`. See this file for more details.

-/

public meta section

open Lean Meta Elab Qq
open CategoryTheory Mathlib.Tactic.BicategoryLike Bicategory

namespace Mathlib.Tactic.Bicategory

section

universe w v u

variable {B : Type u} [Bicategory.{w, v} B]

variable {a b c d : B}
variable {f f' g g' h i j : a ⟶ b}

@[nolint synTaut]
/-
**Mathlib.Tactic.Bicategory.evalComp_nil_nil** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.
Tactic.Bicategory`。
形式化陈述：evalComp_nil_nil (α : f ≅ g) (β : g ≅ h) : (α ≪≫ β).hom = (α ≪≫ β).hom
参数：α : f ≅ g；β : g ≅ h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem evalComp_nil_nil (α : f ≅ g) (β : g ≅ h) :
    (α ≪≫ β).hom = (α ≪≫ β).hom := by
  simp
/-
**Mathlib.Tactic.Bicategory.evalComp_nil_cons** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib
.Tactic.Bicategory`。
形式化陈述：evalComp_nil_cons (α : f ≅ g) (β : g ≅ h) (η : h ⟶ i) (ηs : i ⟶ j) : α.hom
 ≫ (β.hom ≫ η ≫ ηs) = (α ≪≫ β).hom ≫ η ≫ ηs
参数：α : f ≅ g；β : g ≅ h；η : h ⟶ i；ηs : i ⟶ j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem evalComp_nil_cons (α : f ≅ g) (β : g ≅ h) (η : h ⟶ i) (ηs : i ⟶ j) :
    α.hom ≫ (β.hom ≫ η ≫ ηs) = (α ≪≫ β).hom ≫ η ≫ ηs := by
  simp
/-
**Mathlib.Tactic.Bicategory.evalComp_cons** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tac
tic.Bicategory`。
形式化陈述：evalComp_cons (α : f ≅ g) (η : g ⟶ h) {ηs : h ⟶ i} {θ : i ⟶ j} {ι : h ⟶ j}
 (e_ι : ηs ≫ θ = ι) : (α.hom ≫ η ≫ ηs) ≫ θ = α.hom ≫ η ≫ ι
参数：α : f ≅ g；η : g ⟶ h；e_ι : ηs ≫ θ = ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
theorem evalComp_cons (α : f ≅ g) (η : g ⟶ h) {ηs : h ⟶ i} {θ : i ⟶ j} {ι : h ⟶ j}
    (e_ι : ηs ≫ θ = ι) :
    (α.hom ≫ η ≫ ηs) ≫ θ = α.hom ≫ η ≫ ι := by
  simp [e_ι]
/-
**Mathlib.Tactic.Bicategory.eval_comp** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.
Bicategory`。
形式化陈述：eval_comp {η η' : f ⟶ g} {θ θ' : g ⟶ h} {ι : f ⟶ h} (e_η : η = η') (e_θ : 
θ = θ') (e_ηθ : η' ≫ θ' = ι) : η ≫ θ = ι
参数：e_η : η = η'；e_θ : θ = θ'；e_ηθ : η' ≫ θ' = ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eval_comp
    {η η' : f ⟶ g} {θ θ' : g ⟶ h} {ι : f ⟶ h}
    (e_η : η = η') (e_θ : θ = θ') (e_ηθ : η' ≫ θ' = ι) :
    η ≫ θ = ι := by
  simp [e_η, e_θ, e_ηθ]
/-
**Mathlib.Tactic.Bicategory.eval_of** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.Bi
category`。
形式化陈述：eval_of (η : f ⟶ g) : η = (Iso.refl _).hom ≫ η ≫ (Iso.refl _).hom
参数：η : f ⟶ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
theorem eval_of (η : f ⟶ g) :
    η = (Iso.refl _).hom ≫ η ≫ (Iso.refl _).hom := by
  simp
/-
**Mathlib.Tactic.Bicategory.eval_monoidalComp** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib
.Tactic.Bicategory`。
形式化陈述：eval_monoidalComp {η η' : f ⟶ g} {α : g ≅ h} {θ θ' : h ⟶ i} {αθ : g ⟶ i} {
ηαθ : f ⟶ i} (e_η : η = η') (e_θ : θ = θ') (e_αθ : α.hom ≫ θ' = αθ) (e_ηαθ : η' 
≫ αθ = ηαθ) : η ≫ α.hom ≫ θ = ηαθ
参数：e_η : η = η'；e_θ : θ = θ'；e_αθ : α.hom ≫ θ' = αθ；e_ηαθ : η' ≫ αθ = ηαθ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eval_monoidalComp
    {η η' : f ⟶ g} {α : g ≅ h} {θ θ' : h ⟶ i} {αθ : g ⟶ i} {ηαθ : f ⟶ i}
    (e_η : η = η') (e_θ : θ = θ') (e_αθ : α.hom ≫ θ' = αθ) (e_ηαθ : η' ≫ αθ = ηαθ) :
    η ≫ α.hom ≫ θ = ηαθ := by
  simp [e_η, e_θ, e_αθ, e_ηαθ]

@[nolint synTaut]
/-
**Mathlib.Tactic.Bicategory.evalWhiskerLeft_nil** 是 Mathlib 中的一个定理，位于命名空间 `Mathl
ib.Tactic.Bicategory`。
形式化陈述：evalWhiskerLeft_nil (f : a ⟶ b) {g h : b ⟶ c} (α : g ≅ h) : (whiskerLeftIs
o f α).hom = (whiskerLeftIso f α).hom
参数：f : a ⟶ b；α : g ≅ h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Bicategory.whiskerLeftIso_hom`：∀ {B : Type u} [inst : Cat
egoryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h),   (
CategoryTheory.Bicategory.whiskerL…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem evalWhiskerLeft_nil (f : a ⟶ b) {g h : b ⟶ c} (α : g ≅ h) :
    (whiskerLeftIso f α).hom = (whiskerLeftIso f α).hom := by
  simp
/-
**Mathlib.Tactic.Bicategory.evalWhiskerLeft_of_cons** 是 Mathlib 中的一个定理，位于命名空间 `M
athlib.Tactic.Bicategory`。
形式化陈述：evalWhiskerLeft_of_cons {f : a ⟶ b} {g h i j : b ⟶ c} (α : g ≅ h) (η : h ⟶
 i) {ηs : i ⟶ j} {θ : f ≫ i ⟶ f ≫ j} (e_θ : f ◁ ηs = θ) : f ◁ (α.hom ≫ η ≫ ηs) =
 (whiskerLeftIso f α).hom ≫ f ◁ η ≫ θ
参数：α : g ≅ h；η : h ⟶ i；e_θ : f ◁ ηs = θ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Bicategory.whiskerLeft_comp`：∀ {B : Type u} [self : Categ
oryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) {g h i : b ⟶ c} (η : g ⟶ h) (θ :
 h ⟶ i),   CategoryTheory.Bicate…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Bicategory.whiskerLeftIso_hom`：∀ {B : Type u} [inst : Cat
egoryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h),   (
CategoryTheory.Bicategory.whiskerL…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem evalWhiskerLeft_of_cons
    {f : a ⟶ b} {g h i j : b ⟶ c}
    (α : g ≅ h) (η : h ⟶ i) {ηs : i ⟶ j} {θ : f ≫ i ⟶ f ≫ j} (e_θ : f ◁ ηs = θ) :
    f ◁ (α.hom ≫ η ≫ ηs) = (whiskerLeftIso f α).hom ≫ f ◁ η ≫ θ := by
  simp [e_θ]
/-
**Mathlib.Tactic.Bicategory.evalWhiskerLeft_comp** 是 Mathlib 中的一个定理，位于命名空间 `Math
lib.Tactic.Bicategory`。
形式化陈述：evalWhiskerLeft_comp {f : a ⟶ b} {g : b ⟶ c} {h i : c ⟶ d} {η : h ⟶ i} {η₁
 : g ≫ h ⟶ g ≫ i} {η₂ : f ≫ g ≫ h ⟶ f ≫ g ≫ i} {η₃ : f ≫ g ≫ h ⟶ (f ≫ g) ≫ i} {η
₄ : (f ≫ g) ≫ h ⟶ (f ≫ g) ≫ i} (e_η₁ : g ◁ η = η₁) (e_η₂ : f ◁ η₁ = η₂) (e_η₃ : 
η₂ ≫ (α_ _ _ _).inv = η₃) (e_η₄ : (α_ _ _ _).hom ≫ η₃ = η₄) : (f ≫ g) ◁ η = η₄
参数：f ≫ g；f ≫ g；f ≫ g；e_η₁ : g ◁ η = η₁；e_η₂ : f ◁ η₁ = η₂；e_η₃ : η₂ ≫ (α_ _ _ _)
.inv = η₃；e_η₄ : (α_ _ _ _).hom ≫ η₃ = η₄。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Bicategory.comp_whiskerLeft`：∀ {B : Type u} [self : Categ
oryTheory.Bicategory B] {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (η 
: h ⟶ h'),   CategoryTheory.Bica…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem evalWhiskerLeft_comp
    {f : a ⟶ b} {g : b ⟶ c} {h i : c ⟶ d}
    {η : h ⟶ i} {η₁ : g ≫ h ⟶ g ≫ i} {η₂ : f ≫ g ≫ h ⟶ f ≫ g ≫ i}
    {η₃ : f ≫ g ≫ h ⟶ (f ≫ g) ≫ i} {η₄ : (f ≫ g) ≫ h ⟶ (f ≫ g) ≫ i}
    (e_η₁ : g ◁ η = η₁) (e_η₂ : f ◁ η₁ = η₂)
    (e_η₃ : η₂ ≫ (α_ _ _ _).inv = η₃) (e_η₄ : (α_ _ _ _).hom ≫ η₃ = η₄) :
    (f ≫ g) ◁ η = η₄ := by
  simp [e_η₁, e_η₂, e_η₃, e_η₄]
/-
**Mathlib.Tactic.Bicategory.evalWhiskerLeft_id** 是 Mathlib 中的一个定理，位于命名空间 `Mathli
b.Tactic.Bicategory`。
形式化陈述：evalWhiskerLeft_id {η : f ⟶ g} {η₁ : f ⟶ 𝟙 a ≫ g} {η₂ : 𝟙 a ≫ f ⟶ 𝟙 a ≫ g}
 (e_η₁ : η ≫ (fun_ _).inv = η₁) (e_η₂ : (fun_ _).hom ≫ η₁ = η₂) : 𝟙 a ◁ η = η₂
参数：e_η₁ : η ≫ (fun_ _).inv = η₁；e_η₂ : (fun_ _).hom ≫ η₁ = η₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Bicategory.id_whiskerLeft`：∀ {B : Type u} [self : Categor
yTheory.Bicategory B] {a b : B} {f g : a ⟶ b} (η : f ⟶ g),   CategoryTheory.Bica
tegory.whiskerLeft (CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem evalWhiskerLeft_id {η : f ⟶ g}
    {η₁ : f ⟶ 𝟙 a ≫ g} {η₂ : 𝟙 a ≫ f ⟶ 𝟙 a ≫ g}
    (e_η₁ : η ≫ (λ_ _).inv = η₁) (e_η₂ : (λ_ _).hom ≫ η₁ = η₂) :
    𝟙 a ◁ η = η₂ := by
  simp [e_η₁, e_η₂]
/-
**Mathlib.Tactic.Bicategory.eval_whiskerLeft** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.
Tactic.Bicategory`。
形式化陈述：eval_whiskerLeft {f : a ⟶ b} {g h : b ⟶ c} {η η' : g ⟶ h} {θ : f ≫ g ⟶ f ≫
 h} (e_η : η = η') (e_θ : f ◁ η' = θ) : f ◁ η = θ
参数：e_η : η = η'；e_θ : f ◁ η' = θ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eval_whiskerLeft
    {f : a ⟶ b} {g h : b ⟶ c}
    {η η' : g ⟶ h} {θ : f ≫ g ⟶ f ≫ h}
    (e_η : η = η') (e_θ : f ◁ η' = θ) :
    f ◁ η = θ := by
  simp [e_η, e_θ]
/-
**Mathlib.Tactic.Bicategory.eval_whiskerRight** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib
.Tactic.Bicategory`。
形式化陈述：eval_whiskerRight {f g : a ⟶ b} {h : b ⟶ c} {η η' : f ⟶ g} {θ : f ≫ h ⟶ g 
≫ h} (e_η : η = η') (e_θ : η' ▷ h = θ) : η ▷ h = θ
参数：e_η : η = η'；e_θ : η' ▷ h = θ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eval_whiskerRight
    {f g : a ⟶ b} {h : b ⟶ c}
    {η η' : f ⟶ g} {θ : f ≫ h ⟶ g ≫ h}
    (e_η : η = η') (e_θ : η' ▷ h = θ) :
    η ▷ h = θ := by
  simp [e_η, e_θ]

@[nolint synTaut]
/-
**Mathlib.Tactic.Bicategory.evalWhiskerRight_nil** 是 Mathlib 中的一个定理，位于命名空间 `Math
lib.Tactic.Bicategory`。
形式化陈述：evalWhiskerRight_nil (α : f ≅ g) (h : b ⟶ c) : α.hom ▷ h = α.hom ▷ h
参数：α : f ≅ g；h : b ⟶ c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem evalWhiskerRight_nil (α : f ≅ g) (h : b ⟶ c) :
    α.hom ▷ h = α.hom ▷ h := by
  simp
/-
**Mathlib.Tactic.Bicategory.evalWhiskerRightAux_of** 是 Mathlib 中的一个定理，位于命名空间 `Ma
thlib.Tactic.Bicategory`。
形式化陈述：evalWhiskerRightAux_of {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) : η ▷ h = (Is
o.refl _).hom ≫ η ▷ h ≫ (Iso.refl _).hom
参数：η : f ⟶ g；h : b ⟶ c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
theorem evalWhiskerRightAux_of {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) :
    η ▷ h = (Iso.refl _).hom ≫ η ▷ h ≫ (Iso.refl _).hom := by
  simp
/-
**Mathlib.Tactic.Bicategory.evalWhiskerRight_cons_of_of** 是 Mathlib 中的一个定理，位于命名空
间 `Mathlib.Tactic.Bicategory`。
形式化陈述：evalWhiskerRight_cons_of_of {f g h i : a ⟶ b} {j : b ⟶ c} {α : f ≅ g} {η :
 g ⟶ h} {ηs : h ⟶ i} {ηs₁ : h ≫ j ⟶ i ≫ j} {η₁ : g ≫ j ⟶ h ≫ j} {η₂ : g ≫ j ⟶ i 
≫ j} {η₃ : f ≫ j ⟶ i ≫ j} (e_ηs₁ : ηs ▷ j = ηs₁) (e_η₁ : η ▷ j = η₁) (e_η₂ : η₁ 
≫ ηs₁ = η₂) (e_η₃ : (whiskerRightIso α j).hom ≫ η₂ = η₃) : (α.hom ≫ η ≫ ηs) ▷ j 
= η₃
参数：e_ηs₁ : ηs ▷ j = ηs₁；e_η₁ : η ▷ j = η₁；e_η₂ : η₁ ≫ ηs₁ = η₂；e_η₃ : (whiskerRi
ghtIso α j).hom ≫ η₂ = η₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Bicategory.comp_whiskerRight`：∀ {B : Type u} [self : Cate
goryTheory.Bicategory B] {a b c : B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) (i 
: b ⟶ c),   CategoryTheory.Bicate…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Bicategory.whiskerRightIso_hom`：∀ {B : Type u} [inst : Ca
tegoryTheory.Bicategory B] {a b c : B} {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c),   
(CategoryTheory.Bicategory.whiskerR…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem evalWhiskerRight_cons_of_of
    {f g h i : a ⟶ b} {j : b ⟶ c}
    {α : f ≅ g} {η : g ⟶ h} {ηs : h ⟶ i} {ηs₁ : h ≫ j ⟶ i ≫ j}
    {η₁ : g ≫ j ⟶ h ≫ j} {η₂ : g ≫ j ⟶ i ≫ j} {η₃ : f ≫ j ⟶ i ≫ j}
    (e_ηs₁ : ηs ▷ j = ηs₁) (e_η₁ : η ▷ j = η₁)
    (e_η₂ : η₁ ≫ ηs₁ = η₂) (e_η₃ : (whiskerRightIso α j).hom ≫ η₂ = η₃) :
    (α.hom ≫ η ≫ ηs) ▷ j = η₃ := by
  simp_all
/-
**Mathlib.Tactic.Bicategory.evalWhiskerRight_cons_whisker** 是 Mathlib 中的一个定理，位于命
名空间 `Mathlib.Tactic.Bicategory`。
形式化陈述：evalWhiskerRight_cons_whisker {f : a ⟶ b} {g : a ⟶ c} {h i : b ⟶ c} {j : a
 ⟶ c} {k : c ⟶ d} {α : g ≅ f ≫ h} {η : h ⟶ i} {ηs : f ≫ i ⟶ j} {η₁ : h ≫ k ⟶ i ≫
 k} {η₂ : f ≫ (h ≫ k) ⟶ f ≫ (i ≫ k)} {ηs₁ : (f ≫ i) ≫ k ⟶ j ≫ k} {ηs₂ : f ≫ (i ≫
 k) ⟶ j ≫ k} {η₃ : f ≫ (h ≫ k) ⟶ j ≫ k} {η₄ : (f ≫ h) ≫ k ⟶ j ≫ k} {η₅ : g ≫ k ⟶
 j ≫ k} (e_η₁ : ((Iso.refl _).hom ≫ η ≫ (Iso.refl _).hom) ▷ k = η₁) (e_η₂ : f ◁ 
η₁ = η₂) (e_ηs₁ : ηs ▷ k = ηs₁) (e_ηs₂ : (α_ _ _ _).inv ≫ ηs₁ = ηs₂) (e_η₃ : η₂ 
≫ ηs₂ = η₃) (e_η₄ : (α_ _ 
参数：h ≫ k；i ≫ k；f ≫ i；i ≫ k；h ≫ k；f ≫ h；e_η₁ : ((Iso.refl _).hom ≫ η ≫ (Iso.refl 
_).hom) ▷ k = η₁；e_η₂ : f ◁ η₁ = η₂；e_ηs₁ : ηs ▷ k = ηs₁；e_ηs₂ : (α_ _ _ _).inv 
≫ ηs₁ = ηs₂；e_η₃ : η₂ ≫ ηs₂ = η₃。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Bicategory.comp_whiskerRight`：∀ {B : Type u} [self : Cate
goryTheory.Bicategory B] {a b c : B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) (i 
: b ⟶ c),   CategoryTheory.Bicate…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Bicategory.whisker_assoc`：∀ {B : Type u} [self : Category
Theory.Bicategory B] {a b c d : B} (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') (h : 
c ⟶ d),   CategoryTheory.Bica…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Bicategory.whiskerRightIso_hom`：∀ {B : Type u} [inst : Ca
tegoryTheory.Bicategory B] {a b c : B} {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c),   
(CategoryTheory.Bicategory.whiskerR…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem evalWhiskerRight_cons_whisker
    {f : a ⟶ b} {g : a ⟶ c} {h i : b ⟶ c} {j : a ⟶ c} {k : c ⟶ d}
    {α : g ≅ f ≫ h} {η : h ⟶ i} {ηs : f ≫ i ⟶ j}
    {η₁ : h ≫ k ⟶ i ≫ k} {η₂ : f ≫ (h ≫ k) ⟶ f ≫ (i ≫ k)} {ηs₁ : (f ≫ i) ≫ k ⟶ j ≫ k}
    {ηs₂ : f ≫ (i ≫ k) ⟶ j ≫ k} {η₃ : f ≫ (h ≫ k) ⟶ j ≫ k} {η₄ : (f ≫ h) ≫ k ⟶ j ≫ k}
    {η₅ : g ≫ k ⟶ j ≫ k}
    (e_η₁ : ((Iso.refl _).hom ≫ η ≫ (Iso.refl _).hom) ▷ k = η₁) (e_η₂ : f ◁ η₁ = η₂)
    (e_ηs₁ : ηs ▷ k = ηs₁) (e_ηs₂ : (α_ _ _ _).inv ≫ ηs₁ = ηs₂)
    (e_η₃ : η₂ ≫ ηs₂ = η₃) (e_η₄ : (α_ _ _ _).hom ≫ η₃ = η₄)
    (e_η₅ : (whiskerRightIso α k).hom ≫ η₄ = η₅) :
    (α.hom ≫ (f ◁ η) ≫ ηs) ▷ k = η₅ := by
  simp at e_η₁ e_η₅
  simp [e_η₁, e_η₂, e_ηs₁, e_ηs₂, e_η₃, e_η₄, e_η₅]
/-
**Mathlib.Tactic.Bicategory.evalWhiskerRight_comp** 是 Mathlib 中的一个定理，位于命名空间 `Mat
hlib.Tactic.Bicategory`。
形式化陈述：evalWhiskerRight_comp {f f' : a ⟶ b} {g : b ⟶ c} {h : c ⟶ d} {η : f ⟶ f'} 
{η₁ : f ≫ g ⟶ f' ≫ g} {η₂ : (f ≫ g) ≫ h ⟶ (f' ≫ g) ≫ h} {η₃ : (f ≫ g) ≫ h ⟶ f' ≫
 (g ≫ h)} {η₄ : f ≫ (g ≫ h) ⟶ f' ≫ (g ≫ h)} (e_η₁ : η ▷ g = η₁) (e_η₂ : η₁ ▷ h =
 η₂) (e_η₃ : η₂ ≫ (α_ _ _ _).hom = η₃) (e_η₄ : (α_ _ _ _).inv ≫ η₃ = η₄) : η ▷ (
g ≫ h) = η₄
参数：f ≫ g；f' ≫ g；f ≫ g；g ≫ h；g ≫ h；g ≫ h；e_η₁ : η ▷ g = η₁；e_η₂ : η₁ ▷ h = η₂；e_η
₃ : η₂ ≫ (α_ _ _ _).hom = η₃；e_η₄ : (α_ _ _ _).inv ≫ η₃ = η₄。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Bicategory.whiskerRight_comp`：∀ {B : Type u} [self : Cate
goryTheory.Bicategory B] {a b c d : B} {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (
h : c ⟶ d),   CategoryTheory.Bica…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem evalWhiskerRight_comp
    {f f' : a ⟶ b} {g : b ⟶ c} {h : c ⟶ d}
    {η : f ⟶ f'} {η₁ : f ≫ g ⟶ f' ≫ g} {η₂ : (f ≫ g) ≫ h ⟶ (f' ≫ g) ≫ h}
    {η₃ : (f ≫ g) ≫ h ⟶ f' ≫ (g ≫ h)} {η₄ : f ≫ (g ≫ h) ⟶ f' ≫ (g ≫ h)}
    (e_η₁ : η ▷ g = η₁) (e_η₂ : η₁ ▷ h = η₂)
    (e_η₃ : η₂ ≫ (α_ _ _ _).hom = η₃) (e_η₄ : (α_ _ _ _).inv ≫ η₃ = η₄) :
    η ▷ (g ≫ h) = η₄ := by
  simp [e_η₁, e_η₂, e_η₃, e_η₄]
/-
**Mathlib.Tactic.Bicategory.evalWhiskerRight_id** 是 Mathlib 中的一个定理，位于命名空间 `Mathl
ib.Tactic.Bicategory`。
形式化陈述：evalWhiskerRight_id {η : f ⟶ g} {η₁ : f ⟶ g ≫ 𝟙 b} {η₂ : f ≫ 𝟙 b ⟶ g ≫ 𝟙 b
} (e_η₁ : η ≫ (ρ_ _).inv = η₁) (e_η₂ : (ρ_ _).hom ≫ η₁ = η₂) : η ▷ 𝟙 b = η₂
参数：e_η₁ : η ≫ (ρ_ _).inv = η₁；e_η₂ : (ρ_ _).hom ≫ η₁ = η₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Bicategory.whiskerRight_id`：∀ {B : Type u} [self : Catego
ryTheory.Bicategory B] {a b : B} {f g : a ⟶ b} (η : f ⟶ g),   CategoryTheory.Bic
ategory.whiskerRight η (Categor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem evalWhiskerRight_id
    {η : f ⟶ g} {η₁ : f ⟶ g ≫ 𝟙 b} {η₂ : f ≫ 𝟙 b ⟶ g ≫ 𝟙 b}
    (e_η₁ : η ≫ (ρ_ _).inv = η₁) (e_η₂ : (ρ_ _).hom ≫ η₁ = η₂) :
    η ▷ 𝟙 b = η₂ := by
  simp [e_η₁, e_η₂]
/-
**Mathlib.Tactic.Bicategory.eval_bicategoricalComp** 是 Mathlib 中的一个定理，位于命名空间 `Ma
thlib.Tactic.Bicategory`。
形式化陈述：eval_bicategoricalComp {η η' : f ⟶ g} {α : g ≅ h} {θ θ' : h ⟶ i} {αθ : g ⟶
 i} {ηαθ : f ⟶ i} (e_η : η = η') (e_θ : θ = θ') (e_αθ : α.hom ≫ θ' = αθ) (e_ηαθ 
: η' ≫ αθ = ηαθ) : η ≫ α.hom ≫ θ = ηαθ
参数：e_η : η = η'；e_θ : θ = θ'；e_αθ : α.hom ≫ θ' = αθ；e_ηαθ : η' ≫ αθ = ηαθ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eval_bicategoricalComp
    {η η' : f ⟶ g} {α : g ≅ h} {θ θ' : h ⟶ i} {αθ : g ⟶ i} {ηαθ : f ⟶ i}
    (e_η : η = η') (e_θ : θ = θ') (e_αθ : α.hom ≫ θ' = αθ) (e_ηαθ : η' ≫ αθ = ηαθ) :
    η ≫ α.hom ≫ θ = ηαθ := by
  simp [e_η, e_θ, e_αθ, e_ηαθ]

end

open Mor₂Iso

/-
**Mathlib.Tactic.Bicategory.** 是 Mathlib 中的一个实例，位于命名空间 `Mathlib.Tactic.Bicategor
y`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MkEvalComp BicategoryM where
  mkEvalCompNilNil α β := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    let f ← α.srcM
    let g ← α.tgtM
    let h ← β.tgtM
    have a : Q($ctx.B) := f.src.e
    have b : Q($ctx.B) := f.tgt.e
    have f : Q($a ⟶ $b) := f.e
    have g : Q($a ⟶ $b) := g.e
    have h : Q($a ⟶ $b) := h.e
    have α : Q($f ≅ $g) := α.e
    have β : Q($g ≅ $h) := β.e
    return q(evalComp_nil_nil $α $β)
  mkEvalCompNilCons α β η ηs := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    let f ← α.srcM
    let g ← α.tgtM
    let h ← β.tgtM
    let i ← η.tgtM
    let j ← ηs.tgtM
    have a : Q($ctx.B) := f.src.e
    have b : Q($ctx.B) := f.tgt.e
    have f : Q($a ⟶ $b) := f.e
    have g : Q($a ⟶ $b) := g.e
    have h : Q($a ⟶ $b) := h.e
    have i : Q($a ⟶ $b) := i.e
    have j : Q($a ⟶ $b) := j.e
    have α : Q($f ≅ $g) := α.e
    have β : Q($g ≅ $h) := β.e
    have η : Q($h ⟶ $i) := η.e.e
    have ηs : Q($i ⟶ $j) := ηs.e.e
    return q(evalComp_nil_cons $α $β $η $ηs)
  mkEvalCompCons α η ηs θ ι e_ι := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    let f ← α.srcM
    let g ← α.tgtM
    let h ← η.tgtM
    let i ← ηs.tgtM
    let j ← θ.tgtM
    have a : Q($ctx.B) := f.src.e
    have b : Q($ctx.B) := f.tgt.e
    have f : Q($a ⟶ $b) := f.e
    have g : Q($a ⟶ $b) := g.e
    have h : Q($a ⟶ $b) := h.e
    have i : Q($a ⟶ $b) := i.e
    have j : Q($a ⟶ $b) := j.e
    have α : Q($f ≅ $g) := α.e
    have η : Q($g ⟶ $h) := η.e.e
    have ηs : Q($h ⟶ $i) := ηs.e.e
    have θ : Q($i ⟶ $j) := θ.e.e
    have ι : Q($h ⟶ $j) := ι.e.e
    have e_ι : Q($ηs ≫ $θ = $ι) := e_ι
    return q(evalComp_cons $α $η $e_ι)
/-
**Mathlib.Tactic.Bicategory.** 是 Mathlib 中的一个实例，位于命名空间 `Mathlib.Tactic.Bicategor
y`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MkEvalWhiskerLeft BicategoryM where
  mkEvalWhiskerLeftNil f α := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    let g ← α.srcM
    let h ← α.tgtM
    have a : Q($ctx.B) := f.src.e
    have b : Q($ctx.B) := f.tgt.e
    have c : Q($ctx.B) := g.tgt.e
    have f : Q($a ⟶ $b) := f.e
    have g : Q($b ⟶ $c) := g.e
    have h : Q($b ⟶ $c) := h.e
    have α : Q($g ≅ $h) := α.e
    return q(evalWhiskerLeft_nil $f $α)
  mkEvalWhiskerLeftOfCons f α η ηs θ e_θ := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    let g ← α.srcM
    let h ← α.tgtM
    let i ← η.tgtM
    let j ← ηs.tgtM
    have a : Q($ctx.B) := f.src.e
    have b : Q($ctx.B) := f.tgt.e
    have c : Q($ctx.B) := g.tgt.e
    have f : Q($a ⟶ $b) := f.e
    have g : Q($b ⟶ $c) := g.e
    have h : Q($b ⟶ $c) := h.e
    have i : Q($b ⟶ $c) := i.e
    have j : Q($b ⟶ $c) := j.e
    have α : Q($g ≅ $h) := α.e
    have η : Q($h ⟶ $i) := η.e.e
    have ηs : Q($i ⟶ $j) := ηs.e.e
    have θ : Q($f ≫ $i ⟶ $f ≫ $j) := θ.e.e
    have e_θ : Q($f ◁ $ηs = $θ) := e_θ
    return q(evalWhiskerLeft_of_cons $α $η $e_θ)
  mkEvalWhiskerLeftComp f g η η₁ η₂ η₃ η₄ e_η₁ e_η₂ e_η₃ e_η₄ := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    let h ← η.srcM
    let i ← η.tgtM
    have a : Q($ctx.B) := f.src.e
    have b : Q($ctx.B) := f.tgt.e
    have c : Q($ctx.B) := g.tgt.e
    have d : Q($ctx.B) := h.tgt.e
    have f : Q($a ⟶ $b) := f.e
    have g : Q($b ⟶ $c) := g.e
    have h : Q($c ⟶ $d) := h.e
    have i : Q($c ⟶ $d) := i.e
    have η : Q($h ⟶ $i) := η.e.e
    have η₁ : Q($g ≫ $h ⟶ $g ≫ $i) := η₁.e.e
    have η₂ : Q($f ≫ $g ≫ $h ⟶ $f ≫ $g ≫ $i) := η₂.e.e
    have η₃ : Q($f ≫ $g ≫ $h ⟶ ($f ≫ $g) ≫ $i) := η₃.e.e
    have η₄ : Q(($f ≫ $g) ≫ $h ⟶ ($f ≫ $g) ≫ $i) := η₄.e.e
    have e_η₁ : Q($g ◁ $η = $η₁) := e_η₁
    have e_η₂ : Q($f ◁ $η₁ = $η₂) := e_η₂
    have e_η₃ : Q($η₂ ≫ (α_ _ _ _).inv = $η₃) := e_η₃
    have e_η₄ : Q((α_ _ _ _).hom ≫ $η₃ = $η₄) := e_η₄
    return q(evalWhiskerLeft_comp $e_η₁ $e_η₂ $e_η₃ $e_η₄)
  mkEvalWhiskerLeftId η η₁ η₂ e_η₁ e_η₂ := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    let f ← η.srcM
    let g ← η.tgtM
    have a : Q($ctx.B) := f.src.e
    have b : Q($ctx.B) := f.tgt.e
    have f : Q($a ⟶ $b) := f.e
    have g : Q($a ⟶ $b) := g.e
    have η : Q($f ⟶ $g) := η.e.e
    have η₁ : Q($f ⟶ 𝟙 $a ≫ $g) := η₁.e.e
    have η₂ : Q(𝟙 $a ≫ $f ⟶ 𝟙 $a ≫ $g) := η₂.e.e
    have e_η₁ : Q($η ≫ (λ_ _).inv = $η₁) := e_η₁
    have e_η₂ : Q((λ_ _).hom ≫ $η₁ = $η₂) := e_η₂
    return q(evalWhiskerLeft_id $e_η₁ $e_η₂)
/-
**Mathlib.Tactic.Bicategory.** 是 Mathlib 中的一个实例，位于命名空间 `Mathlib.Tactic.Bicategor
y`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MkEvalWhiskerRight BicategoryM where
  mkEvalWhiskerRightAuxOf η h := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    let f ← η.srcM
    let g ← η.tgtM
    have a : Q($ctx.B) := f.src.e
    have b : Q($ctx.B) := f.tgt.e
    have c : Q($ctx.B) := h.tgt.e
    have f : Q($a ⟶ $b) := f.e
    have g : Q($a ⟶ $b) := g.e
    have h : Q($b ⟶ $c) := h.e
    have η : Q($f ⟶ $g) := η.e.e
    return q(evalWhiskerRightAux_of $η $h)
  mkEvalWhiskerRightAuxCons _ _ _ _ _ _ _ _ _ _ _ := do
    throwError "not implemented"
  mkEvalWhiskerRightNil α h := do
      let ctx ← read
      let _bicat := ctx.instBicategory
      let f ← α.srcM
      let g ← α.tgtM
      have a : Q($ctx.B) := f.src.e
      have b : Q($ctx.B) := f.tgt.e
      have c : Q($ctx.B) := h.tgt.e
      have f : Q($a ⟶ $b) := f.e
      have g : Q($a ⟶ $b) := g.e
      have h : Q($b ⟶ $c) := h.e
      have α : Q($f ≅ $g) := α.e
      return q(evalWhiskerRight_nil $α $h)
  mkEvalWhiskerRightConsOfOf j α η ηs ηs₁ η₁ η₂ η₃ e_ηs₁ e_η₁ e_η₂ e_η₃ := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    let f ← α.srcM
    let g ← α.tgtM
    let h ← η.tgtM
    let i ← ηs.tgtM
    have a : Q($ctx.B) := f.src.e
    have b : Q($ctx.B) := f.tgt.e
    have c : Q($ctx.B) := j.tgt.e
    have f : Q($a ⟶ $b) := f.e
    have g : Q($a ⟶ $b) := g.e
    have h : Q($a ⟶ $b) := h.e
    have i : Q($a ⟶ $b) := i.e
    have j : Q($b ⟶ $c) := j.e
    have α : Q($f ≅ $g) := α.e
    have η : Q($g ⟶ $h) := η.e.e
    have ηs : Q($h ⟶ $i) := ηs.e.e
    have ηs₁ : Q($h ≫ $j ⟶ $i ≫ $j) := ηs₁.e.e
    have η₁ : Q($g ≫ $j ⟶ $h ≫ $j) := η₁.e.e
    have η₂ : Q($g ≫ $j ⟶ $i ≫ $j) := η₂.e.e
    have η₃ : Q($f ≫ $j ⟶ $i ≫ $j) := η₃.e.e
    have e_ηs₁ : Q($ηs ▷ $j = $ηs₁) := e_ηs₁
    have e_η₁ : Q($η ▷ $j = $η₁) := e_η₁
    have e_η₂ : Q($η₁ ≫ $ηs₁ = $η₂) := e_η₂
    have e_η₃ : Q((whiskerRightIso $α $j).hom ≫ $η₂ = $η₃) := e_η₃
    return q(evalWhiskerRight_cons_of_of $e_ηs₁ $e_η₁ $e_η₂ $e_η₃)
  mkEvalWhiskerRightConsWhisker f k α η ηs η₁ η₂ ηs₁ ηs₂ η₃ η₄ η₅
      e_η₁ e_η₂ e_ηs₁ e_ηs₂ e_η₃ e_η₄ e_η₅ := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    let g ← α.srcM
    let h ← η.srcM
    let i ← η.tgtM
    let j ← ηs.tgtM
    have a : Q($ctx.B) := f.src.e
    have b : Q($ctx.B) := f.tgt.e
    have c : Q($ctx.B) := h.tgt.e
    have d : Q($ctx.B) := k.tgt.e
    have f : Q($a ⟶ $b) := f.e
    have g : Q($a ⟶ $c) := g.e
    have h : Q($b ⟶ $c) := h.e
    have i : Q($b ⟶ $c) := i.e
    have j : Q($a ⟶ $c) := j.e
    have k : Q($c ⟶ $d) := k.e
    have α : Q($g ≅ $f ≫ $h) := α.e
    have η : Q($h ⟶ $i) := η.e.e
    have ηs : Q($f ≫ $i ⟶ $j) := ηs.e.e
    have η₁ : Q($h ≫ $k ⟶ $i ≫ $k) := η₁.e.e
    have η₂ : Q($f ≫ ($h ≫ $k) ⟶ $f ≫ ($i ≫ $k)) := η₂.e.e
    have ηs₁ : Q(($f ≫ $i) ≫ $k ⟶ $j ≫ $k) := ηs₁.e.e
    have ηs₂ : Q($f ≫ ($i ≫ $k) ⟶ $j ≫ $k) := ηs₂.e.e
    have η₃ : Q($f ≫ ($h ≫ $k) ⟶ $j ≫ $k) := η₃.e.e
    have η₄ : Q(($f ≫ $h) ≫ $k ⟶ $j ≫ $k) := η₄.e.e
    have η₅ : Q($g ≫ $k ⟶ $j ≫ $k) := η₅.e.e
    have e_η₁ : Q(((Iso.refl _).hom ≫ $η ≫ (Iso.refl _).hom) ▷ $k = $η₁) := e_η₁
    have e_η₂ : Q($f ◁ $η₁ = $η₂) := e_η₂
    have e_ηs₁ : Q($ηs ▷ $k = $ηs₁) := e_ηs₁
    have e_ηs₂ : Q((α_ _ _ _).inv ≫ $ηs₁ = $ηs₂) := e_ηs₂
    have e_η₃ : Q($η₂ ≫ $ηs₂ = $η₃) := e_η₃
    have e_η₄ : Q((α_ _ _ _).hom ≫ $η₃ = $η₄) := e_η₄
    have e_η₅ : Q((whiskerRightIso $α $k).hom ≫ $η₄ = $η₅) := e_η₅
    return q(evalWhiskerRight_cons_whisker $e_η₁ $e_η₂ $e_ηs₁ $e_ηs₂ $e_η₃ $e_η₄ $e_η₅)
  mkEvalWhiskerRightComp g h η η₁ η₂ η₃ η₄ e_η₁ e_η₂ e_η₃ e_η₄ := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    let f ← η.srcM
    let f' ← η.tgtM
    have a : Q($ctx.B) := f.src.e
    have b : Q($ctx.B) := f.tgt.e
    have c : Q($ctx.B) := g.tgt.e
    have d : Q($ctx.B) := h.tgt.e
    have f : Q($a ⟶ $b) := f.e
    have f' : Q($a ⟶ $b) := f'.e
    have g : Q($b ⟶ $c) := g.e
    have h : Q($c ⟶ $d) := h.e
    have η : Q($f ⟶ $f') := η.e.e
    have η₁ : Q($f ≫ $g ⟶ $f' ≫ $g) := η₁.e.e
    have η₂ : Q(($f ≫ $g) ≫ $h ⟶ ($f' ≫ $g) ≫ $h) := η₂.e.e
    have η₃ : Q(($f ≫ $g) ≫ $h ⟶ $f' ≫ ($g ≫ $h)) := η₃.e.e
    have η₄ : Q($f ≫ ($g ≫ $h) ⟶ $f' ≫ ($g ≫ $h)) := η₄.e.e
    have e_η₁ : Q($η ▷ $g = $η₁) := e_η₁
    have e_η₂ : Q($η₁ ▷ $h = $η₂) := e_η₂
    have e_η₃ : Q($η₂ ≫ (α_ _ _ _).hom = $η₃) := e_η₃
    have e_η₄ : Q((α_ _ _ _).inv ≫ $η₃ = $η₄) := e_η₄
    return q(evalWhiskerRight_comp $e_η₁ $e_η₂ $e_η₃ $e_η₄)
  mkEvalWhiskerRightId η η₁ η₂ e_η₁ e_η₂ := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    let f ← η.srcM
    let g ← η.tgtM
    have a : Q($ctx.B) := f.src.e
    have b : Q($ctx.B) := f.tgt.e
    have f : Q($a ⟶ $b) := f.e
    have g : Q($a ⟶ $b) := g.e
    have η : Q($f ⟶ $g) := η.e.e
    have η₁ : Q($f ⟶ $g ≫ 𝟙 $b) := η₁.e.e
    have η₂ : Q($f ≫ 𝟙 $b ⟶ $g ≫ 𝟙 $b) := η₂.e.e
    have e_η₁ : Q($η ≫ (ρ_ _).inv = $η₁) := e_η₁
    have e_η₂ : Q((ρ_ _).hom ≫ $η₁ = $η₂) := e_η₂
    return q(evalWhiskerRight_id $e_η₁ $e_η₂)
/-
**Mathlib.Tactic.Bicategory.** 是 Mathlib 中的一个实例，位于命名空间 `Mathlib.Tactic.Bicategor
y`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MkEvalHorizontalComp BicategoryM where
  mkEvalHorizontalCompAuxOf _ _ := do
    throwError "not implemented"
  mkEvalHorizontalCompAuxCons _ _ _ _ _ _ _ _ _ _ _ := do
    throwError "not implemented"
  mkEvalHorizontalCompAux'Whisker _ _ _ _ _ _ _ _ _ _ _ := do
    throwError "not implemented"
  mkEvalHorizontalCompAux'OfWhisker _ _ _ _ _ _ _ _ _ _ _ := do
    throwError "not implemented"
  mkEvalHorizontalCompNilNil _ _ := do
    throwError "not implemented"
  mkEvalHorizontalCompNilCons _ _ _ _ _ _ _ _ _ _ _ _ := do
    throwError "not implemented"
  mkEvalHorizontalCompConsNil _ _ _ _ _ _ _ _ _ _ _ _ := do
    throwError "not implemented"
  mkEvalHorizontalCompConsCons _ _ _ _ _ _ _ _ _ _ _ _ _ _ := do
    throwError "not implemented"
/-
**Mathlib.Tactic.Bicategory.** 是 Mathlib 中的一个实例，位于命名空间 `Mathlib.Tactic.Bicategor
y`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MkEval BicategoryM where
  mkEvalComp η θ η' θ' ι e_η e_θ e_ηθ := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    let f ← η'.srcM
    let g ← η'.tgtM
    let h ← θ'.tgtM
    have a : Q($ctx.B) := f.src.e
    have b : Q($ctx.B) := f.tgt.e
    have f : Q($a ⟶ $b) := f.e
    have g : Q($a ⟶ $b) := g.e
    have h : Q($a ⟶ $b) := h.e
    have η : Q($f ⟶ $g) := η.e
    have η' : Q($f ⟶ $g) := η'.e.e
    have θ : Q($g ⟶ $h) := θ.e
    have θ' : Q($g ⟶ $h) := θ'.e.e
    have ι : Q($f ⟶ $h) := ι.e.e
    have e_η : Q($η = $η') := e_η
    have e_θ : Q($θ = $θ') := e_θ
    have e_ηθ : Q($η' ≫ $θ' = $ι) := e_ηθ
    return q(eval_comp $e_η $e_θ $e_ηθ)
  mkEvalWhiskerLeft f η η' θ e_η e_θ := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    let g ← η'.srcM
    let h ← η'.tgtM
    have a : Q($ctx.B) := f.src.e
    have b : Q($ctx.B) := f.tgt.e
    have c : Q($ctx.B) := g.tgt.e
    have f : Q($a ⟶ $b) := f.e
    have g : Q($b ⟶ $c) := g.e
    have h : Q($b ⟶ $c) := h.e
    have η : Q($g ⟶ $h) := η.e
    have η' : Q($g ⟶ $h) := η'.e.e
    have θ : Q($f ≫ $g ⟶ $f ≫ $h) := θ.e.e
    have e_η : Q($η = $η') := e_η
    have e_θ : Q($f ◁ $η' = $θ) := e_θ
    return q(eval_whiskerLeft $e_η $e_θ)
  mkEvalWhiskerRight η h η' θ e_η e_θ := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    let f ← η'.srcM
    let g ← η'.tgtM
    have a : Q($ctx.B) := f.src.e
    have b : Q($ctx.B) := f.tgt.e
    have c : Q($ctx.B) := h.tgt.e
    have f : Q($a ⟶ $b) := f.e
    have g : Q($a ⟶ $b) := g.e
    have h : Q($b ⟶ $c) := h.e
    have η : Q($f ⟶ $g) := η.e
    have η' : Q($f ⟶ $g) := η'.e.e
    have θ : Q($f ≫ $h ⟶ $g ≫ $h) := θ.e.e
    have e_η : Q($η = $η') := e_η
    have e_θ : Q($η' ▷ $h = $θ) := e_θ
    return q(eval_whiskerRight $e_η $e_θ)
  mkEvalHorizontalComp _ _ _ _ _ _ _ _ := do
    throwError "not implemented"
  mkEvalOf η := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    let f := η.src
    let g := η.tgt
    have a : Q($ctx.B) := f.src.e
    have b : Q($ctx.B) := f.tgt.e
    have f : Q($a ⟶ $b) := f.e
    have g : Q($a ⟶ $b) := g.e
    have η : Q($f ⟶ $g) := η.e
    return q(eval_of $η)
  mkEvalMonoidalComp η θ α η' θ' αθ ηαθ e_η e_θ e_αθ e_ηαθ := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    let f ← η'.srcM
    let g ← η'.tgtM
    let h ← α.tgtM
    let i ← θ'.tgtM
    have a : Q($ctx.B) := f.src.e
    have b : Q($ctx.B) := f.tgt.e
    have f : Q($a ⟶ $b) := f.e
    have g : Q($a ⟶ $b) := g.e
    have h : Q($a ⟶ $b) := h.e
    have i : Q($a ⟶ $b) := i.e
    have η : Q($f ⟶ $g) := η.e
    have η' : Q($f ⟶ $g) := η'.e.e
    have α : Q($g ≅ $h) := α.e
    have θ : Q($h ⟶ $i) := θ.e
    have θ' : Q($h ⟶ $i) := θ'.e.e
    have αθ : Q($g ⟶ $i) := αθ.e.e
    have ηαθ : Q($f ⟶ $i) := ηαθ.e.e
    have e_η : Q($η = $η') := e_η
    have e_θ : Q($θ = $θ') := e_θ
    have e_αθ : Q(Iso.hom $α ≫ $θ' = $αθ) := e_αθ
    have e_ηαθ : Q($η' ≫ $αθ = $ηαθ) := e_ηαθ
    return q(eval_bicategoricalComp $e_η $e_θ $e_αθ $e_ηαθ)
/-
**Mathlib.Tactic.Bicategory.** 是 Mathlib 中的一个实例，位于命名空间 `Mathlib.Tactic.Bicategor
y`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MonadNormalExpr BicategoryM where
  whiskerRightM η h := do
    return .whisker (← MonadMor₂.whiskerRightM η.e (.of h)) η h
  hConsM _ _ := do
    throwError "not implemented"
  whiskerLeftM f η := do
    return .whisker (← MonadMor₂.whiskerLeftM (.of f) η.e) f η
  nilM α := do
    return .nil (← MonadMor₂.homM α) α
  consM α η ηs := do
    return .cons (← MonadMor₂.comp₂M (← MonadMor₂.homM α) (← MonadMor₂.comp₂M η.e ηs.e)) α η ηs
/-
**Mathlib.Tactic.Bicategory.** 是 Mathlib 中的一个实例，位于命名空间 `Mathlib.Tactic.Bicategor
y`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MkMor₂ BicategoryM where
  ofExpr := Mor₂OfExpr

end Mathlib.Tactic.Bicategory

