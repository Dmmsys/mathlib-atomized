/-
Copyright (c) 2018 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Opposites

/-!
# Morphisms from equations between objects.

When working categorically, sometimes one encounters an equation `h : X = Y` between objects.

Your initial aversion to this is natural and appropriate:
you're in for some trouble, and if there is another way to approach the problem that won't
rely on this equality, it may be worth pursuing.

You have two options:
1. Use the equality `h` as one normally would in Lean (e.g. using `rw` and `subst`).
   This may immediately cause difficulties, because in category theory everything is dependently
   typed, and equations between objects quickly lead to nasty goals with `eq.rec`.
2. Promote `h` to a morphism using `eqToHom h : X ⟶ Y`, or `eqToIso h : X ≅ Y`.

This file introduces various `simp` lemmas which in favourable circumstances
result in the various `eqToHom` morphisms to drop out at the appropriate moment!
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

-- morphism levels before object levels. See note [category theory universes].
namespace CategoryTheory

open Opposite

/-- An equality `X = Y` gives us a morphism `X ⟶ Y`.

It is typically better to use this, rather than rewriting by the equality then using `𝟙 _`
which usually leads to dependent type theory hell.
-/
/-
**CategoryTheory.eqToHom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：eqToHom {C : Type u₁} [CategoryStruct.{v₁} C] {X Y : C} (p : X = Y) : X ⟶ 
Y
参数：p : X = Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equality `X = Y` gives us a morphism `X ⟶ Y`.

It is typically better to use this, rather than rewriting by the equality then u
sing `𝟙 _`
which usually leads to dependent type theory hell.
-/
def eqToHom {C : Type u₁} [CategoryStruct.{v₁} C] {X Y : C} (p : X = Y) :
    X ⟶ Y := by
  rw [p]
  exact 𝟙 _

/-- `eqToHom'` is the dual of `eqToHom`, which we need for `to_dual`.
Please avoid using this directly. -/
@[to_dual existing eqToHom]
/-
**CategoryTheory.eqToHom'** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：eqToHom' {C : Type u₁} [CategoryStruct.{v₁} C] {X Y : C} (p : X = Y) : Y ⟶
 X
参数：p : X = Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
`eqToHom'` is the dual of `eqToHom`, which we need for `to_dual`.
Please avoid using this directly.
-/
abbrev eqToHom' {C : Type u₁} [CategoryStruct.{v₁} C] {X Y : C} (p : X = Y) : Y ⟶ X :=
  eqToHom p.symm

@[simp]
/-
**CategoryTheory.eqToHom_refl** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：eqToHom_refl {C : Type u₁} [CategoryStruct.{v₁} C] (X : C) (p : X = X) : e
qToHom p = 𝟙 X
参数：X : C；p : X = X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eqToHom_refl {C : Type u₁} [CategoryStruct.{v₁} C] (X : C) (p : X = X) :
    eqToHom p = 𝟙 X :=
  rfl

variable {C : Type u₁} [Category.{v₁} C]

@[to_dual none, reassoc (attr := simp)]
/-
**CategoryTheory.eqToHom_trans** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：eqToHom_trans {X Y Z : C} (p : X = Y) (q : Y = Z) : eqToHom p ≫ eqToHom q 
= eqToHom (p.trans q)
参数：p : X = Y；q : Y = Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem eqToHom_trans {X Y Z : C} (p : X = Y) (q : Y = Z) :
    eqToHom p ≫ eqToHom q = eqToHom (p.trans q) := by
  cases p
  cases q
  simp

/-- `eqToHom h` is heterogeneously equal to the identity of its domain. -/
@[to_dual none]
/-
**CategoryTheory.eqToHom_heq_id_dom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：eqToHom_heq_id_dom (X Y : C) (h : X = Y) : eqToHom h ≍ 𝟙 X
参数：X Y : C；h : X = Y。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`eqToHom h` is heterogeneously equal to the identity of its domain.
-/
lemma eqToHom_heq_id_dom (X Y : C) (h : X = Y) : eqToHom h ≍ 𝟙 X := by
  subst h; rfl

/-- `eqToHom h` is heterogeneously equal to the identity of its codomain. -/
@[to_dual none]
/-
**CategoryTheory.eqToHom_heq_id_cod** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：eqToHom_heq_id_cod (X Y : C) (h : X = Y) : eqToHom h ≍ 𝟙 Y
参数：X Y : C；h : X = Y。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`eqToHom h` is heterogeneously equal to the identity of its codomain.
-/
lemma eqToHom_heq_id_cod (X Y : C) (h : X = Y) : eqToHom h ≍ 𝟙 Y := by
  subst h; rfl

/-- Two morphisms are conjugate via eqToHom if and only if they are heterogeneously equal.
Note this used to be in the Functor namespace, where it doesn't belong. -/
@[to_dual none]
/-
**CategoryTheory.conj_eqToHom_iff_heq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`
。
形式化陈述：conj_eqToHom_iff_heq {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) (h : W = Y) (h'
 : X = Z) : f = eqToHom h ≫ g ≫ eqToHom h'.symm ↔ f ≍ g
参数：f : W ⟶ X；g : Y ⟶ Z；h : W = Y；h' : X = Z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'

--- 原说明 ---
Two morphisms are conjugate via eqToHom if and only if they are heterogeneously 
equal.
Note this used to be in the Functor namespace, where it doesn't belong.
-/
theorem conj_eqToHom_iff_heq {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) (h : W = Y) (h' : X = Z) :
    f = eqToHom h ≫ g ≫ eqToHom h'.symm ↔ f ≍ g := by
  cases h
  cases h'
  simp

@[to_dual none]
/-
**CategoryTheory.conj_eqToHom_iff_heq'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
`。
形式化陈述：conj_eqToHom_iff_heq' {C} [Category* C] {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶
 Z) (h : W = Y) (h' : Z = X) : f = eqToHom h ≫ g ≫ eqToHom h' ↔ f ≍ g
参数：f : W ⟶ X；g : Y ⟶ Z；h : W = Y；h' : Z = X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.conj_eqToHom_iff_heq`：conj_eqToHom_iff_heq {W X Y Z : C} 
(f : W ⟶ X) (g : Y ⟶ Z) (h : W = Y) (h' : X = Z) : f = eqToHom h ≫ g ≫ eqToHom h
'.symm ↔ f ≍ g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem conj_eqToHom_iff_heq' {C} [Category* C] {W X Y Z : C}
    (f : W ⟶ X) (g : Y ⟶ Z) (h : W = Y) (h' : Z = X) :
    f = eqToHom h ≫ g ≫ eqToHom h' ↔ f ≍ g := conj_eqToHom_iff_heq _ _ _ h'.symm

@[to_dual none]
/-
**CategoryTheory.comp_eqToHom_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：comp_eqToHom_iff {X Y Y' : C} (p : Y = Y') (f : X ⟶ Y) (g : X ⟶ Y') : f ≫ 
eqToHom p = g ↔ f = g ≫ eqToHom p.symm
参数：p : Y = Y'；f : X ⟶ Y；g : X ⟶ Y'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.eqToHom_trans`：eqToHom_trans {X Y Z : C} (p : X = Y) (q :
 Y = Z) : eqToHom p ≫ eqToHom q = eqToHom (p.trans q)
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.eq_whisker`：eq_whisker {f g : X ⟶ Y} (w : f = g) (h : Y ⟶
 Z) : f ≫ h = g ≫ h
-/
theorem comp_eqToHom_iff {X Y Y' : C} (p : Y = Y') (f : X ⟶ Y) (g : X ⟶ Y') :
    f ≫ eqToHom p = g ↔ f = g ≫ eqToHom p.symm :=
  { mp h := by simp [← h]
    mpr h := by simp [eq_whisker h (eqToHom p)] }

@[to_dual none]
/-
**CategoryTheory.eqToHom_comp_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：eqToHom_comp_iff {X X' Y : C} (p : X = X') (f : X ⟶ Y) (g : X' ⟶ Y) : eqTo
Hom p ≫ g = f ↔ g = eqToHom p.symm ≫ f
参数：p : X = X'；f : X ⟶ Y；g : X' ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.eqToHom_trans_assoc`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {X Y Z : C} (p : X = Y) (q : Y = Z) {Z_1 : C} (h : Z ⟶ Z
_1),   CategoryTheory.Ca…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem eqToHom_comp_iff {X X' Y : C} (p : X = X') (f : X ⟶ Y) (g : X' ⟶ Y) :
    eqToHom p ≫ g = f ↔ g = eqToHom p.symm ≫ f :=
  { mp h := by simp [← h]
    mpr h := by simp [h] }

@[to_dual none]
/-
**CategoryTheory.eqToHom_comp_heq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：eqToHom_comp_heq {C} [Category* C] {W X Y : C} (f : Y ⟶ X) (h : W = Y) : e
qToHom h ≫ f ≍ f
参数：f : Y ⟶ X；h : W = Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.conj_eqToHom_iff_heq`：conj_eqToHom_iff_heq {W X Y Z : C} 
(f : W ⟶ X) (g : Y ⟶ Z) (h : W = Y) (h' : X = Z) : f = eqToHom h ≫ g ≫ eqToHom h
'.symm ↔ f ≍ g
· 使用定理 `CategoryTheory.eqToHom_refl`：eqToHom_refl {C : Type u₁} [CategoryStruct.
{v₁} C] (X : C) (p : X = X) : eqToHom p = 𝟙 X
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
theorem eqToHom_comp_heq {C} [Category* C] {W X Y : C}
    (f : Y ⟶ X) (h : W = Y) : eqToHom h ≫ f ≍ f := by
  rw [← conj_eqToHom_iff_heq _ _ h rfl, eqToHom_refl, Category.comp_id]

@[simp, to_dual none]
/-
**CategoryTheory.eqToHom_comp_heq_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`
。
形式化陈述：eqToHom_comp_heq_iff {C} [Category* C] {W X Y Z Z' : C} (f : Y ⟶ X) (g : Z
 ⟶ Z') (h : W = Y) : eqToHom h ≫ f ≍ g ↔ f ≍ g
参数：f : Y ⟶ X；g : Z ⟶ Z'；h : W = Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HEq.trans`：∀ {α β φ : Sort u} {a : α} {b : β} {c : φ}, a ≍ b → b ≍ c → a
 ≍ c
· 使用定理 `HEq.symm`：∀ {α β : Sort u} {a : α} {b : β}, a ≍ b → b ≍ a
· 使用定理 `CategoryTheory.eqToHom_comp_heq`：eqToHom_comp_heq {C} [Category* C] {W X
 Y : C} (f : Y ⟶ X) (h : W = Y) : eqToHom h ≫ f ≍ f
-/
theorem eqToHom_comp_heq_iff {C} [Category* C] {W X Y Z Z' : C}
    (f : Y ⟶ X) (g : Z ⟶ Z') (h : W = Y) :
    eqToHom h ≫ f ≍ g ↔ f ≍ g :=
  ⟨(eqToHom_comp_heq ..).symm.trans, (eqToHom_comp_heq ..).trans⟩

@[simp, to_dual none]
/-
**CategoryTheory.heq_eqToHom_comp_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`
。
形式化陈述：heq_eqToHom_comp_iff {C} [Category* C] {W X Y Z Z' : C} (f : Y ⟶ X) (g : Z
 ⟶ Z') (h : W = Y) : g ≍ eqToHom h ≫ f ↔ g ≍ f
参数：f : Y ⟶ X；g : Z ⟶ Z'；h : W = Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HEq.trans`：∀ {α β φ : Sort u} {a : α} {b : β} {c : φ}, a ≍ b → b ≍ c → a
 ≍ c
· 使用定理 `CategoryTheory.eqToHom_comp_heq`：eqToHom_comp_heq {C} [Category* C] {W X
 Y : C} (f : Y ⟶ X) (h : W = Y) : eqToHom h ≫ f ≍ f
· 使用定理 `HEq.symm`：∀ {α β : Sort u} {a : α} {b : β}, a ≍ b → b ≍ a
-/
theorem heq_eqToHom_comp_iff {C} [Category* C] {W X Y Z Z' : C}
    (f : Y ⟶ X) (g : Z ⟶ Z') (h : W = Y) :
    g ≍ eqToHom h ≫ f ↔ g ≍ f :=
  ⟨(·.trans (eqToHom_comp_heq ..)), (·.trans (eqToHom_comp_heq ..).symm)⟩

@[to_dual none]
/-
**CategoryTheory.comp_eqToHom_heq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：comp_eqToHom_heq {C} [Category* C] {X Y Z : C} (f : X ⟶ Y) (h : Y = Z) : f
 ≫ eqToHom h ≍ f
参数：f : X ⟶ Y；h : Y = Z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.conj_eqToHom_iff_heq'`：conj_eqToHom_iff_heq' {C} [Categor
y* C] {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) (h : W = Y) (h' : Z = X) : f = eqToH
om h ≫ g ≫ eqToHom h' ↔ f …
· 使用定理 `CategoryTheory.eqToHom_refl`：eqToHom_refl {C : Type u₁} [CategoryStruct.
{v₁} C] (X : C) (p : X = X) : eqToHom p = 𝟙 X
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
theorem comp_eqToHom_heq {C} [Category* C] {X Y Z : C}
    (f : X ⟶ Y) (h : Y = Z) : f ≫ eqToHom h ≍ f := by
  rw [← conj_eqToHom_iff_heq' _ _ rfl h, eqToHom_refl, Category.id_comp]

@[simp, to_dual none]
/-
**CategoryTheory.comp_eqToHom_heq_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`
。
形式化陈述：comp_eqToHom_heq_iff {C} [Category* C] {W X Y Z Z' : C} (f : X ⟶ Y) (g : Z
 ⟶ Z') (h : Y = W) : f ≫ eqToHom h ≍ g ↔ f ≍ g
参数：f : X ⟶ Y；g : Z ⟶ Z'；h : Y = W。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HEq.trans`：∀ {α β φ : Sort u} {a : α} {b : β} {c : φ}, a ≍ b → b ≍ c → a
 ≍ c
· 使用定理 `HEq.symm`：∀ {α β : Sort u} {a : α} {b : β}, a ≍ b → b ≍ a
· 使用定理 `CategoryTheory.comp_eqToHom_heq`：comp_eqToHom_heq {C} [Category* C] {X Y
 Z : C} (f : X ⟶ Y) (h : Y = Z) : f ≫ eqToHom h ≍ f
-/
theorem comp_eqToHom_heq_iff {C} [Category* C] {W X Y Z Z' : C}
    (f : X ⟶ Y) (g : Z ⟶ Z') (h : Y = W) :
    f ≫ eqToHom h ≍ g ↔ f ≍ g :=
  ⟨(comp_eqToHom_heq ..).symm.trans, (comp_eqToHom_heq ..).trans⟩

@[simp, to_dual none]
/-
**CategoryTheory.heq_comp_eqToHom_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`
。
形式化陈述：heq_comp_eqToHom_iff {C} [Category* C] {W X Y Z Z' : C} (f : X ⟶ Y) (g : Z
 ⟶ Z') (h : Y = W) : g ≍ f ≫ eqToHom h ↔ g ≍ f
参数：f : X ⟶ Y；g : Z ⟶ Z'；h : Y = W。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HEq.trans`：∀ {α β φ : Sort u} {a : α} {b : β} {c : φ}, a ≍ b → b ≍ c → a
 ≍ c
· 使用定理 `CategoryTheory.comp_eqToHom_heq`：comp_eqToHom_heq {C} [Category* C] {X Y
 Z : C} (f : X ⟶ Y) (h : Y = Z) : f ≫ eqToHom h ≍ f
· 使用定理 `HEq.symm`：∀ {α β : Sort u} {a : α} {b : β}, a ≍ b → b ≍ a
-/
theorem heq_comp_eqToHom_iff {C} [Category* C] {W X Y Z Z' : C}
    (f : X ⟶ Y) (g : Z ⟶ Z') (h : Y = W) :
    g ≍ f ≫ eqToHom h ↔ g ≍ f :=
  ⟨(·.trans (comp_eqToHom_heq ..)), (·.trans (comp_eqToHom_heq ..).symm)⟩

@[to_dual self (reorder := X Z, X' Z', f g, f' g', eq1 eq3, H1 H2)]
/-
**CategoryTheory.heq_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：heq_comp {C} [Category* C] {X Y Z X' Y' Z' : C} {f : X ⟶ Y} {g : Y ⟶ Z} {f
' : X' ⟶ Y'} {g' : Y' ⟶ Z'} (eq1 : X = X') (eq2 : Y = Y') (eq3 : Z = Z') (H1 : f
 ≍ f') (H2 : g ≍ g') : f ≫ g ≍ f' ≫ g'
参数：eq1 : X = X'；eq2 : Y = Y'；eq3 : Z = Z'；H1 : f ≍ f'；H2 : g ≍ g'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem heq_comp {C} [Category* C] {X Y Z X' Y' Z' : C}
    {f : X ⟶ Y} {g : Y ⟶ Z} {f' : X' ⟶ Y'} {g' : Y' ⟶ Z'}
    (eq1 : X = X') (eq2 : Y = Y') (eq3 : Z = Z')
    (H1 : f ≍ f') (H2 : g ≍ g') :
    f ≫ g ≍ f' ≫ g' := by
  congr!

variable {β : Sort*}

/-- We can push `eqToHom` to the left through families of morphisms. -/
@[to_dual none, reassoc (attr := simp)]
/-
**CategoryTheory.eqToHom_naturality** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：eqToHom_naturality {f g : β -> C} (z : forall b, f b ⟶ g b) {j j' : β} (w 
: j = j') : z j ≫ eqToHom (by simp [w]) = eqToHom (by simp [w]) ≫ z j'
参数：z : forall b, f b ⟶ g b；w : j = j'。
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'

--- 原说明 ---
We can push `eqToHom` to the left through families of morphisms.
-/
theorem eqToHom_naturality {f g : β → C} (z : ∀ b, f b ⟶ g b) {j j' : β} (w : j = j') :
    z j ≫ eqToHom (by simp [w]) = eqToHom (by simp [w]) ≫ z j' := by
  cases w
  simp

/-- A variant on `eqToHom_naturality` that helps Lean identify the families `f` and `g`. -/
@[to_dual none, reassoc (attr := simp)]
/-
**CategoryTheory.eqToHom_iso_hom_naturality** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory`。
形式化陈述：eqToHom_iso_hom_naturality {f g : β -> C} (z : forall b, f b ≅ g b) {j j' 
: β} (w : j = j') : (z j).hom ≫ eqToHom (by simp [w]) = eqToHom (by simp [w]) ≫ 
(z j').hom
参数：z : forall b, f b ≅ g b；w : j = j'。
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'

--- 原说明 ---
A variant on `eqToHom_naturality` that helps Lean identify the families `f` and 
`g`.
-/
theorem eqToHom_iso_hom_naturality {f g : β → C} (z : ∀ b, f b ≅ g b) {j j' : β} (w : j = j') :
    (z j).hom ≫ eqToHom (by simp [w]) = eqToHom (by simp [w]) ≫ (z j').hom := by
  cases w
  simp

/-- A variant on `eqToHom_naturality` that helps Lean identify the families `f` and `g`. -/
@[to_dual none, reassoc (attr := simp)]
/-
**CategoryTheory.eqToHom_iso_inv_naturality** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory`。
形式化陈述：eqToHom_iso_inv_naturality {f g : β -> C} (z : forall b, f b ≅ g b) {j j' 
: β} (w : j = j') : (z j).inv ≫ eqToHom (by simp [w]) = eqToHom (by simp [w]) ≫ 
(z j').inv
参数：z : forall b, f b ≅ g b；w : j = j'。
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'

--- 原说明 ---
A variant on `eqToHom_naturality` that helps Lean identify the families `f` and 
`g`.
-/
theorem eqToHom_iso_inv_naturality {f g : β → C} (z : ∀ b, f b ≅ g b) {j j' : β} (w : j = j') :
    (z j).inv ≫ eqToHom (by simp [w]) = eqToHom (by simp [w]) ≫ (z j').inv := by
  cases w
  simp

/-- Reducible form of `congrArg_mpr_hom_left` -/
@[simp, to_dual none]
/-
**CategoryTheory.congrArg_cast_hom_left** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y`。
形式化陈述：congrArg_cast_hom_left {X Y Z : C} (p : X = Y) (q : Y ⟶ Z) : cast (congrAr
g (fun W : C => W ⟶ Z) p.symm) q = eqToHom p ≫ q
参数：p : X = Y；q : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'

--- 原说明 ---
Reducible form of `congrArg_mpr_hom_left`
-/
theorem congrArg_cast_hom_left {X Y Z : C} (p : X = Y) (q : Y ⟶ Z) :
    cast (congrArg (fun W : C => W ⟶ Z) p.symm) q = eqToHom p ≫ q := by
  cases p
  simp

/-- If we (perhaps unintentionally) perform equational rewriting on
the source object of a morphism,
we can replace the resulting `_.mpr f` term by a composition with an `eqToHom`.

It may be advisable to introduce any necessary `eqToHom` morphisms manually,
rather than relying on this lemma firing.
-/
@[to_dual none]
/-
**CategoryTheory.congrArg_mpr_hom_left** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
`。
形式化陈述：congrArg_mpr_hom_left {X Y Z : C} (p : X = Y) (q : Y ⟶ Z) : (congrArg (fun
 W : C => W ⟶ Z) p).mpr q = eqToHom p ≫ q
参数：p : X = Y；q : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'

--- 原说明 ---
If we (perhaps unintentionally) perform equational rewriting on
the source object of a morphism,
we can replace the resulting `_.mpr f` term by a composition with an `eqToHom`.

It may be advisable to introduce any necessary `eqToHom` morphisms manually,
rather than relying on this lemma firing.
-/
theorem congrArg_mpr_hom_left {X Y Z : C} (p : X = Y) (q : Y ⟶ Z) :
    (congrArg (fun W : C => W ⟶ Z) p).mpr q = eqToHom p ≫ q := by
  cases p
  simp

/-- Reducible form of `congrArg_mpr_hom_right` -/
@[simp, to_dual none]
/-
**CategoryTheory.congrArg_cast_hom_right** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry`。
形式化陈述：congrArg_cast_hom_right {X Y Z : C} (p : X ⟶ Y) (q : Z = Y) : cast (congrA
rg (fun W : C => X ⟶ W) q.symm) p = p ≫ eqToHom q.symm
参数：p : X ⟶ Y；q : Z = Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'

--- 原说明 ---
Reducible form of `congrArg_mpr_hom_right`
-/
theorem congrArg_cast_hom_right {X Y Z : C} (p : X ⟶ Y) (q : Z = Y) :
    cast (congrArg (fun W : C => X ⟶ W) q.symm) p = p ≫ eqToHom q.symm := by
  cases q
  simp

/-- If we (perhaps unintentionally) perform equational rewriting on
the target object of a morphism,
we can replace the resulting `_.mpr f` term by a composition with an `eqToHom`.

It may be advisable to introduce any necessary `eqToHom` morphisms manually,
rather than relying on this lemma firing.
-/
@[to_dual none]
/-
**CategoryTheory.congrArg_mpr_hom_right** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y`。
形式化陈述：congrArg_mpr_hom_right {X Y Z : C} (p : X ⟶ Y) (q : Z = Y) : (congrArg (fu
n W : C => X ⟶ W) q).mpr p = p ≫ eqToHom q.symm
参数：p : X ⟶ Y；q : Z = Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'

--- 原说明 ---
If we (perhaps unintentionally) perform equational rewriting on
the target object of a morphism,
we can replace the resulting `_.mpr f` term by a composition with an `eqToHom`.

It may be advisable to introduce any necessary `eqToHom` morphisms manually,
rather than relying on this lemma firing.
-/
theorem congrArg_mpr_hom_right {X Y Z : C} (p : X ⟶ Y) (q : Z = Y) :
    (congrArg (fun W : C => X ⟶ W) q).mpr p = p ≫ eqToHom q.symm := by
  cases q
  simp

/-- An equality `X = Y` gives us an isomorphism `X ≅ Y`.

It is typically better to use this, rather than rewriting by the equality then using `Iso.refl _`
which usually leads to dependent type theory hell.
-/
/-
**CategoryTheory.eqToIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：eqToIso {X Y : C} (p : X = Y) : X ≅ Y
参数：p : X = Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
An equality `X = Y` gives us an isomorphism `X ≅ Y`.

It is typically better to use this, rather than rewriting by the equality then u
sing `Iso.refl _`
which usually leads to dependent type theory hell.
-/
def eqToIso {X Y : C} (p : X = Y) : X ≅ Y :=
  ⟨eqToHom p, eqToHom p.symm, by simp, by simp⟩

@[simp]
/-
**CategoryTheory.eqToIso.hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.eqToIso`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y : C} (p :
 X = Y),   (CategoryTheory.eqToIso p).hom = CategoryTheory.eqToHom p
参数：p : X = Y；CategoryTheory.eqToIso p。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eqToIso.hom {X Y : C} (p : X = Y) : (eqToIso p).hom = eqToHom p :=
  rfl

@[simp, to_dual existing hom]
/-
**CategoryTheory.eqToIso.inv** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.eqToIso`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y : C} (p :
 X = Y),   (CategoryTheory.eqToIso p).inv = CategoryTheory.eqToHom ⋯
参数：p : X = Y；CategoryTheory.eqToIso p。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eqToIso.inv {X Y : C} (p : X = Y) : (eqToIso p).inv = eqToHom p.symm :=
  rfl

@[simp]
/-
**CategoryTheory.eqToIso_refl** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：eqToIso_refl {X : C} (p : X = X) : eqToIso p = Iso.refl X
参数：p : X = X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eqToIso_refl {X : C} (p : X = X) : eqToIso p = Iso.refl X :=
  rfl

@[simp]
/-
**CategoryTheory.eqToIso_trans** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：eqToIso_trans {X Y Z : C} (p : X = Y) (q : Y = Z) : eqToIso p ≪≫ eqToIso q
 = eqToIso (p.trans q)
参数：p : X = Y；q : Y = Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.eqToHom_trans`：eqToHom_trans {X Y Z : C} (p : X = Y) (q :
 Y = Z) : eqToHom p ≫ eqToHom q = eqToHom (p.trans q)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eqToIso_trans {X Y Z : C} (p : X = Y) (q : Y = Z) :
    eqToIso p ≪≫ eqToIso q = eqToIso (p.trans q) := by ext; simp

@[simp, to_dual none]
/-
**CategoryTheory.eqToHom_op** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：eqToHom_op {X Y : C} (h : X = Y) : (eqToHom h).op = eqToHom (congr_arg op 
h.symm)
参数：h : X = Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem eqToHom_op {X Y : C} (h : X = Y) : (eqToHom h).op = eqToHom (congr_arg op h.symm) := by
  cases h
  rfl

@[simp, to_dual none]
/-
**CategoryTheory.eqToHom_unop** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：eqToHom_unop {X Y : Cᵒᵖ} (h : X = Y) : (eqToHom h).unop = eqToHom (congr_a
rg unop h.symm)
参数：h : X = Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem eqToHom_unop {X Y : Cᵒᵖ} (h : X = Y) :
    (eqToHom h).unop = eqToHom (congr_arg unop h.symm) := by
  cases h
  rfl

@[to_dual none]
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : C} (h : X = Y) : IsIso (eqToHom h) :=
  (eqToIso h).isIso_hom

@[simp, to_dual none]
/-
**CategoryTheory.inv_eqToHom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：inv_eqToHom {X Y : C} (h : X = Y) : inv (eqToHom h) = eqToHom h.symm
参数：h : X = Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instIsIsoEqToHom`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {X Y : C} (h : X = Y),   CategoryTheory.IsIso (CategoryTheo
ry.eqToHom h)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.inv_id`：inv_id : inv (𝟙 X) = 𝟙 X
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inv_eqToHom {X Y : C} (h : X = Y) : inv (eqToHom h) = eqToHom h.symm := by
  cat_disch

variable {D : Type u₂} [Category.{v₂} D]

namespace Functor

/-- Proving equality between functors. This isn't an extensionality lemma,
  because usually you don't really want to do this. -/
@[to_dual none]
/-
**CategoryTheory.Functor.ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：ext {F G : C ⥤ D} (h_obj : forall X, F.obj X = G.obj X) (h_map : forall X 
Y f, F.map f = eqToHom (h_obj X) ≫ G.map f ≫ eqToHom (h_obj Y).symm
参数：h_obj : forall X, F.obj X = G.obj X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…

--- 原说明 ---
Proving equality between functors. This isn't an extensionality lemma,
  because usually you don't really want to do this.
-/
theorem ext {F G : C ⥤ D} (h_obj : ∀ X, F.obj X = G.obj X)
    (h_map : ∀ X Y f,
      F.map f = eqToHom (h_obj X) ≫ G.map f ≫ eqToHom (h_obj Y).symm := by cat_disch) :
    F = G := by
  match F, G with
  | mk F_obj _ _ _, mk G_obj _ _ _ =>
    obtain rfl : F_obj = G_obj := by
      ext X
      apply h_obj
    congr
    funext X Y f
    simpa using h_map X Y f

@[to_dual none]
/-
**CategoryTheory.Functor.ext_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Fu
nctor`。
形式化陈述：ext_of_iso {F G : C ⥤ D} (e : F ≅ G) (hobj : forall X, F.obj X = G.obj X) 
(happ : forall X, e.hom.app X = eqToHom (hobj X)
参数：e : F ≅ G；hobj : forall X, F.obj X = G.obj X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.ext`：ext {F G : C ⥤ D} (h_obj : forall X, F.obj X
 = G.obj X) (h_map : forall X Y f, F.map f = eqToHom (h_obj X) ≫ G.map f ≫ eqToH
om (h_obj Y).sym…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.IsIso.mono_of_iso`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   CategoryThe
ory.Mono f
· 使用定理 `CategoryTheory.NatIso.hom_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.eqToHom_trans`：eqToHom_trans {X Y Z : C} (p : X = Y) (q :
 Y = Z) : eqToHom p ≫ eqToHom q = eqToHom (p.trans q)
· 使用定理 `CategoryTheory.eqToHom_refl`：eqToHom_refl {C : Type u₁} [CategoryStruct.
{v₁} C] (X : C) (p : X = X) : eqToHom p = 𝟙 X
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma ext_of_iso {F G : C ⥤ D} (e : F ≅ G) (hobj : ∀ X, F.obj X = G.obj X)
    (happ : ∀ X, e.hom.app X = eqToHom (hobj X) := by cat_disch) : F = G :=
  Functor.ext hobj (fun X Y f => by
    rw [← cancel_mono (e.hom.app Y), e.hom.naturality f, happ, happ, Category.assoc,
    Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id])

/-- Proving equality between functors using heterogeneous equality. -/
@[to_dual none]
/-
**CategoryTheory.Functor.hext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Functor`
。
形式化陈述：hext {F G : C ⥤ D} (h_obj : forall X, F.obj X = G.obj X) (h_map : forall (
X Y) (f : X ⟶ Y), F.map f ≍ G.map f) : F = G
参数：h_obj : forall X, F.obj X = G.obj X；h_map : forall (X Y) (f : X ⟶ Y), F.map f
 ≍ G.map f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.ext`：ext {F G : C ⥤ D} (h_obj : forall X, F.obj X
 = G.obj X) (h_map : forall X Y f, F.map f = eqToHom (h_obj X) ≫ G.map f ≫ eqToH
om (h_obj Y).sym…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.conj_eqToHom_iff_heq`：conj_eqToHom_iff_heq {W X Y Z : C} 
(f : W ⟶ X) (g : Y ⟶ Z) (h : W = Y) (h' : X = Z) : f = eqToHom h ≫ g ≫ eqToHom h
'.symm ↔ f ≍ g

--- 原说明 ---
Proving equality between functors using heterogeneous equality.
-/
theorem hext {F G : C ⥤ D} (h_obj : ∀ X, F.obj X = G.obj X)
    (h_map : ∀ (X Y) (f : X ⟶ Y), F.map f ≍ G.map f) : F = G :=
  Functor.ext h_obj fun _ _ f => (conj_eqToHom_iff_heq _ _ (h_obj _) (h_obj _)).2 <| h_map _ _ f

-- Using equalities between functors.
/-
**CategoryTheory.Functor.congr_obj** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Fun
ctor`。
形式化陈述：congr_obj {F G : C ⥤ D} (h : F = G) (X) : F.obj X = G.obj X
参数：h : F = G；X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem congr_obj {F G : C ⥤ D} (h : F = G) (X) : F.obj X = G.obj X := by rw [h]

@[to_dual none, reassoc]
/-
**CategoryTheory.Functor.congr_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Fun
ctor`。
形式化陈述：congr_hom {F G : C ⥤ D} (h : F = G) {X Y} (f : X ⟶ Y) : F.map f = eqToHom 
(congr_obj h X) ≫ G.map f ≫ eqToHom (congr_obj h Y).symm
参数：h : F = G；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.congr_obj`：congr_obj {F G : C ⥤ D} (h : F = G) (X
) : F.obj X = G.obj X
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
theorem congr_hom {F G : C ⥤ D} (h : F = G) {X Y} (f : X ⟶ Y) :
    F.map f = eqToHom (congr_obj h X) ≫ G.map f ≫ eqToHom (congr_obj h Y).symm := by
  subst h; simp
/-
**CategoryTheory.Functor.congr_inv_of_congr_hom** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Functor`。
形式化陈述：congr_inv_of_congr_hom (F G : C ⥤ D) {X Y : C} (e : X ≅ Y) (hX : F.obj X =
 G.obj X) (hY : F.obj Y = G.obj Y) (h₂ : F.map e.hom = eqToHom (by rw [hX]) ≫ G.
map e.hom ≫ eqToHom (by rw [hY])) : F.map e.inv = eqToHom (by rw [hY]) ≫ G.map e
.inv ≫ eqToHom (by rw [hX])
参数：F G : C ⥤ D；e : X ≅ Y；hX : F.obj X = G.obj X；hY : F.obj Y = G.obj Y；h₂ : F.ma
p e.hom = eqToHom (by rw [hX]) ≫ G.map e.hom ≫ eqToHom (by rw [hY])。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.Iso.inv_hom`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : X ≅ Y), CategoryTheory.inv f.hom = f.inv
· 使用定理 `CategoryTheory.Functor.map_inv`：map_inv (F : C ⥤ D) {X Y : C} (f : X ⟶ Y
) [IsIso f] : F.map (inv f) = inv (F.map f)
· 使用定理 `CategoryTheory.instIsIsoEqToHom`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {X Y : C} (h : X = Y),   CategoryTheory.IsIso (CategoryTheo
ry.eqToHom h)
· 使用定理 `CategoryTheory.inv.congr_simp`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (f f_1 : X ⟶ Y) (e_f : f = f_1)   [I : CategoryTheory.
IsIso f], CategoryT…
· 使用定理 `CategoryTheory.IsIso.inv_comp`：inv_comp [IsIso f] [IsIso h] : inv (f ≫ h
) = inv h ≫ inv f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.inv_eqToHom`：inv_eqToHom {X Y : C} (h : X = Y) : inv (eqT
oHom h) = eqToHom h.symm
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem congr_inv_of_congr_hom (F G : C ⥤ D) {X Y : C} (e : X ≅ Y) (hX : F.obj X = G.obj X)
    (hY : F.obj Y = G.obj Y)
    (h₂ : F.map e.hom = eqToHom (by rw [hX]) ≫ G.map e.hom ≫ eqToHom (by rw [hY])) :
    F.map e.inv = eqToHom (by rw [hY]) ≫ G.map e.inv ≫ eqToHom (by rw [hX]) := by
  simp only [← IsIso.Iso.inv_hom e, Functor.map_inv, h₂, IsIso.inv_comp, inv_eqToHom,
    Category.assoc]

section HEq

-- Composition of functors and maps w.r.t. heq
variable {E : Type u₃} [Category.{v₃} E] {F G : C ⥤ D} {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}

/-
**CategoryTheory.Functor.map_comp_heq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Functor`。
形式化陈述：map_comp_heq (hx : F.obj X = G.obj X) (hy : F.obj Y = G.obj Y) (hz : F.obj
 Z = G.obj Z) (hf : F.map f ≍ G.map f) (hg : F.map g ≍ G.map g) : F.map (f ≫ g) 
≍ G.map (f ≫ g)
参数：hx : F.obj X = G.obj X；hy : F.obj Y = G.obj Y；hz : F.obj Z = G.obj Z；hf : F.m
ap f ≍ G.map f；hg : F.map g ≍ G.map g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
-/
theorem map_comp_heq (hx : F.obj X = G.obj X) (hy : F.obj Y = G.obj Y) (hz : F.obj Z = G.obj Z)
    (hf : F.map f ≍ G.map f) (hg : F.map g ≍ G.map g) :
    F.map (f ≫ g) ≍ G.map (f ≫ g) := by
  rw [F.map_comp, G.map_comp]
  congr
/-
**CategoryTheory.Functor.map_comp_heq'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Functor`。
形式化陈述：map_comp_heq' (hobj : forall X : C, F.obj X = G.obj X) (hmap : forall {X Y
} (f : X ⟶ Y), F.map f ≍ G.map f) : F.map (f ≫ g) ≍ G.map (f ≫ g)
参数：hobj : forall X : C, F.obj X = G.obj X；hmap : forall {X Y} (f : X ⟶ Y), F.map
 f ≍ G.map f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.hext`：hext {F G : C ⥤ D} (h_obj : forall X, F.obj
 X = G.obj X) (h_map : forall (X Y) (f : X ⟶ Y), F.map f ≍ G.map f) : F = G
-/
theorem map_comp_heq' (hobj : ∀ X : C, F.obj X = G.obj X)
    (hmap : ∀ {X Y} (f : X ⟶ Y), F.map f ≍ G.map f) :
    F.map (f ≫ g) ≍ G.map (f ≫ g) := by
  rw [Functor.hext hobj fun _ _ => hmap]
/-
**CategoryTheory.Functor.precomp_map_heq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Functor`。
形式化陈述：precomp_map_heq (H : E ⥤ C) (hmap : forall {X Y} (f : X ⟶ Y), F.map f ≍ G.
map f) {X Y : E} (f : X ⟶ Y) : (H ⋙ F).map f ≍ (H ⋙ G).map f
参数：H : E ⥤ C；hmap : forall {X Y} (f : X ⟶ Y), F.map f ≍ G.map f；f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem precomp_map_heq (H : E ⥤ C) (hmap : ∀ {X Y} (f : X ⟶ Y), F.map f ≍ G.map f) {X Y : E}
    (f : X ⟶ Y) : (H ⋙ F).map f ≍ (H ⋙ G).map f :=
  hmap _
/-
**CategoryTheory.Functor.postcomp_map_heq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Functor`。
形式化陈述：postcomp_map_heq (H : D ⥤ E) (hx : F.obj X = G.obj X) (hy : F.obj Y = G.ob
j Y) (hmap : F.map f ≍ G.map f) : (F ⋙ H).map f ≍ (G ⋙ H).map f
参数：H : D ⥤ E；hx : F.obj X = G.obj X；hy : F.obj Y = G.obj Y；hmap : F.map f ≍ G.ma
p f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
-/
theorem postcomp_map_heq (H : D ⥤ E) (hx : F.obj X = G.obj X) (hy : F.obj Y = G.obj Y)
    (hmap : F.map f ≍ G.map f) : (F ⋙ H).map f ≍ (G ⋙ H).map f := by
  dsimp
  congr
/-
**CategoryTheory.Functor.postcomp_map_heq'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Functor`。
形式化陈述：postcomp_map_heq' (H : D ⥤ E) (hobj : forall X : C, F.obj X = G.obj X) (hm
ap : forall {X Y} (f : X ⟶ Y), F.map f ≍ G.map f) : (F ⋙ H).map f ≍ (G ⋙ H).map 
f
参数：H : D ⥤ E；hobj : forall X : C, F.obj X = G.obj X；hmap : forall {X Y} (f : X ⟶
 Y), F.map f ≍ G.map f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.hext`：hext {F G : C ⥤ D} (h_obj : forall X, F.obj
 X = G.obj X) (h_map : forall (X Y) (f : X ⟶ Y), F.map f ≍ G.map f) : F = G
-/
theorem postcomp_map_heq' (H : D ⥤ E) (hobj : ∀ X : C, F.obj X = G.obj X)
    (hmap : ∀ {X Y} (f : X ⟶ Y), F.map f ≍ G.map f) :
    (F ⋙ H).map f ≍ (G ⋙ H).map f := by rw [Functor.hext hobj fun _ _ => hmap]
/-
**CategoryTheory.Functor.hcongr_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Fu
nctor`。
形式化陈述：hcongr_hom {F G : C ⥤ D} (h : F = G) {X Y} (f : X ⟶ Y) : F.map f ≍ G.map f
参数：h : F = G；f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem hcongr_hom {F G : C ⥤ D} (h : F = G) {X Y} (f : X ⟶ Y) : F.map f ≍ G.map f := by
  rw [h]

end HEq

end Functor

/-- This is not always a good idea as a `@[simp]` lemma,
as we lose the ability to use results that interact with `F`,
e.g. the naturality of a natural transformation.

In some files it may be appropriate to use `attribute [local simp] eqToHom_map`, however.
-/
@[to_dual none]
/-
**CategoryTheory.eqToHom_map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：eqToHom_map (F : C ⥤ D) {X Y : C} (p : X = Y) : F.map (eqToHom p) = eqToHo
m (congr_arg F.obj p)
参数：F : C ⥤ D；p : X = Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'

--- 原说明 ---
This is not always a good idea as a `@[simp]` lemma,
as we lose the ability to use results that interact with `F`,
e.g. the naturality of a natural transformation.

In some files it may be appropriate to use `attribute [local simp] eqToHom_map`,
 however.
-/
theorem eqToHom_map (F : C ⥤ D) {X Y : C} (p : X = Y) :
    F.map (eqToHom p) = eqToHom (congr_arg F.obj p) := by cases p; simp

@[to_dual none, reassoc (attr := simp)]
/-
**CategoryTheory.eqToHom_map_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：eqToHom_map_comp (F : C ⥤ D) {X Y Z : C} (p : X = Y) (q : Y = Z) : F.map (
eqToHom p) ≫ F.map (eqToHom q) = F.map (eqToHom <| p.trans q)
参数：F : C ⥤ D；p : X = Y；q : Y = Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eqToHom_map_comp (F : C ⥤ D) {X Y Z : C} (p : X = Y) (q : Y = Z) :
    F.map (eqToHom p) ≫ F.map (eqToHom q) = F.map (eqToHom <| p.trans q) := by cat_disch

/-- See the note on `eqToHom_map` regarding using this as a `simp` lemma.
-/
/-
**CategoryTheory.eqToIso_map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：eqToIso_map (F : C ⥤ D) {X Y : C} (p : X = Y) : F.mapIso (eqToIso p) = eqT
oIso (congr_arg F.obj p)
参数：F : C ⥤ D；p : X = Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.mapIso_refl`：mapIso_refl (F : C ⥤ D) (X : C) : F.
mapIso (Iso.refl X) = Iso.refl (F.obj X)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'

--- 原说明 ---
See the note on `eqToHom_map` regarding using this as a `simp` lemma.
-/
theorem eqToIso_map (F : C ⥤ D) {X Y : C} (p : X = Y) :
    F.mapIso (eqToIso p) = eqToIso (congr_arg F.obj p) := by ext; cases p; simp

@[simp]
/-
**CategoryTheory.eqToIso_map_trans** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：eqToIso_map_trans (F : C ⥤ D) {X Y Z : C} (p : X = Y) (q : Y = Z) : F.mapI
so (eqToIso p) ≪≫ F.mapIso (eqToIso q) = F.mapIso (eqToIso <| p.trans q)
参数：F : C ⥤ D；p : X = Y；q : Y = Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.mapIso_refl`：mapIso_refl (F : C ⥤ D) (X : C) : F.
mapIso (Iso.refl X) = Iso.refl (F.obj X)
· 使用定理 `CategoryTheory.Iso.trans_refl`：trans_refl (α : X ≅ Y) : α ≪≫ Iso.refl Y 
= α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eqToIso_map_trans (F : C ⥤ D) {X Y Z : C} (p : X = Y) (q : Y = Z) :
    F.mapIso (eqToIso p) ≪≫ F.mapIso (eqToIso q) = F.mapIso (eqToIso <| p.trans q) := by cat_disch

@[simp, to_dual none]
/-
**CategoryTheory.eqToHom_app** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：eqToHom_app {F G : C ⥤ D} (h : F = G) (X : C) : (eqToHom h : F ⟶ G).app X 
= eqToHom (Functor.congr_obj h X)
参数：h : F = G；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.congr_obj`：congr_obj {F G : C ⥤ D} (h : F = G) (X
) : F.obj X = G.obj X
-/
theorem eqToHom_app {F G : C ⥤ D} (h : F = G) (X : C) :
    (eqToHom h : F ⟶ G).app X = eqToHom (Functor.congr_obj h X) := by subst h; rfl

@[to_dual none]
/-
**CategoryTheory.NatTrans.congr** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.NatTra
ns`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F G : CategoryTheory.Functor C 
D} (α : F ⟶ G) {X Y : C} (h : X = Y),   α.app X =     CategoryTheory.CategoryStr
uct.comp (F.map (CategoryTheory.eqToHom h))       (CategoryTheory.CategoryStruct
.comp (α.app Y) (G.map (CategoryTheory.eqToHom ⋯)))
参数：α : F ⟶ G；h : X = Y；F.map (CategoryTheory.eqToHom h)；CategoryTheory.CategoryS
truct.comp (α.app Y) (G.map (CategoryTheory.eqToHom ⋯))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.naturality_assoc`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.eqToHom_map`：eqToHom_map (F : C ⥤ D) {X Y : C} (p : X = Y
) : F.map (eqToHom p) = eqToHom (congr_arg F.obj p)
· 使用定理 `CategoryTheory.eqToHom_trans`：eqToHom_trans {X Y Z : C} (p : X = Y) (q :
 Y = Z) : eqToHom p ≫ eqToHom q = eqToHom (p.trans q)
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem NatTrans.congr {F G : C ⥤ D} (α : F ⟶ G) {X Y : C} (h : X = Y) :
    α.app X = F.map (eqToHom h) ≫ α.app Y ≫ G.map (eqToHom h.symm) := by
  rw [α.naturality_assoc]
  simp [eqToHom_map]

@[to_dual none]
/-
**CategoryTheory.eq_conj_eqToHom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：eq_conj_eqToHom {X Y : C} (f : X ⟶ Y) : f = eqToHom rfl ≫ f ≫ eqToHom rfl
参数：f : X ⟶ Y。
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
theorem eq_conj_eqToHom {X Y : C} (f : X ⟶ Y) : f = eqToHom rfl ≫ f ≫ eqToHom rfl := by
  simp only [Category.id_comp, eqToHom_refl, Category.comp_id]

@[to_dual none]
/-
**CategoryTheory.dcongr_arg** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：dcongr_arg {ι : Type*} {F G : ι -> C} (α : forall i, F i ⟶ G i) {i j : ι} 
(h : i = j) : α i = eqToHom (congr_arg F h) ≫ α j ≫ eqToHom (congr_arg G h.symm)
参数：α : forall i, F i ⟶ G i；h : i = j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
theorem dcongr_arg {ι : Type*} {F G : ι → C} (α : ∀ i, F i ⟶ G i) {i j : ι} (h : i = j) :
    α i = eqToHom (congr_arg F h) ≫ α j ≫ eqToHom (congr_arg G h.symm) := by
  subst h
  simp

@[simp]
/-
**CategoryTheory.InducedCategory.eqToHom_hom** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.InducedCategory`。
形式化陈述：∀ {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{u_4, u_3}
 D] {F : C → D}   {X Y : CategoryTheory.InducedCategory D F} (h : X = Y), (Categ
oryTheory.eqToHom h).hom = CategoryTheory.eqToHom ⋯
参数：h : X = Y；CategoryTheory.eqToHom h。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma InducedCategory.eqToHom_hom {C D : Type*} [Category D] {F : C → D}
    {X Y : InducedCategory D F} (h : X = Y) :
    (eqToHom h).hom = eqToHom (by subst h; rfl) := by
  subst h
  rfl

@[simp]
/-
**CategoryTheory.ObjectProperty.eqToHom_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.ObjectProperty`。
形式化陈述：∀ {C : Type u_2} [inst : CategoryTheory.Category.{u_3, u_2} C] {P : Catego
ryTheory.ObjectProperty C}   {X Y : P.FullSubcategory} (h : X = Y), (CategoryThe
ory.eqToHom h).hom = CategoryTheory.eqToHom ⋯
参数：h : X = Y；CategoryTheory.eqToHom h。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ObjectProperty.eqToHom_hom {C : Type*} [Category C] {P : ObjectProperty C}
    {X Y : P.FullSubcategory} (h : X = Y) :
    (eqToHom h).hom = eqToHom (by subst h; rfl) := by
  subst h
  rfl

/-- If `T ≃ D` is a bijection and `D` is a category, then
`InducedCategory D e` is equivalent to `D`. -/
@[simps]
/-
**CategoryTheory.Equivalence.induced** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.E
quivalence`。
形式化陈述：{D : Type u₂} →   [inst : CategoryTheory.Category.{v₂, u₂} D] → {T : Type 
u_2} → (e : T ≃ D) → CategoryTheory.InducedCategory D ⇑e ≌ D
参数：e : T ≃ D。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `T ≃ D` is a bijection and `D` is a category, then
`InducedCategory D e` is equivalent to `D`.
-/
def Equivalence.induced {T : Type*} (e : T ≃ D) :
    InducedCategory D e ≌ D where
  functor := inducedFunctor e
  inverse :=
    { obj := e.symm
      map f := InducedCategory.homMk (eqToHom (by simp) ≫ f ≫ eqToHom (by simp)) }
  unitIso := NatIso.ofComponents (fun _ ↦ eqToIso (by simp))
  counitIso := NatIso.ofComponents (fun _ ↦ eqToIso (by simp))

end CategoryTheory

