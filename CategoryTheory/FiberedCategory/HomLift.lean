/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Calle Sönne
-/
module

public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.CommSq

/-!

# HomLift

Given a functor `p : 𝒳 ⥤ 𝒮`, this file provides API for expressing the fact that `p(φ) = f`
for given morphisms `φ` and `f`. The reason this API is needed is because, in general, `p.map φ = f`
does not make sense when the domain and/or codomain of `φ` and `f` are not definitionally equal.

## Main definition

Given morphism `φ : a ⟶ b` in `𝒳` and `f : R ⟶ S` in `𝒮`, `p.IsHomLift f φ` is a class
which expresses the fact that `f = p(φ)`.

We also define a macro `subst_hom_lift p f φ` which can be used to substitute `f` with `p(φ)` in a
goal, this tactic is just short for `obtain ⟨⟩ := (inferInstance : p.IsHomLift f φ)`, and
it is used to make the code more readable.

## Implementation
The class `IsHomLift` is defined as an inductive with the single constructor
`.map (φ : a ⟶ b) : IsHomLift p (p.map φ) φ`, similar to how `Eq a b` has the single constructor
`.rfl (a : α) : Eq a a`.

-/

@[expose] public section

universe u₁ v₁ u₂ v₂

open CategoryTheory Category

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒳] [Category.{v₂} 𝒮] (p : 𝒳 ⥤ 𝒮)

namespace CategoryTheory

/-- Given a functor `p : 𝒳 ⥤ 𝒮`, an arrow `φ : a ⟶ b` in `𝒳` and an arrow `f : R ⟶ S` in `𝒮`,
`p.IsHomLift f φ` expresses the fact that `φ` lifts `f` through `p`.
This is often drawn as:
```
  a --φ--> b
  -        -
  |        |
  v        v
  R --f--> S
``` -/
/-
**CategoryTheory.inductive** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory`。
形式化陈述：inductive Functor.IsHomLift : forall {R S : 𝒮} {a b : 𝒳} (_ : R ⟶ S) (_ : 
a ⟶ b), Prop | map {a b : 𝒳} (φ : a ⟶ b) : IsHomLift (p.map φ) φ  /-- `subst_hom
_lift p f φ` tries to substitute `f` with `p(φ)` by using `p.IsHomLift f φ` -/ m
acro "subst_hom_lift" p:term:max f:term:max φ:term:max : tactic => `(tactic| obt
ain ⟨⟩
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a functor `p : 𝒳 ⥤ 𝒮`, an arrow `φ : a ⟶ b` in `𝒳` and an arrow `f : R ⟶ S
` in `𝒮`,
`p.IsHomLift f φ` expresses the fact that `φ` lifts `f` through `p`.
This is often drawn as:
```
  a --φ--> b
  -        -
  |        |
  v        v
  R --f--> S
```
-/
class inductive Functor.IsHomLift : ∀ {R S : 𝒮} {a b : 𝒳} (_ : R ⟶ S) (_ : a ⟶ b), Prop
  | map {a b : 𝒳} (φ : a ⟶ b) : IsHomLift (p.map φ) φ

/-- `subst_hom_lift p f φ` tries to substitute `f` with `p(φ)` by using `p.IsHomLift f φ` -/
macro "subst_hom_lift" p:term:max f:term:max φ:term:max : tactic =>
  `(tactic| obtain ⟨⟩ := (inferInstance : Functor.IsHomLift $p $f $φ))

namespace IsHomLift

/-- For any arrow `φ : a ⟶ b` in `𝒳`, `φ` lifts the arrow `p.map φ` in the base `𝒮`. -/
@[simp]
/-
**CategoryTheory.IsHomLift.map** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.IsHomLi
ft`。
形式化陈述：map {a b : 𝒳} (φ : a ⟶ b) : p.IsHomLift (p.map φ) φ
参数：φ : a ⟶ b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For any arrow `φ : a ⟶ b` in `𝒳`, `φ` lifts the arrow `p.map φ` in the base `𝒮`.
-/
instance map {a b : 𝒳} (φ : a ⟶ b) : p.IsHomLift (p.map φ) φ := .map φ

@[simp]
/-
**CategoryTheory.IsHomLift.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.IsHomLift`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (a : 𝒳) : p.IsHomLift (𝟙 (p.obj a)) (𝟙 a) := by
  rw [← p.map_id]; infer_instance
/-
**CategoryTheory.IsHomLift.id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsHomLif
t`。
形式化陈述：∀ {𝒮 : Type u₁} {𝒳 : Type u₂} [inst : CategoryTheory.Category.{v₁, u₂} 𝒳] 
[inst_1 : CategoryTheory.Category.{v₂, u₁} 𝒮]   {p : CategoryTheory.Functor 𝒳 𝒮}
 {R : 𝒮} {a : 𝒳},   p.obj a = R → p.IsHomLift (CategoryTheory.CategoryStruct.id 
R) (CategoryTheory.CategoryStruct.id a)
参数：CategoryTheory.CategoryStruct.id R；CategoryTheory.CategoryStruct.id a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsHomLift.instIsHomLiftIdObj`：∀ {𝒮 : Type u₁} {𝒳 : Type u
₂} [inst : CategoryTheory.Category.{v₁, u₂} 𝒳] [inst_1 : CategoryTheory.Category
.{v₂, u₁} 𝒮]   (p : CategoryTheor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
protected lemma id {p : 𝒳 ⥤ 𝒮} {R : 𝒮} {a : 𝒳} (ha : p.obj a = R) : p.IsHomLift (𝟙 R) (𝟙 a) := by
  cases ha; infer_instance

section

variable {R S : 𝒮} {a b : 𝒳}

/-
**CategoryTheory.IsHomLift.domain_eq** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.I
sHomLift`。
形式化陈述：domain_eq (f : R ⟶ S) (φ : a ⟶ b) [p.IsHomLift f φ] : p.obj a = R
参数：f : R ⟶ S；φ : a ⟶ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma domain_eq (f : R ⟶ S) (φ : a ⟶ b) [p.IsHomLift f φ] : p.obj a = R := by
  subst_hom_lift p f φ; rfl
/-
**CategoryTheory.IsHomLift.codomain_eq** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.IsHomLift`。
形式化陈述：codomain_eq (f : R ⟶ S) (φ : a ⟶ b) [p.IsHomLift f φ] : p.obj b = S
参数：f : R ⟶ S；φ : a ⟶ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma codomain_eq (f : R ⟶ S) (φ : a ⟶ b) [p.IsHomLift f φ] : p.obj b = S := by
  subst_hom_lift p f φ; rfl

variable (f : R ⟶ S) (φ : a ⟶ b) [p.IsHomLift f φ]
/-
**CategoryTheory.IsHomLift.fac** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.IsHomLi
ft`。
形式化陈述：fac : f = eqToHom (domain_eq p f φ).symm ≫ p.map φ ≫ eqToHom (codomain_eq 
p f φ)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.IsHomLift.domain_eq`：domain_eq (f : R ⟶ S) (φ : a ⟶ b) [p
.IsHomLift f φ] : p.obj a = R
· 使用引理 `CategoryTheory.IsHomLift.codomain_eq`：codomain_eq (f : R ⟶ S) (φ : a ⟶ b
) [p.IsHomLift f φ] : p.obj b = S
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
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma fac : f = eqToHom (domain_eq p f φ).symm ≫ p.map φ ≫ eqToHom (codomain_eq p f φ) := by
  subst_hom_lift p f φ; simp
/-
**CategoryTheory.IsHomLift.fac'** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.IsHomL
ift`。
形式化陈述：fac' : p.map φ = eqToHom (domain_eq p f φ) ≫ f ≫ eqToHom (codomain_eq p f 
φ).symm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsHomLift.domain_eq`：domain_eq (f : R ⟶ S) (φ : a ⟶ b) [p
.IsHomLift f φ] : p.obj a = R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.IsHomLift.codomain_eq`：codomain_eq (f : R ⟶ S) (φ : a ⟶ b
) [p.IsHomLift f φ] : p.obj b = S
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
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma fac' : p.map φ = eqToHom (domain_eq p f φ) ≫ f ≫ eqToHom (codomain_eq p f φ).symm := by
  subst_hom_lift p f φ; simp
/-
**CategoryTheory.IsHomLift.commSq** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.IsHo
mLift`。
形式化陈述：commSq : CommSq (p.map φ) (eqToHom (domain_eq p f φ)) (eqToHom (codomain_e
q p f φ)) f where w
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsHomLift.domain_eq`：domain_eq (f : R ⟶ S) (φ : a ⟶ b) [p
.IsHomLift f φ] : p.obj a = R
· 使用引理 `CategoryTheory.IsHomLift.codomain_eq`：codomain_eq (f : R ⟶ S) (φ : a ⟶ b
) [p.IsHomLift f φ] : p.obj b = S
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.IsHomLift.fac`：fac : f = eqToHom (domain_eq p f φ).symm ≫
 p.map φ ≫ eqToHom (codomain_eq p f φ)
· 使用定理 `CategoryTheory.eqToHom_trans_assoc`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {X Y Z : C} (p : X = Y) (q : Y = Z) {Z_1 : C} (h : Z ⟶ Z
_1),   CategoryTheory.Ca…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma commSq : CommSq (p.map φ) (eqToHom (domain_eq p f φ)) (eqToHom (codomain_eq p f φ)) f where
  w := by simp only [fac p f φ, eqToHom_trans_assoc, eqToHom_refl, id_comp]

end

/-
**CategoryTheory.IsHomLift.eq_of_isHomLift** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.IsHomLift`。
形式化陈述：eq_of_isHomLift {a b : 𝒳} (f : p.obj a ⟶ p.obj b) (φ : a ⟶ b) [p.IsHomLift
 f φ] : f = p.map φ
参数：f : p.obj a ⟶ p.obj b；φ : a ⟶ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.IsHomLift.domain_eq`：domain_eq (f : R ⟶ S) (φ : a ⟶ b) [p
.IsHomLift f φ] : p.obj a = R
· 使用引理 `CategoryTheory.IsHomLift.codomain_eq`：codomain_eq (f : R ⟶ S) (φ : a ⟶ b
) [p.IsHomLift f φ] : p.obj b = S
· 使用引理 `CategoryTheory.IsHomLift.fac`：fac : f = eqToHom (domain_eq p f φ).symm ≫
 p.map φ ≫ eqToHom (codomain_eq p f φ)
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma eq_of_isHomLift {a b : 𝒳} (f : p.obj a ⟶ p.obj b) (φ : a ⟶ b) [p.IsHomLift f φ] :
    f = p.map φ := by
  simp only [fac p f φ, eqToHom_refl, comp_id, id_comp]
/-
**CategoryTheory.IsHomLift.of_fac** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.IsHo
mLift`。
形式化陈述：of_fac {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (ha : p.obj a = R) (hb 
: p.obj b = S) (h : f = eqToHom ha.symm ≫ p.map φ ≫ eqToHom hb) : p.IsHomLift f 
φ
参数：f : R ⟶ S；φ : a ⟶ b；ha : p.obj a = R；hb : p.obj b = S；h : f = eqToHom ha.symm
 ≫ p.map φ ≫ eqToHom hb。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma of_fac {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (ha : p.obj a = R) (hb : p.obj b = S)
    (h : f = eqToHom ha.symm ≫ p.map φ ≫ eqToHom hb) : p.IsHomLift f φ := by
  subst ha hb h; simp
/-
**CategoryTheory.IsHomLift.of_fac'** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.IsH
omLift`。
形式化陈述：of_fac' {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (ha : p.obj a = R) (hb
 : p.obj b = S) (h : p.map φ = eqToHom ha ≫ f ≫ eqToHom hb.symm) : p.IsHomLift f
 φ
参数：f : R ⟶ S；φ : a ⟶ b；ha : p.obj a = R；hb : p.obj b = S；h : p.map φ = eqToHom h
a ≫ f ≫ eqToHom hb.symm。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma of_fac' {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (ha : p.obj a = R) (hb : p.obj b = S)
    (h : p.map φ = eqToHom ha ≫ f ≫ eqToHom hb.symm) : p.IsHomLift f φ := by
  subst ha hb
  obtain rfl : f = p.map φ := by simpa using h.symm
  infer_instance
/-
**CategoryTheory.IsHomLift.of_commsq** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.I
sHomLift`。
形式化陈述：of_commsq {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (ha : p.obj a = R) (
hb : p.obj b = S) (h : p.map φ ≫ eqToHom hb = (eqToHom ha) ≫ f) : p.IsHomLift f 
φ
参数：f : R ⟶ S；φ : a ⟶ b；ha : p.obj a = R；hb : p.obj b = S；h : p.map φ ≫ eqToHom h
b = (eqToHom ha) ≫ f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma of_commsq {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (ha : p.obj a = R) (hb : p.obj b = S)
    (h : p.map φ ≫ eqToHom hb = (eqToHom ha) ≫ f) : p.IsHomLift f φ := by
  subst ha hb
  obtain rfl : f = p.map φ := by simpa using h.symm
  infer_instance
/-
**CategoryTheory.IsHomLift.of_commSq** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.I
sHomLift`。
形式化陈述：of_commSq {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (ha : p.obj a = R) (
hb : p.obj b = S) (h : CommSq (p.map φ) (eqToHom ha) (eqToHom hb) f) : p.IsHomLi
ft f φ
参数：f : R ⟶ S；φ : a ⟶ b；ha : p.obj a = R；hb : p.obj b = S；h : CommSq (p.map φ) (e
qToHom ha) (eqToHom hb) f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsHomLift.of_commsq`：of_commsq {R S : 𝒮} {a b : 𝒳} (f : R
 ⟶ S) (φ : a ⟶ b) (ha : p.obj a = R) (hb : p.obj b = S) (h : p.map φ ≫ eqToHom h
b = (eqToHom ha) ≫ f) : …
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
-/
lemma of_commSq {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (ha : p.obj a = R) (hb : p.obj b = S)
    (h : CommSq (p.map φ) (eqToHom ha) (eqToHom hb) f) : p.IsHomLift f φ :=
  of_commsq p f φ ha hb h.1
/-
**CategoryTheory.IsHomLift.comp** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.IsHomL
ift`。
形式化陈述：comp {R S T : 𝒮} {a b c : 𝒳} (f : R ⟶ S) (g : S ⟶ T) (φ : a ⟶ b) (ψ : b ⟶ 
c) [p.IsHomLift f φ] [p.IsHomLift g ψ] : p.IsHomLift (f ≫ g) (φ ≫ ψ)
参数：f : R ⟶ S；g : S ⟶ T；φ : a ⟶ b；ψ : b ⟶ c。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsHomLift.of_commSq`：of_commSq {R S : 𝒮} {a b : 𝒳} (f : R
 ⟶ S) (φ : a ⟶ b) (ha : p.obj a = R) (hb : p.obj b = S) (h : CommSq (p.map φ) (e
qToHom ha) (eqToHom hb) …
· 使用引理 `CategoryTheory.IsHomLift.domain_eq`：domain_eq (f : R ⟶ S) (φ : a ⟶ b) [p
.IsHomLift f φ] : p.obj a = R
· 使用引理 `CategoryTheory.IsHomLift.codomain_eq`：codomain_eq (f : R ⟶ S) (φ : a ⟶ b
) [p.IsHomLift f φ] : p.obj b = S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用引理 `CategoryTheory.CommSq.horiz_comp`：horiz_comp {W X X' Y Z Z' : C} {f : W 
⟶ X} {f' : X ⟶ X'} {g : W ⟶ Y} {h : X ⟶ Z} {h' : X' ⟶ Z'} {i : Y ⟶ Z} {i' : Z ⟶ 
Z'} (hsq₁ : CommSq f g…
· 使用引理 `CategoryTheory.IsHomLift.commSq`：commSq : CommSq (p.map φ) (eqToHom (dom
ain_eq p f φ)) (eqToHom (codomain_eq p f φ)) f where w
-/
instance comp {R S T : 𝒮} {a b c : 𝒳} (f : R ⟶ S) (g : S ⟶ T) (φ : a ⟶ b)
    (ψ : b ⟶ c) [p.IsHomLift f φ] [p.IsHomLift g ψ] : p.IsHomLift (f ≫ g) (φ ≫ ψ) := by
  apply of_commSq
  -- This line transforms the first goal in suitable form; the last line closes all three goals.
  on_goal 1 => rw [p.map_comp]
  apply CommSq.horiz_comp (commSq p f φ) (commSq p g ψ)

/-- If `φ : a ⟶ b` and `ψ : b ⟶ c` lift `𝟙 R`, then so does `φ ≫ ψ` -/
/-
**CategoryTheory.IsHomLift.comp_of_lift_id** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTh
eory.IsHomLift`。
形式化陈述：comp_of_lift_id (R : 𝒮) {a b c : 𝒳} (φ : a ⟶ b) (ψ : b ⟶ c) [p.IsHomLift (
𝟙 R) φ] [p.IsHomLift (𝟙 R) ψ] : p.IsHomLift (𝟙 R) (φ ≫ ψ)
参数：R : 𝒮；φ : a ⟶ b；ψ : b ⟶ c；𝟙 R；𝟙 R。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…

--- 原说明 ---
If `φ : a ⟶ b` and `ψ : b ⟶ c` lift `𝟙 R`, then so does `φ ≫ ψ`
-/
instance comp_of_lift_id (R : 𝒮) {a b c : 𝒳} (φ : a ⟶ b) (ψ : b ⟶ c)
    [p.IsHomLift (𝟙 R) φ] [p.IsHomLift (𝟙 R) ψ] : p.IsHomLift (𝟙 R) (φ ≫ ψ) :=
  comp_id (𝟙 R) ▸ comp p (𝟙 R) (𝟙 R) φ ψ
/-
**CategoryTheory.IsHomLift.comp_lift_id_right** 是 Mathlib 中的一个实例，位于命名空间 `Categor
yTheory.IsHomLift`。
形式化陈述：comp_lift_id_right {a b c : 𝒳} {S T : 𝒮} (f : S ⟶ T) (φ : a ⟶ b) [p.IsHomL
ift f φ] (ψ : b ⟶ c) [p.IsHomLift (𝟙 T) ψ] : p.IsHomLift f (φ ≫ ψ)
参数：f : S ⟶ T；φ : a ⟶ b；ψ : b ⟶ c；𝟙 T。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
instance comp_lift_id_right {a b c : 𝒳} {S T : 𝒮} (f : S ⟶ T) (φ : a ⟶ b) [p.IsHomLift f φ]
    (ψ : b ⟶ c) [p.IsHomLift (𝟙 T) ψ] : p.IsHomLift f (φ ≫ ψ) := by
  simpa using (inferInstance : p.IsHomLift (f ≫ 𝟙 T) (φ ≫ ψ))

/-- If `φ : a ⟶ b` lifts `f` and `ψ : b ⟶ c` lifts `𝟙 T`, then `φ ≫ ψ` lifts `f` -/
/-
**CategoryTheory.IsHomLift.comp_lift_id_right'** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.IsHomLift`。
形式化陈述：comp_lift_id_right' {R S : 𝒮} {a b c : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) [p.IsHom
Lift f φ] (T : 𝒮) (ψ : b ⟶ c) [p.IsHomLift (𝟙 T) ψ] : p.IsHomLift f (φ ≫ ψ)
参数：f : R ⟶ S；φ : a ⟶ b；T : 𝒮；ψ : b ⟶ c；𝟙 T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.IsHomLift.codomain_eq`：codomain_eq (f : R ⟶ S) (φ : a ⟶ b
) [p.IsHomLift f φ] : p.obj b = S
· 使用引理 `CategoryTheory.IsHomLift.domain_eq`：domain_eq (f : R ⟶ S) (φ : a ⟶ b) [p
.IsHomLift f φ] : p.obj a = R

--- 原说明 ---
If `φ : a ⟶ b` lifts `f` and `ψ : b ⟶ c` lifts `𝟙 T`, then `φ ≫ ψ` lifts `f`
-/
lemma comp_lift_id_right' {R S : 𝒮} {a b c : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) [p.IsHomLift f φ]
    (T : 𝒮) (ψ : b ⟶ c) [p.IsHomLift (𝟙 T) ψ] : p.IsHomLift f (φ ≫ ψ) := by
  obtain rfl : S = T := by rw [← codomain_eq p f φ, domain_eq p (𝟙 T) ψ]
  infer_instance
/-
**CategoryTheory.IsHomLift.comp_lift_id_left** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.IsHomLift`。
形式化陈述：comp_lift_id_left {a b c : 𝒳} {S T : 𝒮} (f : S ⟶ T) (ψ : b ⟶ c) [p.IsHomLi
ft f ψ] (φ : a ⟶ b) [p.IsHomLift (𝟙 S) φ] : p.IsHomLift f (φ ≫ ψ)
参数：f : S ⟶ T；ψ : b ⟶ c；φ : a ⟶ b；𝟙 S。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
instance comp_lift_id_left {a b c : 𝒳} {S T : 𝒮} (f : S ⟶ T) (ψ : b ⟶ c) [p.IsHomLift f ψ]
    (φ : a ⟶ b) [p.IsHomLift (𝟙 S) φ] : p.IsHomLift f (φ ≫ ψ) := by
  simpa using (inferInstance : p.IsHomLift (𝟙 S ≫ f) (φ ≫ ψ))

/-- If `φ : a ⟶ b` lifts `𝟙 T` and `ψ : b ⟶ c` lifts `f`, then `φ  ≫ ψ` lifts `f` -/
/-
**CategoryTheory.IsHomLift.comp_lift_id_left'** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.IsHomLift`。
形式化陈述：comp_lift_id_left' {a b c : 𝒳} (R : 𝒮) (φ : a ⟶ b) [p.IsHomLift (𝟙 R) φ] {
S T : 𝒮} (f : S ⟶ T) (ψ : b ⟶ c) [p.IsHomLift f ψ] : p.IsHomLift f (φ ≫ ψ)
参数：R : 𝒮；φ : a ⟶ b；𝟙 R；f : S ⟶ T；ψ : b ⟶ c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.IsHomLift.codomain_eq`：codomain_eq (f : R ⟶ S) (φ : a ⟶ b
) [p.IsHomLift f φ] : p.obj b = S
· 使用引理 `CategoryTheory.IsHomLift.domain_eq`：domain_eq (f : R ⟶ S) (φ : a ⟶ b) [p
.IsHomLift f φ] : p.obj a = R

--- 原说明 ---
If `φ : a ⟶ b` lifts `𝟙 T` and `ψ : b ⟶ c` lifts `f`, then `φ  ≫ ψ` lifts `f`
-/
lemma comp_lift_id_left' {a b c : 𝒳} (R : 𝒮) (φ : a ⟶ b) [p.IsHomLift (𝟙 R) φ]
    {S T : 𝒮} (f : S ⟶ T) (ψ : b ⟶ c) [p.IsHomLift f ψ] : p.IsHomLift f (φ ≫ ψ) := by
  obtain rfl : R = S := by rw [← codomain_eq p (𝟙 R) φ, domain_eq p f ψ]
  infer_instance
/-
**CategoryTheory.IsHomLift.eqToHom_domain_lift_id** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.IsHomLift`。
形式化陈述：eqToHom_domain_lift_id {p : 𝒳 ⥤ 𝒮} {a b : 𝒳} (hab : a = b) {R : 𝒮} (hR : p
.obj a = R) : p.IsHomLift (𝟙 R) (eqToHom hab)
参数：hab : a = b；hR : p.obj a = R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma eqToHom_domain_lift_id {p : 𝒳 ⥤ 𝒮} {a b : 𝒳} (hab : a = b) {R : 𝒮} (hR : p.obj a = R) :
    p.IsHomLift (𝟙 R) (eqToHom hab) := by
  subst hR hab; simp
/-
**CategoryTheory.IsHomLift.eqToHom_codomain_lift_id** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.IsHomLift`。
形式化陈述：eqToHom_codomain_lift_id {p : 𝒳 ⥤ 𝒮} {a b : 𝒳} (hab : a = b) {S : 𝒮} (hS :
 p.obj b = S) : p.IsHomLift (𝟙 S) (eqToHom hab)
参数：hab : a = b；hS : p.obj b = S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma eqToHom_codomain_lift_id {p : 𝒳 ⥤ 𝒮} {a b : 𝒳} (hab : a = b) {S : 𝒮} (hS : p.obj b = S) :
    p.IsHomLift (𝟙 S) (eqToHom hab) := by
  subst hS hab; simp
/-
**CategoryTheory.IsHomLift.id_lift_eqToHom_domain** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.IsHomLift`。
形式化陈述：id_lift_eqToHom_domain {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} (hRS : R = S) {a : 𝒳} (ha : p
.obj a = R) : p.IsHomLift (eqToHom hRS) (𝟙 a)
参数：hRS : R = S；ha : p.obj a = R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma id_lift_eqToHom_domain {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} (hRS : R = S) {a : 𝒳} (ha : p.obj a = R) :
    p.IsHomLift (eqToHom hRS) (𝟙 a) := by
  subst hRS ha; simp
/-
**CategoryTheory.IsHomLift.id_lift_eqToHom_codomain** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.IsHomLift`。
形式化陈述：id_lift_eqToHom_codomain {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} (hRS : R = S) {b : 𝒳} (hb :
 p.obj b = S) : p.IsHomLift (eqToHom hRS) (𝟙 b)
参数：hRS : R = S；hb : p.obj b = S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma id_lift_eqToHom_codomain {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} (hRS : R = S) {b : 𝒳} (hb : p.obj b = S) :
    p.IsHomLift (eqToHom hRS) (𝟙 b) := by
  subst hRS hb; simp


section

variable {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) [p.IsHomLift f φ]

/-
**CategoryTheory.IsHomLift.comp_id_lift** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.IsHomLift`。
形式化陈述：comp_id_lift : p.IsHomLift f (𝟙 a ≫ φ)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
instance comp_id_lift : p.IsHomLift f (𝟙 a ≫ φ) := by
  simp_all
/-
**CategoryTheory.IsHomLift.id_comp_lift** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.IsHomLift`。
形式化陈述：id_comp_lift : p.IsHomLift f (φ ≫ 𝟙 b)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
instance id_comp_lift : p.IsHomLift f (φ ≫ 𝟙 b) := by
  simp_all
/-
**CategoryTheory.IsHomLift.lift_id_comp** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.IsHomLift`。
形式化陈述：lift_id_comp : p.IsHomLift (𝟙 R ≫ f) φ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
instance lift_id_comp : p.IsHomLift (𝟙 R ≫ f) φ := by
  simp_all
/-
**CategoryTheory.IsHomLift.lift_comp_id** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.IsHomLift`。
形式化陈述：lift_comp_id : p.IsHomLift (f ≫ 𝟙 S) φ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
instance lift_comp_id : p.IsHomLift (f ≫ 𝟙 S) φ := by
  simp_all
/-
**CategoryTheory.IsHomLift.comp_eqToHom_lift** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.IsHomLift`。
形式化陈述：comp_eqToHom_lift {a' : 𝒳} (h : a' = a) : p.IsHomLift f (eqToHom h ≫ φ)
参数：h : a' = a。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
instance comp_eqToHom_lift {a' : 𝒳} (h : a' = a) : p.IsHomLift f (eqToHom h ≫ φ) := by
  subst h; simp_all
/-
**CategoryTheory.IsHomLift.eqToHom_comp_lift** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.IsHomLift`。
形式化陈述：eqToHom_comp_lift {b' : 𝒳} (h : b = b') : p.IsHomLift f (φ ≫ eqToHom h)
参数：h : b = b'。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
instance eqToHom_comp_lift {b' : 𝒳} (h : b = b') : p.IsHomLift f (φ ≫ eqToHom h) := by
  subst h; simp_all
/-
**CategoryTheory.IsHomLift.lift_eqToHom_comp** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.IsHomLift`。
形式化陈述：lift_eqToHom_comp {R' : 𝒮} (h : R' = R) : p.IsHomLift (eqToHom h ≫ f) φ
参数：h : R' = R。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
instance lift_eqToHom_comp {R' : 𝒮} (h : R' = R) : p.IsHomLift (eqToHom h ≫ f) φ := by
  subst h; simp_all
/-
**CategoryTheory.IsHomLift.lift_comp_eqToHom** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.IsHomLift`。
形式化陈述：lift_comp_eqToHom {S' : 𝒮} (h : S = S') : p.IsHomLift (f ≫ eqToHom h) φ
参数：h : S = S'。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
instance lift_comp_eqToHom {S' : 𝒮} (h : S = S') : p.IsHomLift (f ≫ eqToHom h) φ := by
  subst h; simp_all

end

@[simp]
/-
**CategoryTheory.IsHomLift.comp_eqToHom_lift_iff** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.IsHomLift`。
形式化陈述：comp_eqToHom_lift_iff {R S : 𝒮} {a' a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (h : 
a' = a) : p.IsHomLift f (eqToHom h ≫ φ) ↔ p.IsHomLift f φ where mp hφ'
参数：f : R ⟶ S；φ : a ⟶ b；h : a' = a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma comp_eqToHom_lift_iff {R S : 𝒮} {a' a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (h : a' = a) :
    p.IsHomLift f (eqToHom h ≫ φ) ↔ p.IsHomLift f φ where
  mp hφ' := by subst h; simpa using hφ'
  mpr _ := inferInstance

@[simp]
/-
**CategoryTheory.IsHomLift.eqToHom_comp_lift_iff** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.IsHomLift`。
形式化陈述：eqToHom_comp_lift_iff {R S : 𝒮} {a b b' : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (h : 
b = b') : p.IsHomLift f (φ ≫ eqToHom h) ↔ p.IsHomLift f φ where mp hφ'
参数：f : R ⟶ S；φ : a ⟶ b；h : b = b'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma eqToHom_comp_lift_iff {R S : 𝒮} {a b b' : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (h : b = b') :
    p.IsHomLift f (φ ≫ eqToHom h) ↔ p.IsHomLift f φ where
  mp hφ' := by subst h; simpa using hφ'
  mpr _ := inferInstance

@[simp]
/-
**CategoryTheory.IsHomLift.lift_eqToHom_comp_iff** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.IsHomLift`。
形式化陈述：lift_eqToHom_comp_iff {R' R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (h : 
R' = R) : p.IsHomLift (eqToHom h ≫ f) φ ↔ p.IsHomLift f φ where mp hφ'
参数：f : R ⟶ S；φ : a ⟶ b；h : R' = R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma lift_eqToHom_comp_iff {R' R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (h : R' = R) :
    p.IsHomLift (eqToHom h ≫ f) φ ↔ p.IsHomLift f φ where
  mp hφ' := by subst h; simpa using hφ'
  mpr _ := inferInstance

@[simp]
/-
**CategoryTheory.IsHomLift.lift_comp_eqToHom_iff** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.IsHomLift`。
形式化陈述：lift_comp_eqToHom_iff {R S S' : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (h : 
S = S') : p.IsHomLift (f ≫ eqToHom h) φ ↔ p.IsHomLift f φ where mp
参数：f : R ⟶ S；φ : a ⟶ b；h : S = S'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma lift_comp_eqToHom_iff {R S S' : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (h : S = S') :
    p.IsHomLift (f ≫ eqToHom h) φ ↔ p.IsHomLift f φ where
  mp := fun hφ' => by subst h; simpa using hφ'
  mpr := fun _ => inferInstance

section

variable {R S : 𝒮} {a b : 𝒳}

/-- Given a morphism `f : R ⟶ S`, and an isomorphism `φ : a ≅ b` lifting `f`, `isoOfIsoLift f φ` is
the isomorphism `Φ : R ≅ S` with `Φ.hom = f` induced from `φ` -/
@[simps hom]
/-
**CategoryTheory.IsHomLift.isoOfIsoLift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.IsHomLift`。
形式化陈述：isoOfIsoLift (f : R ⟶ S) (φ : a ≅ b) [p.IsHomLift f φ.hom] : R ≅ S where h
om
参数：f : R ⟶ S；φ : a ≅ b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a morphism `f : R ⟶ S`, and an isomorphism `φ : a ≅ b` lifting `f`, `isoOf
IsoLift f φ` is
the isomorphism `Φ : R ≅ S` with `Φ.hom = f` induced from `φ`
-/
def isoOfIsoLift (f : R ⟶ S) (φ : a ≅ b) [p.IsHomLift f φ.hom] :
    R ≅ S where
  hom := f
  inv := eqToHom (codomain_eq p f φ.hom).symm ≫ (p.mapIso φ).inv ≫ eqToHom (domain_eq p f φ.hom)
  hom_inv_id := by subst_hom_lift p f φ.hom; simp [← p.map_comp]
  inv_hom_id := by subst_hom_lift p f φ.hom; simp [← p.map_comp]

@[simp]
/-
**CategoryTheory.IsHomLift.isoOfIsoLift_inv_hom_id** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.IsHomLift`。
形式化陈述：isoOfIsoLift_inv_hom_id (f : R ⟶ S) (φ : a ≅ b) [p.IsHomLift f φ.hom] : (i
soOfIsoLift p f φ).inv ≫ f = 𝟙 S
参数：f : R ⟶ S；φ : a ≅ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
-/
lemma isoOfIsoLift_inv_hom_id (f : R ⟶ S) (φ : a ≅ b) [p.IsHomLift f φ.hom] :
    (isoOfIsoLift p f φ).inv ≫ f = 𝟙 S :=
  (isoOfIsoLift p f φ).inv_hom_id

@[simp]
/-
**CategoryTheory.IsHomLift.isoOfIsoLift_hom_inv_id** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.IsHomLift`。
形式化陈述：isoOfIsoLift_hom_inv_id (f : R ⟶ S) (φ : a ≅ b) [p.IsHomLift f φ.hom] : f 
≫ (isoOfIsoLift p f φ).inv = 𝟙 R
参数：f : R ⟶ S；φ : a ≅ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
-/
lemma isoOfIsoLift_hom_inv_id (f : R ⟶ S) (φ : a ≅ b) [p.IsHomLift f φ.hom] :
    f ≫ (isoOfIsoLift p f φ).inv = 𝟙 R :=
  (isoOfIsoLift p f φ).hom_inv_id

/-- If `φ : a ⟶ b` lifts `f : R ⟶ S` and `φ` is an isomorphism, then so is `f`. -/
/-
**CategoryTheory.IsHomLift.isIso_of_lift_isIso** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.IsHomLift`。
形式化陈述：isIso_of_lift_isIso (f : R ⟶ S) (φ : a ⟶ b) [p.IsHomLift f φ] [IsIso φ] : 
IsIso f
参数：f : R ⟶ S；φ : a ⟶ b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.IsHomLift.domain_eq`：domain_eq (f : R ⟶ S) (φ : a ⟶ b) [p
.IsHomLift f φ] : p.obj a = R
· 使用引理 `CategoryTheory.IsHomLift.codomain_eq`：codomain_eq (f : R ⟶ S) (φ : a ⟶ b
) [p.IsHomLift f φ] : p.obj b = S
· 使用定理 `CategoryTheory.instIsIsoEqToHom`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {X Y : C} (h : X = Y),   CategoryTheory.IsIso (CategoryTheo
ry.eqToHom h)
· 使用引理 `CategoryTheory.IsHomLift.fac`：fac : f = eqToHom (domain_eq p f φ).symm ≫
 p.map φ ≫ eqToHom (codomain_eq p f φ)

--- 原说明 ---
If `φ : a ⟶ b` lifts `f : R ⟶ S` and `φ` is an isomorphism, then so is `f`.
-/
lemma isIso_of_lift_isIso (f : R ⟶ S) (φ : a ⟶ b) [p.IsHomLift f φ] [IsIso φ] : IsIso f :=
  (fac p f φ) ▸ inferInstance

/-- Given `φ : a ≅ b` and `f : R ≅ S`, such that `φ.hom` lifts `f.hom`, then `φ.inv` lifts
`f.inv`. -/
/-
**CategoryTheory.IsHomLift.inv_lift_inv** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.IsHomLift`。
形式化陈述：inv_lift_inv (f : R ≅ S) (φ : a ≅ b) [p.IsHomLift f.hom φ.hom] : p.IsHomLi
ft f.inv φ.inv
参数：f : R ≅ S；φ : a ≅ b。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsHomLift.of_commSq`：of_commSq {R S : 𝒮} {a b : 𝒳} (f : R
 ⟶ S) (φ : a ⟶ b) (ha : p.obj a = R) (hb : p.obj b = S) (h : CommSq (p.map φ) (e
qToHom ha) (eqToHom hb) …
· 使用引理 `CategoryTheory.IsHomLift.codomain_eq`：codomain_eq (f : R ⟶ S) (φ : a ⟶ b
) [p.IsHomLift f φ] : p.obj b = S
· 使用引理 `CategoryTheory.IsHomLift.domain_eq`：domain_eq (f : R ⟶ S) (φ : a ⟶ b) [p
.IsHomLift f φ] : p.obj a = R
· 使用定理 `CategoryTheory.CommSq.horiz_inv`：horiz_inv {f : W ≅ X} {i : Y ≅ Z} (p : 
CommSq f.hom g h i.hom) : CommSq f.inv h g i.inv
· 使用引理 `CategoryTheory.IsHomLift.commSq`：commSq : CommSq (p.map φ) (eqToHom (dom
ain_eq p f φ)) (eqToHom (codomain_eq p f φ)) f where w

--- 原说明 ---
Given `φ : a ≅ b` and `f : R ≅ S`, such that `φ.hom` lifts `f.hom`, then `φ.inv`
 lifts
`f.inv`.
-/
instance inv_lift_inv (f : R ≅ S) (φ : a ≅ b) [p.IsHomLift f.hom φ.hom] :
    p.IsHomLift f.inv φ.inv := by
  apply of_commSq
  apply CommSq.horiz_inv (f := p.mapIso φ) (commSq p f.hom φ.hom)

/-- Given `φ : a ≅ b` and `f : R ⟶ S`, such that `φ.hom` lifts `f`, then `φ.inv` lifts the
inverse of `f` given by `isoOfIsoLift`. -/
/-
**CategoryTheory.IsHomLift.inv_lift** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Is
HomLift`。
形式化陈述：inv_lift (f : R ⟶ S) (φ : a ≅ b) [p.IsHomLift f φ.hom] : p.IsHomLift (isoO
fIsoLift p f φ).inv φ.inv
参数：f : R ⟶ S；φ : a ≅ b。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsHomLift.of_commSq`：of_commSq {R S : 𝒮} {a b : 𝒳} (f : R
 ⟶ S) (φ : a ⟶ b) (ha : p.obj a = R) (hb : p.obj b = S) (h : CommSq (p.map φ) (e
qToHom ha) (eqToHom hb) …
· 使用引理 `CategoryTheory.IsHomLift.codomain_eq`：codomain_eq (f : R ⟶ S) (φ : a ⟶ b
) [p.IsHomLift f φ] : p.obj b = S
· 使用引理 `CategoryTheory.IsHomLift.domain_eq`：domain_eq (f : R ⟶ S) (φ : a ⟶ b) [p
.IsHomLift f φ] : p.obj a = R
· 使用定理 `CategoryTheory.CommSq.horiz_inv`：horiz_inv {f : W ≅ X} {i : Y ≅ Z} (p : 
CommSq f.hom g h i.hom) : CommSq f.inv h g i.inv
· 使用引理 `CategoryTheory.IsHomLift.commSq`：commSq : CommSq (p.map φ) (eqToHom (dom
ain_eq p f φ)) (eqToHom (codomain_eq p f φ)) f where w

--- 原说明 ---
Given `φ : a ≅ b` and `f : R ⟶ S`, such that `φ.hom` lifts `f`, then `φ.inv` lif
ts the
inverse of `f` given by `isoOfIsoLift`.
-/
instance inv_lift (f : R ⟶ S) (φ : a ≅ b) [p.IsHomLift f φ.hom] :
    p.IsHomLift (isoOfIsoLift p f φ).inv φ.inv := by
  apply of_commSq
  apply CommSq.horiz_inv (f := p.mapIso φ) (by apply commSq p f φ.hom)

/-- If `φ : a ⟶ b` lifts `f : R ⟶ S` and both are isomorphisms, then `φ⁻¹` lifts `f⁻¹`. -/
/-
**CategoryTheory.IsHomLift.inv** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsHomLi
ft`。
形式化陈述：∀ {𝒮 : Type u₁} {𝒳 : Type u₂} [inst : CategoryTheory.Category.{v₁, u₂} 𝒳] 
[inst_1 : CategoryTheory.Category.{v₂, u₁} 𝒮]   (p : CategoryTheory.Functor 𝒳 𝒮)
 {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) [inst_2 : CategoryTheory.IsIso f]  
 [inst_3 : CategoryTheory.IsIso φ] [p.IsHomLift f φ], p.IsHomLift (CategoryTheor
y.inv f) (CategoryTheory.inv φ)
参数：p : CategoryTheory.Functor 𝒳 𝒮；f : R ⟶ S；φ : a ⟶ b；CategoryTheory.inv f；Categ
oryTheory.inv φ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `φ : a ⟶ b` lifts `f : R ⟶ S` and both are isomorphisms, then `φ⁻¹` lifts `f⁻
¹`.
-/
protected instance inv (f : R ⟶ S) (φ : a ⟶ b) [IsIso f] [IsIso φ] [p.IsHomLift f φ] :
    p.IsHomLift (inv f) (inv φ) :=
  have : p.IsHomLift (asIso f).hom (asIso φ).hom := by simp_all
  IsHomLift.inv_lift_inv p (asIso f) (asIso φ)

end

/-- If `φ : a ≅ b` is an isomorphism lifting `𝟙 S` for some `S : 𝒮`, then `φ⁻¹` also
lifts `𝟙 S`. -/
/-
**CategoryTheory.IsHomLift.lift_id_inv** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.IsHomLift`。
形式化陈述：lift_id_inv (S : 𝒮) {a b : 𝒳} (φ : a ≅ b) [p.IsHomLift (𝟙 S) φ.hom] : p.Is
HomLift (𝟙 S) φ.inv
参数：S : 𝒮；φ : a ≅ b；𝟙 S。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsIso.inv_id`：inv_id : inv (𝟙 X) = 𝟙 X

--- 原说明 ---
If `φ : a ≅ b` is an isomorphism lifting `𝟙 S` for some `S : 𝒮`, then `φ⁻¹` also
lifts `𝟙 S`.
-/
instance lift_id_inv (S : 𝒮) {a b : 𝒳} (φ : a ≅ b) [p.IsHomLift (𝟙 S) φ.hom] :
    p.IsHomLift (𝟙 S) φ.inv :=
  have : p.IsHomLift (asIso (𝟙 S)).hom φ.hom := by simp_all
  (IsIso.inv_id (X := S)) ▸ (IsHomLift.inv_lift_inv p (asIso (𝟙 S)) φ)
/-
**CategoryTheory.IsHomLift.lift_id_inv_isIso** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.IsHomLift`。
形式化陈述：lift_id_inv_isIso (S : 𝒮) {a b : 𝒳} (φ : a ⟶ b) [IsIso φ] [p.IsHomLift (𝟙 
S) φ] : p.IsHomLift (𝟙 S) (inv φ)
参数：S : 𝒮；φ : a ⟶ b；𝟙 S。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsHomLift.inv`：∀ {𝒮 : Type u₁} {𝒳 : Type u₂} [inst : Cate
goryTheory.Category.{v₁, u₂} 𝒳] [inst_1 : CategoryTheory.Category.{v₂, u₁} 𝒮]   
(p : CategoryTheor…
· 使用定理 `CategoryTheory.IsIso.inv_id`：inv_id : inv (𝟙 X) = 𝟙 X
-/
instance lift_id_inv_isIso (S : 𝒮) {a b : 𝒳} (φ : a ⟶ b) [IsIso φ] [p.IsHomLift (𝟙 S) φ] :
    p.IsHomLift (𝟙 S) (inv φ) :=
  (IsIso.inv_id (X := S)) ▸ (IsHomLift.inv p _ φ)

end IsHomLift

end CategoryTheory

