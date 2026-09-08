/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Equivalence

/-!
# The Karoubi envelope of a category

In this file, we define the Karoubi envelope `Karoubi C` of a category `C`.

## Main constructions and definitions

- `Karoubi C` is the Karoubi envelope of a category `C`: it is an idempotent
  complete category. It is also preadditive when `C` is preadditive.
- `toKaroubi C : C ⥤ Karoubi C` is a fully faithful functor, which is an equivalence
  (`toKaroubiIsEquivalence`) when `C` is idempotent complete.

-/

@[expose] public section

noncomputable section

open CategoryTheory.Category CategoryTheory.Preadditive CategoryTheory.Limits

namespace CategoryTheory

variable (C : Type*) [Category* C]

namespace Idempotents

/-- In a preadditive category `C`, when an object `X` decomposes as `X ≅ P ⨿ Q`, one may
consider `P` as a direct factor of `X` and up to unique isomorphism, it is determined by the
obvious idempotent `X ⟶ P ⟶ X` which is the projection onto `P` with kernel `Q`. More generally,
one may define a formal direct factor of an object `X : C` : it consists of an idempotent
`p : X ⟶ X` which is thought as the "formal image" of `p`. The type `Karoubi C` shall be the
type of the objects of the karoubi envelope of `C`. It makes sense for any category `C`. -/
/-
**CategoryTheory.Idempotents.Karoubi** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory.I
dempotents`。
形式化陈述：Karoubi where /-- an object of the underlying category -/ X : C /-- an end
omorphism of the object -/ p : X ⟶ X /-- the condition that the given endomorphi
sm is an idempotent -/ idem : p ≫ p = p
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a preadditive category `C`, when an object `X` decomposes as `X ≅ P ⨿ Q`, one
 may
consider `P` as a direct factor of `X` and up to unique isomorphism, it is deter
mined by the
obvious idempotent `X ⟶ P ⟶ X` which is the projection onto `P` with kernel `Q`.
 More generally,
one may define a formal direct factor of an object `X : C` : it consists of an i
dempotent
`p : X ⟶ X` which is thought as the "formal image" of `p`. The type `Karoubi C` 
shall be the
type of the objects of the karoubi envelope of `C`. It makes sense for any categ
ory `C`.
-/
structure Karoubi where
  /-- an object of the underlying category -/
  X : C
  /-- an endomorphism of the object -/
  p : X ⟶ X
  /-- the condition that the given endomorphism is an idempotent -/
  idem : p ≫ p = p := by cat_disch

namespace Karoubi

variable {C}

attribute [reassoc (attr := simp)] idem

@[ext (iff := false)]
/-
**CategoryTheory.Idempotents.Karoubi.ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Idempotents.Karoubi`。
形式化陈述：ext {P Q : Karoubi C} (h_X : P.X = Q.X) (h_p : P.p ≫ eqToHom h_X = eqToHom
 h_X ≫ Q.p) : P = Q
参数：h_X : P.X = Q.X；h_p : P.p ≫ eqToHom h_X = eqToHom h_X ≫ Q.p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Idempotents.Karoubi.mk.injEq`：∀ {C : Type u_1} [inst : Ca
tegoryTheory.Category.{v_1, u_1} C] (X : C) (p : X ⟶ X)   (idem : autoParam (Cat
egoryTheory.CategoryStruct.comp p…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem ext {P Q : Karoubi C} (h_X : P.X = Q.X) (h_p : P.p ≫ eqToHom h_X = eqToHom h_X ≫ Q.p) :
    P = Q := by
  cases P
  cases Q
  dsimp at h_X h_p
  subst h_X
  simpa only [mk.injEq, heq_eq_eq, true_and, eqToHom_refl, comp_id, id_comp] using h_p

/-- A morphism `P ⟶ Q` in the category `Karoubi C` is a morphism in the underlying category
`C` which satisfies a relation, which in the preadditive case, expresses that it induces a
map between the corresponding "formal direct factors" and that it vanishes on the complement
formal direct factor. -/
@[ext]
/-
**CategoryTheory.Idempotents.Karoubi.Hom** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheo
ry.Idempotents.Karoubi`。
形式化陈述：Hom (P Q : Karoubi C) where /-- a morphism between the underlying objects 
-/ f : P.X ⟶ Q.X /-- compatibility of the given morphism with the given idempote
nts -/ comm : P.p ≫ f ≫ Q.p = f
参数：P Q : Karoubi C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism `P ⟶ Q` in the category `Karoubi C` is a morphism in the underlying c
ategory
`C` which satisfies a relation, which in the preadditive case, expresses that it
 induces a
map between the corresponding "formal direct factors" and that it vanishes on th
e complement
formal direct factor.
-/
structure Hom (P Q : Karoubi C) where
  /-- a morphism between the underlying objects -/
  f : P.X ⟶ Q.X
  /-- compatibility of the given morphism with the given idempotents -/
  comm : P.p ≫ f ≫ Q.p = f := by cat_disch
/-
**CategoryTheory.Idempotents.Karoubi.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
Idempotents.Karoubi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preadditive C] (P Q : Karoubi C) : Inhabited (Hom P Q) :=
  ⟨⟨0, by rw [zero_comp, comp_zero]⟩⟩

@[reassoc (attr := simp)]
/-
**CategoryTheory.Idempotents.Karoubi.p_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Idempotents.Karoubi`。
形式化陈述：p_comp {P Q : Karoubi C} (f : Hom P Q) : P.p ≫ f.f = f.f
参数：f : Hom P Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Idempotents.Karoubi.Hom.comm`：∀ {C : Type u_1} [inst : Ca
tegoryTheory.Category.{v_1, u_1} C] {P Q : CategoryTheory.Idempotents.Karoubi C}
   (self : P.Hom Q), CategoryTheo…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Idempotents.Karoubi.idem`：∀ {C : Type u_1} [inst : Catego
ryTheory.Category.{v_1, u_1} C] (self : CategoryTheory.Idempotents.Karoubi C),  
 CategoryTheory.CategoryStruc…
-/
theorem p_comp {P Q : Karoubi C} (f : Hom P Q) : P.p ≫ f.f = f.f := by
  rw [← f.comm, ← assoc, P.idem]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Idempotents.Karoubi.comp_p** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Idempotents.Karoubi`。
形式化陈述：comp_p {P Q : Karoubi C} (f : Hom P Q) : f.f ≫ Q.p = f.f
参数：f : Hom P Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Idempotents.Karoubi.Hom.comm`：∀ {C : Type u_1} [inst : Ca
tegoryTheory.Category.{v_1, u_1} C] {P Q : CategoryTheory.Idempotents.Karoubi C}
   (self : P.Hom Q), CategoryTheo…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Idempotents.Karoubi.idem`：∀ {C : Type u_1} [inst : Catego
ryTheory.Category.{v_1, u_1} C] (self : CategoryTheory.Idempotents.Karoubi C),  
 CategoryTheory.CategoryStruc…
-/
theorem comp_p {P Q : Karoubi C} (f : Hom P Q) : f.f ≫ Q.p = f.f := by
  rw [← f.comm, assoc, assoc, Q.idem]

@[reassoc]
/-
**CategoryTheory.Idempotents.Karoubi.p_comm** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Idempotents.Karoubi`。
形式化陈述：p_comm {P Q : Karoubi C} (f : Hom P Q) : P.p ≫ f.f = f.f ≫ Q.p
参数：f : Hom P Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Idempotents.Karoubi.p_comp`：p_comp {P Q : Karoubi C} (f :
 Hom P Q) : P.p ≫ f.f = f.f
· 使用定理 `CategoryTheory.Idempotents.Karoubi.comp_p`：comp_p {P Q : Karoubi C} (f :
 Hom P Q) : f.f ≫ Q.p = f.f
-/
theorem p_comm {P Q : Karoubi C} (f : Hom P Q) : P.p ≫ f.f = f.f ≫ Q.p := by rw [p_comp, comp_p]
/-
**CategoryTheory.Idempotents.Karoubi.comp_proof** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Idempotents.Karoubi`。
形式化陈述：comp_proof {P Q R : Karoubi C} (g : Hom Q R) (f : Hom P Q) : P.p ≫ (f.f ≫ 
g.f) ≫ R.p = f.f ≫ g.f
参数：g : Hom Q R；f : Hom P Q。
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
· 使用定理 `CategoryTheory.Idempotents.Karoubi.comp_p`：comp_p {P Q : Karoubi C} (f :
 Hom P Q) : f.f ≫ Q.p = f.f
· 使用定理 `CategoryTheory.Idempotents.Karoubi.p_comp_assoc`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] {P Q : CategoryTheory.Idempotents.Karoub
i C}   (f : P.Hom Q) {Z : C} (h : Q.X…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comp_proof {P Q R : Karoubi C} (g : Hom Q R) (f : Hom P Q) :
    P.p ≫ (f.f ≫ g.f) ≫ R.p = f.f ≫ g.f := by simp

/-- The category structure on the karoubi envelope of a category. -/
/-
**CategoryTheory.Idempotents.Karoubi.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
Idempotents.Karoubi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category structure on the karoubi envelope of a category.
-/
instance : Category (Karoubi C) where
  Hom := Karoubi.Hom
  id P := ⟨P.p, by repeat' rw [P.idem]⟩
  comp f g := ⟨f.f ≫ g.f, Karoubi.comp_proof g f⟩

@[simp]
/-
**CategoryTheory.Idempotents.Karoubi.hom_ext_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Idempotents.Karoubi`。
形式化陈述：hom_ext_iff {P Q : Karoubi C} {f g : P ⟶ Q} : f = g ↔ f.f = g.f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Idempotents.Karoubi.Hom.ext`：∀ {C : Type u_1} {inst : Cat
egoryTheory.Category.{v_1, u_1} C} {P Q : CategoryTheory.Idempotents.Karoubi C} 
  {x y : P.Hom Q}, x.f = y.f → x…
-/
theorem hom_ext_iff {P Q : Karoubi C} {f g : P ⟶ Q} : f = g ↔ f.f = g.f := by
  constructor
  · intro h
    rw [h]
  · apply Hom.ext

@[ext]
/-
**CategoryTheory.Idempotents.Karoubi.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Idempotents.Karoubi`。
形式化陈述：hom_ext {P Q : Karoubi C} (f g : P ⟶ Q) (h : f.f = g.f) : f = g
参数：f g : P ⟶ Q；h : f.f = g.f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hom_ext {P Q : Karoubi C} (f g : P ⟶ Q) (h : f.f = g.f) : f = g := by
  simpa [hom_ext_iff] using h

@[simp]
/-
**CategoryTheory.Idempotents.Karoubi.comp_f** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Idempotents.Karoubi`。
形式化陈述：comp_f {P Q R : Karoubi C} (f : P ⟶ Q) (g : Q ⟶ R) : (f ≫ g).f = f.f ≫ g.f
参数：f : P ⟶ Q；g : Q ⟶ R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_f {P Q R : Karoubi C} (f : P ⟶ Q) (g : Q ⟶ R) : (f ≫ g).f = f.f ≫ g.f := rfl

@[simp]
/-
**CategoryTheory.Idempotents.Karoubi.id_f** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Idempotents.Karoubi`。
形式化陈述：id_f {P : Karoubi C} : Hom.f (𝟙 P) = P.p
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_f {P : Karoubi C} : Hom.f (𝟙 P) = P.p := rfl

/-- It is possible to coerce an object of `C` into an object of `Karoubi C`.
See also the functor `toKaroubi`. -/
/-
**CategoryTheory.Idempotents.Karoubi.coe** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Idempotents.Karoubi`。
形式化陈述：coe : CoeTC C (Karoubi C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
It is possible to coerce an object of `C` into an object of `Karoubi C`.
See also the functor `toKaroubi`.
-/
instance coe : CoeTC C (Karoubi C) :=
  ⟨fun X => ⟨X, 𝟙 X, by rw [comp_id]⟩⟩
/-
**CategoryTheory.Idempotents.Karoubi.coe_X** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Idempotents.Karoubi`。
形式化陈述：coe_X (X : C) : (X : Karoubi C).X = X
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_X (X : C) : (X : Karoubi C).X = X := by simp

@[simp]
/-
**CategoryTheory.Idempotents.Karoubi.coe_p** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Idempotents.Karoubi`。
形式化陈述：coe_p (X : C) : (X : Karoubi C).p = 𝟙 X
参数：X : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_p (X : C) : (X : Karoubi C).p = 𝟙 X := rfl

@[simp]
/-
**CategoryTheory.Idempotents.Karoubi.eqToHom_f** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Idempotents.Karoubi`。
形式化陈述：eqToHom_f {P Q : Karoubi C} (h : P = Q) : Karoubi.Hom.f (eqToHom h) = P.p 
≫ eqToHom (congr_arg Karoubi.X h)
参数：h : P = Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eqToHom_f {P Q : Karoubi C} (h : P = Q) :
    Karoubi.Hom.f (eqToHom h) = P.p ≫ eqToHom (congr_arg Karoubi.X h) := by
  subst h
  simp only [eqToHom_refl, Karoubi.id_f, comp_id]

end Karoubi

/-- The obvious fully faithful functor `toKaroubi` sends an object `X : C` to the obvious
formal direct factor of `X` given by `𝟙 X`. -/
@[simps, implicit_reducible]
/-
**CategoryTheory.Idempotents.toKaroubi** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Idempotents`。
形式化陈述：toKaroubi : C ⥤ Karoubi C where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The obvious fully faithful functor `toKaroubi` sends an object `X : C` to the ob
vious
formal direct factor of `X` given by `𝟙 X`.
-/
def toKaroubi : C ⥤ Karoubi C where
  obj X := ⟨X, 𝟙 X, by rw [comp_id]⟩
  map f := ⟨f, by simp only [comp_id, id_comp]⟩

/-- The functor `toKaroubi C : C ⥤ Karoubi C` is fully faithful. -/
/-
**CategoryTheory.Idempotents.fullyFaithfulToKaroubi** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Idempotents`。
形式化陈述：fullyFaithfulToKaroubi : (toKaroubi C).FullyFaithful where preimage f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `toKaroubi C : C ⥤ Karoubi C` is fully faithful.
-/
def fullyFaithfulToKaroubi : (toKaroubi C).FullyFaithful where
  preimage f := f.f
/-
**CategoryTheory.Idempotents.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Idempote
nts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (toKaroubi C).Full := (fullyFaithfulToKaroubi C).full
/-
**CategoryTheory.Idempotents.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Idempote
nts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (toKaroubi C).Faithful := (fullyFaithfulToKaroubi C).faithful

variable {C}

@[simps add]
/-
**CategoryTheory.Idempotents.instAdd** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.I
dempotents`。
形式化陈述：instAdd [Preadditive C] {P Q : Karoubi C} : Add (P ⟶ Q) where add f g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAdd [Preadditive C] {P Q : Karoubi C} : Add (P ⟶ Q) where
  add f g := ⟨f.f + g.f, by rw [add_comp, comp_add, f.comm, g.comm]⟩

@[simps neg]
/-
**CategoryTheory.Idempotents.instNeg** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.I
dempotents`。
形式化陈述：instNeg [Preadditive C] {P Q : Karoubi C} : Neg (P ⟶ Q) where neg f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNeg [Preadditive C] {P Q : Karoubi C} : Neg (P ⟶ Q) where
  neg f := ⟨-f.f, by simpa only [neg_comp, comp_neg, neg_inj] using f.comm⟩

@[simps zero]
/-
**CategoryTheory.Idempotents.instZero** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
Idempotents`。
形式化陈述：instZero [Preadditive C] {P Q : Karoubi C} : Zero (P ⟶ Q) where zero
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instZero [Preadditive C] {P Q : Karoubi C} : Zero (P ⟶ Q) where
  zero := ⟨0, by simp only [comp_zero, zero_comp]⟩
/-
**CategoryTheory.Idempotents.instAddCommGroupHom** 是 Mathlib 中的一个实例，位于命名空间 `Cate
goryTheory.Idempotents`。
形式化陈述：instAddCommGroupHom [Preadditive C] {P Q : Karoubi C} : AddCommGroup (P ⟶ 
Q) where zero_add f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddCommGroupHom [Preadditive C] {P Q : Karoubi C} : AddCommGroup (P ⟶ Q) where
  zero_add f := by
    ext
    apply zero_add
  add_zero f := by
    ext
    apply add_zero
  add_assoc f g h' := by
    ext
    apply add_assoc
  add_comm f g := by
    ext
    apply add_comm
  neg_add_cancel f := by
    ext
    apply neg_add_cancel
  zsmul := zsmulRec
  nsmul := nsmulRec

namespace Karoubi

/-
**CategoryTheory.Idempotents.Karoubi.hom_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Idempotents.Karoubi`。
形式化陈述：hom_eq_zero_iff [Preadditive C] {P Q : Karoubi C} {f : P ⟶ Q} : f = 0 ↔ f.
f = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Idempotents.Karoubi.hom_ext_iff`：hom_ext_iff {P Q : Karou
bi C} {f g : P ⟶ Q} : f = g ↔ f.f = g.f
-/
theorem hom_eq_zero_iff [Preadditive C] {P Q : Karoubi C} {f : P ⟶ Q} : f = 0 ↔ f.f = 0 :=
  hom_ext_iff

/-- The map sending `f : P ⟶ Q` to `f.f : P.X ⟶ Q.X` is additive. -/
@[simps]
/-
**CategoryTheory.Idempotents.Karoubi.inclusionHom** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Idempotents.Karoubi`。
形式化陈述：inclusionHom [Preadditive C] (P Q : Karoubi C) : AddMonoidHom (P ⟶ Q) (P.X
 ⟶ Q.X) where toFun f
参数：P Q : Karoubi C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map sending `f : P ⟶ Q` to `f.f : P.X ⟶ Q.X` is additive.
-/
def inclusionHom [Preadditive C] (P Q : Karoubi C) : AddMonoidHom (P ⟶ Q) (P.X ⟶ Q.X) where
  toFun f := f.f
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
/-
**CategoryTheory.Idempotents.Karoubi.sum_hom** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Idempotents.Karoubi`。
形式化陈述：sum_hom [Preadditive C] {P Q : Karoubi C} {α : Type*} (s : Finset α) (f : 
α -> (P ⟶ Q)) : (∑ x in s, f x).f = ∑ x in s, (f x).f
参数：s : Finset α；f : α -> (P ⟶ Q)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem sum_hom [Preadditive C] {P Q : Karoubi C} {α : Type*} (s : Finset α) (f : α → (P ⟶ Q)) :
    (∑ x ∈ s, f x).f = ∑ x ∈ s, (f x).f :=
  map_sum (inclusionHom P Q) f s

end Karoubi

/-- The category `Karoubi C` is preadditive if `C` is. -/
/-
**CategoryTheory.Idempotents.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Idempote
nts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category `Karoubi C` is preadditive if `C` is.
-/
instance [Preadditive C] : Preadditive (Karoubi C) where
  homGroup P Q := by infer_instance
/-
**CategoryTheory.Idempotents.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Idempote
nts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preadditive C] : Functor.Additive (toKaroubi C) where

open Karoubi

variable (C)
/-
**CategoryTheory.Idempotents.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Idempote
nts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIdempotentComplete (Karoubi C) := by
  refine ⟨?_⟩
  intro P p hp
  simp only [hom_ext_iff, comp_f] at hp
  use ⟨P.X, p.f, hp⟩
  use ⟨p.f, by rw [comp_p p, hp]⟩
  use ⟨p.f, by rw [hp, p_comp p]⟩
  simp [hp]

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Idempotents.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Idempote
nts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsIdempotentComplete C] : (toKaroubi C).EssSurj :=
  ⟨fun P => by
    rcases IsIdempotentComplete.idempotents_split P.X P.p P.idem with ⟨Y, i, e, ⟨h₁, h₂⟩⟩
    use Y
    exact
      Nonempty.intro
        { hom := ⟨i, by simp [← Category.assoc, h₁, ← h₂]⟩
          inv := ⟨e, by simp [Category.assoc, h₁, ← h₂]⟩ }⟩

/-- If `C` is idempotent complete, the functor `toKaroubi : C ⥤ Karoubi C` is an equivalence. -/
/-
**CategoryTheory.Idempotents.toKaroubi_isEquivalence** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Idempotents`。
形式化陈述：∀ (C : Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTh
eory.IsIdempotentComplete C],   (CategoryTheory.Idempotents.toKaroubi C).IsEquiv
alence
参数：C : Type u_1；CategoryTheory.Idempotents.toKaroubi C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Idempotents.instFaithfulKaroubiToKaroubi`：∀ (C : Type u_1
) [inst : CategoryTheory.Category.{v_1, u_1} C], (CategoryTheory.Idempotents.toK
aroubi C).Faithful
· 使用定理 `CategoryTheory.Idempotents.instFullKaroubiToKaroubi`：∀ (C : Type u_1) [i
nst : CategoryTheory.Category.{v_1, u_1} C], (CategoryTheory.Idempotents.toKarou
bi C).Full
· 使用定理 `CategoryTheory.Idempotents.instEssSurjKaroubiToKaroubiOfIsIdempotentComp
lete`：∀ (C : Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTh
eory.IsIdempotentComplete C],   (CategoryTheory.Idempotents.toKaro…

--- 原说明 ---
If `C` is idempotent complete, the functor `toKaroubi : C ⥤ Karoubi C` is an equ
ivalence.
-/
instance toKaroubi_isEquivalence [IsIdempotentComplete C] : (toKaroubi C).IsEquivalence where

/-- The equivalence `C ≅ Karoubi C` when `C` is idempotent complete. -/
/-
**CategoryTheory.Idempotents.toKaroubiEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Idempotents`。
形式化陈述：toKaroubiEquivalence [IsIdempotentComplete C] : C ≌ Karoubi C
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Idempotents.toKaroubi_isEquivalence`：∀ (C : Type u_1) [in
st : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.IsIdempotentComplete 
C],   (CategoryTheory.Idempotents.toKaro…

--- 原说明 ---
The equivalence `C ≅ Karoubi C` when `C` is idempotent complete.
-/
def toKaroubiEquivalence [IsIdempotentComplete C] : C ≌ Karoubi C :=
  (toKaroubi C).asEquivalence
/-
**CategoryTheory.Idempotents.toKaroubiEquivalence_functor_additive** 是 Mathlib 中
的一个实例，位于命名空间 `CategoryTheory.Idempotents`。
形式化陈述：toKaroubiEquivalence_functor_additive [Preadditive C] [IsIdempotentComplet
e C] : (toKaroubiEquivalence C).functor.Additive
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance toKaroubiEquivalence_functor_additive [Preadditive C] [IsIdempotentComplete C] :
    (toKaroubiEquivalence C).functor.Additive :=
  inferInstanceAs <| (toKaroubi C).Additive

namespace Karoubi

variable {C}

/-- The split mono which appears in the factorisation `decompId P`. -/
@[simps]
/-
**CategoryTheory.Idempotents.Karoubi.decompId_i** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Idempotents.Karoubi`。
形式化陈述：decompId_i (P : Karoubi C) : P ⟶ P.X
参数：P : Karoubi C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The split mono which appears in the factorisation `decompId P`.
-/
def decompId_i (P : Karoubi C) : P ⟶ P.X :=
  ⟨P.p, by rw [coe_p, comp_id, P.idem]⟩

/-- The split epi which appears in the factorisation `decompId P`. -/
@[simps]
/-
**CategoryTheory.Idempotents.Karoubi.decompId_p** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Idempotents.Karoubi`。
形式化陈述：decompId_p (P : Karoubi C) : (P.X : Karoubi C) ⟶ P
参数：P : Karoubi C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The split epi which appears in the factorisation `decompId P`.
-/
def decompId_p (P : Karoubi C) : (P.X : Karoubi C) ⟶ P :=
  ⟨P.p, by rw [coe_p, id_comp, P.idem]⟩

/-- The formal direct factor of `P.X` given by the idempotent `P.p` in the category `C`
is actually a direct factor in the category `Karoubi C`. -/
@[reassoc]
/-
**CategoryTheory.Idempotents.Karoubi.decompId** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Idempotents.Karoubi`。
形式化陈述：decompId (P : Karoubi C) : 𝟙 P = decompId_i P ≫ decompId_p P
参数：P : Karoubi C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Idempotents.Karoubi.hom_ext`：hom_ext {P Q : Karoubi C} (f
 g : P ⟶ Q) (h : f.f = g.f) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Idempotents.Karoubi.idem`：∀ {C : Type u_1} [inst : Catego
ryTheory.Category.{v_1, u_1} C] (self : CategoryTheory.Idempotents.Karoubi C),  
 CategoryTheory.CategoryStruc…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The formal direct factor of `P.X` given by the idempotent `P.p` in the category 
`C`
is actually a direct factor in the category `Karoubi C`.
-/
theorem decompId (P : Karoubi C) : 𝟙 P = decompId_i P ≫ decompId_p P := by
  ext
  simp only [comp_f, id_f, P.idem, decompId_i, decompId_p]

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Idempotents.Karoubi.decomp_p** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Idempotents.Karoubi`。
形式化陈述：decomp_p (P : Karoubi C) : (toKaroubi C).map P.p = decompId_p P ≫ decompId
_i P
参数：P : Karoubi C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Idempotents.Karoubi.hom_ext`：hom_ext {P Q : Karoubi C} (f
 g : P ⟶ Q) (h : f.f = g.f) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Idempotents.Karoubi.decompId_p_f`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] (P : CategoryTheory.Idempotents.Karoubi 
C),   P.decompId_p.f = P.p
· 使用定理 `CategoryTheory.Idempotents.Karoubi.decompId_i_f`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] (P : CategoryTheory.Idempotents.Karoubi 
C),   P.decompId_i.f = P.p
· 使用定理 `CategoryTheory.Idempotents.Karoubi.idem`：∀ {C : Type u_1} [inst : Catego
ryTheory.Category.{v_1, u_1} C] (self : CategoryTheory.Idempotents.Karoubi C),  
 CategoryTheory.CategoryStruc…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem decomp_p (P : Karoubi C) : (toKaroubi C).map P.p = decompId_p P ≫ decompId_i P := by
  ext
  simp only [comp_f, decompId_p_f, decompId_i_f, P.idem, toKaroubi_map_f]
/-
**CategoryTheory.Idempotents.Karoubi.decompId_i_toKaroubi** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Idempotents.Karoubi`。
形式化陈述：decompId_i_toKaroubi (X : C) : decompId_i ((toKaroubi C).obj X) = 𝟙 _
参数：X : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem decompId_i_toKaroubi (X : C) : decompId_i ((toKaroubi C).obj X) = 𝟙 _ :=
  rfl
/-
**CategoryTheory.Idempotents.Karoubi.decompId_p_toKaroubi** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Idempotents.Karoubi`。
形式化陈述：decompId_p_toKaroubi (X : C) : decompId_p ((toKaroubi C).obj X) = 𝟙 _
参数：X : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem decompId_p_toKaroubi (X : C) : decompId_p ((toKaroubi C).obj X) = 𝟙 _ :=
  rfl
/-
**CategoryTheory.Idempotents.Karoubi.decompId_i_naturality** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Idempotents.Karoubi`。
形式化陈述：decompId_i_naturality {P Q : Karoubi C} (f : P ⟶ Q) : f ≫ decompId_i Q = d
ecompId_i P ≫ (by exact Hom.mk f.f (by simp))
参数：f : P ⟶ Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Idempotents.Karoubi.decompId_i_f`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] (P : CategoryTheory.Idempotents.Karoubi 
C),   P.decompId_i.f = P.p
· 使用定理 `CategoryTheory.Idempotents.Karoubi.comp_p`：comp_p {P Q : Karoubi C} (f :
 Hom P Q) : f.f ≫ Q.p = f.f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Idempotents.Karoubi.p_comp`：p_comp {P Q : Karoubi C} (f :
 Hom P Q) : P.p ≫ f.f = f.f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem decompId_i_naturality {P Q : Karoubi C} (f : P ⟶ Q) :
    f ≫ decompId_i Q = decompId_i P ≫ (by exact Hom.mk f.f (by simp)) := by
  simp
/-
**CategoryTheory.Idempotents.Karoubi.decompId_p_naturality** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Idempotents.Karoubi`。
形式化陈述：decompId_p_naturality {P Q : Karoubi C} (f : P ⟶ Q) : decompId_p P ≫ f = (
by exact Hom.mk f.f (by simp)) ≫ decompId_p Q
参数：f : P ⟶ Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Idempotents.Karoubi.decompId_p_f`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] (P : CategoryTheory.Idempotents.Karoubi 
C),   P.decompId_p.f = P.p
· 使用定理 `CategoryTheory.Idempotents.Karoubi.p_comp`：p_comp {P Q : Karoubi C} (f :
 Hom P Q) : P.p ≫ f.f = f.f
· 使用定理 `CategoryTheory.Idempotents.Karoubi.comp_p`：comp_p {P Q : Karoubi C} (f :
 Hom P Q) : f.f ≫ Q.p = f.f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem decompId_p_naturality {P Q : Karoubi C} (f : P ⟶ Q) :
    decompId_p P ≫ f = (by exact Hom.mk f.f (by simp)) ≫ decompId_p Q := by
  simp

@[simp]
/-
**CategoryTheory.Idempotents.Karoubi.zsmul_hom** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Idempotents.Karoubi`。
形式化陈述：zsmul_hom [Preadditive C] {P Q : Karoubi C} (n : Int) (f : P ⟶ Q) : (n • f
).f = n • f.f
参数：n : Int；f : P ⟶ Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_zsmul`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLik
e F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem zsmul_hom [Preadditive C] {P Q : Karoubi C} (n : ℤ) (f : P ⟶ Q) : (n • f).f = n • f.f :=
  map_zsmul (inclusionHom P Q) n f

set_option backward.defeqAttrib.useBackward true in
/-- If `X : Karoubi C`, then `X` is a retract of `((toKaroubi C).obj X.X)`. -/
@[simps]
/-
**CategoryTheory.Idempotents.Karoubi.retract** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Idempotents.Karoubi`。
形式化陈述：retract (X : Karoubi C) : Retract X ((toKaroubi C).obj X.X) where i
参数：X : Karoubi C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `X : Karoubi C`, then `X` is a retract of `((toKaroubi C).obj X.X)`.
-/
def retract (X : Karoubi C) : Retract X ((toKaroubi C).obj X.X) where
  i := ⟨X.p, by simp⟩
  r := ⟨X.p, by simp⟩

end Karoubi

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Idempotents.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Idempote
nts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (toKaroubi C).PreservesEpimorphisms where
  preserves f _ := ⟨fun g h eq ↦ by
    ext
    rw [← cancel_epi f]
    simpa using eq⟩

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Idempotents.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Idempote
nts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (toKaroubi C).PreservesMonomorphisms where
  preserves f _ := ⟨fun g h eq ↦ by
    ext
    rw [← cancel_mono f]
    simpa using eq⟩

end Idempotents

end CategoryTheory

