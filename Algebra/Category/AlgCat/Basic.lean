/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.ConcreteCategory.ReflectsIso
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.FreeAlgebra
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Category instance for algebras over a commutative ring

We introduce the bundled category `AlgCat` of algebras over a fixed commutative ring `R` along
with the forgetful functors to `RingCat` and `ModuleCat`. We furthermore show that the functor
associating to a type the free `R`-algebra on that type is left adjoint to the forgetful functor.
-/

@[expose] public section

open CategoryTheory Limits

universe v u

variable (R : Type u) [CommRing R]

/-- The category of R-algebras and their morphisms. -/
/-
**AlgCat** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u) → [CommRing R] → Type (max u (v + 1))
参数：v + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of R-algebras and their morphisms.
-/
structure AlgCat where
  private mk ::
  /-- The underlying type. -/
  carrier : Type v
  [isRing : Ring carrier]
  [isAlgebra : Algebra R carrier]

attribute [instance] AlgCat.isRing AlgCat.isAlgebra

initialize_simps_projections AlgCat (-isRing, -isAlgebra)

namespace AlgCat

/-
**AlgCat.** 是 Mathlib 中的一个实例，位于命名空间 `AlgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort (AlgCat R) (Type v) :=
  ⟨AlgCat.carrier⟩

attribute [coe] AlgCat.carrier

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The object in the category of R-algebras associated to a type equipped with the appropriate
typeclasses. This is the preferred way to construct a term of `AlgCat R`. -/
/-
**AlgCat.of** 是 Mathlib 中的一个缩写定义，位于命名空间 `AlgCat`。
形式化陈述：of (X : Type v) [Ring X] [Algebra R X] : AlgCat.{v} R
参数：X : Type v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The object in the category of R-algebras associated to a type equipped with the 
appropriate
typeclasses. This is the preferred way to construct a term of `AlgCat R`.
-/
abbrev of (X : Type v) [Ring X] [Algebra R X] : AlgCat.{v} R :=
  ⟨X⟩
/-
**AlgCat.coe_of** 是 Mathlib 中的一个引理，位于命名空间 `AlgCat`。
形式化陈述：coe_of (X : Type v) [Ring X] [Algebra R X] : (of R X : Type v) = X
参数：X : Type v。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_of (X : Type v) [Ring X] [Algebra R X] : (of R X : Type v) = X :=
  rfl

variable {R} in
/-- The type of morphisms in `AlgCat R`. -/
@[ext]
/-
**AlgCat.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `AlgCat`。
形式化陈述：{R : Type u} → [inst : CommRing R] → AlgCat R → AlgCat R → Type v
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of morphisms in `AlgCat R`.
-/
structure Hom (A B : AlgCat.{v} R) where
  private mk ::
  /-- The underlying algebra map. -/
  hom' : A →ₐ[R] B

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**AlgCat.** 是 Mathlib 中的一个实例，位于命名空间 `AlgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (AlgCat.{v} R) where
  Hom A B := Hom A B
  id A := ⟨AlgHom.id R A⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**AlgCat.** 是 Mathlib 中的一个实例，位于命名空间 `AlgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ConcreteCategory (AlgCat.{v} R) (· →ₐ[R] ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

variable {R} in
/-- Turn a morphism in `AlgCat` back into an `AlgHom`. -/
/-
**AlgCat.Hom.hom** 是 Mathlib 中的一个定义，位于命名空间 `AlgCat.Hom`。
形式化陈述：{R : Type u} → [inst : CommRing R] → {A B : AlgCat R} → A.Hom B → ↑A →ₐ[R]
 ↑B
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a morphism in `AlgCat` back into an `AlgHom`.
-/
abbrev Hom.hom {A B : AlgCat.{v} R} (f : Hom A B) :=
  ConcreteCategory.hom (C := AlgCat R) f

variable {R} in
/-- Typecheck an `AlgHom` as a morphism in `AlgCat`. -/
/-
**AlgCat.ofHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `AlgCat`。
形式化陈述：ofHom {A B : Type v} [Ring A] [Ring B] [Algebra R A] [Algebra R B] (f : A 
->ₐ[R] B) : of R A ⟶ of R B
参数：f : A ->ₐ[R] B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typecheck an `AlgHom` as a morphism in `AlgCat`.
-/
abbrev ofHom {A B : Type v} [Ring A] [Ring B] [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) :
    of R A ⟶ of R B :=
  ConcreteCategory.ofHom (C := AlgCat R) f

variable {R} in
/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
/-
**AlgCat.Hom.Simps.hom** 是 Mathlib 中的一个定义，位于命名空间 `AlgCat.Hom.Simps`。
形式化陈述：{R : Type u} → [inst : CommRing R] → (A B : AlgCat R) → A.Hom B → ↑A →ₐ[R]
 ↑B
参数：A B : AlgCat R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas.
-/
def Hom.Simps.hom (A B : AlgCat.{v} R) (f : Hom A B) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp]
/-
**AlgCat.hom_id** 是 Mathlib 中的一个引理，位于命名空间 `AlgCat`。
形式化陈述：hom_id {A : AlgCat.{v} R} : (𝟙 A : A ⟶ A).hom = AlgHom.id R A
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep 
them for `dsimp`.
-/
lemma hom_id {A : AlgCat.{v} R} : (𝟙 A : A ⟶ A).hom = AlgHom.id R A := rfl

/- Provided for rewriting. -/
/-
**AlgCat.id_apply** 是 Mathlib 中的一个引理，位于命名空间 `AlgCat`。
形式化陈述：id_apply (A : AlgCat.{v} R) (a : A) : (𝟙 A : A ⟶ A) a = a
参数：A : AlgCat.{v} R；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Provided for rewriting.
-/
lemma id_apply (A : AlgCat.{v} R) (a : A) :
    (𝟙 A : A ⟶ A) a = a := by simp

@[simp]
/-
**AlgCat.hom_comp** 是 Mathlib 中的一个引理，位于命名空间 `AlgCat`。
形式化陈述：hom_comp {A B C : AlgCat.{v} R} (f : A ⟶ B) (g : B ⟶ C) : (f ≫ g).hom = g.
hom.comp f.hom
参数：f : A ⟶ B；g : B ⟶ C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_comp {A B C : AlgCat.{v} R} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
/-
**AlgCat.comp_apply** 是 Mathlib 中的一个引理，位于命名空间 `AlgCat`。
形式化陈述：comp_apply {A B C : AlgCat.{v} R} (f : A ⟶ B) (g : B ⟶ C) (a : A) : (f ≫ g
) a = g (f a)
参数：f : A ⟶ B；g : B ⟶ C；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Provided for rewriting.
-/
lemma comp_apply {A B C : AlgCat.{v} R} (f : A ⟶ B) (g : B ⟶ C) (a : A) :
    (f ≫ g) a = g (f a) := by simp

@[ext]
/-
**AlgCat.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `AlgCat`。
形式化陈述：hom_ext {A B : AlgCat.{v} R} {f g : A ⟶ B} (hf : f.hom = g.hom) : f = g
参数：hf : f.hom = g.hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgCat.Hom.ext`：∀ {R : Type u} {inst : CommRing R} {A B : AlgCat R} {x y
 : A.Hom B}, x.hom' = y.hom' → x = y
-/
lemma hom_ext {A B : AlgCat.{v} R} {f g : A ⟶ B} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[simp]
/-
**AlgCat.hom_ofHom** 是 Mathlib 中的一个引理，位于命名空间 `AlgCat`。
形式化陈述：hom_ofHom {R : Type u} [CommRing R] {X Y : Type v} [Ring X] [Algebra R X] 
[Ring Y] [Algebra R Y] (f : X ->ₐ[R] Y) : (ofHom f).hom = f
参数：f : X ->ₐ[R] Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_ofHom {R : Type u} [CommRing R] {X Y : Type v} [Ring X] [Algebra R X] [Ring Y]
    [Algebra R Y] (f : X →ₐ[R] Y) : (ofHom f).hom = f := rfl

@[simp]
/-
**AlgCat.ofHom_hom** 是 Mathlib 中的一个引理，位于命名空间 `AlgCat`。
形式化陈述：ofHom_hom {A B : AlgCat.{v} R} (f : A ⟶ B) : ofHom (Hom.hom f) = f
参数：f : A ⟶ B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_hom {A B : AlgCat.{v} R} (f : A ⟶ B) :
    ofHom (Hom.hom f) = f := rfl

@[simp]
/-
**AlgCat.ofHom_id** 是 Mathlib 中的一个引理，位于命名空间 `AlgCat`。
形式化陈述：ofHom_id {X : Type v} [Ring X] [Algebra R X] : ofHom (AlgHom.id R X) = 𝟙 (
of R X)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_id {X : Type v} [Ring X] [Algebra R X] : ofHom (AlgHom.id R X) = 𝟙 (of R X) := rfl

@[simp]
/-
**AlgCat.ofHom_comp** 是 Mathlib 中的一个引理，位于命名空间 `AlgCat`。
形式化陈述：ofHom_comp {X Y Z : Type v} [Ring X] [Ring Y] [Ring Z] [Algebra R X] [Alge
bra R Y] [Algebra R Z] (f : X ->ₐ[R] Y) (g : Y ->ₐ[R] Z) : ofHom (g.comp f) = of
Hom f ≫ ofHom g
参数：f : X ->ₐ[R] Y；g : Y ->ₐ[R] Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_comp {X Y Z : Type v} [Ring X] [Ring Y] [Ring Z] [Algebra R X] [Algebra R Y]
    [Algebra R Z] (f : X →ₐ[R] Y) (g : Y →ₐ[R] Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl
/-
**AlgCat.ofHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `AlgCat`。
形式化陈述：ofHom_apply {R : Type u} [CommRing R] {X Y : Type v} [Ring X] [Algebra R X
] [Ring Y] [Algebra R Y] (f : X ->ₐ[R] Y) (x : X) : ofHom f x = f x
参数：f : X ->ₐ[R] Y；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_apply {R : Type u} [CommRing R] {X Y : Type v} [Ring X] [Algebra R X] [Ring Y]
    [Algebra R Y] (f : X →ₐ[R] Y) (x : X) : ofHom f x = f x := rfl
/-
**AlgCat.inv_hom_apply** 是 Mathlib 中的一个引理，位于命名空间 `AlgCat`。
形式化陈述：inv_hom_apply {A B : AlgCat.{v} R} (e : A ≅ B) (x : A) : e.inv (e.hom x) =
 x
参数：e : A ≅ B；x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.hom_inv_id_apply`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {F : C → C → Type uF}   {carrier 
: C → Type w} {instFunLik…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inv_hom_apply {A B : AlgCat.{v} R} (e : A ≅ B) (x : A) : e.inv (e.hom x) = x := by
  simp
/-
**AlgCat.hom_inv_apply** 是 Mathlib 中的一个引理，位于命名空间 `AlgCat`。
形式化陈述：hom_inv_apply {A B : AlgCat.{v} R} (e : A ≅ B) (x : B) : e.hom (e.inv x) =
 x
参数：e : A ≅ B；x : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.inv_hom_id_apply`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {F : C → C → Type uF}   {carrier 
: C → Type w} {instFunLik…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma hom_inv_apply {A B : AlgCat.{v} R} (e : A ≅ B) (x : B) : e.hom (e.inv x) = x := by
  simp
/-
**AlgCat.** 是 Mathlib 中的一个实例，位于命名空间 `AlgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (AlgCat R) :=
  ⟨of R R⟩
/-
**AlgCat.forget_obj** 是 Mathlib 中的一个引理，位于命名空间 `AlgCat`。
形式化陈述：forget_obj {A : AlgCat.{v} R} : (forget (AlgCat.{v} R)).obj A = A
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma forget_obj {A : AlgCat.{v} R} : (forget (AlgCat.{v} R)).obj A = A := rfl

@[deprecated ConcreteCategory.forget_map_eq_ofHom (since := "2026-03-03")]
/-
**AlgCat.forget_map** 是 Mathlib 中的一个引理，位于命名空间 `AlgCat`。
形式化陈述：forget_map {A B : AlgCat.{v} R} (f : A ⟶ B) : (forget (AlgCat.{v} R)).map 
f = (f : _ -> _)
参数：f : A ⟶ B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma forget_map {A B : AlgCat.{v} R} (f : A ⟶ B) :
    (forget (AlgCat.{v} R)).map f = (f : _ → _) :=
  rfl
/-
**AlgCat.** 是 Mathlib 中的一个实例，位于命名空间 `AlgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {S : AlgCat.{v} R} : Ring ((forget (AlgCat R)).obj S) :=
  inferInstanceAs <| Ring S.carrier
/-
**AlgCat.** 是 Mathlib 中的一个实例，位于命名空间 `AlgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {S : AlgCat.{v} R} : Algebra R ((forget (AlgCat R)).obj S) :=
  inferInstanceAs <| Algebra R S.carrier
/-
**AlgCat.hasForgetToRing** 是 Mathlib 中的一个实例，位于命名空间 `AlgCat`。
形式化陈述：hasForgetToRing : HasForget₂ (AlgCat.{v} R) RingCat.{v} where forget₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToRing : HasForget₂ (AlgCat.{v} R) RingCat.{v} where
  forget₂ :=
    { obj := fun A => RingCat.of A
      map := fun f => RingCat.ofHom f.hom.toRingHom }

@[simp]
/-
**AlgCat.forget** 是 Mathlib 中的一个引理，位于命名空间 `AlgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma forget₂_ringCat_obj (X : AlgCat.{v} R) :
    (forget₂ (AlgCat.{v} R) RingCat.{v}).obj X = RingCat.of X :=
  rfl

@[simp]
/-
**AlgCat.forget** 是 Mathlib 中的一个引理，位于命名空间 `AlgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma forget₂_ringCat_map {X Y : AlgCat.{v} R} (f : X ⟶ Y) :
    (forget₂ (AlgCat.{v} R) RingCat.{v}).map f = RingCat.ofHom f.hom :=
  rfl
/-
**AlgCat.** 是 Mathlib 中的一个实例，位于命名空间 `AlgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (A : AlgCat.{v} R) : Algebra R ((forget₂ (AlgCat.{v} R) RingCat).obj A) :=
  inferInstanceAs <| Algebra R A
/-
**AlgCat.hasForgetToModule** 是 Mathlib 中的一个实例，位于命名空间 `AlgCat`。
形式化陈述：hasForgetToModule : HasForget₂ (AlgCat.{v} R) (ModuleCat.{v} R) where forg
et₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToModule : HasForget₂ (AlgCat.{v} R) (ModuleCat.{v} R) where
  forget₂ :=
    { obj := fun M => ModuleCat.of R M
      map := fun f => ModuleCat.ofHom f.hom.toLinearMap }

@[simp]
/-
**AlgCat.forget** 是 Mathlib 中的一个引理，位于命名空间 `AlgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma forget₂_module_obj (X : AlgCat.{v} R) :
    (forget₂ (AlgCat.{v} R) (ModuleCat.{v} R)).obj X = ModuleCat.of R X :=
  rfl

@[simp]
/-
**AlgCat.forget** 是 Mathlib 中的一个引理，位于命名空间 `AlgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma forget₂_module_map {X Y : AlgCat.{v} R} (f : X ⟶ Y) :
    (forget₂ (AlgCat.{v} R) (ModuleCat.{v} R)).map f = ModuleCat.ofHom f.hom.toLinearMap :=
  rfl

/-- The "free algebra" functor, sending a type `S` to the free algebra on `S`. -/
@[simps! obj map]
/-
**AlgCat.free** 是 Mathlib 中的一个定义，位于命名空间 `AlgCat`。
形式化陈述：free : Type u ⥤ AlgCat.{u} R where obj S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The "free algebra" functor, sending a type `S` to the free algebra on `S`.
-/
def free : Type u ⥤ AlgCat.{u} R where
  obj S := of R (FreeAlgebra R S)
  map f := ofHom <| FreeAlgebra.lift _ <| FreeAlgebra.ι _ ∘ f

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The free/forget adjunction for `R`-algebras. -/
/-
**AlgCat.adj** 是 Mathlib 中的一个定义，位于命名空间 `AlgCat`。
形式化陈述：adj : free.{u} R ⊣ forget (AlgCat.{u} R)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The free/forget adjunction for `R`-algebras.
-/
def adj : free.{u} R ⊣ forget (AlgCat.{u} R) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ =>
        { toFun := fun f ↦ ↾((FreeAlgebra.lift _).symm f.hom)
          invFun := fun f ↦ ofHom <| (FreeAlgebra.lift _) f
          left_inv := fun f ↦ by aesop
          right_inv := fun f ↦ by aesop } }
/-
**AlgCat.** 是 Mathlib 中的一个实例，位于命名空间 `AlgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget (AlgCat.{u} R)).IsRightAdjoint := (adj R).isRightAdjoint

end AlgCat

variable {R}
variable {X₁ X₂ : Type v}

/-- Build an isomorphism in the category `AlgCat R` from an `AlgEquiv` between `Algebra`s. -/
@[simps]
/-
**AlgEquiv.toAlgebraIso** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AlgEquiv.toAlgebraIso {g₁ : Ring X₁} {g₂ : Ring X₂} {m₁ : Algebra R X₁} {m
₂ : Algebra R X₂} (e : X₁ ≃ₐ[R] X₂) : AlgCat.of R X₁ ≅ AlgCat.of R X₂ where hom
参数：e : X₁ ≃ₐ[R] X₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Build an isomorphism in the category `AlgCat R` from an `AlgEquiv` between `Alge
bra`s.
-/
def AlgEquiv.toAlgebraIso {g₁ : Ring X₁} {g₂ : Ring X₂} {m₁ : Algebra R X₁} {m₂ : Algebra R X₂}
    (e : X₁ ≃ₐ[R] X₂) : AlgCat.of R X₁ ≅ AlgCat.of R X₂ where
  hom := AlgCat.ofHom (e : X₁ →ₐ[R] X₂)
  inv := AlgCat.ofHom (e.symm : X₂ →ₐ[R] X₁)

namespace CategoryTheory.Iso

/-- Build an `AlgEquiv` from an isomorphism in the category `AlgCat R`. -/
@[simps]
/-
**CategoryTheory.Iso.toAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：toAlgEquiv {X Y : AlgCat.{v} R} (i : X ≅ Y) : X ≃ₐ[R] Y
参数：i : X ≅ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Build an `AlgEquiv` from an isomorphism in the category `AlgCat R`.
-/
def toAlgEquiv {X Y : AlgCat.{v} R} (i : X ≅ Y) : X ≃ₐ[R] Y :=
  { i.hom.hom with
    toFun := i.hom
    invFun := i.inv
    left_inv := fun x ↦ by simp
    right_inv := fun x ↦ by simp }

end CategoryTheory.Iso

/-- Algebra equivalences between `Algebra`s are the same as (isomorphic to) isomorphisms in
`AlgCat`. -/
@[simps]
/-
**algEquivIsoAlgebraIso** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：algEquivIsoAlgebraIso {X Y : Type v} [Ring X] [Ring Y] [Algebra R X] [Alge
bra R Y] : (X ≃ₐ[R] Y) ≅ (AlgCat.of R X ≅ AlgCat.of R Y) where hom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Algebra equivalences between `Algebra`s are the same as (isomorphic to) isomorph
isms in
`AlgCat`.
-/
def algEquivIsoAlgebraIso {X Y : Type v} [Ring X] [Ring Y] [Algebra R X] [Algebra R Y] :
    (X ≃ₐ[R] Y) ≅ (AlgCat.of R X ≅ AlgCat.of R Y) where
  hom := ↾fun e ↦ e.toAlgebraIso
  inv := ↾fun i ↦ i.toAlgEquiv
/-
**AlgCat.forget_reflects_isos** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：AlgCat.forget_reflects_isos : (forget (AlgCat.{v} R)).ReflectsIsomorphisms
 where reflects {X Y} f _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
· 使用定理 `MonoidHom.map_mul'`：∀ {M : Type u_10} {N : Type u_11} [inst : MulOne M] 
[inst_1 : MulOne N] (self : M →* N) (x y : M),   (↑self).toFun (x * y) = (↑self)
.toFun x…
· 使用定理 `RingHom.map_add'`：∀ {α : Type u_5} {β : Type u_6} [inst : NonAssocSemiri
ng α] [inst_1 : NonAssocSemiring β] (self : α →+* β) (x y : α),   (↑↑self).toFun
 (x + …
· 使用定理 `AlgHom.commutes'`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] 
[inst_…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
instance AlgCat.forget_reflects_isos : (forget (AlgCat.{v} R)).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget (AlgCat.{v} R)).map f)
    let e : X ≃ₐ[R] Y := { f.hom, i.toEquiv with }
    exact e.toAlgebraIso.isIso_hom

namespace AlgCat

/-- The restriction of scalars functor `AlgCat S ⥤ AlgCat R` induced by a ring homomorphism
`R →+* S`. -/
@[simps]
/-
**AlgCat.restrictScalars** 是 Mathlib 中的一个定义，位于命名空间 `AlgCat`。
形式化陈述：restrictScalars {R S : Type*} [CommRing R] [CommRing S] (f : R ->+* S) : A
lgCat.{v} S ⥤ AlgCat.{v} R where obj A
参数：f : R ->+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction of scalars functor `AlgCat S ⥤ AlgCat R` induced by a ring homom
orphism
`R →+* S`.
-/
def restrictScalars {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    AlgCat.{v} S ⥤ AlgCat.{v} R where
  obj A :=
    letI : Algebra R A := Algebra.compHom _ f
    AlgCat.of R A
  map {A B} g :=
    letI : Algebra R A := Algebra.compHom _ f
    letI : Algebra R B := Algebra.compHom _ f
    letI : Algebra R S := f.toAlgebra
    haveI : IsScalarTower R S A := .of_algebraMap_eq' rfl
    haveI : IsScalarTower R S B := .of_algebraMap_eq' rfl
    AlgCat.ofHom (g.hom.restrictScalars _)

-- The option makes `simps` produce the correct lemmas
set_option backward.isDefEq.respectTransparency false in
/-- Restricting scalars along the identity is isomorphic to the identity. -/
@[simps!]
/-
**AlgCat.restrictScalarsId'** 是 Mathlib 中的一个定义，位于命名空间 `AlgCat`。
形式化陈述：restrictScalarsId' {R : Type*} [CommRing R] (f : R ->+* R) (hf : f = .id R
) : AlgCat.restrictScalars.{v} f ≅ 𝟭 _
参数：f : R ->+* R；hf : f = .id R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restricting scalars along the identity is isomorphic to the identity.
-/
def restrictScalarsId' {R : Type*} [CommRing R] (f : R →+* R) (hf : f = .id R) :
    AlgCat.restrictScalars.{v} f ≅ 𝟭 _ :=
  NatIso.ofComponents
    fun A ↦ AlgEquiv.toAlgebraIso <|
      @AlgEquiv.ofRingEquiv (f := RingEquiv.refl _) _ _ _ _ _ _
        ((restrictScalars f).obj A).isAlgebra _ fun _ ↦ by subst hf; rfl

-- The option makes `simps` produce the correct lemmas
set_option backward.isDefEq.respectTransparency false in
/-- Restricting scalars along a composition is isomorphic to the composition
of restriction of scalars. -/
@[simps!]
/-
**AlgCat.restrictScalarsComp'** 是 Mathlib 中的一个定义，位于命名空间 `AlgCat`。
形式化陈述：restrictScalarsComp' {R S T : Type*} [CommRing R] [CommRing S] [CommRing T
] (f : R ->+* S) (g : S ->+* T) (gf : R ->+* T) (hfg : gf = g.comp f) : AlgCat.r
estrictScalars.{v} gf ≅ AlgCat.restrictScalars.{v} g ⋙ AlgCat.restrictScalars.{v
} f
参数：f : R ->+* S；g : S ->+* T；gf : R ->+* T；hfg : gf = g.comp f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restricting scalars along a composition is isomorphic to the composition
of restriction of scalars.
-/
def restrictScalarsComp' {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S)
      (g : S →+* T) (gf : R →+* T) (hfg : gf = g.comp f) :
    AlgCat.restrictScalars.{v} gf ≅
      AlgCat.restrictScalars.{v} g ⋙ AlgCat.restrictScalars.{v} f :=
  NatIso.ofComponents
    fun A ↦ AlgEquiv.toAlgebraIso <|
      @AlgEquiv.ofRingEquiv (f := RingEquiv.refl _) _ _ _ _ _ _
        ((restrictScalars gf).obj A).isAlgebra
        ((restrictScalars f).obj ((restrictScalars g).obj A)).isAlgebra
        fun _ ↦ by subst hfg; rfl

/-- A ring isomorphism induces an equivalence of categories of algebras. -/
@[simps]
/-
**AlgCat.restrictScalarsEquivalenceOfRingEquiv** 是 Mathlib 中的一个定义，位于命名空间 `AlgCat
`。
形式化陈述：restrictScalarsEquivalenceOfRingEquiv {R S : Type*} [CommRing R] [CommRing
 S] (e : R ≃+* S) : AlgCat.{u} S ≌ AlgCat.{u} R where functor
参数：e : R ≃+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A ring isomorphism induces an equivalence of categories of algebras.
-/
def restrictScalarsEquivalenceOfRingEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    AlgCat.{u} S ≌ AlgCat.{u} R where
  functor := restrictScalars e.toRingHom
  inverse := restrictScalars e.symm.toRingHom
  unitIso := (restrictScalarsId' _ rfl).symm ≪≫
    restrictScalarsComp' _ _ _ e.toRingHom_comp_symm_toRingHom.symm
  counitIso := (restrictScalarsComp' _ _ _ e.symm_toRingHom_comp_toRingHom.symm).symm ≪≫
    restrictScalarsId' _ rfl
/-
**AlgCat.** 是 Mathlib 中的一个实例，位于命名空间 `AlgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    (restrictScalars e.toRingHom).IsEquivalence :=
  inferInstanceAs <| (restrictScalarsEquivalenceOfRingEquiv e).functor.IsEquivalence
/-
**AlgCat.** 是 Mathlib 中的一个实例，位于命名空间 `AlgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    (restrictScalars e.symm.toRingHom).IsEquivalence :=
  inferInstanceAs <| (restrictScalarsEquivalenceOfRingEquiv e).inverse.IsEquivalence

/-- The equivalence of categories of `ℤ`-algebras and rings. -/
@[simps! (dsimpLhs := true) functor inverse_obj inverse_map_hom unitIso_hom_app_hom_apply counitIso]
/-
**AlgCat.intEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `AlgCat`。
形式化陈述：intEquivalence : AlgCat.{u} Int ≌ RingCat.{u} where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence of categories of `ℤ`-algebras and rings.
-/
def intEquivalence : AlgCat.{u} ℤ ≌ RingCat.{u} where
  functor := forget₂ _ _
  inverse.obj A := AlgCat.of ℤ A
  inverse.map f := AlgCat.ofHom f.hom.toIntAlgHom
  unitIso := NatIso.ofComponents
    fun A ↦ AlgEquiv.toAlgebraIso (@.ofRingEquiv (f := RingEquiv.refl _)
      _ _ _ _ _ _ _ (Ring.toIntAlgebra _) fun _ ↦ by simp)
  counitIso := Iso.refl _
/-
**AlgCat.** 是 Mathlib 中的一个实例，位于命名空间 `AlgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget₂ (AlgCat.{u} ℤ) RingCat.{u}).IsEquivalence :=
  inferInstanceAs <| intEquivalence.functor.IsEquivalence

end AlgCat

