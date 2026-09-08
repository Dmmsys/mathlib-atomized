/-
Copyright (c) 2025 Yaël Dillies, Christian Merten, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Christian Merten, Michał Mrugała, Andrew Yang
-/
module

public import Mathlib.Algebra.Category.AlgCat.Basic
public import Mathlib.Algebra.Category.Ring.Under.Basic
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.CategoryTheory.WithTerminal.Cone

/-!
# The category of commutative algebras over a commutative ring

This file defines the bundled category `CommAlgCat` of commutative algebras over a fixed commutative
ring `R` along with the forgetful functors to `CommRingCat` and `AlgCat`.
-/

@[expose] public section

open CategoryTheory Limits

universe w v u

variable {R : Type u} [CommRing R]

variable (R) in
/-- The category of R-algebras and their morphisms. -/
/-
**CommAlgCat** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u) → [CommRing R] → Type (max u (v + 1))
参数：v + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of R-algebras and their morphisms.
-/
structure CommAlgCat where
  private mk ::
  /-- The underlying type. -/
  carrier : Type v
  [commRing : CommRing carrier]
  [algebra : Algebra R carrier]

namespace CommAlgCat
variable {A B C : CommAlgCat.{v} R} {X Y Z : Type v} [CommRing X] [Algebra R X]
  [CommRing Y] [Algebra R Y] [CommRing Z] [Algebra R Z]

attribute [instance] commRing algebra

initialize_simps_projections CommAlgCat (-commRing, -algebra)

/-
**CommAlgCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommAlgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort (CommAlgCat R) (Type v) := ⟨carrier⟩

attribute [coe] carrier

variable (R) in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The object in the category of R-algebras associated to a type equipped with the appropriate
typeclasses. This is the preferred way to construct a term of `CommAlgCat R`. -/
/-
**CommAlgCat.of** 是 Mathlib 中的一个缩写定义，位于命名空间 `CommAlgCat`。
形式化陈述：of (X : Type v) [CommRing X] [Algebra R X] : CommAlgCat.{v} R
参数：X : Type v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The object in the category of R-algebras associated to a type equipped with the 
appropriate
typeclasses. This is the preferred way to construct a term of `CommAlgCat R`.
-/
abbrev of (X : Type v) [CommRing X] [Algebra R X] : CommAlgCat.{v} R := ⟨X⟩

variable (R) in
/-
**CommAlgCat.coe_of** 是 Mathlib 中的一个引理，位于命名空间 `CommAlgCat`。
形式化陈述：coe_of (X : Type v) [CommRing X] [Algebra R X] : (of R X : Type v) = X
参数：X : Type v。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_of (X : Type v) [CommRing X] [Algebra R X] : (of R X : Type v) = X := rfl

/-- The type of morphisms in `CommAlgCat R`. -/
@[ext]
/-
**CommAlgCat.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `CommAlgCat`。
形式化陈述：{R : Type u} → [inst : CommRing R] → CommAlgCat R → CommAlgCat R → Type v
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of morphisms in `CommAlgCat R`.
-/
structure Hom (A B : CommAlgCat.{v} R) where
  private mk ::
  /-- The underlying algebra map. -/
  hom' : A →ₐ[R] B

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**CommAlgCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommAlgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (CommAlgCat.{v} R) where
  Hom A B := Hom A B
  id A := ⟨AlgHom.id R A⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**CommAlgCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommAlgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ConcreteCategory (CommAlgCat.{v} R) (· →ₐ[R] ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `CommAlgCat` back into an `AlgHom`. -/
/-
**CommAlgCat.Hom.hom** 是 Mathlib 中的一个定义，位于命名空间 `CommAlgCat.Hom`。
形式化陈述：{R : Type u} → [inst : CommRing R] → {A B : CommAlgCat R} → A.Hom B → ↑A →
ₐ[R] ↑B
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a morphism in `CommAlgCat` back into an `AlgHom`.
-/
abbrev Hom.hom (f : Hom A B) := ConcreteCategory.hom (C := CommAlgCat R) f

/-- Typecheck an `AlgHom` as a morphism in `CommAlgCat`. -/
/-
**CommAlgCat.ofHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `CommAlgCat`。
形式化陈述：ofHom (f : X ->ₐ[R] Y) : of R X ⟶ of R Y
参数：f : X ->ₐ[R] Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typecheck an `AlgHom` as a morphism in `CommAlgCat`.
-/
abbrev ofHom (f : X →ₐ[R] Y) : of R X ⟶ of R Y := ConcreteCategory.ofHom (C := CommAlgCat R) f

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
/-
**CommAlgCat.Hom.Simps.hom** 是 Mathlib 中的一个定义，位于命名空间 `CommAlgCat.Hom.Simps`。
形式化陈述：{R : Type u} → [inst : CommRing R] → (A B : CommAlgCat R) → A.Hom B → ↑A →
ₐ[R] ↑B
参数：A B : CommAlgCat R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas.
-/
def Hom.Simps.hom (A B : CommAlgCat.{v} R) (f : Hom A B) := f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

/-
**CommAlgCat.hom_id** 是 Mathlib 中的一个定理，位于命名空间 `CommAlgCat`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {A : CommAlgCat R},   CommAlgCat.Hom.ho
m (CategoryTheory.CategoryStruct.id A) = AlgHom.id R ↑A
参数：CategoryTheory.CategoryStruct.id A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep 
them for `dsimp`.
-/
@[simp] lemma hom_id : (𝟙 A : A ⟶ A).hom = AlgHom.id R A := rfl

/- Provided for rewriting. -/
/-
**CommAlgCat.id_apply** 是 Mathlib 中的一个引理，位于命名空间 `CommAlgCat`。
形式化陈述：id_apply (A : CommAlgCat.{v} R) (a : A) : (𝟙 A : A ⟶ A) a = a
参数：A : CommAlgCat.{v} R；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Provided for rewriting.
-/
lemma id_apply (A : CommAlgCat.{v} R) (a : A) : (𝟙 A : A ⟶ A) a = a := by simp
/-
**CommAlgCat.hom_comp** 是 Mathlib 中的一个定理，位于命名空间 `CommAlgCat`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {A B C : CommAlgCat R} (f : A ⟶ B) (g :
 B ⟶ C),   CommAlgCat.Hom.hom (CategoryTheory.CategoryStruct.comp f g) = (CommAl
gCat.Hom.hom g).comp (CommAlgCat.Hom.hom f)
参数：f : A ⟶ B；g : B ⟶ C；CategoryTheory.CategoryStruct.comp f g；CommAlgCat.Hom.hom
 g；CommAlgCat.Hom.hom f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma hom_comp (f : A ⟶ B) (g : B ⟶ C) : (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
/-
**CommAlgCat.comp_apply** 是 Mathlib 中的一个引理，位于命名空间 `CommAlgCat`。
形式化陈述：comp_apply (f : A ⟶ B) (g : B ⟶ C) (a : A) : (f ≫ g) a = g (f a)
参数：f : A ⟶ B；g : B ⟶ C；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Provided for rewriting.
-/
lemma comp_apply (f : A ⟶ B) (g : B ⟶ C) (a : A) : (f ≫ g) a = g (f a) := by simp
/-
**CommAlgCat.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `CommAlgCat`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {A B : CommAlgCat R} {f g : A ⟶ B},   C
ommAlgCat.Hom.hom f = CommAlgCat.Hom.hom g → f = g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CommAlgCat.Hom.ext`：∀ {R : Type u} {inst : CommRing R} {A B : CommAlgCat
 R} {x y : A.Hom B}, x.hom' = y.hom' → x = y
-/
@[ext] lemma hom_ext {f g : A ⟶ B} (hf : f.hom = g.hom) : f = g := Hom.ext hf
/-
**CommAlgCat.hom_ofHom** 是 Mathlib 中的一个定理，位于命名空间 `CommAlgCat`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {X Y : Type v} [inst_1 : CommRing X] [i
nst_2 : Algebra R X] [inst_3 : CommRing Y]   [inst_4 : Algebra R Y] (f : X →ₐ[R]
 Y), CommAlgCat.Hom.hom (CommAlgCat.ofHom f) = f
参数：f : X →ₐ[R] Y；CommAlgCat.ofHom f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma hom_ofHom (f : X →ₐ[R] Y) : (ofHom f).hom = f := rfl
/-
**CommAlgCat.ofHom_hom** 是 Mathlib 中的一个定理，位于命名空间 `CommAlgCat`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {A B : CommAlgCat R} (f : A ⟶ B), CommA
lgCat.ofHom (CommAlgCat.Hom.hom f) = f
参数：f : A ⟶ B；CommAlgCat.Hom.hom f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofHom_hom (f : A ⟶ B) : ofHom f.hom = f := rfl
/-
**CommAlgCat.ofHom_id** 是 Mathlib 中的一个定理，位于命名空间 `CommAlgCat`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {X : Type v} [inst_1 : CommRing X] [ins
t_2 : Algebra R X],   CommAlgCat.ofHom (AlgHom.id R X) = CategoryTheory.Category
Struct.id (CommAlgCat.of R X)
参数：AlgHom.id R X；CommAlgCat.of R X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofHom_id : ofHom (.id R X) = 𝟙 (of R X) := rfl

@[simp]
/-
**CommAlgCat.ofHom_comp** 是 Mathlib 中的一个引理，位于命名空间 `CommAlgCat`。
形式化陈述：ofHom_comp (f : X ->ₐ[R] Y) (g : Y ->ₐ[R] Z) : ofHom (g.comp f) = ofHom f 
≫ ofHom g
参数：f : X ->ₐ[R] Y；g : Y ->ₐ[R] Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_comp (f : X →ₐ[R] Y) (g : Y →ₐ[R] Z) : ofHom (g.comp f) = ofHom f ≫ ofHom g := rfl
/-
**CommAlgCat.ofHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `CommAlgCat`。
形式化陈述：ofHom_apply (f : X ->ₐ[R] Y) (x : X) : ofHom f x = f x
参数：f : X ->ₐ[R] Y；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_apply (f : X →ₐ[R] Y) (x : X) : ofHom f x = f x := rfl
/-
**CommAlgCat.inv_hom_apply** 是 Mathlib 中的一个引理，位于命名空间 `CommAlgCat`。
形式化陈述：inv_hom_apply (e : A ≅ B) (x : A) : e.inv (e.hom x) = x
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
lemma inv_hom_apply (e : A ≅ B) (x : A) : e.inv (e.hom x) = x := by simp
/-
**CommAlgCat.hom_inv_apply** 是 Mathlib 中的一个引理，位于命名空间 `CommAlgCat`。
形式化陈述：hom_inv_apply (e : A ≅ B) (x : B) : e.hom (e.inv x) = x
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
lemma hom_inv_apply (e : A ≅ B) (x : B) : e.hom (e.inv x) = x := by simp
/-
**CommAlgCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommAlgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (CommAlgCat R) := ⟨of R R⟩
/-
**CommAlgCat.forget_obj** 是 Mathlib 中的一个引理，位于命名空间 `CommAlgCat`。
形式化陈述：forget_obj (A : CommAlgCat.{v} R) : (forget (CommAlgCat.{v} R)).obj A = A
参数：A : CommAlgCat.{v} R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma forget_obj (A : CommAlgCat.{v} R) : (forget (CommAlgCat.{v} R)).obj A = A := rfl

@[deprecated ConcreteCategory.forget_map_eq_ofHom (since := "2026-03-06")]
/-
**CommAlgCat.forget_map** 是 Mathlib 中的一个引理，位于命名空间 `CommAlgCat`。
形式化陈述：forget_map (f : A ⟶ B) : (forget (CommAlgCat.{v} R)).map f = (f : _ -> _)
参数：f : A ⟶ B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma forget_map (f : A ⟶ B) : (forget (CommAlgCat.{v} R)).map f = (f : _ → _) := rfl
/-
**CommAlgCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommAlgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CommRing ((forget (CommAlgCat R)).obj A) := inferInstanceAs <| CommRing A
/-
**CommAlgCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommAlgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Algebra R ((forget (CommAlgCat R)).obj A) := inferInstanceAs <| Algebra R A
/-
**CommAlgCat.hasForgetToCommRingCat** 是 Mathlib 中的一个实例，位于命名空间 `CommAlgCat`。
形式化陈述：hasForgetToCommRingCat : HasForget₂ (CommAlgCat.{v} R) CommRingCat.{v} whe
re forget₂.obj A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToCommRingCat : HasForget₂ (CommAlgCat.{v} R) CommRingCat.{v} where
  forget₂.obj A := .of A
  forget₂.map f := CommRingCat.ofHom f.hom.toRingHom
/-
**CommAlgCat.hasForgetToAlgCat** 是 Mathlib 中的一个实例，位于命名空间 `CommAlgCat`。
形式化陈述：hasForgetToAlgCat : HasForget₂ (CommAlgCat.{v} R) (AlgCat.{v} R) where for
get₂.obj A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToAlgCat : HasForget₂ (CommAlgCat.{v} R) (AlgCat.{v} R) where
  forget₂.obj A := .of R A
  forget₂.map f := AlgCat.ofHom f.hom
/-
**CommAlgCat.forget** 是 Mathlib 中的一个引理，位于命名空间 `CommAlgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma forget₂_commRingCat_obj (A : CommAlgCat.{v} R) :
    (forget₂ (CommAlgCat.{v} R) CommRingCat.{v}).obj A = .of A := rfl
/-
**CommAlgCat.forget** 是 Mathlib 中的一个引理，位于命名空间 `CommAlgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma forget₂_commRingCat_map (f : A ⟶ B) :
    (forget₂ (CommAlgCat.{v} R) CommRingCat.{v}).map f = CommRingCat.ofHom f.hom := rfl
/-
**CommAlgCat.forget** 是 Mathlib 中的一个引理，位于命名空间 `CommAlgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma forget₂_algCat_obj (A : CommAlgCat.{v} R) :
    (forget₂ (CommAlgCat.{v} R) (AlgCat.{v} R)).obj A = .of R A := rfl
/-
**CommAlgCat.forget** 是 Mathlib 中的一个引理，位于命名空间 `CommAlgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma forget₂_algCat_map (f : A ⟶ B) :
    (forget₂ (CommAlgCat.{v} R) (AlgCat.{v} R)).map f = AlgCat.ofHom f.hom := rfl

/-- Build an isomorphism in the category `CommAlgCat R` from an `AlgEquiv` between commutative
`Algebra`s. -/
@[simps]
/-
**CommAlgCat.isoMk** 是 Mathlib 中的一个定义，位于命名空间 `CommAlgCat`。
形式化陈述：isoMk {X Y : Type v} {_ : CommRing X} {_ : CommRing Y} {_ : Algebra R X} {
_ : Algebra R Y} (e : X ≃ₐ[R] Y) : of R X ≅ of R Y where hom
参数：e : X ≃ₐ[R] Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Build an isomorphism in the category `CommAlgCat R` from an `AlgEquiv` between c
ommutative
`Algebra`s.
-/
def isoMk {X Y : Type v} {_ : CommRing X} {_ : CommRing Y} {_ : Algebra R X} {_ : Algebra R Y}
    (e : X ≃ₐ[R] Y) : of R X ≅ of R Y where
  hom := ofHom (e : X →ₐ[R] Y)
  inv := ofHom (e.symm : Y →ₐ[R] X)

/-- Build an `AlgEquiv` from an isomorphism in the category `CommAlgCat R`. -/
@[simps]
/-
**CommAlgCat.algEquivOfIso** 是 Mathlib 中的一个定义，位于命名空间 `CommAlgCat`。
形式化陈述：algEquivOfIso (i : A ≅ B) : A ≃ₐ[R] B where __
参数：i : A ≅ B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Build an `AlgEquiv` from an isomorphism in the category `CommAlgCat R`.
-/
def algEquivOfIso (i : A ≅ B) : A ≃ₐ[R] B where
  __ := i.hom.hom
  toFun := i.hom
  invFun := i.inv
  left_inv x := by simp
  right_inv x := by simp

/-- Algebra equivalences between `Algebra`s are the same as isomorphisms in `CommAlgCat`. -/
@[simps]
/-
**CommAlgCat.isoEquivAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CommAlgCat`。
形式化陈述：isoEquivAlgEquiv : (of R X ≅ of R Y) ≃ (X ≃ₐ[R] Y) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Algebra equivalences between `Algebra`s are the same as isomorphisms in `CommAlg
Cat`.
-/
def isoEquivAlgEquiv : (of R X ≅ of R Y) ≃ (X ≃ₐ[R] Y) where
  toFun := algEquivOfIso
  invFun := isoMk
/-
**CommAlgCat.reflectsIsomorphisms_forget** 是 Mathlib 中的一个实例，位于命名空间 `CommAlgCat`。
形式化陈述：reflectsIsomorphisms_forget : (forget (CommAlgCat.{u} R)).ReflectsIsomorph
isms where reflects {X Y} f _
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
instance reflectsIsomorphisms_forget : (forget (CommAlgCat.{u} R)).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget (CommAlgCat.{u} R)).map f)
    let e : X ≃ₐ[R] Y := { f.hom, i.toEquiv with }
    exact (isoMk e).isIso_hom

variable (R)

/-- Universe lift functor for commutative algebras. -/
/-
**CommAlgCat.uliftFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CommAlgCat`。
形式化陈述：uliftFunctor : CommAlgCat.{v} R ⥤ CommAlgCat.{max v w} R where obj A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Universe lift functor for commutative algebras.
-/
def uliftFunctor : CommAlgCat.{v} R ⥤ CommAlgCat.{max v w} R where
  obj A := .of R <| ULift A
  map {A B} f := CommAlgCat.ofHom <|
    ULift.algEquiv.symm.toAlgHom.comp <| f.hom.comp ULift.algEquiv.toAlgHom

/-- The universe lift functor for commutative algebras is fully faithful. -/
/-
**CommAlgCat.fullyFaithfulUliftFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CommAlgCat`。
形式化陈述：fullyFaithfulUliftFunctor : (uliftFunctor R).FullyFaithful where preimage 
{A B} f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The universe lift functor for commutative algebras is fully faithful.
-/
def fullyFaithfulUliftFunctor : (uliftFunctor R).FullyFaithful where
  preimage {A B} f :=
    CommAlgCat.ofHom <| ULift.algEquiv.toAlgHom.comp <| f.hom.comp ULift.algEquiv.symm.toAlgHom
/-
**CommAlgCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommAlgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (uliftFunctor R).Full :=
  (fullyFaithfulUliftFunctor R).full
/-
**CommAlgCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommAlgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (uliftFunctor R).Faithful :=
  (fullyFaithfulUliftFunctor R).faithful

end CommAlgCat

/-- The category of commutative algebras over a commutative ring `R` is the same as commutative
rings under `R`. -/
@[simps]
/-
**commAlgCatEquivUnder** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：commAlgCatEquivUnder (R : CommRingCat) : CommAlgCat R ≌ Under R where func
tor.obj A
参数：R : CommRingCat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of commutative algebras over a commutative ring `R` is the same as 
commutative
rings under `R`.
-/
def commAlgCatEquivUnder (R : CommRingCat) : CommAlgCat R ≌ Under R where
  functor.obj A := R.mkUnder A
  functor.map {A B} f := f.hom.toUnder
  inverse.obj A := .of _ A
  inverse.map {A B} f := CommAlgCat.ofHom <| CommRingCat.toAlgHom f
  unitIso := NatIso.ofComponents fun A ↦
    CommAlgCat.isoMk { toRingEquiv := .refl A, commutes' _ := rfl }
  counitIso := .refl _

-- TODO: Generalize to `UnivLE.{u, v}` once `commAlgCatEquivUnder` is generalized.
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasColimits (CommAlgCat.{u} R) :=
  Adjunction.has_colimits_of_equivalence (commAlgCatEquivUnder (.of R)).functor

-- TODO: Generalize to `UnivLE.{u, v}` once `commAlgCatEquivUnder` is generalized.
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasLimits (CommAlgCat.{u} R) :=
  Adjunction.has_limits_of_equivalence (commAlgCatEquivUnder (.of R)).functor
