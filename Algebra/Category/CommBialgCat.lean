/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Andrew Yang
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.RingTheory.Bialgebra.Equiv

/-!
# The category of commutative bialgebras over a commutative ring

This file defines the bundled category `CommBialgCat R` of commutative bialgebras over a fixed
commutative ring `R` along with the forgetful functor to `CommAlgCat`.
-/

@[expose] public section

noncomputable section

open Bialgebra Coalgebra Opposite CategoryTheory Limits MonObj
open scoped MonoidalCategory

universe v u
variable {R : Type u} [CommRing R]

variable (R) in
/-- The category of commutative `R`-bialgebras and their morphisms. -/
/-
**CommBialgCat** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u) → [CommRing R] → Type (max u (v + 1))
参数：v + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of commutative `R`-bialgebras and their morphisms.
-/
structure CommBialgCat where
  private mk ::
  /-- The underlying type. -/
  carrier : Type v
  [commRing : CommRing carrier]
  [bialgebra : Bialgebra R carrier]

namespace CommBialgCat
variable {A B C : CommBialgCat.{v} R} {X Y Z : Type v} [CommRing X] [Bialgebra R X]
  [CommRing Y] [Bialgebra R Y] [CommRing Z] [Bialgebra R Z]

attribute [instance] commRing bialgebra

initialize_simps_projections CommBialgCat (-commRing, -bialgebra)

/-
**CommBialgCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommBialgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort (CommBialgCat R) (Type v) := ⟨carrier⟩

attribute [coe] CommBialgCat.carrier

variable (R) in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Turn an unbundled `R`-bialgebra into the corresponding object in the category of `R`-bialgebras.

This is the preferred way to construct a term of `CommBialgCat R`. -/
/-
**CommBialgCat.of** 是 Mathlib 中的一个缩写定义，位于命名空间 `CommBialgCat`。
形式化陈述：of (X : Type v) [CommRing X] [Bialgebra R X] : CommBialgCat.{v} R
参数：X : Type v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn an unbundled `R`-bialgebra into the corresponding object in the category of
 `R`-bialgebras.

This is the preferred way to construct a term of `CommBialgCat R`.
-/
abbrev of (X : Type v) [CommRing X] [Bialgebra R X] : CommBialgCat.{v} R := ⟨X⟩

variable (R) in
/-
**CommBialgCat.coe_of** 是 Mathlib 中的一个引理，位于命名空间 `CommBialgCat`。
形式化陈述：coe_of (X : Type v) [CommRing X] [Bialgebra R X] : (of R X : Type v) = X
参数：X : Type v。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_of (X : Type v) [CommRing X] [Bialgebra R X] : (of R X : Type v) = X := rfl

/-- The type of morphisms in `CommBialgCat R`. -/
@[ext]
/-
**CommBialgCat.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `CommBialgCat`。
形式化陈述：{R : Type u} → [inst : CommRing R] → CommBialgCat R → CommBialgCat R → Typ
e v
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of morphisms in `CommBialgCat R`.
-/
structure Hom (A B : CommBialgCat.{v} R) where
  private mk ::
  /-- The underlying bialgebra map. -/
  hom' : A →ₐc[R] B

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**CommBialgCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommBialgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (CommBialgCat.{v} R) where
  Hom A B := Hom A B
  id A := ⟨.id R A⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**CommBialgCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommBialgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ConcreteCategory (CommBialgCat.{v} R) (· →ₐc[R] ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `CommBialgCat` back into a `BialgHom`. -/
/-
**CommBialgCat.Hom.hom** 是 Mathlib 中的一个定义，位于命名空间 `CommBialgCat.Hom`。
形式化陈述：{R : Type u} → [inst : CommRing R] → {A B : CommBialgCat R} → A.Hom B → ↑A
 →ₐc[R] ↑B
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a morphism in `CommBialgCat` back into a `BialgHom`.
-/
abbrev Hom.hom (f : Hom A B) : A →ₐc[R] B := ConcreteCategory.hom (C := CommBialgCat R) f

/-- Typecheck a `BialgHom` as a morphism in `CommBialgCat R`. -/
/-
**CommBialgCat.ofHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `CommBialgCat`。
形式化陈述：ofHom {X Y : Type v} {_ : CommRing X} {_ : CommRing Y} {_ : Bialgebra R X}
 {_ : Bialgebra R Y} (f : X ->ₐc[R] Y) : of R X ⟶ of R Y
参数：f : X ->ₐc[R] Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typecheck a `BialgHom` as a morphism in `CommBialgCat R`.
-/
abbrev ofHom {X Y : Type v} {_ : CommRing X} {_ : CommRing Y} {_ : Bialgebra R X}
    {_ : Bialgebra R Y} (f : X →ₐc[R] Y) : of R X ⟶ of R Y :=
  ConcreteCategory.ofHom (C := CommBialgCat R) f

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
/-
**CommBialgCat.Hom.Simps.hom** 是 Mathlib 中的一个定义，位于命名空间 `CommBialgCat.Hom.Simps`。
形式化陈述：{R : Type u} → [inst : CommRing R] → (A B : CommBialgCat R) → A.Hom B → ↑A
 →ₐc[R] ↑B
参数：A B : CommBialgCat R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas.
-/
def Hom.Simps.hom (A B : CommBialgCat.{v} R) (f : Hom A B) := f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

/-
**CommBialgCat.hom_id** 是 Mathlib 中的一个定理，位于命名空间 `CommBialgCat`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {A : CommBialgCat R},   CommBialgCat.Ho
m.hom (CategoryTheory.CategoryStruct.id A) = BialgHom.id R ↑A
参数：CategoryTheory.CategoryStruct.id A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep 
them for `dsimp`.
-/
@[simp] lemma hom_id : (𝟙 A : A ⟶ A).hom = .id R A := rfl
/-
**CommBialgCat.hom_comp** 是 Mathlib 中的一个定理，位于命名空间 `CommBialgCat`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {A B C : CommBialgCat R} (f : A ⟶ B) (g
 : B ⟶ C),   CommBialgCat.Hom.hom (CategoryTheory.CategoryStruct.comp f g) = (Co
mmBialgCat.Hom.hom g).comp (CommBialgCat.Hom.hom f)
参数：f : A ⟶ B；g : B ⟶ C；CategoryTheory.CategoryStruct.comp f g；CommBialgCat.Hom.h
om g；CommBialgCat.Hom.hom f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep 
them for `dsimp`.
-/
@[simp] lemma hom_comp (f : A ⟶ B) (g : B ⟶ C) : (f ≫ g).hom = g.hom.comp f.hom := rfl
/-
**CommBialgCat.id_apply** 是 Mathlib 中的一个引理，位于命名空间 `CommBialgCat`。
形式化陈述：id_apply (A : CommBialgCat.{v} R) (a : A) : (𝟙 A : A ⟶ A) a = a
参数：A : CommBialgCat.{v} R；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BialgHom.id_apply`：∀ (R : Type u_1) (A : Type u_2) [inst : CommSemiring 
R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : CoalgebraStruct R A]
 (x : A…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep 
them for `dsimp`.
-/
lemma id_apply (A : CommBialgCat.{v} R) (a : A) : (𝟙 A : A ⟶ A) a = a := by simp
/-
**CommBialgCat.comp_apply** 是 Mathlib 中的一个引理，位于命名空间 `CommBialgCat`。
形式化陈述：comp_apply (f : A ⟶ B) (g : B ⟶ C) (a : A) : (f ≫ g) a = g (f a)
参数：f : A ⟶ B；g : B ⟶ C；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BialgHom.comp_apply`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} {C :
 Type u_4} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Semiring B]
 [inst_3 …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_apply (f : A ⟶ B) (g : B ⟶ C) (a : A) : (f ≫ g) a = g (f a) := by simp
/-
**CommBialgCat.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `CommBialgCat`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {A B : CommBialgCat R} {f g : A ⟶ B},  
 CommBialgCat.Hom.hom f = CommBialgCat.Hom.hom g → f = g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CommBialgCat.Hom.ext`：∀ {R : Type u} {inst : CommRing R} {A B : CommBial
gCat R} {x y : A.Hom B}, x.hom' = y.hom' → x = y
-/
@[ext] lemma hom_ext {f g : A ⟶ B} (hf : f.hom = g.hom) : f = g := Hom.ext hf
/-
**CommBialgCat.hom_ofHom** 是 Mathlib 中的一个定理，位于命名空间 `CommBialgCat`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {X Y : Type v} [inst_1 : CommRing X] [i
nst_2 : Bialgebra R X] [inst_3 : CommRing Y]   [inst_4 : Bialgebra R Y] (f : X →
ₐc[R] Y), CommBialgCat.Hom.hom (CommBialgCat.ofHom f) = f
参数：f : X →ₐc[R] Y；CommBialgCat.ofHom f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma hom_ofHom (f : X →ₐc[R] Y) : (ofHom f).hom = f := rfl
/-
**CommBialgCat.ofHom_hom** 是 Mathlib 中的一个定理，位于命名空间 `CommBialgCat`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {A B : CommBialgCat R} (f : A ⟶ B), Com
mBialgCat.ofHom (CommBialgCat.Hom.hom f) = f
参数：f : A ⟶ B；CommBialgCat.Hom.hom f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofHom_hom (f : A ⟶ B) : ofHom f.hom = f := rfl
/-
**CommBialgCat.ofHom_id** 是 Mathlib 中的一个定理，位于命名空间 `CommBialgCat`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {X : Type v} [inst_1 : CommRing X] [ins
t_2 : Bialgebra R X],   CommBialgCat.ofHom (BialgHom.id R X) = CategoryTheory.Ca
tegoryStruct.id (CommBialgCat.of R X)
参数：BialgHom.id R X；CommBialgCat.of R X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofHom_id : ofHom (.id R X) = 𝟙 (of R X) := rfl

@[simp]
/-
**CommBialgCat.ofHom_comp** 是 Mathlib 中的一个引理，位于命名空间 `CommBialgCat`。
形式化陈述：ofHom_comp (f : X ->ₐc[R] Y) (g : Y ->ₐc[R] Z) : ofHom (g.comp f) = ofHom 
f ≫ ofHom g
参数：f : X ->ₐc[R] Y；g : Y ->ₐc[R] Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_comp (f : X →ₐc[R] Y) (g : Y →ₐc[R] Z) : ofHom (g.comp f) = ofHom f ≫ ofHom g := rfl
/-
**CommBialgCat.ofHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `CommBialgCat`。
形式化陈述：ofHom_apply (f : X ->ₐc[R] Y) (x : X) : ofHom f x = f x
参数：f : X ->ₐc[R] Y；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_apply (f : X →ₐc[R] Y) (x : X) : ofHom f x = f x := rfl
/-
**CommBialgCat.inv_hom_apply** 是 Mathlib 中的一个引理，位于命名空间 `CommBialgCat`。
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
**CommBialgCat.hom_inv_apply** 是 Mathlib 中的一个引理，位于命名空间 `CommBialgCat`。
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
**CommBialgCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommBialgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (CommBialgCat R) := ⟨of R R⟩
/-
**CommBialgCat.forget_obj** 是 Mathlib 中的一个引理，位于命名空间 `CommBialgCat`。
形式化陈述：forget_obj (A : CommBialgCat.{v} R) : (forget (CommBialgCat.{v} R)).obj A 
= A
参数：A : CommBialgCat.{v} R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma forget_obj (A : CommBialgCat.{v} R) : (forget (CommBialgCat.{v} R)).obj A = A :=
  rfl

@[deprecated ConcreteCategory.forget_map_eq_ofHom (since := "2026-03-06")]
/-
**CommBialgCat.forget_map** 是 Mathlib 中的一个引理，位于命名空间 `CommBialgCat`。
形式化陈述：forget_map (f : A ⟶ B) : (forget (CommBialgCat.{v} R)).map f = (f : _ -> _
)
参数：f : A ⟶ B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma forget_map (f : A ⟶ B) : (forget (CommBialgCat.{v} R)).map f = (f : _ → _) := rfl
/-
**CommBialgCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommBialgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CommRing ((forget (CommBialgCat R)).obj A) := inferInstanceAs <| CommRing A
/-
**CommBialgCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommBialgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Bialgebra R ((forget (CommBialgCat R)).obj A) := inferInstanceAs <| Bialgebra R A
/-
**CommBialgCat.hasForgetToCommAlgCat** 是 Mathlib 中的一个实例，位于命名空间 `CommBialgCat`。
形式化陈述：hasForgetToCommAlgCat : HasForget₂ (CommBialgCat.{v} R) (CommAlgCat.{v} R)
 where forget₂.obj M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToCommAlgCat : HasForget₂ (CommBialgCat.{v} R) (CommAlgCat.{v} R) where
  forget₂.obj M := .of R M
  forget₂.map f := CommAlgCat.ofHom f.hom.toAlgHom
/-
**CommBialgCat.forget** 是 Mathlib 中的一个引理，位于命名空间 `CommBialgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma forget₂_commAlgCat_obj (A : CommBialgCat.{v} R) :
    (forget₂ (CommBialgCat.{v} R) (CommAlgCat.{v} R)).obj A = .of R A := rfl
/-
**CommBialgCat.forget** 是 Mathlib 中的一个引理，位于命名空间 `CommBialgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma forget₂_commAlgCat_map (f : A ⟶ B) :
    (forget₂ (CommBialgCat.{v} R) (CommAlgCat.{v} R)).map f =
      CommAlgCat.ofHom f.hom.toAlgHom := rfl

/-- Forgetting to the underlying type and then building the bundled object returns the original
bialgebra. -/
@[simps]
/-
**CommBialgCat.ofIsoSelf** 是 Mathlib 中的一个定义，位于命名空间 `CommBialgCat`。
形式化陈述：ofIsoSelf (M : CommBialgCat.{v} R) : of R M ≅ M where hom
参数：M : CommBialgCat.{v} R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Forgetting to the underlying type and then building the bundled object returns t
he original
bialgebra.
-/
def ofIsoSelf (M : CommBialgCat.{v} R) : of R M ≅ M where
  hom := 𝟙 M
  inv := 𝟙 M

@[deprecated (since := "2026-06-09")] alias ofSelfIso := ofIsoSelf

/-- Build an isomorphism in the category `CommBialgCat R` from a `BialgEquiv` between
`Bialgebra`s. -/
@[simps]
/-
**CommBialgCat.isoMk** 是 Mathlib 中的一个定义，位于命名空间 `CommBialgCat`。
形式化陈述：isoMk {X Y : Type v} {_ : CommRing X} {_ : CommRing Y} {_ : Bialgebra R X}
 {_ : Bialgebra R Y} (e : X ≃ₐc[R] Y) : of R X ≅ of R Y where hom
参数：e : X ≃ₐc[R] Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Build an isomorphism in the category `CommBialgCat R` from a `BialgEquiv` betwee
n
`Bialgebra`s.
-/
def isoMk {X Y : Type v} {_ : CommRing X} {_ : CommRing Y} {_ : Bialgebra R X}
    {_ : Bialgebra R Y} (e : X ≃ₐc[R] Y) : of R X ≅ of R Y where
  hom := ofHom (e : X →ₐc[R] Y)
  inv := ofHom (e.symm : Y →ₐc[R] X)

/-- Build a `BialgEquiv` from an isomorphism in the category `CommBialgCat R`. -/
@[simps apply, simps -isSimp symm_apply]
/-
**CommBialgCat.bialgEquivOfIso** 是 Mathlib 中的一个定义，位于命名空间 `CommBialgCat`。
形式化陈述：bialgEquivOfIso (i : A ≅ B) : A ≃ₐc[R] B where __
参数：i : A ≅ B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Build a `BialgEquiv` from an isomorphism in the category `CommBialgCat R`.
-/
def bialgEquivOfIso (i : A ≅ B) : A ≃ₐc[R] B where
  __ := i.hom.hom
  toFun := i.hom
  invFun := i.inv
  left_inv x := by simp
  right_inv x := by simp

/-- Bialgebra equivalences between `Bialgebra`s are the same as isomorphisms in `CommBialgCat`. -/
@[simps]
/-
**CommBialgCat.isoEquivBialgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CommBialgCat`。
形式化陈述：isoEquivBialgEquiv : (of R X ≅ of R Y) ≃ (X ≃ₐc[R] Y) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bialgebra equivalences between `Bialgebra`s are the same as isomorphisms in `Com
mBialgCat`.
-/
def isoEquivBialgEquiv : (of R X ≅ of R Y) ≃ (X ≃ₐc[R] Y) where
  toFun := bialgEquivOfIso
  invFun := isoMk
  left_inv _ := rfl
  right_inv _ := rfl
/-
**CommBialgCat.reflectsIsomorphisms_forget** 是 Mathlib 中的一个实例，位于命名空间 `CommBialgC
at`。
形式化陈述：reflectsIsomorphisms_forget : (forget (CommBialgCat.{u} R)).ReflectsIsomor
phisms where reflects {X Y} f _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
· 使用定理 `BialgHom.map_mul'`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} [inst 
: CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : Semir
ing B] …
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
instance reflectsIsomorphisms_forget : (forget (CommBialgCat.{u} R)).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget (CommBialgCat.{u} R)).map f)
    let e : X ≃ₐc[R] Y := { f.hom, i.toEquiv with }
    exact (isoMk e).isIso_hom

end CommBialgCat

attribute [local ext] Quiver.Hom.unop_inj

/-
**CommAlgCat.monObjOpOf** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：CommAlgCat.monObjOpOf {A : Type u} [CommRing A] [Bialgebra R A] : MonObj (
op <| CommAlgCat.of R A) where one
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance CommAlgCat.monObjOpOf {A : Type u} [CommRing A] [Bialgebra R A] :
    MonObj (op <| CommAlgCat.of R A) where
  one := (CommAlgCat.ofHom <| counitAlgHom R A).op
  mul := (CommAlgCat.ofHom <| comulAlgHom R A).op
  one_mul := by ext; exact Coalgebra.rTensor_counit_comul _
  mul_one := by ext; exact Coalgebra.lTensor_counit_comul _
  mul_assoc := by ext; exact (Coalgebra.coassoc_symm_apply _).symm

@[simp]
/-
**CommAlgCat.one_op_of_unop_hom** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CommAlgCat.one_op_of_unop_hom {A : Type u} [CommRing A] [Bialgebra R A] : 
η[op <| CommAlgCat.of R A].unop.hom = counitAlgHom R A
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma CommAlgCat.one_op_of_unop_hom {A : Type u} [CommRing A] [Bialgebra R A] :
    η[op <| CommAlgCat.of R A].unop.hom = counitAlgHom R A := rfl

@[simp]
/-
**CommAlgCat.mul_op_of_unop_hom** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CommAlgCat.mul_op_of_unop_hom {A : Type u} [CommRing A] [Bialgebra R A] : 
μ[op <| CommAlgCat.of R A].unop.hom = comulAlgHom R A
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma CommAlgCat.mul_op_of_unop_hom {A : Type u} [CommRing A] [Bialgebra R A] :
    μ[op <| CommAlgCat.of R A].unop.hom = comulAlgHom R A := rfl
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {A : Type u} [CommRing A] [Bialgebra R A] [IsCocomm R A] :
    IsCommMonObj (Opposite.op <| CommAlgCat.of R A) where
  mul_comm := by ext; exact comm_comul R _
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {A B : Type u} [CommRing A] [Bialgebra R A] [CommRing B] [Bialgebra R B]
    (f : A →ₐc[R] B) : IsMonHom (CommAlgCat.ofHom f.toAlgHom).op where
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (A : (CommAlgCat R)ᵒᵖ) [MonObj A] : Bialgebra R A.unop :=
  .ofAlgHom μ[A].unop.hom η[A].unop.hom
    congr(($((MonObj.mul_assoc_flip A).symm)).unop.hom)
    congr(($(MonObj.one_mul A)).unop.hom)
    congr(($(MonObj.mul_one A)).unop.hom)

variable (R) in
/-- Commutative bialgebras over a commutative ring `R` are the same thing as comonoid
`R`-algebras. -/
@[simps! functor_obj_unop_X inverse_obj unitIso_hom_app
  unitIso_inv_app counitIso_hom_app counitIso_inv_app]
/-
**commBialgCatEquivComonCommAlgCat** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：commBialgCatEquivComonCommAlgCat : CommBialgCat R ≌ (Mon (CommAlgCat R)ᵒᵖ)
ᵒᵖ where functor.obj A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def commBialgCatEquivComonCommAlgCat : CommBialgCat R ≌ (Mon (CommAlgCat R)ᵒᵖ)ᵒᵖ where
  functor.obj A := .op <| .mk <| .op <| .of R A
  functor.map {A B} f := .op <| .mk' <| .op <| CommAlgCat.ofHom <| f.hom.toAlgHom
  inverse.obj A := .of R A.unop.X.unop
  inverse.map {A B} f := CommBialgCat.ofHom <| .ofAlgHom f.unop.hom.unop.hom
    congr(($(IsMonHom.one_hom (f := f.unop.hom))).unop.hom)
    congr(($((IsMonHom.mul_hom (f := f.unop.hom)).symm)).unop.hom)
  unitIso.hom := 𝟙 _
  unitIso.inv := 𝟙 _
  counitIso.hom := 𝟙 _
  counitIso.inv := 𝟙 _

@[simp]
/-
**commBialgCatEquivComonCommAlgCat_functor_map_unop_hom** 是 Mathlib 中的一个引理，位于命名空
间 ``。
形式化陈述：commBialgCatEquivComonCommAlgCat_functor_map_unop_hom {A B : CommBialgCat 
R} (f : A ⟶ B) : ((commBialgCatEquivComonCommAlgCat R).functor.map f).unop.hom =
 (CommAlgCat.ofHom f.hom.toAlgHom).op
参数：f : A ⟶ B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma commBialgCatEquivComonCommAlgCat_functor_map_unop_hom {A B : CommBialgCat R} (f : A ⟶ B) :
  ((commBialgCatEquivComonCommAlgCat R).functor.map f).unop.hom =
    (CommAlgCat.ofHom f.hom.toAlgHom).op := rfl

@[simp]
/-
**commBialgCatEquivComonCommAlgCat_inverse_map_unop_hom** 是 Mathlib 中的一个引理，位于命名空
间 ``。
形式化陈述：commBialgCatEquivComonCommAlgCat_inverse_map_unop_hom {A B : (Mon (CommAlg
Cat R)ᵒᵖ)ᵒᵖ} (f : A ⟶ B) : ((commBialgCatEquivComonCommAlgCat R).inverse.map f).
hom.toAlgHom = f.unop.hom.unop.hom
参数：Mon (CommAlgCat R)ᵒᵖ；f : A ⟶ B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma commBialgCatEquivComonCommAlgCat_inverse_map_unop_hom
    {A B : (Mon (CommAlgCat R)ᵒᵖ)ᵒᵖ} (f : A ⟶ B) :
  ((commBialgCatEquivComonCommAlgCat R).inverse.map f).hom.toAlgHom =
    f.unop.hom.unop.hom := rfl
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {A : CommBialgCat.{u} R} [IsCocomm R A] :
    IsCommMonObj ((commBialgCatEquivComonCommAlgCat R).functor.obj A).unop.X :=
  inferInstanceAs <| IsCommMonObj <| op <| CommAlgCat.of R A
