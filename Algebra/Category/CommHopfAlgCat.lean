/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała
-/
module

public import Mathlib.Algebra.Category.CommBialgCat
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.RingTheory.HopfAlgebra.Convolution
public import Mathlib.RingTheory.HopfAlgebra.TensorProduct

/-!
# The category of commutative Hopf algebras over a commutative ring

This file defines the bundled category `CommHopfAlgCat` of commutative Hopf algebras over a fixed
commutative ring `R` along with the forgetful functor to `CommBialgCat`.
-/

public noncomputable section

open CategoryTheory Coalgebra HopfAlgebra Limits

universe v u
variable {R : Type u} [CommRing R]

/-- The category of commutative `R`-Hopf algebras and their morphisms. -/
/-
**CommHopfAlgCat** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u) → [CommRing R] → Type (max u (v + 1))
参数：v + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of commutative `R`-Hopf algebras and their morphisms.
-/
structure CommHopfAlgCat (R : Type u) [CommRing R] where
  /-- Turn an unbundled `R`-Hopf algebra into the corresponding object in the category of
  `R`-Hopf algebras. -/
  of (R) ::
  /-- The underlying type. -/
  protected X : Type v
  [commRing : CommRing X]
  [hopfAlgebra : HopfAlgebra R X]

namespace CommHopfAlgCat
variable {A B C : CommHopfAlgCat.{v} R} {X Y Z : Type v} [CommRing X] [HopfAlgebra R X]
  [CommRing Y] [HopfAlgebra R Y] [CommRing Z] [HopfAlgebra R Z]

attribute [instance] commRing hopfAlgebra

initialize_simps_projections CommHopfAlgCat (-commRing, -hopfAlgebra)

/-
**CommHopfAlgCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommHopfAlgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort (CommHopfAlgCat R) (Type v) := ⟨CommHopfAlgCat.X⟩

attribute [coe] CommHopfAlgCat.X

variable (R) in
/-
**CommHopfAlgCat.coe_of** 是 Mathlib 中的一个引理，位于命名空间 `CommHopfAlgCat`。
形式化陈述：coe_of (X : Type v) [CommRing X] [HopfAlgebra R X] : (of R X : Type v) = X
参数：X : Type v。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_of (X : Type v) [CommRing X] [HopfAlgebra R X] : (of R X : Type v) = X := rfl

/-- The type of morphisms in `CommHopfAlgCat R`. -/
@[ext]
/-
**CommHopfAlgCat.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `CommHopfAlgCat`。
形式化陈述：{R : Type u} → [inst : CommRing R] → CommHopfAlgCat R → CommHopfAlgCat R →
 Type v
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of morphisms in `CommHopfAlgCat R`.
-/
structure Hom (A B : CommHopfAlgCat.{v} R) where
  mk ::
  /-- The underlying bialgebra map. -/
  hom' : A →ₐc[R] B
/-
**CommHopfAlgCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommHopfAlgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (CommHopfAlgCat.{v} R) where
  Hom A B := Hom A B
  id A := ⟨.id R A⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩
/-
**CommHopfAlgCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommHopfAlgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ConcreteCategory (CommHopfAlgCat.{v} R) (· →ₐc[R] ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `CommHopfAlgCat` back into a `BialgHom`. -/
/-
**CommHopfAlgCat.Hom.hom** 是 Mathlib 中的一个定义，位于命名空间 `CommHopfAlgCat.Hom`。
形式化陈述：{R : Type u} → [inst : CommRing R] → {A B : CommHopfAlgCat R} → A.Hom B → 
↑A →ₐc[R] ↑B
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a morphism in `CommHopfAlgCat` back into a `BialgHom`.
-/
abbrev Hom.hom (f : Hom A B) := ConcreteCategory.hom (C := CommHopfAlgCat R) f

/-- Typecheck a `BialgHom` as a morphism in `CommHopfAlgCat R`. -/
/-
**CommHopfAlgCat.ofHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `CommHopfAlgCat`。
形式化陈述：ofHom {_ : CommRing X} {_ : CommRing Y} {_ : HopfAlgebra R X} {_ : HopfAlg
ebra R Y} (f : X ->ₐc[R] Y) : of R X ⟶ of R Y
参数：f : X ->ₐc[R] Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typecheck a `BialgHom` as a morphism in `CommHopfAlgCat R`.
-/
abbrev ofHom {_ : CommRing X} {_ : CommRing Y} {_ : HopfAlgebra R X} {_ : HopfAlgebra R Y}
    (f : X →ₐc[R] Y) : of R X ⟶ of R Y := ConcreteCategory.ofHom (C := CommHopfAlgCat R) f

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
/-
**CommHopfAlgCat.Hom.Simps.hom** 是 Mathlib 中的一个定义，位于命名空间 `CommHopfAlgCat.Hom.Sim
ps`。
形式化陈述：{R : Type u} → [inst : CommRing R] → (A B : CommHopfAlgCat R) → A.Hom B → 
↑A →ₐc[R] ↑B
参数：A B : CommHopfAlgCat R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas.
-/
def Hom.Simps.hom (A B : CommHopfAlgCat.{v} R) (f : Hom A B) := f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

/-
**CommHopfAlgCat.hom_id** 是 Mathlib 中的一个定理，位于命名空间 `CommHopfAlgCat`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {A : CommHopfAlgCat R},   ↑(CommHopfAlg
Cat.Hom.hom (CategoryTheory.CategoryStruct.id A)) = AlgHom.id R ↑A
参数：CommHopfAlgCat.Hom.hom (CategoryTheory.CategoryStruct.id A)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep 
them for `dsimp`.
-/
@[simp] lemma hom_id : (𝟙 A : A ⟶ A).hom = AlgHom.id R A := rfl

/- Provided for rewriting. -/
/-
**CommHopfAlgCat.id_apply** 是 Mathlib 中的一个引理，位于命名空间 `CommHopfAlgCat`。
形式化陈述：id_apply (A : CommHopfAlgCat.{v} R) (a : A) : (𝟙 A : A ⟶ A) a = a
参数：A : CommHopfAlgCat.{v} R；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Provided for rewriting.
-/
lemma id_apply (A : CommHopfAlgCat.{v} R) (a : A) : (𝟙 A : A ⟶ A) a = a := by simp
/-
**CommHopfAlgCat.hom_comp** 是 Mathlib 中的一个定理，位于命名空间 `CommHopfAlgCat`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {A B C : CommHopfAlgCat R} (f : A ⟶ B) 
(g : B ⟶ C),   CommHopfAlgCat.Hom.hom (CategoryTheory.CategoryStruct.comp f g) =
     (CommHopfAlgCat.Hom.hom g).comp (CommHopfAlgCat.Hom.hom f)
参数：f : A ⟶ B；g : B ⟶ C；CategoryTheory.CategoryStruct.comp f g；CommHopfAlgCat.Hom
.hom g；CommHopfAlgCat.Hom.hom f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma hom_comp (f : A ⟶ B) (g : B ⟶ C) : (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
/-
**CommHopfAlgCat.comp_apply** 是 Mathlib 中的一个引理，位于命名空间 `CommHopfAlgCat`。
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

--- 原说明 ---
Provided for rewriting.
-/
lemma comp_apply (f : A ⟶ B) (g : B ⟶ C) (a : A) : (f ≫ g) a = g (f a) := by simp
/-
**CommHopfAlgCat.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `CommHopfAlgCat`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {A B : CommHopfAlgCat R} {f g : A ⟶ B},
   CommHopfAlgCat.Hom.hom f = CommHopfAlgCat.Hom.hom g → f = g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CommHopfAlgCat.Hom.ext`：∀ {R : Type u} {inst : CommRing R} {A B : CommHo
pfAlgCat R} {x y : A.Hom B}, x.hom' = y.hom' → x = y
-/
@[ext] lemma hom_ext {f g : A ⟶ B} (hf : f.hom = g.hom) : f = g := Hom.ext hf
/-
**CommHopfAlgCat.hom_ofHom** 是 Mathlib 中的一个定理，位于命名空间 `CommHopfAlgCat`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {X Y : Type v} [inst_1 : CommRing X] [i
nst_2 : HopfAlgebra R X] [inst_3 : CommRing Y]   [inst_4 : HopfAlgebra R Y] (f :
 X →ₐc[R] Y), CommHopfAlgCat.Hom.hom (CommHopfAlgCat.ofHom f) = f
参数：f : X →ₐc[R] Y；CommHopfAlgCat.ofHom f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma hom_ofHom (f : X →ₐc[R] Y) : (ofHom f).hom = f := rfl
/-
**CommHopfAlgCat.ofHom_hom** 是 Mathlib 中的一个定理，位于命名空间 `CommHopfAlgCat`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {A B : CommHopfAlgCat R} (f : A ⟶ B),  
 CommHopfAlgCat.ofHom (CommHopfAlgCat.Hom.hom f) = f
参数：f : A ⟶ B；CommHopfAlgCat.Hom.hom f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofHom_hom (f : A ⟶ B) : ofHom f.hom = f := rfl
/-
**CommHopfAlgCat.ofHom_id** 是 Mathlib 中的一个定理，位于命名空间 `CommHopfAlgCat`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {X : Type v} [inst_1 : CommRing X] [ins
t_2 : HopfAlgebra R X],   CommHopfAlgCat.ofHom (BialgHom.id R X) =     CategoryT
heory.CategoryStruct.id { X := X, commRing := inst_1, hopfAlgebra := inst_2 }
参数：BialgHom.id R X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofHom_id : ofHom (.id R X) = 𝟙 (of R X) := rfl

@[simp]
/-
**CommHopfAlgCat.ofHom_comp** 是 Mathlib 中的一个引理，位于命名空间 `CommHopfAlgCat`。
形式化陈述：ofHom_comp (f : X ->ₐc[R] Y) (g : Y ->ₐc[R] Z) : ofHom (g.comp f) = ofHom 
f ≫ ofHom g
参数：f : X ->ₐc[R] Y；g : Y ->ₐc[R] Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_comp (f : X →ₐc[R] Y) (g : Y →ₐc[R] Z) : ofHom (g.comp f) = ofHom f ≫ ofHom g := rfl
/-
**CommHopfAlgCat.ofHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `CommHopfAlgCat`。
形式化陈述：ofHom_apply (f : X ->ₐc[R] Y) (x : X) : ofHom f x = f x
参数：f : X ->ₐc[R] Y；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_apply (f : X →ₐc[R] Y) (x : X) : ofHom f x = f x := rfl
/-
**CommHopfAlgCat.inv_hom_apply** 是 Mathlib 中的一个引理，位于命名空间 `CommHopfAlgCat`。
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
**CommHopfAlgCat.hom_inv_apply** 是 Mathlib 中的一个引理，位于命名空间 `CommHopfAlgCat`。
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
**CommHopfAlgCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommHopfAlgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (CommHopfAlgCat R) := ⟨of R R⟩
/-
**CommHopfAlgCat.forget_obj** 是 Mathlib 中的一个引理，位于命名空间 `CommHopfAlgCat`。
形式化陈述：forget_obj (A : CommHopfAlgCat.{v} R) : (forget (CommHopfAlgCat.{v} R)).ob
j A = A
参数：A : CommHopfAlgCat.{v} R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma forget_obj (A : CommHopfAlgCat.{v} R) : (forget (CommHopfAlgCat.{v} R)).obj A = A := rfl
/-
**CommHopfAlgCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommHopfAlgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CommRing ((forget (CommHopfAlgCat R)).obj A) := inferInstanceAs <| CommRing A
/-
**CommHopfAlgCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommHopfAlgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HopfAlgebra R ((forget (CommHopfAlgCat R)).obj A) := inferInstanceAs <| HopfAlgebra R A
/-
**CommHopfAlgCat.hasForgetToCommBialgCat** 是 Mathlib 中的一个实例，位于命名空间 `CommHopfAlgC
at`。
形式化陈述：hasForgetToCommBialgCat : HasForget₂ (CommHopfAlgCat.{v} R) (CommBialgCat.
{v} R) where forget₂.obj A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToCommBialgCat : HasForget₂ (CommHopfAlgCat.{v} R) (CommBialgCat.{v} R) where
  forget₂.obj A := .of R A
  forget₂.map f := CommBialgCat.ofHom f.hom
/-
**CommHopfAlgCat.forget** 是 Mathlib 中的一个引理，位于命名空间 `CommHopfAlgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma forget₂_commBialgCat_obj (A : CommHopfAlgCat.{v} R) :
    (forget₂ (CommHopfAlgCat.{v} R) (CommBialgCat.{v} R)).obj A = .of R A := rfl
/-
**CommHopfAlgCat.forget** 是 Mathlib 中的一个引理，位于命名空间 `CommHopfAlgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma forget₂_commBialgCat_map (f : A ⟶ B) :
    (forget₂ (CommHopfAlgCat.{v} R) (CommBialgCat.{v} R)).map f = CommBialgCat.ofHom f.hom := rfl

/-- Forgetting to the underlying type and then building the bundled object returns the original Hopf
algebra. -/
@[expose, simps]
/-
**CommHopfAlgCat.ofIsoSelf** 是 Mathlib 中的一个定义，位于命名空间 `CommHopfAlgCat`。
形式化陈述：ofIsoSelf (A : CommHopfAlgCat.{v} R) : of R A ≅ A where hom
参数：A : CommHopfAlgCat.{v} R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Forgetting to the underlying type and then building the bundled object returns t
he original Hopf
algebra.
-/
def ofIsoSelf (A : CommHopfAlgCat.{v} R) : of R A ≅ A where
  hom := 𝟙 A
  inv := 𝟙 A

/-- Build an isomorphism in the category `CommHopfAlgCat R` from a `BialgEquiv` between
`HopfAlgebra`s. -/
@[expose, simps]
/-
**CommHopfAlgCat.isoMk** 是 Mathlib 中的一个定义，位于命名空间 `CommHopfAlgCat`。
形式化陈述：isoMk {X Y : Type v} {_ : CommRing X} {_ : CommRing Y} {_ : HopfAlgebra R 
X} {_ : HopfAlgebra R Y} (e : X ≃ₐc[R] Y) : of R X ≅ of R Y where hom
参数：e : X ≃ₐc[R] Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Build an isomorphism in the category `CommHopfAlgCat R` from a `BialgEquiv` betw
een
`HopfAlgebra`s.
-/
def isoMk {X Y : Type v} {_ : CommRing X} {_ : CommRing Y} {_ : HopfAlgebra R X}
    {_ : HopfAlgebra R Y} (e : X ≃ₐc[R] Y) : of R X ≅ of R Y where
  hom := ofHom (e : X →ₐc[R] Y)
  inv := ofHom (e.symm : Y →ₐc[R] X)

/-- Build a `BialgEquiv` from an isomorphism in the category `CommHopfAlgCat R`. -/
-- TODO: Make `BialgEquiv.toCoalgEquiv` the simp normal form so that this can be simp
@[expose, simps -isSimp]
/-
**CommHopfAlgCat.ofIso** 是 Mathlib 中的一个定义，位于命名空间 `CommHopfAlgCat`。
形式化陈述：ofIso (i : A ≅ B) : A ≃ₐc[R] B where __
参数：i : A ≅ B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def ofIso (i : A ≅ B) : A ≃ₐc[R] B where
  __ := i.hom.hom
  toFun := i.hom
  invFun := i.inv
  left_inv x := by simp
  right_inv x := by simp

/-- Commutative Hopf algebra equivalences between `HopfAlgebra`s are the same as isomorphisms in
`CommHopfAlgCat R`. -/
@[expose, simps]
/-
**CommHopfAlgCat.isoEquivBialgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CommHopfAlgCat`。
形式化陈述：isoEquivBialgEquiv : (of R X ≅ of R Y) ≃ (X ≃ₐc[R] Y) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Commutative Hopf algebra equivalences between `HopfAlgebra`s are the same as iso
morphisms in
`CommHopfAlgCat R`.
-/
def isoEquivBialgEquiv : (of R X ≅ of R Y) ≃ (X ≃ₐc[R] Y) where
  toFun := ofIso
  invFun := isoMk
  left_inv _ := rfl
  right_inv _ := rfl
/-
**CommHopfAlgCat.reflectsIsomorphisms_forget** 是 Mathlib 中的一个实例，位于命名空间 `CommHopf
AlgCat`。
形式化陈述：reflectsIsomorphisms_forget : (forget (CommHopfAlgCat.{u} R)).ReflectsIsom
orphisms where reflects {X Y} f _
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
instance reflectsIsomorphisms_forget : (forget (CommHopfAlgCat.{u} R)).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget (CommHopfAlgCat.{u} R)).map f)
    let e : X ≃ₐc[R] Y := { f.hom, i.toEquiv with }
    exact (isoMk e).isIso_hom

end CommHopfAlgCat

attribute [local ext] Quiver.Hom.unop_inj

/-
**CommAlgCat.grpObjOpOf** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：CommAlgCat.grpObjOpOf {A : Type u} [CommRing A] [HopfAlgebra R A] : GrpObj
 (Opposite.op <| CommAlgCat.of R A) where inv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance CommAlgCat.grpObjOpOf {A : Type u} [CommRing A] [HopfAlgebra R A] :
    GrpObj (Opposite.op <| CommAlgCat.of R A) where
  inv := (CommAlgCat.ofHom <| antipodeAlgHom R A).op
  left_inv := by
    ext x
    -- TODO: Add more simp lemmas to make this `simpa ... using ...` again.
    simp only [unop_comp, unop_tensorObj, hom_comp, coe_tensorObj, lift_unop_hom,
      Quiver.Hom.unop_op, ConcreteCategory.hom_ofHom, unop_id, hom_id,
      ← Algebra.TensorProduct.lmul'_comp_map, mul_op_of_unop_hom, AlgHom.coe_comp,
      Function.comp_apply, Bialgebra.comulAlgHom_apply, unop_tensorUnit, coe_tensorUnit,
      toUnit_unop_hom, one_op_of_unop_hom, Bialgebra.counitAlgHom_apply, Algebra.ofId_apply]
    exact mul_antipode_rTensor_comul_apply (R := R) x
  right_inv := by
    ext x
    -- TODO: Add more simp lemmas to make this `simpa ... using ...` again.
    simp only [unop_comp, unop_tensorObj, hom_comp, coe_tensorObj, lift_unop_hom, unop_id, hom_id,
      Quiver.Hom.unop_op, ConcreteCategory.hom_ofHom, ← Algebra.TensorProduct.lmul'_comp_map,
      mul_op_of_unop_hom, AlgHom.coe_comp, Function.comp_apply, Bialgebra.comulAlgHom_apply,
      unop_tensorUnit, coe_tensorUnit, toUnit_unop_hom, one_op_of_unop_hom,
      Bialgebra.counitAlgHom_apply, Algebra.ofId_apply]
    exact mul_antipode_lTensor_comul_apply (R := R) x

open Opposite MonObj

@[simp]
/-
**CommAlgCat.inv_op_of_unop_hom** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CommAlgCat.inv_op_of_unop_hom {A : Type u} [CommRing A] [HopfAlgebra R A] 
: ι[op <| CommAlgCat.of R A].unop.hom = antipodeAlgHom R A
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma CommAlgCat.inv_op_of_unop_hom {A : Type u} [CommRing A] [HopfAlgebra R A] :
    ι[op <| CommAlgCat.of R A].unop.hom = antipodeAlgHom R A := rfl
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (A : (CommAlgCat R)ᵒᵖ) [GrpObj A] : HopfAlgebra R A.unop :=
  .ofAlgHom ι[A].unop.hom
    congr($(GrpObj.left_inv (X := A)).unop.hom)
    congr($(GrpObj.right_inv (X := A)).unop.hom)

variable (R) in
/-- Commutative Hopf algebras over a commutative ring `R` are the same thing as cogroup
`R`-algebras. -/
@[expose, simps! functor_obj_unop_X inverse_obj unitIso_hom_app unitIso_inv_app counitIso_hom_app
  counitIso_inv_app]
/-
**commHopfAlgCatEquivCogrpCommAlgCat** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：commHopfAlgCatEquivCogrpCommAlgCat : CommHopfAlgCat R ≌ (Grp (CommAlgCat R
)ᵒᵖ)ᵒᵖ where functor.obj A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def commHopfAlgCatEquivCogrpCommAlgCat : CommHopfAlgCat R ≌ (Grp (CommAlgCat R)ᵒᵖ)ᵒᵖ where
  functor.obj A := op <| .mk <| op <| .of R A
  functor.map {A B} f := op <| .mk <| .mk' <| op <| CommAlgCat.ofHom f.hom
  inverse.obj A := .of R A.unop.X.unop
  inverse.map {A B} f := CommHopfAlgCat.ofHom <| .ofAlgHom f.unop.hom.hom.unop.hom
    congr(($(IsMonHom.one_hom (f := f.unop.hom.hom))).unop.hom)
    congr(($((IsMonHom.mul_hom (f := f.unop.hom.hom)).symm)).unop.hom)
  unitIso.hom := 𝟙 _
  unitIso.inv := 𝟙 _
  counitIso.hom := 𝟙 _
  counitIso.inv := 𝟙 _
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {A : CommHopfAlgCat.{u} R} [IsCocomm R A] :
    IsCommMonObj ((commHopfAlgCatEquivCogrpCommAlgCat R).functor.obj A).unop.X :=
  inferInstanceAs <| IsCommMonObj <| op <| CommAlgCat.of R A
