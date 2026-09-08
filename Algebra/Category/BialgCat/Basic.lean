/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.Algebra.Category.CoalgCat.Basic
public import Mathlib.Algebra.Category.AlgCat.Basic
public import Mathlib.RingTheory.Bialgebra.Equiv

/-!
# The category of bialgebras over a commutative ring

We introduce the bundled category `BialgCat` of bialgebras over a fixed commutative ring `R`
along with the forgetful functors to `CoalgCat` and `AlgCat`.

This file mimics `Mathlib/LinearAlgebra/QuadraticForm/QuadraticModuleCat.lean`.

-/

@[expose] public section

open CategoryTheory

universe v u

variable (R : Type u) [CommRing R]

/-- The category of `R`-bialgebras. -/
/-
**BialgCat** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u) → [CommRing R] → Type (max u (v + 1))
参数：v + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of `R`-bialgebras.
-/
structure BialgCat where
  /-- The underlying type. -/
  carrier : Type v
  [instRing : Ring carrier]
  [instBialgebra : Bialgebra R carrier]

initialize_simps_projections BialgCat (-instRing, -instBialgebra)
attribute [instance] BialgCat.instBialgebra BialgCat.instRing

variable {R}

namespace BialgCat

open Bialgebra

/-
**BialgCat.** 是 Mathlib 中的一个实例，位于命名空间 `BialgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort (BialgCat.{v} R) (Type v) :=
  ⟨(·.carrier)⟩

variable (R) in
/-- The object in the category of `R`-bialgebras associated to an `R`-bialgebra. -/
@[simps]
/-
**BialgCat.of** 是 Mathlib 中的一个定义，位于命名空间 `BialgCat`。
形式化陈述：of (X : Type v) [Ring X] [Bialgebra R X] : BialgCat R where carrier
参数：X : Type v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The object in the category of `R`-bialgebras associated to an `R`-bialgebra.
-/
def of (X : Type v) [Ring X] [Bialgebra R X] :
    BialgCat R where
  carrier := X

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**BialgCat.of_comul** 是 Mathlib 中的一个引理，位于命名空间 `BialgCat`。
形式化陈述：of_comul {X : Type v} [Ring X] [Bialgebra R X] : Coalgebra.comul (A
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma of_comul {X : Type v} [Ring X] [Bialgebra R X] :
    Coalgebra.comul (A := of R X) = Coalgebra.comul (R := R) (A := X) := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**BialgCat.of_counit** 是 Mathlib 中的一个引理，位于命名空间 `BialgCat`。
形式化陈述：of_counit {X : Type v} [Ring X] [Bialgebra R X] : Coalgebra.counit (A
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma of_counit {X : Type v} [Ring X] [Bialgebra R X] :
    Coalgebra.counit (A := of R X) = Coalgebra.counit (R := R) (A := X) := rfl

/-- A type alias for `BialgHom` to avoid confusion between the categorical and
algebraic spellings of composition. -/
@[ext]
/-
**BialgCat.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `BialgCat`。
形式化陈述：{R : Type u} → [inst : CommRing R] → BialgCat R → BialgCat R → Type v
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type alias for `BialgHom` to avoid confusion between the categorical and
algebraic spellings of composition.
-/
structure Hom (V W : BialgCat.{v} R) where
  /-- The underlying `BialgHom` -/
  toBialgHom' : V →ₐc[R] W
/-
**BialgCat.category** 是 Mathlib 中的一个实例，位于命名空间 `BialgCat`。
形式化陈述：category : Category (BialgCat.{v} R) where Hom X Y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance category : Category (BialgCat.{v} R) where
  Hom X Y := Hom X Y
  id X := ⟨BialgHom.id R X⟩
  comp f g := ⟨BialgHom.comp g.toBialgHom' f.toBialgHom'⟩
/-
**BialgCat.concreteCategory** 是 Mathlib 中的一个实例，位于命名空间 `BialgCat`。
形式化陈述：concreteCategory : ConcreteCategory (BialgCat.{v} R) (· ->ₐc[R] ·) where h
om f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance concreteCategory : ConcreteCategory (BialgCat.{v} R) (· →ₐc[R] ·) where
  hom f := f.toBialgHom'
  ofHom f := ⟨f⟩

/-- Turn a morphism in `BialgCat` back into a `BialgHom`. -/
/-
**BialgCat.Hom.toBialgHom** 是 Mathlib 中的一个定义，位于命名空间 `BialgCat.Hom`。
形式化陈述：{R : Type u} → [inst : CommRing R] → {X Y : BialgCat R} → X.Hom Y → X.carr
ier →ₐc[R] Y.carrier
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a morphism in `BialgCat` back into a `BialgHom`.
-/
abbrev Hom.toBialgHom {X Y : BialgCat R} (f : Hom X Y) :=
  ConcreteCategory.hom (C := BialgCat R) f

/-- Typecheck a `BialgHom` as a morphism in `BialgCat R`. -/
/-
**BialgCat.ofHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `BialgCat`。
形式化陈述：ofHom {X Y : Type v} [Ring X] [Ring Y] [Bialgebra R X] [Bialgebra R Y] (f 
: X ->ₐc[R] Y) : of R X ⟶ of R Y
参数：f : X ->ₐc[R] Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typecheck a `BialgHom` as a morphism in `BialgCat R`.
-/
abbrev ofHom {X Y : Type v} [Ring X] [Ring Y]
    [Bialgebra R X] [Bialgebra R Y] (f : X →ₐc[R] Y) :
    of R X ⟶ of R Y :=
  ConcreteCategory.ofHom f
/-
**BialgCat.Hom.toBialgHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `BialgCat.Hom`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] (V W : BialgCat R), Function.Injective 
BialgCat.Hom.toBialgHom
参数：V W : BialgCat R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Hom.toBialgHom_injective (V W : BialgCat.{v} R) :
    Function.Injective (Hom.toBialgHom : Hom V W → _) :=
  fun ⟨f⟩ ⟨g⟩ _ => by congr

-- TODO: if `Quiver.Hom` and the instance above were `reducible`, this wouldn't be needed.
@[ext]
/-
**BialgCat.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `BialgCat`。
形式化陈述：hom_ext {X Y : BialgCat.{v} R} (f g : X ⟶ Y) (h : f.toBialgHom = g.toBialg
Hom) : f = g
参数：f g : X ⟶ Y；h : f.toBialgHom = g.toBialgHom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BialgCat.Hom.ext`：∀ {R : Type u} {inst : CommRing R} {V W : BialgCat R} 
{x y : V.Hom W}, x.toBialgHom' = y.toBialgHom' → x = y
-/
lemma hom_ext {X Y : BialgCat.{v} R} (f g : X ⟶ Y) (h : f.toBialgHom = g.toBialgHom) :
    f = g :=
  Hom.ext h
/-
**BialgCat.toBialgHom_comp** 是 Mathlib 中的一个定理，位于命名空间 `BialgCat`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {X Y Z : BialgCat R} (f : X ⟶ Y) (g : Y
 ⟶ Z),   BialgCat.Hom.toBialgHom (CategoryTheory.CategoryStruct.comp f g) =     
(BialgCat.Hom.toBialgHom g).comp (BialgCat.Hom.toBialgHom f)
参数：f : X ⟶ Y；g : Y ⟶ Z；CategoryTheory.CategoryStruct.comp f g；BialgCat.Hom.toBia
lgHom g；BialgCat.Hom.toBialgHom f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toBialgHom_comp {X Y Z : BialgCat.{v} R} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).toBialgHom = g.toBialgHom.comp f.toBialgHom :=
  rfl
/-
**BialgCat.toBialgHom_id** 是 Mathlib 中的一个定理，位于命名空间 `BialgCat`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {M : BialgCat R},   BialgCat.Hom.toBial
gHom (CategoryTheory.CategoryStruct.id M) = BialgHom.id R M.carrier
参数：CategoryTheory.CategoryStruct.id M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toBialgHom_id {M : BialgCat.{v} R} :
    Hom.toBialgHom (𝟙 M) = BialgHom.id _ _ :=
  rfl
/-
**BialgCat.hasForgetToAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `BialgCat`。
形式化陈述：hasForgetToAlgebra : HasForget₂ (BialgCat R) (AlgCat R) where forget₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToAlgebra : HasForget₂ (BialgCat R) (AlgCat R) where
  forget₂ :=
    { obj := fun X => AlgCat.of R X
      map := fun {X Y} f => AlgCat.ofHom f.toBialgHom }

@[simp]
/-
**BialgCat.forget** 是 Mathlib 中的一个定理，位于命名空间 `BialgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forget₂_algebra_obj (X : BialgCat R) :
    (forget₂ (BialgCat R) (AlgCat R)).obj X = AlgCat.of R X :=
  rfl

@[simp]
/-
**BialgCat.forget** 是 Mathlib 中的一个定理，位于命名空间 `BialgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forget₂_algebra_map (X Y : BialgCat R) (f : X ⟶ Y) :
    (forget₂ (BialgCat R) (AlgCat R)).map f = AlgCat.ofHom f.toBialgHom :=
  rfl
/-
**BialgCat.hasForgetToCoalgebra** 是 Mathlib 中的一个实例，位于命名空间 `BialgCat`。
形式化陈述：hasForgetToCoalgebra : HasForget₂ (BialgCat R) (CoalgCat R) where forget₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToCoalgebra : HasForget₂ (BialgCat R) (CoalgCat R) where
  forget₂ :=
    { obj := fun X => CoalgCat.of R X
      map := fun {_ _} f => CoalgCat.ofHom f.toBialgHom }

@[simp]
/-
**BialgCat.forget** 是 Mathlib 中的一个定理，位于命名空间 `BialgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forget₂_coalgebra_obj (X : BialgCat R) :
    (forget₂ (BialgCat R) (CoalgCat R)).obj X = CoalgCat.of R X :=
  rfl

@[simp]
/-
**BialgCat.forget** 是 Mathlib 中的一个定理，位于命名空间 `BialgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forget₂_coalgebra_map (X Y : BialgCat R) (f : X ⟶ Y) :
    (forget₂ (BialgCat R) (CoalgCat R)).map f = CoalgCat.ofHom f.toBialgHom :=
  rfl

end BialgCat

namespace BialgEquiv

open BialgCat

variable {X Y Z : Type v}
variable [Ring X] [Ring Y] [Ring Z]
variable [Bialgebra R X] [Bialgebra R Y] [Bialgebra R Z]

/-- Build an isomorphism in the category `BialgCat R` from a
`BialgEquiv`. -/
@[simps]
/-
**BialgEquiv.toBialgIso** 是 Mathlib 中的一个定义，位于命名空间 `BialgEquiv`。
形式化陈述：toBialgIso (e : X ≃ₐc[R] Y) : BialgCat.of R X ≅ BialgCat.of R Y where hom
参数：e : X ≃ₐc[R] Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Build an isomorphism in the category `BialgCat R` from a
`BialgEquiv`.
-/
def toBialgIso (e : X ≃ₐc[R] Y) : BialgCat.of R X ≅ BialgCat.of R Y where
  hom := BialgCat.ofHom e
  inv := BialgCat.ofHom e.symm
  hom_inv_id := Hom.ext <| DFunLike.ext _ _ e.left_inv
  inv_hom_id := Hom.ext <| DFunLike.ext _ _ e.right_inv
/-
**BialgEquiv.toBialgIso_refl** 是 Mathlib 中的一个定理，位于命名空间 `BialgEquiv`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {X : Type v} [inst_1 : Ring X] [inst_2 
: Bialgebra R X],   (BialgEquiv.refl R X).toBialgIso = CategoryTheory.Iso.refl (
BialgCat.of R X)
参数：BialgEquiv.refl R X；BialgCat.of R X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toBialgIso_refl : toBialgIso (BialgEquiv.refl R X) = .refl _ :=
  rfl
/-
**BialgEquiv.toBialgIso_symm** 是 Mathlib 中的一个定理，位于命名空间 `BialgEquiv`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {X Y : Type v} [inst_1 : Ring X] [inst_
2 : Ring Y] [inst_3 : Bialgebra R X]   [inst_4 : Bialgebra R Y] (e : X ≃ₐc[R] Y)
, e.symm.toBialgIso = e.toBialgIso.symm
参数：e : X ≃ₐc[R] Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toBialgIso_symm (e : X ≃ₐc[R] Y) :
    toBialgIso e.symm = (toBialgIso e).symm :=
  rfl
/-
**BialgEquiv.toBialgIso_trans** 是 Mathlib 中的一个定理，位于命名空间 `BialgEquiv`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {X Y Z : Type v} [inst_1 : Ring X] [ins
t_2 : Ring Y] [inst_3 : Ring Z]   [inst_4 : Bialgebra R X] [inst_5 : Bialgebra R
 Y] [inst_6 : Bialgebra R Z] (e : X ≃ₐc[R] Y) (f : Y ≃ₐc[R] Z),   (e.trans f).to
BialgIso = e.toBialgIso ≪≫ f.toBialgIso
参数：e : X ≃ₐc[R] Y；f : Y ≃ₐc[R] Z；e.trans f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toBialgIso_trans (e : X ≃ₐc[R] Y) (f : Y ≃ₐc[R] Z) :
    toBialgIso (e.trans f) = toBialgIso e ≪≫ toBialgIso f :=
  rfl

end BialgEquiv

namespace CategoryTheory.Iso

open Bialgebra

variable {X Y Z : BialgCat.{v} R}

/-- Build a `BialgEquiv` from an isomorphism in the category
`BialgCat R`. -/
/-
**CategoryTheory.Iso.toBialgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Iso`
。
形式化陈述：toBialgEquiv (i : X ≅ Y) : X ≃ₐc[R] Y
参数：i : X ≅ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Build a `BialgEquiv` from an isomorphism in the category
`BialgCat R`.
-/
def toBialgEquiv (i : X ≅ Y) : X ≃ₐc[R] Y :=
  { i.hom.toBialgHom with
    invFun := i.inv.toBialgHom
    left_inv := fun x => BialgHom.congr_fun (congr_arg BialgCat.Hom.toBialgHom i.3) x
    right_inv := fun x => BialgHom.congr_fun (congr_arg BialgCat.Hom.toBialgHom i.4) x }
/-
**CategoryTheory.Iso.toBialgEquiv_toBialgHom** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Iso`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {X Y : BialgCat R} (i : X ≅ Y), ↑i.toBi
algEquiv = i.hom.toBialgHom'
参数：i : X ≅ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BialgEquivClass.toBialgHomClass`：∀ {F : Type u_1} {R : Type u_2} {A : Ty
pe u_3} {B : Type u_4} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 :
 Semiring B] [inst_3 …
· 使用定理 `BialgEquiv.instBialgEquivClass`：∀ {R : Type u} {A : Type v} {B : Type w}
 [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 :
 Algebra R A] [inst_…
-/
@[simp] theorem toBialgEquiv_toBialgHom (i : X ≅ Y) :
    (i.toBialgEquiv : X →ₐc[R] Y) = i.hom.1 := rfl
/-
**CategoryTheory.Iso.toBialgEquiv_refl** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Iso`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {X : BialgCat R},   (CategoryTheory.Iso
.refl X).toBialgEquiv = BialgEquiv.refl R X.carrier
参数：CategoryTheory.Iso.refl X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toBialgEquiv_refl : toBialgEquiv (.refl X) = .refl _ _ :=
  rfl
/-
**CategoryTheory.Iso.toBialgEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Iso`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {X Y : BialgCat R} (e : X ≅ Y), e.symm.
toBialgEquiv = e.toBialgEquiv.symm
参数：e : X ≅ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toBialgEquiv_symm (e : X ≅ Y) :
    toBialgEquiv e.symm = (toBialgEquiv e).symm :=
  rfl
/-
**CategoryTheory.Iso.toBialgEquiv_trans** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Iso`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {X Y Z : BialgCat R} (e : X ≅ Y) (f : Y
 ≅ Z),   (e ≪≫ f).toBialgEquiv = e.toBialgEquiv.trans f.toBialgEquiv
参数：e : X ≅ Y；f : Y ≅ Z；e ≪≫ f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toBialgEquiv_trans (e : X ≅ Y) (f : Y ≅ Z) :
    toBialgEquiv (e ≪≫ f) = e.toBialgEquiv.trans f.toBialgEquiv :=
  rfl

end CategoryTheory.Iso

/-
**BialgCat.forget_reflects_isos** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：BialgCat.forget_reflects_isos : (forget (BialgCat.{v} R)).ReflectsIsomorph
isms where reflects {X Y} f _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
· 使用定理 `BialgHom.map_mul'`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} [inst 
: CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : Semir
ing B] …
· 使用定理 `CategoryTheory.IsIso.out`：∀ {C : Type u} {inst : CategoryTheory.Category
.{v, u} C} {X Y : C} {f : X ⟶ Y} [self : CategoryTheory.IsIso f],   ∃ inv,     C
ategoryTheory.…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
instance BialgCat.forget_reflects_isos :
    (forget (BialgCat.{v} R)).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget (BialgCat.{v} R)).map f)
    let e : X ≃ₐc[R] Y := { f.toBialgHom, i.toEquiv with }
    exact ⟨e.toBialgIso.isIso_hom.1⟩
