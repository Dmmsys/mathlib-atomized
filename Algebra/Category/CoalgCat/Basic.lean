/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.RingTheory.Coalgebra.Equiv

/-!
# The category of coalgebras over a commutative ring

We introduce the bundled category `CoalgCat` of coalgebras over a fixed commutative ring `R`
along with the forgetful functor to `ModuleCat`.

This file mimics `Mathlib/LinearAlgebra/QuadraticForm/QuadraticModuleCat.lean`.

-/

@[expose] public section

open CategoryTheory

universe v u

variable (R : Type u) [CommRing R]

/-- The category of `R`-coalgebras. -/
/-
**CoalgCat** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u) → [CommRing R] → Type (max u (v + 1))
参数：v + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of `R`-coalgebras.
-/
structure CoalgCat extends ModuleCat.{v} R where
  instCoalgebra : Coalgebra R carrier

attribute [instance] CoalgCat.instCoalgebra

variable {R}

namespace CoalgCat

open Coalgebra

/-
**CoalgCat.** 是 Mathlib 中的一个实例，位于命名空间 `CoalgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort (CoalgCat.{v} R) (Type v) :=
  ⟨(·.carrier)⟩
/-
**CoalgCat.moduleCat_of_toModuleCat** 是 Mathlib 中的一个定理，位于命名空间 `CoalgCat`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] (X : CoalgCat R), ModuleCat.of R ↑X.toM
oduleCat = X.toModuleCat
参数：X : CoalgCat R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem moduleCat_of_toModuleCat (X : CoalgCat.{v} R) :
    ModuleCat.of R X.toModuleCat = X.toModuleCat :=
  rfl

variable (R) in
/-- The object in the category of `R`-coalgebras associated to an `R`-coalgebra. -/
/-
**CoalgCat.of** 是 Mathlib 中的一个缩写定义，位于命名空间 `CoalgCat`。
形式化陈述：of (X : Type v) [AddCommGroup X] [Module R X] [Coalgebra R X] : CoalgCat R
参数：X : Type v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The object in the category of `R`-coalgebras associated to an `R`-coalgebra.
-/
abbrev of (X : Type v) [AddCommGroup X] [Module R X] [Coalgebra R X] :
    CoalgCat R :=
  { ModuleCat.of R X with
    instCoalgebra := (inferInstance : Coalgebra R X) }

@[simp]
/-
**CoalgCat.of_comul** 是 Mathlib 中的一个引理，位于命名空间 `CoalgCat`。
形式化陈述：of_comul {X : Type v} [AddCommGroup X] [Module R X] [Coalgebra R X] : Coal
gebra.comul (A
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma of_comul {X : Type v} [AddCommGroup X] [Module R X] [Coalgebra R X] :
    Coalgebra.comul (A := of R X) = Coalgebra.comul (R := R) (A := X) := rfl

@[simp]
/-
**CoalgCat.of_counit** 是 Mathlib 中的一个引理，位于命名空间 `CoalgCat`。
形式化陈述：of_counit {X : Type v} [AddCommGroup X] [Module R X] [Coalgebra R X] : Coa
lgebra.counit (A
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma of_counit {X : Type v} [AddCommGroup X] [Module R X] [Coalgebra R X] :
    Coalgebra.counit (A := of R X) = Coalgebra.counit (R := R) (A := X) := rfl

/-- A type alias for `CoalgHom` to avoid confusion between the categorical and
algebraic spellings of composition. -/
@[ext]
/-
**CoalgCat.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `CoalgCat`。
形式化陈述：{R : Type u} → [inst : CommRing R] → CoalgCat R → CoalgCat R → Type v
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type alias for `CoalgHom` to avoid confusion between the categorical and
algebraic spellings of composition.
-/
structure Hom (V W : CoalgCat.{v} R) where
  /-- The underlying `CoalgHom` -/
  toCoalgHom' : V →ₗc[R] W
/-
**CoalgCat.category** 是 Mathlib 中的一个实例，位于命名空间 `CoalgCat`。
形式化陈述：category : Category (CoalgCat.{v} R) where Hom M N
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance category : Category (CoalgCat.{v} R) where
  Hom M N := Hom M N
  id M := ⟨CoalgHom.id R M⟩
  comp f g := ⟨CoalgHom.comp g.toCoalgHom' f.toCoalgHom'⟩
/-
**CoalgCat.concreteCategory** 是 Mathlib 中的一个实例，位于命名空间 `CoalgCat`。
形式化陈述：concreteCategory : ConcreteCategory (CoalgCat.{v} R) (· ->ₗc[R] ·) where h
om f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance concreteCategory : ConcreteCategory (CoalgCat.{v} R) (· →ₗc[R] ·) where
  hom f := f.toCoalgHom'
  ofHom f := ⟨f⟩

/-- Turn a morphism in `CoalgCat` back into a `CoalgHom`. -/
/-
**CoalgCat.Hom.toCoalgHom** 是 Mathlib 中的一个定义，位于命名空间 `CoalgCat.Hom`。
形式化陈述：{R : Type u} → [inst : CommRing R] → {X Y : CoalgCat R} → X.Hom Y → ↑X.toM
oduleCat →ₗc[R] ↑Y.toModuleCat
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a morphism in `CoalgCat` back into a `CoalgHom`.
-/
abbrev Hom.toCoalgHom {X Y : CoalgCat.{v} R} (f : Hom X Y) : X →ₗc[R] Y :=
  ConcreteCategory.hom (C := CoalgCat.{v} R) f

/-- Typecheck a `CoalgHom` as a morphism in `CoalgCat R`. -/
/-
**CoalgCat.ofHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `CoalgCat`。
形式化陈述：ofHom {X Y : Type v} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Modul
e R Y] [Coalgebra R X] [Coalgebra R Y] (f : X ->ₗc[R] Y) : of R X ⟶ of R Y
参数：f : X ->ₗc[R] Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typecheck a `CoalgHom` as a morphism in `CoalgCat R`.
-/
abbrev ofHom {X Y : Type v} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    [Coalgebra R X] [Coalgebra R Y] (f : X →ₗc[R] Y) :
    of R X ⟶ of R Y :=
  ConcreteCategory.ofHom f
/-
**CoalgCat.Hom.toCoalgHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `CoalgCat.Hom`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] (V W : CoalgCat R), Function.Injective 
CoalgCat.Hom.toCoalgHom'
参数：V W : CoalgCat R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Hom.toCoalgHom_injective (V W : CoalgCat.{v} R) :
    Function.Injective (Hom.toCoalgHom' : Hom V W → _) :=
  fun ⟨f⟩ ⟨g⟩ _ => by congr

@[ext]
/-
**CoalgCat.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `CoalgCat`。
形式化陈述：hom_ext {M N : CoalgCat.{v} R} (f g : M ⟶ N) (h : f.toCoalgHom = g.toCoalg
Hom) : f = g
参数：f g : M ⟶ N；h : f.toCoalgHom = g.toCoalgHom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CoalgCat.Hom.ext`：∀ {R : Type u} {inst : CommRing R} {V W : CoalgCat R} 
{x y : V.Hom W}, x.toCoalgHom' = y.toCoalgHom' → x = y
-/
lemma hom_ext {M N : CoalgCat.{v} R} (f g : M ⟶ N) (h : f.toCoalgHom = g.toCoalgHom) :
    f = g :=
  Hom.ext h
/-
**CoalgCat.toCoalgHom_comp** 是 Mathlib 中的一个定理，位于命名空间 `CoalgCat`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {M N U : CoalgCat R} (f : M ⟶ N) (g : N
 ⟶ U),   CoalgCat.Hom.toCoalgHom (CategoryTheory.CategoryStruct.comp f g) =     
(CoalgCat.Hom.toCoalgHom g).comp (CoalgCat.Hom.toCoalgHom f)
参数：f : M ⟶ N；g : N ⟶ U；CategoryTheory.CategoryStruct.comp f g；CoalgCat.Hom.toCoa
lgHom g；CoalgCat.Hom.toCoalgHom f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toCoalgHom_comp {M N U : CoalgCat.{v} R} (f : M ⟶ N) (g : N ⟶ U) :
    (f ≫ g).toCoalgHom = g.toCoalgHom.comp f.toCoalgHom :=
  rfl
/-
**CoalgCat.toCoalgHom_id** 是 Mathlib 中的一个定理，位于命名空间 `CoalgCat`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {M : CoalgCat R},   CoalgCat.Hom.toCoal
gHom (CategoryTheory.CategoryStruct.id M) = CoalgHom.id R ↑M.toModuleCat
参数：CategoryTheory.CategoryStruct.id M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toCoalgHom_id {M : CoalgCat.{v} R} :
    Hom.toCoalgHom (𝟙 M) = CoalgHom.id _ _ :=
  rfl
/-
**CoalgCat.hasForgetToModule** 是 Mathlib 中的一个实例，位于命名空间 `CoalgCat`。
形式化陈述：hasForgetToModule : HasForget₂ (CoalgCat R) (ModuleCat R) where forget₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToModule : HasForget₂ (CoalgCat R) (ModuleCat R) where
  forget₂ :=
    { obj := fun M => ModuleCat.of R M
      map := fun f => ModuleCat.ofHom f.toCoalgHom.toLinearMap }

@[simp]
/-
**CoalgCat.forget** 是 Mathlib 中的一个定理，位于命名空间 `CoalgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forget₂_obj (X : CoalgCat R) :
    (forget₂ (CoalgCat R) (ModuleCat R)).obj X = ModuleCat.of R X :=
  rfl

@[simp]
/-
**CoalgCat.forget** 是 Mathlib 中的一个定理，位于命名空间 `CoalgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forget₂_map (X Y : CoalgCat R) (f : X ⟶ Y) :
    (forget₂ (CoalgCat R) (ModuleCat R)).map f = ModuleCat.ofHom (f.toCoalgHom : X →ₗ[R] Y) :=
  rfl

end CoalgCat

namespace CoalgEquiv

open CoalgCat

variable {X Y Z : Type v}
variable [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y] [AddCommGroup Z] [Module R Z]
variable [Coalgebra R X] [Coalgebra R Y] [Coalgebra R Z]

/-- Build an isomorphism in the category `CoalgCat R` from a
`CoalgEquiv`. -/
@[simps]
/-
**CoalgEquiv.toCoalgIso** 是 Mathlib 中的一个定义，位于命名空间 `CoalgEquiv`。
形式化陈述：toCoalgIso (e : X ≃ₗc[R] Y) : CoalgCat.of R X ≅ CoalgCat.of R Y where hom
参数：e : X ≃ₗc[R] Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Build an isomorphism in the category `CoalgCat R` from a
`CoalgEquiv`.
-/
def toCoalgIso (e : X ≃ₗc[R] Y) : CoalgCat.of R X ≅ CoalgCat.of R Y where
  hom := CoalgCat.ofHom e
  inv := CoalgCat.ofHom e.symm
  hom_inv_id := Hom.ext <| DFunLike.ext _ _ e.left_inv
  inv_hom_id := Hom.ext <| DFunLike.ext _ _ e.right_inv
/-
**CoalgEquiv.toCoalgIso_refl** 是 Mathlib 中的一个定理，位于命名空间 `CoalgEquiv`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {X : Type v} [inst_1 : AddCommGroup X] 
[inst_2 : _root_.Module R X]   [inst_3 : Coalgebra R X], (CoalgEquiv.refl R X).t
oCoalgIso = CategoryTheory.Iso.refl (CoalgCat.of R X)
参数：CoalgEquiv.refl R X；CoalgCat.of R X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toCoalgIso_refl :
    toCoalgIso (CoalgEquiv.refl R X) = .refl _ :=
  rfl
/-
**CoalgEquiv.toCoalgIso_symm** 是 Mathlib 中的一个定理，位于命名空间 `CoalgEquiv`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {X Y : Type v} [inst_1 : AddCommGroup X
] [inst_2 : _root_.Module R X]   [inst_3 : AddCommGroup Y] [inst_4 : _root_.Modu
le R Y] [inst_5 : Coalgebra R X] [inst_6 : Coalgebra R Y]   (e : X ≃ₗc[R] Y), e.
symm.toCoalgIso = e.toCoalgIso.symm
参数：e : X ≃ₗc[R] Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toCoalgIso_symm (e : X ≃ₗc[R] Y) :
    toCoalgIso e.symm = (toCoalgIso e).symm :=
  rfl
/-
**CoalgEquiv.toCoalgIso_trans** 是 Mathlib 中的一个定理，位于命名空间 `CoalgEquiv`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {X Y Z : Type v} [inst_1 : AddCommGroup
 X] [inst_2 : _root_.Module R X]   [inst_3 : AddCommGroup Y] [inst_4 : _root_.Mo
dule R Y] [inst_5 : AddCommGroup Z] [inst_6 : _root_.Module R Z]   [inst_7 : Coa
lgebra R X] [inst_8 : Coalgebra R Y] [inst_9 : Coalgebra R Z] (e : X ≃ₗc[R] Y) (
f : Y ≃ₗc[R] Z),   (e.trans f).toCoalgIso = e.toCoalgIso ≪≫ f.toCoalgIso
参数：e : X ≃ₗc[R] Y；f : Y ≃ₗc[R] Z；e.trans f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toCoalgIso_trans (e : X ≃ₗc[R] Y) (f : Y ≃ₗc[R] Z) :
    toCoalgIso (e.trans f) = toCoalgIso e ≪≫ toCoalgIso f :=
  rfl

end CoalgEquiv

namespace CategoryTheory.Iso

open Coalgebra

variable {X Y Z : CoalgCat.{v} R}

/-- Build a `CoalgEquiv` from an isomorphism in the category
`CoalgCat R`. -/
/-
**CategoryTheory.Iso.toCoalgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Iso`
。
形式化陈述：toCoalgEquiv (i : X ≅ Y) : X ≃ₗc[R] Y
参数：i : X ≅ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Build a `CoalgEquiv` from an isomorphism in the category
`CoalgCat R`.
-/
def toCoalgEquiv (i : X ≅ Y) : X ≃ₗc[R] Y :=
  { i.hom.toCoalgHom with
    invFun := i.inv.toCoalgHom
    left_inv := fun x => CoalgHom.congr_fun (congr_arg CoalgCat.Hom.toCoalgHom i.3) x
    right_inv := fun x => CoalgHom.congr_fun (congr_arg CoalgCat.Hom.toCoalgHom i.4) x }
/-
**CategoryTheory.Iso.toCoalgEquiv_toCoalgHom** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Iso`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {X Y : CoalgCat R} (i : X ≅ Y), ↑i.toCo
algEquiv = CoalgCat.Hom.toCoalgHom i.hom
参数：i : X ≅ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CoalgEquivClass.toCoalgHomClass`：∀ {F : Type u_5} {R : outParam (Type u_
6)} {A : outParam (Type u_7)} {B : outParam (Type u_8)} {inst : CommSemiring R} 
  {inst_1 : AddCommMo…
· 使用定理 `CoalgEquiv.instCoalgEquivClass`：∀ {R : Type u_1} {A : Type u_2} {B : Typ
e u_3} [inst : CommSemiring R] [inst_1 : AddCommMonoid A]   [inst_2 : AddCommMon
oid B] [inst_3 : _ro…
-/
@[simp] theorem toCoalgEquiv_toCoalgHom (i : X ≅ Y) :
    i.toCoalgEquiv = i.hom.toCoalgHom := rfl
/-
**CategoryTheory.Iso.toCoalgEquiv_refl** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Iso`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {X : CoalgCat R},   (CategoryTheory.Iso
.refl X).toCoalgEquiv = CoalgEquiv.refl R ↑X.toModuleCat
参数：CategoryTheory.Iso.refl X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toCoalgEquiv_refl : toCoalgEquiv (.refl X) = .refl _ _ :=
  rfl
/-
**CategoryTheory.Iso.toCoalgEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Iso`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {X Y : CoalgCat R} (e : X ≅ Y), e.symm.
toCoalgEquiv = e.toCoalgEquiv.symm
参数：e : X ≅ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toCoalgEquiv_symm (e : X ≅ Y) :
    toCoalgEquiv e.symm = (toCoalgEquiv e).symm :=
  rfl
/-
**CategoryTheory.Iso.toCoalgEquiv_trans** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Iso`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {X Y Z : CoalgCat R} (e : X ≅ Y) (f : Y
 ≅ Z),   (e ≪≫ f).toCoalgEquiv = e.toCoalgEquiv.trans f.toCoalgEquiv
参数：e : X ≅ Y；f : Y ≅ Z；e ≪≫ f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toCoalgEquiv_trans (e : X ≅ Y) (f : Y ≅ Z) :
    toCoalgEquiv (e ≪≫ f) = e.toCoalgEquiv.trans f.toCoalgEquiv :=
  rfl

end CategoryTheory.Iso

/-
**CoalgCat.forget_reflects_isos** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：CoalgCat.forget_reflects_isos : (forget (CoalgCat.{v} R)).ReflectsIsomorph
isms where reflects {X Y} f _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
· 使用定理 `CategoryTheory.IsIso.out`：∀ {C : Type u} {inst : CategoryTheory.Category
.{v, u} C} {X Y : C} {f : X ⟶ Y} [self : CategoryTheory.IsIso f],   ∃ inv,     C
ategoryTheory.…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
instance CoalgCat.forget_reflects_isos :
    (forget (CoalgCat.{v} R)).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget (CoalgCat.{v} R)).map f)
    let e : X ≃ₗc[R] Y := { f.toCoalgHom, i.toEquiv with }
    exact ⟨e.toCoalgIso.isIso_hom.1⟩
