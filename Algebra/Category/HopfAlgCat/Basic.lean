/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.Algebra.Category.BialgCat.Basic
public import Mathlib.RingTheory.HopfAlgebra.Basic

/-!
# The category of Hopf algebras over a commutative ring

We introduce the bundled category `HopfAlgCat` of Hopf algebras over a fixed commutative ring
`R` along with the forgetful functor to `BialgCat`.

This file mimics `Mathlib/LinearAlgebra/QuadraticForm/QuadraticModuleCat.lean`.

-/

@[expose] public section

open CategoryTheory

universe v u

variable (R : Type u) [CommRing R]

set_option backward.privateInPublic true in
/-- The category of `R`-Hopf algebras. -/
/-
**HopfAlgCat** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u) → [CommRing R] → Type (max u (v + 1))
参数：v + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of `R`-Hopf algebras.
-/
structure HopfAlgCat where
  private mk ::
  /-- The underlying type. -/
  carrier : Type v
  [instRing : Ring carrier]
  [instHopfAlgebra : HopfAlgebra R carrier]

initialize_simps_projections HopfAlgCat (-instRing, -instHopfAlgebra)
attribute [instance] HopfAlgCat.instHopfAlgebra HopfAlgCat.instRing

variable {R}

namespace HopfAlgCat

open HopfAlgebra

/-
**HopfAlgCat.** 是 Mathlib 中的一个实例，位于命名空间 `HopfAlgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort (HopfAlgCat.{v} R) (Type v) :=
  ⟨(·.carrier)⟩

variable (R) in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The object in the category of `R`-Hopf algebras associated to an `R`-Hopf algebra. -/
/-
**HopfAlgCat.of** 是 Mathlib 中的一个缩写定义，位于命名空间 `HopfAlgCat`。
形式化陈述：of (X : Type v) [Ring X] [HopfAlgebra R X] : HopfAlgCat R where carrier
参数：X : Type v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The object in the category of `R`-Hopf algebras associated to an `R`-Hopf algebr
a.
-/
abbrev of (X : Type v) [Ring X] [HopfAlgebra R X] :
    HopfAlgCat R where
  carrier := X

@[simp]
/-
**HopfAlgCat.of_comul** 是 Mathlib 中的一个引理，位于命名空间 `HopfAlgCat`。
形式化陈述：of_comul {X : Type v} [Ring X] [HopfAlgebra R X] : Coalgebra.comul (A
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma of_comul {X : Type v} [Ring X] [HopfAlgebra R X] :
    Coalgebra.comul (A := of R X) = Coalgebra.comul (R := R) (A := X) := rfl

@[simp]
/-
**HopfAlgCat.of_counit** 是 Mathlib 中的一个引理，位于命名空间 `HopfAlgCat`。
形式化陈述：of_counit {X : Type v} [Ring X] [HopfAlgebra R X] : Coalgebra.counit (A
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma of_counit {X : Type v} [Ring X] [HopfAlgebra R X] :
    Coalgebra.counit (A := of R X) = Coalgebra.counit (R := R) (A := X) := rfl

/-- A type alias for `BialgHom` to avoid confusion between the categorical and
algebraic spellings of composition. -/
@[ext]
/-
**HopfAlgCat.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `HopfAlgCat`。
形式化陈述：{R : Type u} → [inst : CommRing R] → HopfAlgCat R → HopfAlgCat R → Type v
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type alias for `BialgHom` to avoid confusion between the categorical and
algebraic spellings of composition.
-/
structure Hom (V W : HopfAlgCat.{v} R) where
  /-- The underlying `BialgHom`. -/
  toBialgHom' : V →ₐc[R] W
/-
**HopfAlgCat.category** 是 Mathlib 中的一个实例，位于命名空间 `HopfAlgCat`。
形式化陈述：category : Category (HopfAlgCat.{v} R) where Hom X Y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance category : Category (HopfAlgCat.{v} R) where
  Hom X Y := Hom X Y
  id X := ⟨BialgHom.id R X⟩
  comp f g := ⟨BialgHom.comp g.toBialgHom' f.toBialgHom'⟩
/-
**HopfAlgCat.concreteCategory** 是 Mathlib 中的一个实例，位于命名空间 `HopfAlgCat`。
形式化陈述：concreteCategory : ConcreteCategory (HopfAlgCat.{v} R) (· ->ₐc[R] ·) where
 hom f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance concreteCategory : ConcreteCategory (HopfAlgCat.{v} R) (· →ₐc[R] ·) where
  hom f := f.toBialgHom'
  ofHom f := ⟨f⟩

/-- Turn a morphism in `HopfAlgCat` back into a `BialgHom`. -/
/-
**HopfAlgCat.Hom.toBialgHom** 是 Mathlib 中的一个定义，位于命名空间 `HopfAlgCat.Hom`。
形式化陈述：{R : Type u} → [inst : CommRing R] → {X Y : HopfAlgCat R} → X.Hom Y → X.ca
rrier →ₐc[R] Y.carrier
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a morphism in `HopfAlgCat` back into a `BialgHom`.
-/
abbrev Hom.toBialgHom {X Y : HopfAlgCat R} (f : Hom X Y) :=
  ConcreteCategory.hom (C := HopfAlgCat R) f

/-- Typecheck a `BialgHom` as a morphism in `HopfAlgCat R`. -/
/-
**HopfAlgCat.ofHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `HopfAlgCat`。
形式化陈述：ofHom {X Y : Type v} [Ring X] [Ring Y] [HopfAlgebra R X] [HopfAlgebra R Y]
 (f : X ->ₐc[R] Y) : of R X ⟶ of R Y
参数：f : X ->ₐc[R] Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typecheck a `BialgHom` as a morphism in `HopfAlgCat R`.
-/
abbrev ofHom {X Y : Type v} [Ring X] [Ring Y]
    [HopfAlgebra R X] [HopfAlgebra R Y] (f : X →ₐc[R] Y) :
    of R X ⟶ of R Y :=
  ConcreteCategory.ofHom f
/-
**HopfAlgCat.Hom.toBialgHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `HopfAlgCat.Hom`
。
形式化陈述：∀ {R : Type u} [inst : CommRing R] (V W : HopfAlgCat R), Function.Injectiv
e HopfAlgCat.Hom.toBialgHom
参数：V W : HopfAlgCat R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Hom.toBialgHom_injective (V W : HopfAlgCat.{v} R) :
    Function.Injective (Hom.toBialgHom : Hom V W → _) :=
  fun ⟨f⟩ ⟨g⟩ _ => by congr

@[ext]
/-
**HopfAlgCat.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `HopfAlgCat`。
形式化陈述：hom_ext {X Y : HopfAlgCat.{v} R} (f g : X ⟶ Y) (h : f.toBialgHom = g.toBia
lgHom) : f = g
参数：f g : X ⟶ Y；h : f.toBialgHom = g.toBialgHom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HopfAlgCat.Hom.ext`：∀ {R : Type u} {inst : CommRing R} {V W : HopfAlgCat
 R} {x y : V.Hom W}, x.toBialgHom' = y.toBialgHom' → x = y
-/
lemma hom_ext {X Y : HopfAlgCat.{v} R} (f g : X ⟶ Y) (h : f.toBialgHom = g.toBialgHom) :
    f = g :=
  Hom.ext h
/-
**HopfAlgCat.toBialgHom_comp** 是 Mathlib 中的一个定理，位于命名空间 `HopfAlgCat`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {X Y Z : HopfAlgCat R} (f : X ⟶ Y) (g :
 Y ⟶ Z),   HopfAlgCat.Hom.toBialgHom (CategoryTheory.CategoryStruct.comp f g) = 
    (HopfAlgCat.Hom.toBialgHom g).comp (HopfAlgCat.Hom.toBialgHom f)
参数：f : X ⟶ Y；g : Y ⟶ Z；CategoryTheory.CategoryStruct.comp f g；HopfAlgCat.Hom.toB
ialgHom g；HopfAlgCat.Hom.toBialgHom f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toBialgHom_comp {X Y Z : HopfAlgCat.{v} R} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).toBialgHom = g.toBialgHom.comp f.toBialgHom :=
  rfl
/-
**HopfAlgCat.toBialgHom_id** 是 Mathlib 中的一个定理，位于命名空间 `HopfAlgCat`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {M : HopfAlgCat R},   HopfAlgCat.Hom.to
BialgHom (CategoryTheory.CategoryStruct.id M) = BialgHom.id R M.carrier
参数：CategoryTheory.CategoryStruct.id M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toBialgHom_id {M : HopfAlgCat.{v} R} :
    Hom.toBialgHom (𝟙 M) = BialgHom.id _ _ :=
  rfl
/-
**HopfAlgCat.hasForgetToBialgebra** 是 Mathlib 中的一个实例，位于命名空间 `HopfAlgCat`。
形式化陈述：hasForgetToBialgebra : HasForget₂ (HopfAlgCat R) (BialgCat R) where forget
₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToBialgebra : HasForget₂ (HopfAlgCat R) (BialgCat R) where
  forget₂ :=
    { obj := fun X => BialgCat.of R X
      map := fun {_ _} f => BialgCat.ofHom f.toBialgHom }

@[simp]
/-
**HopfAlgCat.forget** 是 Mathlib 中的一个定理，位于命名空间 `HopfAlgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forget₂_bialgebra_obj (X : HopfAlgCat R) :
    (forget₂ (HopfAlgCat R) (BialgCat R)).obj X = BialgCat.of R X :=
  rfl

@[simp]
/-
**HopfAlgCat.forget** 是 Mathlib 中的一个定理，位于命名空间 `HopfAlgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forget₂_bialgebra_map (X Y : HopfAlgCat R) (f : X ⟶ Y) :
    (forget₂ (HopfAlgCat R) (BialgCat R)).map f = BialgCat.ofHom f.toBialgHom :=
  rfl

end HopfAlgCat

namespace BialgEquiv

open HopfAlgCat

variable {X Y Z : Type v}
variable [Ring X] [Ring Y] [Ring Z]
variable [HopfAlgebra R X] [HopfAlgebra R Y] [HopfAlgebra R Z]

/-- Build an isomorphism in the category `HopfAlgCat R` from a
`BialgEquiv`. -/
@[simps]
/-
**BialgEquiv.toHopfAlgIso** 是 Mathlib 中的一个定义，位于命名空间 `BialgEquiv`。
形式化陈述：toHopfAlgIso (e : X ≃ₐc[R] Y) : HopfAlgCat.of R X ≅ HopfAlgCat.of R Y wher
e hom
参数：e : X ≃ₐc[R] Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Build an isomorphism in the category `HopfAlgCat R` from a
`BialgEquiv`.
-/
def toHopfAlgIso (e : X ≃ₐc[R] Y) : HopfAlgCat.of R X ≅ HopfAlgCat.of R Y where
  hom := HopfAlgCat.ofHom e
  inv := HopfAlgCat.ofHom e.symm
  hom_inv_id := Hom.ext <| DFunLike.ext _ _ e.left_inv
  inv_hom_id := Hom.ext <| DFunLike.ext _ _ e.right_inv
/-
**BialgEquiv.toHopfAlgIso_refl** 是 Mathlib 中的一个定理，位于命名空间 `BialgEquiv`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {X : Type v} [inst_1 : Ring X] [inst_2 
: HopfAlgebra R X],   (BialgEquiv.refl R X).toHopfAlgIso = CategoryTheory.Iso.re
fl (HopfAlgCat.of R X)
参数：BialgEquiv.refl R X；HopfAlgCat.of R X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toHopfAlgIso_refl :
    toHopfAlgIso (BialgEquiv.refl R X) = .refl _ :=
  rfl
/-
**BialgEquiv.toHopfAlgIso_symm** 是 Mathlib 中的一个定理，位于命名空间 `BialgEquiv`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {X Y : Type v} [inst_1 : Ring X] [inst_
2 : Ring Y] [inst_3 : HopfAlgebra R X]   [inst_4 : HopfAlgebra R Y] (e : X ≃ₐc[R
] Y), e.symm.toHopfAlgIso = e.toHopfAlgIso.symm
参数：e : X ≃ₐc[R] Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toHopfAlgIso_symm (e : X ≃ₐc[R] Y) :
    toHopfAlgIso e.symm = (toHopfAlgIso e).symm :=
  rfl
/-
**BialgEquiv.toHopfAlgIso_trans** 是 Mathlib 中的一个定理，位于命名空间 `BialgEquiv`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {X Y Z : Type v} [inst_1 : Ring X] [ins
t_2 : Ring Y] [inst_3 : Ring Z]   [inst_4 : HopfAlgebra R X] [inst_5 : HopfAlgeb
ra R Y] [inst_6 : HopfAlgebra R Z] (e : X ≃ₐc[R] Y) (f : Y ≃ₐc[R] Z),   (e.trans
 f).toHopfAlgIso = e.toHopfAlgIso ≪≫ f.toHopfAlgIso
参数：e : X ≃ₐc[R] Y；f : Y ≃ₐc[R] Z；e.trans f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toHopfAlgIso_trans (e : X ≃ₐc[R] Y) (f : Y ≃ₐc[R] Z) :
    toHopfAlgIso (e.trans f) = toHopfAlgIso e ≪≫ toHopfAlgIso f :=
  rfl

end BialgEquiv

namespace CategoryTheory.Iso

open HopfAlgebra

variable {X Y Z : HopfAlgCat.{v} R}

/-- Build a `BialgEquiv` from an isomorphism in the category
`HopfAlgCat R`. -/
/-
**CategoryTheory.Iso.toHopfAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Is
o`。
形式化陈述：toHopfAlgEquiv (i : X ≅ Y) : X ≃ₐc[R] Y
参数：i : X ≅ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Build a `BialgEquiv` from an isomorphism in the category
`HopfAlgCat R`.
-/
def toHopfAlgEquiv (i : X ≅ Y) : X ≃ₐc[R] Y :=
  { i.hom.toBialgHom with
    invFun := i.inv.toBialgHom
    left_inv := fun x => BialgHom.congr_fun (congr_arg HopfAlgCat.Hom.toBialgHom i.3) x
    right_inv := fun x => BialgHom.congr_fun (congr_arg HopfAlgCat.Hom.toBialgHom i.4) x }
/-
**CategoryTheory.Iso.toHopfAlgEquiv_toBialgHom** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Iso`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {X Y : HopfAlgCat R} (i : X ≅ Y), ↑i.to
HopfAlgEquiv = i.hom.toBialgHom'
参数：i : X ≅ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BialgEquivClass.toBialgHomClass`：∀ {F : Type u_1} {R : Type u_2} {A : Ty
pe u_3} {B : Type u_4} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 :
 Semiring B] [inst_3 …
· 使用定理 `BialgEquiv.instBialgEquivClass`：∀ {R : Type u} {A : Type v} {B : Type w}
 [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 :
 Algebra R A] [inst_…
-/
@[simp] theorem toHopfAlgEquiv_toBialgHom (i : X ≅ Y) :
    (i.toHopfAlgEquiv : X →ₐc[R] Y) = i.hom.1 := rfl
/-
**CategoryTheory.Iso.toHopfAlgEquiv_refl** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Iso`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {X : HopfAlgCat R},   (CategoryTheory.I
so.refl X).toHopfAlgEquiv = BialgEquiv.refl R X.carrier
参数：CategoryTheory.Iso.refl X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toHopfAlgEquiv_refl : toHopfAlgEquiv (.refl X) = .refl _ _ :=
  rfl
/-
**CategoryTheory.Iso.toHopfAlgEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Iso`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {X Y : HopfAlgCat R} (e : X ≅ Y), e.sym
m.toHopfAlgEquiv = e.toHopfAlgEquiv.symm
参数：e : X ≅ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toHopfAlgEquiv_symm (e : X ≅ Y) :
    toHopfAlgEquiv e.symm = (toHopfAlgEquiv e).symm :=
  rfl
/-
**CategoryTheory.Iso.toHopfAlgEquiv_trans** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Iso`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {X Y Z : HopfAlgCat R} (e : X ≅ Y) (f :
 Y ≅ Z),   (e ≪≫ f).toHopfAlgEquiv = e.toHopfAlgEquiv.trans f.toHopfAlgEquiv
参数：e : X ≅ Y；f : Y ≅ Z；e ≪≫ f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toHopfAlgEquiv_trans (e : X ≅ Y) (f : Y ≅ Z) :
    toHopfAlgEquiv (e ≪≫ f) = e.toHopfAlgEquiv.trans f.toHopfAlgEquiv :=
  rfl

end CategoryTheory.Iso

/-
**HopfAlgCat.forget_reflects_isos** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：HopfAlgCat.forget_reflects_isos : (forget (HopfAlgCat.{v} R)).ReflectsIsom
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
· 使用定理 `CategoryTheory.IsIso.out`：∀ {C : Type u} {inst : CategoryTheory.Category
.{v, u} C} {X Y : C} {f : X ⟶ Y} [self : CategoryTheory.IsIso f],   ∃ inv,     C
ategoryTheory.…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
instance HopfAlgCat.forget_reflects_isos :
    (forget (HopfAlgCat.{v} R)).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget (HopfAlgCat.{v} R)).map f)
    let e : X ≃ₐc[R] Y := { f.toBialgHom, i.toEquiv with }
    exact ⟨e.toHopfAlgIso.isIso_hom.1⟩
