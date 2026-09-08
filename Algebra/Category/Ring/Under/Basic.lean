/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# Under `CommRingCat`

In this file we provide basic API for `Under R` when `R : CommRingCat`. `Under R` is
(equivalent to) the category of commutative `R`-algebras. For not necessarily commutative
algebras, use `AlgCat R` instead.
-/

@[expose] public section

noncomputable section

universe u

open TensorProduct CategoryTheory Limits

variable {R S : CommRingCat.{u}}

namespace CommRingCat

/-
**CommRingCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommRingCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort (Under R) (Type u) where
  coe A := A.right
/-
**CommRingCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommRingCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (A : Under R) : Algebra R A := RingHom.toAlgebra A.hom.hom

/-- Turn a morphism in `Under R` into an algebra homomorphism. -/
/-
**CommRingCat.toAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `CommRingCat`。
形式化陈述：toAlgHom {A B : Under R} (f : A ⟶ B) : A ->ₐ[R] B where __
参数：f : A ⟶ B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a morphism in `Under R` into an algebra homomorphism.
-/
def toAlgHom {A B : Under R} (f : A ⟶ B) : A →ₐ[R] B where
  __ := f.right.hom
  commutes' a := by
    have : (A.hom ≫ f.right) a = B.hom a := by simp
    simpa only [Functor.const_obj_obj, Functor.id_obj, CommRingCat.comp_apply] using! this

@[simp]
/-
**CommRingCat.toAlgHom_id** 是 Mathlib 中的一个引理，位于命名空间 `CommRingCat`。
形式化陈述：toAlgHom_id (A : Under R) : toAlgHom (𝟙 A) = AlgHom.id R A
参数：A : Under R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toAlgHom_id (A : Under R) : toAlgHom (𝟙 A) = AlgHom.id R A := rfl

@[simp]
/-
**CommRingCat.toAlgHom_comp** 是 Mathlib 中的一个引理，位于命名空间 `CommRingCat`。
形式化陈述：toAlgHom_comp {A B C : Under R} (f : A ⟶ B) (g : B ⟶ C) : toAlgHom (f ≫ g)
 = (toAlgHom g).comp (toAlgHom f)
参数：f : A ⟶ B；g : B ⟶ C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toAlgHom_comp {A B C : Under R} (f : A ⟶ B) (g : B ⟶ C) :
    toAlgHom (f ≫ g) = (toAlgHom g).comp (toAlgHom f) := rfl

@[simp]
/-
**CommRingCat.toAlgHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `CommRingCat`。
形式化陈述：toAlgHom_apply {A B : Under R} (f : A ⟶ B) (a : A) : toAlgHom f a = f.righ
t a
参数：f : A ⟶ B；a : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toAlgHom_apply {A B : Under R} (f : A ⟶ B) (a : A) :
    toAlgHom f a = f.right a :=
  rfl

variable (R) in
/-- Make an object of `Under R` from an `R`-algebra. -/
@[implicit_reducible, simps! hom, simps! -isSimp right]
/-
**CommRingCat.mkUnder** 是 Mathlib 中的一个定义，位于命名空间 `CommRingCat`。
形式化陈述：mkUnder (A : Type u) [CommRing A] [Algebra R A] : Under R
参数：A : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Make an object of `Under R` from an `R`-algebra.
-/
def mkUnder (A : Type u) [CommRing A] [Algebra R A] : Under R :=
  Under.mk (CommRingCat.ofHom <| algebraMap R A)

@[ext]
/-
**CommRingCat.mkUnder_ext** 是 Mathlib 中的一个引理，位于命名空间 `CommRingCat`。
形式化陈述：mkUnder_ext {A : Type u} [CommRing A] [Algebra R A] {B : Under R} {f g : m
kUnder R A ⟶ B} (h : forall a : A, f.right a = g.right a) : f = g
参数：h : forall a : A, f.right a = g.right a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Under.UnderMorphism.ext`：∀ {T : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} T] {X : T} {U V : CategoryTheory.Under X} {f g : U ⟶ V}
,   CategoryTheory.Under.Hom…
· 使用引理 `CommRingCat.hom_ext`：hom_ext {R S : CommRingCat} {f g : R ⟶ S} (hf : f.h
om = g.hom) : f = g
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
-/
lemma mkUnder_ext {A : Type u} [CommRing A] [Algebra R A] {B : Under R}
    {f g : mkUnder R A ⟶ B} (h : ∀ a : A, f.right a = g.right a) :
    f = g := by
  ext x
  exact h x

end CommRingCat

namespace AlgHom

/-- Make a morphism in `Under R` from an algebra map. -/
/-
**AlgHom.toUnder** 是 Mathlib 中的一个定义，位于命名空间 `AlgHom`。
形式化陈述：toUnder {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R 
B] (f : A ->ₐ[R] B) : CommRingCat.mkUnder R A ⟶ CommRingCat.mkUnder R B
参数：f : A ->ₐ[R] B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Make a morphism in `Under R` from an algebra map.
-/
def toUnder {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) : CommRingCat.mkUnder R A ⟶ CommRingCat.mkUnder R B :=
  Under.homMk (CommRingCat.ofHom f.toRingHom) <| by
    ext a
    exact f.commutes' a

@[simp]
/-
**AlgHom.toUnder_right** 是 Mathlib 中的一个引理，位于命名空间 `AlgHom`。
形式化陈述：toUnder_right {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Alge
bra R B] (f : A ->ₐ[R] B) (a : A) : Under.Hom.right f.toUnder a = f a
参数：f : A ->ₐ[R] B；a : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toUnder_right {A B : Type u} [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (f : A →ₐ[R] B) (a : A) :
    Under.Hom.right f.toUnder a = f a :=
  rfl

@[simp]
/-
**AlgHom.toUnder_comp** 是 Mathlib 中的一个引理，位于命名空间 `AlgHom`。
形式化陈述：toUnder_comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Alge
bra R A] [Algebra R B] [Algebra R C] (f : A ->ₐ[R] B) (g : B ->ₐ[R] C) : (g.comp
 f).toUnder = f.toUnder ≫ g.toUnder
参数：f : A ->ₐ[R] B；g : B ->ₐ[R] C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toUnder_comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C] (f : A →ₐ[R] B) (g : B →ₐ[R] C) :
    (g.comp f).toUnder = f.toUnder ≫ g.toUnder :=
  rfl

end AlgHom

namespace AlgEquiv

/-- Make an isomorphism in `Under R` from an algebra isomorphism. -/
/-
**AlgEquiv.toUnder** 是 Mathlib 中的一个定义，位于命名空间 `AlgEquiv`。
形式化陈述：toUnder {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R 
B] (f : A ≃ₐ[R] B) : CommRingCat.mkUnder R A ≅ CommRingCat.mkUnder R B where hom
参数：f : A ≃ₐ[R] B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Make an isomorphism in `Under R` from an algebra isomorphism.
-/
def toUnder {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f : A ≃ₐ[R] B) :
    CommRingCat.mkUnder R A ≅ CommRingCat.mkUnder R B where
  hom := f.toAlgHom.toUnder
  inv := f.symm.toAlgHom.toUnder

@[simp]
/-
**AlgEquiv.toUnder_hom_right_apply** 是 Mathlib 中的一个引理，位于命名空间 `AlgEquiv`。
形式化陈述：toUnder_hom_right_apply {A B : Type u} [CommRing A] [CommRing B] [Algebra 
R A] [Algebra R B] (f : A ≃ₐ[R] B) (a : A) : f.toUnder.hom.right a = f a
参数：f : A ≃ₐ[R] B；a : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toUnder_hom_right_apply {A B : Type u} [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (f : A ≃ₐ[R] B) (a : A) :
    f.toUnder.hom.right a = f a := rfl

@[simp]
/-
**AlgEquiv.toUnder_inv_right_apply** 是 Mathlib 中的一个引理，位于命名空间 `AlgEquiv`。
形式化陈述：toUnder_inv_right_apply {A B : Type u} [CommRing A] [CommRing B] [Algebra 
R A] [Algebra R B] (f : A ≃ₐ[R] B) (b : B) : f.toUnder.inv.right b = f.symm b
参数：f : A ≃ₐ[R] B；b : B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toUnder_inv_right_apply {A B : Type u} [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (f : A ≃ₐ[R] B) (b : B) :
    f.toUnder.inv.right b = f.symm b := rfl

@[simp]
/-
**AlgEquiv.toUnder_trans** 是 Mathlib 中的一个引理，位于命名空间 `AlgEquiv`。
形式化陈述：toUnder_trans {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Alg
ebra R A] [Algebra R B] [Algebra R C] (f : A ≃ₐ[R] B) (g : B ≃ₐ[R] C) : (f.trans
 g).toUnder = f.toUnder ≪≫ g.toUnder
参数：f : A ≃ₐ[R] B；g : B ≃ₐ[R] C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toUnder_trans {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C] (f : A ≃ₐ[R] B) (g : B ≃ₐ[R] C) :
    (f.trans g).toUnder = f.toUnder ≪≫ g.toUnder :=
  rfl

end AlgEquiv

namespace CommRingCat

variable [Algebra R S]

variable (R S) in
/-- The base change functor `A ↦ S ⊗[R] A`. -/
@[simps! obj_right map_right]
/-
**CommRingCat.tensorProd** 是 Mathlib 中的一个定义，位于命名空间 `CommRingCat`。
形式化陈述：tensorProd : Under R ⥤ Under S where obj A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The base change functor `A ↦ S ⊗[R] A`.
-/
def tensorProd : Under R ⥤ Under S where
  obj A := mkUnder S (S ⊗[R] A)
  map f := Algebra.TensorProduct.map (AlgHom.id S S) (toAlgHom f) |>.toUnder
  map_comp {X Y Z} f g := by simp [Algebra.TensorProduct.map_id_comp]

set_option backward.isDefEq.respectTransparency false in
variable (S) in
/-- The natural isomorphism `S ⊗[R] A ≅ pushout A.hom (algebraMap R S)` in `Under S`. -/
/-
**CommRingCat.tensorProdObjIsoPushoutObj** 是 Mathlib 中的一个定义，位于命名空间 `CommRingCat`
。
形式化陈述：tensorProdObjIsoPushoutObj (A : Under R) : mkUnder S (S otimes[R] A) ≅ (Un
der.pushout (ofHom <| algebraMap R S)).obj A
参数：A : Under R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isomorphism `S ⊗[R] A ≅ pushout A.hom (algebraMap R S)` in `Under S`
.
-/
def tensorProdObjIsoPushoutObj (A : Under R) :
    mkUnder S (S ⊗[R] A) ≅ (Under.pushout (ofHom <| algebraMap R S)).obj A :=
  Under.isoMk (CommRingCat.isPushout_tensorProduct R S A).flip.isoPushout <| by
    simp only [mkUnder_hom, AlgHom.toRingHom_eq_coe, IsPushout.inr_isoPushout_hom]
    rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CommRingCat.pushout_inl_tensorProdObjIsoPushoutObj_inv_right** 是 Mathlib 中的一个引
理，位于命名空间 `CommRingCat`。
形式化陈述：pushout_inl_tensorProdObjIsoPushoutObj_inv_right (A : Under R) : pushout.i
nl A.hom (ofHom <| algebraMap R S) ≫ (tensorProdObjIsoPushoutObj S A).inv.right 
= (ofHom <| Algebra.TensorProduct.includeRight.toRingHom)
参数：A : Under R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePushouts_of_has_finite_limits`：∀ (C :
 Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFin
iteColimits C],   CategoryTheory.Limits.HasFiniteWideP…
· 使用定理 `CategoryTheory.Limits.hasFiniteColimits_of_hasColimits`：∀ (C : Type u) [
inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasColimits C], 
  CategoryTheory.Limits.HasFiniteColimits C
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Under.isoMk_inv_right`：∀ {T : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} T] {X : T} {f g : CategoryTheory.Under X}   (hr : f.right
 ≅ g.right)   (hw : autoPa…
· 使用定理 `CategoryTheory.IsPushout.inl_isoPushout_inv`：inl_isoPushout_inv (h : IsP
ushout f g inl inr) [HasPushout f g] : pushout.inl _ _ ≫ h.isoPushout.inv = inl
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pushout_inl_tensorProdObjIsoPushoutObj_inv_right (A : Under R) :
    pushout.inl A.hom (ofHom <| algebraMap R S) ≫ (tensorProdObjIsoPushoutObj S A).inv.right =
      (ofHom <| Algebra.TensorProduct.includeRight.toRingHom) := by
  simp [tensorProdObjIsoPushoutObj]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CommRingCat.pushout_inr_tensorProdObjIsoPushoutObj_inv_right** 是 Mathlib 中的一个引
理，位于命名空间 `CommRingCat`。
形式化陈述：pushout_inr_tensorProdObjIsoPushoutObj_inv_right (A : Under R) : pushout.i
nr A.hom (ofHom <| algebraMap R S) ≫ (tensorProdObjIsoPushoutObj S A).inv.right 
= (CommRingCat.ofHom <| Algebra.TensorProduct.includeLeftRingHom)
参数：A : Under R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePushouts_of_has_finite_limits`：∀ (C :
 Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFin
iteColimits C],   CategoryTheory.Limits.HasFiniteWideP…
· 使用定理 `CategoryTheory.Limits.hasFiniteColimits_of_hasColimits`：∀ (C : Type u) [
inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasColimits C], 
  CategoryTheory.Limits.HasFiniteColimits C
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `CategoryTheory.Under.isoMk_inv_right`：∀ {T : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} T] {X : T} {f g : CategoryTheory.Under X}   (hr : f.right
 ≅ g.right)   (hw : autoPa…
· 使用定理 `CategoryTheory.IsPushout.inr_isoPushout_inv`：inr_isoPushout_inv (h : IsP
ushout f g inl inr) [HasPushout f g] : pushout.inr _ _ ≫ h.isoPushout.inv = inr
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pushout_inr_tensorProdObjIsoPushoutObj_inv_right (A : Under R) :
    pushout.inr A.hom (ofHom <| algebraMap R S) ≫
      (tensorProdObjIsoPushoutObj S A).inv.right =
      (CommRingCat.ofHom <| Algebra.TensorProduct.includeLeftRingHom) := by
  simp [tensorProdObjIsoPushoutObj]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable (R S) in
/-- `A ↦ S ⊗[R] A` is naturally isomorphic to `A ↦ pushout A.hom (algebraMap R S)`. -/
/-
**CommRingCat.tensorProdIsoPushout** 是 Mathlib 中的一个定义，位于命名空间 `CommRingCat`。
形式化陈述：tensorProdIsoPushout : tensorProd R S ≅ Under.pushout (ofHom <| algebraMap
 R S)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`A ↦ S ⊗[R] A` is naturally isomorphic to `A ↦ pushout A.hom (algebraMap R S)`.
-/
def tensorProdIsoPushout : tensorProd R S ≅ Under.pushout (ofHom <| algebraMap R S) :=
  NatIso.ofComponents (fun A ↦ tensorProdObjIsoPushoutObj S A) <| by
    intro A B f
    dsimp
    rw [← cancel_epi (tensorProdObjIsoPushoutObj S A).inv]
    ext : 1
    apply pushout.hom_ext
    · rw [← cancel_mono (tensorProdObjIsoPushoutObj S B).inv.right]
      ext x
      simp [mkUnder_right]
    · rw [← cancel_mono (tensorProdObjIsoPushoutObj S B).inv.right]
      ext (x : S)
      simp [mkUnder_right]

@[simp]
/-
**CommRingCat.tensorProdIsoPushout_app** 是 Mathlib 中的一个引理，位于命名空间 `CommRingCat`。
形式化陈述：tensorProdIsoPushout_app (A : Under R) : (tensorProdIsoPushout R S).app A 
= tensorProdObjIsoPushoutObj S A
参数：A : Under R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePushouts_of_has_finite_limits`：∀ (C :
 Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFin
iteColimits C],   CategoryTheory.Limits.HasFiniteWideP…
· 使用定理 `CategoryTheory.Limits.hasFiniteColimits_of_hasColimits`：∀ (C : Type u) [
inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasColimits C], 
  CategoryTheory.Limits.HasFiniteColimits C
-/
lemma tensorProdIsoPushout_app (A : Under R) :
    (tensorProdIsoPushout R S).app A = tensorProdObjIsoPushoutObj S A :=
  rfl

end CommRingCat

