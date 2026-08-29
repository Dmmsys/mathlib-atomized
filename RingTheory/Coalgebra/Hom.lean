/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov, Amelia Livingston
-/
module

public import Mathlib.RingTheory.Coalgebra.Basic

/-!
# Homomorphisms of `R`-coalgebras

This file defines bundled homomorphisms of `R`-coalgebras. We largely mimic
`Mathlib/Algebra/Algebra/Hom.lean`.

## Main definitions

* `CoalgHom R A B`: the type of `R`-coalgebra morphisms from `A` to `B`.
* `Coalgebra.counitCoalgHom R A : A →ₗc[R] R`: the counit of a coalgebra as a coalgebra
  homomorphism.

## Notation

* `A →ₗc[R] B` : `R`-coalgebra homomorphism from `A` to `B`.

-/

@[expose] public section

open TensorProduct Coalgebra

universe u v w

/--
Definition of `CoalgHom` / `CoalgHom` 的定义

English:
structure CoalgHom
  parameters: (R A B : Type*) [CommSemiring R]
  extends: A ->ₗ[R] B
  axioms and operations (2):
    - counit_comp : counit ∘ₗ toLinearMap = counit
    - map_comp_comul : TensorProduct.map toLinearMap toLinearMap ∘ₗ comul = comul ∘ₗ toLinearMap

中文:
结构 CoalgHom
  参数: (R A B : 类型) [CommSemiring R]
  继承: A ->ₗ[R] B
  公理与运算 (2 个):
    - counit_comp : counit ∘ₗ toLinearMap = counit
    - map_comp_comul : TensorProduct.map toLinearMap toLinearMap ∘ₗ comul = comul ∘ₗ toLinearMap
-/
structure CoalgHom (R A B : Type*) [CommSemiring R]
    [AddCommMonoid A] [Module R A] [AddCommMonoid B] [Module R B]
    [CoalgebraStruct R A] [CoalgebraStruct R B] extends A ->ₗ[R] B where
  counit_comp : counit ∘ₗ toLinearMap = counit
  map_comp_comul : TensorProduct.map toLinearMap toLinearMap ∘ₗ comul = comul ∘ₗ toLinearMap

@[inherit_doc CoalgHom]
infixr:25 " ->ₗc " => CoalgHom _

@[inherit_doc]
notation:25 A " ->ₗc[" R "] " B => CoalgHom R A B

/--
Definition of `CoalgHomClass` / `CoalgHomClass` 的定义

English:
class CoalgHomClass
  parameters: (F : Type*) (R A B : outParam Type*)
  extends: SemilinearMapClass F (RingHom.id R) A B
  axioms and operations (2):
    - counit_comp : forall f : F, counit ∘ₗ (f : A ->ₗ[R] B) = counit
    - map_comp_comul : forall f : F, TensorProduct.map (f : A ->ₗ[R] B) (f : A ->ₗ[R] B) ∘ₗ comul = comul ∘ₗ (f : A ->ₗ[R] B)

中文:
类 CoalgHomClass
  参数: (F : 类型) (R A B : outParam 类型)
  继承: SemilinearMapClass F (RingHom.id R) A B
  公理与运算 (2 个):
    - counit_comp : 对任意 f : F, counit ∘ₗ (f : A ->ₗ[R] B) = counit
    - map_comp_comul : 对任意 f : F, TensorProduct.map (f : A ->ₗ[R] B) (f : A ->ₗ[R] B) ∘ₗ comul = comul ∘ₗ (f : A ->ₗ[R] B)
-/
class CoalgHomClass (F : Type*) (R A B : outParam Type*)
    [CommSemiring R] [AddCommMonoid A] [Module R A] [AddCommMonoid B] [Module R B]
    [CoalgebraStruct R A] [CoalgebraStruct R B] [FunLike F A B] : Prop
    extends SemilinearMapClass F (RingHom.id R) A B where
  counit_comp : forall f : F, counit ∘ₗ (f : A ->ₗ[R] B) = counit
  map_comp_comul : forall f : F, TensorProduct.map (f : A ->ₗ[R] B)
    (f : A ->ₗ[R] B) ∘ₗ comul = comul ∘ₗ (f : A ->ₗ[R] B)

attribute [simp] CoalgHomClass.counit_comp CoalgHomClass.map_comp_comul

namespace CoalgHomClass

variable {R A B F : Type*} [CommSemiring R]
  [AddCommMonoid A] [Module R A] [AddCommMonoid B] [Module R B]
  [CoalgebraStruct R A] [CoalgebraStruct R B] [FunLike F A B]
  [CoalgHomClass F R A B]

/-- Turn an element of a type `F` satisfying `CoalgHomClass F R A B` into an actual
`CoalgHom`. This is declared as the default coercion from `F` to `A →ₗc[R] B`. -/
@[coe]
/--
Definition of `toCoalgHom` / `toCoalgHom` 的定义

English:
definition toCoalgHom
  signature: (f : F)
  body: { (f : A ->ₗ[R] B) with
    toFun := f
    counit_comp := CoalgHomClass.counit_comp f
    map_comp_comul := CoalgHomClass.map_comp_comul f }

中文:
定义 toCoalgHom
  签名: (f : F)
  定义体: { (f : A ->ₗ[R] B) with
    toFun := f
    counit_comp := CoalgHomClass.counit_comp f
    map_comp_comul := CoalgHomClass.map_comp_comul f }

Depends on / 依赖: CoalgHomClass, CoalgHomClass.counit_comp, CoalgHomClass.map_comp_comul, counit_comp, map_comp_comul
-/
def toCoalgHom (f : F) : A ->ₗc[R] B :=
  { (f : A ->ₗ[R] B) with
    toFun := f
    counit_comp := CoalgHomClass.counit_comp f
    map_comp_comul := CoalgHomClass.map_comp_comul f }

/--
Instance `instCoeToCoalgHom` / 实例 `instCoeToCoalgHom`

English:
instance instCoeToCoalgHom
  signature: : CoeHead F (A ->ₗc[R] B)
  body: ⟨CoalgHomClass.toCoalgHom⟩

@[simp]

中文:
实例 instCoeToCoalgHom
  签名: : CoeHead F (A ->ₗc[R] B)
  定义体: ⟨CoalgHomClass.toCoalgHom⟩

@[simp]

Depends on / 依赖: CoalgHomClass, CoalgHomClass.toCoalgHom, toCoalgHom
-/
instance instCoeToCoalgHom : CoeHead F (A ->ₗc[R] B) :=
  ⟨CoalgHomClass.toCoalgHom⟩

@[simp]
/--
theorem `counit_comp_apply` / 定理 `counit_comp_apply`

English:
theorem counit_comp_apply
  given: (f : F) (x : A)
  statement: counit (f x) = counit (R := R) x
  proof: LinearMap.congr_fun (counit_comp f) _

@[simp]

中文:
定理 counit_comp_apply
  条件: (f : F) (x : A)
  结论: counit (f x) = counit (R := R) x
  证明: LinearMap.congr_fun (counit_comp f) _

@[simp]
-/
theorem counit_comp_apply (f : F) (x : A) : counit (f x) = counit (R := R) x :=
  LinearMap.congr_fun (counit_comp f) _

@[simp]
/--
theorem `map_comp_comul_apply` / 定理 `map_comp_comul_apply`

English:
theorem map_comp_comul_apply
  given: (f : F) (x : A)
  proof: LinearMap.congr_fun (map_comp_comul f) _

中文:
定理 map_comp_comul_apply
  条件: (f : F) (x : A)
  证明: LinearMap.congr_fun (map_comp_comul f) _
-/
theorem map_comp_comul_apply (f : F) (x : A) :
    TensorProduct.map f f (σ₁₂ := .id _) (comul x) = comul (R := R) (f x) :=
  LinearMap.congr_fun (map_comp_comul f) _

end CoalgHomClass

namespace CoalgHom

variable {R A B C D : Type*}

section

variable [CommSemiring R] [AddCommMonoid A] [Module R A] [AddCommMonoid B] [Module R B]
  [AddCommMonoid C] [Module R C] [AddCommMonoid D] [Module R D]
  [CoalgebraStruct R A] [CoalgebraStruct R B] [CoalgebraStruct R C] [CoalgebraStruct R D]

/--
Instance `funLike` / 实例 `funLike`

English:
instance funLike
  signature: : FunLike (A ->ₗc[R] B) A B where
  body: f.toFun
  coe_injective f g h := by
    rcases f with ⟨⟨⟨_, _⟩, _⟩, _, _⟩
    rcases g with ⟨⟨⟨_, _⟩, _⟩, _, _⟩
    congr

中文:
实例 funLike
  签名: : FunLike (A ->ₗc[R] B) A B where
  定义体: f.toFun
  coe_injective f g h := by
    rcases f with ⟨⟨⟨_, _⟩, _⟩, _, _⟩
    rcases g with ⟨⟨⟨_, _⟩, _⟩, _, _⟩
    congr

Depends on / 依赖: f.toFun
-/
instance funLike : FunLike (A ->ₗc[R] B) A B where
  coe f := f.toFun
  coe_injective f g h := by
    rcases f with ⟨⟨⟨_, _⟩, _⟩, _, _⟩
    rcases g with ⟨⟨⟨_, _⟩, _⟩, _, _⟩
    congr

/--
Instance `coalgHomClass` / 实例 `coalgHomClass`

English:
instance coalgHomClass
  signature: : CoalgHomClass (A ->ₗc[R] B) R A B where
  body: fun f => f.map_add'
  map_smulₛₗ := fun f => f.map_smul'
  counit_comp := fun f => f.counit_comp
  map_comp_comul := fun f => f.map_comp_comul

中文:
实例 coalgHomClass
  签名: : CoalgHomClass (A ->ₗc[R] B) R A B where
  定义体: fun f => f.map_add'
  map_smulₛₗ := fun f => f.map_smul'
  counit_comp := fun f => f.counit_comp
  map_comp_comul := fun f => f.map_comp_comul

Depends on / 依赖: f.map_add, map_add
-/
instance coalgHomClass : CoalgHomClass (A ->ₗc[R] B) R A B where
  map_add := fun f => f.map_add'
  map_smulₛₗ := fun f => f.map_smul'
  counit_comp := fun f => f.counit_comp
  map_comp_comul := fun f => f.map_comp_comul

/--
Definition of `Simps.apply` / `Simps.apply` 的定义

English:
definition Simps.apply
  signature: {R α β : Type*} [CommSemiring R]
  body: f

initialize_simps_projections CoalgHom (toFun -> apply)

@[simp]

中文:
定义 Simps.apply
  签名: {R α β : 类型} [CommSemiring R]
  定义体: f

initialize_simps_projections CoalgHom (toFun -> apply)

@[simp]
-/
def Simps.apply {R α β : Type*} [CommSemiring R]
    [AddCommMonoid α] [Module R α] [AddCommMonoid β]
    [Module R β] [CoalgebraStruct R α] [CoalgebraStruct R β]
    (f : α ->ₗc[R] β) : α -> β := f

initialize_simps_projections CoalgHom (toFun -> apply)

@[simp]
/--
theorem `coe_coe` / 定理 `coe_coe`

English:
theorem coe_coe
  given: {F : Type*} [FunLike F A B] [CoalgHomClass F R A B] (f : F)
  proof: rfl

@[simp]

中文:
定理 coe_coe
  条件: {F : 类型} [FunLike F A B] [CoalgHomClass F R A B] (f : F)
  证明: rfl

@[simp]
-/
protected theorem coe_coe {F : Type*} [FunLike F A B] [CoalgHomClass F R A B] (f : F) :
    ⇑(f : A ->ₗc[R] B) = f :=
  rfl

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: {f : A ->ₗ[R] B} (h h₁)
  statement: ((⟨f, h, h₁⟩ : A ->ₗc[R] B) : A -> B) = f
  proof: rfl

@[norm_cast]

中文:
定理 coe_mk
  条件: {f : A ->ₗ[R] B} (h h₁)
  结论: ((⟨f, h, h₁⟩ : A ->ₗc[R] B) : A -> B) = f
  证明: rfl

@[norm_cast]
-/
theorem coe_mk {f : A ->ₗ[R] B} (h h₁) : ((⟨f, h, h₁⟩ : A ->ₗc[R] B) : A -> B) = f :=
  rfl

@[norm_cast]
/--
theorem `coe_mks` / 定理 `coe_mks`

English:
theorem coe_mks
  given: {f : A -> B} (h₁ h₂ h₃ h₄)
  statement: ⇑(⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩ : A ->ₗc[R] B) = f
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_mks
  条件: {f : A -> B} (h₁ h₂ h₃ h₄)
  结论: ⇑(⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩ : A ->ₗc[R] B) = f
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_mks {f : A -> B} (h₁ h₂ h₃ h₄) : ⇑(⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩ : A ->ₗc[R] B) = f :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_linearMap_mk` / 定理 `coe_linearMap_mk`

English:
theorem coe_linearMap_mk
  given: {f : A ->ₗ[R] B} (h h₁)
  statement: ((⟨f, h, h₁⟩ : A ->ₗc[R] B) : A ->ₗ[R] B) = f
  proof: rfl

@[simp]

中文:
定理 coe_linearMap_mk
  条件: {f : A ->ₗ[R] B} (h h₁)
  结论: ((⟨f, h, h₁⟩ : A ->ₗc[R] B) : A ->ₗ[R] B) = f
  证明: rfl

@[simp]
-/
theorem coe_linearMap_mk {f : A ->ₗ[R] B} (h h₁) : ((⟨f, h, h₁⟩ : A ->ₗc[R] B) : A ->ₗ[R] B) = f :=
  rfl

@[simp]
/--
theorem `toLinearMap_eq_coe` / 定理 `toLinearMap_eq_coe`

English:
theorem toLinearMap_eq_coe
  given: (f : A ->ₗc[R] B)
  statement: f.toLinearMap = f
  proof: rfl

@[simp, norm_cast]

中文:
定理 toLinearMap_eq_coe
  条件: (f : A ->ₗc[R] B)
  结论: f.toLinearMap = f
  证明: rfl

@[simp, norm_cast]
-/
theorem toLinearMap_eq_coe (f : A ->ₗc[R] B) : f.toLinearMap = f :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_toLinearMap` / 定理 `coe_toLinearMap`

English:
theorem coe_toLinearMap
  given: (f : A ->ₗc[R] B)
  statement: ⇑(f : A ->ₗ[R] B) = f
  proof: rfl

@[norm_cast]

中文:
定理 coe_toLinearMap
  条件: (f : A ->ₗc[R] B)
  结论: ⇑(f : A ->ₗ[R] B) = f
  证明: rfl

@[norm_cast]
-/
theorem coe_toLinearMap (f : A ->ₗc[R] B) : ⇑(f : A ->ₗ[R] B) = f :=
  rfl

@[norm_cast]
/--
theorem `coe_toAddMonoidHom` / 定理 `coe_toAddMonoidHom`

English:
theorem coe_toAddMonoidHom
  given: (f : A ->ₗc[R] B)
  statement: ⇑(f : A ->+ B) = f
  proof: rfl

中文:
定理 coe_toAddMonoidHom
  条件: (f : A ->ₗc[R] B)
  结论: ⇑(f : A ->+ B) = f
  证明: rfl
-/
theorem coe_toAddMonoidHom (f : A ->ₗc[R] B) : ⇑(f : A ->+ B) = f :=
  rfl

/--
theorem `coe_fn_injective` / 定理 `coe_fn_injective`

English:
theorem coe_fn_injective
  statement: @Function.Injective (A ->ₗc[R] B) (A -> B) (↑)
  proof: DFunLike.coe_injective

中文:
定理 coe_fn_injective
  结论: @Function.Injective (A ->ₗc[R] B) (A -> B) (↑)
  证明: DFunLike.coe_injective

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem coe_fn_injective : @Function.Injective (A ->ₗc[R] B) (A -> B) (↑) :=
  DFunLike.coe_injective

/--
theorem `coe_fn_inj` / 定理 `coe_fn_inj`

English:
theorem coe_fn_inj
  given: {φ₁ φ₂ : A ->ₗc[R] B}
  statement: (φ₁ : A -> B) = φ₂ ↔ φ₁ = φ₂
  proof: DFunLike.coe_fn_eq

中文:
定理 coe_fn_inj
  条件: {φ₁ φ₂ : A ->ₗc[R] B}
  结论: (φ₁ : A -> B) = φ₂ ↔ φ₁ = φ₂
  证明: DFunLike.coe_fn_eq

Depends on / 依赖: DFunLike, DFunLike.coe_fn_eq, coe_fn_eq
-/
theorem coe_fn_inj {φ₁ φ₂ : A ->ₗc[R] B} : (φ₁ : A -> B) = φ₂ ↔ φ₁ = φ₂ :=
  DFunLike.coe_fn_eq

/--
theorem `coe_linearMap_injective` / 定理 `coe_linearMap_injective`

English:
theorem coe_linearMap_injective
  statement: Function.Injective ((↑) : (A ->ₗc[R] B) -> A ->ₗ[R] B)
  proof: fun φ₁ φ₂ H => coe_fn_injective
    show ((φ₁ : A ->ₗ[R] B) : A -> B) = ((φ₂ : A ->ₗ[R] B) : A -> B) from congr_arg _ H

中文:
定理 coe_linearMap_injective
  结论: Function.Injective ((↑) : (A ->ₗc[R] B) -> A ->ₗ[R] B)
  证明: fun φ₁ φ₂ H => coe_fn_injective
    show ((φ₁ : A ->ₗ[R] B) : A -> B) = ((φ₂ : A ->ₗ[R] B) : A -> B) from congr_arg _ H

Depends on / 依赖: coe_fn_injective, congr_arg
-/
theorem coe_linearMap_injective : Function.Injective ((↑) : (A ->ₗc[R] B) -> A ->ₗ[R] B) :=
fun φ₁ φ₂ H => coe_fn_injective
    show ((φ₁ : A ->ₗ[R] B) : A -> B) = ((φ₂ : A ->ₗ[R] B) : A -> B) from congr_arg _ H

/--
theorem `coe_addMonoidHom_injective` / 定理 `coe_addMonoidHom_injective`

English:
theorem coe_addMonoidHom_injective
  statement: Function.Injective ((↑) : (A ->ₗc[R] B) -> A ->+ B)
  proof: LinearMap.toAddMonoidHom_injective.comp coe_linearMap_injective

中文:
定理 coe_addMonoidHom_injective
  结论: Function.Injective ((↑) : (A ->ₗc[R] B) -> A ->+ B)
  证明: LinearMap.toAddMonoidHom_injective.comp coe_linearMap_injective

Depends on / 依赖: LinearMap, LinearMap.toAddMonoidHom_injective.comp, coe_linearMap_injective, toAddMonoidHom_injective
-/
theorem coe_addMonoidHom_injective : Function.Injective ((↑) : (A ->ₗc[R] B) -> A ->+ B) :=
  LinearMap.toAddMonoidHom_injective.comp coe_linearMap_injective

/--
theorem `congr_fun` / 定理 `congr_fun`

English:
theorem congr_fun
  given: {φ₁ φ₂ : A ->ₗc[R] B} (H : φ₁ = φ₂) (x : A)
  statement: φ₁ x = φ₂ x
  proof: DFunLike.congr_fun H x

中文:
定理 congr_fun
  条件: {φ₁ φ₂ : A ->ₗc[R] B} (H : φ₁ = φ₂) (x : A)
  结论: φ₁ x = φ₂ x
  证明: DFunLike.congr_fun H x
-/
protected theorem congr_fun {φ₁ φ₂ : A ->ₗc[R] B} (H : φ₁ = φ₂) (x : A) : φ₁ x = φ₂ x :=
  DFunLike.congr_fun H x

/--
theorem `congr_arg` / 定理 `congr_arg`

English:
theorem congr_arg
  given: (φ : A ->ₗc[R] B) {x y : A} (h : x = y)
  statement: φ x = φ y
  proof: DFunLike.congr_arg φ h

@[ext]

中文:
定理 congr_arg
  条件: (φ : A ->ₗc[R] B) {x y : A} (h : x = y)
  结论: φ x = φ y
  证明: DFunLike.congr_arg φ h

@[ext]
-/
protected theorem congr_arg (φ : A ->ₗc[R] B) {x y : A} (h : x = y) : φ x = φ y :=
  DFunLike.congr_arg φ h

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {φ₁ φ₂ : A ->ₗc[R] B} (H : forall x, φ₁ x = φ₂ x)
  statement: φ₁ = φ₂
  proof: DFunLike.ext _ _ H

@[ext high]

中文:
定理 ext
  条件: {φ₁ φ₂ : A ->ₗc[R] B} (H : 对任意 x, φ₁ x = φ₂ x)
  结论: φ₁ = φ₂
  证明: DFunLike.ext _ _ H

@[ext high]

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {φ₁ φ₂ : A ->ₗc[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = φ₂ :=
  DFunLike.ext _ _ H

@[ext high]
/--
theorem `ext_of_ring` / 定理 `ext_of_ring`

English:
theorem ext_of_ring
  given: {f g : R ->ₗc[R] A} (h : f 1 = g 1)
  statement: f = g
  proof: coe_linearMap_injective (by ext; assumption)

@[simp]

中文:
定理 ext_of_ring
  条件: {f g : R ->ₗc[R] A} (h : f 1 = g 1)
  结论: f = g
  证明: coe_linearMap_injective (by ext; assumption)

@[simp]

Depends on / 依赖: coe_linearMap_injective
-/
theorem ext_of_ring {f g : R ->ₗc[R] A} (h : f 1 = g 1) : f = g :=
  coe_linearMap_injective (by ext; assumption)

@[simp]
/--
theorem `mk_coe` / 定理 `mk_coe`

English:
theorem mk_coe
  given: {f : A ->ₗc[R] B} (h₁ h₂ h₃ h₄)
  statement: (⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩ : A ->ₗc[R] B) = f
  proof: ext fun _ => rfl

中文:
定理 mk_coe
  条件: {f : A ->ₗc[R] B} (h₁ h₂ h₃ h₄)
  结论: (⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩ : A ->ₗc[R] B) = f
  证明: ext fun _ => rfl
-/
theorem mk_coe {f : A ->ₗc[R] B} (h₁ h₂ h₃ h₄) : (⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩ : A ->ₗc[R] B) = f :=
  ext fun _ => rfl

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (f : A ->ₗc[R] B) (f' : A -> B) (h : f' = ⇑f)
  body: { toLinearMap := (f : A ->ₗ[R] B).copy f' h
    counit_comp := by ext; simp_all
    map_comp_comul := by simp only [(f : A ->ₗ[R] B).copy_eq f' h,
      CoalgHomClass.map_comp_comul] }

@[simp]

中文:
定义 copy
  签名: (f : A ->ₗc[R] B) (f' : A -> B) (h : f' = ⇑f)
  定义体: { toLinearMap := (f : A ->ₗ[R] B).copy f' h
    counit_comp := by ext; simp_all
    map_comp_comul := by simp only [(f : A ->ₗ[R] B).copy_eq f' h,
      CoalgHomClass.map_comp_comul] }

@[simp]
-/
protected def copy (f : A ->ₗc[R] B) (f' : A -> B) (h : f' = ⇑f) : A ->ₗc[R] B :=
  { toLinearMap := (f : A ->ₗ[R] B).copy f' h
    counit_comp := by ext; simp_all
    map_comp_comul := by simp only [(f : A ->ₗ[R] B).copy_eq f' h,
      CoalgHomClass.map_comp_comul] }

@[simp]
/--
theorem `coe_copy` / 定理 `coe_copy`

English:
theorem coe_copy
  given: (f : A ->ₗc[R] B) (f' : A -> B) (h : f' = ⇑f)
  statement: ⇑(f.copy f' h) = f'
  proof: rfl

中文:
定理 coe_copy
  条件: (f : A ->ₗc[R] B) (f' : A -> B) (h : f' = ⇑f)
  结论: ⇑(f.copy f' h) = f'
  证明: rfl
-/
theorem coe_copy (f : A ->ₗc[R] B) (f' : A -> B) (h : f' = ⇑f) : ⇑(f.copy f' h) = f' :=
  rfl

/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (f : A ->ₗc[R] B) (f' : A -> B) (h : f' = ⇑f)
  statement: f.copy f' h = f
  proof: DFunLike.ext' h

中文:
定理 copy_eq
  条件: (f : A ->ₗc[R] B) (f' : A -> B) (h : f' = ⇑f)
  结论: f.copy f' h = f
  证明: DFunLike.ext' h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem copy_eq (f : A ->ₗc[R] B) (f' : A -> B) (h : f' = ⇑f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (R A)

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : A ->ₗc[R] A
  body: { LinearMap.id with
    counit_comp := by ext; rfl
    map_comp_comul := by simp only [map_id, LinearMap.id_comp, LinearMap.comp_id] }

中文:
定义 id
  签名: : A ->ₗc[R] A
  定义体: { LinearMap.id with
    counit_comp := by ext; rfl
    map_comp_comul := by simp only [map_id, LinearMap.id_comp, LinearMap.comp_id] }
-/
@[simps!] protected def id : A ->ₗc[R] A :=
  { LinearMap.id with
    counit_comp := by ext; rfl
    map_comp_comul := by simp only [map_id, LinearMap.id_comp, LinearMap.comp_id] }

variable {R A}

@[simp, norm_cast]
/--
theorem `coe_id` / 定理 `coe_id`

English:
theorem coe_id
  statement: ⇑(CoalgHom.id R A) = id
  proof: rfl

@[simp]

中文:
定理 coe_id
  结论: ⇑(CoalgHom.id R A) = id
  证明: rfl

@[simp]
-/
theorem coe_id : ⇑(CoalgHom.id R A) = id :=
  rfl

@[simp]
/--
theorem `id_toLinearMap` / 定理 `id_toLinearMap`

English:
theorem id_toLinearMap
  statement: (CoalgHom.id R A : A ->ₗ[R] A) = LinearMap.id
  proof: rfl

中文:
定理 id_toLinearMap
  结论: (CoalgHom.id R A : A ->ₗ[R] A) = LinearMap.id
  证明: rfl
-/
theorem id_toLinearMap : (CoalgHom.id R A : A ->ₗ[R] A) = LinearMap.id := rfl

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (φ₁ : B ->ₗc[R] C) (φ₂ : A ->ₗc[R] B)
  body: { (φ₁ : B ->ₗ[R] C) ∘ₗ (φ₂ : A ->ₗ[R] B) with
    counit_comp := by ext; simp
    map_comp_comul := by ext; simp [map_comp] }

@[simp]

中文:
定义 comp
  签名: (φ₁ : B ->ₗc[R] C) (φ₂ : A ->ₗc[R] B)
  定义体: { (φ₁ : B ->ₗ[R] C) ∘ₗ (φ₂ : A ->ₗ[R] B) with
    counit_comp := by ext; simp
    map_comp_comul := by ext; simp [map_comp] }

@[simp]
-/
@[simps!] def comp (φ₁ : B ->ₗc[R] C) (φ₂ : A ->ₗc[R] B) : A ->ₗc[R] C :=
  { (φ₁ : B ->ₗ[R] C) ∘ₗ (φ₂ : A ->ₗ[R] B) with
    counit_comp := by ext; simp
    map_comp_comul := by ext; simp [map_comp] }

@[simp]
/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: (φ₁ : B ->ₗc[R] C) (φ₂ : A ->ₗc[R] B)
  statement: ⇑(φ₁.comp φ₂) = φ₁ ∘ φ₂
  proof: rfl

@[simp]

中文:
定理 coe_comp
  条件: (φ₁ : B ->ₗc[R] C) (φ₂ : A ->ₗc[R] B)
  结论: ⇑(φ₁.comp φ₂) = φ₁ ∘ φ₂
  证明: rfl

@[simp]
-/
theorem coe_comp (φ₁ : B ->ₗc[R] C) (φ₂ : A ->ₗc[R] B) : ⇑(φ₁.comp φ₂) = φ₁ ∘ φ₂ := rfl

@[simp]
/--
theorem `comp_toLinearMap` / 定理 `comp_toLinearMap`

English:
theorem comp_toLinearMap
  given: (φ₁ : B ->ₗc[R] C) (φ₂ : A ->ₗc[R] B)
  proof: rfl

中文:
定理 comp_toLinearMap
  条件: (φ₁ : B ->ₗc[R] C) (φ₂ : A ->ₗc[R] B)
  证明: rfl
-/
theorem comp_toLinearMap (φ₁ : B ->ₗc[R] C) (φ₂ : A ->ₗc[R] B) :
    φ₁.comp φ₂ = (φ₁ : B ->ₗ[R] C) ∘ₗ (φ₂ : A ->ₗ[R] B) := rfl

variable (φ : A ->ₗc[R] B)

@[simp]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  statement: φ.comp (CoalgHom.id R A) = φ
  proof: ext fun _x => rfl

@[simp]

中文:
定理 comp_id
  结论: φ.comp (CoalgHom.id R A) = φ
  证明: ext fun _x => rfl

@[simp]
-/
theorem comp_id : φ.comp (CoalgHom.id R A) = φ :=
  ext fun _x => rfl

@[simp]
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  statement: (CoalgHom.id R B).comp φ = φ
  proof: ext fun _x => rfl

中文:
定理 id_comp
  结论: (CoalgHom.id R B).comp φ = φ
  证明: ext fun _x => rfl
-/
theorem id_comp : (CoalgHom.id R B).comp φ = φ :=
  ext fun _x => rfl

/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  given: (φ₁ : C ->ₗc[R] D) (φ₂ : B ->ₗc[R] C) (φ₃ : A ->ₗc[R] B)
  proof: ext fun _x => rfl

中文:
定理 comp_assoc
  条件: (φ₁ : C ->ₗc[R] D) (φ₂ : B ->ₗc[R] C) (φ₃ : A ->ₗc[R] B)
  证明: ext fun _x => rfl
-/
theorem comp_assoc (φ₁ : C ->ₗc[R] D) (φ₂ : B ->ₗc[R] C) (φ₃ : A ->ₗc[R] B) :
    (φ₁.comp φ₂).comp φ₃ = φ₁.comp (φ₂.comp φ₃) :=
  ext fun _x => rfl

/--
theorem `map_smul_of_tower` / 定理 `map_smul_of_tower`

English:
theorem map_smul_of_tower
  statement: {R'} [SMul R' A] [SMul R' B] [LinearMap.CompatibleSMul A B R' R] (r : R')
  proof: φ.toLinearMap.map_smul_of_tower r x

@[simps -isSimp toSemigroup_toMul_mul toOne_one]

中文:
定理 map_smul_of_tower
  结论: {R'} [SMul R' A] [SMul R' B] [LinearMap.CompatibleSMul A B R' R] (r : R')
  证明: φ.toLinearMap.map_smul_of_tower r x

@[simps -isSimp toSemigroup_toMul_mul toOne_one]

Depends on / 依赖: map_smul_of_tower, toLinearMap, toLinearMap.map_smul_of_tower
-/
theorem map_smul_of_tower {R'} [SMul R' A] [SMul R' B] [LinearMap.CompatibleSMul A B R' R] (r : R')
    (x : A) : φ (r • x) = r • φ x :=
  φ.toLinearMap.map_smul_of_tower r x

@[simps -isSimp toSemigroup_toMul_mul toOne_one]
/--
Instance `End` / 实例 `End`

English:
instance End
  signature: : Monoid (A ->ₗc[R] A) where
  body: comp
  mul_assoc _ _ _ := rfl
  one := CoalgHom.id R A
  one_mul _ := ext fun _ => rfl
  mul_one _ := ext fun _ => rfl

@[simp]

中文:
实例 End
  签名: : Monoid (A ->ₗc[R] A) where
  定义体: comp
  mul_assoc _ _ _ := rfl
  one := CoalgHom.id R A
  one_mul _ := ext fun _ => rfl
  mul_one _ := ext fun _ => rfl

@[simp]
-/
instance End : Monoid (A ->ₗc[R] A) where
  mul := comp
  mul_assoc _ _ _ := rfl
  one := CoalgHom.id R A
  one_mul _ := ext fun _ => rfl
  mul_one _ := ext fun _ => rfl

@[simp]
/--
theorem `one_apply` / 定理 `one_apply`

English:
theorem one_apply
  given: (x : A)
  statement: (1 : A ->ₗc[R] A) x = x
  proof: rfl

@[simp]

中文:
定理 one_apply
  条件: (x : A)
  结论: (1 : A ->ₗc[R] A) x = x
  证明: rfl

@[simp]
-/
theorem one_apply (x : A) : (1 : A ->ₗc[R] A) x = x :=
  rfl

@[simp]
/--
theorem `mul_apply` / 定理 `mul_apply`

English:
theorem mul_apply
  given: (φ ψ : A ->ₗc[R] A) (x : A)
  statement: (φ * ψ) x = φ (ψ x)
  proof: rfl

中文:
定理 mul_apply
  条件: (φ ψ : A ->ₗc[R] A) (x : A)
  结论: (φ * ψ) x = φ (ψ x)
  证明: rfl
-/
theorem mul_apply (φ ψ : A ->ₗc[R] A) (x : A) : (φ * ψ) x = φ (ψ x) :=
  rfl

end

end CoalgHom

namespace Coalgebra

variable (R : Type u) (A : Type v) (B : Type w) {ι : Type*}

variable [CommSemiring R] [AddCommMonoid A] [AddCommMonoid B] [Module R A] [Module R B]
variable [Coalgebra R A] [Coalgebra R B]

/--
Definition of `counitCoalgHom` / `counitCoalgHom` 的定义

English:
definition counitCoalgHom
  signature: : A ->ₗc[R] R
  body: { counit with
    counit_comp := by ext; simp
    map_comp_comul := by
      ext
      simp only [LinearMap.coe_comp, Function.comp_apply, CommSemiring.comul_apply,
        ← LinearMap.lTensor_comp_rTensor, rTensor_counit_comul, LinearMap.lTensor_tmul] }

@[simp]

中文:
定义 counitCoalgHom
  签名: : A ->ₗc[R] R
  定义体: { counit with
    counit_comp := by ext; simp
    map_comp_comul := by
      ext
      simp only [LinearMap.coe_comp, Function.comp_apply, CommSemiring.comul_apply,
        ← LinearMap.lTensor_comp_rTensor, rTensor_counit_comul, LinearMap.lTensor_tmul] }

@[simp]

Depends on / 依赖: CommSemiring, CommSemiring.comul_apply, Function, Function.comp_apply, LinearMap, LinearMap.coe_comp, LinearMap.lTensor_comp_rTensor, LinearMap.lTensor_tmul, coe_comp, comp_apply, comul_apply, counit, counit_comp, lTensor_comp_rTensor, lTensor_tmul, map_comp_comul, rTensor_counit_comul
-/
noncomputable def counitCoalgHom : A ->ₗc[R] R :=
  { counit with
    counit_comp := by ext; simp
    map_comp_comul := by
      ext
      simp only [LinearMap.coe_comp, Function.comp_apply, CommSemiring.comul_apply,
        ← LinearMap.lTensor_comp_rTensor, rTensor_counit_comul, LinearMap.lTensor_tmul] }

@[simp]
/--
theorem `counitCoalgHom_apply` / 定理 `counitCoalgHom_apply`

English:
theorem counitCoalgHom_apply
  given: (x : A)
  proof: rfl

@[simp]

中文:
定理 counitCoalgHom_apply
  条件: (x : A)
  证明: rfl

@[simp]
-/
theorem counitCoalgHom_apply (x : A) :
    counitCoalgHom R A x = counit x := rfl

@[simp]
/--
theorem `counitCoalgHom_toLinearMap` / 定理 `counitCoalgHom_toLinearMap`

English:
theorem counitCoalgHom_toLinearMap
  proof: rfl

中文:
定理 counitCoalgHom_toLinearMap
  证明: rfl
-/
theorem counitCoalgHom_toLinearMap :
    counitCoalgHom R A = counit (R := R) (A := A) := rfl

variable {R}

/--
Instance `subsingleton_to_ring` / 实例 `subsingleton_to_ring`

English:
instance subsingleton_to_ring
  signature: : Subsingleton (A ->ₗc[R] R)
  body: ⟨fun f g => CoalgHom.ext fun x => by
    have hf := CoalgHomClass.counit_comp_apply f x
    have hg := CoalgHomClass.counit_comp_apply g x
    simp_all only [CommSemiring.counit_apply]⟩

@[ext high]

中文:
实例 subsingleton_to_ring
  签名: : Subsingleton (A ->ₗc[R] R)
  定义体: ⟨fun f g => CoalgHom.ext fun x => by
    have hf := CoalgHomClass.counit_comp_apply f x
    have hg := CoalgHomClass.counit_comp_apply g x
    simp_all only [CommSemiring.counit_apply]⟩

@[ext high]

Depends on / 依赖: CoalgHom, CoalgHom.ext, CoalgHomClass, CoalgHomClass.counit_comp_apply, CommSemiring, CommSemiring.counit_apply, counit_apply, counit_comp_apply
-/
instance subsingleton_to_ring : Subsingleton (A ->ₗc[R] R) :=
  ⟨fun f g => CoalgHom.ext fun x => by
    have hf := CoalgHomClass.counit_comp_apply f x
    have hg := CoalgHomClass.counit_comp_apply g x
    simp_all only [CommSemiring.counit_apply]⟩

@[ext high]
/--
theorem `ext_to_ring` / 定理 `ext_to_ring`

English:
theorem ext_to_ring
  given: (f g : A ->ₗc[R] R)
  statement: f = g
  proof: Subsingleton.elim _ _

中文:
定理 ext_to_ring
  条件: (f g : A ->ₗc[R] R)
  结论: f = g
  证明: Subsingleton.elim _ _

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
theorem ext_to_ring (f g : A ->ₗc[R] R) : f = g := Subsingleton.elim _ _

variable {A B}
/--
If `φ : A → B` is a coalgebra map and `a = ∑ xᵢ ⊗ yᵢ`, then `φ a = ∑ φ xᵢ ⊗ φ yᵢ`
-/
@[simps]
/--
Definition of `Repr.induced` / `Repr.induced` 的定义

English:
definition Repr.induced
  signature: {a : A} (repr : Repr R a ι)
  body: repr.index
  left := φ ∘ repr.left
  right := φ ∘ repr.right
  eq := (congr($((CoalgHomClass.map_comp_comul φ).symm) a).trans <|
      by rw [LinearMap.comp_apply, ← repr.eq, map_sum]; rfl).symm

中文:
定义 Repr.induced
  签名: {a : A} (repr : Repr R a ι)
  定义体: repr.index
  left := φ ∘ repr.left
  right := φ ∘ repr.right
  eq := (congr($((CoalgHomClass.map_comp_comul φ).symm) a).trans <|
      by rw [LinearMap.comp_apply, ← repr.eq, map_sum]; rfl).symm

Depends on / 依赖: repr.index
-/
def Repr.induced {a : A} (repr : Repr R a ι)
    {F : Type*} [FunLike F A B] [CoalgHomClass F R A B]
    (φ : F) : Repr R (φ a) ι where
  index := repr.index
  left := φ ∘ repr.left
  right := φ ∘ repr.right
  eq := (congr($((CoalgHomClass.map_comp_comul φ).symm) a).trans <|
      by rw [LinearMap.comp_apply, ← repr.eq, map_sum]; rfl).symm

end Coalgebra
